//! Original context-zero TypeCall entry for the connected pure producer.
//! Staging owns no original raw Invoke. Every actual Evidence remains under
//! the immutable OriginalOnly consumer policy. No nonzero entry is admitted.

use std::collections::{HashMap, HashSet};

use super::{AdmittedFrame, Analysis, Atom, ContextPath, Expr, Failure, Graph,
    Transition, TypeWorkBudget, charge};
use super::deferred_frame::{ProjectionClass, RouteId};
use super::local_recipe::Compiler;
use super::producer::RootFeed;
use super::producer_driver::{self, DriverState, EvidenceInputs};
use super::producer_evidence::TopologyInput;
use super::producer_zero::ExactEvidenceZero;
use super::source_occurrence::FamilyGuard;
use super::source_topology;
use super::support_plan::{self, QualifiedFamily};

#[derive(Clone, Copy)]
enum Decision { Original, Installed(RouteId) }

struct EvidenceRecord {
    function: usize,
    factory: usize,
    zero_context: usize,
    topology: source_topology::Prepared,
}

struct Entry {
    // These tokens are minted only for this checked family's original visit.
    admitted: HashMap<usize, AdmittedFrame>,
}

struct Tables {
    evidence: HashMap<usize, EvidenceRecord>,
    classes: HashMap<usize, ProjectionClass>,
    zero_empty: HashSet<usize>,
}

impl Tables {
    fn new() -> Self {
        Self { evidence: HashMap::new(), classes: HashMap::new(), zero_empty: HashSet::new() }
    }

    fn retain_class(&mut self, expression: usize, class: ProjectionClass,
        zero_empty: bool, budget: &mut TypeWorkBudget) -> Result<(), Failure>
    {
        charge(budget, 2)?;
        if let Some(old) = self.classes.get(&expression) {
            if *old != class { return Err(Failure::Invalid); }
        } else {
            self.classes.try_reserve(1).map_err(|_| Failure::Resource)?;
            self.classes.insert(expression, class);
        }
        if zero_empty && !self.zero_empty.contains(&expression) {
            self.zero_empty.try_reserve(1).map_err(|_| Failure::Resource)?;
            self.zero_empty.insert(expression);
        }
        Ok(())
    }
}

pub(super) struct State<'g> {
    driver: DriverState<'g>,
    tables: Tables,
    entries: HashMap<usize, Entry>,
    decisions: HashMap<usize, Decision>,
}

impl<'g> State<'g> {
    fn new(graph: &'g Graph, routes: &mut super::deferred_frame::Arena,
        budget: &mut TypeWorkBudget) -> Result<Self, Failure>
    {
        Ok(Self { driver: DriverState::new(graph, routes, budget)?, tables: Tables::new(),
            entries: HashMap::new(), decisions: HashMap::new() })
    }
}

struct Host<'s> {
    tables: &'s Tables,
    entry: &'s Entry,
}

impl producer_driver::Host for Host<'_> {
    fn zero_empty_slot(&self, expression: usize) -> bool {
        self.tables.zero_empty.contains(&expression)
    }
    fn class(&self, expression: usize) -> Option<ProjectionClass> {
        self.tables.classes.get(&expression).copied()
    }
    fn admitted(&self, function: usize) -> Option<&AdmittedFrame> {
        self.entry.admitted.get(&function)
    }
    fn exact_evidence_zero(&self, expression: usize) -> Option<ExactEvidenceZero> {
        self.tables.evidence.get(&expression).map(|record| ExactEvidenceZero {
            expression, context: record.zero_context,
        })
    }
    fn evidence(&self, expression: usize, function: usize) -> Option<EvidenceInputs<'_>> {
        let record = self.tables.evidence.get(&expression)?;
        if record.function != function { return None; }
        let topology = &record.topology;
        Some(EvidenceInputs { topology: TopologyInput { visits: &topology.visits,
            bindings: &topology.bindings, residuals: &topology.residuals },
            classes: &topology.classes })
    }
}

// Keep new owner construction out of the large evaluator's per-visit frame.
// Existing FrameState stays borrowed; neither driver staging nor publication
// moves it out of Analysis.
fn ensure_state<'g>(analysis: &mut Analysis<'g>, budget: &mut TypeWorkBudget)
    -> Result<(), Failure>
{
    super::source_visit::ensure_frames(analysis, budget)?;
    if analysis.source_recipes.is_empty() {
        charge(budget, 1)?;
        analysis.source_recipes.try_reserve_exact(1).map_err(|_| Failure::Resource)?;
        let compiler = Compiler::new(analysis, budget)?;
        analysis.source_recipes.push(compiler);
    }
    if analysis.source_producers.is_empty() {
        charge(budget, 1)?;
        analysis.source_producers.try_reserve_exact(1).map_err(|_| Failure::Resource)?;
        let frames = analysis.frames.first_mut().ok_or(Failure::Invalid)?;
        let state = State::new(analysis.graph, &mut frames.arena, budget)?;
        analysis.source_producers.push(state);
    }
    Ok(())
}

fn retain_classes(analysis: &mut Analysis<'_>, expressions: impl IntoIterator<Item = usize>,
    budget: &mut TypeWorkBudget) -> Result<bool, Failure>
{
    let compiler = analysis.source_recipes.first_mut().ok_or(Failure::Invalid)?;
    let tables = &mut analysis.source_producers.first_mut().ok_or(Failure::Invalid)?.tables;
    for expression in expressions {
        charge(budget, 1)?;
        // Scope baselines (in particular fresh-Raw Empty slots) stay inside
        // QualifiedFactory. This table serves exact original saved heads and
        // therefore accepts only the complete all-writer source class.
        let Some(class) = compiler.prove_source_class(expression, budget)?
            else { return Ok(false); };
        let empty = compiler.prove_zero_empty_slot(expression, budget)?;
        tables.retain_class(expression, class, empty, budget)?;
    }
    Ok(true)
}

// Static proof caches may survive a decline. They contain only original Graph
// coordinates, complete classes and immutable topology, never attempted ScopeIds,
// observed answers, publication decisions or activation/memo state. Canonical
// original E0 path coordinates may also remain, with their interning/revision
// costs paid; a coordinate has no slot, value or publication authority.
fn prepare_entry<'g>(analysis: &mut Analysis<'g>, slot: usize, expression: usize,
    budget: &mut TypeWorkBudget) -> Result<bool, Failure>
{
    let family: QualifiedFamily<'g> = {
        let compiler = analysis.source_recipes.first_mut().ok_or(Failure::Invalid)?;
        let Ok(family) = support_plan::prepare_family(analysis.graph, compiler, expression, budget)?
            else { return Ok(false); };
        family
    };
    let guard = FamilyGuard::new(analysis.graph, &family, budget)?;
    let Some(occurrence) = guard.check(analysis, slot, budget)? else { return Ok(false); };
    let mut admitted = HashMap::new();
    charge(budget, family.factories().len())?;
    admitted.try_reserve(family.factories().len()).map_err(|_| Failure::Resource)?;
    let mut evidence = Vec::new();
    let mut seen = HashSet::new();
    for factory in family.factories() {
        admitted.insert(factory.returned(), guard.admit(occurrence, factory.returned(), budget)?);
        if !retain_classes(analysis, factory.support_classes().iter()
            .map(|proof| proof.expression), budget)? { return Ok(false); }
        for support in [factory.factory_support(), factory.returned_support()] {
            charge(budget, support.visits().len())?;
            for visit in support.visits() {
                if !matches!(visit.kind, support_plan::SupportKind::Evidence) { continue; }
                charge(budget, 1)?;
                if seen.contains(&visit.expression) { continue; }
                seen.try_reserve(1).map_err(|_| Failure::Resource)?;
                evidence.try_reserve(1).map_err(|_| Failure::Resource)?;
                let compiler = analysis.source_recipes.first_mut().ok_or(Failure::Invalid)?;
                let Some(payload) = compiler.direct_evidence_payload(visit.expression, budget)?
                    else { return Ok(false); };
                seen.insert(visit.expression);
                evidence.push((visit.expression, payload.body, payload.factory));
            }
        }
    }
    // Root actuals are outside the factory's capture-support closure. Retain
    // their complete classes and zero-writer proofs without scanning unrelated
    // graph expressions. typed_factory authenticated the original Merge/Slot
    // metadata shape and complete Type/Row witnesses.
    let Expr::Call { function, arguments, type_application: true, .. } =
        analysis.graph.expressions.get(expression).ok_or(Failure::Invalid)?
        else { return Err(Failure::Invalid); };
    let mut roots = super::copy_slice(arguments, budget)?;
    roots.try_reserve(2).map_err(|_| Failure::Resource)?;
    roots.push(*function);
    roots.push(expression);
    let mut root_seen = HashSet::new();
    while let Some(root) = roots.pop() {
        charge(budget, 2)?;
        if root_seen.contains(&root) { continue; }
        root_seen.try_reserve(1).map_err(|_| Failure::Resource)?;
        root_seen.insert(root);
        if !retain_classes(analysis, [root], budget)? { return Ok(false); }
        if let Some(Expr::Merge(children)) = analysis.graph.expressions.get(root) {
            charge(budget, children.len())?;
            roots.try_reserve(children.len()).map_err(|_| Failure::Resource)?;
            roots.extend(children);
        }
    }
    // Retain the complete static certificate before any EvidenceRecord can
    // refer to it. This immutable cache may survive a later semantic decline.
    analysis.source_producers.first_mut().ok_or(Failure::Invalid)?
        .driver.registry.add_family(family, budget)?;
    for (evidence, function, factory) in evidence {
        charge(budget, 1)?;
        if let Some(record) = analysis.source_producers.first().ok_or(Failure::Invalid)?
            .tables.evidence.get(&evidence)
        {
            if record.function != function || record.factory != factory { return Err(Failure::Invalid); }
            continue;
        }
        let Some(topology) = source_topology::prepare(analysis, evidence, function, budget)?
            else { return Ok(false); };
        if !retain_classes(analysis, topology.classes.iter().map(|(expression, _)| *expression),
            budget)? { return Ok(false); }
        // The original owner interns the exact E0 coordinate. ContextPaths and
        // revision change monotonically and stay paid even if staging declines.
        // No E0 slot, head, body, activation or publication is acquired here;
        // this coordinate cannot supply evidence or satisfy a readiness gate.
        let zero_context = analysis.context(0, Transition::Call(evidence), budget)?;
        if !matches!(analysis.contexts.paths.get(zero_context),
            Some(ContextPath::Step { parent: 0, transition: Transition::Call(actual), .. })
                if *actual == evidence)
        { return Err(Failure::Invalid); }
        charge(budget, 1)?;
        let tables = &mut analysis.source_producers.first_mut().ok_or(Failure::Invalid)?.tables;
        tables.evidence.try_reserve(1).map_err(|_| Failure::Resource)?;
        tables.evidence.insert(evidence, EvidenceRecord { function, factory, zero_context, topology });
    }
    let state = analysis.source_producers.first_mut().ok_or(Failure::Invalid)?;
    charge(budget, 1)?;
    state.entries.try_reserve(1).map_err(|_| Failure::Resource)?;
    state.entries.insert(expression, Entry { admitted });
    Ok(true)
}

// Only the actual original Evidence publisher calls this after all original
// routes are installed and before exposing Closure(G,E). Static qualification
// supplies complete classes; observed atoms and speculative saved sidecars do
// not grant canonical original-frame authority.
pub(super) fn record_actual_evidence(analysis: &mut Analysis<'_>, evidence: usize,
    function: usize, context: usize, budget: &mut TypeWorkBudget) -> Result<(), Failure>
{
    register_actual_evidence(analysis, evidence, function, context, budget).map(|_| ())
}

// A successful original transfer can predate its static certificate. Avoid
// even acquiring E when this actual replay has no retained source record.
pub(super) fn record_completed_evidence(analysis: &mut Analysis<'_>, evidence: usize,
    function: usize, arguments_context: usize, budget: &mut TypeWorkBudget,
) -> Result<(), Failure> {
    let Some(state) = analysis.source_producers.first() else { return Ok(()); };
    charge(budget, 1)?;
    if !state.tables.evidence.contains_key(&evidence) { return Ok(()); }
    let context = analysis.context(arguments_context, Transition::Call(evidence), budget)?;
    record_actual_evidence(analysis, evidence, function, context, budget)
}

struct OriginalEvidenceCoordinates {
    captures: Vec<usize>,
    supports: Vec<usize>,
}

fn register_actual_evidence(analysis: &mut Analysis<'_>, evidence: usize,
    function: usize, context: usize, budget: &mut TypeWorkBudget,
) -> Result<Option<OriginalEvidenceCoordinates>, Failure> {
    let Some(state) = analysis.source_producers.first() else { return Ok(None); };
    charge(budget, 1)?;
    let Some(record) = state.tables.evidence.get(&evidence) else { return Ok(None); };
    charge(budget, 2)?;
    if record.function != function || !matches!(analysis.contexts.paths.get(context),
        Some(ContextPath::Step { transition: Transition::Call(actual), .. }) if *actual == evidence)
    { return Err(Failure::Invalid); }
    let qualified = state.driver.registry.factory(record.factory)?;
    if qualified.returned() != function { return Err(Failure::Invalid); }
    let support = qualified.returned_support();
    let captures = super::copy_slice(support.captures(), budget)?;
    charge(budget, captures.len().checked_add(support.visits().len()).ok_or(Failure::Resource)?)?;
    let mut classes = Vec::new();
    let mut support_expressions = Vec::new();
    classes.try_reserve_exact(captures.len()).map_err(|_| Failure::Resource)?;
    support_expressions.try_reserve_exact(support.visits().len()).map_err(|_| Failure::Resource)?;
    for &capture in &captures {
        charge(budget, 1)?;
        classes.push(*state.tables.classes.get(&capture).ok_or(Failure::Invalid)?);
    }
    for visit in support.visits() {
        if !matches!(visit.kind, support_plan::SupportKind::Terminal(_)) { continue; }
        charge(budget, captures.len().checked_add(1).ok_or(Failure::Resource)?)?;
        if captures.contains(&visit.expression) { continue; }
        if !state.tables.classes.contains_key(&visit.expression)
            || !matches!(analysis.graph.expressions.get(visit.expression), Some(Expr::Slot))
        { return Err(Failure::Invalid); }
        support_expressions.push(visit.expression);
    }
    // Static support precedes dictionary cuts. A hidden terminal may not yet
    // have a leaf at E; install its original Slot without inventing an answer.
    // Exact live Heads then retain every later original write and watch.
    for &expression in &support_expressions {
        analysis.install_slot(expression, context, budget)?;
    }
    charge(budget, captures.len().checked_add(support_expressions.len()).ok_or(Failure::Resource)?)?;
    let mut bindings = Vec::new();
    let mut supports = Vec::new();
    bindings.try_reserve_exact(captures.len()).map_err(|_| Failure::Resource)?;
    supports.try_reserve_exact(support_expressions.len()).map_err(|_| Failure::Resource)?;
    let frames = analysis.frames.first_mut().ok_or(Failure::Invalid)?;
    for &capture in &captures {
        let route = frames.arena.head(super::deferred_frame::OriginalPort {
            expression: capture, context }, budget)?;
        bindings.push((capture, route));
    }
    for &expression in &support_expressions {
        let route = frames.arena.head(super::deferred_frame::OriginalPort {
            expression, context }, budget)?;
        supports.push((expression, route));
    }
    let admitted = AdmittedFrame { function };
    frames.arena.original_evidence_frame(function, context, &captures, &bindings, &classes,
        &supports, &admitted, budget)?;
    Ok(Some(OriginalEvidenceCoordinates { captures, supports: support_expressions }))
}

// Publication authentication only. Presence never supplies a class, chooses
// a source decision or changes staging. The exact output belongs to the
// original Evidence expression and its canonical original Call destination.
fn published_evidence(analysis: &Analysis<'_>, evidence: usize, function: usize,
    context: usize, budget: &mut TypeWorkBudget,
) -> Result<bool, Failure> {
    charge(budget, 2)?;
    let Some(ContextPath::Step { parent, transition: Transition::Call(actual), .. }) =
        analysis.contexts.paths.get(context) else { return Err(Failure::Invalid); };
    if *actual != evidence { return Err(Failure::Invalid); }
    let Some(&slot) = analysis.indices.get(&(evidence, *parent)) else { return Ok(false); };
    let output = analysis.slots.get(slot).ok_or(Failure::Invalid)?;
    if output.key != (evidence, *parent) { return Err(Failure::Invalid); }
    charge(budget, output.atoms.len())?;
    Ok(output.atoms.contains(&Atom::Closure(function, context)))
}

fn backfill_actual_evidence(analysis: &mut Analysis<'_>, budget: &mut TypeWorkBudget)
    -> Result<(), Failure>
{
    let state = analysis.source_producers.first().ok_or(Failure::Invalid)?;
    charge(budget, state.tables.evidence.len())?;
    let mut pending = Vec::new();
    pending.try_reserve_exact(state.tables.evidence.len()).map_err(|_| Failure::Resource)?;
    for (&evidence, record) in &state.tables.evidence {
        if published_evidence(analysis, evidence, record.function, record.zero_context, budget)? {
            pending.push((record.function, record.zero_context));
        }
    }
    // Original ports grow and later entries can retain new certificates.
    // This deduplication belongs to one publication batch, never to a claimed
    // permanent traversal completion or a cached ordered atom answer.
    let mut visited = HashSet::new();
    while let Some((function, creation)) = pending.pop() {
        charge(budget, 2)?;
        if visited.contains(&(function, creation)) { continue; }
        visited.try_reserve(1).map_err(|_| Failure::Resource)?;
        visited.insert((function, creation));
        charge(budget, 1)?;
        let evidence = match analysis.contexts.paths.get(creation) {
            Some(ContextPath::Step { transition: Transition::Call(evidence), .. }) => Some(*evidence),
            _ => None,
        };
        let coordinates = if let Some(evidence) = evidence {
            charge(budget, 1)?;
            let certified = analysis.source_producers.first().ok_or(Failure::Invalid)?
                .tables.evidence.get(&evidence);
            if let Some(record) = certified {
                // A literal Function can also be evaluated at Call(e). That
                // path alone does not authenticate an Evidence publication.
                if record.function == function
                    && published_evidence(analysis, evidence, function, creation, budget)?
                {
                    register_actual_evidence(analysis, evidence, function, creation, budget)?
                } else { None }
            } else { None }
        } else { None };
        let captures = match &coordinates {
            Some(coordinates) => coordinates.captures.as_slice(),
            None => match analysis.graph.expressions.get(function) {
                Some(Expr::Function { captures, .. }) => captures.as_slice(),
                _ => return Err(Failure::Invalid),
            },
        };
        let supports = coordinates.as_ref().map_or(&[][..], |coordinates| coordinates.supports.as_slice());
        charge(budget, captures.len().checked_add(supports.len()).ok_or(Failure::Resource)?)?;
        for &expression in captures.iter().chain(supports) {
            charge(budget, 2)?;
            let Some(&slot) = analysis.indices.get(&(expression, creation)) else { continue; };
            let original = analysis.slots.get(slot).ok_or(Failure::Invalid)?;
            if original.key != (expression, creation) { return Err(Failure::Invalid); }
            charge(budget, original.atoms.len())?;
            pending.try_reserve(original.atoms.len()).map_err(|_| Failure::Resource)?;
            for atom in &original.atoms {
                match atom {
                    Atom::Closure(function, creation) => pending.push((*function, *creation)),
                    Atom::FramedClosure(function, frame) => {
                        let creation = analysis.frames.first().ok_or(Failure::Invalid)?
                            .arena.original_creation(*frame, budget)?;
                        if let Some(creation) = creation { pending.push((*function, creation)); }
                    }
                    _ => {}
                }
            }
        }
    }
    Ok(())
}

// Returns true only when this exact original Call has a retained LOCAL route.
// Its original incoming/saved feeds remain in the ordinary solver. A declined
// zero occurrence permanently keeps its original protocol; no repeated failed
// staging and no fallback after a first live publication are possible.
pub(super) fn visit(analysis: &mut Analysis<'_>, slot: usize, expression: usize,
    context: usize, budget: &mut TypeWorkBudget) -> Result<bool, Failure>
{
    if context != 0 || analysis.focus.is_some() || analysis.frozen_contexts != 0
        || analysis.graph.producers.len() != 1
    { return Ok(false); }
    ensure_state(analysis, budget)?;
    charge(budget, 1)?;
    let state = analysis.source_producers.first_mut().ok_or(Failure::Invalid)?;
    if let Some(decision) = state.decisions.get(&slot).copied() {
        return match decision {
            Decision::Original => Ok(false),
            Decision::Installed(route) => {
                analysis.install_frame_link(slot, route, budget)?;
                Ok(true)
            }
        };
    }
    charge(budget, 1)?;
    state.decisions.try_reserve(1).map_err(|_| Failure::Resource)?;
    state.decisions.insert(slot, Decision::Original);
    if !prepare_entry(analysis, slot, expression, budget)? { return Ok(false); }
    let Expr::Call { function, arguments, type_application: true, .. } =
        analysis.graph.expressions.get(expression).ok_or(Failure::Invalid)?
        else { return Err(Failure::Invalid); };
    // Keep the exact original inputs and live watches before suppressing the
    // raw factory invocation. Readiness is an equation over every ordered input.
    analysis.slot(*function, 0, budget)?;
    charge(budget, arguments.len())?;
    for argument in arguments { analysis.slot(*argument, 0, budget)?; }
    let begun = analysis.source_producers.first_mut().ok_or(Failure::Invalid)?
        .driver.begin(expression, context, budget)?;
    if begun.is_err() { return Ok(false); }
    let ran = {
        let state = analysis.source_producers.first_mut().ok_or(Failure::Invalid)?;
        let host = Host { tables: &state.tables,
            entry: state.entries.get(&expression).ok_or(Failure::Invalid)? };
        let compiler = analysis.source_recipes.first_mut().ok_or(Failure::Invalid)?;
        let frames = analysis.frames.first_mut().ok_or(Failure::Invalid)?;
        state.driver.run(&host, compiler, &mut frames.types, &mut frames.arena, budget)?
    };
    // Driver aborts every failed attempt before returning, including all helper
    // cache journals. The preinstalled Original decision remains authoritative.
    if ran.is_err() { return Ok(false); }
    let copied = (|| {
        let state = analysis.source_producers.first_mut().ok_or(Failure::Invalid)?;
        let feeds: Vec<RootFeed> = super::copy_slice(&state.driver.registry.staged_root_feeds, budget)?;
        let activations = super::copy_slice(&state.driver.registry.staged_activation_edges, budget)?;
        Ok((feeds, activations))
    })();
    let (feeds, activations) = match copied {
        Ok(publication) => publication,
        Err(failure) => {
            analysis.source_producers.first_mut().ok_or(Failure::Invalid)?.driver.abort()?;
            return Err(failure);
        }
    };
    let sealed = match analysis.source_producers.first_mut().ok_or(Failure::Invalid)?.driver.seal(budget) {
        Ok(sealed) => sealed,
        Err(failure) => {
            analysis.source_producers.first_mut().ok_or(Failure::Invalid)?.driver.abort()?;
            return Err(failure);
        }
    };
    if sealed.expression != expression { return Err(Failure::Invalid); }
    // From seal onward every failure is terminal, including original metadata
    // backfill. No child runs while this visit owns the publication batch.
    backfill_actual_evidence(analysis, budget)?;
    let route = sealed.local.route;
    for feed in feeds {
        charge(budget, 2)?;
        let Expr::Function { body, .. } = analysis.graph.expressions.get(feed.returned)
            .ok_or(Failure::Invalid)? else { return Err(Failure::Invalid); };
        let root = *analysis.roots.get(body).ok_or(Failure::Invalid)?;
        let target = analysis.install_slot(feed.capture, root, budget)?;
        analysis.install_frame_link(target, feed.route, budget)?;
    }
    for (activation, condition) in activations {
        analysis.publish_frame_activation(activation, condition, budget)?;
    }
    analysis.install_frame_link(slot, route, budget)?;
    let state = analysis.source_producers.first_mut().ok_or(Failure::Invalid)?;
    state.driver.commit()?;
    *state.decisions.get_mut(&slot).ok_or(Failure::Invalid)? = Decision::Installed(route);
    Ok(true)
}

// Post-execution integration evidence, never an admission or runtime gate.
#[cfg(test)]
pub(super) fn coverage_for_test(analysis: &Analysis<'_>, application: usize)
    -> (bool, usize, usize)
{
    use super::producer::{ScopeKind, ScopeState};
    let Some(state) = analysis.source_producers.first() else { return (false, 0, 0); };
    let installed = analysis.indices.get(&(application, 0)).is_some_and(|slot|
        matches!(state.decisions.get(slot), Some(Decision::Installed(_))));
    let mut raw = 0;
    let mut evidence = 0;
    for scope in &state.driver.registry.scopes {
        if scope.state != ScopeState::Complete { continue; }
        match scope.kind {
            ScopeKind::Raw { .. } => raw += 1,
            ScopeKind::Evidence { .. } => evidence += 1,
            _ => {}
        }
    }
    (installed, raw, evidence)
}

// Same Graph and typed witnesses, choosing the retained original protocol for
// a reference arm before any visit. This cannot mint producer authority.
#[cfg(test)]
pub(super) fn original_entries_for_test(analysis: &mut Analysis<'_>, applications: &[usize],
    budget: &mut TypeWorkBudget) -> Result<(), Failure>
{
    ensure_state(analysis, budget)?;
    for &application in applications {
        charge(budget, 1)?;
        if !matches!(analysis.graph.expressions.get(application),
            Some(Expr::Call { type_application: true, .. })) { return Err(Failure::Invalid); }
        let slot = analysis.install_slot(application, 0, budget)?;
        let state = analysis.source_producers.first_mut().ok_or(Failure::Invalid)?;
        if state.decisions.contains_key(&slot) { return Err(Failure::Invalid); }
        state.decisions.try_reserve(1).map_err(|_| Failure::Resource)?;
        state.decisions.insert(slot, Decision::Original);
    }
    Ok(())
}
