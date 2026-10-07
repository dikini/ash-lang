//! Private child of capture::value. Source admission remains disabled.
//! Exact original same-code/same-specialized-context coalescence only.

use std::collections::HashMap;

use super::{AdmittedFrame, CaptureTopology, Expr, Failure, Graph,
    PreparedDictionaryRoutes, TypeWorkBudget, charge, copy_slice};
use super::deferred_frame::{Arena as FrameArena, CaptureAlternative, CompletedFrame,
    OriginalPort, ProjectionClass, RouteId};
use super::typed_environment::TypeOrigin;

#[derive(Clone, Copy, Debug)]
pub(super) struct LocalRecipe {
    pub(super) expression: usize,
    // Proved class of the COMPLETE local-plus-ALL-feeds occurrence, not the
    // local route alone. Empty local may receive Callable dictionary feeds.
    pub(super) class: ProjectionClass,
    // Exact LOCAL original Expr recipe at specialized context E, excluding
    // creation/Call/root/incoming transfer feeds. Never Head(q,E) itself.
    pub(super) route: RouteId,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct DictionaryFeed {
    requirement: crate::interface::RequirementId,
    method: crate::interface::MethodId,
    ordinal: usize,
    source: OriginalPort,
}

struct PortPlan {
    expression: usize,
    class: ProjectionClass,
    local: RouteId,
    lexical: bool,
    dictionary: Vec<DictionaryFeed>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct FamilyKey {
    function: usize,
    evidence: usize,
    arguments_context: usize,
    specialized: usize,
    topology: usize,
}

impl FamilyKey {
    fn same_specialization(self, other: Self) -> bool {
        self.function == other.function && self.evidence == other.evidence
            && self.specialized == other.specialized && self.topology == other.topology
    }
}

pub(super) struct FamilyPlan {
    key: FamilyKey,
    captures: Vec<usize>,
    ports: Vec<PortPlan>,
}

impl FamilyPlan {
    pub(super) fn matches(&self, function: usize, evidence: usize,
        arguments_context: usize, specialized: usize) -> bool
    {
        self.key.function == function && self.key.evidence == evidence
            && self.key.arguments_context == arguments_context && self.key.specialized == specialized
    }
}

fn local_for(locals: &[LocalRecipe], expression: usize, budget: &mut TypeWorkBudget)
    -> Result<Option<LocalRecipe>, Failure>
{
    charge(budget, locals.len())?;
    let mut matching = locals.iter().filter(|local| local.expression == expression);
    let Some(local) = matching.next() else { return Ok(None); };
    if matching.next().is_some() { return Ok(None); }
    Ok(Some(*local))
}

fn dictionary_feed(graph: &Graph, evidence: usize, ordinal: usize, context: usize)
    -> Result<DictionaryFeed, Failure>
{
    let Some(Expr::Evidence { bindings, .. }) = graph.expressions.get(evidence)
        else { return Err(Failure::Invalid); };
    let &(requirement, method, expression) = bindings.get(ordinal).ok_or(Failure::Invalid)?;
    if graph.expressions.get(expression).is_none() { return Err(Failure::Invalid); }
    Ok(DictionaryFeed { requirement, method, ordinal,
        source: OriginalPort { expression, context } })
}

// Full original CaptureTopology remains the authority for visits, lexical
// cuts, binding ordinals and uncaptured dictionary obligations. This function
// checks PREPARATION only; it cannot mint AdmittedFrame.
// Each LocalRecipe.class must be proved for the COMPLETE occurrence, including
// all future lexical and dictionary feeds, never inferred from local atoms.
// First slice declines the WHOLE family if any lexical visit is not available
// as an exact declared capture on every input. No guessed deep creation route.
pub(super) fn prepare_family(
    graph: &Graph, topology: &CaptureTopology, topology_index: usize,
    function: usize, evidence: usize, arguments_context: usize, specialized: usize,
    locals: &[LocalRecipe], budget: &mut TypeWorkBudget,
) -> Result<Option<FamilyPlan>, Failure> {
    let Some(Expr::Function { captures, .. }) = graph.expressions.get(function)
        else { return Ok(None); };
    if !matches!(graph.expressions.get(evidence), Some(Expr::Evidence { .. })) { return Ok(None); }
    let captures = copy_slice(captures, budget)?;
    let mut ports = Vec::new();
    charge(budget, topology.visits.len())?;
    ports.try_reserve(topology.visits.len()).map_err(|_| Failure::Resource)?;
    for visit in &topology.visits {
        charge(budget, ports.len() + captures.len())?;
        if ports.iter().any(|port: &PortPlan| port.expression == visit.expression) {
            return Err(Failure::Invalid);
        }
        if visit.lexical && !captures.contains(&visit.expression) { return Ok(None); }
        if graph.expressions.get(visit.expression).is_none() { return Err(Failure::Invalid); }
        let Some(local) = local_for(locals, visit.expression, budget)? else { return Ok(None); };
        let ordinals = topology.bindings.get(visit.binding_start..visit.binding_end)
            .ok_or(Failure::Invalid)?;
        charge(budget, ordinals.len())?;
        let mut dictionary = Vec::new();
        dictionary.try_reserve_exact(ordinals.len()).map_err(|_| Failure::Resource)?;
        for ordinal in ordinals {
            dictionary.push(dictionary_feed(graph, evidence, *ordinal, arguments_context)?);
        }
        ports.push(PortPlan { expression: visit.expression, class: local.class,
            local: local.route, lexical: visit.lexical, dictionary });
    }
    if let PreparedDictionaryRoutes::Pending(obligations) = &topology.dictionary {
        for obligation in obligations {
            charge(budget, ports.len() + 1)?;
            let expression = graph.evidence.get(obligation.evidence).ok_or(Failure::Invalid)?.1;
            let feed = dictionary_feed(graph, evidence, obligation.binding, arguments_context)?;
            if let Some(port) = ports.iter_mut().find(|port| port.expression == expression) {
                // Original pending dictionary routing follows the first
                // lexical transfer. This first slice cannot reorder that
                // unusual overlapping case into dictionary-before-lexical.
                if port.lexical { return Ok(None); }
                port.dictionary.try_reserve(1).map_err(|_| Failure::Resource)?;
                port.dictionary.push(feed);
            } else {
                let Some(local) = local_for(locals, expression, budget)? else { return Ok(None); };
                let mut dictionary = Vec::new();
                dictionary.try_reserve(1).map_err(|_| Failure::Resource)?;
                dictionary.push(feed);
                ports.try_reserve(1).map_err(|_| Failure::Resource)?;
                ports.push(PortPlan { expression, class: local.class, local: local.route,
                    lexical: false, dictionary });
            }
        }
    }
    // Every declared capture has its own complete E equation, including empty
    // ports; an absent equation cannot borrow another capture's values.
    for capture in &captures {
        charge(budget, ports.len())?;
        if !ports.iter().any(|port| port.expression == *capture) { return Err(Failure::Invalid); }
    }
    Ok(Some(FamilyPlan { key: FamilyKey { function, evidence, arguments_context,
        specialized, topology: topology_index }, captures, ports }))
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct InputKey {
    pub(super) frame: CompletedFrame,
    // Stable position in this immutable input frame's alternatives().
    pub(super) alternative: usize,
}

#[derive(Clone, Copy)]
struct InputStamp { key: InputKey, arguments_context: usize, origin: TypeOrigin }

struct PortEquation {
    expression: usize,
    class: ProjectionClass,
    lexical: bool,
    // Local first, then each new argument context's ordered dictionary feeds
    // followed by that transfer's lexical feeds. Earlier contributions retain
    // their position; duplicate routes are harmless.
    sources: Vec<RouteId>,
}

struct Record {
    family: FamilyKey,
    frame: CompletedFrame,
    ports: Vec<PortEquation>,
    inputs: Vec<InputStamp>,
}

impl Record {
    fn copy(&self, budget: &mut TypeWorkBudget) -> Result<Self, Failure> {
        charge(budget, self.ports.len())?;
        let mut ports = Vec::new();
        ports.try_reserve_exact(self.ports.len()).map_err(|_| Failure::Resource)?;
        for port in &self.ports {
            ports.push(PortEquation { expression: port.expression, class: port.class, lexical: port.lexical,
                sources: copy_slice(&port.sources, budget)? });
        }
        Ok(Self { family: self.family, frame: self.frame, ports,
            inputs: copy_slice(&self.inputs, budget)? })
    }
}

// Short borrowed parent adapter. Publication MUST use the parent's existing
// revision/virtual-reader/concrete-port notification path; a raw arena head
// update is insufficient. Origin binding must preserve unresolved contexts.
pub(super) trait Transport {
    fn arena(&mut self) -> Result<&mut FrameArena, Failure>;
    fn publish_head(&mut self, port: OriginalPort, complete: RouteId,
        budget: &mut TypeWorkBudget) -> Result<(), Failure>;
    fn bind_origin(&mut self, context: usize, origin: TypeOrigin,
        budget: &mut TypeWorkBudget) -> Result<(), Failure>;
    fn publish_output(&mut self, function: usize, frame: CompletedFrame,
        budget: &mut TypeWorkBudget) -> Result<(), Failure>;
}

#[derive(Default)]
pub(super) struct Coalescer {
    // Exactly the original output atom's identity. Raw (G,I) and (G,E2) are
    // deliberately separate; no same-code global frame interning.
    records: HashMap<(usize, usize), Record>,
}

impl Coalescer {
    pub(super) fn new() -> Self { Self::default() }

    fn first_record(family: &FamilyPlan, admitted: &AdmittedFrame,
        transport: &mut impl Transport, budget: &mut TypeWorkBudget) -> Result<Record, Failure>
    {
        let arena = transport.arena()?;
        charge(budget, family.ports.len())?;
        let mut ports = Vec::new();
        ports.try_reserve_exact(family.ports.len()).map_err(|_| Failure::Resource)?;
        for port in &family.ports {
            let sources = copy_slice(&[port.local], budget)?;
            ports.push(PortEquation { expression: port.expression, class: port.class,
                lexical: port.lexical, sources });
        }
        charge(budget, family.captures.len().checked_mul(2).ok_or(Failure::Resource)?)?;
        let mut captures = Vec::new();
        let mut classes = Vec::new();
        captures.try_reserve_exact(family.captures.len()).map_err(|_| Failure::Resource)?;
        classes.try_reserve_exact(family.captures.len()).map_err(|_| Failure::Resource)?;
        for capture in &family.captures {
            charge(budget, family.ports.len())?;
            let plan = family.ports.iter().find(|port| port.expression == *capture).ok_or(Failure::Invalid)?;
            captures.push((*capture, arena.head(OriginalPort { expression: *capture,
                context: family.key.specialized }, budget)?));
            classes.push(plan.class);
        }
        let pending = arena.bindings(family.key.function, &family.captures, &captures, &classes,
            TypeOrigin::OriginalContext(family.key.specialized), budget)?;
        let frame = arena.complete_under(pending, admitted)?;
        Ok(Record { family: family.key, frame, ports, inputs: Vec::new() })
    }

    // The parent must first admit the WHOLE immutable family, original local
    // compiler, projection classes, context/fold/freeze guards and every input
    // creation route. No observation-driven late fallback is available here.
    pub(super) fn transfer(
        &mut self, family: &FamilyPlan, admitted: &AdmittedFrame, input_key: InputKey,
        input: &CaptureAlternative, transport: &mut impl Transport,
        budget: &mut TypeWorkBudget,
    ) -> Result<CompletedFrame, Failure> {
        charge(budget, family.captures.len())?;
        if admitted.function != family.key.function || input.function != family.key.function
            || input.captures.len() != family.captures.len()
            || input.captures.iter().zip(&family.captures).any(|((capture, _), expected)| capture != expected)
        { return Err(Failure::Invalid); }
        let key = (family.key.function, family.key.specialized);
        let mut dictionary_context_seen = false;
        charge(budget, 1)?;
        if let Some(record) = self.records.get(&key) {
            if !record.family.same_specialization(family.key) { return Err(Failure::Invalid); }
            // Local(q,E) is compiled once at E. Different original argument
            // contexts may feed that same E after ContextPaths folds Call(e).
            // The whole source qualifier still authenticates each exact visit;
            // it must never substitute a newly compiled or incompatible local.
            if record.ports.len() != family.ports.len() { return Err(Failure::Invalid); }
            charge(budget, family.ports.len())?;
            for (equation, port) in record.ports.iter().zip(&family.ports) {
                if equation.expression != port.expression || equation.class != port.class
                    || equation.lexical != port.lexical || equation.sources.first() != Some(&port.local)
                { return Err(Failure::Invalid); }
            }
            charge(budget, record.inputs.len())?;
            for stamp in &record.inputs {
                if stamp.arguments_context == family.key.arguments_context {
                    dictionary_context_seen = true;
                    if stamp.key == input_key {
                        if stamp.origin != input.type_origin { return Err(Failure::Invalid); }
                        transport.publish_output(family.key.function, record.frame, budget)?;
                        return Ok(record.frame);
                    }
                }
            }
        }
        // Reserve table publication before any complete-head/closure update.
        charge(budget, 1)?;
        self.records.try_reserve(1).map_err(|_| Failure::Resource)?;
        let first = !self.records.contains_key(&key);
        let mut record = match self.records.get(&key) {
            Some(record) => record.copy(budget)?,
            None => Self::first_record(family, admitted, transport, budget)?,
        };
        if input_key.frame == record.frame { return Err(Failure::Invalid); }
        // The paid input-stamp scan already establishes prior dictionary
        // contexts. No second context table or uncharged retained entry.
        let new_dictionary_context = !dictionary_context_seen;
        charge(budget, family.ports.len())?;
        let mut changes = Vec::new();
        changes.try_reserve_exact(family.ports.len()).map_err(|_| Failure::Resource)?;
        if record.ports.len() != family.ports.len() { return Err(Failure::Invalid); }
        for (plan, equation) in family.ports.iter().zip(&mut record.ports) {
            if plan.expression != equation.expression || plan.class != equation.class { return Err(Failure::Invalid); }
            let mut changed = first;
            if new_dictionary_context {
                // Preserve transfer history: Local, dictionary(A), lexical(A),
                // dictionary(B), lexical(B). Do not move B's dictionary ahead
                // of previously installed lexical feeds from A.
                charge(budget, plan.dictionary.len())?;
                equation.sources.try_reserve(plan.dictionary.len()).map_err(|_| Failure::Resource)?;
                for feed in &plan.dictionary {
                    if feed.source.context != family.key.arguments_context { return Err(Failure::Invalid); }
                    equation.sources.push(transport.arena()?.head(feed.source, budget)?);
                    changed = true;
                }
            }
            if plan.lexical {
                charge(budget, input.captures.len())?;
                let source = input.captures.iter().find(|(capture, _)| *capture == plan.expression)
                    .map(|(_, route)| *route).ok_or(Failure::Invalid)?;
                charge(budget, equation.sources.len())?;
                if !equation.sources.contains(&source) {
                    charge(budget, 1)?;
                    equation.sources.try_reserve(1).map_err(|_| Failure::Resource)?;
                    equation.sources.push(source);
                    changed = true;
                }
            }
            if changed {
                let route = transport.arena()?.join(equation.class, &equation.sources, budget)?;
                changes.push((OriginalPort { expression: equation.expression,
                    context: family.key.specialized }, route));
            }
        }
        charge(budget, 1)?;
        record.inputs.try_reserve(1).map_err(|_| Failure::Resource)?;
        record.inputs.push(InputStamp { key: input_key,
            arguments_context: family.key.arguments_context, origin: input.type_origin });
        // Stable Frame's capture Heads now see the complete per-port union.
        // A failed publication commits no input stamp; retry repeats it. A
        // resource failure may leave paid unpublished routes/partial heads,
        // as original Analysis mutations do, but cannot skip missing work.
        for (port, route) in changes { transport.publish_head(port, route, budget)?; }
        transport.bind_origin(family.key.specialized, input.type_origin, budget)?;
        let frame = record.frame;
        self.records.insert(key, record); // Capacity was reserved above.
        transport.publish_output(family.key.function, frame, budget)?;
        Ok(frame)
    }
}
