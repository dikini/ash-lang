//! Exact original Evidence coordinates and E-local pure source closure.
//! This prepares immutable structure/classes only. It installs no routes,
//! contexts, slots, Heads, root feeds, activation conditions or live watches.

use std::collections::HashSet;

use super::{Analysis, Expr, Failure, PreparedDictionaryRoutes, TypeWorkBudget,
    charge};
use super::deferred_frame::ProjectionClass;
use super::local_recipe::Compiler;
use super::producer_evidence::{DictionaryFeed, VisitInput};

pub(super) struct Prepared {
    pub(super) visits: Vec<VisitInput>,
    pub(super) bindings: Vec<DictionaryFeed>,
    pub(super) residuals: Vec<DictionaryFeed>,
    // Complete homogeneous ALL-writer source classes, never fresh-I baselines.
    pub(super) classes: Vec<(usize, ProjectionClass)>,
}

pub(super) fn prepare<'g>(analysis: &mut Analysis<'g>, evidence: usize,
    function: usize, budget: &mut TypeWorkBudget,
) -> Result<Option<Prepared>, Failure> {
    let graph = analysis.graph;
    charge(budget, 2)?;
    let Some(Expr::Evidence { bindings: source_bindings, .. }) = graph.expressions.get(evidence)
        else { return Ok(None); };
    let Some(Expr::Function { captures, .. }) = graph.expressions.get(function)
        else { return Ok(None); };
    let plan = analysis.prepare_capture_topology(function, evidence, budget)?;
    // Finish this whole immutable-cache loan before taking the compiler's
    // mutable loan. No second evidence-key/port map is constructed here.
    let (visits, bindings, residuals, mut pending) = {
        let topology = analysis.capture_topologies.get(plan).ok_or(Failure::Invalid)?;
        let binding_index = analysis.binding_indices.get(&evidence).ok_or(Failure::Invalid)?;
        let mut visits = Vec::new();
        let mut bindings = Vec::new();
        let mut residuals = Vec::new();
        charge(budget, topology.visits.len().checked_add(topology.bindings.len()).ok_or(Failure::Resource)?)?;
        visits.try_reserve_exact(topology.visits.len()).map_err(|_| Failure::Resource)?;
        bindings.try_reserve_exact(topology.bindings.len()).map_err(|_| Failure::Resource)?;
        for visit in &topology.visits {
            charge(budget, 1)?;
            if visit.binding_start != bindings.len() || visit.binding_start > visit.binding_end
                || visit.binding_end > topology.bindings.len() { return Err(Failure::Invalid); }
            let start = bindings.len();
            if let Some(evidence_positions) = analysis.evidence_ports.get(&visit.expression) {
                charge(budget, evidence_positions.len())?;
                for &evidence_ordinal in evidence_positions {
                    let &(key, target) = graph.evidence.get(evidence_ordinal).ok_or(Failure::Invalid)?;
                    if target != visit.expression { return Err(Failure::Invalid); }
                    if let Some(binding_positions) = binding_index.get(&key) {
                        charge(budget, binding_positions.len())?;
                        for &binding_ordinal in binding_positions {
                            let tuple = source_bindings.get(binding_ordinal).ok_or(Failure::Invalid)?;
                            if (tuple.0, tuple.1) != key
                                || topology.bindings.get(bindings.len()) != Some(&binding_ordinal)
                                || bindings.len() >= visit.binding_end
                            { return Err(Failure::Invalid); }
                            // Capacity was reserved for the exact compact plan
                            // length; each original duplicate retains its pair.
                            bindings.push(DictionaryFeed { binding_ordinal, evidence_ordinal });
                        }
                    }
                }
            }
            if bindings.len() != visit.binding_end { return Err(Failure::Invalid); }
            visits.push(VisitInput { expression: visit.expression, lexical: visit.lexical,
                binding_start: start, binding_end: bindings.len() });
        }
        if bindings.len() != topology.bindings.len() { return Err(Failure::Invalid); }
        if let PreparedDictionaryRoutes::Pending(obligations) = &topology.dictionary {
            charge(budget, obligations.len())?;
            residuals.try_reserve_exact(obligations.len()).map_err(|_| Failure::Resource)?;
            for obligation in obligations {
                let &(key, _) = graph.evidence.get(obligation.evidence).ok_or(Failure::Invalid)?;
                let tuple = source_bindings.get(obligation.binding).ok_or(Failure::Invalid)?;
                if key != (tuple.0, tuple.1) { return Err(Failure::Invalid); }
                residuals.push(DictionaryFeed { binding_ordinal: obligation.binding,
                    evidence_ordinal: obligation.evidence });
            }
        }
        let mut pending = Vec::new();
        charge(budget, captures.len())?;
        pending.try_reserve_exact(captures.len()).map_err(|_| Failure::Resource)?;
        pending.extend(captures.iter().map(|capture| (*capture, false)));
        let extra = visits.len().checked_add(residuals.len()).ok_or(Failure::Resource)?;
        charge(budget, extra)?;
        pending.try_reserve(extra).map_err(|_| Failure::Resource)?;
        pending.extend(visits.iter().map(|visit| (visit.expression, false)));
        for residual in &residuals {
            pending.push((graph.evidence.get(residual.evidence_ordinal).ok_or(Failure::Invalid)?.1, false));
        }
        (visits, bindings, residuals, pending)
    };

    // This is E's LOCAL dependency closure. In particular a nested TypeCall
    // follows its original callee and ALL actual arguments, not its factory's
    // captures/body: the Raw producer owns that separate creation environment.
    let mut seen = HashSet::new();
    let mut active = HashSet::new();
    let mut expressions = Vec::new();
    while let Some((expression, finish)) = pending.pop() {
        charge(budget, 1)?;
        if finish {
            active.remove(&expression);
            seen.try_reserve(1).map_err(|_| Failure::Resource)?;
            seen.insert(expression);
            continue;
        }
        if seen.contains(&expression) { continue; }
        // Evidence's weaker shape deliberately ignores bindings, so its
        // shape cache alone cannot certify this larger LOCAL dependency DAG.
        if active.contains(&expression) { return Ok(None); }
        active.try_reserve(1).map_err(|_| Failure::Resource)?;
        expressions.try_reserve(1).map_err(|_| Failure::Resource)?;
        pending.try_reserve(1).map_err(|_| Failure::Resource)?;
        active.insert(expression);
        expressions.push(expression);
        pending.push((expression, true));
        match graph.expressions.get(expression).ok_or(Failure::Invalid)? {
            Expr::Scalar | Expr::Slot => {}
            Expr::Alias(child) => {
                charge(budget, 1)?;
                pending.try_reserve(1).map_err(|_| Failure::Resource)?;
                pending.push((*child, false));
            }
            Expr::Merge(children) => {
                charge(budget, children.len())?;
                pending.try_reserve(children.len()).map_err(|_| Failure::Resource)?;
                pending.extend(children.iter().map(|child| (*child, false)));
            }
            Expr::Call { function, arguments, type_application: true, .. } => {
                let count = arguments.len().checked_add(1).ok_or(Failure::Resource)?;
                charge(budget, count)?;
                pending.try_reserve(count).map_err(|_| Failure::Resource)?;
                pending.push((*function, false));
                pending.extend(arguments.iter().map(|argument| (*argument, false)));
            }
            Expr::Evidence { value, bindings } => {
                let count = bindings.len().checked_add(1).ok_or(Failure::Resource)?;
                charge(budget, count)?;
                pending.try_reserve(count).map_err(|_| Failure::Resource)?;
                pending.push((*value, false));
                pending.extend(bindings.iter().map(|(_, _, argument)| (*argument, false)));
            }
            // Includes literal Function, ordinary Apply, allocation, handler,
            // request/resume, opaque Unknown and every other unproved recipe.
            _ => return Ok(None),
        }
    }
    if analysis.source_recipes.is_empty() {
        charge(budget, 1)?;
        analysis.source_recipes.try_reserve_exact(1).map_err(|_| Failure::Resource)?;
        let compiler = Compiler::new(analysis, budget)?;
        analysis.source_recipes.push(compiler);
    }
    let compiler = analysis.source_recipes.first_mut().ok_or(Failure::Invalid)?;
    let mut classes = Vec::new();
    charge(budget, expressions.len())?;
    classes.try_reserve_exact(expressions.len()).map_err(|_| Failure::Resource)?;
    for expression in expressions {
        // Slots are terminals in this walk. A unique lexical callable can be
        // an opaque source; Resource Slots retain their exact metadata class.
        // Expr::Resource itself remains unsupported above. No raw-I role or
        // context-zero emptiness certificate is inferred from this class.
        if matches!(graph.expressions.get(expression), Some(Expr::Slot))
            && compiler.source_slot_role(expression, budget)?.is_none()
        { return Ok(None); }
        let Some(class) = compiler.prove_source_class(expression, budget)? else { return Ok(None); };
        classes.push((expression, class));
    }
    Ok(Some(Prepared { visits, bindings, residuals, classes }))
}
