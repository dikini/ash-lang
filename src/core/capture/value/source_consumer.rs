//! Original Evidence materialization at an immutable source-policy boundary.
//! Private uncompiled work. Actual Evidence remains at its original destination;
//! only synthetic coalescence fixtures can seal enabled Head publication sites.

use super::{Atom, CaptureSlotPolicy, CheckedEvidenceVisit, EvidenceReader, Expr,
    Failure, Graph, ObservedCaptureSlots, PreparedDictionaryRoutes, Transition,
    ContextPath, TypeWorkBudget, charge};
use super::deferred_frame::{CompletedFrame, ProjectionClass, RouteId};
#[cfg(test)]
use super::deferred_frame::OriginalPort;

// Only the complete source-family qualifier may create these. The qualifier
// is not implemented in this packet. Coordinates/code shape alone cannot mint
// a site, and no per-occurrence fallback may remove a sealed source site.
pub(super) struct SourceSite<'g> {
    graph: &'g Graph,
    evidence: usize,
    function: usize,
    // Complete original virtual footprint and complete occurrence classes.
    // Only the future source qualifier can establish these assertions.
    footprint: Vec<(usize, ProjectionClass)>,
}

struct SitePublication {
    function: usize,
    footprint: Vec<(usize, ProjectionClass)>,
}

// The same sealed decisions must accompany every focused copy. Resetting
// mutable preparation/coalescence state does not reset this policy. Publishers
// may create Heads only at Call(e) for a SourceSite in this exact policy.
pub(super) struct PublicationPolicy<'g> {
    graph: &'g Graph,
    source: PublicationSites,
}

enum PublicationSites {
    // Constant storage for the conservative production boundary. There is no
    // expression-sized vector of disabled sites to allocate or copy.
    OriginalOnly,
    Enabled(Vec<Option<SitePublication>>),
}

impl<'g> PublicationPolicy<'g> {
    pub(super) fn seal_into(analysis: &mut super::Analysis<'g>,
        sites: &[SourceSite<'g>], budget: &mut TypeWorkBudget) -> Result<(), Failure>
    {
        charge(budget, 1)?;
        if analysis.source_policy.is_some() { return Err(Failure::Invalid); }
        let graph = analysis.graph;
        if sites.is_empty() {
            analysis.source_policy = Some(Self { graph, source: PublicationSites::OriginalOnly });
            return Ok(());
        }
        charge(budget, graph.expressions.len().checked_add(sites.len()).ok_or(Failure::Resource)?)?;
        let mut source = Vec::new();
        source.try_reserve_exact(graph.expressions.len()).map_err(|_| Failure::Resource)?;
        source.resize_with(graph.expressions.len(), || None);
        for site in sites {
            charge(budget, 1)?;
            if !std::ptr::eq(site.graph, graph)
                || !matches!(graph.expressions.get(site.evidence), Some(Expr::Evidence { .. }))
                || source.get(site.evidence).ok_or(Failure::Invalid)?.is_some()
            { return Err(Failure::Invalid); }
            let Some(Expr::Function { captures, .. }) = graph.expressions.get(site.function)
                else { return Err(Failure::Invalid); };
            charge(budget, site.footprint.len())?;
            for (position, &(expression, class)) in site.footprint.iter().enumerate() {
                charge(budget, position)?;
                if graph.expressions.get(expression).is_none()
                    || site.footprint[..position].iter().any(|(prior, _)| *prior == expression)
                { return Err(Failure::Invalid); }
                if let ProjectionClass::Callable(code) = class {
                    charge(budget, 1)?;
                    if !matches!(graph.expressions.get(code), Some(Expr::Function { .. })) {
                        return Err(Failure::Invalid);
                    }
                }
            }
            charge(budget, captures.len())?;
            for capture in captures {
                charge(budget, site.footprint.len())?;
                if !site.footprint.iter().any(|(expression, _)| expression == capture) {
                    return Err(Failure::Invalid);
                }
            }
            let footprint = super::copy_slice(&site.footprint, budget)?;
            *source.get_mut(site.evidence).ok_or(Failure::Invalid)? =
                Some(SitePublication { function: site.function, footprint });
        }
        charge(budget, 1)?;
        analysis.source_policy = Some(Self { graph, source: PublicationSites::Enabled(source) });
        Ok(())
    }

    pub(super) fn copy(&self, budget: &mut TypeWorkBudget) -> Result<Self, Failure> {
        charge(budget, 1)?;
        let PublicationSites::Enabled(sites) = &self.source else {
            return Ok(Self { graph: self.graph, source: PublicationSites::OriginalOnly });
        };
        charge(budget, sites.len())?;
        let mut source = Vec::new();
        source.try_reserve_exact(sites.len()).map_err(|_| Failure::Resource)?;
        for site in sites {
            let copied = match site {
                Some(site) => Some(SitePublication { function: site.function,
                    footprint: super::copy_slice(&site.footprint, budget)? }),
                None => None,
            };
            source.push(copied);
        }
        Ok(Self { graph: self.graph, source: PublicationSites::Enabled(source) })
    }

    fn original_destination(visit: &mut CheckedEvidenceVisit<'_, 'g>,
        budget: &mut TypeWorkBudget) -> Result<OriginalDestination, Failure>
    {
        // Consume only this owner's canonical policy, never another policy
        // for the same Graph. Focus copies preserve these exact decisions.
        charge(budget, 3)?;
        let policy = visit.analysis.source_policy.as_ref().ok_or(Failure::Invalid)?;
        let original = match &policy.source {
            PublicationSites::OriginalOnly => matches!(policy.graph.expressions.get(visit.evidence),
                Some(Expr::Evidence { .. })),
            PublicationSites::Enabled(sites) => matches!(sites.get(visit.evidence), Some(None)),
        };
        if !std::ptr::eq(policy.graph, visit.analysis.graph) || !original {
            return Err(Failure::Invalid);
        }
        let context = visit.analysis.context(visit.arguments_context,
            Transition::Call(visit.evidence), budget)?;
        charge(budget, 1)?;
        if !matches!(visit.analysis.contexts.paths.get(context),
            Some(ContextPath::Step { transition: Transition::Call(evidence), .. })
                if *evidence == visit.evidence)
            || context < visit.analysis.frozen_contexts
        { return Err(Failure::Invalid); }
        // Distinct original Call IDs cannot fold together. Under the sealed
        // publisher policy this destination can never acquire a virtual Head;
        // this proof does not inspect the current head table.
        Ok(OriginalDestination { evidence: visit.evidence, context })
    }
}

// The publisher still owns the complete route/class proof. This gate grants
// only publication at an exact coordinate in its one sealed source footprint;
// neither local shape nor a current head/atom observation grants authority.
#[cfg(test)]
pub(super) fn authorize_head(
    analysis: &super::Analysis<'_>, original: OriginalPort,
    budget: &mut TypeWorkBudget,
) -> Result<(), Failure> {
    charge(budget, 3)?;
    let policy = analysis.source_policy.as_ref().ok_or(Failure::Invalid)?;
    if !std::ptr::eq(policy.graph, analysis.graph)
        || original.context < analysis.frozen_contexts
    { return Err(Failure::Invalid); }
    let Some(ContextPath::Step { transition: Transition::Call(evidence), .. }) =
        analysis.contexts.paths.get(original.context)
        else { return Err(Failure::Invalid); };
    charge(budget, 1)?;
    let PublicationSites::Enabled(sites) = &policy.source else { return Err(Failure::Invalid); };
    let Some(Some(site)) = sites.get(*evidence) else { return Err(Failure::Invalid); };
    if !matches!(analysis.graph.expressions.get(site.function), Some(Expr::Function { .. })) {
        return Err(Failure::Invalid);
    }
    charge(budget, site.footprint.len())?;
    if !site.footprint.iter().any(|(expression, _)| *expression == original.expression) {
        return Err(Failure::Invalid);
    }
    Ok(())
}

// Synthetic coalescence correspondence fixtures only. The explicit original
// function/Evidence/complete-footprint rows replace a source proof IN TESTS;
// this helper is unavailable to production and is not a source qualifier.
#[cfg(test)]
pub(super) fn synthetic_site<'g>(
    graph: &'g Graph, evidence: usize, function: usize,
    footprint: &[(usize, ProjectionClass)], budget: &mut TypeWorkBudget,
) -> Result<SourceSite<'g>, Failure> {
    charge(budget, 1)?;
    Ok(SourceSite { graph, evidence, function,
        footprint: super::copy_slice(footprint, budget)? })
}

struct OriginalDestination {
    evidence: usize,
    context: usize,
}

struct AlternativeRoutes {
    // Positions in the exact original CaptureTopology. Only lexical visits
    // have a route; missing support is rejected during preflight, never Empty.
    lexical: Vec<Option<RouteId>>,
}

pub(super) fn materialize<'s, 'g>(mut visit: CheckedEvidenceVisit<'s, 'g>,
    function: usize, frame: CompletedFrame,
    budget: &mut TypeWorkBudget) -> Result<CheckedEvidenceVisit<'s, 'g>, Failure>
{
    let destination = PublicationPolicy::original_destination(&mut visit, budget)?;
    let graph = visit.analysis.graph;
    let Some(Expr::Function { captures, .. }) = graph.expressions.get(function)
        else { return Err(Failure::Invalid); };
    charge(budget, 2)?;
    if visit.analysis.slots.get(visit.slot).ok_or(Failure::Invalid)?.key
        != (destination.evidence, visit.arguments_context)
        || visit.analysis.frames.first().ok_or(Failure::Invalid)?.arena.function(frame)? != function
    { return Err(Failure::Invalid); }
    // Authenticate this frame through the actual installed Evidence input,
    // not through equality of a code/frame ordinal supplied by another owner.
    charge(budget, 1)?;
    let input = &visit.analysis.slots.get(visit.value).ok_or(Failure::Invalid)?.atoms;
    charge(budget, input.len())?;
    if !input.contains(&Atom::FramedClosure(function, frame)) { return Err(Failure::Invalid); }
    let plan = visit.analysis.prepare_capture_topology(function, destination.evidence, budget)?;
    let alternatives = visit.analysis.frame_alternatives(frame, budget)?;
    if alternatives.is_empty() { return Err(Failure::Invalid); }
    let visits = &visit.analysis.capture_topologies[plan].visits;
    charge(budget, alternatives.len())?;
    let mut prepared = Vec::new();
    prepared.try_reserve_exact(alternatives.len()).map_err(|_| Failure::Resource)?;
    for alternative in &alternatives {
        charge(budget, captures.len().checked_add(visits.len()).ok_or(Failure::Resource)?)?;
        if alternative.function != function || alternative.captures.len() != captures.len()
            || !alternative.captures.iter().zip(captures)
                .all(|((actual, _), expected)| actual == expected)
        { return Err(Failure::Invalid); }
        let mut lexical = Vec::new();
        lexical.try_reserve_exact(visits.len()).map_err(|_| Failure::Resource)?;
        for capture in visits {
            let route = if capture.lexical {
                Some(alternative.creation_route(capture.expression, budget)?
                    .ok_or(Failure::Invalid)?)
            } else { None };
            lexical.push(route);
        }
        prepared.push(AlternativeRoutes { lexical });
    }
    let stamp = (visit.analysis.current, visit.slot, function, frame);
    charge(budget, 2)?;
    let frames = visit.analysis.frames.first_mut().ok_or(Failure::Invalid)?;
    let complete = frames.transfers.contains(&stamp);
    frames.transfers.try_reserve(1).map_err(|_| Failure::Resource)?;
    // Type origins/watches remain live on structural replay, including every
    // alternative's unresolved original context. New query writes target E.
    visit.analysis.transfer_frame_type_origins(frame, destination.context, visit.slot, budget)?;
    if complete {
        super::source_producer::record_actual_evidence(visit.analysis, visit.evidence,
            function, destination.context, budget)?;
        return Ok(visit);
    }
    for alternative in &prepared {
        match visit.reader {
            EvidenceReader::Own(reader) => install(&mut visit, reader, plan,
                destination.context, alternative, budget)?,
            EvidenceReader::Other => install(&mut visit, ObservedCaptureSlots, plan,
                destination.context, alternative, budget)?,
        }
        // Residuals follow this alternative's entire capture transfer. An
        // overlapping residual must remain before the NEXT alternative's
        // lexical contribution, as in the original separate Closure visits.
        install_residuals(&mut visit, plan, destination.context, budget)?;
    }
    super::source_producer::record_actual_evidence(visit.analysis, visit.evidence,
        function, destination.context, budget)?;
    visit.analysis.atom(visit.slot, Atom::Closure(function, destination.context), budget)?;
    // The exact structural stamp is committed only after every original
    // route, residual and output succeeds. Partial refusal cannot skip work.
    visit.analysis.frames.first_mut().ok_or(Failure::Invalid)?.transfers.insert(stamp);
    Ok(visit)
}

fn install<P: CaptureSlotPolicy>(visit: &mut CheckedEvidenceVisit<'_, '_>, policy: P,
    plan: usize, context: usize, alternative: &AlternativeRoutes,
    budget: &mut TypeWorkBudget) -> Result<(), Failure>
{
    policy.prepare(budget)?;
    for position in 0..alternative.lexical.len() {
        charge(budget, 1)?;
        let capture = visit.analysis.capture_topologies[plan].visits[position];
        let destination = policy.slot(visit.analysis, capture.expression, context, budget)?;
        for position in capture.binding_start..capture.binding_end {
            charge(budget, 1)?;
            let binding = visit.analysis.capture_topologies[plan].bindings[position];
            let expression = visit.bindings.get(binding).ok_or(Failure::Invalid)?.2;
            let source = policy.slot(visit.analysis, expression, visit.arguments_context, budget)?;
            visit.analysis.edge(destination, source, budget)?;
        }
        if let Some(route) = alternative.lexical[position] {
            visit.analysis.install_frame_link(destination, route, budget)?;
        }
    }
    Ok(())
}

fn install_residuals(visit: &mut CheckedEvidenceVisit<'_, '_>, plan: usize,
    context: usize, budget: &mut TypeWorkBudget) -> Result<(), Failure>
{
    charge(budget, 1)?;
    let count = match &visit.analysis.capture_topologies[plan].dictionary {
        PreparedDictionaryRoutes::Complete => 0,
        PreparedDictionaryRoutes::Pending(obligations) => obligations.len(),
    };
    for position in 0..count {
        charge(budget, 2)?;
        let obligation = match &visit.analysis.capture_topologies[plan].dictionary {
            PreparedDictionaryRoutes::Pending(obligations) => obligations[position],
            PreparedDictionaryRoutes::Complete => return Err(Failure::Invalid),
        };
        let argument = visit.bindings.get(obligation.binding).ok_or(Failure::Invalid)?.2;
        let expression = visit.analysis.graph.evidence.get(obligation.evidence)
            .ok_or(Failure::Invalid)?.1;
        let target = visit.analysis.slot(expression, context, budget)?;
        visit.analysis.link(target, argument, visit.arguments_context, budget)?;
    }
    Ok(())
}
