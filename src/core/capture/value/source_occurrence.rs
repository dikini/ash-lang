//! Eligibility for one original source Call before raw Invoke construction.
//! Source-only experiment. A guard admits staging, never publication by itself.

use std::collections::HashSet;

use super::{AdmittedFrame, Analysis, ContextPath, Expr, Failure, Graph, Transition,
    TypeWorkBudget, charge};
use super::support_plan::{QualifiedFamily, UniqueBodyGuard};

pub(super) struct FamilyGuard<'g> {
    graph: &'g Graph,
    application: usize,
    factory: usize,
    factories: HashSet<usize>,
    returned: HashSet<usize>,
    bodies: Vec<UniqueBodyGuard>,
}

#[derive(Clone, Copy)]
pub(super) struct Occurrence {
    pub(super) application: usize,
}

impl<'g> FamilyGuard<'g> {
    pub(super) fn new(graph: &'g Graph, family: &QualifiedFamily<'g>,
        budget: &mut TypeWorkBudget) -> Result<Self, Failure>
    {
        let root = family.root();
        let count = family.factories().len();
        charge(budget, count.checked_mul(4).ok_or(Failure::Resource)?)?;
        let mut factories = HashSet::new();
        let mut returned = HashSet::new();
        let mut bodies = Vec::new();
        factories.try_reserve(count).map_err(|_| Failure::Resource)?;
        returned.try_reserve(count).map_err(|_| Failure::Resource)?;
        bodies.try_reserve_exact(count.checked_mul(2).ok_or(Failure::Resource)?)
            .map_err(|_| Failure::Resource)?;
        for factory in family.factories() {
            if !std::ptr::eq(factory.factory_support().graph(), graph)
                || !std::ptr::eq(factory.returned_support().graph(), graph)
                || !factories.insert(factory.factory())
            { return Err(Failure::Invalid); }
            returned.insert(factory.returned());
            bodies.extend(factory.unique_body_guards());
        }
        if !factories.contains(&root.factory) || !returned.contains(&root.body) {
            return Err(Failure::Invalid);
        }
        Ok(Self { graph, application: root.expression, factory: root.factory,
            factories, returned, bodies })
    }

    // The original Graph.start installs all roots before the first close.
    // Reject missing/shared/overwritten root associations. These checks retain
    // the qualifier's literal F -> literal G constructor boundary at runtime.
    pub(super) fn check(&self, analysis: &Analysis<'g>, slot: usize,
        budget: &mut TypeWorkBudget) -> Result<Option<Occurrence>, Failure>
    {
        charge(budget, 4)?;
        if !std::ptr::eq(self.graph, analysis.graph) || analysis.focus.is_some()
            || analysis.frozen_contexts != 0 || analysis.current != Some(slot)
        { return Ok(None); }
        let (application, context) = analysis.slots.get(slot).ok_or(Failure::Invalid)?.key;
        if application != self.application
            || !matches!(self.graph.expressions.get(application),
                Some(Expr::Call { type_application: true, .. }))
        { return Ok(None); }
        // The first connected candidate enters only at exact zero. A current
        // nonzero origin observation is not a proof about every future saved,
        // root or callable writer. Virtual children of this admitted entry use
        // closed normalized scopes and need no original nonzero entry permit.
        // Widening this boundary requires lifetime origin-producer closure,
        // including all full kinded alternatives, before first publication.
        if context != 0 { return Ok(None); }
        for guard in &self.bodies {
            charge(budget, 3)?;
            let Some(&root) = analysis.roots.get(&guard.body) else { return Ok(None); };
            if !matches!(analysis.contexts.paths.get(root),
                Some(ContextPath::Step { parent: 0, transition: Transition::Root(owner), .. })
                    if *owner == guard.function)
            { return Ok(None); }
        }
        let mut cursor = context;
        while let Some(ContextPath::Step { parent, transition, .. }) =
            analysis.contexts.paths.get(cursor)
        {
            charge(budget, 2)?;
            match transition {
                Transition::Root(owner) | Transition::Invoke(_, owner) => {
                    if self.factories.contains(owner) { return Ok(None); }
                }
                Transition::Focus | Transition::Restore(..) | Transition::Dispatch(..) => {
                    return Ok(None);
                }
                Transition::Call(_) => {}
            }
            cursor = *parent;
        }
        if cursor != 0 { return Err(Failure::Invalid); }
        // No original raw invocation may already own incoming writers. On
        // replay the source owner uses its retained completed staging decision;
        // it does not call this initial-eligibility gate to change protocols.
        charge(budget, 1)?;
        if analysis.contexts.extensions.contains_key(&(context,
            Transition::Invoke(application, self.factory)))
        { return Ok(None); }
        Ok(Some(Occurrence { application }))
    }

    // Mint only while the checked source visit still owns its staging loan.
    // Whole-plan completion and original own-input readiness precede any
    // output or K/root publication; this token alone grants neither.
    pub(super) fn admit(&self, occurrence: Occurrence, function: usize,
        budget: &mut TypeWorkBudget) -> Result<AdmittedFrame, Failure>
    {
        charge(budget, 2)?;
        if occurrence.application != self.application || !self.returned.contains(&function) {
            return Err(Failure::Invalid);
        }
        Ok(AdmittedFrame { function })
    }
}
