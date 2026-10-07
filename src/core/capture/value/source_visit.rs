//! Exclusive matched source Function visits. Definition and bounded typed-body
//! constructors retain original creation identities, capture/root equations,
//! and Call/Evidence transport. No deferred Evidence family is enabled here.
//!
//! LocalShape is weaker than a complete occurrence class. Definition visits
//! exclude nonlocal writers at zero. Typed-body visits separately authenticate
//! completed original Invoke provenance and permanent capture writer classes.
//! Original concrete capture equations remain live; their values are not read
//! or cached by preparation. No Type/Row substitution is guessed here.

use super::{AdmittedFrame, Analysis, Atom, Expr, Failure, FrameState,
    ContextPath, FunctionCaptureInstallation, Transition, TypeWorkBudget, charge};
use super::deferred_frame::{OriginalPort, ProjectionClass};
use super::local_recipe::{Compiler, LocalShape, RecipeTag, SlotRole};

#[derive(Clone, Copy)]
enum ConstructorOrigin {
    Definition,
    TypedLeaf { application: usize, factory: usize, arguments_context: usize },
}

struct ConstructorClasses {
    classes: Vec<ProjectionClass>,
    origin: ConstructorOrigin,
}

struct Prepared;
struct Installed;

// Phase ownership cannot escape the exclusive original Function visit.
// Only Installed may complete/publish. The extra payload is one flat Vec;
// Graph, Analysis and FrameState remain borrowed in their existing owner.
struct SourceFunctionVisit<'s, 'g, Phase> {
    original: FunctionCaptureInstallation<'s, 'g>,
    classes: ConstructorClasses,
    phase: std::marker::PhantomData<Phase>,
}

fn prepare_classes(
    analysis: &mut Analysis<'_>, expression: usize, creation: usize,
    captures: &[usize], budget: &mut TypeWorkBudget,
) -> Result<Option<ConstructorClasses>, Failure> {
    charge(budget, 1)?;
    if analysis.focus.is_some() || analysis.frozen_contexts != 0
        || analysis.graph.producers.len() != 1
    {
        return Ok(None);
    }
    let origin = if creation == 0 {
        ConstructorOrigin::Definition
    } else {
        charge(budget, 1)?;
        let Some(ContextPath::Step { parent, transition: Transition::Invoke(application, factory), .. })
            = analysis.contexts.paths.get(creation).copied() else { return Ok(None); };
        // The completed exact own-Call stamp authenticates original canonical
        // q@A -> Invoke(q,F) provenance, not just a plausible path. That visit
        // installed its parameters and independent q@0 saved captures before
        // queuing the body. Later recurrence can supply additional feeds to I;
        // permanent all-writer classes below and original live ports cover them.
        // This is not a freshness or unique-creation certificate for all visits.
        charge(budget, 3)?; // index, slot-key and completed-transfer lookup
        let Some(&call_slot) = analysis.indices.get(&(application, parent)) else { return Ok(None); };
        if analysis.slots.get(call_slot).ok_or(Failure::Invalid)?.key != (application, parent)
            || !analysis.callable_transfers.contains(&(Some(call_slot), call_slot, factory, 0))
        { return Ok(None); }
        ConstructorOrigin::TypedLeaf { application, factory, arguments_context: parent }
    };
    if analysis.source_recipes.is_empty() {
        charge(budget, 1)?;
        analysis.source_recipes.try_reserve_exact(1).map_err(|_| Failure::Resource)?;
        let compiler = Compiler::new(analysis, budget)?;
        analysis.source_recipes.push(compiler);
    }
    let compiler = analysis.source_recipes.first_mut().ok_or(Failure::Invalid)?;
    if !compiler.compile_set(&[expression], budget)? { return Ok(None); }
    let prepared = compiler.prepared(expression).ok_or(Failure::Invalid)?;
    if !matches!(prepared.source, Expr::Function { .. })
        || !matches!(prepared.shape, LocalShape::Callable(code) if code == expression)
    {
        return Err(Failure::Invalid);
    }
    if let ConstructorOrigin::TypedLeaf { application, factory, .. } = origin {
        if !compiler.compile_set(&[application], budget)? { return Ok(None); }
        let source = compiler.prepared(application).ok_or(Failure::Invalid)?;
        if !matches!(source.tag, RecipeTag::TypedCall { factory: actual, body }
            if actual == factory && body == expression)
        { return Ok(None); }
        // Both complete original witnesses (full Forall kinds and Type/Row
        // actuals) remain in Graph and original Invoke transport. This batch
        // associates provenance; it performs no normalized substitution.
    }
    charge(budget, captures.len())?;
    let mut classes = Vec::new();
    classes.try_reserve_exact(captures.len()).map_err(|_| Failure::Resource)?;
    for &capture in captures {
        charge(budget, 1)?;
        let role = compiler.source_slot_role(capture, budget)?;
        let class = match origin {
            ConstructorOrigin::Definition => match role {
                // Root/Invoke/Call writers are nonzero. Unproved assignment
                // and provider writer roles declined before these zero-context classes.
                Some(SlotRole::Unbound | SlotRole::Metadata | SlotRole::Dictionary { .. }) => ProjectionClass::Empty,
                Some(SlotRole::Resource) => ProjectionClass::Metadata,
                Some(SlotRole::Global { .. } | SlotRole::Lexical { .. }) | None => {
                    if !compiler.compile_set(&[capture], budget)? { return Ok(None); }
                    match compiler.prepared(capture).ok_or(Failure::Invalid)?.shape {
                        LocalShape::Empty => ProjectionClass::Empty,
                        LocalShape::Metadata => ProjectionClass::Metadata,
                        LocalShape::Callable(code) => ProjectionClass::Callable(code),
                    }
                }
            },
            ConstructorOrigin::TypedLeaf { .. } => match role {
                // All metadata writers are Free/Unknown/Resource projections.
                // Dictionary provenance includes ALL original ordered binding
                // inputs; same-expression capture/root feeds preserve its code
                // class across contexts. Current atom emptiness is irrelevant.
                Some(SlotRole::Metadata) => ProjectionClass::Metadata,
                Some(SlotRole::Dictionary { .. }) => {
                    if !compiler.compile_set(&[capture], budget)? { return Ok(None); }
                    match compiler.prepared(capture).ok_or(Failure::Invalid)?.shape {
                        LocalShape::Empty => ProjectionClass::Empty,
                        LocalShape::Callable(code) => ProjectionClass::Callable(code),
                        LocalShape::Metadata => return Ok(None),
                    }
                }
                _ => return Ok(None),
            },
        };
        // Definition conversion is occurrence-specific. Typed-leaf conversion
        // uses the separate all-writers law and the completed original visit.
        classes.push(class);
    }
    Ok(Some(ConstructorClasses { classes, origin }))
}

pub(super) fn install_function(
    original: FunctionCaptureInstallation<'_, '_>, budget: &mut TypeWorkBudget,
) -> Result<(), Failure> {
    let graph = original.analysis.graph;
    charge(budget, original.captures.len().checked_add(1).ok_or(Failure::Resource)?)?;
    let Expr::Function { captures, body, .. } = graph.expressions.get(original.expression).ok_or(Failure::Invalid)?
        else { return Err(Failure::Invalid); };
    if captures != original.captures || *body != original.body
        || original.analysis.slots.get(original.slot).ok_or(Failure::Invalid)?.key
            != (original.expression, original.creation)
    {
        return Err(Failure::Invalid);
    }
    let classes = prepare_classes(original.analysis, original.expression,
        original.creation, original.captures, budget)?;
    let Some(classes) = classes else { return original.install_original(budget); };
    SourceFunctionVisit::<Prepared> { original, classes,
        phase: std::marker::PhantomData }.install_captures(budget)?.publish(budget)
}

impl<'s, 'g> SourceFunctionVisit<'s, 'g, Prepared> {
    fn install_captures(self, budget: &mut TypeWorkBudget)
        -> Result<SourceFunctionVisit<'s, 'g, Installed>, Failure>
    {
        let FunctionCaptureInstallation { analysis, slot, expression, creation, body, captures } = self.original;
        // Exact original ordered installation before any completed Closure is
        // visible. Saved creation ports and every required symbolic-root feed
        // stay in the original solver and retain all subsequent updates.
        for capture in captures {
            let source = analysis.install_slot(*capture, creation, budget)?;
            if let Some(root) = analysis.roots.get(&body).copied() {
                let target = analysis.install_slot(*capture, root, budget)?;
                analysis.edge(target, source, budget)?;
            }
        }
        Ok(SourceFunctionVisit {
            original: FunctionCaptureInstallation { analysis, slot, expression, creation, body, captures },
            classes: self.classes, phase: std::marker::PhantomData,
        })
    }
}

// Keep one-time FrameState construction off the per-visit phase frame. Never
// take/move an existing FrameState out of Analysis during a source visit.
fn ensure_frames(analysis: &mut Analysis<'_>, budget: &mut TypeWorkBudget) -> Result<(), Failure> {
    if analysis.frames.is_empty() {
        charge(budget, 1)?;
        analysis.frames.try_reserve_exact(1).map_err(|_| Failure::Resource)?;
        analysis.frames.push(FrameState::new_deferred());
    }
    Ok(())
}

impl SourceFunctionVisit<'_, '_, Installed> {
    fn publish(self, budget: &mut TypeWorkBudget) -> Result<(), Failure> {
        let FunctionCaptureInstallation { analysis, slot, expression, creation, captures, .. } = self.original;
        // Prepared -> Installed retains the exclusive original loan and the
        // authenticated constructor origin; installation cannot alter it.
        ensure_frames(analysis, budget)?;
        let frames = analysis.frames.first_mut().ok_or(Failure::Invalid)?;
        charge(budget, captures.len())?;
        let mut routes = Vec::new();
        routes.try_reserve_exact(captures.len()).map_err(|_| Failure::Resource)?;
        for capture in captures {
            let route = frames.arena.head(OriginalPort { expression: *capture, context: creation }, budget)?;
            routes.push((*capture, route));
        }
        // The private token exists only during this authenticated installed
        // owner visit. It is neither retained nor returned to another owner.
        let admitted = AdmittedFrame { function: expression };
        let frame = frames.arena.original_constructor_frame(expression, creation, captures, &routes,
            &self.classes.classes, &admitted, budget)?;
        analysis.atom(slot, Atom::FramedClosure(expression, frame), budget)?;
        // Private compile/native seam witness, not a performance observer or
        // accepted compiler diagnostic. Emit only after actual publication.
        #[cfg(debug_assertions)]
        match self.classes.origin {
            ConstructorOrigin::Definition => eprintln!(
                "ash-fusion-definition-source function={} creation=0 captures={}", expression, captures.len()),
            ConstructorOrigin::TypedLeaf { application, factory, arguments_context } => eprintln!(
                "ash-fusion-typed-leaf-source function={} creation={} application={} factory={} arguments_context={} captures={}",
                expression, creation, application, factory, arguments_context, captures.len()),
        }
        Ok(())
    }
}
