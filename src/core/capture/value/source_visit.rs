//! Exclusive matched source Function visits. This first connected batch only
//! represents original definition constructors; nested TypeCall/Evidence and
//! ordinary invocation transport retain their exact original identities.
//!
//! LocalShape is weaker than a complete occurrence class. At context zero,
//! the owner below separately proves the absence of nonlocal writer kinds.
//! Original concrete capture equations remain live; their values are not read
//! or cached by preparation. No Type/Row substitution is guessed here.

use super::{AdmittedFrame, Analysis, Atom, Expr, Failure, FrameState,
    FunctionCaptureInstallation, TypeWorkBudget, charge};
use super::deferred_frame::{OriginalPort, ProjectionClass};
use super::local_recipe::{Compiler, LocalShape, SlotRole};

struct DefinitionClasses(Vec<ProjectionClass>);

struct Prepared;
struct Installed;

// Phase ownership cannot escape the exclusive original Function visit.
// Only Installed may complete/publish. The extra payload is one flat Vec;
// Graph, Analysis and FrameState remain borrowed in their existing owner.
struct DefinitionFunctionVisit<'s, 'g, Phase> {
    original: FunctionCaptureInstallation<'s, 'g>,
    classes: DefinitionClasses,
    phase: std::marker::PhantomData<Phase>,
}

fn prepare_classes(
    analysis: &mut Analysis<'_>, expression: usize, creation: usize,
    captures: &[usize], budget: &mut TypeWorkBudget,
) -> Result<Option<DefinitionClasses>, Failure> {
    charge(budget, 1)?;
    if creation != 0 || analysis.focus.is_some() || analysis.frozen_contexts != 0
        || analysis.graph.producers.len() != 1
    {
        return Ok(None);
    }
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
    charge(budget, captures.len())?;
    let mut classes = Vec::new();
    classes.try_reserve_exact(captures.len()).map_err(|_| Failure::Resource)?;
    for &capture in captures {
        charge(budget, 1)?;
        // These are definition occurrences, not fresh ordinary invocations.
        // Graph-owned assignment/provider roles have already been excluded.
        // Metadata root Unknown writers are at Root(G), never at context zero;
        // Evidence writers are at Call(e), never at context zero. Unbound and
        // dictionary Slots therefore have no original context-zero writer.
        // A resource Slot retains its actual resource owner via its live port.
        let class = match compiler.source_slot_role(capture, budget)? {
            Some(SlotRole::Unbound | SlotRole::Metadata | SlotRole::Dictionary { .. }) => ProjectionClass::Empty,
            Some(SlotRole::Resource) => ProjectionClass::Metadata,
            Some(SlotRole::Global { .. }) | None => {
                if !compiler.compile_set(&[capture], budget)? { return Ok(None); }
                match compiler.prepared(capture).ok_or(Failure::Invalid)?.shape {
                    LocalShape::Empty => ProjectionClass::Empty,
                    LocalShape::Metadata => ProjectionClass::Metadata,
                    LocalShape::Callable(code) => ProjectionClass::Callable(code),
                }
            }
        };
        // This conversion belongs ONLY to the proven definition occurrence.
        // An arbitrary caller/root/frozen occurrence receives no such class.
        classes.push(class);
    }
    Ok(Some(DefinitionClasses(classes)))
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
    DefinitionFunctionVisit::<Prepared> { original, classes,
        phase: std::marker::PhantomData }.install_captures(budget)?.publish(budget)
}

impl<'s, 'g> DefinitionFunctionVisit<'s, 'g, Prepared> {
    fn install_captures(self, budget: &mut TypeWorkBudget)
        -> Result<DefinitionFunctionVisit<'s, 'g, Installed>, Failure>
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
        Ok(DefinitionFunctionVisit {
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

impl DefinitionFunctionVisit<'_, '_, Installed> {
    fn publish(self, budget: &mut TypeWorkBudget) -> Result<(), Failure> {
        let FunctionCaptureInstallation { analysis, slot, expression, creation, captures, .. } = self.original;
        // Prepared -> Installed retains the exclusive original loan and the
        // proven definition context; capture installation cannot alter it.
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
        let frame = frames.arena.definition_frame(expression, captures, &routes,
            &self.classes.0, &admitted, budget)?;
        analysis.atom(slot, Atom::FramedClosure(expression, frame), budget)?;
        // Private compile/native seam witness, not a performance observer or
        // accepted compiler diagnostic. Emit only after actual publication.
        #[cfg(debug_assertions)]
        eprintln!("ash-fusion-definition-source function={} creation=0 captures={}", expression, captures.len());
        Ok(())
    }
}
