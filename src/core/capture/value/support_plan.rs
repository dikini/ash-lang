//! Static capture-support closure for one immutable Graph.
//! This private child of capture::value is not installed or enabled. It
//! records the original topology traversal before dictionary cuts; it does
//! not prove complete occurrence classes, readiness, or frame admission.

use std::collections::{HashMap, HashSet};

use super::{Expr, Failure, Graph, TypeWorkBudget, charge, copy_slice};
use super::local_recipe::{Compiler, RecipeTag, SlotRole};
use super::deferred_frame::ProjectionClass;

#[derive(Clone, Copy, Debug)]
pub(super) struct TypedCallRelation {
    pub(super) expression: usize,
    pub(super) factory: usize,
    pub(super) body: usize,
}

#[derive(Clone, Copy, Debug)]
pub(super) enum SupportKind {
    Alias,
    Merge,
    // Index into this plan's ordered original TypedCall relations.
    TypedCall(usize),
    Evidence,
    Terminal(SlotRole),
}

#[derive(Clone, Copy, Debug)]
pub(super) struct SupportVisit {
    pub(super) expression: usize,
    pub(super) kind: SupportKind,
}

#[derive(Clone, Copy, Debug)]
pub(super) enum Decline {
    NotFunction,
    Recipe,
    UnsupportedTerminal,
    UnsupportedSlot,
    UnknownSlot,
    NotTypedCall,
    SharedBody,
    SourceWriters,
    SourceClass,
    FactoryCycle,
}

// The owner may retain this once per Graph/function and reuse it at many
// Evidence sites. Private vectors expose only immutable slices. The Graph
// loan keeps original capture/operand coordinates paired with their source.
pub(super) struct CaptureSupportPlan<'g> {
    graph: &'g Graph,
    function: usize,
    captures: &'g [usize],
    visits: Vec<SupportVisit>,
    typed_calls: Vec<TypedCallRelation>,
}

impl<'g> CaptureSupportPlan<'g> {
    pub(super) fn graph(&self) -> &'g Graph { self.graph }
    pub(super) fn function(&self) -> usize { self.function }
    pub(super) fn captures(&self) -> &'g [usize] { self.captures }
    pub(super) fn visits(&self) -> &[SupportVisit] { &self.visits }
    pub(super) fn typed_calls(&self) -> &[TypedCallRelation] { &self.typed_calls }
}

// Structure only: terminal Global at I remains that exact original port. It
// does not become Global at zero; Unbound does not certify contextual Empty.
// Factory dependency acyclicity through each returned body's captures needs
// a separate iterative qualifier. A visited set here only bounds this walk.
pub(super) fn prepare<'g>(
    graph: &'g Graph, compiler: &mut Compiler<'g>, function: usize,
    budget: &mut TypeWorkBudget,
) -> Result<Result<CaptureSupportPlan<'g>, Decline>, Failure> {
    charge(budget, 1)?;
    let Some(Expr::Function { captures, .. }) = graph.expressions.get(function) else {
        if graph.expressions.get(function).is_none() { return Err(Failure::Invalid); }
        return Ok(Err(Decline::NotFunction));
    };
    // Function preparation stops before captures. It establishes the paired
    // compiler's original Graph loan without recursively compiling this plan.
    if !compiler.compile_set(&[function], budget)? {
        return Ok(Err(Decline::Recipe));
    }
    charge(budget, 1)?;
    let prepared = compiler.prepared(function).ok_or(Failure::Invalid)?;
    if !std::ptr::eq(prepared.source, &graph.expressions[function])
        || !matches!(prepared.tag, RecipeTag::Function)
    { return Err(Failure::Invalid); }

    let mut pending = copy_slice(captures, budget)?;
    let mut visited = HashSet::new();
    let mut visits = Vec::new();
    let mut typed_calls = Vec::new();
    while let Some(expression) = pending.pop() {
        charge(budget, 1)?;
        if visited.contains(&expression) { continue; }
        charge(budget, 1)?;
        visited.try_reserve(1).map_err(|_| Failure::Resource)?;
        visited.insert(expression);
        let source = graph.expressions.get(expression).ok_or(Failure::Invalid)?;
        let kind = match source {
            Expr::Alias(child) => {
                charge(budget, 1)?;
                pending.try_reserve(1).map_err(|_| Failure::Resource)?;
                pending.push(*child);
                SupportKind::Alias
            }
            Expr::Merge(children) => {
                charge(budget, children.len())?;
                pending.try_reserve(children.len()).map_err(|_| Failure::Resource)?;
                pending.extend(children);
                SupportKind::Merge
            }
            Expr::Call { function, arguments, type_application: true, .. } => {
                if !compiler.compile_set(&[expression], budget)? {
                    return Ok(Err(Decline::Recipe));
                }
                charge(budget, 1)?;
                let prepared = compiler.prepared(expression).ok_or(Failure::Invalid)?;
                if !std::ptr::eq(prepared.source, source) { return Err(Failure::Invalid); }
                let RecipeTag::TypedCall { factory, body } = prepared.tag else {
                    return Err(Failure::Invalid);
                };
                // The checked factory relation remains in the original Graph;
                // no full Type/Row witness is reduced to its metadata inputs.
                charge(budget, 2)?;
                if !matches!(graph.expressions.get(factory),
                    Some(Expr::Function { body: actual, .. }) if *actual == body)
                    || !matches!(graph.expressions.get(body), Some(Expr::Function { .. }))
                { return Err(Failure::Invalid); }
                let relation = typed_calls.len();
                charge(budget, 1)?;
                typed_calls.try_reserve(1).map_err(|_| Failure::Resource)?;
                typed_calls.push(TypedCallRelation { expression, factory, body });
                let count = arguments.len().checked_add(1).ok_or(Failure::Resource)?;
                charge(budget, count)?;
                pending.try_reserve(count).map_err(|_| Failure::Resource)?;
                // Same pushes as original CaptureTopology: LIFO visits the
                // arguments in reverse order before the function operand.
                pending.push(*function);
                pending.extend(arguments);
                SupportKind::TypedCall(relation)
            }
            Expr::Evidence { value, bindings } => {
                let count = bindings.len().checked_add(1).ok_or(Failure::Resource)?;
                charge(budget, count)?;
                pending.try_reserve(count).map_err(|_| Failure::Resource)?;
                pending.push(*value);
                pending.extend(bindings.iter().map(|(_, _, argument)| *argument));
                SupportKind::Evidence
            }
            Expr::Slot => {
                let Some(role) = compiler.source_slot_role(expression, budget)? else {
                    return Ok(Err(Decline::UnknownSlot));
                };
                match role {
                    SlotRole::Metadata | SlotRole::Resource | SlotRole::Global { .. }
                    | SlotRole::Dictionary { .. } | SlotRole::Unbound => SupportKind::Terminal(role),
                    SlotRole::Lexical { .. } => return Ok(Err(Decline::UnsupportedSlot)),
                }
            }
            _ => return Ok(Err(Decline::UnsupportedTerminal)),
        };
        charge(budget, 1)?;
        visits.try_reserve(1).map_err(|_| Failure::Resource)?;
        visits.push(SupportVisit { expression, kind });
    }
    // Nothing publishes until the whole static closure has been retained.
    Ok(Ok(CaptureSupportPlan { graph, function, captures, visits, typed_calls }))
}

#[derive(Clone, Copy, Debug)]
pub(super) struct ExpressionClass {
    pub(super) expression: usize,
    pub(super) class: ProjectionClass,
}

// Conditional on the owner's FamilyGuard. The local Slot equation is Empty.
// A formal additionally receives its ORIGINAL actual route, and a saved
// capture additionally receives expression@0. Both fields may be present;
// the owner retains formal-before-capture installation and all capture seeds.
// A noncaptured global receives no global@0 route merely from its SlotRole.
#[derive(Clone, Copy, Debug)]
pub(super) struct SlotBaseline {
    pub(super) expression: usize,
    pub(super) role: SlotRole,
    pub(super) formal_ordinal: Option<usize>,
    pub(super) saved_capture_ordinal: Option<usize>,
    pub(super) class: ProjectionClass,
}

#[derive(Clone, Copy, Debug)]
pub(super) struct UniqueBodyGuard {
    pub(super) function: usize,
    pub(super) body: usize,
}

pub(super) struct QualifiedFactory<'g> {
    factory: usize,
    returned: usize,
    returned_body: usize,
    factory_support: CaptureSupportPlan<'g>,
    returned_support: CaptureSupportPlan<'g>,
    capture_seeds: &'g [usize],
    slot_baselines: Vec<SlotBaseline>,
    declared_capture_classes: Vec<ExpressionClass>,
    support_classes: Vec<ExpressionClass>,
}

impl<'g> QualifiedFactory<'g> {
    pub(super) fn factory(&self) -> usize { self.factory }
    pub(super) fn returned(&self) -> usize { self.returned }
    pub(super) fn factory_support(&self) -> &CaptureSupportPlan<'g> { &self.factory_support }
    pub(super) fn returned_support(&self) -> &CaptureSupportPlan<'g> { &self.returned_support }
    pub(super) fn capture_seeds(&self) -> &'g [usize] { self.capture_seeds }
    pub(super) fn slot_baselines(&self) -> &[SlotBaseline] { &self.slot_baselines }
    pub(super) fn declared_capture_classes(&self) -> &[ExpressionClass] { &self.declared_capture_classes }
    pub(super) fn support_classes(&self) -> &[ExpressionClass] { &self.support_classes }
    pub(super) fn unique_body_guards(&self) -> [UniqueBodyGuard; 2] {
        [UniqueBodyGuard { function: self.factory, body: self.returned },
            UniqueBodyGuard { function: self.returned, body: self.returned_body }]
    }

    fn dependency_count(&self) -> Result<usize, Failure> {
        self.factory_support.typed_calls.len().checked_add(self.returned_support.typed_calls.len())
            .ok_or(Failure::Resource)
    }

    fn dependency(&self, position: usize) -> Result<TypedCallRelation, Failure> {
        let first = self.factory_support.typed_calls.len();
        if position < first {
            self.factory_support.typed_calls.get(position).copied().ok_or(Failure::Invalid)
        } else {
            self.returned_support.typed_calls.get(position - first).copied().ok_or(Failure::Invalid)
        }
    }
}

// Static qualification only. It neither stages Type/Row substitution nor
// publishes a frame. Every coherent ordered dictionary tuple, exact live seed,
// full typed witness and saved q@0 stream stays with the original producer.
pub(super) struct QualifiedFamily<'g> {
    root: TypedCallRelation,
    relations: Vec<TypedCallRelation>,
    factories: Vec<QualifiedFactory<'g>>,
}

impl<'g> QualifiedFamily<'g> {
    pub(super) fn root(&self) -> TypedCallRelation { self.root }
    pub(super) fn relations(&self) -> &[TypedCallRelation] { &self.relations }
    pub(super) fn factories(&self) -> &[QualifiedFactory<'g>] { &self.factories }
}

fn typed_relation<'g>(graph: &'g Graph, compiler: &mut Compiler<'g>, expression: usize,
    budget: &mut TypeWorkBudget) -> Result<Result<TypedCallRelation, Decline>, Failure>
{
    if !compiler.compile_set(&[expression], budget)? {
        return Ok(Err(Decline::Recipe));
    }
    charge(budget, 1)?;
    let source = graph.expressions.get(expression).ok_or(Failure::Invalid)?;
    let prepared = compiler.prepared(expression).ok_or(Failure::Invalid)?;
    if !std::ptr::eq(prepared.source, source) { return Err(Failure::Invalid); }
    let RecipeTag::TypedCall { factory, body } = prepared.tag else {
        return Ok(Err(Decline::NotTypedCall));
    };
    if !compiler.raw_local_recipe(expression, budget)? {
        return Ok(Err(Decline::SourceWriters));
    }
    if compiler.prove_source_class(expression, budget)? != Some(ProjectionClass::Callable(body)) {
        return Ok(Err(Decline::SourceClass));
    }
    Ok(Ok(TypedCallRelation { expression, factory, body }))
}

fn slot_baseline(
    compiler: &Compiler<'_>, expression: usize, formals: &[usize], captures: &[usize],
    source_class: ProjectionClass, budget: &mut TypeWorkBudget,
) -> Result<Result<SlotBaseline, Decline>, Failure> {
    let Some(role) = compiler.fresh_raw_slot_role(expression, budget)? else {
        return Ok(Err(Decline::UnsupportedSlot));
    };
    charge(budget, formals.len().checked_add(captures.len()).ok_or(Failure::Resource)?)?;
    let formal_ordinal = formals.iter().position(|formal| *formal == expression);
    let saved_capture_ordinal = captures.iter().position(|capture| *capture == expression);
    let class = if formal_ordinal.is_some() {
        if !matches!(role, SlotRole::Metadata) || source_class != ProjectionClass::Metadata {
            return Ok(Err(Decline::SourceClass));
        }
        ProjectionClass::Metadata
    } else if saved_capture_ordinal.is_some() {
        source_class
    } else {
        // No local Slot atom, no matching F formal/capture, no writer in this
        // fresh raw Invoke. Global initialization and dictionary replacement
        // have distinct zero/Call destinations under the required guard.
        ProjectionClass::Empty
    };
    Ok(Ok(SlotBaseline { expression, role, formal_ordinal, saved_capture_ordinal, class }))
}

fn qualify_factory<'g>(
    graph: &'g Graph, compiler: &mut Compiler<'g>, relation: TypedCallRelation,
    budget: &mut TypeWorkBudget,
) -> Result<Result<QualifiedFactory<'g>, Decline>, Failure> {
    let TypedCallRelation { factory, body: returned, .. } = relation;
    charge(budget, 2)?;
    let Some(Expr::Function { parameters: formals, body, captures }) = graph.expressions.get(factory)
        else { return Err(Failure::Invalid); };
    if *body != returned { return Err(Failure::Invalid); }
    let Some(Expr::Function { body: returned_body, captures: declared, .. }) = graph.expressions.get(returned)
        else { return Err(Failure::Invalid); };
    for (function, body) in [(factory, returned), (returned, *returned_body)] {
        if compiler.unique_body_owner(body, budget)? != Some(function) {
            return Ok(Err(Decline::SharedBody));
        }
    }
    if !compiler.raw_returned_body(returned, budget)? {
        return Ok(Err(Decline::SourceWriters));
    }
    let factory_support = match prepare(graph, compiler, factory, budget)? {
        Ok(plan) => plan, Err(reason) => return Ok(Err(reason)),
    };
    let returned_support = match prepare(graph, compiler, returned, budget)? {
        Ok(plan) => plan, Err(reason) => return Ok(Err(reason)),
    };
    let mut slot_baselines = Vec::new();
    let mut support_classes = Vec::new();
    let mut seen = HashSet::new();
    // Include ALL F formals even when the returned capture projection ignores
    // one. Then follow original F and G support orders; keep one coordinate
    // entry without flattening their original operand/binding tuples.
    for expression in formals.iter().copied().chain(factory_support.visits.iter().map(|visit| visit.expression))
        .chain(returned_support.visits.iter().map(|visit| visit.expression))
    {
        charge(budget, 1)?;
        if seen.contains(&expression) { continue; }
        charge(budget, 1)?;
        seen.try_reserve(1).map_err(|_| Failure::Resource)?;
        seen.insert(expression);
        let Some(source_class) = compiler.prove_source_class(expression, budget)? else {
            return Ok(Err(Decline::SourceClass));
        };
        let class = if matches!(graph.expressions.get(expression), Some(Expr::Slot)) {
            let baseline = match slot_baseline(compiler, expression, formals, captures, source_class, budget)? {
                Ok(baseline) => baseline, Err(reason) => return Ok(Err(reason)),
            };
            let class = baseline.class;
            charge(budget, 1)?;
            slot_baselines.try_reserve(1).map_err(|_| Failure::Resource)?;
            slot_baselines.push(baseline);
            class
        } else {
            if !compiler.raw_local_recipe(expression, budget)? {
                return Ok(Err(Decline::SourceWriters));
            }
            source_class
        };
        charge(budget, 1)?;
        support_classes.try_reserve(1).map_err(|_| Failure::Resource)?;
        support_classes.push(ExpressionClass { expression, class });
    }
    charge(budget, declared.len())?;
    let mut declared_capture_classes = Vec::new();
    declared_capture_classes.try_reserve_exact(declared.len()).map_err(|_| Failure::Resource)?;
    for expression in declared {
        charge(budget, support_classes.len())?;
        let class = support_classes.iter().find(|entry| entry.expression == *expression)
            .copied().ok_or(Failure::Invalid)?;
        declared_capture_classes.push(class);
    }
    // Borrow the exact original F capture stream: order and repeated entries
    // remain authoritative, with no copied ordinal/constant-zero records.
    let capture_seeds = captures.as_slice();
    Ok(Ok(QualifiedFactory { factory, returned, returned_body: *returned_body,
        factory_support, returned_support, capture_seeds, slot_baselines,
        declared_capture_classes, support_classes }))
}

#[derive(Clone, Copy)]
struct FamilyWork { factory: usize, index: usize, next: usize }

// Validate every nested TypedCall's exact existing full witness relation and
// visit BOTH its F captures and returned G captures. Unlike Compiler's local
// Function shape, this DFS therefore cannot stop at an unchecked G capture
// dependency. Evidence binding arguments are included by prepare's traversal.
// Dictionary cuts can only stop that traversal earlier: every later lexical
// topology terminal occurs in the retained support closure. A replaced Slot
// is also recorded, but its selected dictionary equation remains owner work.
pub(super) fn prepare_family<'g>(
    graph: &'g Graph, compiler: &mut Compiler<'g>, rootq: usize,
    budget: &mut TypeWorkBudget,
) -> Result<Result<QualifiedFamily<'g>, Decline>, Failure> {
    let root = match typed_relation(graph, compiler, rootq, budget)? {
        Ok(relation) => relation, Err(reason) => return Ok(Err(reason)),
    };
    let first = match qualify_factory(graph, compiler, root, budget)? {
        Ok(factory) => factory, Err(reason) => return Ok(Err(reason)),
    };
    let mut factories = Vec::new();
    let mut relations = Vec::new();
    let mut states = HashMap::new(); // factory -> (index, DFS completed)
    let mut relation_seen = HashSet::new();
    let mut pending = Vec::new();
    charge(budget, 5)?;
    factories.try_reserve(1).map_err(|_| Failure::Resource)?;
    relations.try_reserve(1).map_err(|_| Failure::Resource)?;
    states.try_reserve(1).map_err(|_| Failure::Resource)?;
    relation_seen.try_reserve(1).map_err(|_| Failure::Resource)?;
    pending.try_reserve(1).map_err(|_| Failure::Resource)?;
    factories.push(first);
    relations.push(root);
    relation_seen.insert(root.expression);
    states.insert(root.factory, (0, false));
    pending.push(FamilyWork { factory: root.factory, index: 0, next: 0 });
    while let Some(work) = pending.last().copied() {
        charge(budget, 1)?;
        let factory = factories.get(work.index).ok_or(Failure::Invalid)?;
        if work.next == factory.dependency_count()? {
            charge(budget, 1)?;
            states.get_mut(&work.factory).ok_or(Failure::Invalid)?.1 = true;
            pending.pop();
            continue;
        }
        let next = factory.dependency(work.next)?;
        pending.last_mut().ok_or(Failure::Invalid)?.next += 1;
        let next = match typed_relation(graph, compiler, next.expression, budget)? {
            Ok(relation) => relation, Err(reason) => return Ok(Err(reason)),
        };
        charge(budget, 1)?;
        if !relation_seen.contains(&next.expression) {
            charge(budget, 2)?;
            relation_seen.try_reserve(1).map_err(|_| Failure::Resource)?;
            relations.try_reserve(1).map_err(|_| Failure::Resource)?;
            relation_seen.insert(next.expression);
            relations.push(next);
        }
        charge(budget, 1)?;
        if let Some(&(index, completed)) = states.get(&next.factory) {
            if factories.get(index).ok_or(Failure::Invalid)?.returned != next.body {
                return Err(Failure::Invalid);
            }
            if !completed { return Ok(Err(Decline::FactoryCycle)); }
            continue;
        }
        let next_factory = match qualify_factory(graph, compiler, next, budget)? {
            Ok(factory) => factory, Err(reason) => return Ok(Err(reason)),
        };
        charge(budget, 3)?;
        factories.try_reserve(1).map_err(|_| Failure::Resource)?;
        states.try_reserve(1).map_err(|_| Failure::Resource)?;
        pending.try_reserve(1).map_err(|_| Failure::Resource)?;
        let index = factories.len();
        factories.push(next_factory);
        states.insert(next.factory, (index, false));
        pending.push(FamilyWork { factory: next.factory, index, next: 0 });
    }
    Ok(Ok(QualifiedFamily { root, relations, factories }))
}
