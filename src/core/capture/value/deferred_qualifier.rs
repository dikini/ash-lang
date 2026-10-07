//! Static, conservative source-family qualification. This is preparation,
//! never authority to publish a frame or to skip an original occurrence.
//! The actual Call/Evidence visit must also authenticate its original context,
//! all writer equations, live/frozen boundary, and typed environment alternatives.

use std::collections::{HashMap, HashSet};
use super::{Atom, Expr, Failure, Graph, TypeWorkBudget, charge, copy_slice};
use super::deferred_frame::ProjectionClass;

pub(super) struct Family {
    classes: HashMap<usize, ProjectionClass>,
    factories: HashMap<usize, usize>,
    // Complete ORIGINAL ordered tuples are retained in Graph, never copied as
    // independently selected methods or trimmed to just captured positions.
    evidences: HashSet<usize>,
}

impl Family {
    pub(super) fn class(&self, expression: usize) -> Option<ProjectionClass> {
        self.classes.get(&expression).copied()
    }
    pub(super) fn factory(&self, application: usize) -> Option<usize> {
        self.factories.get(&application).copied()
    }
    pub(super) fn evidence(&self, expression: usize) -> bool {
        self.evidences.contains(&expression)
    }
}

fn combine(left: ProjectionClass, right: ProjectionClass) -> Option<ProjectionClass> {
    match (left, right) {
        (ProjectionClass::Empty, other) | (other, ProjectionClass::Empty) => Some(other),
        (left, right) if left == right => Some(left),
        _ => None,
    }
}

struct Roles {
    globals: HashMap<usize, usize>,
    ambiguous_globals: HashSet<usize>,
    assignments: HashSet<usize>,
    resources: HashSet<usize>,
    dictionary_inputs: HashMap<usize, Vec<usize>>,
}

impl Roles {
    fn new(graph: &Graph, budget: &mut TypeWorkBudget) -> Result<Self, Failure> {
        let mut result = Self { globals: HashMap::new(), ambiguous_globals: HashSet::new(),
            assignments: HashSet::new(), resources: HashSet::new(), dictionary_inputs: HashMap::new() };
        for &(slot, value) in &graph.globals {
            charge(budget, 1)?;
            result.globals.try_reserve(1).map_err(|_| Failure::Resource)?;
            if result.globals.insert(slot, value).is_some() {
                result.ambiguous_globals.try_reserve(1).map_err(|_| Failure::Resource)?;
                result.ambiguous_globals.insert(slot);
            }
        }
        // This is an immutable source-role inventory, not a traversal of old
        // contextual children. No current atom vector proves a writer absent.
        for expression in &graph.expressions {
            charge(budget, 1)?;
            match expression {
                Expr::Bind { binder, .. } => result.assign(*binder, budget)?,
                Expr::Recursive { bindings, .. } => {
                    for (binder, _) in bindings { result.assign(*binder, budget)?; }
                }
                Expr::Match { arms, .. } => {
                    for (bindings, _) in arms {
                        for (binder, _) in bindings { result.assign(*binder, budget)?; }
                    }
                }
                Expr::Handler { clauses, .. } => {
                    for clause in clauses {
                        result.assign(clause.input, budget)?;
                        for (binder, _) in &clause.bindings { result.assign(*binder, budget)?; }
                    }
                }
                Expr::Function { parameters, .. } => {
                    for parameter in parameters {
                        if !graph.metadata.contains_key(parameter) { result.assign(*parameter, budget)?; }
                    }
                }
                Expr::Resource { handle, identity, .. } => {
                    charge(budget, 2)?;
                    result.resources.try_reserve(2).map_err(|_| Failure::Resource)?;
                    result.resources.insert(*handle);
                    result.resources.insert(*identity);
                }
                _ => {}
            }
        }
        // For every exact evidence-port key retain all possible original
        // binding occurrences. Distinct method IDs/ports are never conflated.
        for expression in &graph.expressions {
            if let Expr::Evidence { bindings, .. } = expression {
                for (requirement, method, argument) in bindings {
                    charge(budget, graph.evidence.len() + 1)?;
                    for (key, port) in &graph.evidence {
                        if key == &(*requirement, *method) {
                            result.dictionary_inputs.try_reserve(1).map_err(|_| Failure::Resource)?;
                            let inputs = result.dictionary_inputs.entry(*port).or_default();
                            inputs.try_reserve(1).map_err(|_| Failure::Resource)?;
                            inputs.push(*argument);
                        }
                    }
                }
            }
        }
        Ok(result)
    }
    fn assign(&mut self, port: usize, budget: &mut TypeWorkBudget) -> Result<(), Failure> {
        charge(budget, 1)?;
        self.assignments.try_reserve(1).map_err(|_| Failure::Resource)?;
        self.assignments.insert(port);
        Ok(())
    }
}

// Only an unchanged, unique global factory can authorize positional pairing.
// The full typed witness checker authenticates complete Kinds and Type/Rows;
// shape or equal free-variable sets alone never establish this relation.
fn factory(graph: &Graph, roles: &Roles, call: usize, budget: &mut TypeWorkBudget)
    -> Result<Option<usize>, Failure>
{
    let Some(Expr::Call { function, type_application: true, .. }) = graph.expressions.get(call)
        else { return Ok(None); };
    let Some(Expr::Alias(global)) = graph.expressions.get(*function) else { return Ok(None); };
    if roles.ambiguous_globals.contains(global) || roles.assignments.contains(global) {
        return Ok(None);
    }
    let Some(&factory) = roles.globals.get(global) else { return Ok(None); };
    if super::typed_environment::check_global_factory_use(graph, call,
        Atom::Closure(factory, 0), budget)?.is_none() { return Ok(None); }
    Ok(Some(factory))
}

// This packet admits a finite source recipe inventory only. No production
// caller enables it yet. Unknown/opaque/multi-code/cyclic families decline as
// a whole before any runtime frame publication, rather than falling back late.
pub(super) fn prepare(graph: &Graph, root: usize, budget: &mut TypeWorkBudget)
    -> Result<Option<Family>, Failure>
{
    if graph.producers.len() != 1 { return Ok(None); }
    let roles = Roles::new(graph, budget)?;
    let mut family = Family { classes: HashMap::new(), factories: HashMap::new(), evidences: HashSet::new() };
    let mut pending = copy_slice(&[(root, false)], budget)?;
    let mut active = HashSet::new();
    while let Some((id, finish)) = pending.pop() {
        charge(budget, 1)?;
        if family.classes.contains_key(&id) { continue; }
        let Some(expression) = graph.expressions.get(id) else { return Ok(None); };
        if !finish {
            // Pay a possible dictionary namespace scan even when the port is
            // not a dictionary. Membership never comes from live emptiness.
            if matches!(expression, Expr::Slot) { charge(budget, graph.evidence.len())?; }
            if active.contains(&id) { return Ok(None); }
            active.try_reserve(1).map_err(|_| Failure::Resource)?;
            active.insert(id);
            let mut children = Vec::new();
            match expression {
                Expr::Scalar => {}
                Expr::Slot if graph.metadata.contains_key(&id) || roles.resources.contains(&id) => {}
                Expr::Slot if roles.globals.contains_key(&id) => {
                    if roles.ambiguous_globals.contains(&id) || roles.assignments.contains(&id) { return Ok(None); }
                    children = copy_slice(&[roles.globals[&id]], budget)?;
                }
                Expr::Slot if graph.evidence.iter().any(|(_, port)| *port == id) => {
                    if roles.assignments.contains(&id) || roles.globals.contains_key(&id) { return Ok(None); }
                    if let Some(inputs) = roles.dictionary_inputs.get(&id) { children = copy_slice(inputs, budget)?; }
                }
                Expr::Alias(value) => children = copy_slice(&[*value], budget)?,
                Expr::Merge(values) => children = copy_slice(values, budget)?,
                Expr::Function { captures, .. } => children = copy_slice(captures, budget)?,
                Expr::Call { arguments, type_application: true, .. } => {
                    let Some(factory) = factory(graph, &roles, id, budget)? else { return Ok(None); };
                    let Expr::Function { body, .. } = &graph.expressions[factory] else { return Ok(None); };
                    charge(budget, 1)?;
                    family.factories.try_reserve(1).map_err(|_| Failure::Resource)?;
                    family.factories.insert(id, factory);
                    children = copy_slice(arguments, budget)?;
                    children.try_reserve(2).map_err(|_| Failure::Resource)?;
                    children.push(factory);
                    children.push(*body);
                }
                Expr::Evidence { value, bindings } => {
                    // The existing typed producer supplied this entire tuple.
                    // The first bounded family permits one requirement, with
                    // all original methods retained in their original order.
                    let Some((requirement, _, _)) = bindings.first() else { return Ok(None); };
                    charge(budget, bindings.len())?;
                    if bindings.iter().any(|(other, _, _)| other != requirement) { return Ok(None); }
                    family.evidences.try_reserve(1).map_err(|_| Failure::Resource)?;
                    family.evidences.insert(id);
                    children.try_reserve(bindings.len() + 1).map_err(|_| Failure::Resource)?;
                    children.push(*value);
                    children.extend(bindings.iter().map(|(_, _, argument)| *argument));
                }
                _ => return Ok(None),
            }
            charge(budget, children.len() + 1)?;
            pending.try_reserve(children.len() + 1).map_err(|_| Failure::Resource)?;
            pending.push((id, true));
            pending.extend(children.into_iter().rev().map(|child| (child, false)));
            continue;
        }
        let class = match expression {
            Expr::Scalar => ProjectionClass::Metadata,
            Expr::Slot if graph.metadata.contains_key(&id) || roles.resources.contains(&id) => ProjectionClass::Metadata,
            Expr::Slot if roles.globals.contains_key(&id) => *family.classes.get(&roles.globals[&id]).ok_or(Failure::Invalid)?,
            Expr::Slot => {
                let mut class = ProjectionClass::Empty;
                if let Some(inputs) = roles.dictionary_inputs.get(&id) {
                    for input in inputs {
                        charge(budget, 1)?;
                        let Some(next) = combine(class, *family.classes.get(input).ok_or(Failure::Invalid)?) else { return Ok(None); };
                        class = next;
                    }
                }
                class
            }
            Expr::Alias(value) => *family.classes.get(value).ok_or(Failure::Invalid)?,
            Expr::Merge(values) => {
                for value in values {
                    charge(budget, 1)?;
                    if !matches!(family.classes.get(value), Some(ProjectionClass::Empty | ProjectionClass::Metadata)) { return Ok(None); }
                }
                ProjectionClass::Metadata
            }
            Expr::Function { .. } => ProjectionClass::Callable(id),
            Expr::Call { .. } => {
                let factory = family.factories[&id];
                let Expr::Function { body, .. } = &graph.expressions[factory] else { return Err(Failure::Invalid); };
                match family.classes.get(body) {
                    Some(ProjectionClass::Callable(code)) if code == body => ProjectionClass::Callable(*code),
                    _ => return Ok(None),
                }
            }
            Expr::Evidence { value, .. } => match family.classes.get(value) {
                Some(ProjectionClass::Callable(code)) => ProjectionClass::Callable(*code),
                _ => return Ok(None),
            },
            _ => return Ok(None),
        };
        charge(budget, 1)?;
        family.classes.try_reserve(1).map_err(|_| Failure::Resource)?;
        family.classes.insert(id, class);
        active.remove(&id);
    }
    Ok(Some(family))
}
