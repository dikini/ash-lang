//! Bounded inference of request-carried obligations from typed Core.
//!
//! Stored ordinary values carry no obligation. A portable callable summary
//! retains the complete control graph, including exact handler instances, so
//! importing and specializing it cannot erase newly matching handlers. This
//! graph is finite by Core construction. Abandonment queries use finite frame
//! allocation sites and live/consumed owner occurrences; they run only when
//! local or retained imported control contains a discard. Resume-only export
//! needs no abandonment query and publishes no unproved permission.

use std::{collections::HashMap, sync::Arc};

mod control;
use control::{Analysis, Clause, Control, copy_slice, query_required};

use super::{
    CoreBuilder, NodeId, PureComputation, PureExprKind, PureValue,
    dialect::{CoreOperationFamily, StoredNode},
    effect::{EffectOperation, clone_effect_instance_with_budget},
};
use crate::{
    resolved::BinderId,
    source::Span,
    types::{
        EffectInstance, Type, TypeVariableId, TypeWorkBudget, clone_type_with_budget,
        discard_type_iteratively, same_type_with_budget,
    },
};

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct Value {
    targets: Vec<usize>,
    unknown: bool,
}

/// A compiler-owned, immutable callable graph retained with an authenticated
/// defining binder. Graph edges are indices, never scratch-arena references.
#[derive(Clone, Debug)]
pub(crate) struct CaptureValueSummary {
    graph: Option<Arc<SummaryGraph>>,
    value: Value,
}

impl Default for CaptureValueSummary {
    fn default() -> Self {
        Self {
            graph: None,
            value: Value {
                unknown: true,
                ..Value::default()
            },
        }
    }
}

impl PartialEq for CaptureValueSummary {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
            && match (&self.graph, &other.graph) {
                (None, None) => true,
                (Some(a), Some(b)) => Arc::ptr_eq(a, b),
                _ => false,
            }
    }
}
impl Eq for CaptureValueSummary {}

impl CaptureValueSummary {
    pub(crate) fn clone_with_budget(&self, budget: &mut TypeWorkBudget) -> Result<Self, ()> {
        if self.graph.is_none() {
            return Ok(Self::default());
        }
        Ok(Self {
            graph: self.graph.as_ref().map(Arc::clone),
            value: self.value.copy(budget).map_err(|_| ())?,
        })
    }

    pub(crate) fn is_retained(&self) -> bool {
        self.graph.is_some()
    }

    pub(crate) fn same_with_budget(
        &self,
        other: &Self,
        budget: &mut TypeWorkBudget,
    ) -> Result<bool, ()> {
        if self.graph.is_some() || other.graph.is_some() {
            budget.charge(self.value.targets.len() + other.value.targets.len() + 1)?;
        }
        Ok(self == other)
    }

    // Precharge carrier scans, including control positions that yield nothing.
    // Consumers separately budget their traversal of the yielded types.
    pub(crate) fn types<'a>(
        &'a self,
        budget: &mut TypeWorkBudget,
    ) -> Result<impl Iterator<Item = &'a Type> + use<'a>, ()> {
        if let Some(graph) = &self.graph {
            budget.charge(graph.callables.len())?;
            budget.charge(graph.types.0.len())?;
            budget.charge(graph.code.len())?;
        }
        Ok(self.graph.iter().flat_map(|graph| {
            graph
                .callables
                .iter()
                .map(|callable| &callable.ty)
                .chain(graph.types.0.iter())
                .chain(
                    graph
                        .code
                        .iter()
                        .filter_map(|code| match code {
                            Control::Request(request)
                            | Control::Handler {
                                effect: request, ..
                            } => Some(request),
                            _ => None,
                        })
                        .flat_map(|request| {
                            request.effect.iter().flat_map(|effect| effect.arguments())
                        }),
                )
        }))
    }

    // Each alias scans its shared graph again, so each scan is charged here.
    pub(crate) fn effects<'a>(
        &'a self,
        budget: &mut TypeWorkBudget,
    ) -> Result<impl Iterator<Item = crate::types::EffectId> + use<'a>, ()> {
        if let Some(graph) = &self.graph {
            budget.charge(graph.code.len())?;
        }
        Ok(self
            .graph
            .iter()
            .flat_map(|graph| graph.code.iter())
            .filter_map(|code| match code {
                Control::Request(request)
                | Control::Handler {
                    effect: request, ..
                } => request.effect.as_ref().map(|effect| effect.effect()),
                _ => None,
            }))
    }
}

#[derive(Debug)]
struct SummaryGraph {
    callables: Vec<Callable>,
    code: Vec<Control>,
    types: TypeArguments,
}

#[derive(Debug)]
struct Callable {
    body: usize,
    ty: Type,
    result: Value,
}

impl Drop for Callable {
    fn drop(&mut self) {
        discard_type_iteratively(std::mem::replace(&mut self.ty, Type::Unit));
    }
}

struct ImportedCallables<'a> {
    callables: Vec<(&'a Callable, usize, usize)>,
    graphs: Vec<(&'a SummaryGraph, usize, usize, usize)>,
    values: HashMap<BinderId, Value>,
}

impl<'a> ImportedCallables<'a> {
    fn new(
        imports: &[(BinderId, &'a CaptureValueSummary)],
        local_count: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<Self, Failure> {
        let mut result = Self {
            callables: Vec::new(),
            graphs: Vec::new(),
            values: HashMap::new(),
        };
        let mut code_count = local_count + 1;
        let mut type_count = 0;
        for (binder, summary) in imports {
            charge(budget, result.graphs.len() + 1)?;
            let mut offset = 0;
            if let Some(graph) = &summary.graph {
                let previous = result
                    .graphs
                    .iter()
                    .find(|(old, _, _, _)| std::ptr::eq(*old, graph.as_ref()));
                if let Some((_, found, _, _)) = previous {
                    offset = *found;
                } else {
                    offset = local_count + result.callables.len();
                    charge(
                        budget,
                        graph.callables.len() + graph.code.len() + graph.types.0.len() + 1,
                    )?;
                    result
                        .callables
                        .try_reserve(graph.callables.len())
                        .map_err(|_| Failure::Resource)?;
                    result.callables.extend(
                        graph
                            .callables
                            .iter()
                            .map(|callable| (callable, offset, code_count)),
                    );
                    result
                        .graphs
                        .try_reserve(1)
                        .map_err(|_| Failure::Resource)?;
                    result.graphs.push((graph, offset, code_count, type_count));
                    code_count += graph.code.len();
                    type_count += graph.types.0.len();
                }
            }
            let mut value = summary.value.copy(budget)?;
            for target in &mut value.targets {
                *target += offset;
            }
            result
                .values
                .try_reserve(1)
                .map_err(|_| Failure::Resource)?;
            result.values.insert(*binder, value);
        }
        Ok(result)
    }

    fn get(&self, target: usize, local_count: usize) -> Result<(&'a Callable, usize), Failure> {
        self.callables
            .get(target.checked_sub(local_count).ok_or(Failure::Invalid)?)
            .map(|(callable, offset, _)| (*callable, *offset))
            .ok_or(Failure::Invalid)
    }
}
impl Value {
    fn join(&mut self, other: &Self, budget: &mut TypeWorkBudget) -> Result<(), Failure> {
        charge(budget, other.targets.len() + 1)?;
        self.unknown |= other.unknown;
        for target in &other.targets {
            charge(budget, self.targets.len())?;
            if !self.targets.contains(target) {
                self.targets.try_reserve(1).map_err(|_| Failure::Resource)?;
                self.targets.push(*target);
            }
        }
        charge(
            budget,
            self.targets
                .len()
                .saturating_mul(self.targets.len().max(1).ilog2() as usize + 1),
        )?;
        self.targets.sort_unstable();
        Ok(())
    }

    fn copy(&self, budget: &mut TypeWorkBudget) -> Result<Self, Failure> {
        charge(budget, self.targets.len() + 1)?;
        let mut targets = Vec::new();
        targets
            .try_reserve_exact(self.targets.len())
            .map_err(|_| Failure::Resource)?;
        targets.extend_from_slice(&self.targets);
        Ok(Self {
            targets,
            unknown: self.unknown,
        })
    }
}

#[derive(Clone, Debug)]
struct Request {
    // None denotes admitted requests from an opaque open row.
    effect: Option<Arc<EffectInstance>>,
    ambiguous_instance: bool,
    source: Span,
}

impl Request {
    fn unknown(source: Span) -> Self {
        Self {
            effect: None,
            ambiguous_instance: false,
            source,
        }
    }

    fn effect(
        effect: &EffectInstance,
        source: Span,
        budget: &mut TypeWorkBudget,
    ) -> Result<Self, Failure> {
        Ok(Self {
            effect: Some(Arc::new(
                clone_effect_instance_with_budget(effect, budget).map_err(|_| Failure::Resource)?,
            )),
            ..Self::unknown(source)
        })
    }

    fn copy(&self, budget: &mut TypeWorkBudget) -> Result<Self, Failure> {
        charge(budget, 1)?;
        Ok(Self {
            effect: self.effect.as_ref().map(Arc::clone),
            ambiguous_instance: self.ambiguous_instance,
            source: self.source,
        })
    }
}

#[derive(Default)]
struct Substitutions(HashMap<TypeVariableId, Type>);

#[derive(Debug)]
struct TypeArguments(Vec<Type>);

impl TypeArguments {
    fn into_boxed_slice(mut self) -> Box<[Type]> {
        std::mem::take(&mut self.0).into_boxed_slice()
    }
}

impl Substitutions {
    fn insert(&mut self, variable: TypeVariableId, ty: Type) {
        if let Some(displaced) = self.0.insert(variable, ty) {
            discard_type_iteratively(displaced);
        }
    }
}

impl Drop for TypeArguments {
    fn drop(&mut self) {
        for ty in self.0.drain(..) {
            discard_type_iteratively(ty);
        }
    }
}

impl Drop for Substitutions {
    fn drop(&mut self) {
        for (_, ty) in self.0.drain() {
            discard_type_iteratively(ty);
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct UnsafeDiscard {
    pub(crate) node: usize,
    pub(crate) discard: Span,
    pub(crate) request: Span,
    pub(crate) owner: Option<Span>,
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum Failure {
    Resource,
    Invalid,
    Unsafe(UnsafeDiscard),
}

fn charge(budget: &mut TypeWorkBudget, count: usize) -> Result<(), Failure> {
    budget.charge(count).map_err(|()| Failure::Resource)
}

fn index(node: NodeId) -> usize {
    node.value() as usize
}

fn same_effect(
    a: Option<&EffectInstance>,
    b: Option<&EffectInstance>,
    budget: &mut TypeWorkBudget,
) -> Result<bool, Failure> {
    match (a, b) {
        (None, None) => Ok(true),
        (Some(a), Some(b)) => {
            charge(budget, 1)?;
            if a.effect() != b.effect() || a.arguments().len() != b.arguments().len() {
                return Ok(false);
            }
            for (a, b) in a.arguments().iter().zip(b.arguments()) {
                if !same_type_with_budget(a, b, budget).map_err(|()| Failure::Resource)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        _ => Ok(false),
    }
}

fn compile<F: CoreOperationFamily>(
    nodes: &[StoredNode<F>],
    values: &[Value],
    imported: &ImportedCallables<'_>,
    operation: fn(&F::Kind) -> Option<&EffectOperation>,
    budget: &mut TypeWorkBudget,
) -> Result<(SummaryGraph, Vec<usize>), Failure> {
    let mut graph = SummaryGraph {
        callables: Vec::new(),
        code: Vec::new(),
        types: TypeArguments(Vec::new()),
    };
    charge(budget, nodes.len() + 1)?;
    graph
        .code
        .try_reserve(nodes.len() + 1)
        .map_err(|_| Failure::Resource)?;
    graph.code.resize_with(nodes.len() + 1, || Control::Return);
    graph
        .callables
        .try_reserve(nodes.len() + imported.callables.len())
        .map_err(|_| Failure::Resource)?;
    for _ in nodes {
        graph.callables.push(Callable {
            body: 0,
            ty: Type::Unit,
            result: Value::default(),
        });
    }
    for (import, target_offset, code_offset, type_offset) in &imported.graphs {
        graph
            .code
            .try_reserve(import.code.len())
            .map_err(|_| Failure::Resource)?;
        for code in &import.code {
            graph
                .code
                .push(code.copy(*code_offset, *target_offset, *type_offset, budget)?);
        }
        graph
            .types
            .0
            .try_reserve(import.types.0.len())
            .map_err(|_| Failure::Resource)?;
        for ty in &import.types.0 {
            graph
                .types
                .0
                .push(clone_type_with_budget(ty, budget).map_err(|_| Failure::Resource)?);
        }
        for callable in &import.callables {
            let mut result = callable.result.copy(budget)?;
            for target in &mut result.targets {
                *target += target_offset;
            }
            graph.callables.push(Callable {
                body: callable.body + code_offset,
                ty: clone_type_with_budget(&callable.ty, budget).map_err(|_| Failure::Resource)?,
                result,
            });
        }
    }
    let mut owners = HashMap::new();
    for node in nodes {
        if let Some(EffectOperation::Handler(handler)) = operation(&node.kind) {
            for clause in handler.clauses() {
                owners.try_reserve(1).map_err(|_| Failure::Resource)?;
                owners.insert((handler.id(), clause.resume()), graph.code.len());
                graph.code.try_reserve(1).map_err(|_| Failure::Resource)?;
                graph.code.push(Control::Return);
            }
        }
    }
    let mut roots = Vec::new();
    let mut children = std::collections::HashSet::new();
    for (id, node) in nodes.iter().enumerate() {
        charge(budget, 1)?;
        let source = node.origin.as_ref().ok_or(Failure::Invalid)?.primary_span();
        let code = match F::pure(&node.kind) {
            Some(PureExprKind::Value(PureValue::Function(function))) => {
                let result = values[index(function.body())].copy(budget)?;
                graph.callables[id] = Callable {
                    body: index(function.body()) + 1,
                    ty: clone_type_with_budget(&node.ty, budget).map_err(|_| Failure::Resource)?,
                    result,
                };
                roots.try_reserve(1).map_err(|_| Failure::Resource)?;
                roots.push(index(function.body()) + 1);
                Control::Return
            }
            Some(PureExprKind::Computation(PureComputation::Match(matching))) => {
                let mut arms = Vec::new();
                arms.try_reserve(matching.arms().len())
                    .map_err(|_| Failure::Resource)?;
                for arm in matching.arms() {
                    arms.push(index(arm.body()) + 1);
                }
                graph.code.try_reserve(1).map_err(|_| Failure::Resource)?;
                let branch = graph.code.len();
                graph.code.push(Control::Choice(arms));
                Control::Sequence(copy_slice(
                    &[index(matching.scrutinee()) + 1, branch],
                    budget,
                )?)
            }
            Some(PureExprKind::Computation(pure)) => {
                let mut sequence = Vec::new();
                sequence
                    .try_reserve(F::child_count(&node.kind) + 1)
                    .map_err(|_| Failure::Resource)?;
                for ordinal in 0..F::child_count(&node.kind) {
                    sequence
                        .push(index(F::child_at(&node.kind, ordinal).ok_or(Failure::Invalid)?) + 1);
                }
                if let PureComputation::Apply(application) = pure {
                    let actual = index(application.function());
                    graph
                        .types
                        .0
                        .try_reserve(1)
                        .map_err(|_| Failure::Resource)?;
                    let ty = graph.types.0.len();
                    graph.types.0.push(
                        clone_type_with_budget(&nodes[actual].ty, budget)
                            .map_err(|_| Failure::Resource)?,
                    );
                    graph.code.try_reserve(1).map_err(|_| Failure::Resource)?;
                    sequence.push(graph.code.len());
                    graph.code.push(Control::Call {
                        value: values[actual].copy(budget)?,
                        ty,
                        source,
                    });
                }
                Control::Sequence(sequence)
            }
            _ => match operation(&node.kind) {
                Some(EffectOperation::Request(request)) => {
                    graph.code.try_reserve(1).map_err(|_| Failure::Resource)?;
                    let perform = graph.code.len();
                    graph.code.push(Control::Request(Request::effect(
                        request.effect(),
                        source,
                        budget,
                    )?));
                    Control::Sequence(copy_slice(
                        &[index(request.operand()) + 1, perform],
                        budget,
                    )?)
                }
                Some(EffectOperation::Resume(resume)) => Control::Resume {
                    owner: *owners
                        .get(&(resume.handler(), resume.owner()))
                        .ok_or(Failure::Invalid)?,
                    value: index(resume.value()) + 1,
                },
                Some(EffectOperation::Discard(discard)) => Control::Discard {
                    owner: *owners
                        .get(&(discard.handler(), discard.owner()))
                        .ok_or(Failure::Invalid)?,
                    node: id,
                    source,
                },
                Some(EffectOperation::Handler(handler)) => {
                    let mut clauses = Vec::new();
                    clauses
                        .try_reserve(handler.clauses().len())
                        .map_err(|_| Failure::Resource)?;
                    for clause in handler.clauses() {
                        clauses.push(Clause {
                            body: index(clause.body()) + 1,
                            owner: owners[&(handler.id(), clause.resume())],
                            source: clause.origin().primary_span(),
                        });
                    }
                    Control::Handler {
                        body: index(handler.body()) + 1,
                        effect: Request::effect(handler.effect(), source, budget)?,
                        clauses,
                    }
                }
                None => Control::Return,
            },
        };
        graph.code[id + 1] = code;
        for ordinal in 0..F::child_count(&node.kind) {
            children.try_reserve(1).map_err(|_| Failure::Resource)?;
            children.insert(index(F::child_at(&node.kind, ordinal).ok_or(Failure::Invalid)?) + 1);
        }
    }
    loop {
        let mut changed = false;
        for id in 1..graph.code.len() {
            charge(budget, 1)?;
            if let Control::Sequence(children) | Control::Choice(children) = &graph.code[id] {
                charge(budget, children.len())?;
                if children
                    .iter()
                    .all(|child| matches!(graph.code[*child], Control::Return))
                {
                    graph.code[id] = Control::Return;
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    for id in 1..=nodes.len() {
        if !children.contains(&id) {
            roots.try_reserve(1).map_err(|_| Failure::Resource)?;
            roots.push(id);
        }
    }
    Ok((graph, roots))
}

pub(crate) fn check_builder<F: CoreOperationFamily>(
    builder: &CoreBuilder<F>,
    globals: &[(BinderId, NodeId)],
    imports: &[(BinderId, &CaptureValueSummary)],
    operation: fn(&F::Kind) -> Option<&EffectOperation>,
    budget: &mut TypeWorkBudget,
) -> Result<Vec<CaptureValueSummary>, Failure> {
    check_nodes(&builder.nodes, globals, imports, operation, budget)
}

pub(super) fn check_nodes<F: CoreOperationFamily>(
    nodes: &[StoredNode<F>],
    globals: &[(BinderId, NodeId)],
    imports: &[(BinderId, &CaptureValueSummary)],
    operation: fn(&F::Kind) -> Option<&EffectOperation>,
    budget: &mut TypeWorkBudget,
) -> Result<Vec<CaptureValueSummary>, Failure> {
    charge(budget, nodes.len() + globals.len())?;
    let mut bindings = HashMap::new();
    bindings
        .try_reserve(globals.len())
        .map_err(|_| Failure::Resource)?;
    bindings.extend(globals.iter().map(|(binder, node)| (*binder, index(*node))));
    let imported = ImportedCallables::new(imports, nodes.len(), budget)?;
    let mut has_discard = false;
    for node in nodes {
        has_discard |= matches!(operation(&node.kind), Some(EffectOperation::Discard(_)));
        match F::pure(&node.kind) {
            Some(PureExprKind::Computation(PureComputation::Bind(binding))) => {
                bindings.try_reserve(1).map_err(|_| Failure::Resource)?;
                bindings.insert(binding.binder().id(), index(binding.initializer()));
            }
            Some(PureExprKind::Computation(PureComputation::RecursiveBind(binding))) => {
                charge(budget, binding.members().len())?;
                bindings
                    .try_reserve(binding.members().len())
                    .map_err(|_| Failure::Resource)?;
                for member in binding.members() {
                    bindings.insert(member.binder().id(), index(member.initializer()));
                }
            }
            _ => {}
        }
    }

    // Resume-only final Core needs no abandonment proof. Module publication
    // still requests roots, because a caller may install a discarding handler.
    if !has_discard && globals.is_empty() {
        return Ok(Vec::new());
    }

    // First solve finite value references. No request conclusion is made from
    // an unfinished recursive dependency.
    let mut values = Vec::new();
    values
        .try_reserve_exact(nodes.len())
        .map_err(|_| Failure::Resource)?;
    values.resize_with(nodes.len(), Value::default);
    loop {
        let mut changed = false;
        for (id, node) in nodes.iter().enumerate() {
            charge(budget, 1)?;
            let mut value = Value::default();
            match F::pure(&node.kind) {
                Some(PureExprKind::Value(PureValue::Function(_))) => {
                    value
                        .targets
                        .try_reserve(1)
                        .map_err(|_| Failure::Resource)?;
                    value.targets.push(id);
                }
                Some(PureExprKind::Variable(variable)) => {
                    value = match bindings.get(&variable.binder()) {
                        Some(target) => values[*target].copy(budget)?,
                        None => match imported.values.get(&variable.binder()) {
                            Some(value) => value.copy(budget)?,
                            None => Value {
                                unknown: true,
                                ..Value::default()
                            },
                        },
                    };
                }
                Some(PureExprKind::Computation(computation)) => match computation {
                    PureComputation::Bind(binding) => {
                        value = values[index(binding.body())].copy(budget)?
                    }
                    PureComputation::RecursiveBind(binding) => {
                        value = values[index(binding.body())].copy(budget)?
                    }
                    PureComputation::TypeAbstraction(abstraction) => {
                        value = values[index(abstraction.body())].copy(budget)?
                    }
                    PureComputation::TypeApplication(application) => {
                        value = values[index(application.function())].copy(budget)?
                    }
                    PureComputation::LocalNominalScope(scope) => {
                        value = values[index(scope.body())].copy(budget)?
                    }
                    PureComputation::NewtypeConversion(conversion) => {
                        value = values[index(conversion.child())].copy(budget)?
                    }
                    PureComputation::Match(matching) => {
                        for arm in matching.arms() {
                            value.join(&values[index(arm.body())], budget)?;
                        }
                    }
                    PureComputation::Apply(application) => {
                        let callee = &values[index(application.function())];
                        value.unknown = callee.unknown;
                        for target in &callee.targets {
                            if *target >= nodes.len() {
                                let (callable, offset) = imported.get(*target, nodes.len())?;
                                let mut result = callable.result.copy(budget)?;
                                for target in &mut result.targets {
                                    *target += offset;
                                }
                                value.join(&result, budget)?;
                                continue;
                            }
                            let Some(PureExprKind::Value(PureValue::Function(function))) =
                                F::pure(&nodes[*target].kind)
                            else {
                                return Err(Failure::Invalid);
                            };
                            value.join(&values[index(function.body())], budget)?;
                        }
                    }
                    _ => {}
                },
                _ => match operation(&node.kind) {
                    Some(EffectOperation::Handler(handler)) => {
                        value.join(&values[index(handler.body())], budget)?;
                        for clause in handler.clauses() {
                            value.join(&values[index(clause.body())], budget)?;
                        }
                    }
                    Some(EffectOperation::Request(_) | EffectOperation::Resume(_)) => {
                        value.unknown = true
                    }
                    _ => {}
                },
            }
            charge(budget, values[id].targets.len() + value.targets.len())?;
            if values[id] != value {
                values[id] = value;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    let (graph, roots) = compile(nodes, &values, &imported, operation, budget)?;
    charge(budget, graph.code.len())?;
    if graph
        .code
        .iter()
        .any(|code| matches!(code, Control::Discard { .. }))
    {
        let mut queries = Vec::new();
        for root in roots {
            if query_required(&graph, root, budget)? {
                queries.try_reserve(1).map_err(|_| Failure::Resource)?;
                queries.push(root);
            }
        }
        let mut analysis = Analysis::new(&graph, budget)?;
        analysis.check(&queries, budget)?;
    }
    let graph = Arc::new(graph);
    let mut summaries = Vec::new();
    summaries
        .try_reserve(globals.len())
        .map_err(|_| Failure::Resource)?;
    for (_, node) in globals {
        summaries.push(CaptureValueSummary {
            graph: Some(Arc::clone(&graph)),
            value: values[index(*node)].copy(budget)?,
        });
    }
    Ok(summaries)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        source::{ByteRange, SourceFile},
        types::EffectRow,
    };

    fn checked_core() -> (
        super::super::UnvalidatedEffectProgram,
        SourceFile,
        BinderId,
        BinderId,
    ) {
        let text = concat!(
            "effect A {\nask : Unit -> Unit\n}\neffect B {\nask : Unit -> Unit\n}\n",
            "good : Unit -> Unit ! {B}\ngood () = perform B.ask ()\n",
            "bad : Unit -> Unit ! {B}\nbad () = handle (perform A.ask ()) with A {\nask ignored => {\nlet _ = perform B.ask ()\nresume ()\n}\n}\n",
            "main : Unit -> Unit\nmain () = handle (good ()) with B {\nask ignored => discard\n}\n",
        );
        checked_core_text(text)
    }

    fn checked_core_text(
        text: &str,
    ) -> (
        super::super::UnvalidatedEffectProgram,
        SourceFile,
        BinderId,
        BinderId,
    ) {
        use crate::{
            elaborate::{EffectElaborator, check_module, link_modules},
            evidence_validation::validate_interface_evidence,
            module::{ModuleRoots, load_module_graph},
            resolve::resolve_module,
        };
        let source_identity = SourceFile::new("capture-test-id", "").unwrap().id().value();
        let path = std::env::temp_dir().join(format!(
            "ash-capture-{}-{source_identity}.ash",
            std::process::id()
        ));
        std::fs::write(&path, text).unwrap();
        let loaded = load_module_graph(&path, &ModuleRoots::empty());
        std::fs::remove_file(path).unwrap();
        let graph = loaded.unwrap();
        let module = graph.module(graph.entry()).unwrap();
        let checked = check_module(resolve_module(module, &[]).unwrap()).unwrap();
        let good = checked
            .schemes()
            .iter()
            .find(|scheme| scheme.spelling == "good")
            .unwrap()
            .binder;
        let bad = checked
            .schemes()
            .iter()
            .find(|scheme| scheme.spelling == "bad")
            .unwrap()
            .binder;
        let linked =
            validate_interface_evidence(link_modules(vec![checked], graph.entry()).unwrap())
                .unwrap();
        let mut elaborator = EffectElaborator::for_module_program(&linked).unwrap();
        let root = elaborator
            .synthesize_effect_module_program(&linked)
            .unwrap()
            .node;
        (
            elaborator.finish(root).unwrap(),
            module.source().clone(),
            good,
            bad,
        )
    }

    #[test]
    fn request_identity_is_independent_of_shared_core_origins() {
        use super::super::{EffectExprKind, validate_effect};
        let (mut core, source, _, _) = checked_core_text(concat!(
            "effect A {\nask : Unit -> Unit\n}\neffect B {\nask : Unit -> Unit\n}\neffect C {\nask : Unit -> Unit\n}\n",
            "good : Unit -> Unit ! {B}\ngood () = perform B.ask ()\nbad : Unit -> Unit ! {B}\nbad () = perform B.ask ()\n",
            "main : Unit -> Unit\nmain () = handle (handle (handle (perform C.ask ()) with C {\n",
            "ask ignored => {\nlet _ = perform B.ask ()\nlet _ = resume ()\nlet _ = perform A.ask ()\nperform B.ask ()\n}\n",
            "}) with A {\nask ignored => handle ({\nlet _ = resume ()\nperform B.ask ()\n}) with B {\nask ignored => discard\n}\n}) with B {\nask ignored => resume ()\n}\n",
        ));
        let origin = core
            .nodes
            .iter()
            .find(|node| {
                matches!(
                    node.kind,
                    EffectExprKind::Operation(EffectOperation::Request(_))
                )
            })
            .unwrap()
            .origin
            .clone();
        let mut sites = 0;
        for node in &mut core.nodes {
            if matches!(
                node.kind,
                EffectExprKind::Operation(EffectOperation::Request(_))
            ) {
                node.origin = origin.clone();
                sites += 1;
            }
        }
        assert!(sites >= 5);
        validate_effect(core, &[&source])
            .expect("shared diagnostic provenance cannot merge suspension sites");
    }

    #[test]
    fn final_core_recomputes_capture_after_same_typed_call_target_tampering() {
        use super::super::{
            EffectExprKind, validate::ValidationReason, validate_effect, variable::VariableNode,
        };
        let (core, source, _, _) = checked_core();
        validate_effect(core, &[&source]).expect("honest checked helper is safe");
        let (mut core, source, good, bad) = checked_core();
        let mut replacements = 0;
        for node in &mut core.nodes {
            if matches!(&node.kind, EffectExprKind::Pure(PureExprKind::Variable(variable)) if variable.binder() == good)
            {
                node.kind = EffectExprKind::Pure(PureExprKind::Variable(VariableNode::new(bad)));
                replacements += 1;
            }
        }
        assert_eq!(replacements, 1);
        let error = validate_effect(core, &[&source])
            .expect_err("same type cannot conceal a changed capture summary");
        assert_eq!(error.reason(), ValidationReason::DiscardUnsafe);
    }

    #[test]
    fn raw_core_rejects_skipped_completion_and_restored_live_owners() {
        use crate::{
            core::{ValidationReason, validate_effect},
            elaborate::{EffectElaborator, TypeContext},
            module::{ModuleRoots, load_module_graph},
            resolve::resolve_module,
            resolved::ResolvedDefinitionKind,
        };
        for body in [
            "handle (perform A.ask ()) with A {\nask ignored => {\nlet _ = handle ({\nlet _ = perform B.ask ()\nresume ()\n}) with B {\nask ignored => discard\n}\n()\n}\n}",
            "handle (handle (handle (perform C.ask ()) with C {\nask ignored => {\nlet _ = perform A.ask ()\nlet _ = perform B.ask ()\nresume ()\n}\n}) with A {\nask ignored => handle ({\nlet _ = resume ()\nperform B.ask ()\n}) with B {\nask ignored => discard\n}\n}) with B {\nask ignored => resume ()\n}",
        ] {
            let text = format!(
                "effect A {{\nask : Unit -> Unit\n}}\neffect B {{\nask : Unit -> Unit\n}}\neffect C {{\nask : Unit -> Unit\n}}\nmain : Unit -> Unit\nmain () = {body}\n"
            );
            let unique = SourceFile::new("raw-capture-id", "").unwrap().id().value();
            let path = std::env::temp_dir().join(format!(
                "ash-raw-capture-{}-{unique}.ash",
                std::process::id()
            ));
            std::fs::write(&path, text).unwrap();
            let loaded = load_module_graph(&path, &ModuleRoots::empty());
            std::fs::remove_file(path).unwrap();
            let graph = loaded.unwrap();
            let module = graph.module(graph.entry()).unwrap();
            let resolved = resolve_module(module, &[]).unwrap();
            let ResolvedDefinitionKind::Equational(main) = &resolved.definitions()[0].kind else {
                panic!("equational main")
            };
            let expression = &main.equations[0].body;
            let mut elaborator =
                EffectElaborator::for_resolved_expression(&resolved, expression).unwrap();
            let typed = elaborator
                .synthesize(expression, &TypeContext::new())
                .expect("ordinary typing precedes capture proof");
            let core = elaborator.finish(typed.node).unwrap();
            let error = validate_effect(core, &[module.source()])
                .expect_err("raw Core cannot bypass capture proof");
            assert_eq!(error.reason(), ValidationReason::DiscardUnsafe);
        }
    }

    #[test]
    fn raw_core_preserves_the_selected_capture_prefix() {
        use super::super::{
            EffectExprKind, ValidationReason, binding::BindingNode, effect::DiscardNode,
            validate_effect, variable::TypedBinder,
        };
        for (fixture, safe) in [
            (
                include_str!("../../tests/fixtures/effects/capture-prefix-before.ash"),
                true,
            ),
            (
                include_str!("../../tests/fixtures/effects/capture-prefix-after.ash"),
                false,
            ),
        ] {
            // Publish only a resume-only program, then introduce discard in
            // actual Core. No source capture claim can authorize this check.
            let fixture = fixture.replace("ask ignored => handle ({\nlet _ = resume ()\nperform D.ask ()\n}) with D {\nask ignored => discard\n}", "ask ignored => {\nlet _ = handle ({\nlet _ = resume ()\nperform D.ask ()\n}) with D {\nask ignored => discard\n}\nperform D.ask ()\n}");
            let discard_start = fixture.find("discard").unwrap();
            let text = format!(
                "{}\ngood : Unit -> Unit\ngood () = ()\nbad : Unit -> Unit\nbad () = ()\n",
                fixture.replace("discard", "resume ()")
            );
            let (honest, honest_source, _, _) = checked_core_text(&text);
            validate_effect(honest, &[&honest_source])
                .expect("resume-only fixture has independently valid Core");
            let (mut core, source, _, _) = checked_core_text(&text);
            let id = core
                .nodes
                .iter()
                .position(|node| {
                    matches!(
                        node.kind,
                        EffectExprKind::Operation(EffectOperation::Resume(_))
                    ) && node.origin.as_ref().unwrap().primary_span().range().start() as usize
                        == discard_start
                })
                .unwrap();
            let EffectExprKind::Operation(EffectOperation::Resume(resume)) = &core.nodes[id].kind
            else {
                unreachable!()
            };
            let operand = resume.value();
            let discard = DiscardNode::new(resume.handler(), resume.owner(), resume.use_state());
            let tail = NodeId::new(core.arena, u32::try_from(core.nodes.len()).unwrap());
            let origin = core.nodes[id].origin.clone().unwrap();
            core.nodes.push(StoredNode {
                dialect: core.nodes[id].dialect,
                ty: Type::Unit,
                effects: EffectRow::empty(),
                origin: Some(origin.clone()),
                kind: EffectExprKind::Operation(EffectOperation::Discard(discard)),
            });
            // Keep the old operand reachable and strict without changing the
            // completion choice or relying on an unreachable-node exemption.
            core.nodes[id].kind = EffectExprKind::Pure(PureExprKind::Computation(
                PureComputation::Bind(BindingNode::new(
                    TypedBinder::new(core.arena, BinderId::new(u32::MAX), Type::Unit, origin),
                    operand,
                    tail,
                )),
            ));
            let result = validate_effect(core, &[&source]);
            if safe {
                result.expect("historical live owners are outside the selected suffix");
            } else {
                assert_eq!(
                    result.unwrap_err().reason(),
                    ValidationReason::DiscardUnsafe
                );
            }
        }
    }

    #[test]
    fn linked_core_reselects_handlers_when_type_instances_coincide() {
        use super::super::{
            EffectExprKind, ValidationReason, binding::BindingNode, effect::DiscardNode,
            validate_effect_modules, variable::TypedBinder,
        };
        for (argument, safe) in [("(1, true)", true), ("(1, 1)", false)] {
            let text = format!(
                "effect E<T> {{\nask : Unit -> Unit\n}}\neffect A {{\nask : Unit -> Unit\n}}\neffect B {{\nask : Unit -> Unit\n}}\n\
                 route<T, U> : (T, U) -> Unit ! {{A, B, E<T>}}\nroute ignored = handle ({{\nlet _ = perform E<U>.ask ()\nlet _ = perform A.ask ()\nperform E<T>.ask ()\n}}) with E<U> {{\nask ignored => {{\nlet _ = perform B.ask ()\nresume ()\n}}\n}}\n\
                 invoke : Unit -> Unit ! {{A, B}}\ninvoke () = handle (route {argument}) with E<Int> {{\nask ignored => resume ()\n}}\n\
                 main : Unit -> Unit\nmain () = handle (handle (invoke ()) with A {{\nask ignored => {{\nlet _ = handle ({{\nlet _ = resume ()\nperform B.ask ()\n}}) with B {{\nask ignored => DISCARD_SITE\n}}\nperform B.ask ()\n}}\n}}) with B {{\nask ignored => resume ()\n}}\n\
                 good : Unit -> Unit\ngood () = ()\nbad : Unit -> Unit\nbad () = ()\n"
            );
            let start = text.find("DISCARD_SITE").unwrap();
            let text = text.replace("DISCARD_SITE", "resume ()");
            let (honest, source, _, _) = checked_core_text(&text);
            let module = honest.registry.effects().first().unwrap().id.module();
            validate_effect_modules(honest, &[&source], &[(module, source.id())])
                .expect("resume-only specialization is valid linked Core");
            let (mut core, source, _, _) = checked_core_text(&text);
            let id = core
                .nodes
                .iter()
                .position(|node| {
                    matches!(
                        node.kind,
                        EffectExprKind::Operation(EffectOperation::Resume(_))
                    ) && node.origin.as_ref().unwrap().primary_span().range().start() as usize
                        == start
                })
                .unwrap();
            let EffectExprKind::Operation(EffectOperation::Resume(resume)) = &core.nodes[id].kind
            else {
                unreachable!()
            };
            let operand = resume.value();
            let discard = DiscardNode::new(resume.handler(), resume.owner(), resume.use_state());
            let tail = NodeId::new(core.arena, u32::try_from(core.nodes.len()).unwrap());
            let origin = core.nodes[id].origin.clone().unwrap();
            core.nodes.push(StoredNode {
                dialect: core.nodes[id].dialect,
                ty: Type::Unit,
                effects: EffectRow::empty(),
                origin: Some(origin.clone()),
                kind: EffectExprKind::Operation(EffectOperation::Discard(discard)),
            });
            core.nodes[id].kind = EffectExprKind::Pure(PureExprKind::Computation(
                PureComputation::Bind(BindingNode::new(
                    TypedBinder::new(core.arena, BinderId::new(u32::MAX), Type::Unit, origin),
                    operand,
                    tail,
                )),
            ));
            let module = core.registry.effects().first().unwrap().id.module();
            let result = validate_effect_modules(core, &[&source], &[(module, source.id())]);
            if safe {
                result.expect(
                    "distinct specialized handlers keep the earlier request outside capture",
                );
            } else {
                assert_eq!(
                    result.unwrap_err().reason(),
                    ValidationReason::DiscardUnsafe
                );
            }
        }
    }

    #[test]
    fn capture_work_has_exact_one_short_and_retry_boundaries() {
        use super::super::EffectExprKind;
        let (core, _, _, _) = checked_core();
        let operation: fn(&EffectExprKind) -> Option<&EffectOperation> = |kind| match kind {
            EffectExprKind::Operation(operation) => Some(operation),
            _ => None,
        };
        let mut measured = TypeWorkBudget::unbounded();
        check_nodes(&core.nodes, &[], &[], operation, &mut measured).unwrap();
        let mut exact = TypeWorkBudget::with_limit(measured.used());
        check_nodes(&core.nodes, &[], &[], operation, &mut exact).unwrap();
        assert_eq!(exact.used(), measured.used());
        let mut short = TypeWorkBudget::with_limit(measured.used() - 1);
        assert!(matches!(
            check_nodes(&core.nodes, &[], &[], operation, &mut short),
            Err(Failure::Resource)
        ));
        let mut retry = TypeWorkBudget::with_limit(measured.used());
        check_nodes(&core.nodes, &[], &[], operation, &mut retry).unwrap();
        assert_eq!(retry.used(), measured.used());
    }

    #[test]
    fn imported_capture_carriers_authenticate_identity_and_unknown_state() {
        use crate::{
            interface::{ConstrainedScheme, InterfaceConstraintBudget},
            resolved::{
                ExportedGlobal, ImportedGlobalScheme, same_imported_global_fact_with_budget,
            },
            source::Origin,
        };
        let source = SourceFile::new("capture-auth", "x").unwrap();
        let origin = Origin::Source(source.span(ByteRange::new(0, 1).unwrap()).unwrap());
        let capture = CaptureValueSummary {
            graph: Some(Arc::new(SummaryGraph {
                types: TypeArguments(Vec::new()),
                callables: Vec::new(),
                code: Vec::new(),
            })),
            value: Value {
                targets: Vec::new(),
                unknown: true,
            },
        };
        let exported = ExportedGlobal {
            binder: BinderId::new(0),
            scheme: ConstrainedScheme::from_rank1_type(Type::Unit),
            origin: origin.clone(),
            capture: capture.clone(),
        };
        let mut imported = ImportedGlobalScheme {
            binder: exported.binder,
            scheme: ConstrainedScheme::from_rank1_type(Type::Unit),
            origin,
            capture,
        };
        let matches = |imported: &ImportedGlobalScheme| {
            same_imported_global_fact_with_budget(
                imported,
                &exported,
                &mut TypeWorkBudget::unbounded(),
                &mut InterfaceConstraintBudget::default(),
            )
            .unwrap()
        };
        assert!(matches(&imported));
        imported.capture.value.unknown = false;
        assert!(!matches(&imported), "unknown cannot be relabeled safe");
        imported.capture.value.unknown = true;
        imported.capture.graph = Some(Arc::new(SummaryGraph {
            types: TypeArguments(Vec::new()),
            callables: Vec::new(),
            code: Vec::new(),
        }));
        assert!(
            !matches(&imported),
            "a structurally equal substitute is not the defining carrier"
        );
        imported.capture = CaptureValueSummary::default();
        assert!(
            !matches(&imported),
            "the authenticated summary cannot disappear"
        );
    }

    #[test]
    fn sparse_shared_capture_metadata_scans_are_charged_and_retryable() {
        let source = SourceFile::new("sparse-metadata", "x").unwrap();
        let span = source.span(ByteRange::new(0, 1).unwrap()).unwrap();
        let effect = EffectInstance::new(
            crate::types::EffectId::new(crate::module::ModuleId::new(0), 0),
            vec![Type::Unit].into_boxed_slice(),
        );
        let mut code = Vec::new();
        code.resize_with(4096, || Control::Return);
        code.push(Control::Request(
            Request::effect(&effect, span, &mut TypeWorkBudget::unbounded()).unwrap(),
        ));
        let entries = code.len();
        let summary = CaptureValueSummary {
            graph: Some(Arc::new(SummaryGraph {
                callables: Vec::new(),
                types: TypeArguments(Vec::new()),
                code,
            })),
            value: Value::default(),
        };
        let alias = summary.clone();
        let scan = |budget: &mut TypeWorkBudget| {
            for summary in [&summary, &alias] {
                for _ in summary.types(budget)? {
                    budget.charge(1)?;
                }
                for _ in summary.effects(budget)? {
                    budget.charge(1)?;
                }
            }
            Ok::<(), ()>(())
        };
        let expected = 2 * (2 * entries + 2);
        assert!(
            scan(&mut TypeWorkBudget::with_limit(expected - 1)).is_err(),
            "aliases must account for every filtered control position"
        );
        for _ in 0..2 {
            let mut exact = TypeWorkBudget::with_limit(expected);
            scan(&mut exact).unwrap();
            assert_eq!(exact.used(), expected);
        }
        let absent = CaptureValueSummary::default();
        let mut empty = TypeWorkBudget::with_limit(0);
        assert_eq!(absent.types(&mut empty).unwrap().count(), 0);
        assert_eq!(absent.effects(&mut empty).unwrap().count(), 0);
        assert_eq!(empty.used(), 0);
    }

    #[test]
    fn local_callable_partial_initialization_exhaustion_is_stack_safe() {
        const CHILD: &str = "ASH_CAPTURE_PARTIAL_INITIALIZATION_CHILD";
        if std::env::var_os(CHILD).is_none() {
            let test_name = concat!(
                "core::capture::tests::",
                "local_callable_partial_initialization_exhaustion_is_stack_safe"
            );
            let output = std::process::Command::new(std::env::current_exe().unwrap())
                .args(["--exact", test_name, "--nocapture"])
                .env(CHILD, "1")
                .output()
                .unwrap();
            assert!(
                output.status.success(),
                "partial initialization child failed: {}",
                String::from_utf8_lossy(&output.stderr)
            );
            return;
        }
        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(|| {
                use crate::{
                    core::{EffectCoreBuilder, EffectExprKind},
                    source::Origin,
                };
                let source = SourceFile::new("partial-capture", "x").unwrap();
                let origin = Origin::Source(source.span(ByteRange::new(0, 1).unwrap()).unwrap());
                let mut builder = EffectCoreBuilder::with_effect_registry(Arc::new(
                    crate::resolved::ResolvedRegistry::new(Vec::new(), Vec::new()),
                ));
                let body = builder.unit(Type::Unit, origin.clone()).unwrap();
                let parameter = builder.binder(Type::Unit, origin.clone()).unwrap();
                let mut ty = Type::Unit;
                for _ in 0..8192 {
                    ty = Type::Function(Box::new(Type::Unit), Box::new(ty));
                }
                let function = builder
                    .function(
                        parameter,
                        body,
                        Type::Function(Box::new(Type::Unit), Box::new(Type::Unit)),
                        origin,
                    )
                    .unwrap();
                // Exercise retention cleanup independently of the builder's
                // shallower source-admission limit.
                discard_type_iteratively(std::mem::replace(
                    &mut builder.nodes[index(function)].ty,
                    ty,
                ));
                let mut clone_work = TypeWorkBudget::unbounded();
                discard_type_iteratively(
                    clone_type_with_budget(&builder.nodes[index(function)].ty, &mut clone_work)
                        .unwrap(),
                );
                let imported = ImportedCallables::new(
                    &[],
                    builder.nodes.len(),
                    &mut TypeWorkBudget::unbounded(),
                )
                .unwrap();
                let values = [Value::default(), Value::default()];
                let operation: fn(&EffectExprKind) -> Option<&EffectOperation> = |kind| match kind {
                    EffectExprKind::Operation(operation) => Some(operation),
                    _ => None,
                };
                // Compilation charges the node carrier and each of these two
                // nodes before cloning the function type. This boundary used to
                // exhaust in the following Value copy, before Callable existed.
                let mut partial = TypeWorkBudget::with_limit(
                    builder.nodes.len() + 1 + builder.nodes.len() + clone_work.used(),
                );
                assert!(matches!(
                    compile(&builder.nodes, &values, &imported, operation, &mut partial),
                    Err(Failure::Resource)
                ));
                let mut measured = TypeWorkBudget::unbounded();
                drop(
                    compile(&builder.nodes, &values, &imported, operation, &mut measured).unwrap(),
                );
                let mut retry = TypeWorkBudget::with_limit(measured.used());
                drop(compile(&builder.nodes, &values, &imported, operation, &mut retry).unwrap());
                assert_eq!(retry.used(), measured.used());
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn deep_capture_equations_and_retained_types_are_stack_safe_and_retryable() {
        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(|| {
                use crate::{
                    core::{EffectCoreBuilder, EffectExprKind},
                    source::Origin,
                };
                let source = SourceFile::new("deep-capture", "x").unwrap();
                let origin = Origin::Source(source.span(ByteRange::new(0, 1).unwrap()).unwrap());
                let mut builder = EffectCoreBuilder::with_effect_registry(Arc::new(
                    crate::resolved::ResolvedRegistry::new(Vec::new(), Vec::new()),
                ));
                let unit = builder.unit(Type::Unit, origin.clone()).unwrap();
                let mut root = unit;
                for _ in 0..4096 {
                    let binder = builder.binder(Type::Unit, origin.clone()).unwrap();
                    root = builder
                        .binding(binder, unit, root, Type::Unit, origin.clone())
                        .unwrap();
                }
                let operation: fn(&EffectExprKind) -> Option<&EffectOperation> = |kind| match kind {
                    EffectExprKind::Operation(operation) => Some(operation),
                    _ => None,
                };
                let roots = [(BinderId::new(100_000), root)];
                assert!(matches!(
                    check_builder(
                        &builder,
                        &roots,
                        &[],
                        operation,
                        &mut TypeWorkBudget::with_limit(128)
                    ),
                    Err(Failure::Resource)
                ));
                check_builder(
                    &builder,
                    &roots,
                    &[],
                    operation,
                    &mut TypeWorkBudget::unbounded(),
                )
                .unwrap();
                drop(builder);
                let mut ty = Type::Unit;
                for _ in 0..8192 {
                    ty = Type::Function(Box::new(Type::Unit), Box::new(ty));
                }
                let capture = CaptureValueSummary {
                    graph: Some(Arc::new(SummaryGraph {
                        types: TypeArguments(Vec::new()),
                        callables: vec![Callable {
                            body: 0,
                            ty,
                            result: Value::default(),
                        }],
                        code: vec![Control::Return],
                    })),
                    value: Value {
                        targets: vec![0],
                        unknown: false,
                    },
                };
                assert!(
                    capture
                        .clone_with_budget(&mut TypeWorkBudget::with_limit(1))
                        .is_err()
                );
                for _ in 0..2 {
                    drop(
                        capture
                            .clone_with_budget(&mut TypeWorkBudget::with_limit(2))
                            .unwrap(),
                    );
                }
                drop(capture);
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
