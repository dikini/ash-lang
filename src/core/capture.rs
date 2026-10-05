//! Bounded inference of stored dependencies and request-carried obligations.
//!
//! Portable callable summaries retain finite value and control graphs. Stored
//! resource dependencies are distinct from completion obligations: copied
//! scalars are free, while actual closure/aggregate captures retain their owner.
//! Resource queries run even without discard, and reconstruct one fresh scope
//! occurrence at a time. Abandonment queries preserve live/consumed completion
//! owners across selected handler captures and restored continuations.

use std::{collections::HashMap, sync::Arc};

mod control;
mod value;
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
        EffectInstance, EffectRow, Type, TypeVariableId, TypeWorkBudget, clone_type_with_budget,
        discard_type_iteratively, same_type_with_budget,
    },
};

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct Value {
    targets: Vec<usize>,
    parameters: Vec<usize>,
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

/// Operation-local visits to immutable graph metadata, not callable values.
/// Borrowed graph owners prevent address reuse while the index is live.
#[derive(Default)]
pub(crate) struct CaptureGraphVisits<'a> {
    seen: HashMap<*const SummaryGraph, &'a SummaryGraph>,
}

impl<'a> CaptureGraphVisits<'a> {
    pub(crate) fn visit(
        &mut self,
        summary: &'a CaptureValueSummary,
        budget: &mut TypeWorkBudget,
    ) -> Result<bool, ()> {
        let Some(graph) = &summary.graph else {
            return Ok(false);
        };
        budget.charge(1)?;
        let identity = Arc::as_ptr(graph);
        if self.seen.contains_key(&identity) {
            return Ok(false);
        }
        budget.charge(1)?;
        self.seen.try_reserve(1).map_err(|_| ())?;
        self.seen.insert(identity, graph.as_ref());
        Ok(true)
    }
}

impl CaptureValueSummary {
    /// A bounded provider bridge for an authenticated pure closed-data arrow.
    /// The caller proves the actual operand independent. This query preserves
    /// selected control and callable-result facts; it is not a resource-capture
    /// proof for arbitrary values or internally handled provider helpers.
    pub(crate) fn check_provider_independent_data_call(
        &self,
        metadata: &[TypeVariableId],
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        let graph = self.graph.as_ref().ok_or(Failure::Invalid)?;
        charge(budget, self.value.work_size() + 1)?;
        if self.value.unknown || !self.value.parameters.is_empty() || self.value.targets.is_empty()
        {
            return Err(Failure::Invalid);
        }
        let mut pending = Vec::new();
        let mut seen = std::collections::HashSet::new();
        for target in &self.value.targets {
            let callable = graph.callables.get(*target).ok_or(Failure::Invalid)?;
            graph
                .data
                .as_ref()
                .ok_or(Failure::Invalid)?
                .check_provider_selected_captures(*target, metadata, budget)?;
            let result = callable
                .result
                .instantiate(*target, &Value::default(), budget)?;
            charge(budget, result.work_size() + 1)?;
            if result.unknown || !result.targets.is_empty() || !result.parameters.is_empty() {
                return Err(Failure::Invalid);
            }
            charge(budget, 1)?;
            pending.try_reserve(1).map_err(|_| Failure::Resource)?;
            pending.push(callable.body);
        }
        while let Some(position) = pending.pop() {
            charge(budget, 1)?;
            if seen.contains(&position) {
                continue;
            }
            charge(budget, 1)?;
            seen.try_reserve(1).map_err(|_| Failure::Resource)?;
            seen.insert(position);
            match graph.code.get(position).ok_or(Failure::Invalid)? {
                Control::Return => {}
                Control::Sequence(children) | Control::Choice(children) => {
                    charge(budget, children.len())?;
                    pending
                        .try_reserve(children.len())
                        .map_err(|_| Failure::Resource)?;
                    pending.extend(children);
                }
                Control::Call { value, ty, .. } => {
                    if graph.types.0.get(*ty).is_none() {
                        return Err(Failure::Invalid);
                    }
                    charge(budget, value.work_size() + 1)?;
                    if value.unknown || !value.parameters.is_empty() || value.targets.is_empty() {
                        return Err(Failure::Invalid);
                    }
                    charge(budget, value.targets.len())?;
                    pending
                        .try_reserve(value.targets.len())
                        .map_err(|_| Failure::Resource)?;
                    for target in &value.targets {
                        graph
                            .data
                            .as_ref()
                            .ok_or(Failure::Invalid)?
                            .check_provider_selected_captures(*target, metadata, budget)?;
                        pending.push(graph.callables.get(*target).ok_or(Failure::Invalid)?.body);
                    }
                }
                _ => return Err(Failure::Invalid),
            }
        }
        Ok(())
    }

    pub(crate) fn check_provider_independent_typed_call(
        &self,
        actual: &Type,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        let graph = self.graph.as_ref().ok_or(Failure::Invalid)?;
        charge(budget, self.value.work_size() + 1)?;
        if self.value.unknown || !self.value.parameters.is_empty() || self.value.targets.is_empty()
        {
            return Err(Failure::Invalid);
        }
        Analysis::provider_independent_call(graph, &self.value.targets, actual, false, budget)
    }

    /// Only independently rebuilt canonical source wrappers use this entry.
    pub(crate) fn check_provider_source_wrapper_call(
        proof: &super::provider::ProviderSourceRelation,
        actual: &Type,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        let summary = proof.summary();
        let graph = summary.graph.as_ref().ok_or(Failure::Invalid)?;
        charge(budget, summary.value.work_size() + 1)?;
        if summary.value.unknown
            || !summary.value.parameters.is_empty()
            || summary.value.targets.is_empty()
        {
            return Err(Failure::Invalid);
        }
        Analysis::provider_independent_call(graph, &summary.value.targets, actual, true, budget)
    }

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
        self.graph.as_ref().is_some_and(|graph| graph.effects)
    }

    pub(crate) fn same_with_budget(
        &self,
        other: &Self,
        budget: &mut TypeWorkBudget,
    ) -> Result<bool, ()> {
        if self.graph.is_some() || other.graph.is_some() {
            budget.charge(self.value.work_size() + other.value.work_size() + 1)?;
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
        let mut types = Vec::new();
        if let Some(graph) = &self.graph {
            let count = graph
                .callables
                .len()
                .checked_add(graph.types.0.len())
                .ok_or(())?;
            budget.charge(count)?;
            types.try_reserve(count).map_err(|_| ())?;
            types.extend(graph.callables.iter().map(|callable| &callable.ty));
            types.extend(graph.types.0.iter());
            for request in graph.code.iter().filter_map(|code| match code {
                Control::Request(request)
                | Control::Handler {
                    effect: request, ..
                }
                | Control::Resource {
                    effect: request, ..
                } => Some(request),
                _ => None,
            }) {
                if let Some(effect) = &request.effect {
                    crate::types::extend_owner_type_children_with_charge(
                        effect.arguments(),
                        &mut types,
                        budget,
                    )?;
                }
            }
        }
        Ok(types.into_iter())
    }

    // Charge each explicit scan, including repeated scans of a shared graph.
    pub(crate) fn effects<'a>(
        &'a self,
        budget: &mut TypeWorkBudget,
    ) -> Result<impl Iterator<Item = crate::types::EffectId> + use<'a>, ()> {
        if let Some(graph) = &self.graph {
            budget.charge(graph.code.len())?;
        }
        let mut identities = Vec::new();
        let mut pending = Vec::new();
        if let Some(graph) = &self.graph {
            for request in graph.code.iter().filter_map(|code| match code {
                Control::Request(request)
                | Control::Handler {
                    effect: request, ..
                }
                | Control::Resource {
                    effect: request, ..
                } => Some(request),
                _ => None,
            }) {
                if let Some(effect) = &request.effect {
                    budget.charge(1 + effect.arguments().len())?;
                    identities.try_reserve(1).map_err(|_| ())?;
                    identities.push(effect.effect());
                    pending
                        .try_reserve(effect.arguments().len())
                        .map_err(|_| ())?;
                    pending.extend(effect.arguments());
                }
                while let Some(argument) = pending.pop() {
                    budget.charge(1)?;
                    if let crate::types::KindedArgument::RowArg(row) = argument {
                        if row.tail().is_some() {
                            budget.charge(1)?;
                        }
                        for instance in row
                            .known()
                            .iter()
                            .chain(row.tail().into_iter().flat_map(|tail| tail.lacks()))
                        {
                            budget.charge(1 + instance.arguments().len())?;
                            identities.try_reserve(1).map_err(|_| ())?;
                            identities.push(instance.effect());
                            pending
                                .try_reserve(instance.arguments().len())
                                .map_err(|_| ())?;
                            pending.extend(instance.arguments());
                        }
                    }
                }
            }
        }
        Ok(identities.into_iter())
    }
}

#[derive(Debug)]
struct SummaryGraph {
    effects: bool,
    callables: Vec<Callable>,
    code: Vec<Control>,
    types: TypeArguments,
    data: Option<Arc<value::Graph>>,
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
            value.relocate(offset, budget)?;
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
    fn work_size(&self) -> usize {
        self.targets.len() + self.parameters.len()
    }

    fn parameter(&mut self, parameter: usize, budget: &mut TypeWorkBudget) -> Result<(), Failure> {
        let parameters = &mut self.parameters;
        charge(budget, parameters.len() + 1)?;
        if !parameters.contains(&parameter) {
            parameters.try_reserve(1).map_err(|_| Failure::Resource)?;
            parameters.push(parameter);
        }
        Ok(())
    }

    fn instantiate(
        &self,
        parameter: usize,
        argument: &Self,
        budget: &mut TypeWorkBudget,
    ) -> Result<Self, Failure> {
        let mut result = self.copy(budget)?;
        charge(budget, result.parameters.len())?;
        let returns_argument = result.parameters.contains(&parameter);
        result
            .parameters
            .retain(|candidate| *candidate != parameter);
        if returns_argument {
            result.join(argument, budget)?;
        }
        Ok(result)
    }

    fn relocate(&mut self, offset: usize, budget: &mut TypeWorkBudget) -> Result<(), Failure> {
        charge(budget, self.targets.len() + self.parameters.len())?;
        for target in self.targets.iter_mut().chain(&mut self.parameters) {
            *target += offset;
        }
        Ok(())
    }

    fn join(&mut self, other: &Self, budget: &mut TypeWorkBudget) -> Result<(), Failure> {
        for parameter in &other.parameters {
            self.parameter(*parameter, budget)?;
        }
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
            parameters: if self.parameters.is_empty() {
                Vec::new()
            } else {
                copy_slice(&self.parameters, budget)?
            },
            unknown: self.unknown,
        })
    }
}

#[derive(Clone, Debug)]
struct Request {
    // None denotes admitted requests from an opaque open row.
    effect: Option<Arc<EffectInstance>>,
    opaque_row: Option<Arc<EffectRow>>,
    ambiguous_instance: bool,
    source: Span,
    operation: Option<crate::types::OperationId>,
}

impl Request {
    fn unknown(source: Span) -> Self {
        Self {
            effect: None,
            opaque_row: None,
            ambiguous_instance: false,
            source,
            operation: None,
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
            opaque_row: self.opaque_row.as_ref().map(Arc::clone),
            ambiguous_instance: self.ambiguous_instance,
            source: self.source,
            operation: self.operation,
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
    pub(crate) owner: Option<CompletionOwner>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum CompletionOwner {
    Cleanup(Span),
    Clause(Span),
}

#[derive(Debug)]
pub(crate) struct CleanupRequirement {
    pub(crate) discard: usize,
    pub(crate) local: bool,
    pub(crate) code: usize,
    pub(crate) source: Span,
    pub(crate) context: usize,
    pub(crate) expected: EffectRow,
    pub(crate) row: EffectRow,
    pub(crate) retained: Vec<EffectInstance>,
}

#[derive(Clone, Copy)]
pub(crate) struct MethodUse {
    pub(crate) node: NodeId,
    pub(crate) target: MethodTarget,
    pub(crate) method: crate::interface::MethodId,
    pub(crate) requirement: Option<crate::interface::RequirementId>,
    pub(crate) arguments: usize,
}

/// Analysis-local ordered method records indexed by their exact Core node.
struct MethodUses<'a> {
    by_node: HashMap<usize, Vec<&'a MethodUse>>,
}

impl<'a> MethodUses<'a> {
    fn new(methods: &'a [MethodUse], budget: &mut TypeWorkBudget) -> Result<Self, Failure> {
        // One input visit, at most one hash entry, and one retained reference
        // per record. Repeated-node records retain their original order.
        let work = methods.len().checked_mul(3).ok_or(Failure::Resource)?;
        charge(budget, work)?;
        let mut by_node = HashMap::<usize, Vec<&MethodUse>>::new();
        by_node
            .try_reserve(methods.len())
            .map_err(|_| Failure::Resource)?;
        for method in methods {
            let records = by_node.entry(index(method.node)).or_default();
            records.try_reserve(1).map_err(|_| Failure::Resource)?;
            records.push(method);
        }
        Ok(Self { by_node })
    }

    fn at(&self, node: usize, budget: &mut TypeWorkBudget) -> Result<&[&'a MethodUse], Failure> {
        if self.by_node.is_empty() {
            return Ok(&[]);
        }
        charge(budget, 1)?;
        let records = self.by_node.get(&node).map_or(&[][..], Vec::as_slice);
        charge(budget, records.len())?;
        Ok(records)
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum MethodTarget {
    Binder(BinderId),
    Abstract(crate::interface::RequirementId),
    Adapter { value: usize, binder: BinderId },
}

pub(crate) struct MethodAdapter {
    pub(crate) binder: BinderId,
    pub(crate) head_arguments: Vec<Type>,
    pub(crate) method_parameters: usize,
    pub(crate) prerequisites: Vec<(
        crate::interface::RequirementId,
        crate::interface::MethodId,
        MethodTarget,
    )>,
    pub(crate) source: Span,
}

impl Drop for MethodAdapter {
    fn drop(&mut self) {
        for argument in self.head_arguments.drain(..) {
            crate::types::discard_type_iteratively(argument);
        }
    }
}

pub(crate) fn selection_targets<'a>(
    selection: &crate::interface::EvidenceSelection,
    requested: Option<crate::interface::MethodId>,
    mut implementation: impl FnMut(
        crate::interface::ImplId,
        &mut TypeWorkBudget,
    )
        -> Result<&'a crate::resolved::CheckedImplementationFact, Failure>,
    mut lexical: impl FnMut(
        crate::interface::LexicalEvidenceId,
        crate::interface::MethodId,
        &mut TypeWorkBudget,
    ) -> Result<BinderId, Failure>,
    adapters: &mut Vec<MethodAdapter>,
    work: &mut TypeWorkBudget,
) -> Result<Vec<(crate::interface::MethodId, MethodTarget)>, Failure> {
    use crate::interface::{EvidenceNode, MethodId};
    let mut pending = Vec::new();
    work.charge(selection.node_count())
        .map_err(|()| Failure::Resource)?;
    pending
        .try_reserve(selection.node_count())
        .map_err(|_| Failure::Resource)?;
    pending.push((selection.root(), false));
    let mut values: HashMap<crate::interface::EvidenceNodeId, Vec<(MethodId, MethodTarget)>> =
        HashMap::new();
    charge(work, selection.node_count())?;
    values
        .try_reserve(selection.node_count())
        .map_err(|_| Failure::Resource)?;
    while let Some((node, build)) = pending.pop() {
        work.charge(1).map_err(|()| Failure::Resource)?;
        if values.contains_key(&node) {
            continue;
        }
        let selected = selection.node(node).ok_or(Failure::Invalid)?;
        if !build && let EvidenceNode::Implementation { prerequisites, .. } = selected {
            work.charge(prerequisites.len() + 1)
                .map_err(|()| Failure::Resource)?;
            pending
                .try_reserve(prerequisites.len() + 1)
                .map_err(|_| Failure::Resource)?;
            pending.push((node, true));
            pending.extend(prerequisites.iter().rev().map(|node| (*node, false)));
            continue;
        }
        let mut targets = Vec::new();
        let wanted = (node == selection.root()).then_some(requested).flatten();
        match selected {
            EvidenceNode::Lexical { methods, .. } | EvidenceNode::Abstract { methods, .. } => {
                work.charge(methods.len()).map_err(|()| Failure::Resource)?;
                targets
                    .try_reserve(methods.len())
                    .map_err(|_| Failure::Resource)?;
                for &method in methods {
                    if wanted.is_some_and(|wanted| wanted != method) {
                        continue;
                    }
                    let target = match selected {
                        EvidenceNode::Lexical { source, .. } => {
                            MethodTarget::Binder(lexical(source, method, work)?)
                        }
                        EvidenceNode::Abstract { requirement, .. } => {
                            MethodTarget::Abstract(requirement)
                        }
                        _ => return Err(Failure::Invalid),
                    };
                    targets.push((method, target));
                }
            }
            EvidenceNode::Implementation {
                implementation: implementation_id,
                substitution,
                prerequisites,
                methods,
            } => {
                let owner = implementation(implementation_id, work)?;
                if owner.prerequisites.len() != prerequisites.len() {
                    return Err(Failure::Invalid);
                }
                work.charge(methods.len()).map_err(|()| Failure::Resource)?;
                targets
                    .try_reserve(methods.len())
                    .map_err(|_| Failure::Resource)?;
                for &method in methods {
                    if wanted.is_some_and(|wanted| wanted != method.method()) {
                        continue;
                    }
                    work.charge(owner.methods.len())
                        .map_err(|()| Failure::Resource)?;
                    let fact = owner
                        .methods
                        .iter()
                        .find(|fact| fact.id == method)
                        .ok_or(Failure::Invalid)?;
                    if method.implementation() != implementation_id
                        || fact.head_type_parameter_count != substitution.len()
                        || fact.scheme.type_parameters.len() < substitution.len()
                    {
                        return Err(Failure::Invalid);
                    }
                    let mut adapter = MethodAdapter {
                        binder: fact.binder,
                        head_arguments: Vec::new(),
                        method_parameters: fact.scheme.type_parameters.len() - substitution.len(),
                        prerequisites: Vec::new(),
                        source: fact.span,
                    };
                    work.charge(substitution.len())
                        .map_err(|()| Failure::Resource)?;
                    adapter
                        .head_arguments
                        .try_reserve(substitution.len())
                        .map_err(|_| Failure::Resource)?;
                    for ((parameter, _), actual) in
                        fact.scheme.type_parameters.iter().zip(substitution)
                    {
                        if *parameter != actual.parameter() {
                            return Err(Failure::Invalid);
                        }
                        adapter.head_arguments.push(
                            clone_type_with_budget(actual.argument(), work)
                                .map_err(|()| Failure::Resource)?,
                        );
                    }
                    for (requirement, node) in owner.prerequisites.iter().zip(prerequisites) {
                        let supplied = values.get(node).ok_or(Failure::Invalid)?;
                        work.charge(supplied.len())
                            .map_err(|()| Failure::Resource)?;
                        adapter
                            .prerequisites
                            .try_reserve(supplied.len())
                            .map_err(|_| Failure::Resource)?;
                        adapter.prerequisites.extend(
                            supplied
                                .iter()
                                .map(|(method, target)| (requirement.id, *method, *target)),
                        );
                    }
                    work.charge(1).map_err(|()| Failure::Resource)?;
                    adapters.try_reserve(1).map_err(|_| Failure::Resource)?;
                    let target = MethodTarget::Adapter {
                        value: adapters.len(),
                        binder: fact.binder,
                    };
                    adapters.push(adapter);
                    targets.push((method.method(), target));
                }
            }
        }
        charge(work, 1)?;
        values.try_reserve(1).map_err(|_| Failure::Resource)?;
        values.insert(node, targets);
    }
    values.remove(&selection.root()).ok_or(Failure::Invalid)
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum Failure {
    Resource,
    Escape {
        source: Span,
        acquisition: Span,
    },
    Invalid,
    Unsafe(UnsafeDiscard),
    CleanupContext {
        discard: Span,
        action: Span,
        handler: Span,
    },
    CleanupRow {
        node: usize,
        source: Span,
    },
}

fn charge(budget: &mut TypeWorkBudget, count: usize) -> Result<(), Failure> {
    budget.charge(count).map_err(|()| Failure::Resource)
}

fn index(node: NodeId) -> usize {
    node.value() as usize
}

// A function retains only referenced values from outside its body. Bindings
// evaluated when it is called are not part of its stored environment.
fn free_values_with_methods<F: CoreOperationFamily>(
    nodes: &[StoredNode<F>],
    root: usize,
    parameters: &[BinderId],
    methods: &MethodUses<'_>,
    capture_ports: &[usize],
    budget: &mut TypeWorkBudget,
) -> Result<Vec<BinderId>, Failure> {
    let mut pending = copy_slice(&[root], budget)?;
    let mut seen = std::collections::HashSet::new();
    let mut bound = std::collections::HashSet::new();
    let mut references = Vec::new();
    charge(budget, parameters.len() + 1)?;
    bound
        .try_reserve(parameters.len())
        .map_err(|_| Failure::Resource)?;
    bound.extend(parameters);
    while let Some(id) = pending.pop() {
        charge(budget, 1)?;
        seen.try_reserve(1).map_err(|_| Failure::Resource)?;
        if !seen.insert(id) {
            continue;
        }
        let node = nodes.get(id).ok_or(Failure::Invalid)?;
        if !capture_ports.is_empty() {
            charge(budget, capture_ports.len())?;
            if capture_ports.contains(&id) {
                continue;
            }
        }
        let node_methods = methods.at(id, budget)?;
        for method in node_methods {
            if method.requirement.is_none()
                && let MethodTarget::Binder(binder) | MethodTarget::Adapter { binder, .. } =
                    method.target
            {
                references.try_reserve(1).map_err(|_| Failure::Resource)?;
                references.push(binder);
            }
        }
        // A selected source method occurrence is replaced by its authenticated
        // route in the value graph. Its obsolete placeholder children are not
        // lexical dependencies of the selected callable.
        if node_methods
            .iter()
            .any(|method| method.requirement.is_none())
        {
            continue;
        }
        let mut binders = Vec::new();
        let mut failed = false;
        F::visit_operation_binders(&node.kind, &mut |binder| {
            if charge(budget, 1).is_err() || binders.try_reserve(1).is_err() {
                failed = true;
            } else {
                binders.push(binder.id());
            }
        });
        if failed {
            return Err(Failure::Resource);
        }
        match F::pure(&node.kind) {
            Some(PureExprKind::Variable(variable)) => {
                charge(budget, 1)?;
                references.try_reserve(1).map_err(|_| Failure::Resource)?;
                references.push(variable.binder());
            }
            Some(PureExprKind::Value(PureValue::Function(function))) => {
                binders.try_reserve(1).map_err(|_| Failure::Resource)?;
                binders.push(function.parameter().id());
            }
            Some(PureExprKind::Computation(PureComputation::Bind(binding))) => {
                binders.try_reserve(1).map_err(|_| Failure::Resource)?;
                binders.push(binding.binder().id());
            }
            Some(PureExprKind::Computation(PureComputation::RecursiveBind(binding))) => {
                charge(budget, binding.members().len())?;
                binders
                    .try_reserve(binding.members().len())
                    .map_err(|_| Failure::Resource)?;
                binders.extend(binding.members().iter().map(|member| member.binder().id()));
            }
            Some(PureExprKind::Computation(PureComputation::Match(matching))) => {
                for arm in matching.arms() {
                    for binder in arm.pattern().binder_iter() {
                        charge(budget, 1)?;
                        binders.try_reserve(1).map_err(|_| Failure::Resource)?;
                        binders.push(binder.id());
                    }
                }
            }
            _ => {}
        }
        charge(budget, binders.len() + F::child_count(&node.kind))?;
        bound
            .try_reserve(binders.len())
            .map_err(|_| Failure::Resource)?;
        bound.extend(binders);
        seen.try_reserve(F::child_count(&node.kind))
            .map_err(|_| Failure::Resource)?;
        pending
            .try_reserve(F::child_count(&node.kind))
            .map_err(|_| Failure::Resource)?;
        for ordinal in 0..F::child_count(&node.kind) {
            pending.push(index(
                F::child_at(&node.kind, ordinal).ok_or(Failure::Invalid)?,
            ));
        }
    }
    charge(budget, references.len())?;
    references.retain(|binder| !bound.contains(binder));
    Ok(references)
}

#[derive(Default)]
struct MetadataVariables {
    variables: Vec<TypeVariableId>,
    identities: std::collections::HashSet<TypeVariableId>,
}

impl MetadataVariables {
    fn retain(
        &mut self,
        identity: TypeVariableId,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        // Lookup is indexed; retain first-discovery order in the output vector.
        charge(budget, 1)?;
        if !self.identities.contains(&identity) {
            charge(budget, 2)?;
            self.identities
                .try_reserve(1)
                .map_err(|_| Failure::Resource)?;
            self.variables
                .try_reserve(1)
                .map_err(|_| Failure::Resource)?;
            self.identities.insert(identity);
            self.variables.push(identity);
        }
        Ok(())
    }
}

fn retain_type_variables(
    value: &mut MetadataVariables,
    ty: &Type,
    budget: &mut TypeWorkBudget,
) -> Result<(), Failure> {
    retain_metadata_variables(value, Metadata::Type(ty), budget)
}

#[derive(Clone, Copy)]
enum Metadata<'a> {
    Type(&'a Type),
    Argument(&'a crate::types::KindedArgument),
    Row(&'a crate::types::EffectRow),
}

fn retain_row_variables(
    value: &mut MetadataVariables,
    row: &crate::types::EffectRow,
    budget: &mut TypeWorkBudget,
) -> Result<(), Failure> {
    retain_metadata_variables(value, Metadata::Row(row), budget)
}

fn retain_metadata_variables(
    value: &mut MetadataVariables,
    root: Metadata<'_>,
    budget: &mut TypeWorkBudget,
) -> Result<(), Failure> {
    let mut pending = copy_slice(&[root], budget)?;
    let mut discovered = MetadataVariables::default();
    let mut bound = std::collections::HashSet::new();
    while let Some(metadata) = pending.pop() {
        charge(budget, 1)?;
        match metadata {
            Metadata::Argument(crate::types::KindedArgument::TypeArg(ty)) => {
                pending.try_reserve(1).map_err(|_| Failure::Resource)?;
                pending.push(Metadata::Type(ty));
            }
            Metadata::Argument(crate::types::KindedArgument::RowArg(row)) => {
                pending.try_reserve(1).map_err(|_| Failure::Resource)?;
                pending.push(Metadata::Row(row));
            }
            Metadata::Type(Type::ResourceApply(_, arguments)) => {
                charge(budget, arguments.len())?;
                pending
                    .try_reserve(arguments.len())
                    .map_err(|_| Failure::Resource)?;
                pending.extend(arguments.iter().map(Metadata::Argument));
            }
            Metadata::Type(Type::Variable(variable)) => discovered.retain(*variable, budget)?,
            Metadata::Type(Type::Application(left, right) | Type::Function(left, right)) => {
                pending.try_reserve(2).map_err(|_| Failure::Resource)?;
                pending.extend([Metadata::Type(left), Metadata::Type(right)]);
            }
            Metadata::Type(Type::Tuple(elements)) => {
                charge(budget, elements.len())?;
                pending
                    .try_reserve(elements.len())
                    .map_err(|_| Failure::Resource)?;
                pending.extend(elements.iter().map(Metadata::Type));
            }
            Metadata::Type(Type::Forall(parameters, body)) => {
                charge(budget, parameters.len())?;
                charge(budget, parameters.len())?;
                bound
                    .try_reserve(parameters.len())
                    .map_err(|_| Failure::Resource)?;
                bound.extend(parameters.iter().map(|(variable, _)| *variable));
                pending.try_reserve(1).map_err(|_| Failure::Resource)?;
                pending.push(Metadata::Type(body));
            }
            Metadata::Type(Type::EffectfulFunction(argument, result)) => {
                pending.try_reserve(3).map_err(|_| Failure::Resource)?;
                pending.extend([
                    Metadata::Type(argument),
                    Metadata::Type(result.value()),
                    Metadata::Row(result.effects()),
                ]);
            }
            Metadata::Row(row) => {
                let lacks = if let Some(tail) = row.tail() {
                    if let crate::types::EffectRowVariable::Rigid(variable) = tail.variable() {
                        discovered.retain(variable, budget)?;
                    }
                    tail.lacks()
                } else {
                    &[]
                };
                for effect in row.known().iter().chain(lacks) {
                    charge(budget, 1)?;
                    charge(budget, effect.arguments().len())?;
                    pending
                        .try_reserve(effect.arguments().len())
                        .map_err(|_| Failure::Resource)?;
                    pending.extend(effect.arguments().iter().map(Metadata::Argument));
                }
            }
            _ => {}
        }
    }
    for variable in discovered.variables {
        charge(budget, 1)?;
        if !bound.contains(&variable) {
            value.retain(variable, budget)?;
        }
    }
    Ok(())
}

fn retain_function_metadata<F: CoreOperationFamily>(
    value: &mut MetadataVariables,
    nodes: &[StoredNode<F>],
    root: usize,
    operation: fn(&F::Kind) -> Option<&EffectOperation>,
    budget: &mut TypeWorkBudget,
) -> Result<(), Failure> {
    let mut pending = copy_slice(&[root], budget)?;
    let mut seen = std::collections::HashSet::new();
    let mut bound = Vec::new();
    while let Some(id) = pending.pop() {
        charge(budget, 1)?;
        seen.try_reserve(1).map_err(|_| Failure::Resource)?;
        if !seen.insert(id) {
            continue;
        }
        let node = nodes.get(id).ok_or(Failure::Invalid)?;
        retain_type_variables(value, &node.ty, budget)?;
        retain_row_variables(value, F::effect_row(&node.effects), budget)?;
        match operation(&node.kind) {
            Some(EffectOperation::Resource(resource)) => {
                bound.try_reserve(1).map_err(|_| Failure::Resource)?;
                bound.push(resource.acquisition.identity);
            }
            Some(EffectOperation::ProviderScope(scope)) => {
                charge(budget, 1)?;
                bound.try_reserve(1).map_err(|_| Failure::Resource)?;
                bound.push(scope.descriptor.identity());
                for argument in scope
                    .descriptor
                    .arguments()
                    .iter()
                    .chain(scope.handler.effect().arguments())
                {
                    retain_metadata_variables(value, Metadata::Argument(argument), budget)?;
                }
                retain_type_variables(value, scope.handler_output.value(), budget)?;
                retain_row_variables(value, scope.handler_output.effects(), budget)?;
            }
            Some(EffectOperation::Handler(handler)) => {
                for argument in handler.effect().arguments() {
                    retain_metadata_variables(value, Metadata::Argument(argument), budget)?;
                }
            }
            _ => {}
        }
        if let Some(PureExprKind::Computation(PureComputation::TypeAbstraction(abstraction))) =
            F::pure(&node.kind)
        {
            charge(budget, abstraction.parameters().len())?;
            bound
                .try_reserve(abstraction.parameters().len())
                .map_err(|_| Failure::Resource)?;
            bound.extend(
                abstraction
                    .parameters()
                    .iter()
                    .map(|(variable, _)| *variable),
            );
        }
        if let Some(PureExprKind::Computation(PureComputation::TypeApplication(application))) =
            F::pure(&node.kind)
        {
            for argument in application.arguments() {
                retain_type_variables(value, argument, budget)?;
            }
            for row in application.row_arguments() {
                retain_row_variables(value, row, budget)?;
            }
        }
        charge(budget, F::child_count(&node.kind))?;
        pending
            .try_reserve(F::child_count(&node.kind))
            .map_err(|_| Failure::Resource)?;
        for ordinal in 0..F::child_count(&node.kind) {
            pending.push(index(
                F::child_at(&node.kind, ordinal).ok_or(Failure::Invalid)?,
            ));
        }
    }
    charge(
        budget,
        value.variables.len().saturating_mul(bound.len() + 2),
    )?;
    let identities = &mut value.identities;
    value.variables.retain(|variable| {
        if bound.contains(variable) {
            identities.remove(variable);
            false
        } else {
            true
        }
    });
    Ok(())
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
                if !crate::types::same_kinded_argument_with_budget(a, b, budget)
                    .map_err(|()| Failure::Resource)?
                {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        _ => Ok(false),
    }
}

// Constructor application retains its operand evaluation and value graph. It
// cannot request, capture, or invoke source code after that operand returns.
fn constructor_value<F: CoreOperationFamily>(
    nodes: &[StoredNode<F>],
    mut id: usize,
    budget: &mut TypeWorkBudget,
) -> Result<bool, Failure> {
    loop {
        charge(budget, 1)?;
        match F::pure(&nodes[id].kind) {
            Some(PureExprKind::Value(PureValue::Constructor(_))) => return Ok(true),
            Some(PureExprKind::Computation(PureComputation::TypeApplication(application))) => {
                id = index(application.function());
            }
            _ => return Ok(false),
        }
    }
}

fn compile<F: CoreOperationFamily>(
    nodes: &[StoredNode<F>],
    values: &[Value],
    imported: &ImportedCallables<'_>,
    operation: fn(&F::Kind) -> Option<&EffectOperation>,
    data: &mut value::Graph,
    provider_query: bool,
    budget: &mut TypeWorkBudget,
) -> Result<(SummaryGraph, Vec<usize>), Failure> {
    compile_with_boundary(
        nodes,
        values,
        imported,
        operation,
        data,
        provider_query,
        None,
        budget,
    )
}

#[expect(
    clippy::too_many_arguments,
    reason = "conditional completion edges accompany the same actual capture compilation inputs without an invented handler frame"
)]
fn compile_with_boundary<F: CoreOperationFamily>(
    nodes: &[StoredNode<F>],
    values: &[Value],
    imported: &ImportedCallables<'_>,
    operation: fn(&F::Kind) -> Option<&EffectOperation>,
    data: &mut value::Graph,
    provider_query: bool,
    mut boundary: Option<(
        &ConditionalCapturePorts,
        &mut Vec<ConditionalCompletionEdge>,
    )>,
    budget: &mut TypeWorkBudget,
) -> Result<(SummaryGraph, Vec<usize>), Failure> {
    let mut graph = SummaryGraph {
        effects: F::ALLOWS_EFFECTFUL_TYPES,
        data: None,
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
            result.relocate(*target_offset, budget)?;
            graph.callables.push(Callable {
                body: callable.body + code_offset,
                ty: clone_type_with_budget(&callable.ty, budget).map_err(|_| Failure::Resource)?,
                result,
            });
        }
    }
    let mut owners = HashMap::new();
    for node in nodes {
        let handler = match operation(&node.kind) {
            Some(EffectOperation::Handler(handler)) => Some(handler),
            Some(EffectOperation::ProviderScope(scope)) => Some(&scope.handler),
            _ => None,
        };
        if let Some(handler) = handler {
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
            Some(PureExprKind::Value(PureValue::Intrinsic(_))) => {
                graph.callables[id] = Callable {
                    body: 0,
                    ty: clone_type_with_budget(&node.ty, budget).map_err(|_| Failure::Resource)?,
                    result: Value::default(),
                };
                Control::Return
            }
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
                if let PureComputation::Apply(application) = pure
                    && !constructor_value(nodes, index(application.function()), budget)?
                {
                    let actual = index(application.function());
                    graph
                        .types
                        .0
                        .try_reserve(1)
                        .map_err(|_| Failure::Resource)?;
                    let ty = graph.types.0.len();
                    let callable = match (&nodes[actual].ty, F::effect_row(&node.effects).tail()) {
                        (Type::EffectfulFunction(domain, codomain), Some(reported))
                            if codomain
                                .effects()
                                .tail()
                                .is_some_and(|tail| tail.variable() == reported.variable()) =>
                        {
                            let tail = codomain.effects().tail().ok_or(Failure::Invalid)?;
                            let row = crate::types::rebuild_effect_row_with_budget(
                                codomain.effects().known(),
                                Some(tail.variable()),
                                tail.lacks().iter().chain(reported.lacks()),
                                clone_type_with_budget,
                                budget,
                            )
                            .map_err(|_| Failure::Resource)?;
                            let mut owned = TypeArguments(Vec::new());
                            charge(budget, 2)?;
                            owned.0.try_reserve(2).map_err(|_| Failure::Resource)?;
                            owned.0.push(
                                clone_type_with_budget(domain, budget)
                                    .map_err(|_| Failure::Resource)?,
                            );
                            owned.0.push(
                                clone_type_with_budget(codomain.value(), budget)
                                    .map_err(|_| Failure::Resource)?,
                            );
                            let value = owned.0.pop().ok_or(Failure::Invalid)?;
                            let domain = owned.0.pop().ok_or(Failure::Invalid)?;
                            Type::function_computation(
                                domain,
                                crate::types::ComputationType::new(value, row),
                            )
                        }
                        _ => clone_type_with_budget(&nodes[actual].ty, budget)
                            .map_err(|_| Failure::Resource)?,
                    };
                    graph.types.0.push(callable);
                    graph.code.try_reserve(1).map_err(|_| Failure::Resource)?;
                    sequence.push(graph.code.len());
                    data.position(graph.code.len(), id, budget)?;
                    graph.code.push(Control::Call {
                        value: values[actual].copy(budget)?,
                        ty,
                        source,
                    });
                }
                Control::Sequence(sequence)
            }
            _ => match operation(&node.kind) {
                Some(EffectOperation::ProviderStateAccess(_)) if provider_query => {
                    Control::Unavailable
                }
                Some(EffectOperation::ProviderStateAccess(access)) => {
                    Control::Sequence(copy_slice(&[index(access.operand()) + 1], budget)?)
                }
                Some(EffectOperation::Cleanup(scope)) => {
                    let row_type = graph.types.0.len();
                    charge(budget, 3)?;
                    graph
                        .types
                        .0
                        .try_reserve(1)
                        .map_err(|_| Failure::Resource)?;
                    let effects = crate::types::clone_effect_row_with_budget(
                        F::effect_row(&nodes[index(scope.action)].effects),
                        budget,
                    )
                    .map_err(|_| Failure::Resource)?;
                    graph.types.0.push(Type::function_computation(
                        Type::Unit,
                        crate::types::ComputationType::new(Type::Unit, effects),
                    ));
                    Control::Cleanup {
                        body: index(scope.body) + 1,
                        action: index(scope.action) + 1,
                        row_type,
                        source: scope.span,
                    }
                }
                Some(EffectOperation::Registration(scope)) => Control::Registration {
                    body: index(scope.body) + 1,
                    source: scope.span,
                },
                Some(EffectOperation::Resource(resource)) => {
                    let api = resource.acquisition.api().ok_or(Failure::Invalid)?;
                    let fallible = api.is_native_buffer();
                    charge(budget, usize::from(fallible))?;
                    graph
                        .code
                        .try_reserve(1 + usize::from(fallible))
                        .map_err(|_| Failure::Resource)?;
                    let scope = graph.code.len();
                    data.position(scope, id, budget)?;
                    let mut arguments = Vec::new();
                    charge(budget, 1)?;
                    arguments.try_reserve(1).map_err(|_| Failure::Resource)?;
                    arguments.push(Type::Variable(resource.acquisition.identity));
                    let effect = EffectInstance::new(api.ops(), arguments.into_boxed_slice());
                    graph.code.push(Control::Resource {
                        body: index(resource.body) + 1,
                        effect: Request::effect(&effect, resource.acquisition.span, budget)?,
                    });
                    let acquisition = if fallible {
                        // Initializer completion precedes this choice. Failure
                        // returns without installing a resource frame or owner.
                        let choice = graph.code.len();
                        data.position(choice, id, budget)?;
                        graph
                            .code
                            .push(Control::Choice(copy_slice(&[0, scope], budget)?));
                        choice
                    } else {
                        scope
                    };
                    Control::Sequence(copy_slice(
                        &[index(resource.initializer) + 1, acquisition],
                        budget,
                    )?)
                }
                Some(EffectOperation::ProviderScope(scope)) => {
                    charge(
                        budget,
                        scope
                            .handler
                            .clauses()
                            .len()
                            .checked_add(5)
                            .ok_or(Failure::Resource)?,
                    )?;
                    graph.code.try_reserve(5).map_err(|_| Failure::Resource)?;
                    let mut clauses = Vec::new();
                    clauses
                        .try_reserve_exact(scope.handler.clauses().len())
                        .map_err(|_| Failure::Resource)?;
                    for clause in scope.handler.clauses() {
                        clauses.push(Clause {
                            operation: Some(clause.operation()),
                            body: index(clause.body()) + 1,
                            owner: *owners
                                .get(&(scope.handler.id(), clause.resume()))
                                .ok_or(Failure::Invalid)?,
                            source: clause.origin().primary_span(),
                        });
                    }
                    let handler = graph.code.len();
                    data.position_provider_handler(handler, id, budget)?;
                    graph.code.push(Control::Handler {
                        body: index(scope.handler.body()) + 1,
                        effect: Request::effect(scope.handler.effect(), source, budget)?,
                        clauses,
                    });
                    let row_type = graph.types.0.len();
                    charge(budget, 3)?;
                    graph
                        .types
                        .0
                        .try_reserve(1)
                        .map_err(|_| Failure::Resource)?;
                    let effects = crate::types::clone_effect_row_with_budget(
                        F::effect_row(&nodes[index(scope.finish.body)].effects),
                        budget,
                    )
                    .map_err(|_| Failure::Resource)?;
                    graph.types.0.push(Type::function_computation(
                        Type::Unit,
                        crate::types::ComputationType::new(Type::Unit, effects),
                    ));
                    let completed = graph.code.len();
                    data.position(completed, id, budget)?;
                    graph.code.push(Control::Cleanup {
                        body: handler,
                        action: index(scope.finish.body) + 1,
                        row_type,
                        source,
                    });
                    let choice = graph.code.len();
                    data.position(choice, id, budget)?;
                    graph
                        .code
                        .push(Control::Choice(copy_slice(&[0, completed], budget)?));
                    let acquisition = graph.code.len();
                    data.position(acquisition, id, budget)?;
                    graph.code.push(Control::Sequence(copy_slice(
                        &[index(scope.acquire.body) + 1, choice],
                        budget,
                    )?));
                    let owner = graph.code.len();
                    data.position(owner, id, budget)?;
                    graph.code.push(Control::Resource {
                        body: acquisition,
                        effect: Request::effect(scope.descriptor.native_effect(), source, budget)?,
                    });
                    Control::Sequence(copy_slice(&[index(scope.initializer) + 1, owner], budget)?)
                }
                Some(EffectOperation::Request(request)) => {
                    graph.code.try_reserve(1).map_err(|_| Failure::Resource)?;
                    let perform = graph.code.len();
                    data.position(perform, id, budget)?;
                    let mut inferred = Request::effect(request.effect(), source, budget)?;
                    inferred.operation = Some(request.operation());
                    graph.code.push(Control::Request(inferred));
                    Control::Sequence(copy_slice(
                        &[index(request.operand()) + 1, perform],
                        budget,
                    )?)
                }
                Some(EffectOperation::Resume(resume)) => {
                    match owners.get(&(resume.handler(), resume.owner())) {
                        Some(owner) => Control::Resume {
                            owner: *owner,
                            value: index(resume.value()) + 1,
                        },
                        // A body-free provider forest has no client handler
                        // frame. Querying an unrelated callable grants no
                        // authority to reach its contextual continuation.
                        None if boundary.is_some() => {
                            let (ports, edges) = boundary.as_mut().ok_or(Failure::Invalid)?;
                            let port = ports.completion(id, resume.handler(), resume.owner())?;
                            charge(budget, 1)?;
                            edges.try_reserve(1).map_err(|_| Failure::Resource)?;
                            edges.push(ConditionalCompletionEdge {
                                port,
                                node: id,
                                operand: Some(index(resume.value()) + 1),
                            });
                            Control::Unavailable
                        }
                        None if provider_query => Control::Unavailable,
                        None => return Err(Failure::Invalid),
                    }
                }
                Some(EffectOperation::Discard(discard)) => {
                    if !owners.contains_key(&(discard.handler(), discard.owner())) {
                        let (ports, edges) = boundary.as_mut().ok_or(Failure::Invalid)?;
                        let port = ports.completion(id, discard.handler(), discard.owner())?;
                        charge(budget, 1)?;
                        edges.try_reserve(1).map_err(|_| Failure::Resource)?;
                        edges.push(ConditionalCompletionEdge {
                            port,
                            node: id,
                            operand: None,
                        });
                        Control::Unavailable
                    } else {
                        Control::Discard {
                            owner: *owners
                                .get(&(discard.handler(), discard.owner()))
                                .ok_or(Failure::Invalid)?,
                            node: id,
                            local: true,
                            row_type: {
                                charge(budget, 3)?;
                                graph
                                    .types
                                    .0
                                    .try_reserve(1)
                                    .map_err(|_| Failure::Resource)?;
                                let row_type = graph.types.0.len();
                                graph.types.0.push(Type::function_computation(
                                    Type::Unit,
                                    crate::types::ComputationType::new(
                                        Type::Unit,
                                        crate::types::clone_effect_row_with_budget(
                                            F::effect_row(&node.effects),
                                            budget,
                                        )
                                        .map_err(|_| Failure::Resource)?,
                                    ),
                                ));
                                row_type
                            },
                            source,
                        }
                    }
                }
                Some(EffectOperation::Handler(handler)) => {
                    let mut clauses = Vec::new();
                    clauses
                        .try_reserve(handler.clauses().len())
                        .map_err(|_| Failure::Resource)?;
                    for clause in handler.clauses() {
                        clauses.push(Clause {
                            operation: Some(clause.operation()),
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
    methods: &[MethodUse],
    adapters: &[MethodAdapter],
    budget: &mut TypeWorkBudget,
) -> Result<Vec<CaptureValueSummary>, Failure> {
    check_nodes_with_methods(
        &builder.nodes,
        globals,
        imports,
        operation,
        methods,
        adapters,
        budget,
    )
}

pub(super) fn check_nodes<F: CoreOperationFamily>(
    nodes: &[StoredNode<F>],
    globals: &[(BinderId, NodeId)],
    imports: &[(BinderId, &CaptureValueSummary)],
    operation: fn(&F::Kind) -> Option<&EffectOperation>,
    budget: &mut TypeWorkBudget,
) -> Result<Vec<CaptureValueSummary>, Failure> {
    check_nodes_with_methods(nodes, globals, imports, operation, &[], &[], budget)
}

fn check_nodes_with_methods<F: CoreOperationFamily>(
    nodes: &[StoredNode<F>],
    globals: &[(BinderId, NodeId)],
    imports: &[(BinderId, &CaptureValueSummary)],
    operation: fn(&F::Kind) -> Option<&EffectOperation>,
    methods: &[MethodUse],
    adapters: &[MethodAdapter],
    budget: &mut TypeWorkBudget,
) -> Result<Vec<CaptureValueSummary>, Failure> {
    analyze_nodes_with_methods(
        nodes, globals, imports, operation, methods, adapters, None, None, budget,
    )
}

/// Query roots are actual nodes, not invented global definitions. Lexical
/// bindings and callable groups are reconstructed from the checked graph.
pub(super) fn check_provider_roots_with_methods(
    nodes: &[StoredNode<super::effect::EffectOperationFamily>],
    flow: &super::provider::ProviderLocalFlow<'_>,
    imports: &[(BinderId, &CaptureValueSummary)],
    operation: fn(&super::EffectExprKind) -> Option<&EffectOperation>,
    methods: &[MethodUse],
    adapters: &[MethodAdapter],
    budget: &mut TypeWorkBudget,
) -> Result<Vec<CaptureValueSummary>, Failure> {
    let (root, lexical, data, instantiations, dictionary_variables) =
        flow.inputs(nodes).ok_or(Failure::Invalid)?;
    analyze_nodes_with_methods(
        nodes,
        &[],
        imports,
        operation,
        methods,
        adapters,
        None,
        Some((&[root], lexical, data, instantiations, dictionary_variables)),
        budget,
    )
}

pub(crate) fn infer_cleanup_rows<F: CoreOperationFamily>(
    builder: &CoreBuilder<F>,
    globals: &[(BinderId, NodeId)],
    imports: &[(BinderId, &CaptureValueSummary)],
    operation: fn(&F::Kind) -> Option<&EffectOperation>,
    methods: &[MethodUse],
    adapters: &[MethodAdapter],
    budget: &mut TypeWorkBudget,
) -> Result<Vec<CleanupRequirement>, Failure> {
    let mut rows = Vec::new();
    analyze_nodes_with_methods(
        &builder.nodes,
        globals,
        imports,
        operation,
        methods,
        adapters,
        Some(&mut rows),
        None,
        budget,
    )?;
    Ok(rows)
}

// Actual roots, lexical binders, independently proven data binders,
// canonical source-instantiation ports, and unproved raw dictionary ports.
// Only the opaque provider-flow entry supplies these borrowed inputs.
type ProviderSummaryRoots<'a> = (
    &'a [NodeId],
    &'a [BinderId],
    &'a [BinderId],
    &'a [NodeId],
    &'a [NodeId],
);

#[allow(
    clippy::too_many_arguments,
    reason = "the existing complete graph inputs are shared by safety and optional cleanup-row queries"
)]
fn analyze_nodes_with_methods<F: CoreOperationFamily>(
    nodes: &[StoredNode<F>],
    globals: &[(BinderId, NodeId)],
    imports: &[(BinderId, &CaptureValueSummary)],
    operation: fn(&F::Kind) -> Option<&EffectOperation>,
    methods: &[MethodUse],
    adapters: &[MethodAdapter],
    rows: Option<&mut Vec<CleanupRequirement>>,
    summary_roots: Option<ProviderSummaryRoots<'_>>,
    budget: &mut TypeWorkBudget,
) -> Result<Vec<CaptureValueSummary>, Failure> {
    let Some(BuiltCaptureGraph {
        graph,
        roots,
        values,
        has_discard,
    }) = build_capture_graph(
        nodes,
        globals,
        imports,
        operation,
        methods,
        adapters,
        summary_roots,
        None,
        budget,
    )?
    else {
        return Ok(Vec::new());
    };
    if let Some(rows) = rows {
        *rows = cleanup_requirements(&graph, &roots, budget)?;
    } else if summary_roots.is_none() {
        if has_discard {
            let requirements = cleanup_requirements(&graph, &roots, budget)?;
            check_cleanup_rows(nodes, operation, &requirements, budget)?;
        }
        check_control_roots(&graph, roots, budget)?;
    }
    let graph = Arc::new(graph);
    let mut summaries = Vec::new();
    if let Some((roots, _, _, _, _)) = summary_roots {
        charge(budget, roots.len())?;
        summaries
            .try_reserve_exact(roots.len())
            .map_err(|_| Failure::Resource)?;
        for root in roots {
            summaries.push(CaptureValueSummary {
                graph: Some(Arc::clone(&graph)),
                value: values
                    .get(index(*root))
                    .ok_or(Failure::Invalid)?
                    .copy(budget)?,
            });
        }
    } else {
        summaries
            .try_reserve(globals.len())
            .map_err(|_| Failure::Resource)?;
        for (_, node) in globals {
            summaries.push(CaptureValueSummary {
                graph: Some(Arc::clone(&graph)),
                value: values[index(*node)].copy(budget)?,
            });
        }
    }
    Ok(summaries)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ConditionalContinuationInputId(usize);
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ConditionalOutputInputId(usize);
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ConditionalCaptureInputId(usize);

struct ConditionalClausePort {
    handler: super::effect::HandlerId,
    resume: crate::resolved::ResumeId,
    operation: crate::types::OperationId,
    root: NodeId,
    continuation: ConditionalContinuationInputId,
    output: ConditionalOutputInputId,
    capture: ConditionalCaptureInputId,
    input: crate::types::IterativeTypeOwner,
    answer: crate::types::TypeVariableId,
    residual: crate::types::TypeVariableId,
}
struct ConditionalCapturePorts {
    clauses: Vec<ConditionalClausePort>,
    completions: HashMap<usize, usize>,
}
impl ConditionalCapturePorts {
    fn completion(
        &self,
        node: usize,
        handler: super::effect::HandlerId,
        resume: crate::resolved::ResumeId,
    ) -> Result<usize, Failure> {
        let port = *self.completions.get(&node).ok_or(Failure::Invalid)?;
        let clause = self.clauses.get(port).ok_or(Failure::Invalid)?;
        if clause.handler != handler || clause.resume != resume {
            return Err(Failure::Invalid);
        }
        Ok(port)
    }
}
#[derive(Debug)]
struct ConditionalCompletionEdge {
    port: usize,
    node: usize,
    operand: Option<usize>,
}
struct ConditionalDiscardCaptureEdge {
    input: super::provider::CaptureInputId,
    source: NodeId,
    projected: NodeId,
    handler: super::effect::HandlerId,
    resume: crate::resolved::ResumeId,
    clause: NodeId,
    owner: usize,
}

/// Owns unresolved graph-local continuation and capture inputs. No ordinary
/// Analysis entry or callable value-summary conversion is provided.
pub(in crate::core) struct ConditionalCaptureGraph {
    template: crate::resolved::ProviderTemplateId,
    graph: SummaryGraph,
    roots: Vec<usize>,
    ports: ConditionalCapturePorts,
    edges: Vec<ConditionalCompletionEdge>,
    discards: Vec<ConditionalDiscardCaptureEdge>,
    source_arena: super::dialect::ArenaId,
    projected_arena: super::dialect::ArenaId,
    correspondence: Vec<Option<NodeId>>,
}
struct ConditionalTypeReplacements(HashMap<TypeVariableId, Type>);
impl ConditionalTypeReplacements {
    /// Transfers an already charged clone into the reserved substitution table.
    fn insert_reserved(&mut self, variable: TypeVariableId, ty: Type) {
        if let Some(displaced) = self.0.insert(variable, ty) {
            discard_type_iteratively(displaced);
        }
    }
}
impl Drop for ConditionalTypeReplacements {
    fn drop(&mut self) {
        for (_, ty) in self.0.drain() {
            discard_type_iteratively(ty);
        }
    }
}

#[expect(
    clippy::too_many_arguments,
    reason = "the sealed defining entry and authenticated projection supply actual graph, import, method and source occurrence facts"
)]
pub(in crate::core) fn reconstruct_conditional_handler_capture(
    entry: &super::provider::HandlerFragmentEntry<'_>,
    nodes: &[StoredNode<super::effect::EffectOperationFamily>],
    projected_arena: super::dialect::ArenaId,
    correspondence: &[Option<NodeId>],
    imports: &[(BinderId, &CaptureValueSummary)],
    methods: &[MethodUse],
    adapters: &[MethodAdapter],
    instantiations: &[NodeId],
    dictionary_variables: &[NodeId],
    budget: &mut TypeWorkBudget,
) -> Result<ConditionalCaptureGraph, Failure> {
    let mut ports = ConditionalCapturePorts {
        clauses: Vec::new(),
        completions: HashMap::new(),
    };
    let mut roots = Vec::new();
    let mut lexical = Vec::new();
    for stored in nodes {
        charge(
            budget,
            stored
                .kind
                .child_count()
                .checked_add(1)
                .ok_or(Failure::Resource)?,
        )?;
        for ordinal in 0..stored.kind.child_count() {
            let child = stored.kind.child_at(ordinal).ok_or(Failure::Invalid)?;
            if child.arena() != projected_arena || index(child) >= nodes.len() {
                return Err(Failure::Invalid);
            }
        }
    }
    let project = |node: NodeId| -> Result<NodeId, Failure> {
        if node.arena() != entry.draft.program.arena {
            return Err(Failure::Invalid);
        }
        let target = correspondence
            .get(index(node))
            .copied()
            .flatten()
            .ok_or(Failure::Invalid)?;
        if target.arena() != projected_arena || index(target) >= nodes.len() {
            return Err(Failure::Invalid);
        }
        Ok(target)
    };
    charge(
        budget,
        entry
            .draft
            .clauses
            .len()
            .checked_mul(3)
            .and_then(|count| count.checked_add(entry.draft.program.nodes.len()))
            .ok_or(Failure::Resource)?,
    )?;
    ports
        .clauses
        .try_reserve_exact(entry.draft.clauses.len())
        .map_err(|_| Failure::Resource)?;
    ports
        .completions
        .try_reserve(entry.draft.program.nodes.len())
        .map_err(|_| Failure::Resource)?;
    roots
        .try_reserve_exact(entry.draft.clauses.len())
        .map_err(|_| Failure::Resource)?;
    lexical.try_reserve(1).map_err(|_| Failure::Resource)?;
    lexical.push(entry.draft.state.id());
    let instance = &entry.definition.provided.instance;
    let effect = entry
        .canonical
        .effect(instance.effect())
        .ok_or(Failure::Invalid)?;
    let mut replacements = ConditionalTypeReplacements(HashMap::new());
    charge(budget, effect.parameters.len())?;
    replacements
        .0
        .try_reserve(effect.parameters.len())
        .map_err(|_| Failure::Resource)?;
    if effect.parameters.len() != instance.arguments().len() {
        return Err(Failure::Invalid);
    }
    let mut row_replacements = HashMap::new();
    row_replacements
        .try_reserve(effect.parameters.len())
        .map_err(|_| Failure::Resource)?;
    for (formal, argument) in effect.parameters.iter().zip(instance.arguments()) {
        charge(budget, 1)?;
        match (&formal.kind, argument) {
            (crate::types::Kind::EffectRow, crate::types::KindedArgument::RowArg(row)) => {
                if row_replacements
                    .insert(
                        formal.id,
                        crate::types::clone_effect_row_with_budget(row, budget)
                            .map_err(|()| Failure::Resource)?,
                    )
                    .is_some()
                {
                    return Err(Failure::Invalid);
                }
            }
            (kind, crate::types::KindedArgument::TypeArg(ty))
                if *kind != crate::types::Kind::EffectRow =>
            {
                if replacements.0.contains_key(&formal.id) {
                    return Err(Failure::Invalid);
                }
                replacements.insert_reserved(
                    formal.id,
                    clone_type_with_budget(ty, budget).map_err(|()| Failure::Resource)?,
                );
            }
            _ => return Err(Failure::Invalid),
        }
    }
    for (ordinal, clause) in entry.draft.clauses.iter().enumerate() {
        let root = project(clause.body())?;
        let operation = effect
            .operations
            .get(usize::try_from(clause.operation().operation()).map_err(|_| Failure::Invalid)?)
            .filter(|operation| operation.id == clause.operation())
            .ok_or(Failure::Invalid)?;
        let signature = crate::types::IterativeTypeOwner::new(
            crate::types::substitute_type_and_row_variables_with(
                &operation.annotation.ty,
                &replacements.0,
                &row_replacements,
                |cells| charge(budget, cells),
                || Failure::Resource,
            )?
            .map_err(|_| Failure::Invalid)?,
        );
        let input = signature.function_view().ok_or(Failure::Invalid)?.value();
        ports.clauses.push(ConditionalClausePort {
            handler: entry.draft.handler,
            resume: clause.resume(),
            operation: clause.operation(),
            root,
            continuation: ConditionalContinuationInputId(ordinal),
            output: ConditionalOutputInputId(0),
            capture: ConditionalCaptureInputId(ordinal),
            input: crate::types::IterativeTypeOwner::new(
                clone_type_with_budget(input, budget).map_err(|()| Failure::Resource)?,
            ),
            answer: entry.draft.hidden[0].0,
            residual: entry.draft.hidden[1].0,
        });
        roots.push(root);
        for binder in clause.pattern().binder_iter() {
            charge(budget, 1)?;
            lexical.try_reserve(1).map_err(|_| Failure::Resource)?;
            lexical.push(binder.id());
        }
    }
    for (ordinal, original) in entry.draft.program.nodes.iter().enumerate() {
        charge(budget, 1)?;
        let (handler, resume) = match &original.kind {
            super::effect::EffectExprKind::Operation(EffectOperation::Resume(resume)) => {
                (resume.handler(), resume.owner())
            }
            super::effect::EffectExprKind::Operation(EffectOperation::Discard(discard)) => {
                (discard.handler(), discard.owner())
            }
            _ => continue,
        };
        if handler != entry.draft.handler {
            continue;
        }
        let original_id = NodeId::new(
            entry.draft.program.arena,
            u32::try_from(ordinal).map_err(|_| Failure::Resource)?,
        );
        let target = project(original_id)?;
        let mut selected = None;
        for (port, clause) in ports.clauses.iter().enumerate() {
            charge(budget, 1)?;
            if clause.handler == handler && clause.resume == resume {
                selected = Some(port);
                break;
            }
        }
        let selected = selected.ok_or(Failure::Invalid)?;
        match &original.kind {
            super::effect::EffectExprKind::Operation(EffectOperation::Resume(resume)) => {
                let operand = entry
                    .draft
                    .program
                    .nodes
                    .get(index(resume.value()))
                    .ok_or(Failure::Invalid)?;
                if !same_type_with_budget(&operand.ty, &ports.clauses[selected].input, budget)
                    .map_err(|()| Failure::Resource)?
                    || !same_type_with_budget(
                        &original.ty,
                        &Type::Variable(ports.clauses[selected].answer),
                        budget,
                    )
                    .map_err(|()| Failure::Resource)?
                {
                    return Err(Failure::Invalid);
                }
            }
            super::effect::EffectExprKind::Operation(EffectOperation::Discard(_)) => {
                if !same_type_with_budget(&original.ty, &Type::Unit, budget)
                    .map_err(|()| Failure::Resource)?
                {
                    return Err(Failure::Invalid);
                }
            }
            _ => return Err(Failure::Invalid),
        }
        let target_node = nodes.get(index(target)).ok_or(Failure::Invalid)?;
        let preserved = match (&original.kind, &target_node.kind) {
            (
                super::effect::EffectExprKind::Operation(EffectOperation::Resume(original)),
                super::effect::EffectExprKind::Operation(EffectOperation::Resume(actual)),
            ) => {
                actual.handler() == handler
                    && actual.owner() == resume
                    && actual.value() == project(original.value())?
            }
            (
                super::effect::EffectExprKind::Operation(EffectOperation::Discard(_)),
                super::effect::EffectExprKind::Operation(EffectOperation::Discard(actual)),
            ) => actual.handler() == handler && actual.owner() == resume,
            _ => false,
        };
        if !preserved || ports.completions.insert(index(target), selected).is_some() {
            return Err(Failure::Invalid);
        }
    }
    let mut edges = Vec::new();
    let built = build_capture_graph(
        nodes,
        &[],
        imports,
        |kind| match kind {
            super::effect::EffectExprKind::Operation(operation) => Some(operation),
            _ => None,
        },
        methods,
        adapters,
        Some((&roots, &lexical, &[], instantiations, dictionary_variables)),
        Some((&ports, &mut edges)),
        budget,
    )?
    .ok_or(Failure::Invalid)?;
    if edges.len() != ports.completions.len() {
        return Err(Failure::Invalid);
    }
    let mut discards = Vec::new();
    if let Some(recipe) = entry.row_recipe {
        charge(budget, recipe.discards().len())?;
        discards
            .try_reserve_exact(recipe.discards().len())
            .map_err(|_| Failure::Resource)?;
        for port in recipe.discards() {
            charge(budget, 1)?;
            let projected = project(port.node)?;
            // Every current pending discard belongs to a real nested owner.
            // Provider-entry discards, if source checking later admits them,
            // need their own unresolved external completion edge.
            let Control::Discard {
                owner,
                node: actual,
                ..
            } = built
                .graph
                .code
                .get(index(projected) + 1)
                .ok_or(Failure::Invalid)?
            else {
                return Err(Failure::Invalid);
            };
            if *actual != index(projected) {
                return Err(Failure::Invalid);
            }
            let mut found = false;
            for (ordinal, original) in entry.draft.program.nodes.iter().enumerate() {
                charge(budget, 1)?;
                let super::effect::EffectExprKind::Operation(EffectOperation::Handler(handler)) =
                    &original.kind
                else {
                    continue;
                };
                if handler.id() != port.handler {
                    continue;
                }
                let handler_id = NodeId::new(
                    entry.draft.program.arena,
                    u32::try_from(ordinal).map_err(|_| Failure::Resource)?,
                );
                let actual = project(handler_id)?;
                let Control::Handler { clauses, .. } = built
                    .graph
                    .code
                    .get(index(actual) + 1)
                    .ok_or(Failure::Invalid)?
                else {
                    return Err(Failure::Invalid);
                };
                charge(budget, handler.clauses().len())?;
                if handler.clauses().len() != clauses.len() {
                    return Err(Failure::Invalid);
                }
                for (source, actual) in handler.clauses().iter().zip(clauses) {
                    if source.resume() == port.resume {
                        if actual.owner != *owner
                            || actual.operation != Some(source.operation())
                            || source.body() != port.clause
                            || actual.body != index(project(source.body())?) + 1
                        {
                            return Err(Failure::Invalid);
                        }
                        found = true;
                    }
                }
            }
            if !found {
                return Err(Failure::Invalid);
            }
            discards.push(ConditionalDiscardCaptureEdge {
                input: recipe
                    .capture_input_for_discard(port.node)
                    .ok_or(Failure::Invalid)?,
                source: port.node,
                projected,
                handler: port.handler,
                resume: port.resume,
                clause: port.clause,
                owner: *owner,
            });
        }
    }
    let mut codes = Vec::new();
    charge(budget, roots.len())?;
    codes
        .try_reserve_exact(roots.len())
        .map_err(|_| Failure::Resource)?;
    codes.extend(roots.iter().map(|root| index(*root) + 1));
    charge(budget, correspondence.len())?;
    let mut retained = Vec::new();
    retained
        .try_reserve_exact(correspondence.len())
        .map_err(|_| Failure::Resource)?;
    retained.extend_from_slice(correspondence);
    Ok(ConditionalCaptureGraph {
        template: entry.draft.template,
        graph: built.graph,
        roots: codes,
        ports,
        edges,
        discards,
        source_arena: entry.draft.program.arena,
        projected_arena,
        correspondence: retained,
    })
}

struct BuiltCaptureGraph {
    graph: SummaryGraph,
    roots: Vec<usize>,
    values: Vec<Value>,
    has_discard: bool,
}

#[expect(
    clippy::too_many_arguments,
    reason = "capture graph construction retains exact code, import, method, root and work inputs before choosing an analysis"
)]
fn build_capture_graph<F: CoreOperationFamily>(
    nodes: &[StoredNode<F>],
    globals: &[(BinderId, NodeId)],
    imports: &[(BinderId, &CaptureValueSummary)],
    operation: fn(&F::Kind) -> Option<&EffectOperation>,
    methods: &[MethodUse],
    adapters: &[MethodAdapter],
    summary_roots: Option<ProviderSummaryRoots<'_>>,
    boundary: Option<(
        &ConditionalCapturePorts,
        &mut Vec<ConditionalCompletionEdge>,
    )>,
    budget: &mut TypeWorkBudget,
) -> Result<Option<BuiltCaptureGraph>, Failure> {
    charge(budget, nodes.len() + globals.len())?;
    let mut bindings = HashMap::new();
    bindings
        .try_reserve(globals.len())
        .map_err(|_| Failure::Resource)?;
    bindings.extend(globals.iter().map(|(binder, node)| (*binder, index(*node))));
    let imported = ImportedCallables::new(imports, nodes.len(), budget)?;
    let mut has_discard = false;
    let mut resource_scope = None;
    let mut parameters = HashMap::new();
    for (id, node) in nodes.iter().enumerate() {
        if let Some(EffectOperation::Cleanup(scope)) = operation(&node.kind) {
            resource_scope.get_or_insert(scope.span);
        }
        if let Some(EffectOperation::Resource(resource)) = operation(&node.kind) {
            resource_scope.get_or_insert(resource.acquisition.span);
        }
        if let Some(EffectOperation::ProviderScope(_)) = operation(&node.kind) {
            resource_scope
                .get_or_insert(node.origin.as_ref().ok_or(Failure::Invalid)?.primary_span());
        }
        if let Some(EffectOperation::Registration(scope)) = operation(&node.kind) {
            resource_scope.get_or_insert(scope.span);
        }
        has_discard |= matches!(operation(&node.kind), Some(EffectOperation::Discard(_)));
        match F::pure(&node.kind) {
            Some(PureExprKind::Value(PureValue::Function(function))) => {
                parameters.try_reserve(1).map_err(|_| Failure::Resource)?;
                parameters.insert(function.parameter().id(), id);
            }
            Some(PureExprKind::Computation(PureComputation::Match(matching))) => {
                for arm in matching.arms() {
                    for binder in arm.pattern().binder_iter() {
                        charge(budget, 1)?;
                        bindings.try_reserve(1).map_err(|_| Failure::Resource)?;
                        bindings.insert(binder.id(), index(matching.scrutinee()));
                    }
                }
            }
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
    if !has_discard
        && resource_scope.is_none()
        && globals.is_empty()
        && summary_roots.is_none_or(|(roots, _, _, _, _)| roots.is_empty())
    {
        return Ok(None);
    }

    let values = solve_capture_values(nodes, &bindings, &parameters, &imported, operation, budget)?;

    // Canonical source roots and unproved raw producer roots both retain
    // their actual value ports. The latter are subsequently Unknown; neither
    // may be replaced by a canonical binder capture from below the cut.
    let mut capture_ports = Vec::new();
    let ports: &[NodeId] = if let Some((_, _, _, instantiations, dictionary_variables)) =
        summary_roots
        && !dictionary_variables.is_empty()
    {
        let count = instantiations
            .len()
            .checked_add(dictionary_variables.len())
            .ok_or(Failure::Resource)?;
        charge(budget, count)?;
        capture_ports
            .try_reserve_exact(count)
            .map_err(|_| Failure::Resource)?;
        capture_ports.extend_from_slice(instantiations);
        capture_ports.extend_from_slice(dictionary_variables);
        &capture_ports[..]
    } else {
        summary_roots.map_or(&[][..], |(_, _, _, instantiations, _)| instantiations)
    };
    let mut data = value::Graph::build(
        nodes,
        globals,
        imports,
        &imported,
        operation,
        methods,
        adapters,
        summary_roots.map_or(&[], |(_, _, data, _, _)| data),
        ports,
        budget,
    )?;
    if let Some((_, lexical, _, _, dictionary_variables)) = summary_roots {
        data.retain_provider_lexical(nodes, lexical, budget)?;
        data.refuse_provider_dictionary_variables(nodes, dictionary_variables, budget)?;
    }
    let (mut graph, roots) = compile_with_boundary(
        nodes,
        &values,
        &imported,
        operation,
        &mut data,
        summary_roots.is_some(),
        boundary,
        budget,
    )?;
    graph.data = Some(Arc::new(data));
    Ok(Some(BuiltCaptureGraph {
        graph,
        roots,
        values,
        has_discard,
    }))
}

// The finite-value fixed point completes before typed graph construction, so
// their temporary frames do not overlap on the bounded capture-checking stack.
fn solve_capture_values<F: CoreOperationFamily>(
    nodes: &[StoredNode<F>],
    bindings: &HashMap<BinderId, usize>,
    parameters: &HashMap<BinderId, usize>,
    imported: &ImportedCallables,
    operation: fn(&F::Kind) -> Option<&EffectOperation>,
    budget: &mut TypeWorkBudget,
) -> Result<Vec<Value>, Failure> {
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
                Some(PureExprKind::Value(PureValue::Function(_) | PureValue::Intrinsic(_))) => {
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
                    if let Some(parameter) = parameters.get(&variable.binder()) {
                        value.unknown = false;
                        value.parameter(*parameter, budget)?;
                    }
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
                    PureComputation::Tuple(tuple) => {
                        for element in tuple.elements() {
                            value.join(&values[index(*element)], budget)?;
                        }
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
                                result.relocate(offset, budget)?;
                                result = result.instantiate(
                                    *target,
                                    &values[index(application.argument())],
                                    budget,
                                )?;
                                value.join(&result, budget)?;
                                continue;
                            }
                            if matches!(
                                F::pure(&nodes[*target].kind),
                                Some(PureExprKind::Value(PureValue::Intrinsic(_)))
                            ) {
                                continue;
                            }
                            let Some(PureExprKind::Value(PureValue::Function(function))) =
                                F::pure(&nodes[*target].kind)
                            else {
                                return Err(Failure::Invalid);
                            };
                            let result = values[index(function.body())].instantiate(
                                *target,
                                &values[index(application.argument())],
                                budget,
                            )?;
                            value.join(&result, budget)?;
                        }
                    }
                    _ => {}
                },
                _ => match operation(&node.kind) {
                    Some(EffectOperation::Cleanup(scope)) => {
                        value = values[index(scope.body)].copy(budget)?;
                    }
                    Some(EffectOperation::Registration(scope)) => {
                        value = values[index(scope.body)].copy(budget)?;
                    }
                    Some(EffectOperation::Resource(resource)) => {
                        value = values[index(resource.body)].copy(budget)?;
                    }
                    Some(EffectOperation::ProviderScope(scope)) => {
                        value.join(&values[index(scope.handler.body())], budget)?;
                        for clause in scope.handler.clauses() {
                            value.join(&values[index(clause.body())], budget)?;
                        }
                    }
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
            charge(budget, values[id].work_size() + value.work_size())?;
            if values[id] != value {
                values[id] = value;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    Ok(values)
}

// Keep solver storage out of the graph-construction caller's stack frame.
fn cleanup_requirements(
    graph: &SummaryGraph,
    roots: &[usize],
    budget: &mut TypeWorkBudget,
) -> Result<Vec<CleanupRequirement>, Failure> {
    charge(budget, graph.code.len())?;
    // Only Cleanup nodes contribute inferred close rows. The complete graph
    // includes imported callable bodies; absence proves the empty row without
    // another control fixed point. Safety and row authentication still run.
    if !graph
        .code
        .iter()
        .any(|code| matches!(code, Control::Cleanup { .. }))
    {
        return Ok(Vec::new());
    }
    let mut analysis = Analysis::new(graph, None, budget)?;
    analysis.infer_cleanup_rows = true;
    analysis.check(roots, budget)?;
    Ok(std::mem::take(&mut analysis.cleanup_rows))
}

fn check_cleanup_rows<F: CoreOperationFamily>(
    nodes: &[StoredNode<F>],
    operation: fn(&F::Kind) -> Option<&EffectOperation>,
    requirements: &[CleanupRequirement],
    budget: &mut TypeWorkBudget,
) -> Result<(), Failure> {
    let mut checked = std::collections::HashSet::new();
    for requirement in requirements {
        charge(budget, 1)?;
        let key = (requirement.code, requirement.context);
        if checked.contains(&key) {
            continue;
        }
        checked.try_reserve(1).map_err(|_| Failure::Resource)?;
        checked.insert(key);
        let mut row = EffectRow::empty();
        for action in requirements {
            charge(budget, 1)?;
            if (action.code, action.context) != key {
                continue;
            }
            let mut next = crate::types::clone_effect_row_with_budget(&action.row, budget)
                .map_err(|_| Failure::Resource)?;
            for effect in &action.retained {
                match next
                    .remove_exact_with_budget(effect, budget)
                    .map_err(|_| Failure::Resource)?
                {
                    Ok(rest) => next = rest,
                    Err(crate::types::EffectRowError::Missing) => {}
                    Err(_) => return Err(Failure::Invalid),
                }
            }
            row = row
                .union_with_budget(&next, budget)
                .map_err(|_| Failure::Resource)?
                .map_err(|_| Failure::Invalid)?;
        }
        if !crate::types::same_effect_rows_with_budget(&row, &requirement.expected, budget)
            .map_err(|_| Failure::Resource)?
        {
            return Err(Failure::CleanupRow {
                node: requirement.discard,
                source: requirement.source,
            });
        }
    }
    for (id, node) in nodes.iter().enumerate() {
        charge(budget, 1)?;
        if !matches!(operation(&node.kind), Some(EffectOperation::Discard(_))) {
            continue;
        }
        let mut lexical = false;
        for requirement in requirements {
            charge(budget, 1)?;
            if requirement.local && requirement.discard == id && requirement.context == 0 {
                lexical = true;
                break;
            }
        }
        if !lexical && !F::effect_row(&node.effects).is_empty() {
            return Err(Failure::CleanupRow {
                node: id,
                source: node.origin.as_ref().ok_or(Failure::Invalid)?.primary_span(),
            });
        }
    }
    Ok(())
}

// Keep solver storage out of the graph-construction caller's stack frame.
fn check_control_roots(
    graph: &SummaryGraph,
    roots: Vec<usize>,
    budget: &mut TypeWorkBudget,
) -> Result<(), Failure> {
    charge(budget, graph.code.len())?;
    if graph.code.iter().any(|code| {
        matches!(
            code,
            Control::Discard { .. }
                | Control::Resource { .. }
                | Control::Registration { .. }
                | Control::Cleanup { .. }
        )
    }) {
        let mut queries = Vec::new();
        for root in roots {
            if query_required(graph, root, budget)? {
                queries.try_reserve(1).map_err(|_| Failure::Resource)?;
                queries.push(root);
            }
        }
        let mut analysis = Analysis::new(graph, None, budget)?;
        analysis.check(&queries, budget)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        source::{ByteRange, SourceFile},
        types::EffectRow,
    };

    #[test]
    fn stored_metadata_retains_row_tail_and_lacks_but_not_quantified_variables() {
        let row = TypeVariableId::generated(800);
        let resource = TypeVariableId::generated(801);
        let bound = TypeVariableId::generated(802);
        let effect = crate::types::EffectId::new(crate::module::ModuleId::new(0), 0);
        let effects = EffectRow::open(
            crate::types::EffectRowVariable::Rigid(row),
            Box::new([EffectInstance::new(
                effect,
                Box::new([Type::Variable(resource)]),
            )]),
        );
        let ty = Type::Forall(
            Box::new([(bound, crate::types::Kind::Type)]),
            Box::new(Type::EffectfulFunction(
                Box::new(Type::Variable(bound)),
                Box::new(crate::types::ComputationType::new(Type::Unit, effects)),
            )),
        );
        let mut value = MetadataVariables::default();
        retain_type_variables(&mut value, &ty, &mut TypeWorkBudget::default()).unwrap();
        assert!(value.variables.contains(&row));
        assert!(value.variables.contains(&resource));
        assert!(!value.variables.contains(&bound));
    }

    #[test]
    fn wide_row_metadata_charges_pending_slots_before_reservation() {
        const WIDTH: usize = 256;
        let row_identity = TypeVariableId::generated(803);
        let effect = crate::types::EffectId::new(crate::module::ModuleId::new(0), 0);
        let row = EffectRow::open(
            crate::types::EffectRowVariable::Rigid(row_identity),
            Box::new([EffectInstance::new(
                effect,
                vec![Type::Unit; WIDTH].into_boxed_slice(),
            )]),
        );
        // The root copy, row visit, retained tail identity and effect visit use
        // seven cells. Admit all pending argument slots before reserving them.
        let mut value = MetadataVariables::default();
        let mut short = TypeWorkBudget::with_limit(7 + WIDTH - 1);
        assert!(matches!(
            retain_row_variables(&mut value, &row, &mut short),
            Err(Failure::Resource)
        ));
        assert_eq!(short.used(), 7);
        assert!(value.variables.is_empty());
        assert!(value.identities.is_empty());

        // Each argument has one admitted slot, a tag visit and a Unit visit;
        // the final free tail identity costs another four cells to retain.
        for _ in 0..2 {
            let mut value = MetadataVariables::default();
            let mut exact = TypeWorkBudget::with_limit(3 * WIDTH + 11);
            retain_row_variables(&mut value, &row, &mut exact).unwrap();
            assert_eq!(exact.used(), 3 * WIDTH + 11);
            assert_eq!(value.variables, vec![row_identity]);
            assert_eq!(value.identities.len(), 1);
        }
    }

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
    fn final_core_recomputes_owned_capture_after_same_typed_call_target_change() {
        use super::super::{EffectExprKind, validate_effect, variable::VariableNode};
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
        let validated = validate_effect(core, &[&source])
            .expect("the changed target's captured clause is structurally owned");
        assert!(matches!(
            crate::eval::evaluate_effect(&validated).unwrap().value,
            crate::eval::Value::Unit
        ));
    }

    #[test]
    fn final_core_recomputes_registration_callback_completion_from_actual_target() {
        use super::super::{EffectExprKind, validate_effect, variable::VariableNode};
        let source = "effect Adjust {\npublish : Int -> Int\n}\neffect Stop {\nstop : Int -> Int\n}\ngood : Int -> Int ! {Stop}\ngood value = value\nbad : Int -> Int ! {Stop}\nbad value = perform Stop.stop value\nmain : Unit -> Int\nmain () = handle (hook Adjust {\nregister Adjust good {\nperform Adjust.publish 42\n}\n}) with Stop {\nstop value => {\nlet done = discard\nvalue\n}\n}\n";
        let (core, file, good, _) = checked_core_text(source);
        super::super::validate::registration_proof_check(
            &core,
            &[&file],
            &[(good.module().unwrap(), file.id())],
        )
        .unwrap();
        let validated = validate_effect(core, &[&file]).unwrap();
        assert_eq!(
            crate::eval::evaluate_effect(&validated)
                .unwrap()
                .value
                .to_string(),
            "42"
        );
        for pass in 0..3 {
            let (mut core, file, good, bad) = checked_core_text(source);
            let binding_type = |binder| {
                core.nodes
                    .iter()
                    .find_map(|node| match &node.kind {
                        EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(
                            binding,
                        ))) if binding.binder().id() == binder => Some(binding.binder().ty()),
                        EffectExprKind::Pure(PureExprKind::Computation(
                            PureComputation::RecursiveBind(binding),
                        )) => binding
                            .members()
                            .iter()
                            .find(|member| member.binder().id() == binder)
                            .map(|member| member.binder().ty()),
                        _ => None,
                    })
                    .unwrap()
            };
            assert_eq!(binding_type(good), binding_type(bad));
            if pass > 0 {
                let module = good.module().unwrap();
                let program = super::super::validate::registration_proof_program(
                    core,
                    &[&file],
                    &[(module, file.id())],
                );
                core = if pass == 1 {
                    super::super::transform::identity_effect_traversal(&program)
                } else {
                    super::super::transform::fold_effect_literal_primitives(&program)
                }
                .unwrap();
            }
            let mut replacements = 0;
            for node in &mut core.nodes {
                if matches!(&node.kind, EffectExprKind::Pure(PureExprKind::Variable(variable)) if variable.binder() == good)
                {
                    node.kind =
                        EffectExprKind::Pure(PureExprKind::Variable(VariableNode::new(bad)));
                    replacements += 1;
                }
            }
            assert_eq!(replacements, 1);
            super::super::validate::registration_proof_check(
                &core,
                &[&file],
                &[(good.module().unwrap(), file.id())],
            )
            .expect("the callback's publication and registration are owned by this capture");
            let validated = validate_effect(core, &[&file]).unwrap();
            assert_eq!(
                crate::eval::evaluate_effect(&validated)
                    .unwrap()
                    .value
                    .to_string(),
                "42"
            );
        }
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
        for (case, body) in [
            "handle (perform A.ask ()) with A {\nask ignored => {\nlet _ = handle ({\nlet _ = perform B.ask ()\nresume ()\n}) with B {\nask ignored => discard\n}\n()\n}\n}",
            "handle (handle (handle (perform C.ask ()) with C {\nask ignored => {\nlet _ = perform A.ask ()\nlet _ = perform B.ask ()\nresume ()\n}\n}) with A {\nask ignored => handle ({\nlet _ = resume ()\nperform B.ask ()\n}) with B {\nask ignored => discard\n}\n}) with B {\nask ignored => resume ()\n}",
        ].into_iter().enumerate() {
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
            let result = validate_effect(core, &[module.source()]);
            if case == 0 {
                assert_eq!(result.expect_err("outside live clause remains protected").reason(), ValidationReason::DiscardUnsafe);
            } else {
                let validated = result.expect("restored clauses contained in the selected capture are owned");
                assert!(matches!(crate::eval::evaluate_effect(&validated).unwrap().value, crate::eval::Value::Unit));
            }
        }
    }

    #[test]
    fn raw_core_preserves_the_selected_capture_prefix() {
        use super::super::{
            EffectExprKind, binding::BindingNode, effect::DiscardNode, validate_effect,
            variable::TypedBinder,
        };
        for fixture in [
            include_str!("../../tests/fixtures/effects/capture-prefix-before.ash"),
            include_str!("../../tests/fixtures/effects/capture-prefix-after.ash"),
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
            let validated = validate_effect(core, &[&source]).expect(
                "prefix clauses are either consumed outside or owned inside the selected capture",
            );
            assert!(matches!(
                crate::eval::evaluate_effect(&validated).unwrap().value,
                crate::eval::Value::Unit
            ));
        }
    }

    #[test]
    fn linked_core_reselects_handlers_when_type_instances_coincide() {
        use super::super::{
            EffectExprKind, binding::BindingNode, effect::DiscardNode, validate_effect_modules,
            variable::TypedBinder,
        };
        for argument in ["(1, true)", "(1, 1)"] {
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
            let validated = validate_effect_modules(core, &[&source], &[(module, source.id())])
                .expect("coincident specialized handlers add only structurally owned clauses");
            assert!(matches!(
                crate::eval::evaluate_effect(&validated).unwrap().value,
                crate::eval::Value::Unit
            ));
        }
    }

    #[test]
    fn empty_cleanup_query_charges_the_complete_graph_before_returning() {
        for width in [1, 4096] {
            let graph = SummaryGraph {
                effects: true,
                data: None,
                callables: vec![],
                types: TypeArguments(vec![]),
                code: (0..width).map(|_| Control::Return).collect(),
            };
            assert!(matches!(
                cleanup_requirements(&graph, &[0], &mut TypeWorkBudget::with_limit(width - 1)),
                Err(Failure::Resource)
            ));
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(width);
                assert!(
                    cleanup_requirements(&graph, &[0], &mut exact)
                        .unwrap()
                        .is_empty()
                );
                assert_eq!(exact.used(), width);
            }
        }
    }

    #[test]
    fn no_cleanup_graph_still_rejects_a_forged_nonempty_discard_row() {
        use super::super::EffectExprKind;
        let (mut core, _, _, _) = checked_core();
        let operation: fn(&EffectExprKind) -> Option<&EffectOperation> = |kind| match kind {
            EffectExprKind::Operation(operation) => Some(operation),
            _ => None,
        };
        assert!(
            !core
                .nodes
                .iter()
                .any(|node| matches!(operation(&node.kind), Some(EffectOperation::Cleanup(_))))
        );
        let row = core
            .nodes
            .iter()
            .find(|node| matches!(operation(&node.kind), Some(EffectOperation::Request(_))))
            .unwrap();
        let row = crate::types::clone_effect_row_with_budget(
            &row.effects,
            &mut TypeWorkBudget::unbounded(),
        )
        .unwrap();
        let discard = core
            .nodes
            .iter_mut()
            .find(|node| matches!(operation(&node.kind), Some(EffectOperation::Discard(_))))
            .unwrap();
        discard.effects = row;
        assert!(matches!(
            check_nodes(
                &core.nodes,
                &[],
                &[],
                operation,
                &mut TypeWorkBudget::default()
            ),
            Err(Failure::CleanupRow { .. })
        ));
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
                effects: true,
                data: None,
                types: TypeArguments(Vec::new()),
                callables: Vec::new(),
                code: Vec::new(),
            })),
            value: Value {
                targets: Vec::new(),
                unknown: true,
                ..Value::default()
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
            effects: true,
            data: None,
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
    fn method_use_index_preserves_same_node_order_and_exact_work() {
        use crate::interface::{InterfaceId, MethodId, RequirementId, RequirementOwner};

        let source = SourceFile::new("method-index", "x").unwrap();
        let origin =
            crate::source::Origin::Source(source.span(ByteRange::new(0, 1).unwrap()).unwrap());
        let mut builder = crate::core::EffectCoreBuilder::with_effect_registry(Arc::new(
            crate::resolved::ResolvedRegistry::new(Vec::new(), Vec::new()),
        ));
        let first = builder.unit(Type::Unit, origin.clone()).unwrap();
        let second = builder.unit(Type::Unit, origin).unwrap();
        let module = crate::module::ModuleId::new(44_210);
        let binder = BinderId::resolved(module, 0);
        let interface = InterfaceId::new(module, 0);
        let requirement = RequirementId::new(RequirementOwner::Global(binder), 0);
        let methods = [
            MethodUse {
                node: first,
                target: MethodTarget::Binder(binder),
                method: MethodId::new(interface, 0),
                requirement: None,
                arguments: 0,
            },
            MethodUse {
                node: second,
                target: MethodTarget::Abstract(requirement),
                method: MethodId::new(interface, 1),
                requirement: Some(requirement),
                arguments: 1,
            },
            MethodUse {
                node: first,
                target: MethodTarget::Abstract(requirement),
                method: MethodId::new(interface, 2),
                requirement: Some(requirement),
                arguments: 2,
            },
            MethodUse {
                node: first,
                target: MethodTarget::Abstract(requirement),
                method: MethodId::new(interface, 3),
                requirement: Some(RequirementId::new(RequirementOwner::Global(binder), 1)),
                arguments: 3,
            },
        ];
        let mut construction_short = TypeWorkBudget::with_limit(3 * methods.len() - 1);
        assert!(matches!(
            MethodUses::new(&methods, &mut construction_short),
            Err(Failure::Resource)
        ));
        assert_eq!(construction_short.used(), 0);
        let run = |budget: &mut TypeWorkBudget| {
            let indexed = MethodUses::new(&methods, budget)?;
            let same_node = indexed.at(index(first), budget)?;
            assert_eq!(same_node.len(), 3);
            assert!(std::ptr::eq(same_node[0], &methods[0]));
            assert!(std::ptr::eq(same_node[1], &methods[2]));
            assert!(std::ptr::eq(same_node[2], &methods[3]));
            assert!(std::ptr::eq(
                indexed.at(index(second), budget)?[0],
                &methods[1]
            ));
            assert!(indexed.at(usize::MAX, budget)?.is_empty());
            Ok::<(), Failure>(())
        };
        // Three construction cells per record, then lookup + matching records.
        const EXACT: usize = 3 * 4 + (1 + 3) + (1 + 1) + 1;
        assert!(matches!(
            run(&mut TypeWorkBudget::with_limit(EXACT - 1)),
            Err(Failure::Resource)
        ));
        for _ in 0..2 {
            let mut budget = TypeWorkBudget::with_limit(EXACT);
            run(&mut budget).unwrap();
            assert_eq!(budget.used(), EXACT);
        }
        let mut zero = TypeWorkBudget::with_limit(0);
        assert!(
            MethodUses::new(&[], &mut zero)
                .unwrap()
                .at(0, &mut zero)
                .unwrap()
                .is_empty()
        );
    }

    #[test]
    fn capture_graph_visits_charge_aliases_and_distinct_graphs_with_fresh_retries() {
        let make_summary = || CaptureValueSummary {
            graph: Some(Arc::new(SummaryGraph {
                effects: false,
                data: None,
                callables: Vec::new(),
                types: TypeArguments(vec![Type::Int]),
                code: (0..16).map(|_| Control::Return).collect(),
            })),
            value: Value::default(),
        };
        let first = make_summary();
        let alias = first.clone();
        let distinct = make_summary();
        let scan = |budget: &mut TypeWorkBudget| {
            let mut visits = CaptureGraphVisits::default();
            let mut count = 0;
            for summary in [&first, &alias, &distinct] {
                if visits.visit(summary, budget)? {
                    for ty in summary.types(budget)? {
                        budget.charge(1)?;
                        assert_eq!(*ty, Type::Int);
                        count += 1;
                    }
                }
            }
            Ok::<_, ()>(count)
        };
        // Each distinct graph: lookup + retained key + 17 carrier positions
        // + one fallible retained type slot + one yielded type. The alias adds only one lookup.
        const EXACT: usize = 2 * (2 + 17 + 1 + 1) + 1;
        assert!(scan(&mut TypeWorkBudget::with_limit(EXACT - 1)).is_err());
        for _ in 0..2 {
            let mut budget = TypeWorkBudget::with_limit(EXACT);
            assert_eq!(scan(&mut budget), Ok(2));
            assert_eq!(budget.used(), EXACT);
        }
        let absent = CaptureValueSummary::default();
        assert_eq!(
            CaptureGraphVisits::default().visit(&absent, &mut TypeWorkBudget::with_limit(0)),
            Ok(false),
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
                effects: true,
                data: None,
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
        // Each graph additionally charges the tagged argument scan, exact effect
        // identity/argument slots, and the argument dispatch.
        let expected = 2 * (2 * entries + 6);
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
                let mut data = value::Graph::build(
                    &builder.nodes,
                    &[],
                    &[],
                    &imported,
                    operation,
                    &[],
                    &[],
                    &[],
                    &[],
                    &mut TypeWorkBudget::unbounded(),
                )
                .unwrap();
                // Compilation charges the node carrier and each of these two
                // nodes before cloning the function type. This boundary used to
                // exhaust in the following Value copy, before Callable existed.
                let mut partial = TypeWorkBudget::with_limit(
                    builder.nodes.len() + 1 + builder.nodes.len() + clone_work.used(),
                );
                assert!(matches!(
                    compile(
                        &builder.nodes,
                        &values,
                        &imported,
                        operation,
                        &mut data,
                        false,
                        &mut partial
                    ),
                    Err(Failure::Resource)
                ));
                let mut measured = TypeWorkBudget::unbounded();
                drop(
                    compile(
                        &builder.nodes,
                        &values,
                        &imported,
                        operation,
                        &mut data,
                        false,
                        &mut measured,
                    )
                    .unwrap(),
                );
                let mut retry = TypeWorkBudget::with_limit(measured.used());
                drop(
                    compile(
                        &builder.nodes,
                        &values,
                        &imported,
                        operation,
                        &mut data,
                        false,
                        &mut retry,
                    )
                    .unwrap(),
                );
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
                        &[],
                        &[],
                        &mut TypeWorkBudget::with_limit(128)
                    ),
                    Err(Failure::Resource)
                ));
                check_builder(
                    &builder,
                    &roots,
                    &[],
                    operation,
                    &[],
                    &[],
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
                        effects: true,
                        data: None,
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
                        ..Value::default()
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

    #[test]
    fn actual_provider_query_keeps_contextual_resumes_unavailable() {
        use super::super::{EffectExprKind, PureComputation, PureExprKind};
        let (mut core, _source, good, bad) = checked_core_text(concat!(
            "effect H {\nop : Unit -> Unit\n}\n",
            "good : Unit -> Unit\ngood value = value\n",
            "bad : Unit -> Unit\nbad value = handle (perform H.op value) with H {\nop value => resume value\n}\n",
            "main : Unit -> Unit\nmain value = good value\n",
        ));
        let target = |binder| {
            core.nodes
                .iter()
                .find_map(|node| match &node.kind {
                    EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(
                        binding,
                    ))) if binding.binder().id() == binder => Some(binding.initializer()),
                    EffectExprKind::Pure(PureExprKind::Computation(
                        PureComputation::RecursiveBind(binding),
                    )) => binding
                        .members()
                        .iter()
                        .find(|member| member.binder().id() == binder)
                        .map(|member| member.initializer()),
                    _ => None,
                })
                .unwrap()
        };
        let good_root = target(good);
        let bad_root = target(bad);
        let summarize = |nodes: &[StoredNode<super::super::effect::EffectOperationFamily>],
                         root: NodeId,
                         provider: bool| {
            analyze_nodes_with_methods(
                nodes,
                &[(good, good_root)],
                &[],
                |kind| match kind {
                    EffectExprKind::Operation(op) => Some(op),
                    _ => None,
                },
                &[],
                &[],
                None,
                provider.then_some((&[root][..], &[][..], &[][..], &[][..], &[][..])),
                &mut TypeWorkBudget::unbounded(),
            )
        };
        let honest = summarize(&core.nodes, bad_root, true).unwrap();
        let graph = honest[0].graph.as_ref().unwrap();
        assert!(graph.code.iter().any(|code| matches!(code, Control::Resume { owner, .. } if graph.code.get(*owner).is_some_and(|code| matches!(code, Control::Return)))));
        let resume = core
            .nodes
            .iter_mut()
            .find_map(|node| match &mut node.kind {
                EffectExprKind::Operation(EffectOperation::Resume(resume)) => Some(resume),
                _ => None,
            })
            .unwrap();
        resume.handler = super::super::effect::HandlerId::new(u32::MAX);
        assert!(matches!(
            summarize(&core.nodes, good_root, false),
            Err(Failure::Invalid)
        ));
        let good_summary = summarize(&core.nodes, good_root, true).unwrap();
        good_summary[0]
            .check_provider_independent_typed_call(
                &core.nodes[index(good_root)].ty,
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap();
        let selected = summarize(&core.nodes, bad_root, true).unwrap();
        assert!(
            selected[0]
                .graph
                .as_ref()
                .unwrap()
                .code
                .iter()
                .any(|code| matches!(code, Control::Unavailable))
        );
        assert!(matches!(
            selected[0].check_provider_independent_typed_call(
                &core.nodes[index(bad_root)].ty,
                &mut TypeWorkBudget::unbounded()
            ),
            Err(Failure::Invalid)
        ));
    }
}

#[cfg(test)]
mod provider_capture_tests {
    use super::*;
    #[test]
    fn provider_typed_query_checks_ignored_top_level_stored_dependencies() {
        let actual = Type::Function(Box::new(Type::Unit), Box::new(Type::Unit));
        for (metadata, unknown, captured) in [
            (None, true, true),
            (Some(TypeVariableId::Generated(991)), false, true),
            (None, false, true),
            (None, false, false),
        ] {
            let summary = CaptureValueSummary {
                graph: Some(Arc::new(SummaryGraph {
                    effects: false,
                    callables: vec![Callable {
                        body: 0,
                        ty: actual.clone(),
                        result: Value::default(),
                    }],
                    code: vec![Control::Return],
                    types: TypeArguments(Vec::new()),
                    data: Some(Arc::new(value::provider_typed_capture_graph_for_test(
                        metadata, unknown, captured,
                    ))),
                })),
                value: Value {
                    targets: vec![0],
                    unknown: false,
                    ..Value::default()
                },
            };
            let checked = summary
                .check_provider_independent_typed_call(&actual, &mut TypeWorkBudget::unbounded());
            assert_eq!(
                checked.is_ok(),
                !captured,
                "metadata={metadata:?} unknown={unknown}"
            );
        }
    }

    #[test]
    fn provider_typed_query_rejects_actual_unavailable_control() {
        let actual = Type::Function(Box::new(Type::Unit), Box::new(Type::Unit));
        let summary = CaptureValueSummary {
            graph: Some(Arc::new(SummaryGraph {
                effects: true,
                callables: vec![Callable {
                    body: 0,
                    ty: actual.clone(),
                    result: Value::default(),
                }],
                code: vec![Control::Unavailable],
                types: TypeArguments(Vec::new()),
                data: Some(Arc::new(value::provider_typed_capture_graph_for_test(
                    None, false, false,
                ))),
            })),
            value: Value {
                targets: vec![0],
                unknown: false,
                ..Value::default()
            },
        };
        let mut measured = TypeWorkBudget::unbounded();
        assert!(matches!(
            summary.check_provider_independent_typed_call(&actual, &mut measured),
            Err(Failure::Invalid)
        ));
        let cost = measured.used();
        for prefix in [0, 17] {
            let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
            short.charge(prefix).unwrap();
            assert!(matches!(
                summary.check_provider_independent_typed_call(&actual, &mut short),
                Err(Failure::Resource)
            ));
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(prefix + cost);
                exact.charge(prefix).unwrap();
                assert!(matches!(
                    summary.check_provider_independent_typed_call(&actual, &mut exact),
                    Err(Failure::Invalid)
                ));
                assert_eq!(exact.used(), prefix + cost);
            }
        }
    }

    fn summary(metadata: Option<TypeVariableId>, unknown: bool) -> CaptureValueSummary {
        CaptureValueSummary {
            graph: Some(Arc::new(SummaryGraph {
                effects: false,
                callables: vec![Callable {
                    body: 0,
                    ty: Type::Function(Box::new(Type::Unit), Box::new(Type::Unit)),
                    result: Value::default(),
                }],
                code: vec![Control::Return],
                types: TypeArguments(Vec::new()),
                data: Some(Arc::new(value::provider_capture_graph_for_test(
                    metadata, unknown,
                ))),
            })),
            value: Value {
                targets: vec![0],
                parameters: Vec::new(),
                unknown: false,
            },
        }
    }
    #[test]
    fn provider_capture_rejects_selected_unknown_and_unresolved_lexical_captures() {
        for unknown in [false, true] {
            assert!(matches!(
                summary(None, unknown)
                    .check_provider_independent_data_call(&[], &mut TypeWorkBudget::unbounded()),
                Err(Failure::Invalid)
            ));
        }
    }
    #[test]
    fn provider_capture_metadata_requires_actual_occurrence_instantiation() {
        let formal = TypeVariableId::generated(19);
        let summary = summary(Some(formal), false);
        assert!(matches!(
            summary.check_provider_independent_data_call(
                &[TypeVariableId::generated(20)],
                &mut TypeWorkBudget::unbounded()
            ),
            Err(Failure::Invalid)
        ));
        let mut measured = TypeWorkBudget::unbounded();
        summary
            .check_provider_independent_data_call(&[formal], &mut measured)
            .unwrap();
        let cost = measured.used();
        for prefix in [0, 13] {
            let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
            short.charge(prefix).unwrap();
            assert!(matches!(
                summary.check_provider_independent_data_call(&[formal], &mut short),
                Err(Failure::Resource)
            ));
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(prefix + cost);
                exact.charge(prefix).unwrap();
                summary
                    .check_provider_independent_data_call(&[formal], &mut exact)
                    .unwrap();
                assert_eq!(exact.used(), prefix + cost);
            }
        }
    }
}

#[cfg(test)]
pub(crate) fn conditional_capture_inventory_for_test(
    draft: &super::provider::HandlerFragmentDraft,
    module: &crate::resolved::ResolvedModule,
    work: &mut TypeWorkBudget,
) -> Result<(usize, usize, usize), Failure> {
    let entry = super::provider::HandlerFragmentEntry::reconstruct(draft, module, work).map_err(
        |error| {
            if error.reason() == super::ValidationReason::Resource {
                Failure::Resource
            } else {
                Failure::Invalid
            }
        },
    )?;
    let correspondence = (0..draft.program.nodes.len())
        .map(|ordinal| Some(NodeId::new(draft.program.arena, ordinal as u32)))
        .collect::<Vec<_>>();
    let graph = reconstruct_conditional_handler_capture(
        &entry,
        &draft.program.nodes,
        draft.program.arena,
        &correspondence,
        &[],
        &[],
        &[],
        &[],
        &[],
        work,
    )?;
    assert_eq!(graph.template, draft.template);
    assert_eq!(graph.roots.len(), draft.clauses.len());
    for edge in &graph.edges {
        let port = &graph.ports.clauses[edge.port];
        assert_eq!(port.output, ConditionalOutputInputId(0));
        assert_eq!(port.answer, draft.hidden[0].0);
        assert_eq!(port.residual, draft.hidden[1].0);
        assert!(matches!(
            graph.graph.code[edge.node + 1],
            Control::Unavailable
        ));
        if let Some(operand) = edge.operand {
            assert!(operand < graph.graph.code.len());
        }
        assert!(graph.roots.contains(&(index(port.root) + 1)));
    }
    let nested = graph
        .graph
        .code
        .iter()
        .filter(|code| matches!(code, Control::Handler { .. }))
        .count();
    Ok((graph.ports.clauses.len(), graph.edges.len(), nested))
}

#[cfg(test)]
pub(in crate::core) fn owned_conditional_capture_links_for_test(
    graph: &ConditionalCaptureGraph,
    draft: &super::provider::HandlerFragmentDraft,
    recipe: &super::provider::HandlerRowRecipeDraft,
) {
    assert_eq!(graph.template, draft.template);
    assert_eq!(graph.source_arena, draft.program.arena);
    assert_eq!(graph.correspondence.len(), draft.program.nodes.len());
    assert_eq!(graph.ports.clauses.len(), draft.clauses.len());
    for (ordinal, (port, clause)) in graph
        .ports
        .clauses
        .iter()
        .zip(draft.clauses.iter())
        .enumerate()
    {
        assert_eq!(
            (port.handler, port.resume, port.operation),
            (draft.handler, clause.resume(), clause.operation())
        );
        assert_eq!(
            port.root,
            graph.correspondence[index(clause.body())].unwrap()
        );
        assert_eq!(port.root.arena(), graph.projected_arena);
        assert_eq!(port.continuation, ConditionalContinuationInputId(ordinal));
        assert_eq!(port.capture, ConditionalCaptureInputId(ordinal));
        assert_eq!(graph.roots[ordinal], index(port.root) + 1);
        assert_eq!(port.output, ConditionalOutputInputId(0));
        assert_eq!(
            (port.answer, port.residual),
            (draft.hidden[0].0, draft.hidden[1].0)
        );
    }
    assert_eq!(graph.discards.len(), recipe.discards().len());
    for edge in &graph.discards {
        assert_eq!(
            recipe.capture_input_for_discard(edge.source),
            Some(edge.input)
        );
        assert_eq!(
            edge.projected,
            graph.correspondence[index(edge.source)].unwrap()
        );
        let original = &draft.program.nodes[index(edge.source)];
        let super::effect::EffectExprKind::Operation(EffectOperation::Discard(discard)) =
            &original.kind
        else {
            panic!("retained actual discard")
        };
        assert_eq!(
            (discard.handler(), discard.owner()),
            (edge.handler, edge.resume)
        );
        assert_eq!(edge.clause.arena(), graph.source_arena);
        let Control::Discard { owner, node, .. } = &graph.graph.code[index(edge.projected) + 1]
        else {
            panic!("actual capture discard")
        };
        assert_eq!((*owner, *node), (edge.owner, index(edge.projected)));
    }
    for (ordinal, original) in draft.program.nodes.iter().enumerate() {
        let super::effect::EffectExprKind::Operation(EffectOperation::Cleanup(scope)) =
            &original.kind
        else {
            continue;
        };
        let actual = graph.correspondence[ordinal].unwrap();
        let Control::Cleanup {
            body,
            action,
            source,
            ..
        } = &graph.graph.code[index(actual) + 1]
        else {
            panic!("actual armed cleanup")
        };
        assert_eq!(
            *body,
            index(graph.correspondence[index(scope.body)].unwrap()) + 1
        );
        assert_eq!(
            *action,
            index(graph.correspondence[index(scope.action)].unwrap()) + 1
        );
        assert_eq!(*source, scope.span);
    }
    for (ordinal, original) in draft.program.nodes.iter().enumerate() {
        let super::effect::EffectExprKind::Operation(EffectOperation::Request(request)) =
            &original.kind
        else {
            continue;
        };
        let projected = graph.correspondence[ordinal].unwrap();
        let Control::Sequence(sequence) = &graph.graph.code[index(projected) + 1] else {
            panic!("retained request evaluation")
        };
        assert_eq!(sequence.len(), 2);
        assert_eq!(
            sequence[0],
            index(graph.correspondence[index(request.operand())].unwrap()) + 1
        );
        let Control::Request(actual) = &graph.graph.code[sequence[1]] else {
            panic!("retained actual request")
        };
        assert_eq!(actual.operation, Some(request.operation()));
        assert_eq!(actual.effect.as_deref(), Some(request.effect()));
    }
    for edge in &graph.edges {
        let port = &graph.ports.clauses[edge.port];
        let (ordinal, original) = draft
            .program
            .nodes
            .iter()
            .enumerate()
            .find(|(ordinal, _)| {
                graph.correspondence[*ordinal].is_some_and(|id| index(id) == edge.node)
            })
            .unwrap();
        assert_eq!(graph.ports.completions.get(&edge.node), Some(&edge.port));
        match &original.kind {
            super::effect::EffectExprKind::Operation(EffectOperation::Resume(resume)) => {
                assert_eq!(
                    (resume.handler(), resume.owner()),
                    (port.handler, port.resume)
                );
                assert_eq!(
                    edge.operand,
                    Some(index(graph.correspondence[index(resume.value())].unwrap()) + 1)
                );
                assert_eq!(&*port.input, &draft.program.nodes[index(resume.value())].ty);
                assert_eq!(original.ty, Type::Variable(port.answer));
            }
            super::effect::EffectExprKind::Operation(EffectOperation::Discard(discard)) => {
                assert_eq!(
                    (discard.handler(), discard.owner()),
                    (port.handler, port.resume)
                );
                assert_eq!(edge.operand, None);
            }
            _ => panic!("unresolved completion is tied to actual source completion at {ordinal}"),
        }
        assert!(edge.node < graph.graph.code.len().saturating_sub(1));
        assert!(matches!(
            graph.graph.code[edge.node + 1],
            Control::Unavailable
        ));
        assert!(edge.port < graph.ports.clauses.len());
    }
}

struct KindedArguments(Vec<crate::types::KindedArgument>);
impl KindedArguments {
    fn into_boxed_slice(mut self) -> Box<[crate::types::KindedArgument]> {
        std::mem::take(&mut self.0).into_boxed_slice()
    }
}
impl Drop for KindedArguments {
    fn drop(&mut self) {
        for argument in self.0.drain(..) {
            crate::types::discard_kinded_argument_iteratively(argument);
        }
    }
}
