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
        EffectInstance, Type, TypeVariableId, TypeWorkBudget, clone_type_with_budget,
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
                            }
                            | Control::Resource {
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
                }
                | Control::Resource {
                    effect: request, ..
                } => request.effect.as_ref().map(|effect| effect.effect()),
                _ => None,
            }))
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
    ambiguous_instance: bool,
    source: Span,
    operation: Option<crate::types::OperationId>,
}

impl Request {
    fn unknown(source: Span) -> Self {
        Self {
            effect: None,
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
    Clause(Span),
    Resource(Span),
    Registration(Span),
}

#[derive(Clone, Copy)]
pub(crate) struct MethodUse {
    pub(crate) node: NodeId,
    pub(crate) target: MethodTarget,
    pub(crate) method: crate::interface::MethodId,
    pub(crate) requirement: Option<crate::interface::RequirementId>,
    pub(crate) arguments: usize,
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

#[derive(Clone, Copy, Debug)]
pub(crate) enum Failure {
    Resource,
    Escape { source: Span, acquisition: Span },
    Invalid,
    Unsafe(UnsafeDiscard),
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
    methods: &[MethodUse],
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
        charge(budget, methods.len())?;
        for method in methods {
            if index(method.node) == id
                && method.requirement.is_none()
                && let MethodTarget::Binder(binder) | MethodTarget::Adapter { binder, .. } =
                    method.target
            {
                references.try_reserve(1).map_err(|_| Failure::Resource)?;
                references.push(binder);
            }
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
}

impl MetadataVariables {
    fn retain(
        &mut self,
        identity: TypeVariableId,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        charge(budget, self.variables.len() + 1)?;
        if !self.variables.contains(&identity) {
            self.variables
                .try_reserve(1)
                .map_err(|_| Failure::Resource)?;
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
    let mut bound = Vec::new();
    while let Some(metadata) = pending.pop() {
        charge(budget, 1)?;
        match metadata {
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
                    pending
                        .try_reserve(effect.arguments().len())
                        .map_err(|_| Failure::Resource)?;
                    pending.extend(effect.arguments().iter().map(Metadata::Type));
                }
            }
            _ => {}
        }
    }
    for variable in discovered.variables {
        charge(budget, bound.len())?;
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
            Some(EffectOperation::Handler(handler)) => {
                for argument in handler.effect().arguments() {
                    retain_type_variables(value, argument, budget)?;
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
        value.variables.len().saturating_mul(bound.len() + 1),
    )?;
    value.variables.retain(|variable| !bound.contains(variable));
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
    data: &mut value::Graph,
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
                Some(EffectOperation::Registration(scope)) => Control::Registration {
                    body: index(scope.body) + 1,
                    source: scope.span,
                },
                Some(EffectOperation::Resource(resource)) => {
                    graph.code.try_reserve(1).map_err(|_| Failure::Resource)?;
                    let scope = graph.code.len();
                    data.position(scope, id, budget)?;
                    let mut arguments = Vec::new();
                    charge(budget, 1)?;
                    arguments.try_reserve(1).map_err(|_| Failure::Resource)?;
                    arguments.push(Type::Variable(resource.acquisition.identity));
                    let effect = EffectInstance::new(
                        resource.acquisition.api().ok_or(Failure::Invalid)?.ops(),
                        arguments.into_boxed_slice(),
                    );
                    graph.code.push(Control::Resource {
                        body: index(resource.body) + 1,
                        effect: Request::effect(&effect, resource.acquisition.span, budget)?,
                    });
                    Control::Sequence(copy_slice(
                        &[index(resource.initializer) + 1, scope],
                        budget,
                    )?)
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
        if let Some(EffectOperation::Resource(resource)) = operation(&node.kind) {
            resource_scope.get_or_insert(resource.acquisition.span);
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
    if !has_discard && resource_scope.is_none() && globals.is_empty() {
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
                    Some(EffectOperation::Registration(scope)) => {
                        value = values[index(scope.body)].copy(budget)?;
                    }
                    Some(EffectOperation::Resource(resource)) => {
                        value = values[index(resource.body)].copy(budget)?;
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

    let mut data = value::Graph::build(
        nodes, globals, imports, &imported, operation, methods, adapters, budget,
    )?;
    let (mut graph, roots) = compile(nodes, &values, &imported, operation, &mut data, budget)?;
    graph.data = Some(Arc::new(data));
    check_control_roots(&graph, roots, budget)?;
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
            Control::Discard { .. } | Control::Resource { .. } | Control::Registration { .. }
        )
    }) {
        let mut queries = Vec::new();
        for root in roots {
            if query_required(graph, root, budget)? {
                queries.try_reserve(1).map_err(|_| Failure::Resource)?;
                queries.push(root);
            }
        }
        let mut analysis = Analysis::new(graph, budget)?;
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
    fn final_core_recomputes_registration_callback_completion_from_actual_target() {
        use super::super::{
            EffectExprKind, validate::ValidationReason, validate_effect, variable::VariableNode,
        };
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
            assert_eq!(
                super::super::validate::registration_proof_check(
                    &core,
                    &[&file],
                    &[(good.module().unwrap(), file.id())]
                )
                .unwrap_err()
                .reason(),
                ValidationReason::DiscardUnsafe
            );
            assert_eq!(
                validate_effect(core, &[&file]).unwrap_err().reason(),
                ValidationReason::DiscardUnsafe
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
                let mut data = value::Graph::build(
                    &builder.nodes,
                    &[],
                    &[],
                    &imported,
                    operation,
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
}
