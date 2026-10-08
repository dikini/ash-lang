//! Bounded inference of stored dependencies and request-carried obligations.
//!
//! Portable callable summaries retain finite value and control graphs. Stored
//! resource dependencies are distinct from completion obligations: copied
//! scalars are free, while actual closure/aggregate captures retain their owner.
//! Resource queries run even without discard, and reconstruct one fresh scope
//! occurrence at a time. Abandonment queries preserve live/consumed completion
//! owners across selected handler captures and restored continuations.

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

mod control;
mod value;
use control::{Analysis, Clause, Control, copy_slice, query_required};

use super::{
    CoreBuilder, NodeId, PureComputation, PureExprKind, PureValue,
    dialect::{CoreOperationFamily, StoredNode},
    effect::{EffectOperation, clone_effect_instance_with_budget},
    validate::AuthenticatedCaptureLayouts,
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
    #[cfg(test)]
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
            let callable = graph.callables.get(*target, budget)?;
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
                        pending.push(graph.callables.get(*target, budget)?.body);
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
        Analysis::provider_independent_call(
            graph,
            &self.value.targets,
            actual,
            false,
            false,
            budget,
        )
    }

    /// Only independently rebuilt canonical source wrappers use this entry.
    pub(crate) fn check_provider_source_wrapper_call(
        proof: &super::provider::ProviderSourceRelation,
        actual: &Type,
        allow_owned_scopes: bool,
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
        Analysis::provider_independent_call(
            graph,
            &summary.value.targets,
            actual,
            true,
            allow_owned_scopes,
            budget,
        )
    }

    /// Whether this summary retains a graph. Logical query projections also
    /// retain graphs; presence alone does not prove ordinary capture admission.
    pub(crate) fn has_graph(&self) -> bool {
        self.graph.is_some()
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
            budget.charge(graph.types.0.len())?;
            types.try_reserve(count).map_err(|_| ())?;
            graph
                .callables
                .extend_types(&mut types, budget)
                .map_err(|_| ())?;
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
                budget.charge(request.members.len())?;
                for member in &request.members {
                    crate::types::extend_owner_type_children_with_charge(
                        member.provided.arguments(),
                        &mut types,
                        budget,
                    )?;
                    crate::types::extend_owner_type_children_with_charge(
                        member.native.arguments(),
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
                budget.charge(request.members.len())?;
                for member in &request.members {
                    for effect in [&member.provided, &member.native] {
                        budget.charge(effect.arguments().len().checked_add(1).ok_or(())?)?;
                        identities.try_reserve(1).map_err(|_| ())?;
                        identities.push(effect.effect());
                        pending
                            .try_reserve(effect.arguments().len())
                            .map_err(|_| ())?;
                        pending.extend(effect.arguments());
                    }
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
    callables: CallableSlots,
    code: Vec<Control>,
    types: TypeArguments,
    data: Option<Arc<value::Graph>>,
}

// Dense original code coordinates remain stable even where no callable exists.
// Absence is metadata presence, never a test of the original callable's Type.
#[derive(Debug)]
struct CallableSlots {
    positions: Vec<Option<Callable>>,
    absent_unit: Type,
}

impl CallableSlots {
    fn new(budget: &mut TypeWorkBudget) -> Result<Self, Failure> {
        charge(budget, 1)?; // One private primitive universe witness.
        Ok(Self {
            positions: Vec::new(),
            absent_unit: Type::Unit,
        })
    }

    fn len(&self) -> usize {
        self.positions.len()
    }

    fn get(&self, target: usize, budget: &mut TypeWorkBudget) -> Result<&Callable, Failure> {
        charge(budget, 1)?; // Original position presence classification.
        self.positions
            .get(target)
            .and_then(Option::as_ref)
            .ok_or(Failure::Invalid)
    }

    // Preserve ascending original root order while collapsing only absent
    // metadata. The last absent position supplies the old LIFO first Unit.
    fn extend_types<'a>(
        &'a self,
        pending: &mut Vec<&'a Type>,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        charge(budget, self.positions.len())?; // Every presence classification.
        let mut absent = None;
        for position in &self.positions {
            match position {
                Some(callable) => {
                    charge(budget, 1)?; // Retained original type reference.
                    pending.try_reserve(1).map_err(|_| Failure::Resource)?;
                    pending.push(&callable.ty);
                }
                None => absent = Some(pending.len()),
            }
        }
        if let Some(position) = absent {
            // Witness read/retention plus the actual shifted reference suffix.
            charge(
                budget,
                pending
                    .len()
                    .checked_sub(position)
                    .and_then(|n| n.checked_add(2))
                    .ok_or(Failure::Resource)?,
            )?;
            pending.try_reserve(1).map_err(|_| Failure::Resource)?;
            pending.insert(position, &self.absent_unit);
        }
        Ok(())
    }
}

#[cfg(test)]
impl Default for CallableSlots {
    fn default() -> Self {
        Self {
            positions: Vec::new(),
            absent_unit: Type::Unit,
        }
    }
}

// Existing explicit test callables are all genuine metadata. Production never
// uses this conversion or an infallible allocator to publish a table.
#[cfg(test)]
impl From<Vec<Callable>> for CallableSlots {
    fn from(callables: Vec<Callable>) -> Self {
        Self {
            positions: callables.into_iter().map(Some).collect(),
            absent_unit: Type::Unit,
        }
    }
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
    callables: Vec<(&'a Option<Callable>, usize, usize)>,
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
                            .positions
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

    fn get(
        &self,
        target: usize,
        local_count: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<(&'a Callable, usize), Failure> {
        charge(budget, 1)?; // Imported original position presence classification.
        self.callables
            .get(target.checked_sub(local_count).ok_or(Failure::Invalid)?)
            .and_then(|(callable, offset, _)| callable.as_ref().map(|callable| (callable, *offset)))
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

/// Private transfer of a canonical storage result proved by the original
/// provider native-flow producer. No public constructor or runtime tag can
/// create this relation; composition must retain its exact request/member key.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum NativeStorageResult {
    Store {
        allocated: crate::types::ConstructorId,
        refused: crate::types::ConstructorId,
    },
    Load,
}

#[derive(Clone, Debug)]
struct Request {
    // None denotes admitted requests from an opaque open row.
    effect: Option<Arc<EffectInstance>>,
    opaque_row: Option<Arc<EffectRow>>,
    ambiguous_instance: bool,
    source: Span,
    operation: Option<crate::types::OperationId>,
    // Nonempty only for one admitted single-owner provider group. Source
    // dispatch removes this entire boundary, never a nested handler chain.
    members: Vec<ProviderCaptureMember>,
    clause_members: Vec<usize>,
    native_storage: Option<NativeStorageResult>,
}

#[derive(Clone, Debug)]
struct ProviderCaptureMember {
    provided: Arc<EffectInstance>,
    native: Arc<EffectInstance>,
}

impl Request {
    fn unknown(source: Span) -> Self {
        Self {
            effect: None,
            opaque_row: None,
            ambiguous_instance: false,
            source,
            operation: None,
            members: Vec::new(),
            clause_members: Vec::new(),
            native_storage: None,
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
            members: {
                charge(budget, self.members.len())?;
                let mut members = Vec::new();
                members
                    .try_reserve(self.members.len())
                    .map_err(|_| Failure::Resource)?;
                members.extend(self.members.iter().cloned());
                members
            },
            clause_members: if self.members.is_empty() {
                Vec::new()
            } else {
                copy_slice(&self.clause_members, budget)?
            },
            native_storage: self.native_storage,
        })
    }
}

#[derive(Default)]
struct Substitutions(HashMap<TypeVariableId, Type>);

#[derive(Debug)]
struct TypeArguments(Vec<Type>);

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

/// Analysis-local provenance; it never becomes a language row binder.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct ActualRequestContext {
    code: usize,
    label: usize,
    port: Option<usize>,
    value_context: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ActualDiscardCapture {
    code: usize,
    context: usize,
    request: ActualRequestContext,
}

#[derive(Debug)]
pub(crate) struct CleanupRequirement {
    pub(crate) discard: usize,
    pub(crate) local: bool,
    pub(crate) code: usize,
    pub(crate) source: Span,
    pub(crate) context: usize,
    request: ActualRequestContext,
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

/// Original method records and their immutable lexical-reference projection.
#[derive(Default)]
struct MethodUseGroup<'a> {
    records: Vec<&'a MethodUse>,
    free_binders: Vec<BinderId>,
    replaces_node: bool,
}

/// Analysis-local ordered method records indexed by their exact Core node.
struct MethodUses<'a> {
    by_node: HashMap<usize, MethodUseGroup<'a>>,
    native_layouts: Vec<crate::foreign::ForeignLayoutProducer>,
    authentic_layouts: Option<&'a AuthenticatedCaptureLayouts<'a>>,
    source_layouts: &'a [super::provider::AuthenticatedProviderSourceCapture<'a>],
    source_occurrences: Option<&'a super::dialect::AuthenticatedSourceLayoutOccurrences<'a>>,
    declared_payloads: Vec<TypeVariableId>,
}

impl<'a> MethodUses<'a> {
    fn new(methods: &'a [MethodUse], budget: &mut TypeWorkBudget) -> Result<Self, Failure> {
        Self::new_with_declared(methods, None, |_, _, _| Err(Failure::Invalid), budget)
    }

    fn new_for_nodes<F: CoreOperationFamily>(
        methods: &'a [MethodUse],
        nodes: &[StoredNode<F>],
        declared: Option<&super::provider::DeclaredLayoutMethods<'_>>,
        budget: &mut TypeWorkBudget,
    ) -> Result<Self, Failure> {
        Self::new_with_declared(
            methods,
            declared,
            |route, method, work| {
                declared
                    .ok_or(Failure::Invalid)?
                    .authenticates(nodes, method, route, work)
                    .map_err(|()| Failure::Resource)
            },
            budget,
        )
    }

    fn new_with_declared(
        methods: &'a [MethodUse],
        declared: Option<&super::provider::DeclaredLayoutMethods<'_>>,
        mut authenticate: impl FnMut(usize, &MethodUse, &mut TypeWorkBudget) -> Result<bool, Failure>,
        budget: &mut TypeWorkBudget,
    ) -> Result<Self, Failure> {
        // One input visit, at most one hash entry, and one retained reference
        // per record. Additional lexical descriptors and binder entries pay
        // once while deriving them from those same original records.
        let work = methods.len().checked_mul(3).ok_or(Failure::Resource)?;
        charge(budget, work)?;
        let mut by_node = HashMap::<usize, MethodUseGroup<'a>>::new();
        by_node
            .try_reserve(methods.len())
            .map_err(|_| Failure::Resource)?;
        let mut native_layouts = Vec::new();
        let mut declared_payloads = Vec::new();
        for (route, method) in methods.iter().enumerate() {
            if let MethodTarget::NativeLayout(producer) = method.target {
                charge(budget, 1)?;
                native_layouts
                    .try_reserve(1)
                    .map_err(|_| Failure::Resource)?;
                native_layouts.push(producer);
            }
            let group = match by_node.entry(index(method.node)) {
                std::collections::hash_map::Entry::Occupied(entry) => entry.into_mut(),
                std::collections::hash_map::Entry::Vacant(entry) => {
                    charge(budget, 1)?;
                    entry.insert(MethodUseGroup::default())
                }
            };
            if let MethodTarget::DeclaredLayout(descriptor) = method.target {
                if declared.is_none()
                    || method.requirement.is_some()
                    || method.arguments != 0
                    || !descriptor.matches(method.node, method.method)
                    || group.replaces_node
                    || !authenticate(route, method, budget)?
                {
                    return Err(Failure::Invalid);
                }
                charge(budget, 1)?;
                declared_payloads
                    .try_reserve(1)
                    .map_err(|_| Failure::Resource)?;
                declared_payloads.push(descriptor.payload());
            } else if declared.is_some() && method.requirement.is_none() {
                charge(budget, group.records.len())?;
                if group
                    .records
                    .iter()
                    .any(|prior| matches!(prior.target, MethodTarget::DeclaredLayout(_)))
                {
                    return Err(Failure::Invalid);
                }
            }
            group
                .records
                .try_reserve(1)
                .map_err(|_| Failure::Resource)?;
            if method.requirement.is_none() {
                if let MethodTarget::Binder(binder) | MethodTarget::Adapter { binder, .. } =
                    method.target
                {
                    charge(budget, 1)?;
                    group
                        .free_binders
                        .try_reserve(1)
                        .map_err(|_| Failure::Resource)?;
                    group.free_binders.push(binder);
                }
                group.replaces_node = true;
            }
            group.records.push(method);
        }
        Ok(Self {
            by_node,
            native_layouts,
            authentic_layouts: None,
            source_layouts: &[],
            source_occurrences: None,
            declared_payloads,
        })
    }

    fn at(&self, node: usize, budget: &mut TypeWorkBudget) -> Result<&[&'a MethodUse], Failure> {
        if self.by_node.is_empty() {
            return Ok(&[]);
        }
        charge(budget, 1)?;
        let records = self
            .by_node
            .get(&node)
            .map_or(&[][..], |group| group.records.as_slice());
        charge(budget, records.len())?;
        Ok(records)
    }

    fn capture_at(
        &self,
        node: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<Option<&MethodUseGroup<'a>>, Failure> {
        if self.by_node.is_empty() {
            return Ok(None);
        }
        charge(budget, 1)?;
        // Consumers pay their actual binder/record traversals. The product
        // collector borrows this original descriptor without a second index.
        Ok(self.by_node.get(&node))
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum MethodTarget {
    Binder(BinderId),
    Abstract(crate::interface::RequirementId),
    DeclaredLayout(super::provider::DeclaredLayoutMethod),
    NativeLayout(crate::foreign::ForeignLayoutProducer),
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

#[expect(
    clippy::too_many_arguments,
    reason = "original registry and family certificates authenticate distinct selected producers"
)]
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
    registry: &crate::resolved::ResolvedRegistry,
    // The caller must authenticate the original full family certificate,
    // selected goal/prerequisites and exact forwarding binder. A lexical ID
    // alone cannot establish this relation.
    mut family: impl FnMut(
        &crate::interface::EvidenceSelection,
        crate::interface::EvidenceNodeId,
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
        if !build
            && let EvidenceNode::Implementation { prerequisites, .. }
            | EvidenceNode::ProviderFamily { prerequisites, .. } = selected
        {
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
            EvidenceNode::NativeLayout { producer } => {
                let dictionary = registry.foreign_layout_dictionary(producer, work).map_err(
                    |error| match error {
                        error if error.is_resource_exhaustion() => Failure::Resource,
                        _ => Failure::Invalid,
                    },
                )?;
                if dictionary.producer() != producer
                    || !matches!(
                        dictionary.payload_type(),
                        Type::Unit | Type::Bool | Type::Int
                    )
                    || wanted.is_some_and(|method| method != producer.method())
                {
                    return Err(Failure::Invalid);
                }
                charge(work, 1)?;
                targets.try_reserve(1).map_err(|_| Failure::Resource)?;
                targets.push((producer.method(), MethodTarget::NativeLayout(producer)));
            }
            EvidenceNode::ProviderFamily {
                methods,
                prerequisites,
                ..
            } => {
                charge(
                    work,
                    methods
                        .len()
                        .checked_add(prerequisites.len())
                        .ok_or(Failure::Resource)?,
                )?;
                targets
                    .try_reserve(methods.len())
                    .map_err(|_| Failure::Resource)?;
                for prerequisite in prerequisites {
                    if !values.contains_key(prerequisite) {
                        return Err(Failure::Invalid);
                    }
                }
                for &method in methods {
                    if wanted.is_some_and(|wanted| wanted != method) {
                        continue;
                    }
                    targets.push((
                        method,
                        MethodTarget::Binder(family(selection, node, method, work)?),
                    ));
                }
            }
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

#[derive(Debug, Eq, PartialEq)]
enum AbstractCaptureStep {
    Port(usize),
    Methods(usize),
}

#[derive(Default)]
struct CaptureProjections {
    free_values: Vec<BinderId>,
    abstract_steps: Vec<AbstractCaptureStep>,
    invalid_abstract: bool,
}

impl CaptureProjections {
    fn retain_abstract(
        &mut self,
        step: AbstractCaptureStep,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        charge(budget, 1)?;
        self.abstract_steps
            .try_reserve(1)
            .map_err(|_| Failure::Resource)?;
        self.abstract_steps.push(step);
        Ok(())
    }
}

// Product of two structural folds, with independent cuts and visited bits.
// Lexical references keep their original duplicates and complete bound filter.
// The abstract recipe performs no symbol/evidence allocation: replay follows
// lexical and metadata installation, preserving graph coordinates and errors.
fn capture_projections<F: CoreOperationFamily>(
    nodes: &[StoredNode<F>],
    root: usize,
    parameters: &[BinderId],
    methods: &MethodUses<'_>,
    capture_ports: &[usize],
    budget: &mut TypeWorkBudget,
) -> Result<CaptureProjections, Failure> {
    const LEXICAL: u8 = 1;
    const ABSTRACT: u8 = 2;
    let mut pending = copy_slice(&[(root, LEXICAL | ABSTRACT)], budget)?;
    let mut seen = HashMap::<usize, u8>::new();
    let mut bound = std::collections::HashSet::new();
    let mut result = CaptureProjections::default();
    charge(budget, parameters.len() + 1)?;
    bound
        .try_reserve(parameters.len())
        .map_err(|_| Failure::Resource)?;
    bound.extend(parameters);
    while let Some((id, mut concerns)) = pending.pop() {
        // Pay the visit and its per-concern state even when one concern has
        // already visited this DAG node through a differently pruned path.
        charge(budget, 2)?;
        if result.invalid_abstract {
            concerns &= !ABSTRACT;
        }
        seen.try_reserve(1).map_err(|_| Failure::Resource)?;
        let visited = seen.entry(id).or_default();
        concerns &= !*visited;
        *visited |= concerns;
        if concerns == 0 {
            continue;
        }
        // Lexical validation precedes its capture-port cut. Abstract-only
        // invalid input belongs to the deferred abstract phase instead.
        let node = nodes.get(id);
        if concerns & LEXICAL != 0 && node.is_none() {
            return Err(Failure::Invalid);
        }
        if !capture_ports.is_empty() {
            charge(budget, capture_ports.len())?;
            if capture_ports.contains(&id) {
                if concerns & ABSTRACT != 0 {
                    result.retain_abstract(AbstractCaptureStep::Port(id), budget)?;
                }
                continue;
            }
        }
        if let Some(group) = methods.capture_at(id, budget)? {
            if concerns & ABSTRACT != 0 {
                result.retain_abstract(AbstractCaptureStep::Methods(id), budget)?;
            }
            if concerns & LEXICAL != 0 {
                charge(budget, group.free_binders.len() + 1)?;
                result
                    .free_values
                    .try_reserve(group.free_binders.len())
                    .map_err(|_| Failure::Resource)?;
                result.free_values.extend_from_slice(&group.free_binders);
                // Selected methods replace obsolete lexical placeholders;
                // abstract evidence still visits their original children.
                if group.replaces_node {
                    concerns &= !LEXICAL;
                }
            }
        }
        if concerns == 0 {
            continue;
        }
        let Some(node) = node else {
            charge(budget, 1)?;
            result.invalid_abstract = true;
            continue;
        };
        let mut binders = Vec::new();
        let mut failed = false;
        if concerns & LEXICAL != 0 {
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
                    result
                        .free_values
                        .try_reserve(1)
                        .map_err(|_| Failure::Resource)?;
                    result.free_values.push(variable.binder());
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
        }
        let child_count = F::child_count(&node.kind);
        charge(budget, binders.len() + child_count)?;
        bound
            .try_reserve(binders.len())
            .map_err(|_| Failure::Resource)?;
        bound.extend(binders);
        pending
            .try_reserve(child_count)
            .map_err(|_| Failure::Resource)?;
        for ordinal in 0..child_count {
            let Some(child) = F::child_at(&node.kind, ordinal) else {
                if concerns & LEXICAL != 0 {
                    return Err(Failure::Invalid);
                }
                charge(budget, 1)?;
                result.invalid_abstract = true;
                break;
            };
            pending.push((index(child), concerns));
        }
    }
    charge(budget, result.free_values.len())?;
    result.free_values.retain(|binder| !bound.contains(binder));
    Ok(result)
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
    // Scalar roots own no nested Forall binding or structural worklist.
    // Argument tags still pay their original dispatch; compound roots use the
    // same complete Type/Row walk and shielding below.
    let root = match root {
        Metadata::Argument(crate::types::KindedArgument::TypeArg(ty)) => {
            charge(budget, 1)?;
            Metadata::Type(ty)
        }
        Metadata::Argument(crate::types::KindedArgument::RowArg(row)) => {
            charge(budget, 1)?;
            Metadata::Row(row)
        }
        root => root,
    };
    match root {
        Metadata::Type(
            Type::Bytes
            | Type::String
            | Type::Int
            | Type::Bool
            | Type::Unit
            | Type::Nominal(_)
            | Type::Inference(_),
        ) => {
            charge(budget, 1)?;
            return Ok(());
        }
        Metadata::Type(Type::Variable(variable)) => {
            charge(budget, 1)?;
            return value.retain(*variable, budget);
        }
        Metadata::Row(row) if row.known().is_empty() && row.tail().is_none() => {
            charge(budget, 1)?;
            return Ok(());
        }
        _ => {}
    }
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

// One exact original forest and projection own both header and requested-root
// evidence. Rewrites and other projections construct a fresh owner.
struct FunctionMetadataPreparation<'a, F: CoreOperationFamily> {
    nodes: &'a [StoredNode<F>],
    operation: fn(&F::Kind) -> Option<&EffectOperation>,
    headers: HashMap<usize, NodeMetadataHeader>,
    completed: Vec<CompletedRoot>,
}

struct NodeMetadataHeader {
    variables: Vec<TypeVariableId>,
    requested: Option<std::num::NonZeroUsize>,
}

const REQUESTED_METADATA_FACTS: usize = 16;

struct CompactRoot {
    surviving: Vec<TypeVariableId>,
    bound: Vec<TypeVariableId>,
}

enum CompletedRoot {
    Compact(CompactRoot),
    // The owner's borrowed original node supplies the child recipe.
    OriginalRecipe,
}

enum RootQualification {
    DescendingEdges,
    OriginalRecipe,
}

struct PreparingRoot {
    root: usize,
    value: MetadataVariables,
    bound: Vec<TypeVariableId>,
    qualification: RootQualification,
}

impl PreparingRoot {
    fn finish(
        self,
        budget: &mut TypeWorkBudget,
    ) -> Result<(usize, MetadataVariables, CompletedRoot), Failure> {
        let representation = if matches!(self.qualification, RootQualification::OriginalRecipe)
            || self.value.variables.len() > REQUESTED_METADATA_FACTS
        {
            CompletedRoot::OriginalRecipe
        } else {
            let mut bound = Vec::new();
            let mut fits = true;
            for &variable in &self.bound {
                charge(budget, bound.len() + 1)?;
                if bound.contains(&variable) {
                    continue;
                }
                if self.value.variables.len() + bound.len() == REQUESTED_METADATA_FACTS {
                    fits = false;
                    break;
                }
                charge(budget, 1)?;
                bound.try_reserve(1).map_err(|_| Failure::Resource)?;
                bound.push(variable);
            }
            if fits {
                CompletedRoot::Compact(CompactRoot {
                    surviving: copy_slice(&self.value.variables, budget)?,
                    bound,
                })
            } else {
                CompletedRoot::OriginalRecipe
            }
        };
        Ok((self.root, self.value, representation))
    }
}

impl<'a, F: CoreOperationFamily> FunctionMetadataPreparation<'a, F> {
    fn new(
        nodes: &'a [StoredNode<F>],
        operation: fn(&F::Kind) -> Option<&EffectOperation>,
    ) -> Self {
        Self {
            nodes,
            operation,
            headers: HashMap::new(),
            completed: Vec::new(),
        }
    }

    fn collect(
        &mut self,
        root: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<MetadataVariables, Failure> {
        // Only one additional entry lookup per requested root, not per node.
        charge(budget, 1)?;
        let requested = self.headers.get(&root).and_then(|header| header.requested);
        if let Some(requested) = requested {
            charge(budget, 1)?;
            if let CompletedRoot::Compact(facts) = self
                .completed
                .get(requested.get() - 1)
                .ok_or(Failure::Invalid)?
            {
                let mut value = MetadataVariables::default();
                charge(budget, facts.surviving.len())?;
                for &variable in &facts.surviving {
                    value.retain(variable, budget)?;
                }
                return Ok(value);
            }
        }
        let mut preparation = PreparingRoot {
            root,
            value: MetadataVariables::default(),
            bound: Vec::new(),
            qualification: if requested.is_some() {
                RootQualification::OriginalRecipe
            } else {
                RootQualification::DescendingEdges
            },
        };
        self.read(&mut preparation, budget)?;
        if requested.is_some() {
            // OriginalRecipe never repeats requested-root summary preparation.
            return Ok(preparation.value);
        }
        let (root, value, completed) = preparation.finish(budget)?;
        let requested = self
            .completed
            .len()
            .checked_add(1)
            .and_then(std::num::NonZeroUsize::new)
            .ok_or(Failure::Resource)?;
        // Admit the arena slot, header lookup, and both publication moves first.
        charge(budget, 4)?;
        self.completed
            .try_reserve(1)
            .map_err(|_| Failure::Resource)?;
        let header = self.headers.get_mut(&root).ok_or(Failure::Invalid)?;
        self.completed.push(completed);
        header.requested = Some(requested);
        Ok(value)
    }

    fn read(
        &mut self,
        preparation: &mut PreparingRoot,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        let mut pending = copy_slice(&[preparation.root], budget)?;
        let mut seen = HashSet::new();
        while let Some(id) = pending.pop() {
            charge(budget, 1)?;
            seen.try_reserve(1).map_err(|_| Failure::Resource)?;
            if !seen.insert(id) {
                continue;
            }
            let node = self.nodes.get(id).ok_or(Failure::Invalid)?;
            if self.retain_node(preparation, id, budget)? {
                continue;
            }
            match (self.operation)(&node.kind) {
                Some(EffectOperation::Resource(resource)) => {
                    preparation
                        .bound
                        .try_reserve(1)
                        .map_err(|_| Failure::Resource)?;
                    preparation.bound.push(resource.acquisition.identity);
                }
                Some(EffectOperation::ProviderScope(scope)) => {
                    charge(budget, 1)?;
                    preparation
                        .bound
                        .try_reserve(1)
                        .map_err(|_| Failure::Resource)?;
                    preparation.bound.push(scope.descriptor.identity());
                }
                _ => {}
            }
            if let Some(PureExprKind::Computation(PureComputation::TypeAbstraction(abstraction))) =
                F::pure(&node.kind)
            {
                charge(budget, abstraction.parameters().len())?;
                preparation
                    .bound
                    .try_reserve(abstraction.parameters().len())
                    .map_err(|_| Failure::Resource)?;
                preparation.bound.extend(
                    abstraction
                        .parameters()
                        .iter()
                        .map(|(variable, _)| *variable),
                );
            }
            let children = F::child_count(&node.kind);
            charge(budget, children)?;
            pending
                .try_reserve(children)
                .map_err(|_| Failure::Resource)?;
            for ordinal in 0..children {
                let child = index(F::child_at(&node.kind, ordinal).ok_or(Failure::Invalid)?);
                // Inspect each original parent edge, including seen children.
                // Strict descent proves a closed acyclic recipe without Exit
                // frames. Forward edges select fallback; they reject nothing.
                if matches!(
                    preparation.qualification,
                    RootQualification::DescendingEdges
                ) {
                    charge(budget, 1)?;
                    if child >= id {
                        preparation.qualification = RootQualification::OriginalRecipe;
                    }
                }
                pending.push(child);
            }
        }
        // The complete traversal collected no binding that can remove a variable.
        if preparation.bound.is_empty() {
            charge(budget, 1)?;
            return Ok(());
        }
        charge(
            budget,
            preparation
                .value
                .variables
                .len()
                .saturating_mul(preparation.bound.len() + 2),
        )?;
        let identities = &mut preparation.value.identities;
        preparation.value.variables.retain(|variable| {
            if preparation.bound.contains(variable) {
                identities.remove(variable);
                false
            } else {
                true
            }
        });
        Ok(())
    }

    // Header lookup also discovers a prepared requested root. No second hash
    // probe is added for ordinary descendant nodes.
    fn retain_node(
        &mut self,
        preparation: &mut PreparingRoot,
        id: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<bool, Failure> {
        charge(budget, 1)?;
        if let Some(header) = self.headers.get(&id) {
            if let Some(requested) = header.requested {
                charge(budget, 1)?;
                if let CompletedRoot::Compact(facts) = self
                    .completed
                    .get(requested.get() - 1)
                    .ok_or(Failure::Invalid)?
                {
                    charge(budget, facts.surviving.len() + facts.bound.len())?;
                    for &variable in &facts.surviving {
                        preparation.value.retain(variable, budget)?;
                    }
                    preparation
                        .bound
                        .try_reserve(facts.bound.len())
                        .map_err(|_| Failure::Resource)?;
                    preparation.bound.extend(&facts.bound);
                    return Ok(true);
                }
            }
            charge(budget, header.variables.len())?;
            for &variable in &header.variables {
                preparation.value.retain(variable, budget)?;
            }
            return Ok(false);
        }
        let header = self.read_header(id, budget)?;
        // Original header storage/index plus one scalar requested-root slot.
        charge(
            budget,
            header.len().checked_add(2).ok_or(Failure::Resource)?,
        )?;
        self.headers.try_reserve(1).map_err(|_| Failure::Resource)?;
        charge(budget, header.len())?;
        for &variable in &header {
            preparation.value.retain(variable, budget)?;
        }
        // Refused output merges publish no completed header.
        self.headers.insert(
            id,
            NodeMetadataHeader {
                variables: header,
                requested: None,
            },
        );
        Ok(false)
    }

    #[cfg(test)]
    fn retain_into(
        &mut self,
        value: &mut MetadataVariables,
        root: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        // The test witness preserves incoming state. It publishes no root facts
        // from a caller-dependent derivation; prepared child S+B remain usable.
        let mut preparation = PreparingRoot {
            root,
            value: std::mem::take(value),
            bound: Vec::new(),
            qualification: RootQualification::OriginalRecipe,
        };
        let result = self.read(&mut preparation, budget);
        *value = preparation.value;
        result
    }

    fn read_header(
        &self,
        id: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<Vec<TypeVariableId>, Failure> {
        let node = self.nodes.get(id).ok_or(Failure::Invalid)?;
        let mut header = MetadataVariables::default();
        retain_type_variables(&mut header, &node.ty, budget)?;
        retain_row_variables(&mut header, F::effect_row(&node.effects), budget)?;
        match (self.operation)(&node.kind) {
            Some(EffectOperation::ProviderScope(scope)) => {
                for argument in scope
                    .descriptor
                    .arguments()
                    .iter()
                    .chain(scope.handler.effect().arguments())
                {
                    retain_metadata_variables(&mut header, Metadata::Argument(argument), budget)?;
                }
                if scope.member_count() > 1 {
                    charge(budget, scope.member_count() - 1)?;
                    for member in 1..scope.member_count() {
                        let handler = scope.handler_member(member).ok_or(Failure::Invalid)?;
                        let native = scope
                            .descriptor
                            .native_effect_member(member)
                            .ok_or(Failure::Invalid)?;
                        for argument in handler
                            .effect()
                            .arguments()
                            .iter()
                            .chain(native.arguments())
                        {
                            retain_metadata_variables(
                                &mut header,
                                Metadata::Argument(argument),
                                budget,
                            )?;
                        }
                        let family = scope
                            .descriptor
                            .family_members()
                            .get(member - 1)
                            .ok_or(Failure::Invalid)?;
                        for argument in family.application.arguments() {
                            retain_metadata_variables(
                                &mut header,
                                Metadata::Argument(argument),
                                budget,
                            )?;
                        }
                        retain_type_variables(
                            &mut header,
                            scope
                                .handler_state_member(member)
                                .ok_or(Failure::Invalid)?
                                .ty(),
                            budget,
                        )?;
                    }
                }
                retain_type_variables(&mut header, scope.handler_output.value(), budget)?;
                retain_row_variables(&mut header, scope.handler_output.effects(), budget)?;
            }
            Some(EffectOperation::Handler(handler)) => {
                for argument in handler.effect().arguments() {
                    retain_metadata_variables(&mut header, Metadata::Argument(argument), budget)?;
                }
            }
            _ => {}
        }
        if let Some(PureExprKind::Computation(PureComputation::TypeApplication(application))) =
            F::pure(&node.kind)
        {
            for argument in application.arguments() {
                retain_type_variables(&mut header, argument, budget)?;
            }
            for row in application.row_arguments() {
                retain_row_variables(&mut header, row, budget)?;
            }
        }
        Ok(header.variables)
    }
}

// Created and discarded within one Graph::build_in_domain over its fixed
// borrowed original nodes, operation family and operation projection. Keys are
// original node coordinates in that slice, never names, spans or copied shapes.
#[cfg(test)]
#[derive(Default)]
struct NodeMetadataHeaders {
    variables: HashMap<usize, Vec<TypeVariableId>>,
}

#[cfg(test)]
impl NodeMetadataHeaders {
    fn retain<F: CoreOperationFamily>(
        &mut self,
        value: &mut MetadataVariables,
        nodes: &[StoredNode<F>],
        id: usize,
        operation: fn(&F::Kind) -> Option<&EffectOperation>,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), Failure> {
        charge(budget, 1)?;
        if let Some(variables) = self.variables.get(&id) {
            charge(budget, variables.len())?;
            for &variable in variables {
                value.retain(variable, budget)?;
            }
            return Ok(());
        }
        let node = nodes.get(id).ok_or(Failure::Invalid)?;
        let mut header = MetadataVariables::default();
        retain_type_variables(&mut header, &node.ty, budget)?;
        retain_row_variables(&mut header, F::effect_row(&node.effects), budget)?;
        match operation(&node.kind) {
            Some(EffectOperation::ProviderScope(scope)) => {
                for argument in scope
                    .descriptor
                    .arguments()
                    .iter()
                    .chain(scope.handler.effect().arguments())
                {
                    retain_metadata_variables(&mut header, Metadata::Argument(argument), budget)?;
                }
                if scope.member_count() > 1 {
                    charge(budget, scope.member_count() - 1)?;
                    for member in 1..scope.member_count() {
                        let handler = scope.handler_member(member).ok_or(Failure::Invalid)?;
                        let native = scope
                            .descriptor
                            .native_effect_member(member)
                            .ok_or(Failure::Invalid)?;
                        for argument in handler
                            .effect()
                            .arguments()
                            .iter()
                            .chain(native.arguments())
                        {
                            retain_metadata_variables(
                                &mut header,
                                Metadata::Argument(argument),
                                budget,
                            )?;
                        }
                        let family = scope
                            .descriptor
                            .family_members()
                            .get(member - 1)
                            .ok_or(Failure::Invalid)?;
                        for argument in family.application.arguments() {
                            retain_metadata_variables(
                                &mut header,
                                Metadata::Argument(argument),
                                budget,
                            )?;
                        }
                        retain_type_variables(
                            &mut header,
                            scope
                                .handler_state_member(member)
                                .ok_or(Failure::Invalid)?
                                .ty(),
                            budget,
                        )?;
                    }
                }
                retain_type_variables(&mut header, scope.handler_output.value(), budget)?;
                retain_row_variables(&mut header, scope.handler_output.effects(), budget)?;
            }
            Some(EffectOperation::Handler(handler)) => {
                for argument in handler.effect().arguments() {
                    retain_metadata_variables(&mut header, Metadata::Argument(argument), budget)?;
                }
            }
            _ => {}
        }
        if let Some(PureExprKind::Computation(PureComputation::TypeApplication(application))) =
            F::pure(&node.kind)
        {
            for argument in application.arguments() {
                retain_type_variables(&mut header, argument, budget)?;
            }
            for row in application.row_arguments() {
                retain_row_variables(&mut header, row, budget)?;
            }
        }
        // Admit the complete retained scalar projection and its index before
        // publication. The ordinary structural readers above retain their own
        // per-root Forall filtering and original first-discovery order.
        charge(
            budget,
            header
                .variables
                .len()
                .checked_add(1)
                .ok_or(Failure::Resource)?,
        )?;
        self.variables
            .try_reserve(1)
            .map_err(|_| Failure::Resource)?;
        charge(budget, header.variables.len())?;
        for &variable in &header.variables {
            value.retain(variable, budget)?;
        }
        // A refused derivation or output merge cannot expose a completed entry.
        // No allocation or fallible work follows this publication.
        self.variables.insert(id, header.variables);
        Ok(())
    }
}

#[cfg(test)]
fn retain_function_metadata<F: CoreOperationFamily>(
    value: &mut MetadataVariables,
    nodes: &[StoredNode<F>],
    root: usize,
    operation: fn(&F::Kind) -> Option<&EffectOperation>,
    headers: &mut NodeMetadataHeaders,
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
        headers.retain(value, nodes, id, operation, budget)?;
        // These are subtree bindings, not header facts: collect them for every
        // reader and preserve the original final whole-subtree exclusion.
        match operation(&node.kind) {
            Some(EffectOperation::Resource(resource)) => {
                bound.try_reserve(1).map_err(|_| Failure::Resource)?;
                bound.push(resource.acquisition.identity);
            }
            Some(EffectOperation::ProviderScope(scope)) => {
                charge(budget, 1)?;
                bound.try_reserve(1).map_err(|_| Failure::Resource)?;
                bound.push(scope.descriptor.identity());
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

#[cfg(test)]
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
        None,
        &[],
        ProviderCapturePhase::Executable,
        budget,
    )
}

#[derive(Clone, Copy)]
enum ProviderCapturePhase {
    SourcePreparation,
    Executable,
}

// Import copying completes before per-node control construction, so its
// temporary Control/Callable owners do not enlarge the compilation frame.
#[inline(never)]
fn import_capture_control(
    graph: &mut SummaryGraph,
    imported: &ImportedCallables<'_>,
    budget: &mut TypeWorkBudget,
) -> Result<(), Failure> {
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
        for callable in &import.callables.positions {
            charge(budget, 1)?; // Preserve every dense position and classify presence.
            let copied = if let Some(callable) = callable {
                let mut result = callable.result.copy(budget)?;
                result.relocate(*target_offset, budget)?;
                Some(Callable {
                    body: callable.body + code_offset,
                    ty: clone_type_with_budget(&callable.ty, budget)
                        .map_err(|_| Failure::Resource)?,
                    result,
                })
            } else {
                None
            };
            graph.callables.positions.push(copied);
        }
    }
    Ok(())
}

#[inline(never)]
#[allow(
    clippy::too_many_arguments,
    reason = "borrowed node inputs preserve the existing control construction order without an owning preparation carrier"
)]
fn compile_pure_capture_control<F: CoreOperationFamily>(
    id: usize,
    node: &StoredNode<F>,
    pure: &PureExprKind,
    nodes: &[StoredNode<F>],
    values: &[Value],
    source: Span,
    graph: &mut SummaryGraph,
    data: &mut value::Graph,
    roots: &mut Vec<usize>,
    budget: &mut TypeWorkBudget,
) -> Result<Control, Failure> {
    Ok(match pure {
        PureExprKind::Value(PureValue::Intrinsic(_)) => {
            graph.callables.positions[id] = Some(Callable {
                body: 0,
                ty: clone_type_with_budget(&node.ty, budget).map_err(|_| Failure::Resource)?,
                result: Value::default(),
            });
            Control::Return
        }
        PureExprKind::Value(PureValue::Function(function)) => {
            let result = values[index(function.body())].copy(budget)?;
            graph.callables.positions[id] = Some(Callable {
                body: index(function.body()) + 1,
                ty: clone_type_with_budget(&node.ty, budget).map_err(|_| Failure::Resource)?,
                result,
            });
            roots.try_reserve(1).map_err(|_| Failure::Resource)?;
            roots.push(index(function.body()) + 1);
            Control::Return
        }
        PureExprKind::Computation(PureComputation::Match(matching)) => {
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
        PureExprKind::Computation(pure) => {
            let mut sequence = Vec::new();
            sequence
                .try_reserve(F::child_count(&node.kind) + 1)
                .map_err(|_| Failure::Resource)?;
            for ordinal in 0..F::child_count(&node.kind) {
                sequence.push(index(F::child_at(&node.kind, ordinal).ok_or(Failure::Invalid)?) + 1);
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
        _ => return Err(Failure::Invalid),
    })
}

#[inline(never)]
#[allow(
    clippy::too_many_arguments,
    reason = "the existing selected scope and original borrowed projections retain authority without a copied environment"
)]
fn compile_provider_capture_control<'a, F: CoreOperationFamily>(
    id: usize,
    nodes: &'a [StoredNode<F>],
    scope: &'a super::provider::ProviderScopeNode,
    source: Span,
    operation: fn(&F::Kind) -> Option<&EffectOperation>,
    graph: &mut SummaryGraph,
    data: &mut value::Graph,
    owners: &HashMap<(super::effect::HandlerId, crate::resolved::ResumeId), usize>,
    source_captures: &[super::provider::AuthenticatedProviderSourceCapture<'a>],
    provider_phase: ProviderCapturePhase,
    native_relations: &mut Vec<(
        &'a super::provider::ProviderScopeNode,
        &'a super::provider::AdmittedNativeStorageRelation,
    )>,
    budget: &mut TypeWorkBudget,
) -> Result<Control, Failure> {
    Ok({
        if scope.member_count() > 1 {
            // This helper rechecks frozen current-node projections,
            // state/handler headers and exact copied relation keys.
            // Full Core independently authenticates the catalog and
            // original specialization before executable publication.
            let relations = if matches!(provider_phase, ProviderCapturePhase::SourcePreparation) {
                charge(budget, source_captures.len())?;
                source_captures
                    .iter()
                    .find(|view| view.authenticates_scope(nodes, scope))
                    .ok_or(Failure::Invalid)?
                    .native_storage_relations()
            } else {
                super::provider::authenticate_native_storage_relations(
                    scope.handler.body().arena(),
                    nodes,
                    scope,
                    operation,
                    budget,
                )
                .map_err(|error| {
                    if error.reason() == crate::core::ValidationReason::Resource {
                        Failure::Resource
                    } else {
                        Failure::Invalid
                    }
                })?
            };
            charge(budget, relations.len())?;
            native_relations
                .try_reserve(relations.len())
                .map_err(|_| Failure::Resource)?;
            native_relations.extend(relations.iter().map(|relation| (scope, relation)));
        }
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
        let mut group = Request::effect(scope.handler.effect(), source, budget)?;
        // Preserve legacy single-member shape/tariffs. Additional
        // metadata is paid only for an actual finite family group.
        if scope.member_count() > 1 {
            charge(budget, scope.member_count())?;
            group
                .members
                .try_reserve(scope.member_count())
                .map_err(|_| Failure::Resource)?;
        }
        for member in 0..scope.member_count() {
            if scope.member_count() > 1 {
                charge(budget, 1)?;
            }
            let selected = scope.handler_member(member).ok_or(Failure::Invalid)?;
            if selected.body() != scope.handler.body() {
                return Err(Failure::Invalid);
            }
            if scope.member_count() > 1 {
                group.members.push(ProviderCaptureMember {
                    provided: Arc::new(
                        clone_effect_instance_with_budget(selected.effect(), budget)
                            .map_err(|_| Failure::Resource)?,
                    ),
                    native: Arc::new(
                        clone_effect_instance_with_budget(
                            scope
                                .descriptor
                                .native_effect_member(member)
                                .ok_or(Failure::Invalid)?,
                            budget,
                        )
                        .map_err(|_| Failure::Resource)?,
                    ),
                });
            }
            if scope.member_count() > 1 {
                charge(budget, selected.clauses().len())?;
            }
            if scope.member_count() == 1 {
                clauses
                    .try_reserve_exact(selected.clauses().len())
                    .map_err(|_| Failure::Resource)?;
            } else {
                clauses
                    .try_reserve(selected.clauses().len())
                    .map_err(|_| Failure::Resource)?;
            }
            if scope.member_count() > 1 {
                group
                    .clause_members
                    .try_reserve(selected.clauses().len())
                    .map_err(|_| Failure::Resource)?;
            }
            for clause in selected.clauses() {
                if scope.member_count() > 1 {
                    group.clause_members.push(member);
                }
                clauses.push(Clause {
                    operation: Some(clause.operation()),
                    body: index(clause.body()) + 1,
                    owner: *owners
                        .get(&(selected.id(), clause.resume()))
                        .ok_or(Failure::Invalid)?,
                    source: clause.origin().primary_span(),
                });
            }
        }
        let handler = graph.code.len();
        data.position_provider_handler(handler, id, budget)?;
        graph.code.push(Control::Handler {
            body: index(scope.handler.body()) + 1,
            effect: group,
            clauses,
            owning_resource: None,
        });
        let row_type = graph.types.0.len();
        charge(budget, 3)?;
        graph
            .types
            .0
            .try_reserve(1)
            .map_err(|_| Failure::Resource)?;
        // The admitted finisher interprets exactly its native
        // instance. Other outward demands and row constraints stay.
        let effects = match F::effect_row(&nodes[index(scope.finish.body)].effects)
            .remove_exact_with_budget(scope.descriptor.native_effect(), budget)
            .map_err(|_| Failure::Resource)?
        {
            Ok(row) => row,
            Err(crate::types::EffectRowError::Missing) => {
                crate::types::clone_effect_row_with_budget(
                    F::effect_row(&nodes[index(scope.finish.body)].effects),
                    budget,
                )
                .map_err(|_| Failure::Resource)?
            }
            Err(_) => return Err(Failure::Invalid),
        };
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
        charge(budget, 1)?;
        let Control::Handler {
            owning_resource, ..
        } = &mut graph.code[handler]
        else {
            return Err(Failure::Invalid);
        };
        *owning_resource = Some(owner);
        data.position(owner, id, budget)?;
        let mut native_owner = Request::effect(scope.descriptor.native_effect(), source, budget)?;
        if let Control::Handler { effect, .. } = &graph.code[handler] {
            charge(budget, effect.members.len())?;
            native_owner
                .members
                .try_reserve(effect.members.len())
                .map_err(|_| Failure::Resource)?;
            native_owner.members.extend(effect.members.iter().cloned());
        }
        graph.code.push(Control::Resource {
            body: acquisition,
            effect: native_owner,
        });
        Control::Sequence(copy_slice(&[index(scope.initializer) + 1, owner], budget)?)
    })
}

#[inline(never)]
#[allow(
    clippy::too_many_arguments,
    reason = "borrowed operation inputs keep legacy control construction separate from provider-group temporaries"
)]
fn compile_other_capture_control<F: CoreOperationFamily>(
    id: usize,
    node: &StoredNode<F>,
    operation: Option<&EffectOperation>,
    nodes: &[StoredNode<F>],
    source: Span,
    graph: &mut SummaryGraph,
    data: &mut value::Graph,
    owners: &HashMap<(super::effect::HandlerId, crate::resolved::ResumeId), usize>,
    provider_query: bool,
    boundary: &mut Option<(
        &ConditionalCapturePorts,
        &mut Vec<ConditionalCompletionEdge>,
    )>,
    budget: &mut TypeWorkBudget,
) -> Result<Control, Failure> {
    Ok(match operation {
        Some(EffectOperation::ProviderStateAccess(_)) if provider_query => Control::Unavailable,
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
        Some(EffectOperation::ProviderScope(_)) => return Err(Failure::Invalid),
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
                        source: *ports.completion_sources.get(&id).ok_or(Failure::Invalid)?,
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
                    source: *ports.completion_sources.get(&id).ok_or(Failure::Invalid)?,
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
                owning_resource: None,
            }
        }
        None => Control::Return,
    })
}

#[inline(never)]
fn install_capture_native_relations<F: CoreOperationFamily>(
    nodes: &[StoredNode<F>],
    operation: fn(&F::Kind) -> Option<&EffectOperation>,
    graph: &mut SummaryGraph,
    native_relations: Vec<(
        &super::provider::ProviderScopeNode,
        &super::provider::AdmittedNativeStorageRelation,
    )>,
    budget: &mut TypeWorkBudget,
) -> Result<(), Failure> {
    for (scope, relation) in native_relations {
        let request_id = relation.request();
        if request_id.arena() != scope.handler.body().arena()
            || relation.owner() != scope.descriptor.identity()
            || relation.member() == 0
            || relation.member() >= scope.member_count()
            || scope
                .descriptor
                .family_members()
                .get(relation.member() - 1)
                .is_none_or(|member| member.identity != relation.family())
        {
            return Err(Failure::Invalid);
        }
        let id = index(request_id);
        let node = nodes.get(id).ok_or(Failure::Invalid)?;
        let Some(EffectOperation::Request(request)) = operation(&node.kind) else {
            return Err(Failure::Invalid);
        };
        let selected = scope
            .descriptor
            .native_effect_member(relation.member())
            .ok_or(Failure::Invalid)?;
        if request.operation() != relation.operation()
            || !same_effect(Some(request.effect()), Some(relation.effect()), budget)?
            || !same_effect(Some(request.effect()), Some(selected), budget)?
        {
            return Err(Failure::Invalid);
        }
        let storage = scope
            .descriptor
            .native()
            .storage
            .as_ref()
            .ok_or(Failure::Invalid)?;
        if storage.effect() != request.effect().effect() {
            return Err(Failure::Invalid);
        }
        let result = match relation.result() {
            super::provider::HandlerNativeStorageResult::Store { allocated, refused }
                if request.operation() == storage.store()
                    && allocated == storage.allocated_constructor()
                    && refused == storage.refused_constructor() =>
            {
                NativeStorageResult::Store { allocated, refused }
            }
            super::provider::HandlerNativeStorageResult::Load
                if request.operation() == storage.load() =>
            {
                NativeStorageResult::Load
            }
            _ => return Err(Failure::Invalid),
        };
        let Control::Sequence(sequence) = graph.code.get(id + 1).ok_or(Failure::Invalid)? else {
            return Err(Failure::Invalid);
        };
        let [_operand, perform] = sequence.as_slice() else {
            return Err(Failure::Invalid);
        };
        let perform = *perform;
        let Control::Request(target) = graph.code.get_mut(perform).ok_or(Failure::Invalid)? else {
            return Err(Failure::Invalid);
        };
        if target.native_storage.is_some() {
            return Err(Failure::Invalid);
        }
        target.native_storage = Some(result);
    }
    Ok(())
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
    domain: Option<&HashSet<usize>>,
    source_captures: &[super::provider::AuthenticatedProviderSourceCapture<'_>],
    provider_phase: ProviderCapturePhase,
    budget: &mut TypeWorkBudget,
) -> Result<(SummaryGraph, Vec<usize>), Failure> {
    let mut native_relations: Vec<(
        &super::provider::ProviderScopeNode,
        &super::provider::AdmittedNativeStorageRelation,
    )> = Vec::new();
    let mut graph = SummaryGraph {
        effects: F::ALLOWS_EFFECTFUL_TYPES,
        data: None,
        callables: CallableSlots::new(budget)?,
        code: Vec::new(),
        types: TypeArguments(Vec::new()),
    };
    charge(budget, nodes.len() + 1)?;
    graph
        .code
        .try_reserve(nodes.len() + 1)
        .map_err(|_| Failure::Resource)?;
    graph.code.resize_with(nodes.len() + 1, || {
        if domain.is_some() {
            Control::Unavailable
        } else {
            Control::Return
        }
    });
    graph.code[0] = Control::Return;
    graph
        .callables
        .positions
        .try_reserve(nodes.len() + imported.callables.len())
        .map_err(|_| Failure::Resource)?;
    graph.callables.positions.resize_with(nodes.len(), || None);
    if !imported.graphs.is_empty() {
        import_capture_control(&mut graph, imported, budget)?;
    }
    let mut owners = HashMap::new();
    for (id, node) in nodes.iter().enumerate() {
        if domain.is_some_and(|domain| !domain.contains(&id)) {
            continue;
        }
        let (handler, scope) = match operation(&node.kind) {
            Some(EffectOperation::Handler(handler)) => (Some(handler), None),
            Some(EffectOperation::ProviderScope(scope)) => {
                (Some(&scope.handler), Some(scope.as_ref()))
            }
            _ => (None, None),
        };
        if let Some(handler) = handler {
            let count = scope.map_or(1, |scope| scope.member_count());
            if count > 1 {
                charge(budget, count)?;
            }
            for member in 0..count {
                let handler = if let Some(scope) = scope {
                    scope.handler_member(member).ok_or(Failure::Invalid)?
                } else {
                    handler
                };
                if count > 1 {
                    charge(budget, handler.clauses().len())?;
                }
                for clause in handler.clauses() {
                    owners.try_reserve(1).map_err(|_| Failure::Resource)?;
                    owners.insert((handler.id(), clause.resume()), graph.code.len());
                    graph.code.try_reserve(1).map_err(|_| Failure::Resource)?;
                    graph.code.push(Control::Return);
                }
            }
        }
    }
    let mut roots = Vec::new();
    let mut children = std::collections::HashSet::new();
    for (id, node) in nodes.iter().enumerate() {
        charge(budget, 1)?;
        if domain.is_some_and(|domain| !domain.contains(&id)) {
            continue;
        }
        let source = node.origin.as_ref().ok_or(Failure::Invalid)?.primary_span();
        let code = match F::pure(&node.kind) {
            Some(
                pure @ (PureExprKind::Value(PureValue::Intrinsic(_) | PureValue::Function(_))
                | PureExprKind::Computation(_)),
            ) => compile_pure_capture_control(
                id, node, pure, nodes, values, source, &mut graph, data, &mut roots, budget,
            )?,
            _ => match operation(&node.kind) {
                Some(EffectOperation::ProviderScope(scope)) => compile_provider_capture_control(
                    id,
                    nodes,
                    scope,
                    source,
                    operation,
                    &mut graph,
                    data,
                    &owners,
                    source_captures,
                    provider_phase,
                    &mut native_relations,
                    budget,
                )?,
                operation => compile_other_capture_control(
                    id,
                    node,
                    operation,
                    nodes,
                    source,
                    &mut graph,
                    data,
                    &owners,
                    provider_query,
                    &mut boundary,
                    budget,
                )?,
            },
        };
        graph.code[id + 1] = code;
        for ordinal in 0..F::child_count(&node.kind) {
            children.try_reserve(1).map_err(|_| Failure::Resource)?;
            children.insert(index(F::child_at(&node.kind, ordinal).ok_or(Failure::Invalid)?) + 1);
        }
    }
    // Iterate sealed receipts only; legacy graphs incur no added node scan.
    charge(budget, native_relations.len())?;
    if !native_relations.is_empty() {
        install_capture_native_relations(nodes, operation, &mut graph, native_relations, budget)?;
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
        if domain.is_none_or(|domain| domain.contains(&(id - 1))) && !children.contains(&id) {
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
    analyze_nodes_with_methods(
        &builder.nodes,
        globals,
        imports,
        operation,
        methods,
        adapters,
        None,
        None,
        None,
        None,
        ProviderCapturePhase::SourcePreparation,
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

/// Final Core admission reuses layout facts from independent type validation
/// of this exact immutable node slice. The sealed view grants no authority to
/// source method names or headers copied from another arena.
pub(super) fn check_nodes_with_authentic_layouts<F: CoreOperationFamily>(
    nodes: &[StoredNode<F>],
    globals: &[(BinderId, NodeId)],
    imports: &[(BinderId, &CaptureValueSummary)],
    operation: fn(&F::Kind) -> Option<&EffectOperation>,
    layouts: &AuthenticatedCaptureLayouts<'_>,
    budget: &mut TypeWorkBudget,
) -> Result<Vec<CaptureValueSummary>, Failure> {
    analyze_nodes_with_methods(
        nodes,
        globals,
        imports,
        operation,
        &[],
        &[],
        None,
        None,
        Some(layouts),
        None,
        ProviderCapturePhase::Executable,
        budget,
    )
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
        nodes,
        globals,
        imports,
        operation,
        methods,
        adapters,
        None,
        None,
        None,
        None,
        ProviderCapturePhase::Executable,
        budget,
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
    let (root, lexical, data, instantiations, dictionary_variables, declared) =
        flow.inputs(nodes).ok_or(Failure::Invalid)?;
    analyze_nodes_with_methods(
        nodes,
        &[],
        imports,
        operation,
        methods,
        adapters,
        None,
        Some((
            &[root],
            lexical,
            data,
            instantiations,
            dictionary_variables,
            declared,
        )),
        None,
        None,
        ProviderCapturePhase::SourcePreparation,
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
        None,
        Some(builder),
        ProviderCapturePhase::SourcePreparation,
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
    Option<&'a super::provider::DeclaredLayoutMethods<'a>>,
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
    authentic_layouts: Option<&AuthenticatedCaptureLayouts<'_>>,
    source_builder: Option<&CoreBuilder<F>>,
    provider_phase: ProviderCapturePhase,
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
        None,
        false,
        None,
        authentic_layouts,
        source_builder,
        provider_phase,
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
    if let Some((roots, _, _, _, _, _)) = summary_roots {
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
    source: Span,
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
    completion_sources: HashMap<usize, NodeId>,
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
    source: NodeId,
    port: usize,
    node: usize,
    operand: Option<usize>,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ConditionalCaptureOwner {
    Nested(usize),
    EntryClause(usize),
}
struct ConditionalDiscardCaptureEdge {
    input: super::provider::CaptureInputId,
    source: NodeId,
    projected: NodeId,
    handler: super::effect::HandlerId,
    resume: crate::resolved::ResumeId,
    clause: NodeId,
    owner: ConditionalCaptureOwner,
}

/// Owns unresolved graph-local continuation and capture inputs. No ordinary
/// Analysis entry or callable value-summary conversion is provided.
pub(in crate::core) struct ConditionalCaptureGraph {
    template: crate::resolved::ProviderTemplateId,
    graph: SummaryGraph,
    value_handler: usize,
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
    declared: Option<&super::provider::DeclaredLayoutMethods<'_>>,
    budget: &mut TypeWorkBudget,
) -> Result<ConditionalCaptureGraph, Failure> {
    let mut ports = ConditionalCapturePorts {
        clauses: Vec::new(),
        completions: HashMap::new(),
        completion_sources: HashMap::new(),
    };
    let mut roots = Vec::new();
    let mut value_clauses = Vec::new();
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
            .checked_mul(4)
            .and_then(|count| {
                entry
                    .draft
                    .program
                    .nodes
                    .len()
                    .checked_mul(2)
                    .and_then(|nodes| count.checked_add(nodes))
            })
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
    ports
        .completion_sources
        .try_reserve(entry.draft.program.nodes.len())
        .map_err(|_| Failure::Resource)?;
    roots
        .try_reserve_exact(entry.draft.clauses.len())
        .map_err(|_| Failure::Resource)?;
    value_clauses
        .try_reserve_exact(entry.draft.clauses.len())
        .map_err(|_| Failure::Resource)?;
    lexical.try_reserve(1).map_err(|_| Failure::Resource)?;
    lexical.push(entry.draft.state.id());
    let instance = entry.provided();
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
            source: clause.origin().primary_span(),
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
        value_clauses.push(value::ConditionalClauseInput {
            pattern: clause.pattern(),
            body: root,
            source: clause.origin().primary_span(),
        });
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
        if !preserved
            || ports.completions.insert(index(target), selected).is_some()
            || ports
                .completion_sources
                .insert(index(target), original_id)
                .is_some()
        {
            return Err(Failure::Invalid);
        }
    }
    let mut edges = Vec::new();
    let mut value_handler = None;
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
        Some((
            &roots,
            &lexical,
            &[],
            instantiations,
            dictionary_variables,
            declared,
        )),
        Some((&ports, &mut edges)),
        Some((&value_clauses, &mut value_handler)),
        false,
        None,
        None,
        None,
        ProviderCapturePhase::SourcePreparation,
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
            let source_discard = entry
                .draft
                .program
                .nodes
                .get(index(port.node))
                .ok_or(Failure::Invalid)?;
            let super::effect::EffectExprKind::Operation(EffectOperation::Discard(source_discard)) =
                &source_discard.kind
            else {
                return Err(Failure::Invalid);
            };
            if source_discard.handler() != port.handler || source_discard.owner() != port.resume {
                return Err(Failure::Invalid);
            }
            if port.handler == entry.draft.handler {
                charge(
                    budget,
                    ports
                        .clauses
                        .len()
                        .checked_add(edges.len())
                        .ok_or(Failure::Resource)?,
                )?;
                let ordinal = ports
                    .clauses
                    .iter()
                    .position(|clause| {
                        clause.handler == port.handler && clause.resume == port.resume
                    })
                    .ok_or(Failure::Invalid)?;
                let clause = entry.draft.clauses.get(ordinal).ok_or(Failure::Invalid)?;
                if clause.body() != port.clause
                    || !matches!(
                        built.graph.code.get(index(projected) + 1),
                        Some(Control::Unavailable)
                    )
                    || !edges.iter().any(|edge| {
                        edge.port == ordinal
                            && edge.node == index(projected)
                            && edge.source == port.node
                            && edge.operand.is_none()
                    })
                {
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
                    owner: ConditionalCaptureOwner::EntryClause(ordinal),
                });
                continue;
            }
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
                owner: ConditionalCaptureOwner::Nested(*owner),
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
        value_handler: value_handler.ok_or(Failure::Invalid)?,
        roots: codes,
        ports,
        edges,
        discards,
        source_arena: entry.draft.program.arena,
        projected_arena,
        correspondence: retained,
    })
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ActualValuePathStep {
    Root(Span),
    Call(Span),
    Invoke(Span, Span),
    Dispatch(Span, Span, usize),
}

#[derive(Debug)]
struct ActualCaptureWitness {
    input: super::provider::CaptureInputId,
    request: Span,
    path: Vec<ActualValuePathStep>,
    row: EffectRow,
}

/// Preparation receipt keeps each request row until final independently typed
/// control reconstructs the same original input correspondence. No graph or
/// unfinished equation is retained in executable specialization proof.
#[derive(Debug)]
pub(in crate::core) struct ActualCaptureInputs {
    template: crate::resolved::ProviderTemplateId,
    rows: HashMap<super::provider::CaptureInputId, EffectRow>,
    witnesses: Vec<ActualCaptureWitness>,
}
impl ActualCaptureInputs {
    pub(in crate::core) fn empty(template: crate::resolved::ProviderTemplateId) -> Self {
        Self {
            template,
            rows: HashMap::new(),
            witnesses: Vec::new(),
        }
    }
    pub(in crate::core) fn rows(&self) -> &HashMap<super::provider::CaptureInputId, EffectRow> {
        &self.rows
    }
    pub(in crate::core) fn same(
        &self,
        other: &Self,
        budget: &mut TypeWorkBudget,
    ) -> Result<bool, Failure> {
        charge(
            budget,
            self.rows
                .len()
                .checked_add(self.witnesses.len())
                .ok_or(Failure::Resource)?,
        )?;
        if self.template != other.template
            || self.rows.len() != other.rows.len()
            || self.witnesses.len() != other.witnesses.len()
        {
            return Ok(false);
        }
        for (input, row) in &self.rows {
            let Some(other) = other.rows.get(input) else {
                return Ok(false);
            };
            if !crate::types::same_effect_rows_with_budget(row, other, budget)
                .map_err(|_| Failure::Resource)?
            {
                return Ok(false);
            }
        }
        let mut matched = Vec::new();
        charge(budget, other.witnesses.len())?;
        matched
            .try_reserve_exact(other.witnesses.len())
            .map_err(|_| Failure::Resource)?;
        matched.resize(other.witnesses.len(), false);
        for witness in &self.witnesses {
            let mut found = false;
            for (ordinal, other) in other.witnesses.iter().enumerate() {
                charge(
                    budget,
                    witness
                        .path
                        .len()
                        .checked_add(other.path.len())
                        .and_then(|n| n.checked_add(1))
                        .ok_or(Failure::Resource)?,
                )?;
                if matched[ordinal]
                    || witness.input != other.input
                    || witness.request != other.request
                    || witness.path != other.path
                {
                    continue;
                }
                if crate::types::same_effect_rows_with_budget(&witness.row, &other.row, budget)
                    .map_err(|_| Failure::Resource)?
                {
                    matched[ordinal] = true;
                    found = true;
                    break;
                }
            }
            if !found {
                return Ok(false);
            }
        }
        Ok(true)
    }
}

#[cfg(test)]
pub(in crate::core) fn assert_distinct_actual_captures_for_test(
    inputs: &ActualCaptureInputs,
    effect: crate::types::EffectId,
) {
    assert_eq!(inputs.rows.len(), 1, "one original nested discard input");
    assert_eq!(inputs.witnesses.len(), 2, "two actual callback requests");
    let input = *inputs.rows.keys().next().unwrap();
    assert!(
        inputs
            .witnesses
            .iter()
            .all(|witness| witness.input == input)
    );
    let empty = inputs
        .witnesses
        .iter()
        .find(|witness| witness.row.is_empty())
        .expect("owner-free request contributes empty c");
    let owned = inputs
        .witnesses
        .iter()
        .find(|witness| {
            witness.row.known().len() == 1
                && witness.row.tail().is_none()
                && witness.row.known()[0].effect() == effect
        })
        .expect("captured completion contributes exactly H");
    assert_ne!(
        empty.request, owned.request,
        "independently observed Stop sites"
    );
    assert!(
        crate::types::same_effect_rows_with_budget(
            &inputs.rows[&input],
            &owned.row,
            &mut TypeWorkBudget::unbounded()
        )
        .unwrap()
    );

    let clone = || {
        let mut work = TypeWorkBudget::unbounded();
        ActualCaptureInputs {
            template: inputs.template,
            rows: inputs
                .rows
                .iter()
                .map(|(input, row)| {
                    (
                        *input,
                        crate::types::clone_effect_row_with_budget(row, &mut work).unwrap(),
                    )
                })
                .collect(),
            witnesses: inputs
                .witnesses
                .iter()
                .map(|witness| ActualCaptureWitness {
                    input: witness.input,
                    request: witness.request,
                    path: witness.path.clone(),
                    row: crate::types::clone_effect_row_with_budget(&witness.row, &mut work)
                        .unwrap(),
                })
                .collect(),
        }
    };
    let mut missing = clone();
    missing.rows.clear();
    assert!(
        !inputs
            .same(&missing, &mut TypeWorkBudget::unbounded())
            .unwrap()
    );
    let mut wrong_row = clone();
    wrong_row
        .witnesses
        .iter_mut()
        .find(|witness| witness.row.is_empty())
        .unwrap()
        .row =
        crate::types::clone_effect_row_with_budget(&owned.row, &mut TypeWorkBudget::unbounded())
            .unwrap();
    assert!(
        !inputs
            .same(&wrong_row, &mut TypeWorkBudget::unbounded())
            .unwrap(),
        "joined c equality must not erase individual rows"
    );
    let mut wrong_request = clone();
    wrong_request.witnesses[0].request = wrong_request.witnesses[1].request;
    assert!(
        !inputs
            .same(&wrong_request, &mut TypeWorkBudget::unbounded())
            .unwrap()
    );
    let mut wrong_path = clone();
    wrong_path.witnesses[0].path.clear();
    assert!(
        !inputs
            .same(&wrong_path, &mut TypeWorkBudget::unbounded())
            .unwrap()
    );
    let copied = clone();
    let mut measured = TypeWorkBudget::unbounded();
    assert!(inputs.same(&copied, &mut measured).unwrap());
    let cost = measured.used();
    assert!(cost > 0);
    for prefix in [0, 13] {
        let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
        short.charge(prefix).unwrap();
        assert!(matches!(
            inputs.same(&copied, &mut short),
            Err(Failure::Resource)
        ));
        for _ in 0..2 {
            let mut exact = TypeWorkBudget::with_limit(prefix + cost);
            exact.charge(prefix).unwrap();
            assert!(inputs.same(&copied, &mut exact).unwrap());
            assert_eq!(exact.used(), prefix + cost);
        }
    }
}

/// Preparation input owns one actual typed value/control graph. It provides no
/// executable descriptor or unchecked capture-row annotation.
pub(crate) struct ActualProviderCapture {
    graph: SummaryGraph,
    root: usize,
    native: Request,
}

#[allow(clippy::too_many_arguments)] // Independent source, actual and work authorities stay explicit.
pub(crate) fn prepare_actual_provider_capture<F: CoreOperationFamily>(
    builder: &CoreBuilder<F>,
    body: NodeId,
    globals: &[(BinderId, NodeId)],
    imports: &[(BinderId, &CaptureValueSummary)],
    methods: &[MethodUse],
    adapters: &[MethodAdapter],
    native: &EffectInstance,
    operation: fn(&F::Kind) -> Option<&EffectOperation>,
    budget: &mut TypeWorkBudget,
) -> Result<ActualProviderCapture, Failure> {
    let (arena, nodes, _) = builder
        .provider_projection_parts()
        .map_err(|_| Failure::Invalid)?;
    if !F::ALLOWS_EFFECTFUL_TYPES || body.arena() != arena || index(body) >= nodes.len() {
        return Err(Failure::Invalid);
    }
    for (_, node) in globals {
        charge(budget, 1)?;
        if node.arena() != arena || index(*node) >= nodes.len() {
            return Err(Failure::Invalid);
        }
    }
    let domain = actual_capture_domain(nodes, arena, body, globals, methods, adapters, budget)?;
    let roots = [body];
    let built = build_capture_graph(
        nodes,
        globals,
        imports,
        operation,
        methods,
        adapters,
        Some((&roots, &[], &[], &[], &[], None)),
        None,
        None,
        true,
        Some(&domain),
        None,
        None,
        ProviderCapturePhase::SourcePreparation,
        budget,
    )?
    .ok_or(Failure::Invalid)?;
    Ok(ActualProviderCapture {
        graph: built.graph,
        root: index(body).checked_add(1).ok_or(Failure::Resource)?,
        native: Request::effect(
            native,
            nodes[index(body)]
                .origin
                .as_ref()
                .ok_or(Failure::Invalid)?
                .primary_span(),
            budget,
        )?,
    })
}

// Source checking and final admission query only authenticated typed roots.
// Other staged clause forests may precede their enclosing scope. Preserve
// source node ordinals: no completion port or callable is renamed.
fn actual_capture_domain<F: CoreOperationFamily>(
    nodes: &[StoredNode<F>],
    arena: super::dialect::ArenaId,
    body: NodeId,
    globals: &[(BinderId, NodeId)],
    methods: &[MethodUse],
    adapters: &[MethodAdapter],
    budget: &mut TypeWorkBudget,
) -> Result<HashSet<usize>, Failure> {
    let mut pending = Vec::new();
    let count = globals.len().checked_add(1).ok_or(Failure::Resource)?;
    charge(budget, count)?;
    pending
        .try_reserve_exact(count)
        .map_err(|_| Failure::Resource)?;
    pending.push(body);
    pending.extend(globals.iter().map(|(_, node)| *node));
    // Use the same binding relation as the finite-value solver. A lexical
    // initializer can be outside the body's structural children, while still
    // supplying an actual closure or aggregate retained by that body.
    let mut bindings = HashMap::new();
    charge(
        budget,
        nodes
            .len()
            .checked_add(globals.len())
            .ok_or(Failure::Resource)?,
    )?;
    bindings
        .try_reserve(globals.len())
        .map_err(|_| Failure::Resource)?;
    bindings.extend(globals.iter().copied());
    for stored in nodes {
        match F::pure(&stored.kind) {
            Some(PureExprKind::Computation(PureComputation::Bind(binding))) => {
                charge(budget, 1)?;
                bindings.try_reserve(1).map_err(|_| Failure::Resource)?;
                bindings.insert(binding.binder().id(), binding.initializer());
            }
            Some(PureExprKind::Computation(PureComputation::RecursiveBind(binding))) => {
                charge(budget, binding.members().len())?;
                bindings
                    .try_reserve(binding.members().len())
                    .map_err(|_| Failure::Resource)?;
                for member in binding.members() {
                    bindings.insert(member.binder().id(), member.initializer());
                }
            }
            Some(PureExprKind::Computation(PureComputation::Match(matching))) => {
                charge(budget, matching.arms().len())?;
                for arm in matching.arms() {
                    let mut patterns = Vec::new();
                    charge(budget, 1)?;
                    patterns.try_reserve(1).map_err(|_| Failure::Resource)?;
                    patterns.push(arm.pattern());
                    while let Some(pattern) = patterns.pop() {
                        charge(budget, 1)?;
                        match &pattern.kind {
                            super::data::CorePatternKind::Binder(binder) => {
                                charge(budget, 1)?;
                                bindings.try_reserve(1).map_err(|_| Failure::Resource)?;
                                bindings.insert(binder.id(), matching.scrutinee());
                            }
                            super::data::CorePatternKind::Tuple(elements) => {
                                charge(budget, elements.len())?;
                                patterns
                                    .try_reserve(elements.len())
                                    .map_err(|_| Failure::Resource)?;
                                patterns.extend(elements.iter());
                            }
                            super::data::CorePatternKind::Constructor { payload, .. } => {
                                if let Some(payload) = payload.as_deref() {
                                    charge(budget, 1)?;
                                    patterns.try_reserve(1).map_err(|_| Failure::Resource)?;
                                    patterns.push(payload);
                                }
                            }
                            super::data::CorePatternKind::Wildcard
                            | super::data::CorePatternKind::Boolean(_)
                            | super::data::CorePatternKind::Unit => {}
                        }
                    }
                }
            }
            _ => {}
        }
    }
    // Selected method adapters refer only to these same typed binder roots or
    // authenticated imports. They never authorize an unknown source callable.
    for adapter in adapters {
        charge(budget, 1)?;
        if let Some(node) = bindings.get(&adapter.binder) {
            pending.try_reserve(1).map_err(|_| Failure::Resource)?;
            pending.push(*node);
        }
    }
    let method_uses = MethodUses::new(methods, budget)?;
    let mut domain = HashSet::new();
    while let Some(node) = pending.pop() {
        charge(budget, 1)?;
        if node.arena() != arena {
            return Err(Failure::Invalid);
        }
        let id = usize::try_from(node.value()).map_err(|_| Failure::Invalid)?;
        let stored = nodes.get(id).ok_or(Failure::Invalid)?;
        if domain.contains(&id) {
            continue;
        }
        charge(budget, 1)?;
        domain.try_reserve(1).map_err(|_| Failure::Resource)?;
        domain.insert(id);
        if let Some(PureExprKind::Variable(variable)) = F::pure(&stored.kind) {
            charge(budget, 1)?;
            if let Some(initializer) = bindings.get(&variable.binder()) {
                pending.try_reserve(1).map_err(|_| Failure::Resource)?;
                pending.push(*initializer);
            }
        }
        for method in method_uses.at(id, budget)? {
            if let MethodTarget::Binder(binder) | MethodTarget::Adapter { binder, .. } =
                method.target
            {
                charge(budget, 1)?;
                if let Some(initializer) = bindings.get(&binder) {
                    pending.try_reserve(1).map_err(|_| Failure::Resource)?;
                    pending.push(*initializer);
                }
            }
        }
        let count = F::child_count(&stored.kind);
        charge(budget, count)?;
        pending.try_reserve(count).map_err(|_| Failure::Resource)?;
        for ordinal in 0..count {
            pending.push(F::child_at(&stored.kind, ordinal).ok_or(Failure::Invalid)?);
        }
    }
    Ok(domain)
}

fn instantiate_capture_request(
    request: &mut Request,
    types: &HashMap<TypeVariableId, Type>,
    rows: &HashMap<TypeVariableId, EffectRow>,
    budget: &mut TypeWorkBudget,
) -> Result<(), Failure> {
    if let Some(effect) = &request.effect {
        let mut arguments = Vec::new();
        charge(
            budget,
            effect
                .arguments()
                .len()
                .checked_mul(2)
                .ok_or(Failure::Resource)?,
        )?;
        arguments
            .try_reserve_exact(effect.arguments().len())
            .map_err(|_| Failure::Resource)?;
        for argument in effect.arguments() {
            arguments.push(crate::types::IterativeArgumentOwner::new(
                crate::types::substitute_kinded_argument_with(argument, types, rows, |cells| {
                    budget.charge(cells)
                })
                .map_err(|_| Failure::Resource)?
                .map_err(|_| Failure::Invalid)?,
            ));
        }
        let mut actual = Vec::new();
        actual
            .try_reserve_exact(arguments.len())
            .map_err(|_| Failure::Resource)?;
        actual.extend(
            arguments
                .into_iter()
                .map(crate::types::IterativeArgumentOwner::into_inner),
        );
        request.effect = Some(Arc::new(EffectInstance::new_kinded(
            effect.effect(),
            actual.into_boxed_slice(),
        )));
    }
    if let Some(row) = &request.opaque_row {
        request.opaque_row = Some(Arc::new(
            crate::types::substitute_effect_and_template_rows_with(
                row,
                types,
                rows,
                &HashMap::new(),
                |cells| charge(budget, cells),
                || Failure::Resource,
            )?
            .map_err(|_| Failure::Invalid)?,
        ));
    }
    Ok(())
}

/// Realizes original capture inputs from actual requests before any input-row
/// joins. The immutable original ports bind completion owners and discard sites.
#[allow(clippy::too_many_arguments)] // Independent source, actual and work authorities stay explicit.
pub(in crate::core) fn reconstruct_actual_provider_captures(
    original: &ConditionalCaptureGraph,
    program: &super::UnvalidatedEffectProgram,
    mut actual: ActualProviderCapture,
    types: &HashMap<TypeVariableId, Type>,
    rows: &HashMap<TypeVariableId, EffectRow>,
    body_answer: &Type,
    provided: &EffectInstance,
    budget: &mut TypeWorkBudget,
) -> Result<ActualCaptureInputs, Failure> {
    if original.source_arena != program.arena
        || original.ports.clauses.is_empty()
        || original.roots.len() != original.ports.clauses.len()
    {
        return Err(Failure::Invalid);
    }
    let source = &original.graph;
    let code_offset = actual.graph.code.len();
    let target_offset = actual.graph.callables.len();
    let type_offset = actual.graph.types.0.len();
    let handler = code_offset
        .checked_add(source.code.len())
        .ok_or(Failure::Resource)?;
    let native_owner = handler.checked_add(1).ok_or(Failure::Resource)?;
    let owner_start = native_owner.checked_add(1).ok_or(Failure::Resource)?;
    charge(
        budget,
        source
            .code
            .len()
            .checked_add(source.callables.len())
            .and_then(|n| n.checked_add(source.types.0.len()))
            .and_then(|n| n.checked_add(original.ports.clauses.len() + 2))
            .ok_or(Failure::Resource)?,
    )?;
    actual
        .graph
        .code
        .try_reserve(source.code.len() + original.ports.clauses.len() + 2)
        .map_err(|_| Failure::Resource)?;
    actual
        .graph
        .callables
        .positions
        .try_reserve(source.callables.len())
        .map_err(|_| Failure::Resource)?;
    actual
        .graph
        .types
        .0
        .try_reserve(source.types.0.len())
        .map_err(|_| Failure::Resource)?;
    let mut substitutions = Substitutions(HashMap::new());
    charge(budget, types.len().checked_add(1).ok_or(Failure::Resource)?)?;
    substitutions
        .0
        .try_reserve(types.len() + 1)
        .map_err(|_| Failure::Resource)?;
    for (id, ty) in types {
        substitutions.insert(
            *id,
            clone_type_with_budget(ty, budget).map_err(|_| Failure::Resource)?,
        );
    }
    let answer = original.ports.clauses[0].answer;
    if substitutions.0.contains_key(&answer) {
        return Err(Failure::Invalid);
    }
    substitutions.insert(
        answer,
        clone_type_with_budget(body_answer, budget).map_err(|_| Failure::Resource)?,
    );
    let instantiate = |ty: &Type, budget: &mut TypeWorkBudget| {
        crate::types::substitute_type_and_row_variables_with(
            ty,
            &substitutions.0,
            rows,
            |cells| charge(budget, cells),
            || Failure::Resource,
        )?
        .map_err(|_| Failure::Invalid)
    };
    for code in &source.code {
        let mut code = code.copy(code_offset, target_offset, type_offset, budget)?;
        if let Control::Request(request)
        | Control::Handler {
            effect: request, ..
        }
        | Control::Resource {
            effect: request, ..
        } = &mut code
        {
            instantiate_capture_request(request, &substitutions.0, rows, budget)?;
        }
        actual.graph.code.push(code);
    }
    for ty in &source.types.0 {
        actual.graph.types.0.push(instantiate(ty, budget)?);
    }
    for callable in &source.callables.positions {
        charge(budget, 1)?; // Presence, not an instantiated Unit placeholder.
        let copied = if let Some(callable) = callable {
            let mut result = callable.result.copy(budget)?;
            result.relocate(target_offset, budget)?;
            Some(Callable {
                body: callable
                    .body
                    .checked_add(code_offset)
                    .ok_or(Failure::Resource)?,
                ty: instantiate(&callable.ty, budget)?,
                result,
            })
        } else {
            None
        };
        actual.graph.callables.positions.push(copied);
    }
    let mut clauses = Vec::new();
    charge(budget, original.ports.clauses.len())?;
    clauses
        .try_reserve_exact(original.ports.clauses.len())
        .map_err(|_| Failure::Resource)?;
    for (ordinal, port) in original.ports.clauses.iter().enumerate() {
        if port.continuation.0 != ordinal
            || port.capture.0 != ordinal
            || port.output.0 != 0
            || port.answer != answer
            || original.roots[ordinal] != index(port.root) + 1
        {
            return Err(Failure::Invalid);
        }
        clauses.push(Clause {
            operation: Some(port.operation),
            body: original.roots[ordinal]
                .checked_add(code_offset)
                .ok_or(Failure::Resource)?,
            owner: owner_start.checked_add(ordinal).ok_or(Failure::Resource)?,
            source: port.source,
        });
    }
    for edge in &original.edges {
        charge(
            budget,
            original
                .discards
                .len()
                .checked_add(1)
                .ok_or(Failure::Resource)?,
        )?;
        let port = original
            .ports
            .clauses
            .get(edge.port)
            .ok_or(Failure::Invalid)?;
        if original.ports.completions.get(&edge.node) != Some(&edge.port)
            || port.handler != original.ports.clauses[0].handler
        {
            return Err(Failure::Invalid);
        }
        let position = edge
            .node
            .checked_add(1)
            .and_then(|n| n.checked_add(code_offset))
            .ok_or(Failure::Resource)?;
        if !matches!(actual.graph.code.get(position), Some(Control::Unavailable)) {
            return Err(Failure::Invalid);
        }
        if edge.source.arena() != original.source_arena
            || original
                .correspondence
                .get(index(edge.source))
                .copied()
                .flatten()
                .map(index)
                != Some(edge.node)
        {
            return Err(Failure::Invalid);
        }
        let source_node = program
            .nodes
            .get(index(edge.source))
            .ok_or(Failure::Invalid)?;
        let owner = owner_start
            .checked_add(edge.port)
            .ok_or(Failure::Resource)?;
        actual.graph.code[position] = match (&source_node.kind, edge.operand) {
            (
                super::effect::EffectExprKind::Operation(EffectOperation::Resume(resume)),
                Some(operand),
            ) if resume.handler() == port.handler
                && resume.owner() == port.resume
                && original
                    .correspondence
                    .get(index(resume.value()))
                    .copied()
                    .flatten()
                    .map(|node| index(node) + 1)
                    == Some(operand) =>
            {
                Control::Resume {
                    owner,
                    value: operand.checked_add(code_offset).ok_or(Failure::Resource)?,
                }
            }
            (super::effect::EffectExprKind::Operation(EffectOperation::Discard(discard)), None)
                if discard.handler() == port.handler
                    && discard.owner() == port.resume
                    && original.discards.iter().any(|input| {
                        input.source == edge.source
                            && input.projected.value() as usize == edge.node
                            && input.owner == ConditionalCaptureOwner::EntryClause(edge.port)
                    }) =>
            {
                let row_type = actual.graph.types.0.len();
                charge(budget, 3)?;
                actual
                    .graph
                    .types
                    .0
                    .try_reserve(1)
                    .map_err(|_| Failure::Resource)?;
                actual.graph.types.0.push(Type::function_computation(
                    Type::Unit,
                    crate::types::ComputationType::new(
                        Type::Unit,
                        crate::types::substitute_effect_and_template_rows_with(
                            &source_node.effects,
                            &substitutions.0,
                            rows,
                            &HashMap::new(),
                            |cells| charge(budget, cells),
                            || Failure::Resource,
                        )?
                        .map_err(|_| Failure::Invalid)?,
                    ),
                ));
                Control::Discard {
                    owner,
                    node: edge.node,
                    local: false,
                    row_type,
                    source: source_node
                        .origin
                        .as_ref()
                        .ok_or(Failure::Invalid)?
                        .primary_span(),
                }
            }
            _ => return Err(Failure::Invalid),
        };
    }
    // State access is authenticated source control, not an ordinary callable
    // query. Reconnect only the exact retained original access operand.
    for (ordinal, node) in program.nodes.iter().enumerate() {
        charge(budget, 1)?;
        let super::effect::EffectExprKind::Operation(EffectOperation::ProviderStateAccess(access)) =
            &node.kind
        else {
            continue;
        };
        let projected = original
            .correspondence
            .get(ordinal)
            .copied()
            .flatten()
            .ok_or(Failure::Invalid)?;
        let operand = original
            .correspondence
            .get(index(access.operand()))
            .copied()
            .flatten()
            .ok_or(Failure::Invalid)?;
        if projected.arena() != original.projected_arena
            || operand.arena() != original.projected_arena
        {
            return Err(Failure::Invalid);
        }
        let position = index(projected)
            .checked_add(1)
            .and_then(|n| n.checked_add(code_offset))
            .ok_or(Failure::Resource)?;
        if !matches!(actual.graph.code.get(position), Some(Control::Unavailable)) {
            return Err(Failure::Invalid);
        }
        actual.graph.code[position] =
            Control::Sequence(copy_slice(&[index(operand) + 1 + code_offset], budget)?);
    }
    actual.graph.code.push(Control::Handler {
        body: actual.root,
        effect: Request::effect(provided, provided_source(program)?, budget)?,
        clauses,
        owning_resource: Some(native_owner),
    });
    actual.graph.code.push(Control::Resource {
        body: handler,
        effect: actual.native,
    });
    for _ in &original.ports.clauses {
        actual.graph.code.push(Control::Return);
    }
    let mut data = actual.graph.data.take().ok_or(Failure::Invalid)?;
    {
        let unique = Arc::get_mut(&mut data).ok_or(Failure::Invalid)?;
        let handler_value = unique.import_conditional_handler(
            source.data.as_deref().ok_or(Failure::Invalid)?,
            original.value_handler,
            actual.root,
            handler,
            target_offset,
            code_offset,
            budget,
        )?;
        unique.position(native_owner, handler_value, budget)?;
    }
    actual.graph.data = Some(data);
    let mut analysis = Analysis::new(&actual.graph, None, budget)?;
    analysis.infer_cleanup_rows = true;
    analysis.authenticate_actual_captures = true;
    analysis.check(&[native_owner], budget)?;
    let mut captures = HashMap::new();
    let mut witnesses = Vec::new();
    charge(budget, analysis.actual_captures.len())?;
    witnesses
        .try_reserve(analysis.actual_captures.len())
        .map_err(|_| Failure::Resource)?;
    // Every action for an original input must have the exact closing request
    // driver observed at completion. A missing event never means empty c.
    for action in &analysis.cleanup_rows {
        charge(
            budget,
            original
                .discards
                .len()
                .checked_add(analysis.actual_captures.len())
                .ok_or(Failure::Resource)?,
        )?;
        if original
            .discards
            .iter()
            .any(|port| index(port.projected) + 1 + code_offset == action.code)
            && !analysis.actual_captures.iter().any(|occurrence| {
                occurrence.code == action.code
                    && occurrence.context == action.context
                    && occurrence.request == action.request
            })
        {
            return Err(Failure::Invalid);
        }
    }
    charge(budget, original.discards.len())?;
    captures
        .try_reserve(original.discards.len())
        .map_err(|_| Failure::Resource)?;
    for port in &original.discards {
        let source = program
            .nodes
            .get(index(port.source))
            .ok_or(Failure::Invalid)?;
        let super::effect::EffectExprKind::Operation(EffectOperation::Discard(discard)) =
            &source.kind
        else {
            return Err(Failure::Invalid);
        };
        if port.source.arena() != original.source_arena
            || discard.handler() != port.handler
            || discard.owner() != port.resume
            || port.clause.arena() != original.source_arena
        {
            return Err(Failure::Invalid);
        }
        match port.owner {
            ConditionalCaptureOwner::EntryClause(ordinal) => {
                let clause = original
                    .ports
                    .clauses
                    .get(ordinal)
                    .ok_or(Failure::Invalid)?;
                if clause.handler != port.handler
                    || clause.resume != port.resume
                    || original
                        .correspondence
                        .get(index(port.clause))
                        .copied()
                        .flatten()
                        != Some(clause.root)
                {
                    return Err(Failure::Invalid);
                }
            }
            ConditionalCaptureOwner::Nested(owner) => {
                charge(budget, program.nodes.len())?;
                let handler = program
                    .nodes
                    .iter()
                    .enumerate()
                    .find_map(|(ordinal, node)| match &node.kind {
                        super::effect::EffectExprKind::Operation(EffectOperation::Handler(
                            handler,
                        )) if handler.id() == port.handler => Some((ordinal, handler)),
                        _ => None,
                    })
                    .ok_or(Failure::Invalid)?;
                charge(budget, handler.1.clauses().len())?;
                let projected = original
                    .correspondence
                    .get(handler.0)
                    .copied()
                    .flatten()
                    .ok_or(Failure::Invalid)?;
                let Some(Control::Handler { clauses, .. }) = original
                    .graph
                    .code
                    .get(index(projected).checked_add(1).ok_or(Failure::Resource)?)
                else {
                    return Err(Failure::Invalid);
                };
                let mut ordinal = None;
                for (candidate, clause) in handler.1.clauses().iter().enumerate() {
                    if clause.resume() == port.resume && clause.body() == port.clause {
                        if ordinal.is_some() {
                            return Err(Failure::Invalid);
                        }
                        ordinal = Some(candidate);
                    }
                }
                if clauses
                    .get(ordinal.ok_or(Failure::Invalid)?)
                    .map(|clause| clause.owner)
                    != Some(owner)
                {
                    return Err(Failure::Invalid);
                }
            }
        }

        charge(budget, 1)?;
        let code = index(port.projected)
            .checked_add(1)
            .and_then(|n| n.checked_add(code_offset))
            .ok_or(Failure::Resource)?;
        let Control::Discard { owner, .. } = actual.graph.code.get(code).ok_or(Failure::Invalid)?
        else {
            return Err(Failure::Invalid);
        };
        let expected_owner = match port.owner {
            ConditionalCaptureOwner::Nested(code) => code.checked_add(code_offset),
            ConditionalCaptureOwner::EntryClause(ordinal) => owner_start.checked_add(ordinal),
        }
        .ok_or(Failure::Resource)?;
        if *owner != expected_owner || port.source.arena() != original.source_arena {
            return Err(Failure::Invalid);
        }
        let mut joined = EffectRow::empty();
        for occurrence in &analysis.actual_captures {
            charge(budget, 1)?;
            if occurrence.code != code {
                continue;
            }
            let mut row = EffectRow::empty();
            for action in &analysis.cleanup_rows {
                charge(budget, 1)?;
                if action.code != code
                    || action.context != occurrence.context
                    || action.request != occurrence.request
                {
                    continue;
                }
                let mut demand = crate::types::clone_effect_row_with_budget(&action.row, budget)
                    .map_err(|_| Failure::Resource)?;
                let mut metadata = MetadataVariables::default();
                retain_row_variables(&mut metadata, &demand, budget)?;
                if metadata
                    .variables
                    .contains(&original.ports.clauses[0].residual)
                    || matches!(
                        demand.tail().map(|tail| tail.variable()),
                        Some(crate::types::EffectRowVariable::Inference(_))
                    )
                {
                    return Err(Failure::Invalid);
                }
                for effect in &action.retained {
                    demand = match demand
                        .remove_exact_with_budget(effect, budget)
                        .map_err(|_| Failure::Resource)?
                    {
                        Ok(row) => row,
                        Err(crate::types::EffectRowError::Missing) => demand,
                        Err(_) => return Err(Failure::Invalid),
                    };
                }
                row = row
                    .union_with_budget(&demand, budget)
                    .map_err(|_| Failure::Resource)?
                    .map_err(|_| Failure::Invalid)?;
            }
            joined = joined
                .union_with_budget(&row, budget)
                .map_err(|_| Failure::Resource)?
                .map_err(|_| Failure::Invalid)?;
            let (request, path) = analysis.actual_request_path(occurrence.request, budget)?;
            charge(budget, 1)?;
            witnesses.try_reserve(1).map_err(|_| Failure::Resource)?;
            witnesses.push(ActualCaptureWitness {
                input: port.input,
                request,
                path,
                row,
            });
        }
        if let Some(previous) = captures.insert(port.input, joined) {
            drop(previous);
            return Err(Failure::Invalid);
        }
    }
    Ok(ActualCaptureInputs {
        template: original.template,
        rows: captures,
        witnesses,
    })
}

fn provided_source(program: &super::UnvalidatedEffectProgram) -> Result<Span, Failure> {
    program
        .nodes
        .get(index(program.root))
        .and_then(|node| node.origin.as_ref())
        .map(|origin| origin.primary_span())
        .ok_or(Failure::Invalid)
}

struct BuiltCaptureGraph {
    graph: SummaryGraph,
    roots: Vec<usize>,
    values: Vec<Value>,
    has_discard: bool,
}

#[inline(never)]
fn retain_provider_source_capture<'a, F: CoreOperationFamily>(
    nodes: &'a [StoredNode<F>],
    scope: &'a super::provider::ProviderScopeNode,
    operation: fn(&F::Kind) -> Option<&EffectOperation>,
    source_layouts: &mut Vec<super::provider::AuthenticatedProviderSourceCapture<'a>>,
    budget: &mut TypeWorkBudget,
) -> Result<(), Failure> {
    let view = if scope.descriptor.admitted_arc().is_some() {
        super::provider::authenticate_admitted_provider_capture(
            scope.handler.body().arena(),
            nodes,
            scope,
            operation,
            budget,
        )
        .map(super::provider::AuthenticatedProviderSourceCapture::Admitted)
    } else {
        super::provider::authenticate_prepared_provider_capture(
            scope.handler.body().arena(),
            nodes,
            scope,
            operation,
            budget,
        )
        .map(super::provider::AuthenticatedProviderSourceCapture::Prepared)
    }
    .map_err(|error| {
        if error.reason() == crate::core::ValidationReason::Resource {
            Failure::Resource
        } else {
            Failure::Invalid
        }
    })?;
    charge(budget, 1)?;
    source_layouts
        .try_reserve(1)
        .map_err(|_| Failure::Resource)?;
    source_layouts.push(view);
    Ok(())
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
    conditional_values: Option<(&[value::ConditionalClauseInput<'_>], &mut Option<usize>)>,
    ordinary_control: bool,
    domain: Option<&HashSet<usize>>,
    authentic_layouts: Option<&AuthenticatedCaptureLayouts<'_>>,
    source_builder: Option<&CoreBuilder<F>>,
    provider_phase: ProviderCapturePhase,
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
    let mut source_layouts = Vec::new();
    for (id, node) in nodes.iter().enumerate() {
        let active = domain.is_none_or(|domain| domain.contains(&id));
        if active {
            if let Some(EffectOperation::Cleanup(scope)) = operation(&node.kind) {
                resource_scope.get_or_insert(scope.span);
            }
            if let Some(EffectOperation::Resource(resource)) = operation(&node.kind) {
                resource_scope.get_or_insert(resource.acquisition.span);
            }
            if let Some(EffectOperation::ProviderScope(scope)) = operation(&node.kind) {
                resource_scope
                    .get_or_insert(node.origin.as_ref().ok_or(Failure::Invalid)?.primary_span());
                if matches!(provider_phase, ProviderCapturePhase::SourcePreparation)
                    && scope.member_count() > 1
                {
                    retain_provider_source_capture(
                        nodes,
                        scope,
                        operation,
                        &mut source_layouts,
                        budget,
                    )?;
                }
            }
            if let Some(EffectOperation::Registration(scope)) = operation(&node.kind) {
                resource_scope.get_or_insert(scope.span);
            }
            has_discard |= matches!(operation(&node.kind), Some(EffectOperation::Discard(_)));
        }
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
        && summary_roots.is_none_or(|(roots, _, _, _, _, _)| roots.is_empty())
    {
        return Ok(None);
    }

    let values = solve_capture_values(
        nodes,
        &bindings,
        &parameters,
        &imported,
        operation,
        domain,
        budget,
    )?;

    // Canonical source roots and unproved raw producer roots both retain
    // their actual value ports. The latter are subsequently Unknown; neither
    // may be replaced by a canonical binder capture from below the cut.
    let mut capture_ports = Vec::new();
    let ports: &[NodeId] = if let Some((_, _, _, instantiations, dictionary_variables, _)) =
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
        summary_roots.map_or(&[][..], |(_, _, _, instantiations, _, _)| instantiations)
    };
    // Ordinary helper prerequisites are separate from a family's initializer.
    // Authenticate their exact original catalogue nodes once for this grouped
    // source analysis. Legacy graphs and executable queries take no new walk.
    let source_occurrences = if matches!(provider_phase, ProviderCapturePhase::SourcePreparation)
        && !source_layouts.is_empty()
    {
        source_builder
            .map(|builder| {
                super::dialect::authenticate_source_layout_occurrences(builder, nodes, budget)
                    .map_err(|error| match error {
                        super::BuildError::TypeWorkExceeded => Failure::Resource,
                        _ => Failure::Invalid,
                    })
            })
            .transpose()?
    } else {
        None
    };
    let mut data = value::Graph::build_in_domain(
        nodes,
        globals,
        imports,
        &imported,
        operation,
        methods,
        adapters,
        summary_roots.map_or(&[], |(_, _, data, _, _, _)| data),
        ports,
        conditional_values,
        domain,
        authentic_layouts,
        &source_layouts,
        source_occurrences.as_ref().filter(|view| !view.is_empty()),
        summary_roots.and_then(|(_, _, _, _, _, declared)| declared),
        budget,
    )?;
    if let Some((_, lexical, _, _, dictionary_variables, _)) = summary_roots {
        data.retain_provider_lexical(nodes, lexical, budget)?;
        data.refuse_provider_dictionary_variables(nodes, dictionary_variables, budget)?;
    }
    let (mut graph, roots) = compile_with_boundary(
        nodes,
        &values,
        &imported,
        operation,
        &mut data,
        summary_roots.is_some() && !ordinary_control,
        boundary,
        domain,
        &source_layouts,
        provider_phase,
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
    domain: Option<&HashSet<usize>>,
    budget: &mut TypeWorkBudget,
) -> Result<Vec<Value>, Failure> {
    // First solve finite value references. No request conclusion is made from
    // an unfinished recursive dependency.
    let mut values = Vec::new();
    values
        .try_reserve_exact(nodes.len())
        .map_err(|_| Failure::Resource)?;
    for id in 0..nodes.len() {
        values.push(Value {
            unknown: domain.is_some_and(|domain| !domain.contains(&id)),
            ..Value::default()
        });
    }
    loop {
        let mut changed = false;
        for (id, node) in nodes.iter().enumerate() {
            charge(budget, 1)?;
            if domain.is_some_and(|domain| !domain.contains(&id)) {
                continue;
            }
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
                                let (callable, offset) =
                                    imported.get(*target, nodes.len(), budget)?;
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
                        if scope.member_count() > 1 {
                            charge(budget, scope.member_count())?;
                        }
                        for member in 0..scope.member_count() {
                            let handler = scope.handler_member(member).ok_or(Failure::Invalid)?;
                            if scope.member_count() > 1 {
                                charge(budget, handler.clauses().len())?;
                            }
                            for clause in handler.clauses() {
                                value.join(&values[index(clause.body())], budget)?;
                            }
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
    fn request_copy_retains_exact_legacy_and_group_work_boundaries() {
        use crate::{module::ModuleId, types::EffectId};
        let source = SourceFile::new("request-copy.ash", "x").unwrap();
        let span = source.span(ByteRange::new(0, 1).unwrap()).unwrap();
        let legacy = Request::unknown(span);
        assert!(matches!(
            legacy.copy(&mut TypeWorkBudget::with_limit(0)),
            Err(Failure::Resource)
        ));
        let mut exact = TypeWorkBudget::with_limit(1);
        let copied = legacy.copy(&mut exact).unwrap();
        assert_eq!(exact.used(), 1);
        assert!(copied.members.is_empty() && copied.clause_members.is_empty());

        let effect = Arc::new(EffectInstance::new(
            EffectId::new(ModuleId::new(60_001), 0),
            Box::new([]),
        ));
        let mut group = Request::unknown(span);
        group.members = vec![
            ProviderCaptureMember {
                provided: Arc::clone(&effect),
                native: Arc::clone(&effect),
            },
            ProviderCaptureMember {
                provided: Arc::clone(&effect),
                native: effect,
            },
        ];
        group.clause_members = vec![0, 1, 1];
        // Original request copy, two member references, and the three-entry
        // clause map plus its genuine nonempty-group reservation debit.
        let required = 1 + 2 + 3 + 1;
        for prefix in [0, 9] {
            for available in 0..required {
                let mut short = TypeWorkBudget::with_limit(prefix + available);
                short.charge(prefix).unwrap();
                assert!(matches!(group.copy(&mut short), Err(Failure::Resource)));
            }
            let mut exact = TypeWorkBudget::with_limit(prefix + required);
            exact.charge(prefix).unwrap();
            let copied = group.copy(&mut exact).unwrap();
            assert_eq!(exact.used(), prefix + required);
            assert_eq!(copied.clause_members, group.clause_members);
            assert_eq!(copied.members.len(), 2);
        }
    }

    // Metadata extraction reads these original typed envelopes; this fixture
    // does not claim independent executable admission for its scalar payloads.
    fn metadata_header_nodes() -> Vec<StoredNode<super::super::effect::EffectOperationFamily>> {
        use super::super::{
            TypedBinder,
            dialect::{ArenaId, DialectId},
            effect::{EffectExprKind, EffectOperationFamily, ResourceScopeNode},
            literal::UnitNode,
            type_ops::{TypeAbstractionNode, TypeApplicationNode},
        };
        use crate::{
            interface::LexicalEvidenceId,
            module::ModuleId,
            resolved::{ResourceAcquisition, ResourceMethods},
            source::Origin,
            types::{
                ComputationType, EffectId, EffectRowVariable, Kind, KindedArgument,
                ResourceDefinitionId,
            },
        };
        let module = ModuleId::new(0);
        let arena = ArenaId::new(0);
        let file = SourceFile::new("metadata-original", "()").unwrap();
        let origin = Origin::Source(file.span(ByteRange::new(0, 2).unwrap()).unwrap());
        let variable = |id| TypeVariableId::generated(id);
        let node_id = |id| NodeId::new(arena, id);
        let row = EffectRow::with_tail(
            Box::new([EffectInstance::new(
                EffectId::new(module, 0),
                Box::new([Type::Variable(variable(900))]),
            )]),
            EffectRowVariable::Rigid(variable(901)),
            Box::new([EffectInstance::new(
                EffectId::new(module, 1),
                Box::new([Type::Variable(variable(902))]),
            )]),
        );
        let metadata = Type::ResourceApply(
            ResourceDefinitionId::new(module, 0),
            Box::new([
                KindedArgument::TypeArg(Type::EffectfulFunction(
                    Box::new(Type::Variable(variable(903))),
                    Box::new(ComputationType::new(
                        Type::Forall(
                            Box::new([
                                (variable(904), Kind::Type),
                                (variable(911), Kind::EffectRow),
                            ]),
                            Box::new(Type::EffectfulFunction(
                                Box::new(Type::Variable(variable(904))),
                                Box::new(ComputationType::new(
                                    Type::Unit,
                                    EffectRow::open(
                                        EffectRowVariable::Rigid(variable(911)),
                                        Box::new([]),
                                    ),
                                )),
                            )),
                        ),
                        row.clone(),
                    )),
                )),
                KindedArgument::RowArg(row),
            ]),
        );
        let unit = |ty, effects, kind| StoredNode::<EffectOperationFamily> {
            dialect: DialectId::named(EffectOperationFamily::DIALECT_NAME),
            ty,
            effects,
            origin: Some(origin.clone()),
            kind,
        };
        vec![
            unit(
                metadata,
                EffectRow::open(EffectRowVariable::Rigid(variable(905)), Box::new([])),
                EffectExprKind::Pure(PureExprKind::Value(PureValue::Unit(UnitNode))),
            ),
            unit(
                Type::Unit,
                EffectRow::empty(),
                EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeApplication(
                    TypeApplicationNode::new_with_row_arguments(
                        node_id(0),
                        vec![Type::Variable(variable(906))],
                        vec![EffectRow::open(
                            EffectRowVariable::Rigid(variable(907)),
                            Box::new([EffectInstance::new(
                                EffectId::new(module, 2),
                                Box::new([Type::Variable(variable(908))]),
                            )]),
                        )],
                    ),
                ))),
            ),
            unit(
                Type::Unit,
                EffectRow::empty(),
                EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeAbstraction(
                    TypeAbstractionNode::new(vec![(variable(901), Kind::EffectRow)], node_id(1)),
                ))),
            ),
            unit(
                Type::Unit,
                EffectRow::empty(),
                EffectExprKind::Operation(EffectOperation::Resource(Box::new(
                    ResourceScopeNode::new(
                        ResourceAcquisition {
                            builtin: module,
                            identity: variable(900),
                            handle: BinderId::generated(900),
                            provider: LexicalEvidenceId::new(module, 0),
                            methods: ResourceMethods::Cell([
                                BinderId::generated(901),
                                BinderId::generated(902),
                            ]),
                            span: origin.primary_span(),
                        },
                        TypedBinder::new(
                            arena,
                            BinderId::generated(900),
                            Type::Int,
                            origin.clone(),
                        ),
                        node_id(0),
                        node_id(2),
                    ),
                ))),
            ),
            // Same diagnostic origin and scalar operation; exact original node
            // identity still names different metadata and a separate entry.
            unit(
                Type::Variable(variable(909)),
                EffectRow::empty(),
                EffectExprKind::Pure(PureExprKind::Value(PureValue::Unit(UnitNode))),
            ),
        ]
    }

    fn metadata_header_operation(kind: &super::super::EffectExprKind) -> Option<&EffectOperation> {
        match kind {
            super::super::EffectExprKind::Operation(operation) => Some(operation),
            _ => None,
        }
    }

    fn metadata_recipe_nodes(
        headers: &[Vec<u32>],
        children: &[Vec<u32>],
    ) -> Vec<StoredNode<super::super::effect::EffectOperationFamily>> {
        use super::super::{data::TupleNode, dialect::ArenaId, effect::EffectExprKind};
        headers
            .iter()
            .zip(children)
            .map(|(header, children)| {
                let mut node = metadata_header_nodes().pop().unwrap();
                node.ty = match header.as_slice() {
                    [] => Type::Unit,
                    [variable] => Type::Variable(TypeVariableId::generated(*variable)),
                    variables => Type::Tuple(
                        variables
                            .iter()
                            .map(|variable| Type::Variable(TypeVariableId::generated(*variable)))
                            .collect(),
                    ),
                };
                node.effects = EffectRow::empty();
                node.kind = EffectExprKind::Pure(PureExprKind::Computation(
                    PureComputation::Tuple(TupleNode::new(
                        children
                            .iter()
                            .map(|child| NodeId::new(ArenaId::new(0), *child))
                            .collect(),
                    )),
                ));
                node
            })
            .collect()
    }

    fn metadata_seed(variables: &[u32]) -> MetadataVariables {
        let mut seed = MetadataVariables::default();
        for &variable in variables {
            seed.retain(
                TypeVariableId::generated(variable),
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap();
        }
        seed
    }

    fn metadata_reference(
        nodes: &[StoredNode<super::super::effect::EffectOperationFamily>],
        root: usize,
        seed: &[u32],
    ) -> MetadataVariables {
        let mut value = metadata_seed(seed);
        retain_function_metadata(
            &mut value,
            nodes,
            root,
            metadata_header_operation,
            &mut NodeMetadataHeaders::default(),
            &mut TypeWorkBudget::unbounded(),
        )
        .unwrap();
        value
    }

    fn requested_metadata_compact(
        owner: &FunctionMetadataPreparation<'_, super::super::effect::EffectOperationFamily>,
        root: usize,
    ) -> bool {
        let requested = owner
            .headers
            .get(&root)
            .and_then(|header| header.requested)
            .unwrap();
        matches!(
            owner.completed[requested.get() - 1],
            CompletedRoot::Compact(_)
        )
    }

    fn requested_metadata_matches(
        owner: &mut FunctionMetadataPreparation<'_, super::super::effect::EffectOperationFamily>,
        root: usize,
        seed: &[u32],
    ) {
        let expected = metadata_reference(owner.nodes, root, seed);
        let mut actual = metadata_seed(seed);
        owner
            .retain_into(&mut actual, root, &mut TypeWorkBudget::unbounded())
            .unwrap();
        assert_eq!(actual.variables, expected.variables);
        assert_eq!(actual.identities, expected.identities);
    }

    #[test]
    fn requested_metadata_empty_completed_bindings_preserve_large_metadata_and_seeded_membership() {
        use super::super::{
            dialect::ArenaId, effect::EffectExprKind, type_ops::TypeAbstractionNode,
        };
        use crate::types::Kind;
        let mut nodes =
            metadata_recipe_nodes(&[(1200..1264).collect(), vec![]], &[vec![], vec![0]]);
        let Type::Tuple(elements) = &mut nodes[0].ty else {
            unreachable!()
        };
        let mut expanded = std::mem::take(elements).into_vec();
        expanded.extend([Type::Int, Type::Bool, Type::Unit, Type::String]);
        *elements = expanded.into_boxed_slice();
        let seed = [1500, 1200, 1201];
        let mut owner = FunctionMetadataPreparation::new(&nodes, metadata_header_operation);
        for _ in 0..2 {
            requested_metadata_matches(&mut owner, 1, &seed);
            let actual = owner.collect(1, &mut TypeWorkBudget::unbounded()).unwrap();
            let expected = metadata_reference(&nodes, 1, &[]);
            assert_eq!(actual.variables, expected.variables);
            assert_eq!(actual.identities, expected.identities);
            assert_eq!(actual.variables.len(), 64);
        }
        assert!(!requested_metadata_compact(&owner, 1));
        drop(owner);
        nodes[1].kind = EffectExprKind::Pure(PureExprKind::Computation(
            PureComputation::TypeAbstraction(TypeAbstractionNode::new(
                vec![(TypeVariableId::generated(1200), Kind::Type)],
                NodeId::new(ArenaId::new(0), 0),
            )),
        ));
        let mut owner = FunctionMetadataPreparation::new(&nodes, metadata_header_operation);
        requested_metadata_matches(&mut owner, 1, &seed);
        let mut actual = metadata_seed(&seed);
        owner
            .retain_into(&mut actual, 1, &mut TypeWorkBudget::unbounded())
            .unwrap();
        assert!(!actual.identities.contains(&TypeVariableId::generated(1200)));
        assert!(actual.identities.contains(&TypeVariableId::generated(1500)));
        assert!(actual.identities.contains(&TypeVariableId::generated(1201)));
    }

    #[test]
    fn requested_metadata_distinct_roots_reuse_shared_descending_dag() {
        let nodes = metadata_recipe_nodes(
            &[vec![940], vec![941], vec![942], vec![943], vec![944]],
            &[vec![], vec![0], vec![0], vec![1, 2], vec![3, 1]],
        );
        let mut owner = FunctionMetadataPreparation::new(&nodes, metadata_header_operation);
        for root in [1, 2, 3, 4, 1] {
            let actual = owner
                .collect(root, &mut TypeWorkBudget::unbounded())
                .unwrap();
            let expected = metadata_reference(&nodes, root, &[]);
            assert_eq!(actual.variables, expected.variables);
            assert_eq!(actual.identities, expected.identities);
            assert!(requested_metadata_compact(&owner, root));
            requested_metadata_matches(&mut owner, root, &[946, 940]);
        }
        assert!(
            owner.headers[&0].requested.is_none(),
            "visited leaves are not requested roots"
        );
        let mut fresh = FunctionMetadataPreparation::new(&nodes, metadata_header_operation);
        fresh.collect(4, &mut TypeWorkBudget::unbounded()).unwrap();
        assert_eq!(
            fresh.completed.len(),
            1,
            "a fresh owner inherits no requested coordinates"
        );
    }

    #[test]
    fn requested_metadata_generic_function_body_order_is_a_structural_beneficiary() {
        use super::super::{
            TypedBinder, dialect::ArenaId, effect::EffectExprKind, function::FunctionNode,
            type_ops::TypeAbstractionNode,
        };
        use crate::types::Kind;
        let mut children = vec![vec![]];
        for id in 1..24 {
            children.push(vec![id - 1]);
        }
        children.extend([vec![23], vec![24]]);
        let mut nodes = metadata_recipe_nodes(&vec![vec![]; 26], &children);
        let arena = ArenaId::new(0);
        nodes[24].kind =
            EffectExprKind::Pure(PureExprKind::Value(PureValue::Function(FunctionNode::new(
                TypedBinder::new(
                    arena,
                    BinderId::generated(1500),
                    Type::Unit,
                    nodes[24].origin.clone().unwrap(),
                ),
                NodeId::new(arena, 23),
            ))));
        nodes[25].kind = EffectExprKind::Pure(PureExprKind::Computation(
            PureComputation::TypeAbstraction(TypeAbstractionNode::new(
                vec![(TypeVariableId::generated(1501), Kind::Type)],
                NodeId::new(arena, 24),
            )),
        ));
        // ValueGraph visits the Function first and requests M, then visits its
        // enclosing TypeAbstraction and requests F. Those roots are distinct.
        let mut owner = FunctionMetadataPreparation::new(&nodes, metadata_header_operation);
        owner.collect(23, &mut TypeWorkBudget::unbounded()).unwrap();
        let mut reused_budget = TypeWorkBudget::unbounded();
        let reused = owner.collect(24, &mut reused_budget).unwrap();
        let mut cold_owner = FunctionMetadataPreparation::new(&nodes, metadata_header_operation);
        let mut cold_budget = TypeWorkBudget::unbounded();
        let cold = cold_owner.collect(24, &mut cold_budget).unwrap();
        assert_eq!(reused.variables, cold.variables);
        assert_eq!(reused.identities, cold.identities);
        assert!(reused_budget.used() < cold_budget.used());
        assert_eq!(owner.completed.len(), 2);
    }

    #[test]
    fn requested_metadata_cached_complete_bindings_filter_prefilled_state() {
        let nodes = metadata_header_nodes();
        let mut owner = FunctionMetadataPreparation::new(&nodes, metadata_header_operation);
        for root in [0, 2, 3, 3] {
            let actual = owner
                .collect(root, &mut TypeWorkBudget::unbounded())
                .unwrap();
            assert_eq!(
                actual.variables,
                metadata_reference(&nodes, root, &[]).variables
            );
            requested_metadata_matches(&mut owner, root, &[900, 901, 911, 947]);
        }
        assert!(requested_metadata_compact(&owner, 3));
        let mut value = metadata_seed(&[900, 901, 911, 947]);
        owner
            .retain_into(&mut value, 3, &mut TypeWorkBudget::unbounded())
            .unwrap();
        assert!(!value.identities.contains(&TypeVariableId::generated(900)));
        assert!(!value.identities.contains(&TypeVariableId::generated(901)));
        assert!(
            value.identities.contains(&TypeVariableId::generated(911)),
            "Forall shielding remains header-local"
        );
    }

    #[test]
    fn requested_metadata_forward_and_cyclic_recipes_keep_independent_order() {
        // R children [B,A]; independent R sees [x,z,y], A sees [x,y,z].
        let nodes = metadata_recipe_nodes(
            &[vec![], vec![951], vec![950], vec![952]],
            &[vec![1, 2], vec![], vec![3, 0], vec![]],
        );
        for roots in [[3, 1, 0, 2, 0], [2, 3, 1, 0, 2]] {
            let mut owner = FunctionMetadataPreparation::new(&nodes, metadata_header_operation);
            for root in roots {
                let actual = owner
                    .collect(root, &mut TypeWorkBudget::unbounded())
                    .unwrap();
                assert_eq!(
                    actual.variables,
                    metadata_reference(&nodes, root, &[]).variables
                );
                requested_metadata_matches(&mut owner, root, &[952, 955]);
            }
            assert!(!requested_metadata_compact(&owner, 0));
            assert!(!requested_metadata_compact(&owner, 2));
        }
        let forward = metadata_recipe_nodes(&[vec![956], vec![957]], &[vec![1], vec![]]);
        let mut owner = FunctionMetadataPreparation::new(&forward, metadata_header_operation);
        owner.collect(0, &mut TypeWorkBudget::unbounded()).unwrap();
        assert!(!requested_metadata_compact(&owner, 0));
        requested_metadata_matches(&mut owner, 0, &[957]);
        // The disqualifying edge targets the already-seen root, so proving
        // only newly visited edges would incorrectly publish Compact.
        let backedge = metadata_recipe_nodes(
            &[vec![958], vec![959], vec![]],
            &[vec![], vec![2], vec![0, 1]],
        );
        let mut owner = FunctionMetadataPreparation::new(&backedge, metadata_header_operation);
        owner.collect(2, &mut TypeWorkBudget::unbounded()).unwrap();
        assert!(!requested_metadata_compact(&owner, 2));
        requested_metadata_matches(&mut owner, 2, &[958]);
    }

    #[test]
    fn requested_metadata_capacity_bounds_complete_surviving_and_bound_facts() {
        use super::super::{
            dialect::ArenaId, effect::EffectExprKind, type_ops::TypeAbstractionNode,
        };
        use crate::types::Kind;
        for width in [15, 16, 17, 33] {
            let mut nodes =
                metadata_recipe_nodes(&vec![vec![]; width + 1], &vec![vec![]; width + 1]);
            for (id, node) in nodes.iter_mut().enumerate().skip(1) {
                node.kind = EffectExprKind::Pure(PureExprKind::Computation(
                    PureComputation::TypeAbstraction(TypeAbstractionNode::new(
                        vec![(TypeVariableId::generated(1100 + id as u32), Kind::Type)],
                        NodeId::new(ArenaId::new(0), id as u32 - 1),
                    )),
                ));
            }
            let mut owner = FunctionMetadataPreparation::new(&nodes, metadata_header_operation);
            owner
                .collect(width, &mut TypeWorkBudget::unbounded())
                .unwrap();
            assert_eq!(requested_metadata_compact(&owner, width), width <= 16);
            requested_metadata_matches(&mut owner, width, &[1101, 1133, 1200]);
        }
        for surviving in [15, 16, 17] {
            let mut nodes = metadata_recipe_nodes(
                &[vec![], (1250..1250 + surviving).collect()],
                &[vec![], vec![0]],
            );
            nodes[1].kind = EffectExprKind::Pure(PureExprKind::Computation(
                PureComputation::TypeAbstraction(TypeAbstractionNode::new(
                    vec![(TypeVariableId::generated(1249), Kind::Type)],
                    NodeId::new(ArenaId::new(0), 0),
                )),
            ));
            let mut owner = FunctionMetadataPreparation::new(&nodes, metadata_header_operation);
            for _ in 0..2 {
                owner.collect(1, &mut TypeWorkBudget::unbounded()).unwrap();
                requested_metadata_matches(&mut owner, 1, &[1249]);
            }
            assert_eq!(requested_metadata_compact(&owner, 1), surviving == 15);
            for completed in &owner.completed {
                if let CompletedRoot::Compact(facts) = completed {
                    assert!(facts.surviving.len() + facts.bound.len() <= REQUESTED_METADATA_FACTS);
                }
            }
        }
    }

    #[test]
    fn requested_metadata_every_work_cut_publishes_only_complete_roots_and_retries() {
        let fixtures = [
            metadata_recipe_nodes(
                &[vec![980], vec![981], vec![], vec![982]],
                &[vec![], vec![0], vec![0, 1], vec![2]],
            ),
            metadata_recipe_nodes(
                &[vec![], vec![980], vec![981], vec![982]],
                &[vec![1, 2], vec![], vec![3, 0], vec![]],
            ),
            metadata_recipe_nodes(&[(990..1007).collect()], &[vec![]]),
            metadata_header_nodes(),
        ];
        for (fixture, nodes) in fixtures.iter().enumerate() {
            let root = if fixture == 0 || fixture == 3 { 3 } else { 0 };
            let expected = metadata_reference(nodes, root, &[]);
            let mut measured = TypeWorkBudget::unbounded();
            let mut owner = FunctionMetadataPreparation::new(nodes, metadata_header_operation);
            owner.collect(root, &mut measured).unwrap();
            let cold = measured.used();
            for prefix in [0, 7] {
                for available in 0..cold {
                    let mut owner =
                        FunctionMetadataPreparation::new(nodes, metadata_header_operation);
                    let mut budget = TypeWorkBudget::with_limit(prefix + available);
                    budget.charge(prefix).unwrap();
                    assert!(matches!(
                        owner.collect(root, &mut budget),
                        Err(Failure::Resource)
                    ));
                    assert!(owner.completed.is_empty());
                    assert!(
                        owner
                            .headers
                            .values()
                            .all(|header| header.requested.is_none())
                    );
                    let retry = owner
                        .collect(root, &mut TypeWorkBudget::unbounded())
                        .unwrap();
                    assert_eq!(retry.variables, expected.variables);
                    assert_eq!(retry.identities, expected.identities);
                }
                let mut budget = TypeWorkBudget::with_limit(prefix + cold);
                budget.charge(prefix).unwrap();
                let mut exact_owner =
                    FunctionMetadataPreparation::new(nodes, metadata_header_operation);
                exact_owner.collect(root, &mut budget).unwrap();
                assert_eq!(budget.used(), prefix + cold);
            }
            let mut warm = TypeWorkBudget::unbounded();
            owner.collect(root, &mut warm).unwrap();
            for available in 0..warm.used() {
                assert!(matches!(
                    owner.collect(root, &mut TypeWorkBudget::with_limit(available)),
                    Err(Failure::Resource)
                ));
                assert_eq!(owner.completed.len(), 1);
                let retry = owner
                    .collect(root, &mut TypeWorkBudget::unbounded())
                    .unwrap();
                assert_eq!(retry.variables, expected.variables);
                assert_eq!(retry.identities, expected.identities);
            }
        }
    }

    #[test]
    fn requested_metadata_invalid_coordinates_do_not_publish_and_valid_retry_is_independent() {
        let nodes = metadata_recipe_nodes(&[vec![1010], vec![1011]], &[vec![999], vec![]]);
        let mut owner = FunctionMetadataPreparation::new(&nodes, metadata_header_operation);
        for root in [999, 0] {
            assert!(matches!(
                owner.collect(root, &mut TypeWorkBudget::unbounded()),
                Err(Failure::Invalid)
            ));
            assert!(
                !owner
                    .headers
                    .get(&root)
                    .is_some_and(|header| header.requested.is_some())
            );
            let value = owner.collect(1, &mut TypeWorkBudget::unbounded()).unwrap();
            assert_eq!(value.variables, vec![TypeVariableId::generated(1011)]);
        }
    }

    #[test]
    fn requested_metadata_deep_preparation_and_drop_use_explicit_storage() {
        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(|| {
                const DEPTH: usize = 4096;
                let nodes = metadata_recipe_nodes(
                    &vec![vec![]; DEPTH],
                    &(0..DEPTH)
                        .map(|id| if id == 0 { vec![] } else { vec![id as u32 - 1] })
                        .collect::<Vec<_>>(),
                );
                let mut owner = FunctionMetadataPreparation::new(&nodes, metadata_header_operation);
                let value = owner
                    .collect(DEPTH - 1, &mut TypeWorkBudget::with_limit(327_680))
                    .unwrap();
                assert!(value.variables.is_empty());
                assert_eq!(owner.headers.len(), DEPTH);
                assert_eq!(owner.completed.len(), 1);
                drop(owner);
                drop(nodes);
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn metadata_scalar_admission_keeps_prior_facts_and_complete_row_shielding() {
        use crate::types::{
            EffectId, EffectRowVariable, Kind, KindedArgument, ResourceDefinitionId,
        };
        let variable = |id| TypeVariableId::generated(id);
        let leaf = Type::Variable(variable(900));
        let tagged_leaf = KindedArgument::TypeArg(leaf.clone());
        let empty = EffectRow::empty();
        let tagged_empty = KindedArgument::RowArg(empty.clone());
        let rigid = EffectRow::open(EffectRowVariable::rigid(variable(911)), Box::new([]));
        let inference = EffectRow::open(
            EffectRowVariable::inference(crate::types::InferenceVariableId::new(0)),
            Box::new([]),
        );
        let module = crate::module::ModuleId::new(0);
        let complete = EffectRow::with_tail(
            Box::new([EffectInstance::new(
                EffectId::new(module, 0),
                Box::new([Type::Variable(variable(905))]),
            )]),
            EffectRowVariable::rigid(variable(911)),
            Box::new([EffectInstance::new(
                EffectId::new(module, 1),
                Box::new([Type::Variable(variable(906))]),
            )]),
        );
        let scoped = Type::Forall(
            Box::new([(variable(900), Kind::Type)]),
            Box::new(Type::Tuple(Box::new([
                Type::Variable(variable(900)),
                Type::Variable(variable(903)),
            ]))),
        );
        let owned = Type::ResourceApply(
            ResourceDefinitionId::new(module, 0),
            Box::new([
                KindedArgument::TypeArg(leaf.clone()),
                KindedArgument::RowArg(rigid.clone()),
            ]),
        );
        for (root, additional) in [
            (Metadata::Type(&Type::String), vec![]),
            (Metadata::Type(&leaf), vec![900]),
            (Metadata::Argument(&tagged_leaf), vec![900]),
            (Metadata::Row(&empty), vec![]),
            (Metadata::Argument(&tagged_empty), vec![]),
            (Metadata::Row(&rigid), vec![911]),
            (Metadata::Row(&inference), vec![]),
            (Metadata::Row(&complete), vec![911, 906, 905]),
            (Metadata::Type(&scoped), vec![903]),
            (Metadata::Type(&owned), vec![911, 900]),
        ] {
            let seed = || {
                let mut value = MetadataVariables::default();
                value
                    .retain(variable(902), &mut TypeWorkBudget::unbounded())
                    .unwrap();
                value
            };
            let mut measured = TypeWorkBudget::unbounded();
            let mut output = seed();
            retain_metadata_variables(&mut output, root, &mut measured).unwrap();
            let expected = std::iter::once(variable(902))
                .chain(additional.into_iter().map(variable))
                .collect::<Vec<_>>();
            assert_eq!(output.variables, expected);
            for prefix in [0, 9] {
                for available in 0..measured.used() {
                    let mut refused = seed();
                    let mut work = TypeWorkBudget::with_limit(prefix + available);
                    work.charge(prefix).unwrap();
                    assert!(matches!(
                        retain_metadata_variables(&mut refused, root, &mut work),
                        Err(Failure::Resource)
                    ));
                    assert!(refused.identities.contains(&variable(902)));
                    let mut retry = seed();
                    let mut exact = TypeWorkBudget::with_limit(prefix + measured.used());
                    exact.charge(prefix).unwrap();
                    retain_metadata_variables(&mut retry, root, &mut exact).unwrap();
                    assert_eq!(exact.used(), prefix + measured.used());
                    assert_eq!(retry.variables, expected);
                }
            }
            // A second read preserves the original first-discovery order.
            retain_metadata_variables(&mut output, root, &mut TypeWorkBudget::unbounded()).unwrap();
            assert_eq!(output.variables, expected);
        }
    }

    #[test]
    fn original_header_projection_keeps_rows_order_forall_and_reader_scope_bindings() {
        let nodes = metadata_header_nodes();
        let mut work = TypeWorkBudget::unbounded();
        let mut headers = NodeMetadataHeaders::default();
        let mut scoped = MetadataVariables::default();
        retain_function_metadata(
            &mut scoped,
            &nodes,
            3,
            metadata_header_operation,
            &mut headers,
            &mut work,
        )
        .unwrap();
        assert_eq!(headers.variables.len(), 4);
        let generated = |id| TypeVariableId::generated(id);
        assert!(
            !scoped.variables.contains(&generated(900)),
            "acquired identity stays reader-local"
        );
        assert!(
            !scoped.variables.contains(&generated(901)),
            "TypeAbstraction stays reader-local"
        );
        assert!(
            !scoped.variables.contains(&generated(904)),
            "Forall shielding is per type root"
        );
        assert!(
            !scoped.variables.contains(&generated(911)),
            "Forall shields its row parameter too"
        );
        for id in [902, 903, 905, 906, 907, 908] {
            assert!(scoped.variables.contains(&generated(id)));
        }
        assert!(headers.variables[&0].contains(&generated(900)));
        assert!(headers.variables[&0].contains(&generated(901)));
        assert!(!headers.variables[&0].contains(&generated(904)));

        let mut warm = MetadataVariables::default();
        retain_function_metadata(
            &mut warm,
            &nodes,
            3,
            metadata_header_operation,
            &mut headers,
            &mut work,
        )
        .unwrap();
        assert_eq!(warm.variables, scoped.variables);
        assert_eq!(warm.identities, scoped.identities);
        let mut outside = MetadataVariables::default();
        retain_function_metadata(
            &mut outside,
            &nodes,
            0,
            metadata_header_operation,
            &mut headers,
            &mut work,
        )
        .unwrap();
        assert!(outside.variables.contains(&generated(900)));
        assert!(outside.variables.contains(&generated(901)));
        let mut original = MetadataVariables::default();
        retain_type_variables(&mut original, &nodes[0].ty, &mut work).unwrap();
        retain_row_variables(&mut original, &nodes[0].effects, &mut work).unwrap();
        assert_eq!(
            outside.variables, original.variables,
            "original header read order is retained"
        );

        let mut other = MetadataVariables::default();
        retain_function_metadata(
            &mut other,
            &nodes,
            4,
            metadata_header_operation,
            &mut headers,
            &mut work,
        )
        .unwrap();
        assert_eq!(other.variables, vec![generated(909)]);
        assert_eq!(headers.variables.len(), 5);
        // A new graph build starts empty even at the same original position.
        let mut fresh = NodeMetadataHeaders::default();
        let mut next_nodes = metadata_header_nodes();
        next_nodes[0].ty = Type::Variable(generated(910));
        next_nodes[0].effects = EffectRow::empty();
        let mut next = MetadataVariables::default();
        retain_function_metadata(
            &mut next,
            &next_nodes,
            0,
            metadata_header_operation,
            &mut fresh,
            &mut work,
        )
        .unwrap();
        assert_eq!(next.variables, vec![generated(910)]);
        assert_eq!(fresh.variables.len(), 1);
    }

    #[test]
    fn original_header_projection_completion_and_merges_have_exact_refusal_boundaries() {
        let nodes = metadata_header_nodes();
        let mut measured = TypeWorkBudget::unbounded();
        let mut complete = NodeMetadataHeaders::default();
        let mut output = MetadataVariables::default();
        complete
            .retain(
                &mut output,
                &nodes,
                0,
                metadata_header_operation,
                &mut measured,
            )
            .unwrap();
        let exact = measured.used();
        let expected = output.variables.clone();
        for prefix in [0, 9] {
            for available in 0..exact {
                let mut headers = NodeMetadataHeaders::default();
                let mut output = MetadataVariables::default();
                let mut short = TypeWorkBudget::with_limit(prefix + available);
                short.charge(prefix).unwrap();
                assert!(matches!(
                    headers.retain(
                        &mut output,
                        &nodes,
                        0,
                        metadata_header_operation,
                        &mut short
                    ),
                    Err(Failure::Resource)
                ));
                assert!(
                    headers.variables.is_empty(),
                    "partial derivation or output merge cannot complete a header"
                );
            }
            for _ in 0..2 {
                let mut headers = NodeMetadataHeaders::default();
                let mut output = MetadataVariables::default();
                let mut retry = TypeWorkBudget::with_limit(prefix + exact);
                retry.charge(prefix).unwrap();
                headers
                    .retain(
                        &mut output,
                        &nodes,
                        0,
                        metadata_header_operation,
                        &mut retry,
                    )
                    .unwrap();
                assert_eq!(retry.used(), prefix + exact);
                assert_eq!(output.variables, expected);
                assert_eq!(headers.variables[&0], expected);
            }
        }
        let width = expected.len();
        let mut warm = TypeWorkBudget::with_limit(1 + 2 * width);
        complete
            .retain(&mut output, &nodes, 0, metadata_header_operation, &mut warm)
            .unwrap();
        assert_eq!(warm.used(), 1 + 2 * width);
        assert_eq!(output.variables, expected);
        for prefix in [0, 9] {
            for available in 0..1 + 4 * width {
                let mut output = MetadataVariables::default();
                let mut short = TypeWorkBudget::with_limit(prefix + available);
                short.charge(prefix).unwrap();
                assert!(matches!(
                    complete.retain(
                        &mut output,
                        &nodes,
                        0,
                        metadata_header_operation,
                        &mut short
                    ),
                    Err(Failure::Resource)
                ));
                assert_eq!(
                    complete.variables[&0], expected,
                    "a completed immutable entry survives a refused reader merge"
                );
            }
            let mut output = MetadataVariables::default();
            let mut retry = TypeWorkBudget::with_limit(prefix + 1 + 4 * width);
            retry.charge(prefix).unwrap();
            complete
                .retain(
                    &mut output,
                    &nodes,
                    0,
                    metadata_header_operation,
                    &mut retry,
                )
                .unwrap();
            assert_eq!(retry.used(), prefix + 1 + 4 * width);
            assert_eq!(output.variables, expected);
        }
        let mut invalid = NodeMetadataHeaders::default();
        assert!(matches!(
            invalid.retain(
                &mut MetadataVariables::default(),
                &nodes,
                nodes.len(),
                metadata_header_operation,
                &mut TypeWorkBudget::unbounded()
            ),
            Err(Failure::Invalid)
        ));
        assert!(invalid.variables.is_empty());
    }

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
    fn actual_capture_domain_preserves_ordinals_and_refuses_reachable_orphan_completion() {
        use super::super::EffectExprKind;
        let (mut core, _, good, _) = checked_core();
        let root =
            core.nodes
                .iter()
                .find_map(|node| match &node.kind {
                    EffectExprKind::Pure(PureExprKind::Computation(
                        PureComputation::RecursiveBind(binding),
                    )) => binding
                        .members()
                        .iter()
                        .find(|member| member.binder().id() == good)
                        .map(|member| member.initializer()),
                    EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(
                        binding,
                    ))) if binding.binder().id() == good => Some(binding.initializer()),
                    _ => None,
                })
                .unwrap();
        let arena = core.arena;
        let orphan = core
            .nodes
            .iter_mut()
            .enumerate()
            .find_map(|(id, node)| match &mut node.kind {
                EffectExprKind::Operation(EffectOperation::Resume(resume)) => {
                    resume.handler = super::super::effect::HandlerId::new(u32::MAX);
                    Some(NodeId::new(arena, u32::try_from(id).unwrap()))
                }
                _ => None,
            })
            .unwrap();
        fn operation(kind: &EffectExprKind) -> Option<&EffectOperation> {
            match kind {
                EffectExprKind::Operation(operation) => Some(operation),
                _ => None,
            }
        }
        let query = |root, budget: &mut TypeWorkBudget| {
            let globals = [(good, root)];
            let domain =
                actual_capture_domain(&core.nodes, core.arena, root, &globals, &[], &[], budget)?;
            let roots = [root];
            let built = build_capture_graph(
                &core.nodes,
                &globals,
                &[],
                operation,
                &[],
                &[],
                Some((&roots, &[], &[], &[], &[], None)),
                None,
                None,
                true,
                Some(&domain),
                None,
                None,
                ProviderCapturePhase::SourcePreparation,
                budget,
            )?
            .ok_or(Failure::Invalid)?;
            Ok::<_, Failure>((domain, built))
        };
        let mut unlimited = TypeWorkBudget::unbounded();
        let (domain, built) = query(root, &mut unlimited).unwrap();
        assert!(domain.contains(&index(root)));
        assert!(!domain.contains(&index(orphan)));
        assert!(matches!(
            built.graph.code[index(orphan) + 1],
            Control::Unavailable
        ));
        assert!(matches!(
            query(orphan, &mut TypeWorkBudget::unbounded()),
            Err(Failure::Invalid)
        ));
        assert!(matches!(
            build_capture_graph(
                &core.nodes,
                &[(good, root)],
                &[],
                operation,
                &[],
                &[],
                Some((&[root], &[], &[], &[], &[], None)),
                None,
                None,
                true,
                None,
                None,
                None,
                ProviderCapturePhase::SourcePreparation,
                &mut TypeWorkBudget::unbounded(),
            ),
            Err(Failure::Invalid)
        ));
        let cost = unlimited.used();
        for _ in 0..2 {
            let mut short = TypeWorkBudget::with_limit(cost - 1);
            assert!(matches!(query(root, &mut short), Err(Failure::Resource)));
            let mut exact = TypeWorkBudget::with_limit(cost);
            query(root, &mut exact).unwrap();
            assert_eq!(exact.used(), cost);
        }
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
                callables: CallableSlots::default(),
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
                callables: CallableSlots::default(),
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
            callables: CallableSlots::default(),
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
        let sparse = CaptureValueSummary {
            graph: Some(Arc::new(SummaryGraph {
                effects: false,
                data: None,
                code: vec![Control::Return],
                types: TypeArguments(Vec::new()),
                callables: CallableSlots {
                    positions: vec![
                        None,
                        Some(Callable {
                            body: 0,
                            ty: Type::Unit,
                            result: Value::default(),
                        }),
                        None,
                    ],
                    absent_unit: Type::Unit,
                },
            })),
            value: Value {
                targets: vec![1],
                ..Value::default()
            },
        };
        let first = BinderId::new(1);
        let second = BinderId::new(2);
        let mut work = TypeWorkBudget::unbounded();
        let table =
            ImportedCallables::new(&[(first, &sparse), (second, &sparse)], 4, &mut work).unwrap();
        assert_eq!(table.callables.len(), 3);
        assert_eq!(table.graphs.len(), 1);
        assert_eq!(table.values[&first].targets, vec![5]);
        assert_eq!(table.values[&second].targets, vec![5]);
        assert_eq!(table.get(5, 4, &mut work).unwrap().0.ty, Type::Unit);
        for target in [4, 6, 7] {
            assert!(matches!(
                table.get(target, 4, &mut work),
                Err(Failure::Invalid)
            ));
        }
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
            let group = indexed.capture_at(index(first), budget)?.unwrap();
            assert_eq!(
                (group.replaces_node, group.free_binders.as_slice()),
                (true, &[binder][..])
            );
            let group = indexed.capture_at(index(second), budget)?.unwrap();
            assert!(!group.replaces_node && group.free_binders.is_empty());
            assert!(indexed.capture_at(usize::MAX, budget)?.is_none());
            Ok::<(), Failure>(())
        };
        // Original construction 3M, two descriptors and one retained lexical
        // binder; unchanged full-record lookups, then three borrowed descriptors.
        // Descriptor consumers separately pay their binder/record traversals.
        const EXACT: usize = 3 * 4 + 2 + 1 + (1 + 3) + (1 + 1) + 1 + 1 + 1 + 1;
        for prefix in [0, 9] {
            for allowance in 0..EXACT {
                let mut short = TypeWorkBudget::with_limit(prefix + allowance);
                short.charge(prefix).unwrap();
                assert!(matches!(run(&mut short), Err(Failure::Resource)));
            }
            for _ in 0..2 {
                let mut budget = TypeWorkBudget::with_limit(prefix + EXACT);
                budget.charge(prefix).unwrap();
                run(&mut budget).unwrap();
                assert_eq!(budget.used(), prefix + EXACT);
            }
        }
        // An abstract direct method still prunes its placeholder, even though
        // it contributes no ordinary binder reference. Dictionary arguments
        // in the original records remain available to all graph consumers.
        let mut abstract_only = methods;
        abstract_only[1].requirement = None;
        let indexed = MethodUses::new(&abstract_only, &mut TypeWorkBudget::unbounded()).unwrap();
        let group = indexed
            .capture_at(index(second), &mut TypeWorkBudget::unbounded())
            .unwrap()
            .unwrap();
        assert_eq!(
            (group.replaces_node, group.free_binders.as_slice()),
            (true, &[][..])
        );
        let indexed = MethodUses::new(&methods, &mut TypeWorkBudget::unbounded()).unwrap();
        assert_eq!(
            capture_projections(
                &builder.nodes,
                index(first),
                &[],
                &indexed,
                &[],
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap()
            .free_values,
            vec![binder],
            "the selected original binder remains a lexical dependency"
        );
        assert!(
            capture_projections(
                &builder.nodes,
                index(first),
                &[binder],
                &indexed,
                &[],
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap()
            .free_values
            .is_empty(),
            "ordinary local ownership still removes a bound binder"
        );
        assert!(
            capture_projections(
                &builder.nodes,
                index(second),
                &[],
                &indexed,
                &[],
                &mut TypeWorkBudget::unbounded(),
            )
            .unwrap()
            .free_values
            .is_empty(),
            "dictionary prerequisites are not ordinary lexical binders"
        );
        let mut zero = TypeWorkBudget::with_limit(0);
        assert!(
            MethodUses::new(&[], &mut zero)
                .unwrap()
                .at(0, &mut zero)
                .unwrap()
                .is_empty()
        );
        assert!(
            MethodUses::new(&[], &mut zero)
                .unwrap()
                .capture_at(0, &mut zero)
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn capture_graph_visits_charge_aliases_and_distinct_graphs_with_fresh_retries() {
        let make_summary = || CaptureValueSummary {
            graph: Some(Arc::new(SummaryGraph {
                effects: false,
                data: None,
                callables: CallableSlots::default(),
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
                callables: CallableSlots::default(),
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
                // Compilation charges the primitive table witness, node carrier
                // and each node before cloning the function type. Preserve the
                // same refusal in the following Value copy after that clone.
                let mut partial = TypeWorkBudget::with_limit(
                    1 + builder.nodes.len() + 1 + builder.nodes.len() + clone_work.used(),
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
                        }]
                        .into(),
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
                provider.then_some((&[root][..], &[][..], &[][..], &[][..], &[][..], None)),
                None,
                None,
                ProviderCapturePhase::Executable,
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
                    }]
                    .into(),
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
                }]
                .into(),
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
                }]
                .into(),
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
        None,
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
        match edge.owner {
            ConditionalCaptureOwner::Nested(expected) => {
                let Control::Discard { owner, node, .. } =
                    &graph.graph.code[index(edge.projected) + 1]
                else {
                    panic!("actual nested capture discard")
                };
                assert_eq!((*owner, *node), (expected, index(edge.projected)));
            }
            ConditionalCaptureOwner::EntryClause(ordinal) => {
                assert!(matches!(
                    graph.graph.code[index(edge.projected) + 1],
                    Control::Unavailable
                ));
                assert_eq!(graph.ports.clauses[ordinal].resume, edge.resume);
                assert!(
                    graph
                        .edges
                        .iter()
                        .any(|completion| completion.source == edge.source
                            && completion.port == ordinal
                            && completion.operand.is_none())
                );
            }
        }
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
