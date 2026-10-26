//! Explicit region ownership, selection and owner-targeted service operands.

use super::{NodeId, TypedBinder};
use crate::{module::ModuleId, types::TypeVariableId};

/// Concrete configuration of the compiler-owned host implementation.
/// This selects system backing; it does not select an allocation context.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum HostRegionConfiguration {
    System,
}

/// One lexical owner and its explicit private allocation handler body.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RegionScopeNode {
    pub(crate) entry: bool,
    pub(crate) api: ModuleId,
    pub(crate) identity: TypeVariableId,
    pub(crate) access: TypedBinder,
    pub(crate) preceding: NodeId,
    pub(crate) provider: NodeId,
    pub(crate) body: NodeId,
}

impl RegionScopeNode {
    #[must_use]
    pub const fn identity(&self) -> TypeVariableId {
        self.identity
    }
    #[must_use]
    pub const fn access(&self) -> &TypedBinder {
        &self.access
    }
    #[must_use]
    pub const fn preceding(&self) -> NodeId {
        self.preceding
    }
    #[must_use]
    pub const fn provider(&self) -> NodeId {
        self.provider
    }
    #[must_use]
    pub const fn body(&self) -> NodeId {
        self.body
    }
}

/// The narrow owner-targeted allocation primitive. Both children are explicit.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RegionAllocateNode {
    pub(crate) api: ModuleId,
    pub(crate) context: NodeId,
    pub(crate) request: NodeId,
}

impl RegionAllocateNode {
    #[must_use]
    pub const fn context(&self) -> NodeId {
        self.context
    }
    #[must_use]
    pub const fn request(&self) -> NodeId {
        self.request
    }
}

/// Immediate layout request for a persistent typed value array.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RegionValueRequestNode {
    pub(crate) api: ModuleId,
    pub(crate) fields: usize,
}

/// Tuple or nominal initialization into supplied pending storage.
/// Evaluate context, original fields in order, then explicit storage; initialize locally.
/// Nominal storage includes its private discriminant before the optional payload.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RegionTupleNode {
    pub(crate) constructor: Option<crate::types::ConstructorId>,
    pub(crate) api: ModuleId,
    pub(crate) context: NodeId,
    pub(crate) storage: NodeId,
    pub(crate) fields: Box<[NodeId]>,
}

/// Closure creation into the same supplied Value slots used by records.
/// Context, capture operands and storage are strict; the function body is delayed.
/// Capture binders identify existing lexical values, not new binding definitions.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RegionClosureNode {
    pub(crate) api: ModuleId,
    pub(crate) context: NodeId,
    pub(crate) captures: Box<[NodeId]>,
    pub(crate) storage: NodeId,
    pub(crate) function: super::function::FunctionNode,
}

/// Reconstruct owner effects from its children and the fixed pair's full rows.
/// The preceding query runs before this owner and is never discharged here.
pub(crate) fn owner_effects(
    scope: &RegionScopeNode,
    provider_type: &crate::types::Type,
    preceding: &crate::types::EffectRow,
    provider: &crate::types::EffectRow,
    body: &crate::types::EffectRow,
    budget: &mut crate::types::TypeWorkBudget,
) -> Result<crate::types::EffectRow, ()> {
    use crate::types::{EffectInstance, EffectRow, EffectRowError, Type};
    let api = crate::resolved::RegionApi::for_module(scope.api).ok_or(())?;
    let Type::Tuple(members) = provider_type else {
        return Err(());
    };
    let [allocate, release] = members.as_ref() else {
        return Err(());
    };
    let allocate = allocate.function_view().ok_or(())?;
    let release = release.function_view().ok_or(())?;
    let instance = EffectInstance::new(api.default_alloc(), Box::new([]));
    let mut row = match body.remove_exact_with_budget(&instance, budget)? {
        Ok(row) => row,
        Err(EffectRowError::Missing) => crate::types::clone_effect_row_with_budget(body, budget)?,
        Err(_) => return Err(()),
    };
    let empty = EffectRow::empty();
    for additional in [
        preceding,
        provider,
        allocate.effects().unwrap_or(&empty),
        release.effects().unwrap_or(&empty),
    ] {
        row = row.union_with_budget(additional, budget)?.map_err(|_| ())?;
    }
    Ok(row)
}

pub(crate) fn allocation_effects(
    allocation: &RegionAllocateNode,
    context: &crate::types::EffectRow,
    request: &crate::types::EffectRow,
    budget: &mut crate::types::TypeWorkBudget,
) -> Result<crate::types::EffectRow, ()> {
    use crate::types::{EffectInstance, EffectRow};
    let api = crate::resolved::RegionApi::for_module(allocation.api).ok_or(())?;
    let row = context
        .union_with_budget(request, budget)?
        .map_err(|_| ())?;
    row.union_with_budget(
        &EffectRow::singleton(EffectInstance::new(api.default_alloc(), Box::new([]))),
        budget,
    )?
    .map_err(|_| ())
}

/// Closed byte construction. Its request layout is computed locally after the
/// explicit context and original operand have each been evaluated once.
/// Allocation uses that context's existing service; no payload enters Request.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RegionBufferNode {
    pub(crate) api: ModuleId,
    pub(crate) context: NodeId,
    pub(crate) operand: Option<NodeId>,
    pub(crate) right: Option<NodeId>,
    pub(crate) operation: RegionBufferOperation,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RegionBufferOperation {
    IntegerLiteral(std::sync::Arc<crate::integer::Integer>),
    IntegerArithmetic(super::Primitive),
    StringLiteral(std::sync::Arc<[u8]>),
    Intrinsic(super::packed::IntrinsicNode),
}

/// The only administrative prefix admitted around a direct stored function is
/// its generated Unit context query. This does not admit arbitrary initializer code.
pub(crate) fn closure_initializer<'a, F: super::dialect::CoreOperationFamily>(
    root: NodeId,
    mut kind: impl FnMut(NodeId) -> Option<&'a F::Kind>,
) -> Option<(NodeId, &'a RegionClosureNode)>
where
    F::Kind: 'a,
{
    use super::{PureComputation, PureExprKind, PureValue, effect::EffectOperation};
    if let Some(EffectOperation::RegionClosure(closure)) = F::region_construction(kind(root)?) {
        return Some((root, closure));
    }
    let PureExprKind::Computation(PureComputation::Bind(binding)) = F::pure(kind(root)?)? else {
        return None;
    };
    let Some(EffectOperation::RegionClosure(closure)) =
        F::region_construction(kind(binding.body())?)
    else {
        return None;
    };
    let api = crate::resolved::RegionApi::for_module(closure.api)?;
    let PureExprKind::Variable(context) = F::pure(kind(closure.context)?)? else {
        return None;
    };
    let Some(EffectOperation::Request(query)) =
        F::region_construction(kind(binding.initializer())?)
    else {
        return None;
    };
    if context.binder() != binding.binder().id()
        || query.effect().effect() != api.default_alloc()
        || !query.effect().arguments().is_empty()
        || query.operation() != crate::types::OperationId::new(api.default_alloc(), 1)
        || !matches!(
            F::pure(kind(query.operand())?),
            Some(PureExprKind::Value(PureValue::Unit(_)))
        )
    {
        return None;
    }
    Some((binding.body(), closure))
}
