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

/// Local initialization into the pending storage supplied by an allocation.
/// Evaluate context, original fields in order, then explicit storage; initialize locally.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RegionTupleNode {
    pub(crate) api: ModuleId,
    pub(crate) context: NodeId,
    pub(crate) storage: NodeId,
    pub(crate) fields: Box<[NodeId]>,
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
