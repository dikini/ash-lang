//! Recipe-free metadata for independently admitted scoped providers.
//!
//! Native owners are evaluator state. This descriptor retains defining proof
//! authority and typed arguments; it is never a resource instance or a handle.

use std::sync::Arc;

use super::specialization::OriginalProviderSpecialization;
use crate::{
    core::{NodeId, TypedBinder, effect::HandlerNode},
    foreign::ForeignModuleFact,
    interface::{LexicalEvidenceId, MethodId},
    resolved::{BinderId, ResourceTypeFact},
    types::{ComputationType, ConstructorId, EffectInstance, KindedArgument, Type, TypeVariableId},
};

/// Canonical constructor identities, authenticated from defining declarations.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct ProviderScopeProtocol {
    pub(crate) acquire: [ConstructorId; 2],
    pub(crate) finish: [ConstructorId; 3],
    pub(crate) scope: [ConstructorId; 2],
    pub(crate) completion: [ConstructorId; 3],
}

/// Only the specialization admission module can construct this authority.
#[derive(Debug)]
pub(crate) struct AdmittedProviderScope {
    pub(super) definition: Arc<ResourceTypeFact>,
    pub(super) native: Arc<ForeignModuleFact>,
    pub(super) arguments: Box<[KindedArgument]>,
    pub(super) identity: TypeVariableId,
    pub(super) retained: Box<[TypeVariableId]>,
    pub(super) native_effect: EffectInstance,
    pub(super) protocol: ProviderScopeProtocol,
    pub(super) specialization: OriginalProviderSpecialization,
    pub(super) families: Box<[super::specialization::ProviderFamilyAdmission]>,
}

impl PartialEq for AdmittedProviderScope {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.definition, &other.definition)
            && Arc::ptr_eq(&self.native, &other.native)
            && self.arguments == other.arguments
            && self.identity == other.identity
            && self.retained == other.retained
            && self.native_effect == other.native_effect
            && self.protocol == other.protocol
            && self.specialization == other.specialization
            && self.families == other.families
    }
}
impl Eq for AdmittedProviderScope {}

impl AdmittedProviderScope {
    pub(crate) fn definition(&self) -> &ResourceTypeFact {
        &self.definition
    }
    pub(crate) fn native(&self) -> &ForeignModuleFact {
        &self.native
    }
    pub(crate) fn arguments(&self) -> &[KindedArgument] {
        &self.arguments
    }
    pub(crate) fn identity(&self) -> TypeVariableId {
        self.identity
    }
    pub(crate) fn retained(&self) -> &[TypeVariableId] {
        &self.retained
    }
    pub(crate) fn native_effect(&self) -> &EffectInstance {
        &self.native_effect
    }
    pub(crate) fn protocol(&self) -> ProviderScopeProtocol {
        self.protocol
    }
    pub(crate) fn specialization(&self) -> &OriginalProviderSpecialization {
        &self.specialization
    }
    pub(crate) fn native_effect_member(&self, member: usize) -> Option<&EffectInstance> {
        if member == 0 {
            Some(&self.native_effect)
        } else {
            self.families
                .get(member - 1)
                .map(|family| &family.native_effect)
        }
    }
    pub(crate) fn families(&self) -> &[super::specialization::ProviderFamilyAdmission] {
        &self.families
    }
}

impl Drop for AdmittedProviderScope {
    fn drop(&mut self) {
        for argument in std::mem::take(&mut self.arguments).into_vec() {
            crate::types::discard_kinded_argument_iteratively(argument);
        }
    }
}

/// Source preparation has genuine typed forests and body-free facts but no
/// executable permission. Final Core admission rejects this variant.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ProviderScopeAuthority {
    Prepared(Arc<PreparedProviderScopeFacts>),
    Admitted(Arc<AdmittedProviderScope>),
}
#[derive(Debug)]
pub(crate) struct PreparedProviderScopeFacts {
    metadata: super::specialization::ProviderScopeAdmission,
    capture: Option<super::specialization::PreparedProviderCaptureReceipt>,
}
impl PartialEq for PreparedProviderScopeFacts {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self, other)
    }
}
impl Eq for PreparedProviderScopeFacts {}
impl ProviderScopeAuthority {
    pub(crate) fn prepared(
        metadata: super::specialization::ProviderScopeAdmission,
        budget: &mut crate::types::TypeWorkBudget,
    ) -> Result<Self, crate::core::BuildError> {
        budget
            .charge(1)
            .map_err(|()| crate::core::BuildError::TypeWorkExceeded)?;
        Ok(Self::Prepared(Arc::new(PreparedProviderScopeFacts {
            metadata,
            capture: None,
        })))
    }
    pub(super) fn prepared_with_capture(
        metadata: super::specialization::ProviderScopeAdmission,
        capture: super::specialization::PreparedProviderCaptureReceipt,
    ) -> Self {
        Self::Prepared(Arc::new(PreparedProviderScopeFacts {
            metadata,
            capture: Some(capture),
        }))
    }
    pub(super) fn prepared_capture(
        &self,
    ) -> Option<&super::specialization::PreparedProviderCaptureReceipt> {
        match self {
            Self::Prepared(facts) => facts.capture.as_ref(),
            Self::Admitted(_) => None,
        }
    }
    #[cfg(test)]
    pub(super) fn prepared_definition_for_test(&self) -> Option<&Arc<ResourceTypeFact>> {
        match self {
            Self::Prepared(facts) => Some(&facts.metadata.definition),
            Self::Admitted(_) => None,
        }
    }
    pub(crate) fn admitted_arc(&self) -> Option<&Arc<AdmittedProviderScope>> {
        match self {
            Self::Admitted(admitted) => Some(admitted),
            Self::Prepared(_) => None,
        }
    }
    pub(crate) fn definition(&self) -> &ResourceTypeFact {
        match self {
            Self::Prepared(facts) => &facts.metadata.definition,
            Self::Admitted(facts) => facts.definition(),
        }
    }
    pub(crate) fn native(&self) -> &ForeignModuleFact {
        match self {
            Self::Prepared(facts) => &facts.metadata.native,
            Self::Admitted(facts) => facts.native(),
        }
    }
    pub(crate) fn arguments(&self) -> &[KindedArgument] {
        match self {
            Self::Prepared(facts) => &facts.metadata.arguments,
            Self::Admitted(facts) => facts.arguments(),
        }
    }
    pub(crate) fn identity(&self) -> TypeVariableId {
        match self {
            Self::Prepared(facts) => facts.metadata.identity,
            Self::Admitted(facts) => facts.identity(),
        }
    }
    pub(crate) fn retained(&self) -> &[TypeVariableId] {
        match self {
            Self::Prepared(facts) => &facts.metadata.retained,
            Self::Admitted(facts) => facts.retained(),
        }
    }
    pub(crate) fn native_effect(&self) -> &EffectInstance {
        match self {
            Self::Prepared(facts) => &facts.metadata.native_effect,
            Self::Admitted(facts) => facts.native_effect(),
        }
    }
    pub(crate) fn native_effect_member(&self, member: usize) -> Option<&EffectInstance> {
        match self {
            Self::Prepared(facts) => {
                if member == 0 {
                    Some(&facts.metadata.native_effect)
                } else {
                    facts
                        .metadata
                        .families
                        .get(member - 1)
                        .map(|family| &family.native_effect)
                }
            }
            Self::Admitted(facts) => facts.native_effect_member(member),
        }
    }
    pub(crate) fn family_members(&self) -> &[super::specialization::ProviderFamilyAdmission] {
        match self {
            Self::Prepared(facts) => &facts.metadata.families,
            Self::Admitted(facts) => facts.families(),
        }
    }
    pub(crate) fn protocol(&self) -> ProviderScopeProtocol {
        match self {
            Self::Prepared(facts) => facts.metadata.protocol,
            Self::Admitted(facts) => facts.protocol(),
        }
    }
    pub(crate) fn specialization(&self) -> Option<&OriginalProviderSpecialization> {
        self.admitted_arc().map(|facts| facts.specialization())
    }
    pub(crate) fn relocate(
        &self,
        remapped: &[Option<NodeId>],
        budget: &mut crate::types::TypeWorkBudget,
    ) -> Result<Self, crate::core::BuildError> {
        let admitted = self
            .admitted_arc()
            .ok_or(crate::core::BuildError::InvalidPayload)?;
        budget
            .charge(1)
            .map_err(|()| crate::core::BuildError::TypeWorkExceeded)?;
        Ok(Self::Admitted(Arc::new(
            admitted.relocate(remapped, budget)?,
        )))
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ProviderLifecycleEntry {
    pub(crate) parameter: TypedBinder,
    pub(crate) body: NodeId,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct ProviderForwardingMethod {
    pub(crate) method: MethodId,
    pub(crate) binder: BinderId,
}

/// One exact, nonowning handler attached to the scope's single native owner.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ProviderAttachedHandler {
    pub(crate) handler: HandlerNode,
    pub(crate) state: TypedBinder,
    pub(crate) lexical: LexicalEvidenceId,
    pub(crate) forwardings: Box<[ProviderForwardingMethod]>,
}

/// One lexical instance. Lifecycle entries and handler clauses are ordinary
/// Core graphs authenticated against the original checked specialization.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProviderScopeNode {
    pub(crate) initializer: NodeId,
    pub(crate) acquire: ProviderLifecycleEntry,
    pub(crate) finish: ProviderLifecycleEntry,
    pub(crate) handler_state: TypedBinder,
    pub(crate) handle: TypedBinder,
    pub(crate) handler: HandlerNode,
    pub(crate) handler_output: ComputationType,
    pub(crate) descriptor: ProviderScopeAuthority,
    pub(crate) lexical: LexicalEvidenceId,
    pub(crate) forwardings: Box<[ProviderForwardingMethod]>,
    pub(crate) attached: Box<[ProviderAttachedHandler]>,
    /// Exact source-order clause coordinates, retained once for constant-time graph edges.
    /// Empty for legacy single-handler scopes.
    pub(crate) family_clause_index: Box<[(usize, usize)]>,
}

impl ProviderScopeNode {
    pub(crate) fn initializer(&self) -> NodeId {
        self.initializer
    }
    pub(crate) fn acquire(&self) -> &ProviderLifecycleEntry {
        &self.acquire
    }
    pub(crate) fn finish(&self) -> &ProviderLifecycleEntry {
        &self.finish
    }
    pub(crate) fn handler_state(&self) -> &TypedBinder {
        &self.handler_state
    }
    pub(crate) fn handle(&self) -> &TypedBinder {
        &self.handle
    }
    pub(crate) fn handler(&self) -> &HandlerNode {
        &self.handler
    }
    pub(crate) fn descriptor(&self) -> &ProviderScopeAuthority {
        &self.descriptor
    }
    pub(crate) fn handler_member(&self, member: usize) -> Option<&HandlerNode> {
        if member == 0 {
            Some(&self.handler)
        } else {
            self.attached
                .get(member - 1)
                .map(|attached| &attached.handler)
        }
    }
    pub(crate) fn handler_state_member(&self, member: usize) -> Option<&TypedBinder> {
        if member == 0 {
            Some(&self.handler_state)
        } else {
            self.attached
                .get(member - 1)
                .map(|attached| &attached.state)
        }
    }
    pub(crate) fn member_count(&self) -> usize {
        self.attached.len() + 1
    }
    pub(crate) fn clause_member_at(
        &self,
        clause: usize,
    ) -> Option<(usize, &HandlerNode, &crate::core::EffectClause)> {
        let (member, local) = if self.attached.is_empty() {
            (0, clause)
        } else {
            *self.family_clause_index.get(clause)?
        };
        let handler = self.handler_member(member)?;
        Some((member, handler, handler.clauses().get(local)?))
    }

    /// Returns all initializer, lifecycle, body, and clause edges.
    pub fn child_count(&self) -> usize {
        if self.attached.is_empty() {
            self.handler.clauses().len() + 4
        } else {
            self.family_clause_index.len() + 4
        }
    }
    /// Returns one child in deterministic phase order.
    pub fn child_at(&self, index: usize) -> Option<NodeId> {
        match index {
            0 => Some(self.initializer),
            1 => Some(self.acquire.body),
            2 => Some(self.finish.body),
            3 => Some(self.handler.body()),
            index => self
                .clause_member_at(index - 4)
                .map(|(_, _, clause)| clause.body()),
        }
    }
}

impl Drop for ProviderScopeNode {
    fn drop(&mut self) {
        crate::types::discard_type_iteratively(std::mem::replace(
            &mut self.handler_output.value,
            Type::Unit,
        ));
    }
}

struct ScopeSubstitutions {
    types: std::collections::HashMap<TypeVariableId, Type>,
    rows: std::collections::HashMap<TypeVariableId, crate::types::EffectRow>,
}

impl Drop for ScopeSubstitutions {
    fn drop(&mut self) {
        for (_, ty) in self.types.drain() {
            crate::types::discard_type_iteratively(ty);
        }
        self.rows.clear();
    }
}

impl ScopeSubstitutions {
    fn insert_type(&mut self, id: TypeVariableId, ty: Type) -> bool {
        if let Some(previous) = self.types.insert(id, ty) {
            crate::types::discard_type_iteratively(previous);
            false
        } else {
            true
        }
    }
    fn insert_row(&mut self, id: TypeVariableId, row: crate::types::EffectRow) -> bool {
        if let Some(previous) = self.rows.insert(id, row) {
            drop(previous);
            false
        } else {
            true
        }
    }
    fn instantiate_effect(
        &self,
        effect: &EffectInstance,
        budget: &mut crate::types::TypeWorkBudget,
    ) -> Result<EffectInstance, crate::core::ValidationError> {
        let count = effect.arguments().len();
        budget
            .charge(
                count
                    .checked_mul(2)
                    .and_then(|n| n.checked_add(1))
                    .ok_or_else(resource)?,
            )
            .map_err(|()| resource())?;
        let mut staged = Vec::new();
        staged.try_reserve_exact(count).map_err(|_| resource())?;
        for argument in effect.arguments() {
            let argument = crate::types::substitute_kinded_argument_with(
                argument,
                &self.types,
                &self.rows,
                |cells| budget.charge(cells),
            )
            .map_err(|()| resource())?
            .map_err(|_| invalid())?;
            staged.push(crate::types::IterativeArgumentOwner::new(argument));
        }
        let mut retained = Vec::new();
        retained.try_reserve_exact(count).map_err(|_| resource())?;
        retained.extend(
            staged
                .into_iter()
                .map(crate::types::IterativeArgumentOwner::into_inner),
        );
        Ok(EffectInstance::new_kinded(
            effect.effect(),
            retained.into_boxed_slice(),
        ))
    }
    fn instantiate(
        &self,
        ty: &Type,
        budget: &mut crate::types::TypeWorkBudget,
    ) -> Result<crate::types::IterativeTypeOwner, crate::core::ValidationError> {
        let result = crate::types::substitute_type_and_row_variables_with(
            ty,
            &self.types,
            &self.rows,
            |cells| budget.charge(cells),
            || (),
        );
        result
            .map_err(|()| resource())?
            .map(crate::types::IterativeTypeOwner::new)
            .map_err(|_| invalid())
    }
}

fn nominal_arguments<'a>(
    mut ty: &'a Type,
    count: usize,
    budget: &mut crate::types::TypeWorkBudget,
) -> Result<(crate::types::NominalTypeId, Vec<&'a Type>), crate::core::ValidationError> {
    budget.charge(count).map_err(|()| resource())?;
    let mut arguments = Vec::new();
    arguments.try_reserve_exact(count).map_err(|_| resource())?;
    loop {
        budget.charge(1).map_err(|()| resource())?;
        match ty {
            Type::Application(function, argument) if arguments.len() < count => {
                arguments.push(argument.as_ref());
                ty = function;
            }
            Type::Nominal(family) if arguments.len() == count => {
                arguments.reverse();
                return Ok((*family, arguments));
            }
            _ => return Err(invalid()),
        }
    }
}

fn invalid() -> crate::core::ValidationError {
    crate::core::ValidationError::new(
        crate::core::validate::ValidationReason::ResourceEscape,
        None,
    )
}
fn resource() -> crate::core::ValidationError {
    crate::core::ValidationError::new(crate::core::validate::ValidationReason::Resource, None)
}

/// Derives protocol identities from the defining result shape and the exact
/// admitted native report facts. Spellings do not participate in authority.
pub(crate) fn derive_provider_scope_protocol(
    definition: &ResourceTypeFact,
    native: &ForeignModuleFact,
    arguments: &[KindedArgument],
    registry: &crate::resolved::ResolvedRegistry,
    budget: &mut crate::types::TypeWorkBudget,
) -> Result<ProviderScopeProtocol, crate::core::ValidationError> {
    use crate::foreign::ForeignResultFact;
    use crate::types::{Kind, Type};
    if arguments.len() != definition.parameters.len() {
        return Err(invalid());
    }
    let mut sigma = ScopeSubstitutions {
        types: std::collections::HashMap::new(),
        rows: std::collections::HashMap::new(),
    };
    budget.charge(arguments.len()).map_err(|()| resource())?;
    let row_count = arguments
        .iter()
        .filter(|argument| matches!(argument, KindedArgument::RowArg(_)))
        .count();
    sigma
        .types
        .try_reserve(arguments.len() - row_count)
        .map_err(|_| resource())?;
    sigma.rows.try_reserve(row_count).map_err(|_| resource())?;
    for (formal, actual) in definition.parameters.iter().zip(arguments) {
        let unique = match (&formal.kind, actual) {
            (Kind::EffectRow, KindedArgument::RowArg(row)) => sigma.insert_row(
                formal.id,
                crate::types::clone_effect_row_with_budget(row, budget).map_err(|()| resource())?,
            ),
            (Kind::EffectRow, _) | (_, KindedArgument::RowArg(_)) => return Err(invalid()),
            (_, KindedArgument::TypeArg(ty)) => sigma.insert_type(
                formal.id,
                crate::types::clone_type_with_budget(ty, budget).map_err(|()| resource())?,
            ),
        };
        if !unique {
            return Err(invalid());
        }
    }
    let result = sigma.instantiate(&definition.result.ty, budget)?;
    let (scope, _) = nominal_arguments(&result, 3, budget)?;
    let scope = registry.nominal(scope).ok_or_else(invalid)?;
    budget
        .charge(scope.constructors.len())
        .map_err(|()| resource())?;
    let [refused, completed] = scope.constructors.as_ref() else {
        return Err(invalid());
    };
    let completed_definition = registry.constructor(*completed).ok_or_else(invalid)?;
    let Some(payload) = completed_definition.payload.as_ref() else {
        return Err(invalid());
    };
    let Type::Tuple(completed_payload) = payload else {
        return Err(invalid());
    };
    let [_, completion] = completed_payload.as_ref() else {
        return Err(invalid());
    };
    let (completion, _) = nominal_arguments(completion, 1, budget)?;
    let completion = registry.nominal(completion).ok_or_else(invalid)?;
    budget
        .charge(completion.constructors.len())
        .map_err(|()| resource())?;
    let [closed, consumed, retained] = completion.constructors.as_ref() else {
        return Err(invalid());
    };
    let interpreted = sigma.instantiate_effect(&definition.interpreted.instance, budget)?;
    let state = sigma.instantiate(&definition.state.ty, budget)?;
    let state_family = state.outer_nominal().ok_or_else(invalid)?;
    let mut acquire = None;
    let mut finish = None;
    budget
        .charge(native.operations.len())
        .map_err(|()| resource())?;
    for operation in &native.operations {
        if operation.id.owner() != interpreted.effect() {
            continue;
        }
        match &operation.result {
            ForeignResultFact::Acquire {
                state,
                constructors,
                ..
            } if *state == state_family => {
                let value: [ConstructorId; 2] =
                    constructors.as_slice().try_into().map_err(|_| invalid())?;
                if acquire.as_ref().is_some_and(|previous| previous != &value) {
                    return Err(invalid());
                }
                acquire = Some(value);
            }
            ForeignResultFact::Finish {
                state,
                constructors,
                ..
            } if *state == state_family => {
                let value: [ConstructorId; 3] =
                    constructors.as_slice().try_into().map_err(|_| invalid())?;
                if finish.as_ref().is_some_and(|previous| previous != &value) {
                    return Err(invalid());
                }
                finish = Some(value);
            }
            _ => {}
        }
    }
    Ok(ProviderScopeProtocol {
        acquire: acquire.ok_or_else(invalid)?,
        finish: finish.ok_or_else(invalid)?,
        scope: [*refused, *completed],
        completion: [*closed, *consumed, *retained],
    })
}

/// A member's method vector does not authorize an arbitrary same-typed value.
/// Reconstruct the generated ordinary forwarding graph against the original
/// checked method-to-operation association. Whole-Core scope checking separately
/// establishes that these bindings dominate their uses.
fn authenticate_family_forwardings(
    program: &crate::core::UnvalidatedEffectProgram,
    definition: &Arc<ResourceTypeFact>,
    attached: &ProviderAttachedHandler,
    budget: &mut crate::types::TypeWorkBudget,
) -> Result<(), crate::core::ValidationError> {
    use crate::core::{
        PureComputation, PureExprKind, PureValue,
        effect::{EffectExprKind, EffectOperation},
    };
    budget
        .charge(program.registry.provider_contract_count())
        .map_err(|()| resource())?;
    let mut methods = None;
    for (_, certificate) in program.registry.provider_contracts() {
        budget
            .charge(certificate.resource_count())
            .map_err(|()| resource())?;
        if certificate
            .resource_contracts()
            .any(|(_, _, fact)| Arc::ptr_eq(fact, definition))
            && methods
                .replace(
                    certificate
                        .family_methods(definition.id)
                        .ok_or_else(invalid)?,
                )
                .is_some()
        {
            return Err(invalid());
        }
    }
    let methods = methods.ok_or_else(invalid)?;
    if methods.len() != attached.forwardings.len() {
        return Err(invalid());
    }
    for forwarding in &attached.forwardings {
        budget
            .charge(
                methods
                    .len()
                    .checked_add(program.nodes.len())
                    .ok_or_else(resource)?,
            )
            .map_err(|()| resource())?;
        let mut matching = methods
            .iter()
            .filter(|(method, _)| *method == forwarding.method);
        let (_, operation) = matching.next().ok_or_else(invalid)?;
        if matching.next().is_some() || operation.owner() != attached.handler.effect().effect() {
            return Err(invalid());
        }
        let mut binding = None;
        for stored in &program.nodes {
            let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(candidate))) =
                &stored.kind
            else {
                continue;
            };
            if candidate.binder().id() == forwarding.binder && binding.replace(candidate).is_some()
            {
                return Err(invalid());
            }
        }
        let binding = binding.ok_or_else(invalid)?;
        let initializer = super::node(program, binding.initializer())?;
        let EffectExprKind::Pure(PureExprKind::Value(PureValue::Function(function))) =
            &initializer.kind
        else {
            return Err(invalid());
        };
        let request_node = super::node(program, function.body())?;
        let EffectExprKind::Operation(EffectOperation::Request(request)) = &request_node.kind
        else {
            return Err(invalid());
        };
        let operand = super::node(program, request.operand())?;
        if request.operation() != *operation
            || crate::types::compare_effect_instances_with_budget(
                request.effect(),
                attached.handler.effect(),
                budget,
            )
            .map_err(|()| resource())?
                != std::cmp::Ordering::Equal
            || !matches!(&operand.kind, EffectExprKind::Pure(PureExprKind::Variable(variable))
                if variable.binder() == function.parameter().id())
            || !crate::types::same_type_with_budget(binding.binder().ty(), &initializer.ty, budget)
                .map_err(|()| resource())?
            || !crate::types::same_type_with_budget(function.parameter().ty(), &operand.ty, budget)
                .map_err(|()| resource())?
        {
            return Err(invalid());
        }
        let signature = initializer.ty.function_view().ok_or_else(invalid)?;
        let effects = signature.effects().ok_or_else(invalid)?;
        if !crate::types::same_type_with_budget(
            signature.domain(),
            function.parameter().ty(),
            budget,
        )
        .map_err(|()| resource())?
            || !crate::types::same_type_with_budget(signature.value(), &request_node.ty, budget)
                .map_err(|()| resource())?
            || !crate::types::same_effect_rows_with_budget(effects, &request_node.effects, budget)
                .map_err(|()| resource())?
        {
            return Err(invalid());
        }
    }
    Ok(())
}

impl ProviderScopeNode {
    /// Reconstructs the typed instance relation from the original definition.
    /// The copied-code certificate is authenticated independently afterwards.
    pub(crate) fn authenticate_structure(
        &self,
        program: &crate::core::UnvalidatedEffectProgram,
        id: NodeId,
        budget: &mut crate::types::TypeWorkBudget,
    ) -> Result<(), crate::core::ValidationError> {
        use crate::types::{
            IterativeTypeOwner, Kind, clone_type_with_budget, same_type_with_budget,
        };
        let definition = self.descriptor.definition();
        let admitted = self.descriptor.admitted_arc().ok_or_else(invalid)?;
        if self.attached.is_empty() {
            if !self.family_clause_index.is_empty() {
                return Err(invalid());
            }
        } else {
            budget
                .charge(
                    self.member_count()
                        .checked_add(self.family_clause_index.len())
                        .ok_or_else(resource)?,
                )
                .map_err(|()| resource())?;
            let mut flat = 0usize;
            for member in 0..self.member_count() {
                let handler = self.handler_member(member).ok_or_else(invalid)?;
                if handler.body() != self.handler.body() {
                    return Err(invalid());
                }
                for clause in 0..handler.clauses().len() {
                    if self.family_clause_index.get(flat) != Some(&(member, clause)) {
                        return Err(invalid());
                    }
                    flat = flat.checked_add(1).ok_or_else(resource)?;
                }
            }
            if flat != self.family_clause_index.len() {
                return Err(invalid());
            }
        }
        budget
            .charge(program.registry.provider_contract_count())
            .map_err(|()| resource())?;
        let mut original_definition = false;
        for (_, certificate) in program.registry.provider_contracts() {
            budget
                .charge(certificate.resource_count())
                .map_err(|()| resource())?;
            if certificate
                .resource_contracts()
                .any(|(_, _, fact)| Arc::ptr_eq(fact, &admitted.definition))
            {
                original_definition = true;
                break;
            }
        }
        budget
            .charge(program.registry.foreign_modules().count())
            .map_err(|()| resource())?;
        if !original_definition
            || !program
                .registry
                .foreign_modules()
                .any(|native| Arc::ptr_eq(native, &admitted.native))
        {
            return Err(invalid());
        }
        let arguments = self.descriptor.arguments();
        budget
            .charge(
                arguments
                    .len()
                    .checked_mul(2)
                    .and_then(|n| n.checked_add(1))
                    .ok_or_else(resource)?,
            )
            .map_err(|()| resource())?;
        if arguments.len() != definition.parameters.len()
            || !matches!(arguments.first(), Some(KindedArgument::TypeArg(Type::Variable(identity))) if *identity == self.descriptor.identity())
            || definition
                .parameters
                .first()
                .is_none_or(|parameter| parameter.kind != Kind::Type)
            || self.handler.hook_root().is_some()
            || self.handler.hook_registration.is_some()
        {
            return Err(invalid());
        }
        let mut substitutions = ScopeSubstitutions {
            types: std::collections::HashMap::new(),
            rows: std::collections::HashMap::new(),
        };
        let rows = arguments
            .iter()
            .filter(|arg| matches!(arg, KindedArgument::RowArg(_)))
            .count();
        substitutions
            .types
            .try_reserve(arguments.len() - rows + 1)
            .map_err(|_| resource())?;
        substitutions
            .rows
            .try_reserve(rows)
            .map_err(|_| resource())?;
        for (parameter, argument) in definition.parameters.iter().zip(arguments) {
            let unique = match (&parameter.kind, argument) {
                (Kind::EffectRow, KindedArgument::RowArg(row)) => substitutions.insert_row(
                    parameter.id,
                    crate::types::clone_effect_row_with_budget(row, budget)
                        .map_err(|()| resource())?,
                ),
                (Kind::EffectRow, _) | (_, KindedArgument::RowArg(_)) => return Err(invalid()),
                (_, KindedArgument::TypeArg(ty)) => substitutions.insert_type(
                    parameter.id,
                    clone_type_with_budget(ty, budget).map_err(|()| resource())?,
                ),
            };
            if !unique {
                return Err(invalid());
            }
        }
        let node = |root: NodeId| -> Result<_, crate::core::ValidationError> {
            if root.arena() != program.arena {
                return Err(invalid());
            }
            program
                .nodes
                .get(root.index().map_err(|_| invalid())?)
                .ok_or_else(invalid)
        };
        let provided = substitutions.instantiate_effect(&definition.provided.instance, budget)?;
        let interpreted =
            substitutions.instantiate_effect(&definition.interpreted.instance, budget)?;
        if crate::types::compare_effect_instances_with_budget(
            &provided,
            self.handler.effect(),
            budget,
        )
        .map_err(|()| resource())?
            != std::cmp::Ordering::Equal
            || crate::types::compare_effect_instances_with_budget(
                &interpreted,
                self.descriptor.native_effect(),
                budget,
            )
            .map_err(|()| resource())?
                != std::cmp::Ordering::Equal
        {
            return Err(invalid());
        }
        let catalog = &program.method_evidence;
        budget
            .charge(
                catalog
                    .methods()
                    .len()
                    .checked_add(self.forwardings.len())
                    .ok_or_else(resource)?,
            )
            .map_err(|()| resource())?;
        let interface = definition.provider_application.interface();
        let expected = catalog
            .methods()
            .iter()
            .filter(|method| method.id.interface() == interface)
            .count();
        if self.forwardings.len() != expected {
            return Err(invalid());
        }
        let mut covered = Vec::new();
        budget.charge(expected).map_err(|()| resource())?;
        covered
            .try_reserve_exact(expected)
            .map_err(|_| resource())?;
        covered.resize(expected, false);
        for forwarding in &self.forwardings {
            if forwarding.method.interface() != interface {
                return Err(invalid());
            }
            let ordinal =
                usize::try_from(forwarding.method.declaration()).map_err(|_| invalid())?;
            let Some(slot) = covered.get_mut(ordinal) else {
                return Err(invalid());
            };
            if std::mem::replace(slot, true) {
                return Err(invalid());
            }
            budget
                .charge(catalog.lexical_owners().len())
                .map_err(|()| resource())?;
            let owner = catalog
                .lexical_owner(self.lexical, forwarding.method)
                .ok_or_else(invalid)?;
            if owner.binder != forwarding.binder {
                return Err(invalid());
            }
        }
        let input = substitutions.instantiate(&definition.input.ty, budget)?;
        let state = substitutions.instantiate(&definition.state.ty, budget)?;
        self.authenticate_retained(&node(self.initializer)?.ty, &state, budget)?;
        for actual in [&node(self.initializer)?.ty, self.acquire.parameter.ty()] {
            if !same_type_with_budget(&input, actual, budget).map_err(|()| resource())? {
                return Err(invalid());
            }
        }
        for actual in [self.finish.parameter.ty(), self.handler_state.ty()] {
            if !same_type_with_budget(&state, actual, budget).map_err(|()| resource())? {
                return Err(invalid());
            }
        }
        if self.attached.len() != admitted.families.len() {
            return Err(invalid());
        }
        if !self.attached.is_empty() {
            let original = definition.family_template.as_ref().ok_or_else(invalid)?;
            budget
                .charge(self.attached.len())
                .map_err(|()| resource())?;
            for (index, (attached, member)) in
                self.attached.iter().zip(&admitted.families).enumerate()
            {
                if member.identity.definition != definition.id
                    || member.identity.parameter != original.parameter.id
                    || attached.lexical != member.lexical
                    || attached.lexical == self.lexical
                    || attached.handler.hook_root().is_some()
                    || attached.handler.hook_registration.is_some()
                    || attached.handler.id() == self.handler.id()
                    || attached.state.id() == self.handler_state.id()
                    || !matches!(member.payload, Type::Unit | Type::Bool | Type::Int)
                    || !same_type_with_budget(attached.state.ty(), &state, budget)
                        .map_err(|()| resource())?
                {
                    return Err(invalid());
                }
                budget.charge(index).map_err(|()| resource())?;
                for previous in &self.attached[..index] {
                    if previous.handler.id() == attached.handler.id()
                        || previous.state.id() == attached.state.id()
                    {
                        return Err(invalid());
                    }
                }
                if !substitutions.insert_type(
                    original.parameter.id,
                    clone_type_with_budget(&member.payload, budget).map_err(|()| resource())?,
                ) {
                    return Err(invalid());
                }
                let selected_provided =
                    substitutions.instantiate_effect(&original.provided.instance, budget)?;
                let selected_native =
                    substitutions.instantiate_effect(&original.interpreted.instance, budget)?;
                if crate::types::compare_effect_instances_with_budget(
                    &selected_provided,
                    attached.handler.effect(),
                    budget,
                )
                .map_err(|()| resource())?
                    != std::cmp::Ordering::Equal
                    || crate::types::compare_effect_instances_with_budget(
                        &selected_native,
                        &member.native_effect,
                        budget,
                    )
                    .map_err(|()| resource())?
                        != std::cmp::Ordering::Equal
                    || member.application.interface() != original.provider_application.interface()
                    || member.application.arguments().len()
                        != original.provider_application.arguments().len()
                {
                    return Err(invalid());
                }
                budget
                    .charge(member.application.arguments().len())
                    .map_err(|()| resource())?;
                for (written, actual) in original
                    .provider_application
                    .arguments()
                    .iter()
                    .zip(member.application.arguments())
                {
                    let expected = crate::types::substitute_kinded_argument_with(
                        written,
                        &substitutions.types,
                        &substitutions.rows,
                        |units| budget.charge(units),
                    )
                    .map_err(|()| resource())?
                    .map_err(|_| invalid())?;
                    let expected = crate::types::IterativeArgumentOwner::new(expected);
                    if !crate::types::same_kinded_argument_with_budget(&expected, actual, budget)
                        .map_err(|()| resource())?
                    {
                        return Err(invalid());
                    }
                }
                if let Some(payload) = substitutions.types.remove(&original.parameter.id) {
                    crate::types::discard_type_iteratively(payload);
                }
                let interface = member.application.interface();
                budget
                    .charge(
                        catalog
                            .methods()
                            .len()
                            .checked_add(attached.forwardings.len())
                            .ok_or_else(resource)?,
                    )
                    .map_err(|()| resource())?;
                let expected = catalog
                    .methods()
                    .iter()
                    .filter(|method| method.id.interface() == interface)
                    .count();
                if attached.forwardings.len() != expected {
                    return Err(invalid());
                }
                for (ordinal, forwarding) in attached.forwardings.iter().enumerate() {
                    if forwarding.method.interface() != interface
                        || usize::try_from(forwarding.method.declaration())
                            .map_err(|_| invalid())?
                            != ordinal
                        || !matches!(forwarding.binder, crate::resolved::BinderId::Generated(_))
                    {
                        return Err(invalid());
                    }
                    budget.charge(ordinal).map_err(|()| resource())?;
                    if attached.forwardings[..ordinal]
                        .iter()
                        .any(|other| other.binder == forwarding.binder)
                    {
                        return Err(invalid());
                    }
                }
                authenticate_family_forwardings(program, &admitted.definition, attached, budget)?;
            }
        }
        // A handle is a family instance, never the owned native state.
        budget
            .charge(arguments.len().checked_add(1).ok_or_else(resource)?)
            .map_err(|()| resource())?;
        let handle = if arguments
            .iter()
            .any(|argument| matches!(argument, KindedArgument::RowArg(_)))
        {
            Type::ResourceApply(
                definition.id,
                crate::types::clone_kinded_arguments_with_budget(arguments.iter(), budget)
                    .map_err(|()| resource())?,
            )
        } else {
            let mut types = Vec::new();
            budget
                .charge(
                    arguments
                        .len()
                        .checked_mul(4)
                        .and_then(|n| n.checked_add(1))
                        .ok_or_else(resource)?,
                )
                .map_err(|()| resource())?;
            types
                .try_reserve_exact(arguments.len())
                .map_err(|_| resource())?;
            for argument in arguments {
                let KindedArgument::TypeArg(ty) = argument else {
                    return Err(invalid());
                };
                types.push(IterativeTypeOwner::new(
                    clone_type_with_budget(ty, budget).map_err(|()| resource())?,
                ));
            }
            let mut retained = Vec::new();
            retained
                .try_reserve_exact(types.len())
                .map_err(|_| resource())?;
            retained.extend(types.into_iter().map(IterativeTypeOwner::into_inner));
            Type::apply_arguments(Type::Nominal(definition.family), retained)
        };
        let handle = IterativeTypeOwner::new(handle);
        if !same_type_with_budget(&handle, self.handle.ty(), budget).map_err(|()| resource())? {
            return Err(invalid());
        }
        budget.charge(1).map_err(|()| resource())?;
        let answer = clone_type_with_budget(&node(self.handler.body())?.ty, budget)
            .map_err(|()| resource())?;
        if !substitutions.insert_type(definition.answer.id, answer) {
            return Err(invalid());
        }
        let result = substitutions.instantiate(&definition.result.ty, budget)?;
        if !same_type_with_budget(&result, &node(id)?.ty, budget).map_err(|()| resource())?
            || !same_type_with_budget(
                self.handler_output.value(),
                &node(self.handler.body())?.ty,
                budget,
            )
            .map_err(|()| resource())?
        {
            return Err(invalid());
        }
        Ok(())
    }
}

impl ProviderScopeNode {
    /// Retained owners come from the original acquisition coordinates and the
    /// typed initializer, never from ordinary free source arguments alone.
    fn authenticate_retained(
        &self,
        initializer: &Type,
        state: &Type,
        budget: &mut crate::types::TypeWorkBudget,
    ) -> Result<(), crate::core::ValidationError> {
        use crate::{
            foreign::ForeignResultFact,
            types::{EffectRowVariable, TypeStructureNode},
        };
        let native = self.descriptor.native();
        let effect = self.descriptor.native_effect();
        let identity = self.descriptor.identity();
        let family = state.outer_nominal().ok_or_else(invalid)?;
        budget
            .charge(native.states.len())
            .map_err(|()| resource())?;
        let fact = native
            .states
            .iter()
            .find(|fact| fact.id == family)
            .ok_or_else(invalid)?;
        let (_, arguments) = nominal_arguments(state, fact.parameter_count, budget)?;
        if !matches!(arguments.get(fact.owned_identity_position), Some(Type::Variable(actual)) if *actual == identity)
        {
            return Err(invalid());
        }
        let width = effect.arguments().len();
        budget.charge(width).map_err(|()| resource())?;
        let mut positions = Vec::new();
        positions.try_reserve_exact(width).map_err(|_| resource())?;
        positions.resize(width, false);
        budget
            .charge(native.operations.len())
            .map_err(|()| resource())?;
        let mut acquired = false;
        for operation in &native.operations {
            if operation.id.owner() != effect.effect() {
                continue;
            }
            let ForeignResultFact::Acquire {
                state,
                retained_parameters,
                ..
            } = &operation.result
            else {
                continue;
            };
            if *state != family {
                continue;
            }
            if !matches!(effect.arguments().get(operation.owned_identity_position), Some(KindedArgument::TypeArg(Type::Variable(actual))) if *actual == identity)
            {
                return Err(invalid());
            }
            acquired = true;
            budget
                .charge(retained_parameters.len())
                .map_err(|()| resource())?;
            for position in retained_parameters {
                *positions.get_mut(*position).ok_or_else(invalid)? = true;
            }
        }
        if !acquired {
            return Err(invalid());
        }
        budget.charge(width).map_err(|()| resource())?;
        let count = positions.iter().filter(|required| **required).count();
        budget
            .charge(count.checked_add(width).ok_or_else(resource)?)
            .map_err(|()| resource())?;
        let mut retained = Vec::new();
        retained.try_reserve_exact(count).map_err(|_| resource())?;
        for (position, required) in positions.into_iter().enumerate() {
            if !required {
                continue;
            }
            let Some(KindedArgument::TypeArg(Type::Variable(actual))) =
                effect.arguments().get(position)
            else {
                return Err(invalid());
            };
            if *actual == identity {
                return Err(invalid());
            }
            let supplied = crate::types::visit_type_structure_with_budget(initializer, budget, |node, _| {
                Ok(match node {
                    TypeStructureNode::Type(Type::Variable(found)) => found == actual,
                    TypeStructureNode::Tail(tail) => matches!(tail.variable(), EffectRowVariable::Rigid(found) if found == *actual),
                    _ => false,
                })
            }).map_err(|()| resource())?;
            if !supplied {
                return Err(invalid());
            }
            budget.charge(retained.len()).map_err(|()| resource())?;
            if !retained.contains(actual) {
                retained.push(*actual);
            }
        }
        budget.charge(retained.len()).map_err(|()| resource())?;
        if retained.as_slice() != self.descriptor.retained() {
            return Err(invalid());
        }
        Ok(())
    }
}

impl AdmittedProviderScope {
    pub(crate) fn relocate(
        &self,
        remapped: &[Option<NodeId>],
        budget: &mut crate::types::TypeWorkBudget,
    ) -> Result<Self, crate::core::BuildError> {
        budget
            .charge(
                self.retained
                    .len()
                    .checked_add(3)
                    .ok_or(crate::core::BuildError::TypeWorkExceeded)?,
            )
            .map_err(|()| crate::core::BuildError::TypeWorkExceeded)?;
        let mut retained = Vec::new();
        retained
            .try_reserve_exact(self.retained.len())
            .map_err(|_| crate::core::BuildError::TypeWorkExceeded)?;
        retained.extend_from_slice(&self.retained);
        let native_effect =
            crate::types::clone_effect_instance_with_budget(&self.native_effect, budget)
                .map_err(|()| crate::core::BuildError::TypeWorkExceeded)?;
        let specialization = self.specialization.relocate(remapped, budget)?;
        budget
            .charge(self.families.len())
            .map_err(|()| crate::core::BuildError::TypeWorkExceeded)?;
        let mut families = Vec::new();
        families
            .try_reserve_exact(self.families.len())
            .map_err(|_| crate::core::BuildError::TypeWorkExceeded)?;
        for family in &self.families {
            families.push(family.clone_with_budget(budget)?);
        }
        Ok(Self {
            definition: Arc::clone(&self.definition),
            native: Arc::clone(&self.native),
            arguments: crate::types::clone_kinded_arguments_with_budget(
                self.arguments.iter(),
                budget,
            )
            .map_err(|()| crate::core::BuildError::TypeWorkExceeded)?,
            identity: self.identity,
            retained: retained.into_boxed_slice(),
            native_effect,
            protocol: self.protocol,
            specialization,
            families: families.into_boxed_slice(),
        })
    }
}

impl ProviderScopeNode {
    /// Authenticates constructor codecs by identities and payload structure.
    /// Spellings never select native operations or confer lifecycle authority.
    pub(crate) fn authenticate_protocol(
        &self,
        program: &crate::core::UnvalidatedEffectProgram,
        id: NodeId,
        budget: &mut crate::types::TypeWorkBudget,
    ) -> Result<(), crate::core::ValidationError> {
        use crate::{
            foreign::ForeignResultFact,
            resolved::{ResolvedNominalDeclarationKind, ResolvedRegistry, ResolvedTypeVariable},
            types::{Kind, same_type_with_budget},
        };
        fn parameters<'a>(
            registry: &'a ResolvedRegistry,
            ids: &[ConstructorId],
            count: usize,
            budget: &mut crate::types::TypeWorkBudget,
        ) -> Result<&'a [ResolvedTypeVariable], crate::core::ValidationError> {
            budget
                .charge(
                    ids.len()
                        .checked_add(count)
                        .and_then(|n| n.checked_add(2))
                        .ok_or_else(resource)?,
                )
                .map_err(|()| resource())?;
            let family = ids.first().ok_or_else(invalid)?.owner();
            let nominal = registry.nominal(family).ok_or_else(invalid)?;
            let parameters = registry.nominal_parameters(family).ok_or_else(invalid)?;
            if nominal.declaration_kind != ResolvedNominalDeclarationKind::Data
                || nominal.constructors.as_ref() != ids
                || parameters.len() != count
                || parameters
                    .iter()
                    .any(|parameter| parameter.kind != Kind::Type)
            {
                return Err(invalid());
            }
            for (ordinal, constructor) in ids.iter().enumerate() {
                let declaration = registry.constructor(*constructor).ok_or_else(invalid)?;
                if constructor.owner() != family
                    || usize::try_from(constructor.constructor()).ok() != Some(ordinal)
                    || declaration.id != *constructor
                    || declaration.owner != family
                {
                    return Err(invalid());
                }
            }
            Ok(parameters)
        }
        fn payload(
            registry: &ResolvedRegistry,
            id: ConstructorId,
        ) -> Result<Option<&Type>, crate::core::ValidationError> {
            Ok(registry
                .constructor(id)
                .ok_or_else(invalid)?
                .payload
                .as_ref())
        }
        fn variable(ty: Option<&Type>, id: TypeVariableId) -> bool {
            matches!(ty, Some(Type::Variable(actual)) if *actual == id)
        }
        let registry = &program.registry;
        let protocol = self.descriptor.protocol();
        let scope_parameters = parameters(registry, &protocol.scope, 3, budget)?;
        let completion_parameters = parameters(registry, &protocol.completion, 1, budget)?;
        let acquire_parameters = parameters(registry, &protocol.acquire, 2, budget)?;
        let finish_parameters = parameters(registry, &protocol.finish, 2, budget)?;
        if !variable(
            payload(registry, protocol.scope[0])?,
            scope_parameters[0].id,
        ) || payload(registry, protocol.completion[0])?.is_some()
            || !variable(
                payload(registry, protocol.completion[1])?,
                completion_parameters[0].id,
            )
            || !variable(
                payload(registry, protocol.completion[2])?,
                completion_parameters[0].id,
            )
            || !variable(
                payload(registry, protocol.acquire[0])?,
                acquire_parameters[0].id,
            )
            || !variable(
                payload(registry, protocol.acquire[1])?,
                acquire_parameters[1].id,
            )
            || payload(registry, protocol.finish[0])?.is_some()
            || !variable(
                payload(registry, protocol.finish[1])?,
                finish_parameters[1].id,
            )
        {
            return Err(invalid());
        }
        let Some(Type::Tuple(completed)) = payload(registry, protocol.scope[1])? else {
            return Err(invalid());
        };
        let [answer, completion] = completed.as_ref() else {
            return Err(invalid());
        };
        let (completion, errors) = nominal_arguments(completion, 1, budget)?;
        if !variable(Some(answer), scope_parameters[2].id)
            || completion != protocol.completion[0].owner()
            || !matches!(errors.as_slice(), [Type::Variable(error)] if *error == scope_parameters[1].id)
        {
            return Err(invalid());
        }
        let Some(Type::Tuple(retained)) = payload(registry, protocol.finish[2])? else {
            return Err(invalid());
        };
        if !matches!(retained.as_ref(), [Type::Variable(state), Type::Variable(error)] if *state == finish_parameters[0].id && *error == finish_parameters[1].id)
        {
            return Err(invalid());
        }
        let node = |root: NodeId| -> Result<_, crate::core::ValidationError> {
            if root.arena() != program.arena {
                return Err(invalid());
            }
            program
                .nodes
                .get(root.index().map_err(|_| invalid())?)
                .ok_or_else(invalid)
        };
        let (scope, scope_arguments) = nominal_arguments(&node(id)?.ty, 3, budget)?;
        let [init_error, completion_error, _answer] = scope_arguments.as_slice() else {
            return Err(invalid());
        };
        if scope != protocol.scope[0].owner() {
            return Err(invalid());
        }
        for (root, constructors, error) in [
            (self.acquire.body, protocol.acquire.as_slice(), init_error),
            (
                self.finish.body,
                protocol.finish.as_slice(),
                completion_error,
            ),
        ] {
            let (report, arguments) = nominal_arguments(&node(root)?.ty, 2, budget)?;
            let [state, actual_error] = arguments.as_slice() else {
                return Err(invalid());
            };
            if report != constructors[0].owner()
                || !same_type_with_budget(state, self.finish.parameter.ty(), budget)
                    .map_err(|()| resource())?
                || !same_type_with_budget(actual_error, error, budget).map_err(|()| resource())?
            {
                return Err(invalid());
            }
        }
        let state_family = self
            .finish
            .parameter
            .ty()
            .outer_nominal()
            .ok_or_else(invalid)?;
        // Report codecs must also be original admitted facts of the interpreted
        // foreign effect. A matching user-authored family alone is insufficient.
        let mut acquire = false;
        let mut finish = false;
        budget
            .charge(self.descriptor.native().operations.len())
            .map_err(|()| resource())?;
        for operation in &self.descriptor.native().operations {
            if operation.id.owner() != self.descriptor.native_effect().effect() {
                continue;
            }
            match &operation.result {
                ForeignResultFact::Acquire {
                    state,
                    report,
                    constructors,
                    ..
                } if *state == state_family => {
                    if *report != protocol.acquire[0].owner()
                        || constructors.as_slice() != protocol.acquire
                    {
                        return Err(invalid());
                    }
                    acquire = true;
                }
                ForeignResultFact::Finish {
                    state,
                    report,
                    constructors,
                    ..
                } if *state == state_family => {
                    if *report != protocol.finish[0].owner()
                        || constructors.as_slice() != protocol.finish
                    {
                        return Err(invalid());
                    }
                    finish = true;
                }
                _ => {}
            }
        }
        if !acquire || !finish {
            return Err(invalid());
        }
        Ok(())
    }
}

/// Interprets an admitted native phase only when its exact request is present
/// in the known row. An unknown tail is preserved with its original lacks.
pub(crate) fn interpret_native_phase_row(
    row: &crate::types::EffectRow,
    native: &EffectInstance,
    budget: &mut crate::types::TypeWorkBudget,
) -> Result<crate::types::EffectRow, crate::core::ValidationError> {
    super::charge(budget, row.known().len())?;
    let mut found = false;
    for known in row.known() {
        if known.effect() != native.effect() || known.arguments().len() != native.arguments().len()
        {
            continue;
        }
        let mut equal = true;
        for (left, right) in known.arguments().iter().zip(native.arguments()) {
            if !crate::types::same_kinded_argument_with_budget(left, right, budget)
                .map_err(|()| super::resource())?
            {
                equal = false;
                break;
            }
        }
        if equal {
            found = true;
            break;
        }
    }
    if !found {
        return crate::types::clone_effect_row_with_budget(row, budget)
            .map_err(|()| super::resource());
    }
    row.remove_exact_with_budget(native, budget)
        .map_err(|()| super::resource())?
        .map_err(|_| {
            crate::core::ValidationError::new(crate::core::ValidationReason::EffectRow, None)
        })
}

#[cfg(test)]
mod tests {
    use super::interpret_native_phase_row;
    use crate::{
        module::ModuleId,
        types::{
            EffectId, EffectInstance, EffectRow, EffectRowError, EffectRowVariable, TypeVariableId,
            TypeWorkBudget,
        },
    };

    #[test]
    fn phase_interpretation_preserves_formal_callback_delta_without_native_exclusion() {
        let module = ModuleId::new(0);
        let provided = EffectInstance::new_kinded(EffectId::new(module, 0), Box::new([]));
        let native = EffectInstance::new_kinded(EffectId::new(module, 1), Box::new([]));
        let delta = EffectRow::open(
            EffectRowVariable::rigid(TypeVariableId::new(10)),
            Box::new([provided.clone()]),
        );
        let omega = EffectRow::with_tail(
            Box::new([provided]),
            delta.tail().unwrap().variable(),
            delta.tail().unwrap().lacks().into(),
        );
        let acquire = EffectRow::singleton(native.clone());
        let mut work = TypeWorkBudget::unbounded();
        assert!(matches!(
            acquire.union_with_budget(&omega, &mut work).unwrap(),
            Err(EffectRowError::Ambiguous)
        ));
        let acquire = interpret_native_phase_row(&acquire, &native, &mut work).unwrap();
        let omega_after = interpret_native_phase_row(&omega, &native, &mut work).unwrap();
        assert_eq!(omega_after, omega);
        assert_eq!(
            acquire
                .union_with_budget(&omega_after, &mut work)
                .unwrap()
                .unwrap(),
            omega
        );
        assert_eq!(omega.tail().unwrap().lacks().len(), 1);
    }
}
