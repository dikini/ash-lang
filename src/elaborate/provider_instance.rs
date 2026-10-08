//! Typed initializer preparation shared by every library-defined scope.

use super::provider::contract_validation_failure;
use super::{
    ActiveEvidenceBinder, CheckKind, CoreElaborator, CoreLoweringFamily, ElaborationFailure,
    ElaborationPurpose, ElaborationTask, ElaborationTaskBuffer, OwnedArgumentBuffer,
    OwnedTypeBuffer, OwnerReplacementBuffer, TypeContext, TypeError, TypeReason, TypedNode,
    TypedNodeBuffer, TypedNodeOwner, UnificationFailure, check_mismatch, constraint_resource,
    effect_row_failure, inference_failure, invalid_state, provider, resolved_build_error,
    row_exclusion_error, selection_failure, type_contains_variable, type_resource,
    unsupported_provider_resource,
};
use crate::resolved::{ResolvedProviderResourceExpr, ResourceTypeFact};
use crate::types::{KindedArgument, OperationId, TypeStructureNode};
use crate::{
    core::{EffectOperation, NodeId, RequestNode, TypedBinder},
    evidence::EvidenceSelector,
    interface::{InterfaceApplication, MethodId},
    resolved::BinderId,
    source::{Origin, Span},
    types::{
        ComputationType, EffectInstance, EffectRow, EffectRowVariable, IterativeTypeOwner, Kind,
        Type, TypeVariableId, TypeWorkBudget, discard_type_iteratively,
    },
};
use std::primitive::usize;
use std::{ops::Deref, sync::Arc};
mod copy;
pub(crate) mod final_preparation;
pub(super) use copy::{
    PreparedScopeCopyPlan, lower_final_scope_copies, lower_prepared_scope_copies, lower_family_scope_copies,
};
pub(crate) use final_preparation::FinalProviderPreparation;

/// Compiler preparation retained by an admitted source occurrence. This is
/// neither executable Core permission nor native ownership. Its original code
/// is borrowed during specialization and is absent from executable descriptors.
pub(crate) struct PreparedProviderInstance {
    pub(super) definition: Arc<ResourceTypeFact>,
    pub(super) code: super::provider::PreparedProviderCode,
    pub(super) actuals: ResourceActuals,
    pub(super) handler_rows: crate::core::provider::ResolvedProviderHandlerRows,
    pub(super) body: ProviderComputationOwner,
    pub(super) forwarding: ProviderForwardings,
    pub(super) provider: crate::interface::LexicalEvidenceId,
    pub(super) family_members: Box<[Arc<PreparedProviderFamilyInstance>]>,
    pub(super) family_rows: Box<[crate::core::provider::ResolvedProviderHandlerRows]>,
}
impl PreparedProviderInstance {
    pub(crate) fn family_members(&self) -> &[Arc<PreparedProviderFamilyInstance>] { &self.family_members }
    pub(crate) fn definition(&self) -> &ResourceTypeFact {
        &self.definition
    }
    pub(crate) fn access_type(&self, work: &mut TypeWorkBudget) -> Result<Type, TypeError> {
        self.actuals.access_type(&self.definition, work)
    }
    pub(crate) fn arguments(&self) -> &[KindedArgument] {
        self.actuals.arguments()
    }
    pub(crate) fn provider(&self) -> crate::interface::LexicalEvidenceId {
        self.provider
    }
    pub(crate) fn forwarding_application(&self) -> &InterfaceApplication {
        &self.forwarding.application
    }
    pub(crate) fn forwarding_methods(&self) -> impl Iterator<Item = (MethodId, BinderId, &Type)> {
        self.forwarding
            .methods
            .iter()
            .map(|method| (method.method, method.binder, &*method.ty))
    }
}

/// One frozen exact demand, with nonowning generated forwarding functions.
/// Member indices locate these claims; the original certificate authenticates them.
pub(crate) struct PreparedProviderFamilyInstance {
    source: crate::interface::LexicalEvidenceId,
    identity: crate::core::provider::ProviderFamilyIdentity,
    application: InterfaceApplication,
    requirements: Box<[(crate::interface::EvidenceSelection, crate::interface::EvidenceNodeId)]>,
    selections: Vec<(crate::interface::EvidenceSelection, crate::interface::EvidenceNodeId)>,
    pub(super) payload: IterativeTypeOwner,
    provided: EffectInstance,
    native: EffectInstance,
    forwardings: Box<[(MethodId, OperationId, TypedBinder)]>,
}
impl PreparedProviderFamilyInstance {
    pub(crate) fn source(&self) -> crate::interface::LexicalEvidenceId { self.source }
    pub(crate) fn identity(&self) -> crate::core::provider::ProviderFamilyIdentity { self.identity }
    pub(crate) fn application(&self) -> &InterfaceApplication { &self.application }
    pub(crate) fn requirements(&self) -> &[(crate::interface::EvidenceSelection, crate::interface::EvidenceNodeId)] { &self.requirements }
    pub(crate) fn selections(&self) -> &[(crate::interface::EvidenceSelection, crate::interface::EvidenceNodeId)] { &self.selections }
    pub(crate) fn forwarding_methods(&self) -> impl Iterator<Item=(MethodId, BinderId, &Type)> {
        self.forwardings.iter().map(|(method, _, binder)| (*method, binder.id(), binder.ty()))
    }
}

struct ProviderFamilyArguments(Vec<KindedArgument>);
impl Drop for ProviderFamilyArguments {
    fn drop(&mut self) { for argument in self.0.drain(..) { crate::types::discard_kinded_argument_iteratively(argument); } }
}

pub(super) struct ProviderFamilyDemandScope {
    source: crate::interface::LexicalEvidenceId,
    primary_source: crate::interface::LexicalEvidenceId,
    original: Arc<ResourceTypeFact>,
    authority: Arc<provider::ProviderFamilyOriginalAuthority>,
    certificate: Option<Arc<provider::CheckedProviderContracts>>,
    arguments: ProviderFamilyArguments,
    identity: crate::core::provider::ProviderFamilyIdentity,
    application: InterfaceApplication,
    requirements: Box<[crate::interface::CheckedRequirement]>,
    provided: EffectInstance,
    native: EffectInstance,
    methods: Box<[(MethodId, OperationId)]>,
    members: Vec<Arc<PreparedProviderFamilyInstance>>,
    frozen: bool,
    origin: Origin,
}

/// Resolves an existing forwarding binder without selecting or materializing
/// evidence. Scope/member indices locate claims; original certificates and the
/// exact immutable prerequisite plan authenticate them.
pub(super) fn capture_family_forwarding(
    scopes: &[ProviderFamilyDemandScope],
    registry: &crate::resolved::ResolvedRegistry,
    selection: &crate::interface::EvidenceSelection,
    node: crate::interface::EvidenceNodeId,
    method: MethodId,
    work: &mut TypeWorkBudget,
) -> Result<BinderId, crate::core::capture::Failure> {
    authenticate_family_forwarding(scopes, registry, selection, node, method, true, work)
}

/// Only unfrozen materialization may authenticate a new occurrence receipt.
/// Capture and frozen synthesis always require the retained exact receipt.
fn authenticate_family_forwarding(
    scopes: &[ProviderFamilyDemandScope],
    registry: &crate::resolved::ResolvedRegistry,
    selection: &crate::interface::EvidenceSelection,
    node: crate::interface::EvidenceNodeId,
    method: MethodId,
    require_recorded: bool,
    work: &mut TypeWorkBudget,
) -> Result<BinderId, crate::core::capture::Failure> {
    use crate::core::capture::Failure;
    use crate::interface::{EvidenceNode, RequirementOwner};
    use crate::resolved::ResolvedBuildFailure;

    fn lowering_failure(failure: TypeError) -> Failure {
        match failure {
            TypeError::Internal(ElaborationFailure::TypeResourceExhausted
                | ElaborationFailure::ConstraintResourceExhausted) => Failure::Resource,
            _ => Failure::Invalid,
        }
    }
    fn resolved_failure(failure: ResolvedBuildFailure) -> Failure {
        match failure {
            ResolvedBuildFailure::TypeResource => Failure::Resource,
            _ => Failure::Invalid,
        }
    }
    fn same_arguments(
        left: &[KindedArgument], right: &[KindedArgument], work: &mut TypeWorkBudget,
    ) -> Result<bool, Failure> {
        work.charge(left.len()).map_err(|()| Failure::Resource)?;
        if left.len() != right.len() { return Ok(false); }
        for (left, right) in left.iter().zip(right) {
            if !crate::types::same_kinded_argument_with_budget(left, right, work)
                .map_err(|()| Failure::Resource)? { return Ok(false); }
        }
        Ok(true)
    }
    fn same_application(
        left: &InterfaceApplication, right: &InterfaceApplication, work: &mut TypeWorkBudget,
    ) -> Result<bool, Failure> {
        Ok(left.interface() == right.interface()
            && same_arguments(left.arguments(), right.arguments(), work)?)
    }
    fn apply_arguments(
        arguments: &[KindedArgument], replacements: &OwnerReplacementBuffer,
        work: &mut TypeWorkBudget,
    ) -> Result<ProviderFamilyArguments, Failure> {
        work.charge(arguments.len()).map_err(|()| Failure::Resource)?;
        let mut result = ProviderFamilyArguments(Vec::new());
        result.0.try_reserve_exact(arguments.len()).map_err(|_| Failure::Resource)?;
        for argument in arguments {
            result.0.push(crate::types::substitute_kinded_argument_with(argument,
                replacements.types.as_map(), &replacements.rows, |units| work.charge(units))
                .map_err(|()| Failure::Resource)?.map_err(|_| Failure::Invalid)?);
        }
        Ok(result)
    }
    fn apply_application(
        application: &InterfaceApplication, replacements: &OwnerReplacementBuffer,
        work: &mut TypeWorkBudget,
    ) -> Result<InterfaceApplication, Failure> {
        let mut arguments = apply_arguments(application.arguments(), replacements, work)?;
        Ok(InterfaceApplication::new_kinded(application.interface(),
            std::mem::take(&mut arguments.0).into_boxed_slice()))
    }
    fn apply_effect(
        effect: &EffectInstance, replacements: &OwnerReplacementBuffer,
        work: &mut TypeWorkBudget,
    ) -> Result<EffectInstance, Failure> {
        let mut arguments = apply_arguments(effect.arguments(), replacements, work)?;
        Ok(EffectInstance::new_kinded(effect.effect(),
            std::mem::take(&mut arguments.0).into_boxed_slice()))
    }
    fn same_effect(
        left: &EffectInstance, right: &EffectInstance, work: &mut TypeWorkBudget,
    ) -> Result<bool, Failure> {
        Ok(left.effect() == right.effect()
            && same_arguments(left.arguments(), right.arguments(), work)?)
    }

    let Some(EvidenceNode::ProviderFamily {
        source, definition, parameter, application, prerequisites, methods,
    }) = selection.node(node) else { return Err(Failure::Invalid); };
    work.charge(scopes.len()).map_err(|()| Failure::Resource)?;
    let mut candidates = scopes.iter().filter(|scope| scope.source == source);
    let scope = candidates.next().ok_or(Failure::Invalid)?;
    if candidates.next().is_some() || scope.primary_source == source
        || scope.primary_source.module() != source.module()
        || scope.identity.definition != definition || scope.identity.parameter != parameter
        || scope.original.id != definition || scope.arguments.0.len() != scope.original.parameters.len() {
        return Err(Failure::Invalid);
    }
    work.charge(registry.provider_contract_count()).map_err(|()| Failure::Resource)?;
    let certificate = registry.provider_contracts()
        .find(|(module, _)| **module == definition.module())
        .map(|(_, certificate)| certificate);
    let authority = &scope.authority;
    if !Arc::ptr_eq(authority.fact(), &scope.original) || authority.identity() != scope.identity {
        return Err(Failure::Invalid);
    }
    let identity = authority.identity();
    let header = authority.application();
    let requirements = authority.requirements();
    let associations = authority.methods();
    let handler = authority.handler_certificate();
    if let Some(certificate) = certificate {
        if certificate.module() != definition.module()
            || scope.certificate.as_ref().is_some_and(|original| !Arc::ptr_eq(original, certificate)) {
            return Err(Failure::Invalid);
        }
        work.charge(certificate.resource_count().checked_mul(7).ok_or(Failure::Resource)?)
            .map_err(|()| Failure::Resource)?;
        if !certificate.resource_contracts().any(|(_, _, original)| Arc::ptr_eq(original, &scope.original)) {
            return Err(Failure::Invalid);
        }
        if !Arc::ptr_eq(certificate.family_original_authority(definition).ok_or(Failure::Invalid)?, authority) {
            return Err(Failure::Invalid);
        }
        // This exact original carrier has a published registry certificate.
        // Authenticate its filled slots in the committed phase, including
        // imported and final-synthesis queries; do not probe the pending phase.
        authority.authenticate(true, work)
            .map_err(|failure| resolved_failure(contract_validation_failure(failure)))?;
        certificate.authenticate(true, work).map_err(resolved_failure)?;
        certificate.authenticate_linked_native_facts(registry, work).map_err(resolved_failure)?;
        if certificate.family_identity(definition) != Some(identity)
            || !same_application(certificate.family_provider_application(definition).ok_or(Failure::Invalid)?, header, work)? {
            return Err(Failure::Invalid);
        }
        let published_requirements = certificate.family_requirements(definition).ok_or(Failure::Invalid)?;
        let published_methods = certificate.family_methods(definition).ok_or(Failure::Invalid)?;
        work.charge(requirements.len().checked_add(associations.len()).ok_or(Failure::Resource)?)
            .map_err(|()| Failure::Resource)?;
        if published_requirements.len() != requirements.len() || published_methods != associations {
            return Err(Failure::Invalid);
        }
        for (published, original) in published_requirements.iter().zip(requirements) {
            if published.id != original.id || !same_application(published.application(), original.application(), work)? {
                return Err(Failure::Invalid);
            }
        }
        if !std::ptr::eq(certificate.family_handler_certificate(definition).ok_or(Failure::Invalid)?.canonical_registry(),
            handler.canonical_registry()) { return Err(Failure::Invalid); }
    } else if scope.certificate.is_some() {
        return Err(Failure::Invalid);
    } else {
        // Only a genuine local original without a published source contract
        // uses pending-slot authentication.
        authority.authenticate(false, work)
            .map_err(|failure| resolved_failure(contract_validation_failure(failure)))?;
    }
    // Private local originals use the same genuine handler authority before
    // group publication. Their registered native facts must still be original.
    for original in handler.canonical_registry().foreign_modules() {
        work.charge(1).map_err(|()| Failure::Resource)?;
        let mut found = false;
        for linked in registry.foreign_modules() {
            work.charge(1).map_err(|()| Failure::Resource)?;
            if linked.admission.module_id == original.admission.module_id {
                if !Arc::ptr_eq(linked, original) { return Err(Failure::Invalid); }
                found = true;
            }
        }
        if !found { return Err(Failure::Invalid); }
    }
    let original = scope.original.family_template.as_ref().ok_or(Failure::Invalid)?;
    if identity != scope.identity || original.parameter.id != parameter
        || original.parameter.kind != Kind::Type || requirements.len() != 1
        || prerequisites.len() != requirements.len() || scope.requirements.len() != requirements.len() {
        return Err(Failure::Invalid);
    }

    let mut replacements = OwnerReplacementBuffer::new();
    work.charge(scope.arguments.0.len()).map_err(|()| Failure::Resource)?;
    for (formal, actual) in scope.original.parameters.iter().zip(&scope.arguments.0) {
        if matches!(formal.kind, Kind::EffectRow) != matches!(actual, KindedArgument::RowArg(_)) {
            return Err(Failure::Invalid);
        }
        replacements.insert_cloned(formal.id, actual, work).map_err(lowering_failure)?;
    }
    if !same_application(&apply_application(header, &replacements, work)?, &scope.application, work)?
        || !same_effect(&apply_effect(&original.provided.instance, &replacements, work)?, &scope.provided, work)?
        || !same_effect(&apply_effect(&original.interpreted.instance, &replacements, work)?, &scope.native, work)? {
        return Err(Failure::Invalid);
    }
    work.charge(requirements.len()).map_err(|()| Failure::Resource)?;
    for (ordinal, (canonical, retained)) in requirements.iter().zip(&scope.requirements).enumerate() {
        if canonical.id.owner() != RequirementOwner::ResourceFamily(definition)
            || usize::try_from(canonical.id.declaration()).ok() != Some(ordinal)
            || canonical.id != retained.id
            || !same_application(&apply_application(canonical.application(), &replacements, work)?,
                retained.application(), work)? { return Err(Failure::Invalid); }
    }

    work.charge(scope.members.len()).map_err(|()| Failure::Resource)?;
    let mut selected = None;
    for member in &scope.members {
        if same_application(member.application(), application, work)? {
            if selected.replace(member.as_ref()).is_some() { return Err(Failure::Invalid); }
        }
    }
    let member = selected.ok_or(Failure::Invalid)?;
    if member.source != source || member.identity != identity
        || !matches!(&*member.payload, Type::Unit | Type::Bool | Type::Int)
        || member.requirements.len() != prerequisites.len() { return Err(Failure::Invalid); }
    work.charge(member.selections.len()).map_err(|()| Failure::Resource)?;
    let mut recorded = false;
    for (retained, retained_node) in &member.selections {
        if *retained_node == node && retained.root() == selection.root() && retained.shares_plan_with(selection) {
            if recorded { return Err(Failure::Invalid); }
            recorded = true;
        }
    }
    if require_recorded && !recorded { return Err(Failure::Invalid); }
    replacements.insert_borrowed(parameter, super::BorrowedOwnerArgument::TypeArg(&member.payload), work)
        .map_err(lowering_failure)?;
    if !same_application(&apply_application(header, &replacements, work)?, application, work)? {
        return Err(Failure::Invalid);
    }
    let provided = apply_effect(&original.provided.instance, &replacements, work)?;
    let native = apply_effect(&original.interpreted.instance, &replacements, work)?;
    if !same_effect(&provided, &member.provided, work)? || !same_effect(&native, &member.native, work)? {
        return Err(Failure::Invalid);
    }

    // Keep the whole selection owner: a family node may be a prerequisite of
    // an enclosing Implementation rather than the plan's root.
    work.charge(prerequisites.len()).map_err(|()| Failure::Resource)?;
    let (original_selection, original_node) = member.selections.first().ok_or(Failure::Invalid)?;
    let Some(EvidenceNode::ProviderFamily { prerequisites: original_prerequisites, .. }) = original_selection.node(*original_node)
        else { return Err(Failure::Invalid); };
    if original_prerequisites.len() != member.requirements.len() { return Err(Failure::Invalid); }
    for ((((retained, retained_node), actual), canonical), original_prerequisite) in member.requirements.iter()
        .zip(prerequisites).zip(requirements).zip(original_prerequisites) {
        if retained_node != original_prerequisite || retained_node.index() >= original_node.index()
            || actual.index() >= node.index() || retained.root() != original_selection.root()
            || !retained.shares_plan_with(original_selection) { return Err(Failure::Invalid); }
        let required = apply_application(canonical.application(), &replacements, work)?;
        let Some(EvidenceNode::NativeLayout { producer }) = selection.node(*actual) else {
            return Err(Failure::Invalid);
        };
        let Some(EvidenceNode::NativeLayout { producer: original_producer }) = retained.node(*retained_node) else {
            return Err(Failure::Invalid);
        };
        if producer != original_producer { return Err(Failure::Invalid); }
        let [KindedArgument::TypeArg(payload)] = required.arguments() else { return Err(Failure::Invalid); };
        let dictionary = registry.foreign_layout_dictionary(producer, work).map_err(resolved_failure)?;
        let (encoding, size, alignment) = match payload {
            Type::Unit => (crate::foreign::ForeignScalarEncoding::Unit, 0, 1),
            Type::Bool => (crate::foreign::ForeignScalarEncoding::Bool, 1, 1),
            Type::Int => (crate::foreign::ForeignScalarEncoding::Signed64, 8, 8),
            _ => return Err(Failure::Invalid),
        };
        if producer.interface() != required.interface() || producer.method().interface() != required.interface()
            || producer.method().declaration() != 0 || dictionary.producer() != producer
            || dictionary.payload_type() != payload || producer.payload_type() != *payload
            || dictionary.encoding() != encoding || dictionary.size() != size
            || dictionary.natural_alignment() != alignment { return Err(Failure::Invalid); }
    }

    work.charge(associations.len().checked_mul(3).ok_or(Failure::Resource)?)
        .map_err(|()| Failure::Resource)?;
    if methods.len() != associations.len() || scope.methods.as_ref() != associations
        || member.forwardings.len() != associations.len()
        || !methods.iter().copied().eq(associations.iter().map(|(method, _)| *method)) {
        return Err(Failure::Invalid);
    }
    let canonical = handler.canonical_registry();
    let declaration = canonical.effect(provided.effect()).ok_or(Failure::Invalid)?;
    canonical.authenticate_owner_signature(crate::resolved::OwnerId::Effect(declaration.id),
        None, &declaration.parameters, work).map_err(resolved_failure)?;
    if declaration.parameters.len() != provided.arguments().len() { return Err(Failure::Invalid); }
    let mut operation_replacements = OwnerReplacementBuffer::new();
    work.charge(declaration.parameters.len()).map_err(|()| Failure::Resource)?;
    for (formal, actual) in declaration.parameters.iter().zip(provided.arguments()) {
        operation_replacements.insert_cloned(formal.id, actual, work).map_err(lowering_failure)?;
    }
    let mut binders = std::collections::HashSet::new();
    binders.try_reserve(associations.len()).map_err(|_| Failure::Resource)?;
    let mut selected_binder = None;
    for ((canonical_method, canonical_operation), (actual_method, actual_operation, binder))
        in associations.iter().zip(&member.forwardings) {
        if canonical_method.interface() != application.interface() || canonical_operation.owner() != declaration.id
            || actual_method != canonical_method || actual_operation != canonical_operation
            || !matches!(binder.id(), BinderId::Generated(_)) || !binders.insert(binder.id())
            || binder.origin() != &scope.origin { return Err(Failure::Invalid); }
        let operation = declaration.operations.get(usize::try_from(canonical_operation.operation()).map_err(|_| Failure::Invalid)?)
            .filter(|operation| operation.id == *canonical_operation).ok_or(Failure::Invalid)?;
        let signature = IterativeTypeOwner::new(operation_replacements.substitute(&operation.annotation.ty, work)
            .map_err(lowering_failure)?);
        let function = signature.function_view().ok_or(Failure::Invalid)?;
        let domain = IterativeTypeOwner::new(crate::types::clone_type_with_budget(function.domain(), work)
            .map_err(|()| Failure::Resource)?);
        let result = IterativeTypeOwner::new(crate::types::clone_type_with_budget(function.value(), work)
            .map_err(|()| Failure::Resource)?);
        let effect = crate::types::clone_effect_instance_with_budget(&provided, work).map_err(|()| Failure::Resource)?;
        work.charge(3).map_err(|()| Failure::Resource)?;
        let expected = IterativeTypeOwner::new(Type::function_computation(domain.into_inner(),
            ComputationType::new(result.into_inner(), EffectRow::singleton(effect))));
        if !crate::types::same_type_with_budget(&expected, binder.ty(), work).map_err(|()| Failure::Resource)? {
            return Err(Failure::Invalid);
        }
        if *canonical_method == method { selected_binder = Some(binder.id()); }
    }
    selected_binder.ok_or(Failure::Invalid)
}

pub(super) struct ProviderComputationOwner(pub(super) ComputationType);
impl Deref for ProviderComputationOwner {
    type Target = ComputationType;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl ProviderComputationOwner {
    fn into_inner(mut self) -> ComputationType {
        std::mem::replace(
            &mut self.0,
            ComputationType::new(Type::Unit, EffectRow::empty()),
        )
    }
}
impl Drop for ProviderComputationOwner {
    fn drop(&mut self) {
        discard_type_iteratively(std::mem::replace(&mut self.0.value, Type::Unit));
    }
}

pub(super) struct ProviderForwarding {
    pub(super) method: MethodId,
    pub(super) operation: OperationId,
    pub(super) binder: BinderId,
    pub(super) ty: IterativeTypeOwner,
}

pub(super) struct ProviderForwardings {
    pub(super) application: InterfaceApplication,
    pub(super) effect: EffectInstance,
    pub(super) methods: Vec<ProviderForwarding>,
}

/// One suspended source-checking step. Keeping this owned state in a box
/// preserves the ordinary expression dispatcher's bounded host stack.
pub(super) struct ProviderInstanceProgress<'a> {
    pub(super) resource: &'a ResolvedProviderResourceExpr,
    pub(super) span: Span,
    pub(super) initializer: TypedNodeOwner,
    pub(super) code: super::provider::PreparedProviderCode,
    pub(super) actuals: ResourceActuals,
    pub(super) native: NativeScopeActuals,
    pub(super) forwarding: ProviderForwardings,
    pub(super) members: Vec<(TypedBinder, NodeId)>,
    pub(super) handle: TypedBinder,
    pub(super) previous: Option<usize>,
    pub(super) evidence_marker: Option<crate::evidence::PendingObligationMarker>,
}

pub(super) struct DeferredSourceProviderInstance {
    slot: crate::resolved::ProviderInstanceSlot,
    definition: Arc<ResourceTypeFact>,
    code: super::provider::PreparedProviderCode,
    actuals: ResourceActuals,
    body: ProviderComputationOwner,
    body_node: NodeId,
    scope_node: NodeId,
    forwarding: ProviderForwardings,
    native_effect: EffectInstance,
    members: Vec<(BinderId, NodeId)>,
    rows: crate::core::provider::DeferredProviderHandlerRows,
    copy_plan: PreparedScopeCopyPlan,
    marker: crate::evidence::PendingObligationMarker,
    provider: crate::interface::LexicalEvidenceId,
    span: Span,
}

impl std::fmt::Debug for DeferredSourceProviderInstance {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("DeferredSourceProviderInstance")
            .field("span", &self.span)
            .field("provider", &self.provider)
            .field("body_node", &self.body_node)
            .field("scope_node", &self.scope_node)
            .field("members", &self.members.len())
            .finish_non_exhaustive()
    }
}

enum SourceProviderRows {
    Complete(crate::core::provider::ResolvedProviderHandlerRows),
    Deferred(crate::core::provider::DeferredProviderHandlerRows),
}
impl SourceProviderRows {
    fn output(&self) -> &EffectRow {
        match self {
            Self::Complete(rows) => rows.output(),
            Self::Deferred(rows) => rows.output(),
        }
    }
    fn copy_rows(&self) -> copy::ProviderScopeCopyRows<'_> {
        match self {
            Self::Complete(rows) => copy::ProviderScopeCopyRows {
                residual: rows.residual(),
                pending: rows.pending(),
                nodes: rows.node_rows(),
            },
            Self::Deferred(rows) => copy::ProviderScopeCopyRows {
                residual: rows.residual(),
                pending: rows.pending(),
                nodes: rows.node_rows(),
            },
        }
    }
}

pub(super) struct ResourceActuals {
    arguments: Box<[KindedArgument]>,
    pub(super) replacements: OwnerReplacementBuffer,
}

impl ResourceActuals {
    pub(super) fn arguments(&self) -> &[KindedArgument] {
        &self.arguments
    }

    pub(super) fn access_type(
        &self,
        fact: &ResourceTypeFact,
        work: &mut TypeWorkBudget,
    ) -> Result<Type, TypeError> {
        work.charge(fact.parameters.len())
            .map_err(|()| type_resource())?;
        if self.arguments.len() != fact.parameters.len() {
            return Err(invalid_state());
        }
        let mut rows = false;
        for (formal, actual) in fact.parameters.iter().zip(self.arguments.iter()) {
            match (&formal.kind, actual) {
                (Kind::EffectRow, KindedArgument::RowArg(_)) => rows = true,
                (Kind::EffectRow, _) | (_, KindedArgument::RowArg(_)) => {
                    return Err(invalid_state());
                }
                _ => {}
            }
        }
        if rows {
            work.charge(1).map_err(|()| type_resource())?;
            let arguments =
                crate::types::clone_kinded_arguments_with_budget(self.arguments.iter(), work)
                    .map_err(|()| type_resource())?;
            Ok(Type::ResourceApply(fact.id, arguments))
        } else {
            work.charge(
                self.arguments
                    .len()
                    .checked_add(1)
                    .ok_or_else(type_resource)?,
            )
            .map_err(|()| type_resource())?;
            let mut ty = IterativeTypeOwner::new(Type::Nominal(fact.family));
            for argument in &self.arguments {
                let KindedArgument::TypeArg(argument) = argument else {
                    return Err(invalid_state());
                };
                let argument = crate::types::clone_type_with_budget(argument, work)
                    .map_err(|()| type_resource())?;
                ty = IterativeTypeOwner::new(Type::Application(
                    Box::new(ty.into_inner()),
                    Box::new(argument),
                ));
            }
            Ok(ty.into_inner())
        }
    }
}

/// Typed native association for an instance. This contains no native owner or
/// executable permission; final Core admission reconstructs these relations.
pub(super) struct NativeScopeActuals {
    pub(super) native: Arc<crate::foreign::ForeignModuleFact>,
    pub(super) effect: EffectInstance,
    pub(super) retained: Box<[TypeVariableId]>,
}

impl Drop for ResourceActuals {
    fn drop(&mut self) {
        for argument in std::mem::take(&mut self.arguments).into_vec() {
            crate::types::discard_kinded_argument_iteratively(argument);
        }
    }
}

impl<F: CoreLoweringFamily> CoreElaborator<F> {
    pub(super) fn prepare_final_family_members(
        &mut self, originals: &[Arc<PreparedProviderFamilyInstance>],
    ) -> Result<Box<[Arc<PreparedProviderFamilyInstance>]>, TypeError> {
        self.type_work.charge(originals.len()).map_err(|()| type_resource())?;
        let mut members = Vec::new();
        members.try_reserve_exact(originals.len()).map_err(|_| type_resource())?;
        for original in originals {
            self.type_work.charge(original.requirements.len().checked_add(original.forwardings.len())
                .and_then(|count| count.checked_add(original.selections.len())).ok_or_else(type_resource)?)
                .map_err(|()| type_resource())?;
            let mut requirements = Vec::new();
            requirements.try_reserve_exact(original.requirements.len()).map_err(|_| type_resource())?;
            requirements.extend(original.requirements.iter().cloned());
            let mut selections = Vec::new();
            selections.try_reserve_exact(original.selections.len()).map_err(|_| type_resource())?;
            selections.extend(original.selections.iter().cloned());
            let mut forwardings = Vec::new();
            forwardings.try_reserve_exact(original.forwardings.len()).map_err(|_| type_resource())?;
            for (method, operation, binder) in &original.forwardings {
                let ty = self.clone_type(binder.ty())?;
                let binder = self.builder.binder(ty, binder.origin().clone())?;
                forwardings.push((*method, *operation, binder));
            }
            members.push(Arc::new(PreparedProviderFamilyInstance {
                source: original.source, identity: original.identity,
                application: original.application.clone_with_budget(&mut self.type_work).map_err(|()| type_resource())?,
                requirements: requirements.into_boxed_slice(),
                selections,
                payload: IterativeTypeOwner::new(self.clone_type(&original.payload)?),
                provided: crate::types::clone_effect_instance_with_budget(&original.provided, &mut self.type_work).map_err(|()| type_resource())?,
                native: crate::types::clone_effect_instance_with_budget(&original.native, &mut self.type_work).map_err(|()| type_resource())?,
                forwardings: forwardings.into_boxed_slice(),
            }));
        }
        Ok(members.into_boxed_slice())
    }

    fn begin_provider_family_demands(
        &mut self, resource: &ResolvedProviderResourceExpr, source: &provider::ProviderTemplateSource<'_>, actuals: &ResourceActuals,
    ) -> Result<(), TypeError> {
        let Some(family) = &source.family else {
            if resource.family_provider.is_some() { return Err(invalid_state()); }
            return Ok(());
        };
        let candidate = resource.family_provider.ok_or_else(invalid_state)?;
        let original = source.fact.family_template.as_ref().ok_or_else(invalid_state)?;
        if family.identity.definition != resource.definition || family.identity.parameter != original.parameter.id
            || candidate == resource.provider || candidate.module() != resource.provider.module() { return Err(invalid_state()); }
        self.type_work.charge(self.provider_family_demands.len().checked_add(family.requirements.len()).ok_or_else(type_resource)?)
            .map_err(|()| type_resource())?;
        if self.provider_family_demands.iter().any(|scope| scope.source == candidate) { return Err(invalid_state()); }
        let application = application_requirement(family.provider_application, actuals, &mut self.type_work)?;
        let mut requirements = Vec::new();
        requirements.try_reserve_exact(family.requirements.len()).map_err(|_| type_resource())?;
        for requirement in family.requirements {
            requirements.push(crate::interface::CheckedRequirement { id: requirement.id,
                application: application_requirement(requirement.application(), actuals, &mut self.type_work)?,
                span: requirement.span, origin: Origin::Source(requirement.span) });
        }
        fn application_requirement(application: &InterfaceApplication, actuals: &ResourceActuals, work: &mut TypeWorkBudget) -> Result<InterfaceApplication, TypeError> {
            let mut arguments = ProviderFamilyArguments(Vec::new());
            work.charge(application.arguments().len()).map_err(|()| type_resource())?;
            arguments.0.try_reserve_exact(application.arguments().len()).map_err(|_| type_resource())?;
            for argument in application.arguments() {
                arguments.0.push(crate::types::substitute_kinded_argument_with(argument, actuals.replacements.types.as_map(), &actuals.replacements.rows,
                    |units| work.charge(units)).map_err(|()| type_resource())?.map_err(|_| invalid_state())?);
            }
            Ok(InterfaceApplication::new_kinded(application.interface(), std::mem::take(&mut arguments.0).into_boxed_slice()))
        }
        fn effect(effect: &EffectInstance, actuals: &ResourceActuals, work: &mut TypeWorkBudget) -> Result<EffectInstance, TypeError> {
            let row = EffectRow::singleton(crate::types::clone_effect_instance_with_budget(effect, work).map_err(|()| type_resource())?);
            let row = actuals.replacements.substitute_row(&row, work)?;
            let [effect] = row.known() else { return Err(invalid_state()); };
            if row.tail().is_some() { return Err(invalid_state()); }
            crate::types::clone_effect_instance_with_budget(effect, work).map_err(|()| type_resource())
        }
        let provided = effect(&original.provided.instance, actuals, &mut self.type_work)?;
        let native = effect(&original.interpreted.instance, actuals, &mut self.type_work)?;
        self.type_work.charge(family.methods.len().checked_add(1).ok_or_else(type_resource)?).map_err(|()| type_resource())?;
        let mut methods = Vec::new(); methods.try_reserve_exact(family.methods.len()).map_err(|_| type_resource())?;
        methods.extend_from_slice(family.methods);
        self.provider_family_demands.try_reserve(1).map_err(|_| type_resource())?;
        let mut members = Vec::new();
        let frozen = self.purpose == ElaborationPurpose::FinalSynthesis;
        if frozen {
            let preparation = self.final_provider_preparation.as_ref().ok_or_else(invalid_state)?;
            let plan = preparation.plan(resource.provider).ok_or_else(invalid_state)?;
            self.type_work.charge(plan.family_members.len()).map_err(|()| type_resource())?;
            members.try_reserve_exact(plan.family_members.len()).map_err(|_| type_resource())?;
            for member in &plan.family_members {
                if member.source != candidate || member.identity != family.identity { return Err(invalid_state()); }
                members.push(Arc::clone(member));
            }
        } else {
            self.selection.as_mut().ok_or_else(invalid_state)?.add_scoped_family(candidate, resource.definition, family.identity.parameter,
                application.clone_with_budget(&mut self.type_work).map_err(|()| type_resource())?, &requirements,
                resource.origin.primary_span(), &mut self.constraint_work, &mut self.type_work)
                .map_err(|failure| selection_failure(failure, Some(resource.origin.primary_span())))?;
        }
        let arguments = ProviderFamilyArguments(crate::types::clone_kinded_arguments_with_budget(
            actuals.arguments().iter(), &mut self.type_work).map_err(|()| type_resource())?.into_vec());
        self.type_work.charge(self.registry.provider_contract_count().checked_add(3).ok_or_else(type_resource)?)
            .map_err(|()| type_resource())?;
        let certificate = self.registry.provider_contracts()
            .find(|(module, _)| **module == resource.definition.module())
            .map(|(_, certificate)| Arc::clone(certificate));
        self.provider_family_demands.push(ProviderFamilyDemandScope { source: candidate, identity: family.identity,
            primary_source: resource.provider, original: Arc::clone(source.fact), authority: Arc::clone(family.authority),
            certificate, arguments,
            application, requirements: requirements.into_boxed_slice(), provided, native, methods: methods.into_boxed_slice(),
            members, frozen, origin: Origin::Source(resource.origin.primary_span()) });
        Ok(())
    }

    fn prepare_provider_group_rows(
        &mut self, source: &provider::ProviderTemplateSource<'_>, actuals: &ResourceActuals,
        members: &[Arc<PreparedProviderFamilyInstance>], body: &ComputationType, primary_provided: &EffectInstance, primary_native: &EffectInstance,
    ) -> Result<(crate::core::provider::ResolvedProviderHandlerRows, Box<[crate::core::provider::ResolvedProviderHandlerRows]>), TypeError> {
        let family = source.family.as_ref().ok_or_else(invalid_state)?;
        self.type_work.charge(members.len().checked_add(1).ok_or_else(type_resource)?).map_err(|()| type_resource())?;
        let mut substitutions = Vec::new(); substitutions.try_reserve_exact(members.len()).map_err(|_| type_resource())?;
        for member in members {
            if member.identity != family.identity { return Err(invalid_state()); }
            let mut sigma = OwnerReplacementBuffer::new();
            for (formal, actual) in source.fact.parameters.iter().zip(actuals.arguments()) {
                sigma.insert_cloned(formal.id, actual, &mut self.type_work)?;
            }
            sigma.insert_borrowed(family.identity.parameter, super::BorrowedOwnerArgument::TypeArg(&member.payload), &mut self.type_work)?;
            substitutions.push(sigma);
        }
        let mut inputs = Vec::new(); inputs.try_reserve_exact(members.len() + 1).map_err(|_| type_resource())?;
        inputs.push(crate::core::provider::ProviderGroupRowsInput { original: source.handler,
            types: actuals.replacements.types.as_map(), rows: &actuals.replacements.rows,
            provided: primary_provided, native: primary_native });
        for (member, sigma) in members.iter().zip(&substitutions) {
            inputs.push(crate::core::provider::ProviderGroupRowsInput { original: family.handler,
                types: sigma.types.as_map(), rows: &sigma.rows, provided: &member.provided, native: &member.native });
        }
        let solutions = crate::core::provider::prepare_group_handler_rows(&inputs, body.value(), body.effects(), &mut self.type_work)
            .map_err(|failure| resolved_build_error(contract_validation_failure(failure)))?;
        let mut solutions = solutions.into_vec(); solutions.reverse();
        let primary = solutions.pop().ok_or_else(invalid_state)?; solutions.reverse();
        Ok((primary, solutions.into_boxed_slice()))
    }

    fn freeze_provider_family_demands(&mut self, resource: &ResolvedProviderResourceExpr)
        -> Result<Box<[Arc<PreparedProviderFamilyInstance>]>, TypeError> {
        let Some(source) = resource.family_provider else { return Ok(Box::new([])); };
        let selected = if self.purpose == ElaborationPurpose::FinalSynthesis { Vec::new() } else {
            self.selection.as_ref().ok_or_else(invalid_state)?.selected_family_plans(source, &mut self.type_work)
                .map_err(|failure| selection_failure(failure, Some(resource.origin.primary_span())))?
        };
        for (selection, node) in selected {
            let Some(crate::interface::EvidenceNode::ProviderFamily { methods, .. }) = selection.node(node) else { return Err(invalid_state()); };
            for method in methods { self.materialize_provider_family(&selection, node, *method)?; }
        }
        self.type_work.charge(self.provider_family_demands.len()).map_err(|()| type_resource())?;
        let scope = self.provider_family_demands.iter_mut().find(|scope| scope.source == source).ok_or_else(invalid_state)?;
        self.type_work.charge(scope.members.len()).map_err(|()| type_resource())?;
        let mut members = Vec::new(); members.try_reserve_exact(scope.members.len()).map_err(|_| type_resource())?;
        members.extend(scope.members.iter().cloned());
        scope.frozen = true;
        Ok(members.into_boxed_slice())
    }

    pub(super) fn materialize_provider_family(
        &mut self,
        selection: &crate::interface::EvidenceSelection,
        node: crate::interface::EvidenceNodeId,
        method: MethodId,
    ) -> Result<(usize, BinderId, Type), TypeError> {
        let Some(crate::interface::EvidenceNode::ProviderFamily { source, definition, parameter, application, prerequisites, methods }) = selection.node(node) else {
            return Err(invalid_state());
        };
        self.type_work.charge(methods.len()).map_err(|()| type_resource())?;
        if !methods.contains(&method) { return Err(invalid_state()); }
        self.type_work.charge(self.provider_family_demands.len()).map_err(|()| type_resource())?;
        let index = self.provider_family_demands.iter().position(|scope| scope.source == source).ok_or_else(invalid_state)?;
        let scope = &self.provider_family_demands[index];
        if scope.identity.definition != definition || scope.identity.parameter != parameter
            || prerequisites.len() != scope.requirements.len() { return Err(invalid_state()); }
        self.type_work.charge(scope.members.len()).map_err(|()| type_resource())?;
        let mut cached = None;
        for (member, retained) in scope.members.iter().enumerate() {
            if crate::evidence::same_applications_with_constraint_budget(retained.application(), application, &mut self.constraint_work)
                .map_err(|()| constraint_resource())? {
                if cached.replace(member).is_some() { return Err(invalid_state()); }
            }
        }
        if let Some(member) = cached {
            let frozen = scope.frozen;
            let binder = authenticate_family_forwarding(&self.provider_family_demands, &self.registry,
                selection, node, method, frozen, &mut self.type_work).map_err(|failure| match failure {
                    crate::core::capture::Failure::Resource => type_resource(),
                    _ => invalid_state(),
                })?;
            let retained = &self.provider_family_demands[index].members[member];
            self.type_work.charge(retained.selections.len()).map_err(|()| type_resource())?;
            let recorded = retained.selections.iter().any(|(original, original_node)| *original_node == node
                && original.root() == selection.root() && original.shares_plan_with(selection));
            let (_, _, forwarding) = retained.forwardings.iter().find(|(id, _, _)| *id == method).ok_or_else(invalid_state)?;
            let ty = IterativeTypeOwner::new(crate::types::clone_type_with_budget(forwarding.ty(), &mut self.type_work)
                .map_err(|()| type_resource())?);
            if !recorded {
                if frozen { return Err(invalid_state()); }
                self.type_work.charge(1).map_err(|()| type_resource())?;
                // Unfrozen members are private to this scope. The first Arc
                // clones occur in freeze_provider_family_demands, which also
                // closes the inventory before another materialization.
                let retained = Arc::get_mut(&mut self.provider_family_demands[index].members[member])
                    .ok_or_else(invalid_state)?;
                retained.selections.try_reserve(1).map_err(|_| type_resource())?;
                retained.selections.push((selection.clone(), node));
            }
            return Ok((member, binder, ty.into_inner()));
        }
        if scope.frozen { return Err(invalid_state()); }
        // Match every ordered argument. Only the original rigid payload is a
        // pattern parameter; outer owner/type/row actuals remain exact.
        let registry = Arc::clone(&self.registry);
        let mut candidate = Vec::new(); let mut goal = Vec::new();
        self.constraint_work.charge(scope.application.arguments().len().checked_add(application.arguments().len()).ok_or_else(constraint_resource)?)
            .map_err(|()| constraint_resource())?;
        candidate.try_reserve_exact(scope.application.arguments().len()).map_err(|_| constraint_resource())?;
        goal.try_reserve_exact(application.arguments().len()).map_err(|_| constraint_resource())?;
        candidate.extend(scope.application.arguments()); goal.extend(application.arguments());
        let canonical = crate::interface::authenticate_implementation_application_goal(&registry,
            crate::interface::InterfaceOperationWork::new(scope.origin.primary_span(), &mut self.constraint_work, &mut self.type_work), &goal)
            .map_err(|failure| selection_failure(crate::evidence::map_head_failure(failure), Some(scope.origin.primary_span())))?;
        let substitutions = crate::interface::match_implementation_application_head_against_canonical_goal(&registry,
            crate::interface::InterfaceOperationWork::new(scope.origin.primary_span(), &mut self.constraint_work, &mut self.type_work),
            &[parameter], &candidate, &canonical)
            .map_err(|failure| selection_failure(crate::evidence::map_head_failure(failure), Some(scope.origin.primary_span())))?
            .ok_or_else(invalid_state)?;
        let [substitution] = &*substitutions else { return Err(invalid_state()); };
        if substitution.parameter() != parameter || !matches!(substitution.argument(), Type::Unit | Type::Bool | Type::Int) { return Err(invalid_state()); }
        let mut replacements = OwnerReplacementBuffer::new();
        replacements.insert_cloned(parameter, &KindedArgument::TypeArg(crate::types::clone_type_with_budget(substitution.argument(), &mut self.type_work)
            .map_err(|()| type_resource())?), &mut self.type_work)?;
        let provided = replacements.substitute_row(&EffectRow::singleton(crate::types::clone_effect_instance_with_budget(&scope.provided, &mut self.type_work)
            .map_err(|()| type_resource())?), &mut self.type_work)?;
        let native = replacements.substitute_row(&EffectRow::singleton(crate::types::clone_effect_instance_with_budget(&scope.native, &mut self.type_work)
            .map_err(|()| type_resource())?), &mut self.type_work)?;
        let [provided] = provided.known() else { return Err(invalid_state()); };
        let [native] = native.known() else { return Err(invalid_state()); };
        let provided = crate::types::clone_effect_instance_with_budget(provided, &mut self.type_work).map_err(|()| type_resource())?;
        let native = crate::types::clone_effect_instance_with_budget(native, &mut self.type_work).map_err(|()| type_resource())?;
        let application = application.clone_with_budget(&mut self.type_work).map_err(|()| type_resource())?;
        let payload = IterativeTypeOwner::new(crate::types::clone_type_with_budget(substitution.argument(), &mut self.type_work).map_err(|()| type_resource())?);
        self.type_work.charge(prerequisites.len().checked_add(scope.methods.len()).ok_or_else(type_resource)?).map_err(|()| type_resource())?;
        let mut requirements = Vec::new();
        requirements.try_reserve_exact(prerequisites.len()).map_err(|_| type_resource())?;
        for prerequisite in prerequisites {
            if prerequisite.index() >= node.index() { return Err(invalid_state()); }
            requirements.push((selection.clone(), *prerequisite));
        }
        let mut associations = Vec::new();
        associations.try_reserve_exact(scope.methods.len()).map_err(|_| type_resource())?;
        associations.extend_from_slice(&scope.methods);
        let origin = Origin::Source(scope.origin.primary_span());
        let identity = scope.identity;
        let mut forwardings = Vec::new();
        forwardings.try_reserve_exact(associations.len()).map_err(|_| type_resource())?;
        for (method, operation) in associations {
            let (domain, result) = self.operation_signature(&provided, operation, origin.primary_span())?;
            let effects = EffectRow::singleton(crate::types::clone_effect_instance_with_budget(&provided, &mut self.type_work).map_err(|()| type_resource())?);
            let binder = self.builder.binder(Type::function_computation(domain, ComputationType::new(result, effects)), origin.clone())?;
            forwardings.push((method, operation, binder));
        }
        let member = self.provider_family_demands[index].members.len();
        self.type_work.charge(2).map_err(|()| type_resource())?;
        let mut selections = Vec::new();
        selections.try_reserve_exact(1).map_err(|_| type_resource())?;
        selections.push((selection.clone(), node));
        self.provider_family_demands[index].members.try_reserve(1).map_err(|_| type_resource())?;
        self.provider_family_demands[index].members.push(Arc::new(PreparedProviderFamilyInstance { source, identity, application,
            requirements: requirements.into_boxed_slice(), selections, payload, provided, native, forwardings: forwardings.into_boxed_slice() }));
        if let Err(failure) = capture_family_forwarding(&self.provider_family_demands, &self.registry,
            selection, node, method, &mut self.type_work) {
            self.provider_family_demands[index].members.pop();
            return Err(match failure {
                crate::core::capture::Failure::Resource => type_resource(),
                _ => invalid_state(),
            });
        }
        let (_, _, binder) = self.provider_family_demands[index].members[member].forwardings.iter().find(|(id, _, _)| *id == method).ok_or_else(invalid_state)?;
        Ok((member, binder.id(), crate::types::clone_type_with_budget(binder.ty(), &mut self.type_work).map_err(|()| type_resource())?))
    }

    /// Complete only resource suffixes covered by the ordinary owner closure.
    /// Finished nested bodies precede their enclosing body in this inventory.
    pub(super) fn complete_deferred_provider_instances(
        &mut self,
        marker: crate::evidence::PendingObligationMarker,
        owner: NodeId,
    ) -> Result<(), TypeError> {
        if self.deferred_provider_instances.is_empty() {
            return Ok(());
        }
        if self.purpose != ElaborationPurpose::ModuleCheck {
            return Err(invalid_state());
        }
        // Pending-prefix counts alone are not owner identities: an unrelated
        // later zero-obligation binding may share them. Authenticate the exact
        // finished typed owner before completing any resource below it.
        let mut stack = Vec::new();
        let mut reachable = std::collections::HashSet::new();
        self.type_work.charge(1).map_err(|()| type_resource())?;
        stack.try_reserve(1).map_err(|_| type_resource())?;
        stack.push(owner);
        while let Some(node) = stack.pop() {
            self.type_work.charge(1).map_err(|()| type_resource())?;
            reachable.try_reserve(1).map_err(|_| type_resource())?;
            if !reachable.insert(node) {
                continue;
            }
            let kind = self.builder.compiler_node_kind(node)?;
            self.type_work
                .charge(F::child_count(kind))
                .map_err(|()| type_resource())?;
            stack
                .try_reserve(F::child_count(kind))
                .map_err(|_| type_resource())?;
            for ordinal in 0..F::child_count(kind) {
                stack.push(F::child_at(kind, ordinal).ok_or_else(invalid_state)?);
            }
        }
        let count = self.deferred_provider_instances.len();
        self.type_work.charge(count).map_err(|()| type_resource())?;
        let mut retained = Vec::new();
        retained
            .try_reserve_exact(count)
            .map_err(|_| type_resource())?;
        let pending = std::mem::replace(&mut self.deferred_provider_instances, retained);
        for instance in pending {
            if !marker.covers(instance.marker) || !reachable.contains(&instance.scope_node) {
                self.deferred_provider_instances.push(instance);
                continue;
            }
            self.complete_deferred_provider_instance(instance)?;
        }
        Ok(())
    }

    fn complete_deferred_provider_instance(
        &mut self,
        instance: DeferredSourceProviderInstance,
    ) -> Result<(), TypeError> {
        let DeferredSourceProviderInstance {
            slot,
            definition,
            code,
            actuals,
            body,
            body_node,
            forwarding,
            native_effect,
            members,
            rows: deferred,
            copy_plan,
            provider,
            span,
            ..
        } = instance;
        self.complete_ready_provider_row_equations()?;
        self.zonk_builder_types_since(None, false)
            .map_err(TypeError::Internal)?;
        let value = IterativeTypeOwner::new(self.zonk(body.value())?);
        let effects = self.zonk_effect_row(body.effects())?;
        let body = ProviderComputationOwner(ComputationType::new(value.into_inner(), effects));
        let completed = self.provider_completed_roots.as_deref().unwrap_or(&[]);
        let imported = self.provider_imported_captures.as_deref().unwrap_or(&[]);
        self.type_work
            .charge(
                completed
                    .len()
                    .checked_add(members.len())
                    .and_then(|n| n.checked_add(imported.len()))
                    .ok_or_else(type_resource)?,
            )
            .map_err(|()| type_resource())?;
        let mut roots = Vec::new();
        roots
            .try_reserve_exact(completed.len() + members.len())
            .map_err(|_| type_resource())?;
        roots.extend_from_slice(completed);
        roots.extend_from_slice(&members);
        let (methods, adapters) = self.capture_provider_actual_routes(body_node, &roots)?;
        let imported = self.provider_imported_captures.as_deref().unwrap_or(&[]);
        let mut imports = Vec::new();
        imports
            .try_reserve_exact(imported.len())
            .map_err(|_| type_resource())?;
        imports.extend(imported.iter().map(|(binder, capture)| (*binder, capture)));
        let capture = crate::core::capture::prepare_actual_provider_capture(
            &self.builder,
            body_node,
            &roots,
            &imports,
            &methods,
            &adapters,
            &native_effect,
            F::capture_operation,
            &mut self.type_work,
        )
        .map_err(|failure| super::capture_failure(failure, &mut self.type_work))?;
        let source = if let Some(local) = self
            .pending_local_provider
            .as_ref()
            .filter(|local| local.module() == definition.id.module())
        {
            local.template_source(&code, definition.id, definition.family, &mut self.type_work)?
        } else {
            code.imported_template_source(
                definition.id,
                definition.family,
                self.source_provider_contracts
                    .get(&definition.id.module())
                    .ok_or_else(invalid_state)?,
                &mut self.type_work,
            )?
        };
        let rows = source
            .handler
            .prepare_rows(
                actuals.replacements.types.as_map(),
                &actuals.replacements.rows,
                body.value(),
                body.effects(),
                &forwarding.effect,
                Some(capture),
                &mut self.type_work,
            )
            .map_err(|failure| {
                if failure.is_row_union_ambiguous() {
                    effect_row_failure(
                        super::EffectRowCause::Union,
                        span,
                        "this resource instance has no principal effect-row union",
                    )
                } else {
                    resolved_build_error(contract_validation_failure(failure))
                }
            })?;
        // Validate every canonical original position before solving any copy
        // coordinate. Copy-local identities use the retained exact alpha map.
        let completion = deferred
            .completion(&rows, &mut self.type_work)
            .map_err(|failure| resolved_build_error(contract_validation_failure(failure)))?;
        for (position, identity, row) in completion {
            use crate::core::provider::DeferredProviderRowPosition as Position;
            let row = match position {
                Position::Node(_) | Position::Pending(_) | Position::Handler(_) => copy_plan.phases
                    [2]
                .context()
                .realized_row(row, &mut self.type_work)
                .map_err(|failure| TypeError::Internal(failure.into()))?,
                Position::Output | Position::Residual => {
                    crate::types::clone_effect_row_with_budget(row, &mut self.type_work)
                        .map_err(|()| type_resource())?
                }
            };
            self.complete_provider_row(identity, row)?;
        }
        self.complete_ready_provider_row_equations()?;
        self.zonk_builder_types_since(None, false)
            .map_err(TypeError::Internal)?;
        self.type_work.charge(1).map_err(|()| type_resource())?;
        let prepared = Arc::new(PreparedProviderInstance {
            definition,
            code,
            actuals,
            handler_rows: rows,
            body,
            forwarding,
            provider,
            family_members: Box::new([]),
            family_rows: Box::new([]),
        });
        self.provider_instances
            .stage(&slot, prepared, &mut self.type_work)
            .map_err(resolved_build_error)
    }

    /// The completed ordinary source unifier, rather than resource-body
    /// synthesis, fixes a retained no-capture plan's answer and effect row.
    pub(super) fn finalize_source_provider_plans(&mut self) -> Result<(), TypeError> {
        if self.purpose != ElaborationPurpose::ModuleCheck
            || !self.deferred_provider_instances.is_empty()
        {
            return Err(invalid_state());
        }
        let mut pending = std::mem::take(&mut self.provider_instances);
        let result = (|| {
            self.type_work
                .charge(pending.len())
                .map_err(|()| type_resource())?;
            pending.finalize_unpublished(
                |plan| self.finalize_no_capture_provider_plan(plan),
                invalid_state,
            )
        })();
        // Restore the exact transaction on both success and error. Every slot
        // remains private and unfilled until the later joint publication.
        self.provider_instances = pending;
        result
    }

    fn finalize_no_capture_provider_plan(
        &mut self,
        plan: &mut PreparedProviderInstance,
    ) -> Result<(), TypeError> {
        let source = if let Some(local) = self
            .pending_local_provider
            .as_ref()
            .filter(|local| local.module() == plan.definition.id.module())
        {
            local.template_source(
                &plan.code,
                plan.definition.id,
                plan.definition.family,
                &mut self.type_work,
            )?
        } else {
            plan.code.imported_template_source(
                plan.definition.id,
                plan.definition.family,
                self.source_provider_contracts
                    .get(&plan.definition.id.module())
                    .ok_or_else(invalid_state)?,
                &mut self.type_work,
            )?
        };
        if source.handler.needs_actual_captures() {
            // Actual capture preparation has its own authenticated input
            // domain; this no-capture refresh cannot mint a replacement receipt.
            return Ok(());
        }
        // The initializer preparation already required closed actual arguments.
        // Repeat that invariant before retaining the completed body metadata:
        // rigid Type identities and formal open rows remain ordinary inputs.
        for argument in plan.actuals.arguments() {
            let ambiguous = crate::types::visit_argument_structure_with_budget(
                argument,
                &mut self.type_work,
                |node, _| {
                    Ok(matches!(node, TypeStructureNode::Type(Type::Inference(_)))
                        || matches!(node,
                            TypeStructureNode::Tail(tail)
                                if matches!(tail.variable(), EffectRowVariable::Inference(_))
                        ))
                },
            )
            .map_err(|()| type_resource())?;
            if ambiguous {
                return Err(invalid_state());
            }
        }
        // End the borrowed source view before using the full ordinary zonker.
        let value = IterativeTypeOwner::new(self.zonk(plan.body.value())?);
        let effects = self.zonk_effect_row(plan.body.effects())?;
        let body = ProviderComputationOwner(ComputationType::new(value.into_inner(), effects));
        let source = if let Some(local) = self
            .pending_local_provider
            .as_ref()
            .filter(|local| local.module() == plan.definition.id.module())
        {
            local.template_source(
                &plan.code,
                plan.definition.id,
                plan.definition.family,
                &mut self.type_work,
            )?
        } else {
            plan.code.imported_template_source(
                plan.definition.id,
                plan.definition.family,
                self.source_provider_contracts
                    .get(&plan.definition.id.module())
                    .ok_or_else(invalid_state)?,
                &mut self.type_work,
            )?
        };
        let rows = source
            .handler
            .prepare_rows(
                plan.actuals.replacements.types.as_map(),
                &plan.actuals.replacements.rows,
                body.value(),
                body.effects(),
                &plan.forwarding.effect,
                None,
                &mut self.type_work,
            )
            .map_err(|failure| resolved_build_error(contract_validation_failure(failure)))?;
        // Nothing fallible follows these replacements. The original code,
        // concrete actuals and forwarding identities remain the same owners.
        plan.body = body;
        plan.handler_rows = rows;
        Ok(())
    }

    // Keep the full owned progress out of the ordinary dispatcher's debug
    // frame. Ordinary source expressions only transfer its existing box.
    #[inline(never)]
    pub(super) fn step_provider_instance_completion(
        &mut self,
        progress: Box<ProviderInstanceProgress<'_>>,
        context: &mut TypeContext,
        values: &mut TypedNodeBuffer,
    ) -> Result<(), TypeError> {
        let body = values.pop().ok_or_else(invalid_state)?;
        values.push(self.finish_provider_instance(*progress, body, context)?);
        Ok(())
    }

    pub(super) fn finish_provider_instance(
        &mut self,
        progress: ProviderInstanceProgress<'_>,
        mut body: TypedNodeOwner,
        context: &mut TypeContext,
    ) -> Result<TypedNode, TypeError> {
        use crate::core::provider::{
            ProviderCopiedTemplate, ProviderForwardingMethod, ProviderOriginalTemplate,
            ProviderScopeAdmission, ProviderScopeAuthority, ProviderScopeNode,
            ProviderSpecializationEntries, derive_provider_scope_protocol,
        };
        if self.purpose == ElaborationPurpose::Standalone {
            return Err(unsupported_provider_resource());
        }
        let ProviderInstanceProgress {
            resource,
            span,
            initializer,
            code,
            actuals,
            native,
            forwarding,
            mut members,
            handle,
            previous,
            evidence_marker,
        } = progress;
        let family_members = if resource.family_provider.is_some() {
            if let Some(marker) = evidence_marker { self.close_evidence_obligations(marker)?; }
            self.freeze_provider_family_demands(resource)?
        } else { Box::new([]) };
        // Legacy resources retain ordinary owner closure ordering.
        self.leave_provider_instance_body(resource, previous, context)?;
        let source = if self.purpose == ElaborationPurpose::ModuleCheck {
            if let Some(local) = self
                .pending_local_provider
                .as_ref()
                .filter(|local| local.module() == resource.definition.module())
            {
                local.template_source(
                    &code,
                    resource.definition,
                    resource.family,
                    &mut self.type_work,
                )?
            } else {
                code.imported_template_source(
                    resource.definition,
                    resource.family,
                    self.source_provider_contracts
                        .get(&resource.definition.module())
                        .ok_or_else(invalid_state)?,
                    &mut self.type_work,
                )?
            }
        } else {
            code.template_source(
                resource.definition,
                resource.family,
                &self.registry,
                &mut self.type_work,
            )?
        };
        // Reuse the ordinary zonker's existing unresolved status. Resolved
        // answers keep the same traversal and copy path in both source modes.
        let (checked_value, ambiguous) = self.zonk_with_status(&body.ty)?;
        let mut checked_value = IterativeTypeOwner::new(checked_value);
        if self.purpose == ElaborationPurpose::FinalSynthesis && ambiguous {
            // This published answer guides an ordinary check, never admission.
            // The exact original template and complete caller actuals have
            // already been reconstructed; verify the source slot association.
            let prepared = resource.prepared.get().ok_or_else(invalid_state)?;
            if prepared.provider != resource.provider
                || prepared.definition.id != source.fact.id
                || prepared.definition.family != source.fact.family
                || prepared.actuals.arguments().len() != actuals.arguments().len()
            {
                return Err(invalid_state());
            }
            self.type_work
                .charge(actuals.arguments().len())
                .map_err(|()| type_resource())?;
            for (original, actual) in prepared.actuals.arguments().iter().zip(actuals.arguments()) {
                if !crate::types::same_kinded_argument_with_budget(
                    original,
                    actual,
                    &mut self.type_work,
                )
                .map_err(|()| type_resource())?
                {
                    return Err(invalid_state());
                }
            }
            // Source inference IDs belong to its completed unifier and cannot
            // be reused as final inference identities. Caller rigid identities
            // retain their original source scope; copy-local identities do not
            // enter this caller answer under the existing escape checks.
            if crate::types::visit_type_structure_with_budget(
                prepared.body.value(),
                &mut self.type_work,
                |node, _| {
                    Ok(matches!(node, TypeStructureNode::Type(Type::Inference(_)))
                        || matches!(node, TypeStructureNode::Tail(tail)
                        if matches!(tail.variable(), EffectRowVariable::Inference(_))))
                },
            )
            .map_err(|()| type_resource())?
            {
                return Err(invalid_state());
            }
            let ty = IterativeTypeOwner::new(self.clone_type(prepared.body.value())?);
            let provenance = self.at_span_provenance(&ty, resource.body.span)?;
            let expected = super::ProvenancedTypeOwner::new(super::ProvenancedType {
                ty: ty.into_inner(),
                provenance,
            });
            self.type_work.charge(1).map_err(|()| type_resource())?;
            let mut checked = TypedNodeBuffer(Vec::new());
            checked
                .0
                .try_reserve_exact(1)
                .map_err(|_| type_resource())?;
            checked.push(body.into_inner());
            self.finish_expression_check(
                resource.body.span,
                expected.into_inner(),
                CheckKind::General,
                &mut checked,
            )?;
            body = checked.pop().ok_or_else(invalid_state)?;
            // The real body and any instantiated callable metadata now use
            // this final unifier before canonical rows or copied forests read
            // them. Other source obligations retain their ordinary ordering.
            self.zonk_builder_types_since(None, false)
                .map_err(TypeError::Internal)?;
            checked_value = IterativeTypeOwner::new(self.zonk(&body.ty)?);
        }
        let checked_effects = self.zonk_effect_row(&body.effects)?;
        let checked_body = ProviderComputationOwner(ComputationType::new(
            checked_value.into_inner(),
            checked_effects,
        ));
        let defer_source = self.purpose == ElaborationPurpose::ModuleCheck
            && source.handler.needs_actual_captures();
        let actual_capture = if !source.handler.needs_actual_captures() || defer_source {
            None
        } else {
            let completed = self.provider_completed_roots.as_deref().unwrap_or(&[]);
            let imports_len = self
                .provider_imported_captures
                .as_deref()
                .map_or(0, |captures| captures.len());
            self.type_work
                .charge(
                    members
                        .len()
                        .checked_add(completed.len())
                        .and_then(|n| n.checked_add(imports_len))
                        .ok_or_else(type_resource)?,
                )
                .map_err(|()| type_resource())?;
            let mut roots = Vec::new();
            roots
                .try_reserve_exact(members.len() + completed.len())
                .map_err(|_| type_resource())?;
            roots.extend_from_slice(completed);
            roots.extend(
                members
                    .iter()
                    .map(|(binder, function)| (binder.id(), *function)),
            );
            let (methods, adapters) = if self.purpose == ElaborationPurpose::ModuleCheck {
                self.capture_provider_actual_routes(body.node, &roots)?
            } else {
                (Vec::new(), Vec::new())
            };
            let owned_imports = self.provider_imported_captures.as_deref().unwrap_or(&[]);
            let mut imports = Vec::new();
            imports
                .try_reserve_exact(owned_imports.len())
                .map_err(|_| type_resource())?;
            imports.extend(
                owned_imports
                    .iter()
                    .map(|(binder, capture)| (*binder, capture)),
            );
            Some(
                crate::core::capture::prepare_actual_provider_capture(
                    &self.builder,
                    body.node,
                    &roots,
                    &imports,
                    &methods,
                    &adapters,
                    &native.effect,
                    F::capture_operation,
                    &mut self.type_work,
                )
                .map_err(|failure| super::capture_failure(failure, &mut self.type_work))?,
            )
        };
        let mut family_rows = Box::new([]) as Box<[crate::core::provider::ResolvedProviderHandlerRows]>;
        let rows = if !family_members.is_empty() {
            let (primary, families) = self.prepare_provider_group_rows(&source, &actuals, &family_members, &checked_body,
                &forwarding.effect, &native.effect)?;
            family_rows = families;
            SourceProviderRows::Complete(primary)
        } else if defer_source {
            let count = crate::core::provider::DeferredProviderHandlerRows::row_count(
                source.handler,
                &mut self.type_work,
            )
            .map_err(|failure| resolved_build_error(contract_validation_failure(failure)))?;
            let mut pending = Vec::new();
            self.type_work.charge(count).map_err(|()| type_resource())?;
            pending
                .try_reserve_exact(count)
                .map_err(|_| type_resource())?;
            for _ in 0..count {
                pending.push(self.defer_provider_row(span)?);
            }
            let mut pending = pending.into_iter();
            SourceProviderRows::Deferred(
                crate::core::provider::DeferredProviderHandlerRows::prepare(
                    source.handler,
                    || pending.next(),
                    &mut self.type_work,
                )
                .map_err(|failure| resolved_build_error(contract_validation_failure(failure)))?,
            )
        } else {
            SourceProviderRows::Complete(
                source
                    .handler
                    .prepare_rows(
                        actuals.replacements.types.as_map(),
                        &actuals.replacements.rows,
                        checked_body.value(),
                        checked_body.effects(),
                        &forwarding.effect,
                        actual_capture,
                        &mut self.type_work,
                    )
                    .map_err(|failure| {
                        if failure.is_row_union_ambiguous() {
                            effect_row_failure(
                                super::EffectRowCause::Union,
                                span,
                                "this resource instance has no principal effect-row union",
                            )
                        } else {
                            resolved_build_error(contract_validation_failure(failure))
                        }
                    })?,
            )
        };
        if self.purpose == ElaborationPurpose::FinalSynthesis
            && source.handler.needs_actual_captures()
        {
            let original_rows = &resource
                .prepared
                .get()
                .ok_or_else(invalid_state)?
                .handler_rows;
            let SourceProviderRows::Complete(rows) = &rows else {
                return Err(invalid_state());
            };
            if !original_rows
                .same_actual_captures(rows, &mut self.type_work)
                .map_err(|failure| resolved_build_error(contract_validation_failure(failure)))?
            {
                return Err(invalid_state());
            }
        }
        let final_preparation = if self.purpose == ElaborationPurpose::FinalSynthesis {
            self.type_work.charge(1).map_err(|()| type_resource())?;
            Some(Arc::clone(
                self.final_provider_preparation
                    .as_ref()
                    .ok_or_else(invalid_state)?,
            ))
        } else {
            None
        };
        let final_plan = final_preparation
            .as_ref()
            .map(|preparation| {
                preparation
                    .plan(resource.provider)
                    .ok_or_else(invalid_state)
            })
            .transpose()?;
        let mut source_plan = None;
        let plan = if let Some(final_plan) = final_plan {
            &final_plan.copyplan
        } else {
            source_plan = Some(if family_members.is_empty() {
                self.prepare_scope_copy_plan_with_rows(&source, &actuals, &checked_body, rows.copy_rows(), resource.provider.module(), span)?
            } else {
                let SourceProviderRows::Complete(primary) = &rows else { return Err(invalid_state()); };
                self.prepare_scope_copy_plan_with_family_rows(&source, &actuals, &checked_body, primary,
                    &family_members, &family_rows, resource.provider.module(), span)?
            });
            source_plan.as_ref().ok_or_else(invalid_state)?
        };
        let originals = [
            ProviderOriginalTemplate::Lifecycle(source.acquire.original, source.acquire.program),
            ProviderOriginalTemplate::Lifecycle(source.finish.original, source.finish.program),
            ProviderOriginalTemplate::Handler(source.handler),
        ];
        let relocations = if let Some(final_plan) = final_plan {
            let builder = F::effect_builder(&mut self.builder).ok_or_else(invalid_state)?;
            let target = builder.provider_method_catalog();
            let acquire = final_preparation::final_provider_catalog_relocations(
                source.acquire.program,
                &[source.acquire.body],
                &plan.phases[0],
                &final_plan.copies[0],
                target,
                &mut self.type_work,
            )?;
            let finish = final_preparation::final_provider_catalog_relocations(
                source.finish.program,
                &[source.finish.body],
                &plan.phases[1],
                &final_plan.copies[1],
                target,
                &mut self.type_work,
            )?;
            self.type_work
                .charge(source.handler.original_clauses().len())
                .map_err(|()| type_resource())?;
            let mut roots = Vec::new();
            roots
                .try_reserve_exact(source.handler.original_clauses().len())
                .map_err(|_| type_resource())?;
            roots.extend(
                source
                    .handler
                    .original_clauses()
                    .iter()
                    .map(crate::core::EffectClause::body),
            );
            let handler = final_preparation::final_provider_catalog_relocations(
                source.handler.original_program(),
                &roots,
                &plan.phases[2],
                &final_plan.copies[2],
                target,
                &mut self.type_work,
            )?;
            Some([acquire, finish, handler])
        } else {
            None
        };
        let copied = if let Some(relocations) = &relocations {
            lower_final_scope_copies(
                F::effect_builder(&mut self.builder).ok_or_else(invalid_state)?,
                &source,
                plan,
                [&relocations[0], &relocations[1], &relocations[2]],
                &mut self.type_work,
            )?
        } else {
            lower_prepared_scope_copies(
                F::effect_builder(&mut self.builder).ok_or_else(invalid_state)?,
                &source,
                plan,
                &mut self.type_work,
            )?
        };
        let family_relocations = if let Some(final_plan) = final_plan {
            if final_plan.family_copies.len() != plan.family_phases.len() { return Err(invalid_state()); }
            let mut relocated = Vec::new();
            self.type_work.charge(plan.family_phases.len()).map_err(|()| type_resource())?;
            relocated.try_reserve_exact(plan.family_phases.len()).map_err(|_| type_resource())?;
            if !plan.family_phases.is_empty() {
                let original = source.family.ok_or_else(invalid_state)?.handler;
                self.type_work.charge(original.original_clauses().len()).map_err(|()| type_resource())?;
                let mut roots = Vec::new();
                roots.try_reserve_exact(original.original_clauses().len()).map_err(|_| type_resource())?;
                roots.extend(original.original_clauses().iter().map(crate::core::EffectClause::body));
                let target = F::effect_builder(&mut self.builder).ok_or_else(invalid_state)?.provider_method_catalog();
                for (phase, catalog) in plan.family_phases.iter().zip(&final_plan.family_copies) {
                    relocated.push(final_preparation::final_provider_catalog_relocations(
                        original.original_program(), &roots, phase, catalog, target, &mut self.type_work)?);
                }
            }
            Some(relocated)
        } else { None };
        let mut family_copied = lower_family_scope_copies(
            F::effect_builder(&mut self.builder).ok_or_else(invalid_state)?, &source, plan,
            family_relocations.as_deref(), &mut self.type_work)?;
        if family_copied.len() != family_members.len() { return Err(invalid_state()); }
        let mut dictionary_initializers = Vec::new();
        self.type_work.charge(family_members.len()).map_err(|()| type_resource())?;
        dictionary_initializers.try_reserve_exact(family_members.len()).map_err(|_| type_resource())?;
        for (member, copied) in family_members.iter().zip(&family_copied) {
            if member.requirements.len() != copied.dictionaries.len() { return Err(invalid_state()); }
            self.type_work.charge(member.requirements.len()).map_err(|()| type_resource())?;
            let mut initializers = Vec::new();
            initializers.try_reserve_exact(member.requirements.len()).map_err(|_| type_resource())?;
            for ((selection, node), binder) in member.requirements.iter().zip(&copied.dictionaries) {
                let Some(crate::interface::EvidenceNode::NativeLayout { producer }) = selection.node(*node) else { return Err(invalid_state()); };
                let dictionary = self.registry.foreign_layout_dictionary(producer, &mut self.type_work)
                    .map_err(|failure| if failure.is_resource_exhaustion() { type_resource() } else { invalid_state() })?;
                if dictionary.producer() != producer || !crate::types::same_type_with_budget(binder.ty(), &producer.producer_type(), &mut self.type_work).map_err(|()| type_resource())? {
                    return Err(invalid_state());
                }
                let ty = self.clone_type(binder.ty())?;
                let initializer = self.builder.intrinsic(crate::core::packed::Intrinsic::ForeignLayoutWitness { producer },
                    producer.interface().module(), ty, Origin::Source(span))?;
                initializers.push(initializer);
            }
            dictionary_initializers.push(initializers);
            self.type_work.charge(member.forwardings.len()).map_err(|()| type_resource())?;
            members.try_reserve(member.forwardings.len()).map_err(|_| type_resource())?;
            for (_, operation, binder) in &member.forwardings {
                let function = binder.ty().function_view().ok_or_else(invalid_state)?;
                let domain = self.clone_type(function.domain())?;
                let parameter = self.builder.binder(domain, Origin::Source(span))?;
                let operand_type = self.clone_type(parameter.ty())?;
                let operand = self.builder.variable(parameter.id(), operand_type, Origin::Source(span))?;
                let value = self.clone_type(function.value())?;
                let effects = self.core_effect_row(function.effects().ok_or_else(invalid_state)?)?;
                let provided = crate::types::clone_effect_instance_with_budget(&member.provided, &mut self.type_work).map_err(|()| type_resource())?;
                let request = self.push_effect_core(value, effects, Origin::Source(span), EffectOperation::Request(RequestNode::new(provided, *operation, operand)))?;
                let function_type = self.clone_type(binder.ty())?;
                let function = self.builder.function(parameter, request, function_type, Origin::Source(span))?;
                let binder_type = self.clone_type(binder.ty())?;
                let binder = self.builder.resolved_binder(binder.id(), binder_type, Origin::Source(span))?;
                members.push((binder, function));
            }
        }
        let builder = F::effect_builder(&mut self.builder).ok_or_else(invalid_state)?;
        let acquire_effects =
            builder.provider_scope_entry_row(copied.acquire.body, &mut self.type_work)?;
        let finish_effects =
            builder.provider_scope_entry_row(copied.finish.body, &mut self.type_work)?;
        let effects = if family_members.is_empty() { self.provider_instance_outward_row(
            &initializer.effects,
            &acquire_effects,
            &finish_effects,
            rows.output(),
            &native.effect,
            span,
        )? } else {
            let acquire = self.provider_native_phase_row(&acquire_effects, &native.effect, span)?;
            let finish = self.provider_native_phase_row(&finish_effects, &native.effect, span)?;
            let phases = self.union_effects(&acquire, &finish, span)?;
            let completed = self.union_effects(&phases, rows.output(), span)?;
            self.union_effects(&initializer.effects, &completed, span)?
        };
        let ty = IterativeTypeOwner::new(self.provider_instance_result_type(
            source.fact,
            &actuals,
            checked_body.value(),
        )?);
        self.check_provider_instance_escape(resource, &ty, &effects, context, span)?;
        let deferred_members = if defer_source {
            self.type_work
                .charge(members.len())
                .map_err(|()| type_resource())?;
            let mut roots = Vec::new();
            roots
                .try_reserve_exact(members.len())
                .map_err(|_| type_resource())?;
            roots.extend(members.iter().map(|(binder, node)| (binder.id(), *node)));
            roots
        } else {
            Vec::new()
        };
        let mut body_node = body.node;
        while let Some((binder, function)) = members.pop() {
            let binder_id = binder.id();
            let body_type = self.clone_type(checked_body.value())?;
            body_node = self.builder.binding(
                binder,
                function,
                body_node,
                body_type,
                Origin::Source(span),
            )?;
            if self.purpose == ElaborationPurpose::FinalSynthesis {
                self.type_work
                    .charge(forwarding.methods.len())
                    .map_err(|()| type_resource())?;
                let Some(method) = forwarding
                    .methods
                    .iter()
                    .find(|method| method.binder == binder_id) else { continue; };
                let application = forwarding
                    .application
                    .clone_with_budget(&mut self.type_work)
                    .map_err(|()| type_resource())?;
                self.builder.authenticate_method_evidence(
                    body_node,
                    None,
                    None,
                    method.method,
                    application,
                    crate::core::dialect::MethodEvidenceAnchorRole::LexicalOwner {
                        source: resource.provider,
                        binder: binder_id,
                    },
                    None,
                )?;
            }
        }
        let protocol = derive_provider_scope_protocol(
            source.fact,
            &native.native,
            actuals.arguments(),
            &self.registry,
            &mut self.type_work,
        )
        .map_err(contract_validation_failure)
        .map_err(resolved_build_error)?;
        self.type_work
            .charge(
                native
                    .retained
                    .len()
                    .checked_add(3)
                    .ok_or_else(type_resource)?,
            )
            .map_err(|()| type_resource())?;
        let mut retained = Vec::new();
        retained
            .try_reserve_exact(native.retained.len())
            .map_err(|_| type_resource())?;
        retained.extend_from_slice(&native.retained);
        let native_effect =
            crate::types::clone_effect_instance_with_budget(&native.effect, &mut self.type_work)
                .map_err(|()| type_resource())?;
        let arguments = crate::types::clone_kinded_arguments_with_budget(
            actuals.arguments().iter(),
            &mut self.type_work,
        )
        .map_err(|()| type_resource())?;
        self.type_work.charge(family_members.len()).map_err(|()| type_resource())?;
        let mut family_admissions = Vec::new();
        family_admissions.try_reserve_exact(family_members.len()).map_err(|_| type_resource())?;
        for member in &family_members {
            self.type_work.charge(member.requirements.len().checked_add(member.selections.len()).ok_or_else(type_resource)?)
                .map_err(|()| type_resource())?;
            let mut requirements = Vec::new();
            requirements.try_reserve_exact(member.requirements.len()).map_err(|_| type_resource())?;
            requirements.extend(member.requirements.iter().cloned());
            let mut selections = Vec::new();
            selections.try_reserve_exact(member.selections.len()).map_err(|_| type_resource())?;
            selections.extend(member.selections.iter().cloned());
            family_admissions.push(crate::core::provider::ProviderFamilyAdmission {
                identity: member.identity, lexical: member.source,
                application: member.application.clone_with_budget(&mut self.type_work).map_err(|()| type_resource())?,
                payload: self.clone_type(&member.payload)?,
                native_effect: crate::types::clone_effect_instance_with_budget(&member.native, &mut self.type_work).map_err(|()| type_resource())?,
                requirements: requirements.into_boxed_slice(),
                selections: selections.into_boxed_slice(),
            });
        }
        let admission = ProviderScopeAdmission {
            definition: Arc::clone(source.fact),
            native: Arc::clone(&native.native),
            arguments,
            identity: resource.identity.id,
            retained: retained.into_boxed_slice(),
            native_effect,
            protocol,
            families: family_admissions.into_boxed_slice(),
        };
        let descriptor = if let (Some(final_plan), Some(relocations)) = (final_plan, &relocations) {
            let slots = [
                retain_original_template_slots(source.acquire.occurrences, &mut self.type_work)?,
                retain_original_template_slots(source.finish.occurrences, &mut self.type_work)?,
                retain_original_template_slots(source.handler_occurrences, &mut self.type_work)?,
            ];
            let primary_copies = [0usize, 1, 2].map(|index| ProviderCopiedTemplate {
                original: originals[index],
                nodes: &copied.forests[index].nodes,
                freshening: plan.phases[index].freshening(),
                substitution: plan.phases[index].substitution(),
                node_rows: plan.phases[index].node_rows(),
                occurrences: &final_plan.copies[index].relocations,
                catalog: &relocations[index],
                original_slots: &slots[index],
            });
            self.type_work.charge(family_copied.len().checked_add(3).ok_or_else(type_resource)?)
                .map_err(|()| type_resource())?;
            let mut copies = Vec::new();
            copies.try_reserve_exact(family_copied.len() + 3).map_err(|_| type_resource())?;
            copies.extend(primary_copies);
            let family_slots = match source.family {
                Some(family) => retain_original_handler_slots(family.handler, &mut self.type_work)?,
                None => Vec::new(),
            };
            for (index, family) in family_copied.iter().enumerate() {
                copies.push(ProviderCopiedTemplate {
                    original: ProviderOriginalTemplate::Handler(source.family.ok_or_else(invalid_state)?.handler),
                    nodes: &family.forest.nodes,
                    freshening: plan.family_phases[index].freshening(),
                    substitution: plan.family_phases[index].substitution(),
                    node_rows: plan.family_phases[index].node_rows(),
                    occurrences: &final_plan.family_copies[index].relocations,
                    catalog: &family_relocations.as_ref().ok_or_else(invalid_state)?[index],
                    original_slots: &family_slots,
                });
            }
            let mut dictionary_entries = Vec::new();
            dictionary_entries.try_reserve_exact(family_copied.len()).map_err(|_| type_resource())?;
            for (family, initializers) in family_copied.iter().zip(&dictionary_initializers) {
                self.type_work.charge(family.dictionaries.len()).map_err(|()| type_resource())?;
                let mut entries = Vec::new();
                entries.try_reserve_exact(family.dictionaries.len()).map_err(|_| type_resource())?;
                entries.extend(family.dictionaries.iter().zip(initializers).map(|(binder, initializer)|
                    crate::core::provider::ProviderSpecializationDictionaryEntry { binder, initializer: *initializer }));
                dictionary_entries.push(entries);
            }
            let mut family_entries = Vec::new();
            family_entries.try_reserve_exact(family_copied.len()).map_err(|_| type_resource())?;
            for (family, dictionaries) in family_copied.iter().zip(&dictionary_entries) {
                family_entries.push(crate::core::provider::ProviderSpecializationFamilyEntries {
                    state: &family.state, handler: family.handler, clauses: &family.clauses, dictionaries,
                });
            }
            // The final scope is not enclosed by its forwarding binds yet.
            // Supply only independently lowered prior globals and these exact
            // typed forwarding members as virtual ordinary value bindings.
            let completed = self.provider_completed_roots.as_deref().unwrap_or(&[]);
            self.type_work
                .charge(
                    completed
                        .len()
                        .checked_add(members.len())
                        .ok_or_else(type_resource)?,
                )
                .map_err(|()| type_resource())?;
            let mut capture_globals = Vec::new();
            capture_globals
                .try_reserve_exact(completed.len() + members.len())
                .map_err(|_| type_resource())?;
            capture_globals.extend_from_slice(completed);
            capture_globals.extend(
                members
                    .iter()
                    .map(|(binder, function)| (binder.id(), *function)),
            );
            let entries = ProviderSpecializationEntries {
                acquire: &copied.acquire,
                finish: &copied.finish,
                state: &copied.state,
                handler: copied.handler,
                clauses: &copied.clauses,
                body: body_node,
                capture_globals: &capture_globals,
                families: &family_entries,
            };
            let builder = F::effect_builder(&mut self.builder).ok_or_else(invalid_state)?;
            ProviderScopeAuthority::Admitted(
                builder
                    .admit_provider_scope(admission, entries, &copies, &mut self.type_work)
                    .map_err(contract_validation_failure)
                    .map_err(resolved_build_error)?,
            )
        } else {
            ProviderScopeAuthority::prepared(admission, &mut self.type_work)?
        };
        self.type_work
            .charge(forwarding.methods.len())
            .map_err(|()| type_resource())?;
        let mut methods = Vec::new();
        methods
            .try_reserve_exact(forwarding.methods.len())
            .map_err(|_| type_resource())?;
        for method in &forwarding.methods {
            methods.push(ProviderForwardingMethod {
                method: method.method,
                binder: method.binder,
            });
        }
        let output_value = IterativeTypeOwner::new(self.clone_type(checked_body.value())?);
        let output_effects = self.core_effect_row(rows.output())?;
        let output = ProviderComputationOwner(ComputationType::new(
            output_value.into_inner(),
            output_effects,
        ));
        let core_ty = IterativeTypeOwner::new(self.clone_type(&ty)?);
        let core_effects = self.core_effect_row(&effects)?;
        let provided = crate::types::clone_effect_instance_with_budget(
            &forwarding.effect,
            &mut self.type_work,
        )
        .map_err(|()| type_resource())?;
        let mut attached = Vec::new();
        let mut dictionary_bindings = Vec::new();
        let mut family_clause_index = Vec::new();
        self.type_work.charge(family_copied.len()).map_err(|()| type_resource())?;
        attached.try_reserve_exact(family_copied.len()).map_err(|_| type_resource())?;
        if !family_copied.is_empty() {
            self.type_work.charge(copied.clauses.len()).map_err(|()| type_resource())?;
            family_clause_index.try_reserve(copied.clauses.len()).map_err(|_| type_resource())?;
            family_clause_index.extend((0..copied.clauses.len()).map(|clause| (0, clause)));
        }
        for (index, ((family, member), initializers)) in family_copied.drain(..).zip(&family_members).zip(dictionary_initializers).enumerate() {
            self.type_work.charge(family.clauses.len().checked_add(member.forwardings.len()).and_then(|n| n.checked_add(family.dictionaries.len())).ok_or_else(type_resource)?)
                .map_err(|()| type_resource())?;
            family_clause_index.try_reserve(family.clauses.len()).map_err(|_| type_resource())?;
            family_clause_index.extend((0..family.clauses.len()).map(|clause| (index + 1, clause)));
            dictionary_bindings.try_reserve(family.dictionaries.len()).map_err(|_| type_resource())?;
            dictionary_bindings.extend(family.dictionaries.into_iter().zip(initializers));
            let mut forwardings = Vec::new();
            forwardings.try_reserve_exact(member.forwardings.len()).map_err(|_| type_resource())?;
            forwardings.extend(member.forwardings.iter().map(|(method, _, binder)| ProviderForwardingMethod { method: *method, binder: binder.id() }));
            attached.push(crate::core::provider::ProviderAttachedHandler {
                state: family.state, lexical: member.source,
                forwardings: forwardings.into_boxed_slice(),
                handler: crate::core::effect::HandlerNode::new(family.handler, body_node,
                    crate::types::clone_effect_instance_with_budget(&member.provided, &mut self.type_work).map_err(|()| type_resource())?, family.clauses),
            });
        }
        let mut node = self.push_effect_core(
            core_ty.into_inner(),
            core_effects,
            Origin::Source(span),
            EffectOperation::ProviderScope(Box::new(ProviderScopeNode {
                initializer: initializer.node,
                acquire: copied.acquire,
                finish: copied.finish,
                handler_state: copied.state,
                handle,
                handler: crate::core::effect::HandlerNode::new(
                    copied.handler,
                    body_node,
                    provided,
                    copied.clauses,
                ),
                handler_output: output.into_inner(),
                descriptor,
                lexical: resource.provider,
                forwardings: methods.into_boxed_slice(),
                attached: attached.into_boxed_slice(),
                family_clause_index: family_clause_index.into_boxed_slice(),
            })),
        )?;
        while let Some((binder, initializer)) = dictionary_bindings.pop() {
            let output_type = self.clone_type(&ty)?;
            node = self.builder.binding(binder, initializer, node, output_type, Origin::Source(span))?;
        }
        if self.purpose == ElaborationPurpose::ModuleCheck {
            self.type_work.charge(2).map_err(|()| type_resource())?;
            match rows {
                SourceProviderRows::Complete(rows) => {
                    let prepared = Arc::new(PreparedProviderInstance {
                        definition: Arc::clone(source.fact),
                        code,
                        actuals,
                        handler_rows: rows,
                        body: checked_body,
                        forwarding,
                        provider: resource.provider,
                        family_members,
                        family_rows,
                    });
                    self.provider_instances
                        .stage(&resource.prepared, prepared, &mut self.type_work)
                        .map_err(resolved_build_error)?;
                }
                SourceProviderRows::Deferred(rows) => {
                    let slot = resource
                        .prepared
                        .retain_unpublished(&mut self.type_work)
                        .map_err(resolved_build_error)?;
                    let native_effect = crate::types::clone_effect_instance_with_budget(
                        &native.effect,
                        &mut self.type_work,
                    )
                    .map_err(|()| type_resource())?;
                    self.deferred_provider_instances
                        .try_reserve(1)
                        .map_err(|_| type_resource())?;
                    self.deferred_provider_instances
                        .push(DeferredSourceProviderInstance {
                            slot,
                            definition: Arc::clone(source.fact),
                            code,
                            actuals,
                            body: checked_body,
                            body_node: body.node,
                            scope_node: node,
                            forwarding,
                            native_effect,
                            members: deferred_members,
                            rows,
                            copy_plan: source_plan.take().ok_or_else(invalid_state)?,
                            marker: evidence_marker.ok_or_else(invalid_state)?,
                            provider: resource.provider,
                            span,
                        });
                }
            }
        }
        let provenance = self.at_span_provenance(&ty, span)?;
        Ok(TypedNode {
            node,
            ty: ty.into_inner(),
            effects,
            provenance,
        })
    }

    pub(super) fn provider_instance_result_type(
        &mut self,
        fact: &ResourceTypeFact,
        actuals: &ResourceActuals,
        answer: &Type,
    ) -> Result<Type, TypeError> {
        let mut result = OwnerReplacementBuffer::new();
        for (formal, actual) in fact.parameters.iter().zip(actuals.arguments()) {
            result.insert_cloned(formal.id, actual, &mut self.type_work)?;
        }
        let answer = crate::types::IterativeArgumentOwner::new(KindedArgument::TypeArg(
            self.clone_type(answer)?,
        ));
        result.insert_cloned(fact.answer.id, &answer, &mut self.type_work)?;
        result.substitute(&fact.result.ty, &mut self.type_work)
    }

    /// Interpret each admitted native phase before combining rows. In
    /// particular, this preserves a formal callback tail's established lacks.
    pub(super) fn provider_instance_outward_row(
        &mut self,
        initializer: &EffectRow,
        acquire: &EffectRow,
        finish: &EffectRow,
        handler_output: &EffectRow,
        native: &EffectInstance,
        span: Span,
    ) -> Result<EffectRow, TypeError> {
        let acquire = self.provider_native_phase_row(acquire, native, span)?;
        let finish = self.provider_native_phase_row(finish, native, span)?;
        let output = self.provider_native_phase_row(handler_output, native, span)?;
        let phases = self.union_effects(&acquire, &finish, span)?;
        let completed = self.union_effects(&phases, &output, span)?;
        self.union_effects(initializer, &completed, span)
    }

    pub(super) fn check_provider_instance_escape(
        &mut self,
        resource: &ResolvedProviderResourceExpr,
        ty: &Type,
        effects: &EffectRow,
        context: &TypeContext,
        span: Span,
    ) -> Result<(), TypeError> {
        let row_type = IterativeTypeOwner::new(Type::function_computation(
            Type::Unit,
            ComputationType::new(Type::Unit, self.core_effect_row(effects)?),
        ));
        for (outward, cause) in [(ty, resource.body.span), (&*row_type, span)] {
            self.defer_resource_escape(resource.identity.id, outward, cause, span)?;
            if type_contains_variable(outward, resource.identity.id, &mut self.constraint_work)
                .map_err(|()| constraint_resource())?
            {
                return Err(self.resource_escape_failure(
                    cause,
                    span,
                    "this outward computation contains the resource identity",
                ));
            }
        }
        self.type_work
            .charge(context.binders.capacity())
            .map_err(|()| type_resource())?;
        for fact in context.binders.values() {
            let outer = IterativeTypeOwner::new(self.zonk(&fact.ty)?);
            let cause = fact.provenance.span().unwrap_or(resource.body.span);
            self.defer_resource_escape(resource.identity.id, &outer, cause, span)?;
            if type_contains_variable(&outer, resource.identity.id, &mut self.constraint_work)
                .map_err(|()| constraint_resource())?
            {
                return Err(self.resource_escape_failure(
                    cause,
                    span,
                    "an enclosing binding contains the resource identity",
                ));
            }
        }
        Ok(())
    }

    pub(super) fn schedule_provider_instance<'a>(
        &mut self,
        resource: &'a ResolvedProviderResourceExpr,
        span: Span,
        tasks: &mut ElaborationTaskBuffer<'a>,
    ) -> Result<(), TypeError> {
        if !F::EFFECTS {
            return Err(unsupported_provider_resource());
        }
        self.type_work.charge(2).map_err(|()| type_resource())?;
        tasks.0.try_reserve(2).map_err(|_| type_resource())?;
        tasks.push(ElaborationTask::ProviderInstanceBody { resource, span });
        tasks.push(ElaborationTask::Synthesize {
            expression: &resource.initializer,
            cause: None,
        });
        Ok(())
    }

    /// The initializer value is consumed from the same iterative worklist once.
    /// No source scope binding exists while that initializer is elaborated.
    pub(super) fn step_provider_instance_body<'a>(
        &mut self,
        resource: &'a ResolvedProviderResourceExpr,
        span: Span,
        context: &mut TypeContext,
        tasks: &mut ElaborationTaskBuffer<'a>,
        values: &mut TypedNodeBuffer,
    ) -> Result<(), TypeError> {
        let initializer = values.pop().ok_or_else(invalid_state)?;
        let code = if let Some(local) = self
            .pending_local_provider
            .as_ref()
            .filter(|local| local.module() == resource.definition.module())
        {
            local.original_code(resource.definition, &mut self.type_work)?
        } else {
            self.provider_codes
                .code(resource.definition.module(), &mut self.type_work)?
                .map(provider::PreparedProviderCode::Group)
                .ok_or_else(invalid_state)?
        };
        let source = if self.purpose == ElaborationPurpose::ModuleCheck {
            if let Some(local) = self
                .pending_local_provider
                .as_ref()
                .filter(|local| local.module() == resource.definition.module())
            {
                local.template_source(
                    &code,
                    resource.definition,
                    resource.family,
                    &mut self.type_work,
                )?
            } else {
                code.imported_template_source(
                    resource.definition,
                    resource.family,
                    self.source_provider_contracts
                        .get(&resource.definition.module())
                        .ok_or_else(invalid_state)?,
                    &mut self.type_work,
                )?
            }
        } else {
            code.template_source(
                resource.definition,
                resource.family,
                &self.registry,
                &mut self.type_work,
            )?
        };
        self.type_work.charge(1).map_err(|()| type_resource())?;
        let needs_actual_captures = source.handler.needs_actual_captures();
        let fact = Arc::clone(source.fact);
        let actuals = self.prepare_resource_actuals(resource, &fact, &initializer)?;
        let native = self.prepare_native_scope_actuals(resource, &fact, &actuals, &initializer)?;
        let forwarding = self.prepare_resource_forwardings(resource, &source, &actuals)?;
        let members = self.lower_resource_forwardings(resource, &forwarding)?;
        let evidence_marker = if (needs_actual_captures || source.family.is_some())
            && self.purpose == ElaborationPurpose::ModuleCheck
            && self.selection.is_some()
        {
            Some(self.evidence_marker()?)
        } else {
            None
        };
        let (handle, previous) =
            self.enter_provider_instance_body(resource, &fact, &actuals, &forwarding, context)?;
        self.begin_provider_family_demands(resource, &source, &actuals)?;
        self.type_work.charge(3).map_err(|()| type_resource())?;
        tasks.0.try_reserve(2).map_err(|_| type_resource())?;
        tasks.push(ElaborationTask::FinishProviderInstance(Box::new(
            ProviderInstanceProgress {
                resource,
                span,
                initializer,
                code,
                actuals,
                native,
                forwarding,
                members,
                handle,
                previous,
                evidence_marker,
            },
        )));
        tasks.push(ElaborationTask::Synthesize {
            expression: &resource.body,
            cause: None,
        });
        Ok(())
    }

    /// Installs non-owning access and exact forwarding functions only after
    /// the initializer has been checked in the preceding lexical scope.
    pub(super) fn enter_provider_instance_body(
        &mut self,
        resource: &ResolvedProviderResourceExpr,
        fact: &ResourceTypeFact,
        actuals: &ResourceActuals,
        forwarding: &ProviderForwardings,
        context: &mut TypeContext,
    ) -> Result<(TypedBinder, Option<usize>), TypeError> {
        if !F::EFFECTS || forwarding.methods.len() != resource.forwarding.len() {
            return Err(invalid_state());
        }
        if self.purpose == ElaborationPurpose::ModuleCheck {
            self.type_work
                .charge(forwarding.methods.len())
                .map_err(|()| type_resource())?;
            self.method_capture_binders
                .try_reserve(forwarding.methods.len())
                .map_err(|_| type_resource())?;
            self.method_capture_binders.extend(
                forwarding
                    .methods
                    .iter()
                    .map(|method| (resource.provider, method.method, method.binder)),
            );
        }
        let handle_type = IterativeTypeOwner::new(actuals.access_type(fact, &mut self.type_work)?);
        self.type_work
            .charge(
                forwarding
                    .methods
                    .len()
                    .checked_add(2)
                    .ok_or_else(type_resource)?,
            )
            .map_err(|()| type_resource())?;
        context
            .binders
            .try_reserve(
                forwarding
                    .methods
                    .len()
                    .checked_add(1)
                    .ok_or_else(type_resource)?,
            )
            .map_err(|_| type_resource())?;
        let provenance =
            self.at_span_provenance(&handle_type, resource.handle.origin.primary_span())?;
        let handle_fact = self.clone_type(&handle_type)?;
        if context.insert_with_provenance(resource.handle.id, handle_fact, provenance)? {
            return Err(invalid_state());
        }
        for (method, source) in forwarding.methods.iter().zip(resource.forwarding.iter()) {
            let ty = self.clone_type(&method.ty)?;
            let provenance = self.at_span_provenance(&ty, source.binder.origin.primary_span())?;
            if context.insert_with_provenance(method.binder, ty, provenance)? {
                return Err(invalid_state());
            }
        }
        let previous = self
            .selection
            .as_ref()
            .and_then(EvidenceSelector::lexical_head);
        if let Some(selector) = self.selection.as_mut() {
            let application = forwarding
                .application
                .clone_with_budget(&mut self.type_work)
                .map_err(|()| type_resource())?;
            selector
                .add_lexical_source(
                    resource.provider,
                    application,
                    resource.origin.primary_span(),
                    &mut self.constraint_work,
                )
                .map_err(|error| selection_failure(error, Some(resource.origin.primary_span())))?;
        }
        if let Some(lowering) = self.evidence_lowering.as_mut() {
            self.constraint_work
                .charge(forwarding.methods.len())
                .map_err(|()| constraint_resource())?;
            lowering
                .lexical_binders
                .try_reserve(forwarding.methods.len())
                .map_err(|_| constraint_resource())?;
            for method in &forwarding.methods {
                let application = forwarding
                    .application
                    .clone_with_budget(&mut self.type_work)
                    .map_err(|()| type_resource())?;
                let ty = crate::types::clone_type_with_budget(&method.ty, &mut self.type_work)
                    .map_err(|()| type_resource())?;
                if lowering
                    .lexical_binders
                    .insert(
                        (resource.provider, method.method),
                        ActiveEvidenceBinder {
                            binder: method.binder,
                            application,
                            ty,
                        },
                    )
                    .is_some()
                {
                    return Err(invalid_state());
                }
            }
        }
        let handle = self.builder.resolved_binder(
            resource.handle.id,
            handle_type.into_inner(),
            resource.handle.origin.clone(),
        )?;
        Ok((handle, previous))
    }

    pub(super) fn leave_provider_instance_body(
        &mut self,
        resource: &ResolvedProviderResourceExpr,
        previous: Option<usize>,
        context: &mut TypeContext,
    ) -> Result<(), TypeError> {
        self.constraint_work
            .charge(
                resource
                    .forwarding
                    .len()
                    .checked_add(1)
                    .ok_or_else(constraint_resource)?,
            )
            .map_err(|()| constraint_resource())?;
        if !context.remove_and_discard(resource.handle.id) {
            return Err(invalid_state());
        }
        for source in &resource.forwarding {
            if !context.remove_and_discard(source.binder.id) {
                return Err(invalid_state());
            }
            if let Some(lowering) = self.evidence_lowering.as_mut()
                && lowering
                    .lexical_binders
                    .remove(&(resource.provider, source.method))
                    .is_none()
            {
                return Err(invalid_state());
            }
        }
        if let Some(selector) = self.selection.as_mut() {
            selector.restore_lexical_head(previous);
        }
        Ok(())
    }

    /// Emits ordinary unary Ash functions for the already checked exact
    /// method/operation associations. The surrounding scope installs their
    /// binders only in its body; these functions contain no native owner.
    pub(super) fn lower_resource_forwardings(
        &mut self,
        resource: &ResolvedProviderResourceExpr,
        forwardings: &ProviderForwardings,
    ) -> Result<Vec<(TypedBinder, NodeId)>, TypeError> {
        if !F::EFFECTS || forwardings.methods.len() != resource.forwarding.len() {
            return Err(invalid_state());
        }
        self.type_work
            .charge(forwardings.methods.len())
            .map_err(|()| type_resource())?;
        let mut members = Vec::new();
        members
            .try_reserve_exact(forwardings.methods.len())
            .map_err(|_| type_resource())?;
        for (method, source) in forwardings.methods.iter().zip(resource.forwarding.iter()) {
            if method.method != source.method || method.binder != source.binder.id {
                return Err(invalid_state());
            }
            let function = method.ty.function_view().ok_or_else(invalid_state)?;
            let domain = IterativeTypeOwner::new(self.clone_type(function.domain())?);
            let value = IterativeTypeOwner::new(self.clone_type(function.value())?);
            let row = function.effects().ok_or_else(invalid_state)?;
            let parameter = self.builder.resolved_binder(
                source.parameter.id,
                domain.into_inner(),
                source.parameter.origin.clone(),
            )?;
            let operand_type = self.clone_type(parameter.ty())?;
            let operand = self.builder.variable(
                parameter.id(),
                operand_type,
                source.parameter.origin.clone(),
            )?;
            let effect = crate::types::clone_effect_instance_with_budget(
                &forwardings.effect,
                &mut self.type_work,
            )
            .map_err(|()| type_resource())?;
            let effects = self.core_effect_row(row)?;
            let request = self.push_effect_core(
                value.into_inner(),
                effects,
                source.binder.origin.clone(),
                EffectOperation::Request(RequestNode::new(effect, method.operation, operand)),
            )?;
            let function_type = self.clone_type(&method.ty)?;
            let function = self.builder.function(
                parameter,
                request,
                function_type,
                source.binder.origin.clone(),
            )?;
            let binder_type = self.clone_type(&method.ty)?;
            let binder = self.builder.resolved_binder(
                method.binder,
                binder_type,
                source.binder.origin.clone(),
            )?;
            members.push((binder, function));
        }
        Ok(members)
    }

    /// Derives forwarding types from the original checked association and one
    /// complete actual vector. No method name or implementation search occurs.
    pub(super) fn prepare_resource_forwardings(
        &mut self,
        resource: &ResolvedProviderResourceExpr,
        source: &super::provider::ProviderTemplateSource<'_>,
        actuals: &ResourceActuals,
    ) -> Result<ProviderForwardings, TypeError> {
        let fact = &**source.fact;
        if fact.id != resource.definition
            || fact.family != resource.family
            || source.methods.len() != resource.forwarding.len()
        {
            return Err(invalid_state());
        }
        let count = fact.provider_application.arguments().len();
        self.type_work.charge(count).map_err(|()| type_resource())?;
        let mut arguments = Vec::new();
        arguments
            .try_reserve_exact(count)
            .map_err(|_| type_resource())?;
        for argument in fact.provider_application.arguments() {
            let copied = crate::types::substitute_kinded_argument_with(
                argument,
                actuals.replacements.types.as_map(),
                &actuals.replacements.rows,
                |units| self.type_work.charge(units),
            )
            .map_err(|()| type_resource())?
            .map_err(|_| invalid_state())?;
            arguments.push(crate::types::IterativeArgumentOwner::new(copied));
        }
        self.type_work.charge(count).map_err(|()| type_resource())?;
        let mut retained = Vec::new();
        retained
            .try_reserve_exact(count)
            .map_err(|_| type_resource())?;
        retained.extend(
            arguments
                .into_iter()
                .map(crate::types::IterativeArgumentOwner::into_inner),
        );
        let application = InterfaceApplication::new_kinded(
            fact.provider_application.interface(),
            retained.into_boxed_slice(),
        );
        let template_effect = EffectRow::singleton(
            crate::types::clone_effect_instance_with_budget(
                &fact.provided.instance,
                &mut self.type_work,
            )
            .map_err(|()| type_resource())?,
        );
        let substituted = actuals
            .replacements
            .substitute_row(&template_effect, &mut self.type_work)?;
        if substituted.tail().is_some() || substituted.known().len() != 1 {
            return Err(invalid_state());
        }
        let effect = crate::types::clone_effect_instance_with_budget(
            substituted.known().first().ok_or_else(invalid_state)?,
            &mut self.type_work,
        )
        .map_err(|()| type_resource())?;
        self.type_work
            .charge(source.methods.len())
            .map_err(|()| type_resource())?;
        let mut methods = Vec::new();
        methods
            .try_reserve_exact(source.methods.len())
            .map_err(|_| type_resource())?;
        for ((method, operation), forwarding) in
            source.methods.iter().zip(resource.forwarding.iter())
        {
            if *method != forwarding.method || operation.owner() != effect.effect() {
                return Err(invalid_state());
            }
            let (domain, result) =
                self.operation_signature(&effect, *operation, resource.origin.primary_span())?;
            let result = IterativeTypeOwner::new(result);
            let domain = IterativeTypeOwner::new(domain);
            let effects = EffectRow::singleton(
                crate::types::clone_effect_instance_with_budget(&effect, &mut self.type_work)
                    .map_err(|()| type_resource())?,
            );
            self.type_work.charge(1).map_err(|()| type_resource())?;
            methods.push(ProviderForwarding {
                method: *method,
                operation: *operation,
                binder: forwarding.binder.id,
                ty: IterativeTypeOwner::new(Type::function_computation(
                    domain.into_inner(),
                    ComputationType::new(result.into_inner(), effects),
                )),
            });
        }
        Ok(ProviderForwardings {
            application,
            effect,
            methods,
        })
    }

    /// Checks the already typed initializer; this function never elaborates it
    /// again or selects a provider implementation. Remaining identities follow
    /// the initializer's type through ordinary kind-preserving unification.
    pub(super) fn prepare_resource_actuals(
        &mut self,
        resource: &ResolvedProviderResourceExpr,
        fact: &ResourceTypeFact,
        initializer: &TypedNode,
    ) -> Result<ResourceActuals, TypeError> {
        if resource.definition != fact.id
            || resource.family != fact.family
            || resource.identity.kind != Kind::Type
            || fact
                .parameters
                .first()
                .is_none_or(|parameter| parameter.kind != Kind::Type)
        {
            return Err(invalid_state());
        }
        self.registry
            .authenticate_owner_signature(
                crate::resolved::OwnerId::Resource(fact.id),
                Some(fact.family),
                &fact.parameters,
                &mut self.type_work,
            )
            .map_err(resolved_build_error)?;

        let mut types = OwnedTypeBuffer(Vec::new());
        let mut rows = Vec::new();
        let count = fact.parameters.len();
        self.type_work
            .charge(count.checked_mul(2).ok_or_else(type_resource)?)
            .map_err(|()| type_resource())?;
        types
            .0
            .try_reserve_exact(count)
            .map_err(|_| type_resource())?;
        rows.try_reserve_exact(count).map_err(|_| type_resource())?;
        types.0.push(Type::Variable(resource.identity.id));

        if let Some(written) = &resource.arguments {
            if written.len().checked_add(1) != Some(count) {
                return Err(invalid_state());
            }
            for (argument, parameter) in written.iter().zip(fact.parameters.iter().skip(1)) {
                match (&argument.ty, &parameter.kind) {
                    (KindedArgument::RowArg(_), Kind::EffectRow) => {}
                    (KindedArgument::TypeArg(_), kind) if !matches!(kind, Kind::EffectRow) => {}
                    _ => return Err(invalid_state()),
                }
                let qualified =
                    crate::types::qualify_kinded_argument_with_expected_row_with_budget(
                        &argument.ty,
                        self.expected_effect_rows.last(),
                        &mut self.type_work,
                    )
                    .map_err(|()| type_resource())?
                    .map_err(|_| invalid_state())?
                    .map(crate::types::IterativeArgumentOwner::new);
                let argument = qualified
                    .as_ref()
                    .map_or(&argument.ty, |owner| owner.as_ref());
                match (argument, &parameter.kind) {
                    (KindedArgument::RowArg(row), Kind::EffectRow) => {
                        rows.push(self.zonk_effect_row(row)?);
                    }
                    (KindedArgument::TypeArg(ty), kind) if !matches!(kind, Kind::EffectRow) => {
                        types.0.push(self.zonk(ty)?);
                    }
                    _ => return Err(invalid_state()),
                }
            }
        } else {
            for parameter in fact.parameters.iter().skip(1) {
                if matches!(parameter.kind, Kind::EffectRow) {
                    return Err(invalid_state());
                }
                types.0.push(
                    self.fresh_inference(
                        &parameter.kind,
                        initializer
                            .provenance
                            .span()
                            .unwrap_or(resource.initializer.span),
                    )?,
                );
            }
        }

        let arguments = OwnedArgumentBuffer::retain_defining_actuals(
            &fact.parameters,
            &types.0,
            &rows,
            &mut self.type_work,
        )?;
        let mut actuals = ResourceActuals {
            arguments,
            replacements: OwnerReplacementBuffer::new(),
        };
        for (parameter, argument) in fact.parameters.iter().zip(actuals.arguments.iter()) {
            actuals
                .replacements
                .insert_cloned(parameter.id, argument, &mut self.type_work)?;
        }
        let input = IterativeTypeOwner::new(
            actuals
                .replacements
                .substitute(&fact.input.ty, &mut self.type_work)?,
        );
        match self.unify(&input, &initializer.ty) {
            Ok(()) => {}
            Err(UnificationFailure::Mismatch) => {
                let expected = IterativeTypeOwner::new(self.zonk(&input)?);
                let found = IterativeTypeOwner::new(self.zonk(&initializer.ty)?);
                return Err(check_mismatch(
                    CheckKind::General,
                    resource.initializer.span,
                    expected.into_inner(),
                    found.into_inner(),
                    Some(fact.input.span),
                    &self.registry,
                ));
            }
            Err(UnificationFailure::Infinite) => {
                return Err(inference_failure(
                    TypeReason::InfiniteType,
                    resource.initializer.span,
                    "this initializer would require an infinite resource argument",
                ));
            }
            Err(UnificationFailure::RowExclusion) => {
                return Err(row_exclusion_error(
                    resource.initializer.span,
                    Some(fact.input.span),
                ));
            }
            Err(UnificationFailure::Kind { context, span }) => {
                return Err(TypeError::Internal(ElaborationFailure::Kind {
                    context,
                    span,
                }));
            }
            Err(UnificationFailure::Resource) => return Err(type_resource()),
            Err(UnificationFailure::Invariant) => return Err(invalid_state()),
        }

        // Rebuild the same ordered vector after inference. Formal open rows
        // stay open; only unresolved inference variables are ambiguous.
        for argument in actuals.arguments.iter_mut().skip(1) {
            let zonked = match argument {
                KindedArgument::TypeArg(ty) => {
                    let (ty, ambiguous) = self.zonk_with_status(ty)?;
                    let ty = IterativeTypeOwner::new(ty);
                    if ambiguous {
                        return Err(inference_failure(
                            TypeReason::AmbiguousType,
                            resource.initializer.span,
                            "this initializer does not determine every resource argument",
                        ));
                    }
                    KindedArgument::TypeArg(ty.into_inner())
                }
                KindedArgument::RowArg(row) => KindedArgument::RowArg(self.zonk_effect_row(row)?),
            };
            let zonked = crate::types::IterativeArgumentOwner::new(zonked);
            let qualified = crate::types::qualify_kinded_argument_with_expected_row_with_budget(
                zonked.as_ref(),
                self.expected_effect_rows.last(),
                &mut self.type_work,
            )
            .map_err(|()| type_resource())?
            .map_err(|_| invalid_state())?;
            let qualified = qualified.unwrap_or_else(|| zonked.into_inner());
            crate::types::discard_kinded_argument_iteratively(std::mem::replace(
                argument, qualified,
            ));
            let ambiguous = crate::types::visit_argument_structure_with_budget(
                argument,
                &mut self.type_work,
                |node, _| {
                    Ok(match node {
                        TypeStructureNode::Type(Type::Inference(_)) => true,
                        TypeStructureNode::Tail(tail) => {
                            matches!(tail.variable(), EffectRowVariable::Inference(_))
                        }
                        _ => false,
                    })
                },
            )
            .map_err(|()| type_resource())?;
            if ambiguous {
                return Err(inference_failure(
                    TypeReason::AmbiguousType,
                    resource.initializer.span,
                    "this initializer does not determine every resource argument",
                ));
            }
            let forbidden = crate::types::visit_argument_structure_with_budget(
                argument,
                &mut self.type_work,
                |node, _| {
                    Ok(match node {
                        TypeStructureNode::Type(Type::Variable(id)) => *id == resource.identity.id,
                        TypeStructureNode::Tail(tail) => matches!(tail.variable(),
                        EffectRowVariable::Rigid(id) if id == resource.identity.id),
                        _ => false,
                    })
                },
            )
            .map_err(|()| type_resource())?;
            if forbidden {
                return Err(self.resource_escape_failure(
                    resource.initializer.span,
                    resource.identity.origin.primary_span(),
                    "a resource argument contains the identity introduced only for its body",
                ));
            }
        }
        let typed_input = IterativeTypeOwner::new(self.zonk(&initializer.ty)?);
        if type_contains_variable(
            &typed_input,
            resource.identity.id,
            &mut self.constraint_work,
        )
        .map_err(|()| constraint_resource())?
        {
            return Err(self.resource_escape_failure(
                resource.initializer.span,
                resource.identity.origin.primary_span(),
                "this initializer contains the identity introduced only for the resource body",
            ));
        }
        let mut replacements = OwnerReplacementBuffer::new();
        for (parameter, argument) in fact.parameters.iter().zip(actuals.arguments.iter()) {
            replacements.insert_cloned(parameter.id, argument, &mut self.type_work)?;
        }
        actuals.replacements = replacements;
        Ok(actuals)
    }

    /// Derives retained owner coordinates from the original native acquisition
    /// contract and the already typed initializer. Ordinary free type variables
    /// do not become owners merely by occurring in the source argument vector.
    pub(super) fn prepare_native_scope_actuals(
        &mut self,
        resource: &ResolvedProviderResourceExpr,
        fact: &ResourceTypeFact,
        actuals: &ResourceActuals,
        initializer: &TypedNode,
    ) -> Result<NativeScopeActuals, TypeError> {
        let state = IterativeTypeOwner::new(
            actuals
                .replacements
                .substitute(&fact.state.ty, &mut self.type_work)?,
        );
        let state_family = state.outer_nominal().ok_or_else(invalid_state)?;
        self.type_work.charge(1).map_err(|()| type_resource())?;
        let mut source_interpretation = Vec::new();
        source_interpretation
            .try_reserve_exact(1)
            .map_err(|_| type_resource())?;
        source_interpretation.push(
            crate::types::clone_effect_instance_with_budget(
                &fact.interpreted.instance,
                &mut self.type_work,
            )
            .map_err(|()| type_resource())?,
        );
        let interpreted = actuals.replacements.substitute_row(
            &EffectRow::closed(source_interpretation.into_boxed_slice()),
            &mut self.type_work,
        )?;
        let [effect] = interpreted.known() else {
            return Err(invalid_state());
        };
        if interpreted.tail().is_some() {
            return Err(invalid_state());
        }
        let effect = crate::types::clone_effect_instance_with_budget(effect, &mut self.type_work)
            .map_err(|()| type_resource())?;

        let mut native = None;
        for candidate in self.registry.foreign_modules() {
            self.type_work
                .charge(
                    candidate
                        .effects
                        .len()
                        .checked_add(1)
                        .ok_or_else(type_resource)?,
                )
                .map_err(|()| type_resource())?;
            if candidate.effects.contains(&effect.effect())
                && native.replace(Arc::clone(candidate)).is_some()
            {
                return Err(invalid_state());
            }
        }
        let native = native.ok_or_else(invalid_state)?;
        native.authenticate(&mut self.type_work).map_err(|error| {
            if error.is_resource_exhaustion() {
                type_resource()
            } else {
                invalid_state()
            }
        })?;
        self.type_work
            .charge(native.states.len())
            .map_err(|()| type_resource())?;
        let state_fact = native
            .states
            .iter()
            .find(|entry| entry.id == state_family)
            .ok_or_else(invalid_state)?;
        let (_, state_arguments) = provider::nominal_arguments(&state, &mut self.type_work)?;
        if state_arguments.len() != state_fact.parameter_count
            || !matches!(state_arguments.get(state_fact.owned_identity_position),
                Some(Type::Variable(identity)) if *identity == resource.identity.id)
        {
            return Err(invalid_state());
        }
        let width = effect.arguments().len();
        self.type_work.charge(width).map_err(|()| type_resource())?;
        let mut retained_positions = Vec::new();
        retained_positions
            .try_reserve_exact(width)
            .map_err(|_| type_resource())?;
        retained_positions.resize(width, false);
        let mut acquired = false;
        for operation in &native.operations {
            self.type_work.charge(1).map_err(|()| type_resource())?;
            if operation.id.owner() != effect.effect() {
                continue;
            }
            let crate::foreign::ForeignResultFact::Acquire {
                state: acquired_state,
                retained_parameters,
                ..
            } = &operation.result
            else {
                continue;
            };
            if *acquired_state != state_family {
                continue;
            }
            if !matches!(effect.arguments().get(operation.owned_identity_position),
                    Some(KindedArgument::TypeArg(Type::Variable(identity))) if *identity == resource.identity.id)
            {
                return Err(invalid_state());
            }
            acquired = true;
            self.type_work
                .charge(retained_parameters.len())
                .map_err(|()| type_resource())?;
            for position in retained_parameters {
                *retained_positions
                    .get_mut(*position)
                    .ok_or_else(invalid_state)? = true;
            }
        }
        if !acquired {
            return Err(invalid_state());
        }
        self.type_work.charge(width).map_err(|()| type_resource())?;
        let count = retained_positions
            .iter()
            .filter(|retained| **retained)
            .count();
        self.type_work.charge(count).map_err(|()| type_resource())?;
        let mut retained = Vec::new();
        retained
            .try_reserve_exact(count)
            .map_err(|_| type_resource())?;
        let typed_input = IterativeTypeOwner::new(self.zonk(&initializer.ty)?);
        self.type_work.charge(width).map_err(|()| type_resource())?;
        for (position, required) in retained_positions.into_iter().enumerate() {
            if !required {
                continue;
            }
            let Some(KindedArgument::TypeArg(Type::Variable(identity))) =
                effect.arguments().get(position)
            else {
                return Err(invalid_state());
            };
            self.type_work
                .charge(retained.len())
                .map_err(|()| type_resource())?;
            if *identity == resource.identity.id
                || !type_contains_variable(&typed_input, *identity, &mut self.constraint_work)
                    .map_err(|()| constraint_resource())?
            {
                return Err(self.resource_escape_failure(
                    resource.initializer.span,
                    fact.origin.primary_span(),
                    "a retained native owner is not supplied by this typed initializer",
                ));
            }
            if !retained.contains(identity) {
                retained.push(*identity);
            }
        }
        Ok(NativeScopeActuals {
            native,
            effect,
            retained: retained.into_boxed_slice(),
        })
    }
}

fn retain_original_template_slots(
    occurrences: &[super::provider::CheckedGlobalOccurrence],
    work: &mut TypeWorkBudget,
) -> Result<Vec<crate::interface::EvidenceSlot>, TypeError> {
    work.charge(occurrences.len())
        .map_err(|()| type_resource())?;
    let count = occurrences
        .iter()
        .try_fold(0usize, |count, occurrence| {
            count.checked_add(occurrence.occurrence.evidence.len())
        })
        .ok_or_else(type_resource)?;
    work.charge(count).map_err(|()| type_resource())?;
    let mut slots = Vec::new();
    slots
        .try_reserve_exact(count)
        .map_err(|_| type_resource())?;
    for occurrence in occurrences {
        for slot in &occurrence.occurrence.evidence {
            if slot.selection().is_none() {
                return Err(invalid_state());
            }
            slots.push(slot.clone());
        }
    }
    Ok(slots)
}

fn retain_original_handler_slots(
    original: &crate::core::validate::CheckedHandlerTemplate,
    work: &mut TypeWorkBudget,
) -> Result<Vec<crate::interface::EvidenceSlot>, TypeError> {
    let mut slots = HashMap::new();
    for slot in original.original_evidence_slots() {
        work.charge(1).map_err(|()| type_resource())?;
        if slot.selection().is_none() { return Err(invalid_state()); }
        slots.try_reserve(1).map_err(|_| type_resource())?;
        if slots.insert(slot.storage_id(), slot).is_some() { return Err(invalid_state()); }
    }
    let catalog = original.original_program().method_evidence();
    work.charge(catalog.occurrences().len()).map_err(|()| type_resource())?;
    if slots.len() != catalog.occurrences().len() { return Err(invalid_state()); }
    let mut ordered = Vec::new();
    ordered.try_reserve_exact(slots.len()).map_err(|_| type_resource())?;
    for occurrence in catalog.occurrences() {
        ordered.push(slots.remove(&occurrence.slot).ok_or_else(invalid_state)?.clone());
    }
    if !slots.is_empty() { return Err(invalid_state()); }
    Ok(ordered)
}

#[cfg(test)]
mod actual_capture_tests {
    #[test]
    fn deferred_provider_closure_failures_keep_original_slots_private_and_fresh_retry_succeeds() {
        use crate::{
            module::{ModuleRoots, load_module_graph},
            resolve::{DependencyExports, resolve_module},
            resolved::{CheckedModule, ResolvedDefinitionKind, ResolvedExprKind},
        };
        use std::sync::atomic::{AtomicU64, Ordering};
        static NEXT: AtomicU64 = AtomicU64::new(0);
        struct Tree(std::path::PathBuf);
        impl Drop for Tree {
            fn drop(&mut self) {
                let _ = std::fs::remove_dir_all(&self.0);
            }
        }
        let tree = Tree(std::env::temp_dir().join(format!(
            "ash-deferred-provider-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        )));
        std::fs::create_dir(&tree.0).unwrap();
        let fixtures = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/provider-experiments/control-source");
        for entry in std::fs::read_dir(fixtures).unwrap() {
            let entry = entry.unwrap();
            std::fs::copy(entry.path(), tree.0.join(entry.file_name())).unwrap();
        }
        let entry = tree.0.join("deferred.ash");
        let compile = |source: &str, should_succeed: bool, unknown: bool| {
            std::fs::write(&entry, source).unwrap();
            let registrations = crate::foreign::ForeignRegistrations::new([
                crate::foreign::provider_manifest(crate::module::ForeignRegistrationId::new(1))
                    .unwrap(),
                crate::foreign::sqlite_manifest(crate::module::ForeignRegistrationId::new(2))
                    .unwrap(),
            ])
            .unwrap();
            let graph = load_module_graph(
                &entry,
                &ModuleRoots::empty().with_foreign_registrations(registrations),
            )
            .unwrap();
            let mut checked: Vec<CheckedModule> = Vec::new();
            let mut availability = crate::elaborate::ProviderCodeAvailability::default();
            let mut checking = crate::types::TypeWorkBudget::default();
            let mut coverage = crate::pattern::UsefulnessBudget::default();
            let mut constraints = crate::interface::InterfaceConstraintBudget::default();
            let mut observed = false;
            for loaded in graph.modules() {
                let dependencies = loaded
                    .dependencies()
                    .iter()
                    .map(|edge| {
                        DependencyExports::new(
                            edge,
                            checked
                                .iter()
                                .find(|module| module.module() == edge.target())
                                .unwrap()
                                .exports(),
                        )
                        .unwrap()
                    })
                    .collect::<Vec<_>>();
                let resolved = resolve_module(loaded, &dependencies).unwrap();
                if loaded.id() != graph.entry() {
                    let module = crate::elaborate::check_module_with_budget_and_provider_codes(
                        resolved,
                        &availability,
                        &mut checking,
                        &mut coverage,
                        &mut constraints,
                    )
                    .unwrap();
                    if let Some(code) = module.provider_code() {
                        availability
                            .retain(module.module(), code, &mut checking)
                            .unwrap();
                    }
                    checked.push(module);
                    continue;
                }
                observed = true;
                let selected = resolved
                    .definitions()
                    .iter()
                    .find_map(|definition| {
                        let ResolvedDefinitionKind::Equational(group) = &definition.kind else {
                            return None;
                        };
                        (group.interface.name.spelling == if unknown { "client" } else { "main" })
                            .then_some(&group.equations[0].body)
                    })
                    .unwrap();
                let body = if let ResolvedExprKind::Handle(handler) = &selected.kind {
                    handler.body.as_ref()
                } else {
                    selected
                };
                let ResolvedExprKind::ProviderResource(resource) = &body.kind else {
                    panic!("exact typed source resource occurrence");
                };
                let slot = resource.prepared.retain_for_test();
                let mut work = crate::types::TypeWorkBudget::unbounded();
                let evidence =
                    crate::elaborate::module_bodies::ordinary_source_occurrences_for_test(
                        selected, &mut work,
                    )
                    .unwrap()
                    .iter()
                    .flat_map(|occurrence| occurrence.evidence.iter())
                    .map(|slot| slot.retain_unpublished().unwrap())
                    .collect::<Vec<_>>();
                assert!(!evidence.is_empty());
                let result = crate::elaborate::check_module_with_budget_and_provider_codes(
                    resolved,
                    &availability,
                    &mut checking,
                    &mut coverage,
                    &mut constraints,
                );
                if should_succeed {
                    let checked = result.unwrap();
                    assert!(slot.get().is_some());
                    assert!(evidence.iter().all(|slot| slot.selection().is_some()));
                    drop(checked);
                } else {
                    let Err(error) = result else {
                        panic!("bounded closure refusal required");
                    };
                    if !unknown {
                        assert!(
                            matches!(error, crate::elaborate::TypeError::Interface(_)),
                            "{error:?}"
                        );
                    } else {
                        assert!(
                            matches!(
                                error,
                                crate::elaborate::TypeError::Internal(
                                    crate::elaborate::ElaborationFailure::InvalidState
                                )
                            ),
                            "{error:?}"
                        );
                    }
                    assert!(slot.get().is_none());
                    assert!(evidence.iter().all(|slot| slot.selection().is_none()));
                }
            }
            assert!(observed);
        };
        let header = "import @foreign.sqlite as Native\nimport provider as Provider\nimport capture_library as Library\ninterface Make<A> {\nmake : Unit -> A\n}\n";
        let positive = format!(
            "{header}impl Make<Int> {{\nmake ignored = 42\n}}\nmain : Unit -> Provider.Scope<Native.OpenError, Native.CloseError, Int>\nmain ignored = handle (resource Library.Probe<P> db = Native.InMemory {{\nlet ignored = Library.probe (db, Library.without_owner)\nmake ()\n}}) with Library.H {{\nop ignored => resume ()\n}}\n"
        );
        compile(
            &positive
                .replace("impl Make<Int>", "impl Make<Bool>")
                .replace("make ignored = 42", "make ignored = true"),
            false,
            false,
        );
        compile(&positive, true, false);
        let unknown = format!(
            "{header}impl Make<Int> {{\nmake ignored = 42\n}}\nclient : (Unit -> Unit ! {{Library.Stop, Library.H}}) -> Provider.Scope<Native.OpenError, Native.CloseError, Int> ! {{Library.H}}\nclient callback = resource Library.Probe<P> db = Native.InMemory {{\nlet ignored = Library.probe (db, callback)\nmake ()\n}}\nmain : Unit -> Provider.Scope<Native.OpenError, Native.CloseError, Int>\nmain ignored = handle (client Library.without_owner) with Library.H {{\nop ignored => resume ()\n}}\n"
        );
        compile(&unknown, false, true);
        compile(&positive, true, false);
    }

    #[test]
    fn actual_request_receipts_distinguish_equal_sigma_epsilon_and_reconstruct_final_core() {
        use crate::{
            module::{ModuleRoots, load_module_graph},
            resolve::{DependencyExports, resolve_module},
            resolved::{CheckedModule, ResolvedDefinitionKind, ResolvedExprKind},
        };
        let entry = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/provider-experiments/control-source/capture-demand.ash");
        let registrations = crate::foreign::ForeignRegistrations::new([
            crate::foreign::provider_manifest(crate::module::ForeignRegistrationId::new(1))
                .unwrap(),
            crate::foreign::sqlite_manifest(crate::module::ForeignRegistrationId::new(2)).unwrap(),
        ])
        .unwrap();
        let graph = load_module_graph(
            &entry,
            &ModuleRoots::empty().with_foreign_registrations(registrations),
        )
        .unwrap();
        let mut checked: Vec<CheckedModule> = Vec::new();
        let mut observed = false;
        for loaded in graph.modules() {
            let dependencies = loaded
                .dependencies()
                .iter()
                .map(|edge| {
                    DependencyExports::new(
                        edge,
                        checked
                            .iter()
                            .find(|module| module.module() == edge.target())
                            .unwrap()
                            .exports(),
                    )
                    .unwrap()
                })
                .collect::<Vec<_>>();
            let module =
                crate::elaborate::check_module(resolve_module(loaded, &dependencies).unwrap())
                    .unwrap();
            for definition in module.definitions() {
                let ResolvedDefinitionKind::Equational(definition) = definition.kind() else {
                    continue;
                };
                if definition.interface.name.spelling != "both" {
                    continue;
                }
                let ResolvedExprKind::ProviderResource(resource) =
                    &definition.equations[0].body.kind
                else {
                    panic!("exact Probe instance body")
                };
                let prepared = resource
                    .prepared
                    .get()
                    .expect("actual source request proof");
                let h = module
                    .effects()
                    .iter()
                    .find(|effect| effect.spelling == "H")
                    .unwrap()
                    .id;
                prepared
                    .handler_rows
                    .assert_distinct_actual_captures_for_test(h);
                observed = true;
            }
            checked.push(module);
        }
        assert!(observed, "the canonical library instance was checked");
        let linked = crate::elaborate::link_modules(checked, graph.entry()).unwrap();
        let validated = crate::validate_linked_facts_for_test(linked).unwrap();
        let mut elaborator =
            crate::elaborate::EffectElaborator::for_module_program(&validated).unwrap();
        let typed = elaborator
            .synthesize_effect_module_program(&validated)
            .unwrap();
        let core = elaborator.finish(typed.node).unwrap();
        let sources = graph
            .modules()
            .iter()
            .map(|module| module.source())
            .collect::<Vec<_>>();
        let module_sources = graph
            .modules()
            .iter()
            .map(|module| (module.id(), module.source().id()))
            .collect::<Vec<_>>();
        crate::core::validate_effect_modules(core, &sources, &module_sources).expect(
            "independent final executable reconstruction of the original ports and actual c",
        );
    }
}
