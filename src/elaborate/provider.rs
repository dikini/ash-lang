//! Declaration checking for the bounded source-provider experiment.

#[path = "provider_external.rs"]
mod external;
use external::StagedProviderExternals;

use super::{
    Arc, BinderId, BuildError, CheckedEffectClause, CoreElaborator, CoreLoweringFamily,
    CorePattern, EffectOperation, EffectRow, EffectRowVariable, ElaborationFailure,
    ElaborationTask, EvidenceSelector, HashMap, HashSet, IterativeTypeOwner, Kind, MethodId,
    Origin, PendingEvidencePublication, RefCell, ResolvedExpr, ResolvedExprKind, ResolvedModule,
    Span, Type, TypeError, TypeReason, TypeVariableId, TypeWorkBudget, TypedNode, TypedNodeOwner,
    UnificationFailure, clone_effect_instance_with_budget, clone_effect_row_with_budget,
    clone_kind_with_budget, clone_kinded_type_parameters_with_budget, clone_type_with_budget,
    compare_effect_instances_with_budget, constraint_resource, discard_origin_iteratively,
    discard_type_iteratively, first_invalid_handler_operation_with_budget,
    foreign_privilege_unavailable, inference_failure, invalid_state, provider, provider_globals,
    reserve_context_entry, row_exclusion_error, same_type_with_budget, selection_failure,
    type_resource,
};
#[cfg(test)]
use super::{
    CheckedModule, CorePatternKind, EffectElaborator, InterfaceConstraintBudget, InterfaceReason,
    ResolvedPatternKind, UsefulnessBudget, check_module,
};
use super::{OwnedTypeBuffer, OwnerReplacementBuffer};
use crate::core::{CoreBuilder, EffectOperationFamily, NodeId, TypedBinder, effect::HandlerId};
use crate::{
    foreign::ForeignResultFact,
    module::ForeignOperationRole,
    resolved::{ProviderTemplateId, ResolvedResourceDefinition},
    types::{ComputationType, ConstructorId, NominalTypeId, OperationId},
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Phase {
    Acquire,
    Finish,
    Handler,
}

/// Checker entry context. Core admission must independently reconstruct this
/// relation and native postconditions; this context is not a Core certificate.
#[derive(Debug)]
pub(super) struct CheckingContext {
    native: crate::types::EffectInstance,
    phase: Phase,
    operations: Box<[OperationId]>,
    state_associations: Vec<HeaderStateAssociation>,
}

/// Header association for unpublished local drafts only. It cannot authorize
/// an imported template, publish code or supply a runtime activation.
struct HeaderStateAssociation {
    definition: crate::resolved::ResourceDefinitionId,
    family: NominalTypeId,
    parameters: Box<[TypeVariableId]>,
    state: IterativeTypeOwner,
}

impl std::fmt::Debug for HeaderStateAssociation {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("HeaderStateAssociation")
            .field("definition", &self.definition)
            .field("family", &self.family)
            .field("parameters", &self.parameters)
            .field("state_nominal", &self.state.outer_nominal())
            .finish_non_exhaustive()
    }
}

impl HeaderStateAssociation {
    fn clone_with_budget(&self, work: &mut TypeWorkBudget) -> Result<Self, TypeError> {
        work.charge(self.parameters.len())
            .map_err(|()| type_resource())?;
        let mut parameters = Vec::new();
        parameters
            .try_reserve_exact(self.parameters.len())
            .map_err(|_| type_resource())?;
        parameters.extend_from_slice(&self.parameters);
        Ok(Self {
            definition: self.definition,
            family: self.family,
            parameters: parameters.into_boxed_slice(),
            state: IterativeTypeOwner::new(
                clone_type_with_budget(&self.state, work).map_err(|()| type_resource())?,
            ),
        })
    }
}

impl<F: CoreLoweringFamily> CoreElaborator<F> {
    pub(super) fn is_provider_state_access(&mut self, method: MethodId) -> Result<bool, TypeError> {
        for module in self.registry.foreign_modules() {
            self.type_work.charge(1).map_err(|()| type_resource())?;
            if let Some(access) = &module.state_access {
                self.type_work.charge(1).map_err(|()| type_resource())?;
                if access.method == method {
                    return Ok(true);
                }
            }
        }
        Ok(false)
    }

    pub(super) fn require_provider_state_access_phase(&self, span: Span) -> Result<(), TypeError> {
        if self.provider_context.is_none() {
            return Err(ordinary_state_unavailable(span));
        }
        Ok(())
    }

    pub(super) fn synthesize_provider_state_access(
        &mut self,
        method: MethodId,
        span: Span,
        operand: TypedNode,
    ) -> Result<TypedNode, TypeError> {
        let operand = TypedNodeOwner::new(operand);
        self.require_provider_state_access_phase(span)?;
        if !self.is_provider_state_access(method)? {
            return Err(foreign_privilege_unavailable());
        }
        let exposed = IterativeTypeOwner::new(self.zonk(&operand.ty)?);
        let (family, arguments) = match &*exposed {
            Type::ResourceApply(definition, arguments) => (
                self.registry
                    .resource_signature_family(*definition)
                    .ok_or_else(invalid_state)?,
                crate::types::clone_kinded_arguments_with_budget(
                    arguments.iter(),
                    &mut self.type_work,
                )
                .map_err(|()| type_resource())?,
            ),
            ty => {
                let (family, arguments) = nominal_arguments(ty, &mut self.type_work).map_err(
                    |failure| match failure {
                        TypeError::Internal(ElaborationFailure::InvalidState) => contract_error(
                            span,
                            "state access requires an exact checked local header association",
                        ),
                        other => other,
                    },
                )?;
                let mut retained = OwnedTypeBuffer(Vec::new());
                self.type_work
                    .charge(arguments.len())
                    .map_err(|()| type_resource())?;
                retained
                    .try_reserve(arguments.len())
                    .map_err(|_| type_resource())?;
                for argument in arguments {
                    retained.push(
                        clone_type_with_budget(argument, &mut self.type_work)
                            .map_err(|()| type_resource())?,
                    );
                }
                (
                    family,
                    crate::types::type_arguments_to_kinded_with_budget(
                        retained.into_boxed_slice(),
                        &mut self.type_work,
                    )
                    .map_err(|()| type_resource())?,
                )
            }
        };
        let arguments = super::OwnedArgumentBuffer::from_box(arguments, &mut self.type_work)?;
        let context = self.provider_context.as_ref().ok_or_else(invalid_state)?;
        self.type_work
            .charge(context.state_associations.len())
            .map_err(|()| type_resource())?;
        let association = context
            .state_associations
            .iter()
            .find(|association| association.family == family)
            .ok_or_else(|| {
                contract_error(
                    span,
                    "state access requires an exact checked local header association",
                )
            })?;
        if arguments.0.len() != association.parameters.len() {
            return Err(contract_error(
                span,
                "state access resource argument count differs",
            ));
        }
        let definition = association.definition;
        let mut substitutions = OwnerReplacementBuffer::new();
        for (parameter, argument) in association.parameters.iter().zip(arguments.0.iter()) {
            substitutions.insert_cloned(*parameter, argument, &mut self.type_work)?;
        }
        let state = IterativeTypeOwner::new(
            substitutions.substitute(&association.state, &mut self.type_work)?,
        );
        let retained_arguments = crate::types::clone_kinded_arguments_with_budget(
            arguments.0.iter().map(|argument| argument.as_ref()),
            &mut self.type_work,
        )
        .map_err(|()| type_resource())?;
        let provenance = self.at_span_provenance(&state, span)?;
        let ty = self.clone_type(&state)?;
        let effects = self.core_effect_row(&operand.effects)?;
        let node = self.push_effect_core(
            ty,
            effects,
            Origin::Source(span),
            EffectOperation::ProviderStateAccess(
                crate::core::effect::ProviderStateAccessNode::new_kinded(
                    method,
                    definition,
                    retained_arguments,
                    operand.node,
                ),
            ),
        )?;
        let effects = clone_effect_row_with_budget(&operand.effects, &mut self.type_work)
            .map_err(|()| type_resource())?;
        Ok(TypedNode {
            node,
            ty: state.into_inner(),
            effects,
            provenance,
        })
    }

    pub(super) fn contains_provider_state(&mut self, root: &Type) -> Result<bool, TypeError> {
        if self.registry.foreign_modules().next().is_none() {
            return Ok(false);
        }
        crate::types::visit_type_structure_with_budget(root, &mut self.type_work, |node, _| {
            Ok(
                matches!(node, crate::types::TypeStructureNode::Type(Type::Nominal(id))
                if self.registry.foreign_state(*id).is_some()),
            )
        })
        .map_err(|()| type_resource())
    }

    pub(super) fn check_provider_source_application(
        &mut self,
        function: NodeId,
        argument: &Type,
        span: Span,
    ) -> Result<(), TypeError> {
        if !self.contains_provider_state(argument)? {
            return Ok(());
        }
        let constructor = self.builder.direct_constructor(function)?.ok_or_else(|| {
            contract_error(
                span,
                "controlled native state cannot be passed through an ordinary callable",
            )
        })?;
        let context = self
            .provider_context
            .as_ref()
            .ok_or_else(foreign_privilege_unavailable)?;
        self.type_work
            .charge(context.operations.len())
            .map_err(|()| type_resource())?;
        let allowed = context.operations.iter().any(|operation| {
            self.registry
                .foreign_operation(*operation)
                .is_some_and(|fact| match (&context.phase, &fact.result) {
                    (Phase::Acquire, ForeignResultFact::Acquire { constructors, .. })
                    | (Phase::Finish, ForeignResultFact::Finish { constructors, .. }) => {
                        constructors.contains(&constructor)
                    }
                    _ => false,
                })
        });
        if !allowed {
            return Err(contract_error(
                span,
                "controlled state may occur only in a direct authenticated lifecycle codec application",
            ));
        }
        // The constructor is still ordinary data. Independent native lineage
        // validation must prove guard/publication/completion postconditions.
        Ok(())
    }

    pub(super) fn check_provider_native_request(
        &mut self,
        request: &crate::resolved::ResolvedPerformExpr,
    ) -> Result<(), TypeError> {
        let context = self
            .provider_context
            .as_ref()
            .ok_or_else(foreign_privilege_unavailable)?;
        let fact = self
            .registry
            .foreign_operation(request.operation)
            .ok_or_else(invalid_state)?;
        let phase_matches = match context.phase {
            Phase::Acquire => fact.role == ForeignOperationRole::Acquire,
            Phase::Finish => fact.role == ForeignOperationRole::Finish,
            Phase::Handler => fact.role == ForeignOperationRole::Borrow,
        };
        self.type_work
            .charge(context.operations.len())
            .map_err(|()| type_resource())?;
        if !phase_matches
            || !context.operations.contains(&fact.id)
            || compare_effect_instances_with_budget(
                &context.native,
                &request.effect.instance,
                &mut self.type_work,
            )
            .map_err(|()| type_resource())?
                != std::cmp::Ordering::Equal
        {
            return Err(contract_error(
                request.effect.span,
                "registered native operation does not belong to this provider template phase and exact interpretation",
            ));
        }
        Ok(())
    }
}

/// Header facts alone do not admit a resource or confer lifecycle authority.
#[derive(Debug)]
struct ProviderHeader {
    provider_application: crate::interface::InterfaceApplication,
    state_association: HeaderStateAssociation,
    acquire: Vec<(OperationId, NominalTypeId)>,
    finish: Vec<(OperationId, NominalTypeId)>,
    input_error: Type,
    completion_error: Type,
    methods: Vec<(MethodId, OperationId)>,
    #[cfg(test)]
    scope_constructors: [ConstructorId; 2],
    #[cfg(test)]
    completion_constructors: [ConstructorId; 3],
}

/// Actual checked source occurrence, retained before the source builder is consumed.
pub(super) struct CheckedGlobalOccurrence {
    pub(super) node: Option<NodeId>,
    pub(super) source_node: Option<NodeId>,
    pub(super) value_type: IterativeTypeOwner,
    pub(super) occurrence: crate::resolved::ResolvedOccurrence,
    pub(super) arguments: OwnedTypeBuffer,
    pub(super) row_arguments: Vec<EffectRow>,
}
impl std::fmt::Debug for CheckedGlobalOccurrence {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CheckedGlobalOccurrence")
            .field("source_node", &self.source_node)
            .field("node", &self.node)
            .field("term", &self.occurrence.term)
            .finish_non_exhaustive()
    }
}
impl Drop for CheckedGlobalOccurrence {
    fn drop(&mut self) {
        let span = self.occurrence.origin.primary_span();
        discard_origin_iteratively(std::mem::replace(
            &mut self.occurrence.origin,
            Origin::Source(span),
        ));
    }
}

impl<F: CoreLoweringFamily> CoreElaborator<F> {
    pub(super) fn retain_provider_global_occurrence(
        &mut self,
        occurrence: &crate::resolved::ResolvedOccurrence,
        arguments: &[Type],
        row_arguments: &[EffectRow],
        value_type: &Type,
    ) -> Result<Option<usize>, TypeError> {
        if self.provider_occurrence_template.is_none()
            || !occurrence.global_binder().is_some_and(|binder| {
                self.selection
                    .as_ref()
                    .is_some_and(|selection| selection.scheme(binder).is_some())
            })
        {
            return Ok(None);
        }
        self.type_work
            .charge(
                arguments.len()
                    + row_arguments.len()
                    + occurrence.evidence.len()
                    + occurrence.spelling.len()
                    + 1,
            )
            .map_err(|()| type_resource())?;
        self.provider_global_occurrences
            .try_reserve(1)
            .map_err(|_| type_resource())?;
        let mut retained_arguments = OwnedTypeBuffer(Vec::new());
        retained_arguments
            .try_reserve(arguments.len())
            .map_err(|_| type_resource())?;
        for argument in arguments {
            retained_arguments.push(self.clone_type(argument)?);
        }
        let mut retained_rows = Vec::new();
        retained_rows
            .try_reserve(row_arguments.len())
            .map_err(|_| type_resource())?;
        for row in row_arguments {
            retained_rows.push(
                clone_effect_row_with_budget(row, &mut self.type_work)
                    .map_err(|()| type_resource())?,
            );
        }
        let mut slots = Vec::new();
        slots
            .try_reserve_exact(occurrence.evidence.len())
            .map_err(|_| type_resource())?;
        for slot in &occurrence.evidence {
            slots.push(slot.retain_unpublished().ok_or_else(invalid_state)?);
        }
        provider_globals::charge_origin_clone(&occurrence.origin, &mut self.type_work)?;
        let retained_type = IterativeTypeOwner::new(self.clone_type(value_type)?);
        let index = self.provider_global_occurrences.len();
        self.provider_global_occurrences
            .push(CheckedGlobalOccurrence {
                node: None,
                source_node: None,
                value_type: retained_type,
                occurrence: crate::resolved::ResolvedOccurrence {
                    term: occurrence.term,
                    spelling: occurrence.spelling.clone(),
                    origin: occurrence.origin.clone(),
                    import_span: occurrence.import_span,
                    evidence: slots.into_boxed_slice(),
                },
                arguments: retained_arguments,
                row_arguments: retained_rows,
            });
        Ok(Some(index))
    }
}

/// Provisional source clauses. No root or shared output row is fabricated.
#[cfg(test)]
#[derive(Debug)]
struct HandlerSourceDraft {
    id: ProviderTemplateId,
    handler: HandlerId,
    hidden_answer: TypeVariableId,
    hidden_row: EffectRowVariable,
    state_parameter: TypedBinder,
    direct_demands: EffectRow,
    clauses: Vec<CheckedEffectClause>,
    builder: CoreBuilder<EffectOperationFamily>,
    occurrences: Vec<CheckedGlobalOccurrence>,
    pending_rows: crate::core::provider::HandlerPendingRows,
    #[cfg(test)]
    compile_work: usize,
}

struct PreparedHandlerSource {
    id: ProviderTemplateId,
    handler: HandlerId,
    hidden_answer: TypeVariableId,
    hidden_row: EffectRowVariable,
    state_parameter: TypedBinder,
    direct_demands: EffectRow,
    clauses: Vec<CheckedEffectClause>,
}

struct CompiledHandlerDraft {
    #[cfg(test)]
    compile_work: usize,
    fragment: crate::core::provider::HandlerFragmentDraft,
    staged_externals: Option<StagedProviderExternals>,
}

/// Owned conditional code and unpublished selections. Final specialization,
/// ordinary whole-handler validation and module publication remain separate.
struct CheckedConditionalHandler {
    template: crate::core::validate::CheckedHandlerTemplate,
    staged_externals: StagedProviderExternals,
}

/// Unpublished code: ordinary Core validation and lifecycle entry validation
/// are both required before this draft may enter a checked template table.
#[derive(Debug)]
struct LifecycleTemplateDraft {
    id: ProviderTemplateId,
    phase: Phase,
    parameter: BinderId,
    body: NodeId,
    hidden_answer: TypeVariableId,
    hidden_row: EffectRowVariable,
    formal_parameters: Box<[(TypeVariableId, TypeVariableId, Kind)]>,
    core: crate::core::UnvalidatedEffectProgram,
    staged_externals: Option<StagedProviderExternals>,
    defining_facts: Option<std::sync::Arc<crate::resolved::ProviderDefiningFacts>>,
    #[cfg(test)]
    compile_work: usize,
}

/// Defining lifecycle code after source-occurrence authentication, independent
/// Core checking and native lineage checking. This is generic code, not an
/// ordinary executable provider instance.
struct CheckedLifecycleTemplate {
    original: crate::core::provider::LifecycleOriginal,
    parameter_origin: std::sync::Arc<crate::core::provider::RetainedHandlerOrigin>,
    draft: LifecycleTemplateDraft,
    canonical: std::sync::Arc<crate::resolved::ResolvedRegistry>,
    externals: std::sync::Arc<crate::core::provider::RetainedHandlerExternals>,
    associations: Vec<HeaderStateAssociation>,
}

/// One defining module's immutable conditional code. It carries no ordinary
/// instance, final evidence catalog or runtime admission.
pub(crate) struct CheckedProviderGroup {
    contracts: std::sync::Arc<CheckedProviderContracts>,
    module: crate::module::ModuleId,
    declarations: Vec<Arc<CheckedProviderDeclaration>>,
}

/// Plain owned code before committed publication authentication.
struct AvailableProviderGroup {
    code: Arc<CheckedProviderGroup>,
}
struct CommittedOriginalGroup {
    code: Arc<CheckedProviderGroup>,
    certificate: Arc<CheckedProviderContracts>,
}
enum GroupPreparationPhase {
    Available,
    Committed(CommittedOriginalGroup),
}
struct AvailableProviderComponent {
    original: Arc<PreparedProviderOriginal>,
}
struct CommittedOriginalComponent {
    original: Arc<PreparedProviderOriginal>,
    certificate: Arc<CheckedProviderContracts>,
}
enum ComponentPreparationPhase {
    Pending,
    Committed(CommittedOriginalComponent),
}

/// This token covers only immutable selected-template state associations.
/// Publication and source/linked routing have their own distinct transitions.
struct PreparedOriginalTemplate {
    declaration: Arc<CheckedProviderDeclaration>,
}
impl PreparedOriginalTemplate {
    fn prepare(
        declaration: &Arc<CheckedProviderDeclaration>,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, TypeError> {
        declaration_template_source(declaration, work)?;
        work.charge(1).map_err(|()| type_resource())?;
        Ok(Self {
            declaration: Arc::clone(declaration),
        })
    }
    fn source<'a>(
        &self,
        declaration: &'a CheckedProviderDeclaration,
        work: &mut TypeWorkBudget,
    ) -> Result<ProviderTemplateSource<'a>, TypeError> {
        work.charge(1).map_err(|()| type_resource())?;
        if !std::ptr::eq(self.declaration.as_ref(), declaration) {
            return Err(invalid_state());
        }
        prepared_declaration_template_source(declaration)
    }
}

/// One compiler preparation owner's exact original group. The immutable code
/// never contains the mutable phase or a prepared answer/capture cache.
pub(crate) struct ProviderGroupPreparation {
    code: Arc<CheckedProviderGroup>,
    phase: std::sync::Mutex<GroupPreparationPhase>,
    templates:
        std::sync::Mutex<HashMap<crate::resolved::ResourceDefinitionId, PreparedOriginalTemplate>>,
}
impl std::fmt::Debug for ProviderGroupPreparation {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("ProviderGroupPreparation")
            .field("module", &self.code.module)
            .finish_non_exhaustive()
    }
}
impl std::ops::Deref for ProviderGroupPreparation {
    type Target = CheckedProviderGroup;
    fn deref(&self) -> &Self::Target {
        &self.code
    }
}
impl AvailableProviderGroup {
    fn commit(
        self,
        certificate: &Arc<CheckedProviderContracts>,
        work: &mut TypeWorkBudget,
    ) -> Result<CommittedOriginalGroup, TypeError> {
        self.code
            .authenticate_code(certificate, work)
            .map_err(super::resolved_build_error)?;
        work.charge(1).map_err(|()| type_resource())?;
        Ok(CommittedOriginalGroup {
            code: self.code,
            certificate: Arc::clone(certificate),
        })
    }
}
impl ProviderGroupPreparation {
    pub(crate) fn new(
        code: Arc<CheckedProviderGroup>,
        work: &mut TypeWorkBudget,
    ) -> Result<Arc<Self>, TypeError> {
        work.charge(1).map_err(|()| type_resource())?;
        Ok(Arc::new(Self {
            code,
            phase: std::sync::Mutex::new(GroupPreparationPhase::Available),
            templates: std::sync::Mutex::new(HashMap::new()),
        }))
    }
    pub(crate) fn matches_code(&self, code: &Arc<CheckedProviderGroup>) -> bool {
        Arc::ptr_eq(&self.code, code)
    }
    fn prepare_committed(
        &self,
        certificate: &Arc<CheckedProviderContracts>,
        work: &mut TypeWorkBudget,
    ) -> Result<(), TypeError> {
        work.charge(1).map_err(|()| type_resource())?;
        let mut phase = self.phase.try_lock().map_err(|_| invalid_state())?;
        match &*phase {
            GroupPreparationPhase::Committed(prepared) => {
                if !Arc::ptr_eq(&prepared.code, &self.code)
                    || !Arc::ptr_eq(&prepared.certificate, certificate)
                {
                    return Err(invalid_state());
                }
                return Ok(());
            }
            GroupPreparationPhase::Available => {}
        }
        work.charge(1).map_err(|()| type_resource())?;
        let available = AvailableProviderGroup {
            code: Arc::clone(&self.code),
        };
        let prepared = available.commit(certificate, work)?;
        *phase = GroupPreparationPhase::Committed(prepared);
        Ok(())
    }
    fn prepared_source(
        &self,
        definition: crate::resolved::ResourceDefinitionId,
        family: NominalTypeId,
        work: &mut TypeWorkBudget,
    ) -> Result<ProviderTemplateSource<'_>, TypeError> {
        work.charge(self.code.declarations.len())
            .map_err(|()| type_resource())?;
        let declaration = self
            .code
            .declarations
            .iter()
            .find(|entry| entry.fact.id == definition)
            .ok_or_else(invalid_state)?;
        if declaration.fact.family != family || definition.module() != self.code.module {
            return Err(invalid_state());
        }
        work.charge(1).map_err(|()| type_resource())?;
        let mut templates = self.templates.try_lock().map_err(|_| invalid_state())?;
        if let Some(prepared) = templates.get(&definition) {
            return prepared.source(declaration, work);
        }
        let prepared = PreparedOriginalTemplate::prepare(declaration, work)?;
        work.charge(1).map_err(|()| type_resource())?;
        templates.try_reserve(1).map_err(|_| type_resource())?;
        // The view is staged before the infallible entry publication.
        let source = prepared.source(declaration, work)?;
        templates.insert(definition, prepared);
        Ok(source)
    }
    fn pending_template_source(
        &self,
        definition: crate::resolved::ResourceDefinitionId,
        family: NominalTypeId,
        work: &mut TypeWorkBudget,
    ) -> Result<ProviderTemplateSource<'_>, TypeError> {
        self.prepared_source(definition, family, work)
    }
    fn imported_template_source(
        &self,
        definition: crate::resolved::ResourceDefinitionId,
        family: NominalTypeId,
        certificate: &Arc<CheckedProviderContracts>,
        work: &mut TypeWorkBudget,
    ) -> Result<ProviderTemplateSource<'_>, TypeError> {
        self.prepare_committed(certificate, work)?;
        self.prepared_source(definition, family, work)
    }
    fn template_source(
        &self,
        definition: crate::resolved::ResourceDefinitionId,
        family: NominalTypeId,
        registry: &crate::resolved::ResolvedRegistry,
        work: &mut TypeWorkBudget,
    ) -> Result<ProviderTemplateSource<'_>, TypeError> {
        let certificate = linked_provider_certificate(registry, self.code.module, work)?;
        self.prepare_committed(certificate, work)?;
        self.prepared_source(definition, family, work)
    }
}

/// A component can be promoted using its exact published certificate without
/// requiring complete group code availability in the final prepass.
pub(crate) struct ProviderOriginalPreparation {
    original: Arc<PreparedProviderOriginal>,
    phase: std::sync::Mutex<ComponentPreparationPhase>,
    template: std::sync::Mutex<Option<PreparedOriginalTemplate>>,
}
impl std::ops::Deref for ProviderOriginalPreparation {
    type Target = PreparedProviderOriginal;
    fn deref(&self) -> &Self::Target {
        &self.original
    }
}
impl AvailableProviderComponent {
    fn commit(
        self,
        certificate: &Arc<CheckedProviderContracts>,
        work: &mut TypeWorkBudget,
    ) -> Result<CommittedOriginalComponent, TypeError> {
        certificate
            .authenticate(true, work)
            .map_err(super::resolved_build_error)?;
        work.charge(certificate.declarations.len())
            .map_err(|()| type_resource())?;
        if !certificate
            .declarations
            .iter()
            .any(|contract| Arc::ptr_eq(contract, &self.original.contract))
        {
            return Err(invalid_state());
        }
        authenticate_original_relation(&self.original.declaration, &self.original.contract, work)
            .map_err(super::resolved_build_error)?;
        work.charge(1).map_err(|()| type_resource())?;
        Ok(CommittedOriginalComponent {
            original: self.original,
            certificate: Arc::clone(certificate),
        })
    }
}
impl ProviderOriginalPreparation {
    fn new(
        original: Arc<PreparedProviderOriginal>,
        work: &mut TypeWorkBudget,
    ) -> Result<Arc<Self>, TypeError> {
        work.charge(1).map_err(|()| type_resource())?;
        Ok(Arc::new(Self {
            original,
            phase: std::sync::Mutex::new(ComponentPreparationPhase::Pending),
            template: std::sync::Mutex::new(None),
        }))
    }
    fn source(
        &self,
        definition: crate::resolved::ResourceDefinitionId,
        family: NominalTypeId,
        work: &mut TypeWorkBudget,
    ) -> Result<ProviderTemplateSource<'_>, TypeError> {
        self.prepared_source(definition, family, work)
    }
    fn prepared_source(
        &self,
        definition: crate::resolved::ResourceDefinitionId,
        family: NominalTypeId,
        work: &mut TypeWorkBudget,
    ) -> Result<ProviderTemplateSource<'_>, TypeError> {
        if self.original.declaration.fact.id != definition
            || self.original.declaration.fact.family != family
        {
            return Err(invalid_state());
        }
        work.charge(1).map_err(|()| type_resource())?;
        let mut template = self.template.try_lock().map_err(|_| invalid_state())?;
        if let Some(prepared) = &*template {
            return prepared.source(&self.original.declaration, work);
        }
        let prepared = PreparedOriginalTemplate::prepare(&self.original.declaration, work)?;
        let source = prepared.source(&self.original.declaration, work)?;
        *template = Some(prepared);
        Ok(source)
    }
    fn template_source(
        &self,
        definition: crate::resolved::ResourceDefinitionId,
        family: NominalTypeId,
        registry: &crate::resolved::ResolvedRegistry,
        work: &mut TypeWorkBudget,
    ) -> Result<ProviderTemplateSource<'_>, TypeError> {
        let certificate = linked_provider_certificate(registry, definition.module(), work)?;
        work.charge(1).map_err(|()| type_resource())?;
        let mut phase = self.phase.try_lock().map_err(|_| invalid_state())?;
        match &*phase {
            ComponentPreparationPhase::Committed(prepared) => {
                if !Arc::ptr_eq(&prepared.original, &self.original)
                    || !Arc::ptr_eq(&prepared.certificate, certificate)
                {
                    return Err(invalid_state());
                }
            }
            ComponentPreparationPhase::Pending => {
                work.charge(1).map_err(|()| type_resource())?;
                let available = AvailableProviderComponent {
                    original: Arc::clone(&self.original),
                };
                let prepared = available.commit(certificate, work)?;
                *phase = ComponentPreparationPhase::Committed(prepared);
            }
        }
        self.prepared_source(definition, family, work)
    }
}

fn linked_provider_certificate<'a>(
    registry: &'a crate::resolved::ResolvedRegistry,
    module: crate::module::ModuleId,
    work: &mut TypeWorkBudget,
) -> Result<&'a Arc<CheckedProviderContracts>, TypeError> {
    let mut certificate = None;
    for (owner, candidate) in registry.provider_contracts() {
        work.charge(1).map_err(|()| type_resource())?;
        if *owner == module && certificate.replace(candidate).is_some() {
            return Err(invalid_state());
        }
    }
    certificate.ok_or_else(invalid_state)
}

/// One compiler transaction's checked local originals. Construction validates
/// their exact pending selections and defining captures; this preparation can
/// supply source copies but cannot supply final Core execution authority.
pub(super) struct PreparedLocalProviderCode {
    module: crate::module::ModuleId,
    code: Option<Arc<ProviderGroupPreparation>>,
    originals: Vec<Arc<ProviderOriginalPreparation>>,
}
impl std::fmt::Debug for PreparedLocalProviderCode {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("PreparedLocalProviderCode")
            .field("module", &self.module)
            .finish()
    }
}
impl PreparedLocalProviderCode {
    pub(super) fn prepare(
        code: &Arc<CheckedProviderGroup>,
        facts: crate::resolved::ProviderExternalFacts<'_>,
        publication: &PendingEvidencePublication,
        work: &mut TypeWorkBudget,
    ) -> Result<Arc<Self>, TypeError> {
        code.local_template_view(code.contracts(), facts, publication, work)?;
        work.charge(2).map_err(|()| type_resource())?;
        Ok(Arc::new(Self {
            module: code.module,
            code: Some(ProviderGroupPreparation::new(Arc::clone(code), work)?),
            originals: Vec::new(),
        }))
    }
    pub(super) fn pending(
        module: crate::module::ModuleId,
        count: usize,
        work: &mut TypeWorkBudget,
    ) -> Result<Arc<Self>, TypeError> {
        work.charge(count.checked_add(1).ok_or_else(type_resource)?)
            .map_err(|()| type_resource())?;
        let mut originals = Vec::new();
        originals
            .try_reserve_exact(count)
            .map_err(|_| type_resource())?;
        Ok(Arc::new(Self {
            module,
            code: None,
            originals,
        }))
    }
    pub(super) fn module(&self) -> crate::module::ModuleId {
        self.module
    }
    pub(super) fn code(&self) -> Result<&Arc<CheckedProviderGroup>, TypeError> {
        self.code
            .as_ref()
            .map(|code| &code.code)
            .ok_or_else(invalid_state)
    }
    pub(super) fn contains(&self, definition: crate::resolved::ResourceDefinitionId) -> bool {
        self.code.as_ref().is_some_and(|code| {
            code.declarations
                .iter()
                .any(|entry| entry.fact.id == definition)
        }) || self
            .originals
            .iter()
            .any(|original| original.declaration.fact.id == definition)
    }
    pub(super) fn add(
        &mut self,
        original: Arc<PreparedProviderOriginal>,
        work: &mut TypeWorkBudget,
    ) -> Result<(), TypeError> {
        work.charge(
            self.originals
                .len()
                .checked_add(1)
                .ok_or_else(type_resource)?,
        )
        .map_err(|()| type_resource())?;
        if self.code.is_some()
            || original.declaration.fact.id.module() != self.module
            || self.contains(original.declaration.fact.id)
        {
            return Err(invalid_state());
        }
        self.originals.try_reserve(1).map_err(|_| type_resource())?;
        let original = ProviderOriginalPreparation::new(original, work)?;
        self.originals.push(original);
        Ok(())
    }
    pub(super) fn ordered_originals(
        &self,
        module: &ResolvedModule,
        work: &mut TypeWorkBudget,
    ) -> Result<Vec<Arc<PreparedProviderOriginal>>, TypeError> {
        if self.code.is_some() || self.originals.len() != module.resources().len() {
            return Err(invalid_state());
        }
        work.charge(self.originals.len())
            .map_err(|()| type_resource())?;
        let mut originals = Vec::new();
        originals
            .try_reserve_exact(self.originals.len())
            .map_err(|_| type_resource())?;
        for definition in module.resources() {
            work.charge(
                self.originals
                    .len()
                    .checked_add(1)
                    .ok_or_else(type_resource)?,
            )
            .map_err(|()| type_resource())?;
            let original = self
                .originals
                .iter()
                .find(|original| original.declaration.fact.id == definition.id)
                .ok_or_else(invalid_state)?;
            originals.push(Arc::clone(&original.original));
        }
        Ok(originals)
    }
    pub(super) fn complete(
        &mut self,
        module: &ResolvedModule,
        code: Arc<CheckedProviderGroup>,
        work: &mut TypeWorkBudget,
    ) -> Result<(), TypeError> {
        if self.code.is_some()
            || code.module != self.module
            || code.contracts.module != self.module
            || module.module() != self.module
            || self.originals.len() != module.resources().len()
            || code.declarations.len() != module.resources().len()
            || code.contracts.declarations.len() != module.resources().len()
        {
            return Err(invalid_state());
        }
        work.charge(
            module
                .resources()
                .len()
                .checked_mul(
                    self.originals
                        .len()
                        .checked_add(1)
                        .ok_or_else(type_resource)?,
                )
                .ok_or_else(type_resource)?,
        )
        .map_err(|()| type_resource())?;
        for ((definition, declaration), contract) in module
            .resources()
            .iter()
            .zip(&code.declarations)
            .zip(&code.contracts.declarations)
        {
            if declaration.fact.id != definition.id
                || contract.fact.id != definition.id
                || !self.originals.iter().any(|original| {
                    Arc::ptr_eq(&original.declaration, declaration)
                        && Arc::ptr_eq(&original.contract, contract)
                })
            {
                return Err(invalid_state());
            }
        }
        self.code = Some(ProviderGroupPreparation::new(code, work)?);
        Ok(())
    }
    pub(super) fn original_code(
        &self,
        definition: crate::resolved::ResourceDefinitionId,
        work: &mut TypeWorkBudget,
    ) -> Result<PreparedProviderCode, TypeError> {
        work.charge(
            self.originals
                .len()
                .checked_add(1)
                .ok_or_else(type_resource)?,
        )
        .map_err(|()| type_resource())?;
        if let Some(code) = &self.code {
            return Ok(PreparedProviderCode::Group(Arc::clone(code)));
        }
        let original = self
            .originals
            .iter()
            .find(|original| original.declaration.fact.id == definition)
            .ok_or_else(invalid_state)?;
        Ok(PreparedProviderCode::Original(Arc::clone(original)))
    }
    pub(super) fn template_source<'a>(
        &self,
        code: &'a PreparedProviderCode,
        definition: crate::resolved::ResourceDefinitionId,
        family: NominalTypeId,
        work: &mut TypeWorkBudget,
    ) -> Result<ProviderTemplateSource<'a>, TypeError> {
        work.charge(
            self.originals
                .len()
                .checked_add(1)
                .ok_or_else(type_resource)?,
        )
        .map_err(|()| type_resource())?;
        match code {
            PreparedProviderCode::Group(code)
                if self
                    .code
                    .as_ref()
                    .is_some_and(|original| Arc::ptr_eq(original, code)) =>
            {
                code.pending_template_source(definition, family, work)
            }
            PreparedProviderCode::Original(code)
                if self
                    .originals
                    .iter()
                    .any(|original| Arc::ptr_eq(original, code)) =>
            {
                code.source(definition, family, work)
            }
            _ => Err(invalid_state()),
        }
    }
}

/// Instance preparation retains immutable original allocations. A private
/// original remains distinct from the completed group exported by a module.
pub(crate) enum PreparedProviderCode {
    Group(Arc<ProviderGroupPreparation>),
    Original(Arc<ProviderOriginalPreparation>),
}
impl PreparedProviderCode {
    pub(super) fn imported_template_source(
        &self,
        definition: crate::resolved::ResourceDefinitionId,
        family: NominalTypeId,
        certificate: &Arc<CheckedProviderContracts>,
        work: &mut TypeWorkBudget,
    ) -> Result<ProviderTemplateSource<'_>, TypeError> {
        match self {
            Self::Group(code) => {
                code.imported_template_source(definition, family, certificate, work)
            }
            Self::Original(_) => Err(invalid_state()),
        }
    }
    pub(super) fn template_source(
        &self,
        definition: crate::resolved::ResourceDefinitionId,
        family: NominalTypeId,
        registry: &crate::resolved::ResolvedRegistry,
        work: &mut TypeWorkBudget,
    ) -> Result<ProviderTemplateSource<'_>, TypeError> {
        match self {
            Self::Group(code) => code.template_source(definition, family, registry, work),
            Self::Original(original) => {
                original.template_source(definition, family, registry, work)
            }
        }
    }
}

/// Borrowed immutable code inputs. These views confer no instance authority;
/// copying and final Core admission must establish the specialization relation.
pub(super) struct ProviderTemplateSource<'a> {
    pub(super) fact: &'a Arc<crate::resolved::ResourceTypeFact>,
    pub(super) acquire: LifecycleTemplateSource<'a>,
    pub(super) finish: LifecycleTemplateSource<'a>,
    pub(super) handler: &'a crate::core::validate::CheckedHandlerTemplate,
    pub(super) handler_occurrences: &'a [CheckedGlobalOccurrence],
    pub(super) methods: &'a [(MethodId, OperationId)],
}

pub(super) struct LifecycleTemplateSource<'a> {
    pub(super) original: &'a crate::core::provider::LifecycleOriginal,
    pub(super) program: &'a crate::core::UnvalidatedEffectProgram,
    pub(super) body: NodeId,
    pub(super) occurrences: &'a [CheckedGlobalOccurrence],
}

/// Canonical body-free proof shared by declaration summaries and separately
/// retained defining code. No typed program, source expression or recipe node
/// graph is reachable from this certificate.
pub(crate) struct CheckedProviderContracts {
    module: crate::module::ModuleId,
    declarations: Vec<Arc<ProviderDeclarationContract>>,
    sources: Vec<(
        crate::module::ModuleId,
        std::sync::Arc<crate::source::SourceFile>,
    )>,
}
struct ProviderDeclarationContract {
    provider_application: std::sync::Arc<crate::interface::InterfaceApplication>,
    methods: std::sync::Arc<[(MethodId, OperationId)]>,
    spelling: String,
    public: bool,
    fact: std::sync::Arc<crate::resolved::ResourceTypeFact>,
    acquire: LifecycleContractCertificate,
    finish: LifecycleContractCertificate,
    handlers: crate::core::validate::CheckedHandlerContractCertificate,
}
struct LifecycleContractCertificate {
    template: ProviderTemplateId,
    phase: Phase,
    parameter: BinderId,
    parameter_origin: std::sync::Arc<crate::core::provider::RetainedHandlerOrigin>,
    hidden_answer: TypeVariableId,
    hidden_row: EffectRowVariable,
    formals: Vec<(TypeVariableId, TypeVariableId)>,
    canonical: std::sync::Arc<crate::resolved::ResolvedRegistry>,
    externals: std::sync::Arc<crate::core::provider::RetainedHandlerExternals>,
}
impl PartialEq for CheckedProviderContracts {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self, other)
    }
}
impl Eq for CheckedProviderContracts {}
impl std::fmt::Debug for CheckedProviderContracts {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("CheckedProviderContracts")
            .field("module", &self.module)
            .field("declarations", &self.declarations.len())
            .finish_non_exhaustive()
    }
}
fn authenticate_provider_application_witness(
    fact: &crate::resolved::ResourceTypeFact,
    checked_application: &crate::interface::InterfaceApplication,
    work: &mut TypeWorkBudget,
) -> Result<(), crate::resolved::ResolvedBuildFailure> {
    use crate::resolved::ResolvedBuildFailure as Failure;
    if fact.provider_application.interface() != checked_application.interface()
        || fact.provider.interface.id != checked_application.interface()
        || fact.provider_application.arguments().len() != checked_application.arguments().len()
        || fact.provider.arguments.len() != checked_application.arguments().len()
    {
        return Err(Failure::InvalidState);
    }
    work.charge(checked_application.arguments().len())
        .map_err(|()| Failure::TypeResource)?;
    for ((canonical, checked), written) in fact
        .provider_application
        .arguments()
        .iter()
        .zip(checked_application.arguments())
        .zip(fact.provider.arguments.iter())
    {
        if !crate::types::same_kinded_argument_with_budget(canonical, checked, work)
            .map_err(|()| Failure::TypeResource)?
        {
            return Err(Failure::InvalidState);
        }
        if !crate::types::same_kinded_argument_with_budget(checked, &written.ty, work)
            .map_err(|()| Failure::TypeResource)?
        {
            return Err(Failure::InvalidState);
        }
    }
    Ok(())
}

impl CheckedProviderContracts {
    pub(crate) fn resource_count(&self) -> usize {
        self.declarations.len()
    }
    pub(crate) fn defining_sources(
        &self,
    ) -> &[(
        crate::module::ModuleId,
        std::sync::Arc<crate::source::SourceFile>,
    )] {
        &self.sources
    }
    pub(crate) fn authenticate(
        &self,
        committed: bool,
        work: &mut TypeWorkBudget,
    ) -> Result<(), crate::resolved::ResolvedBuildFailure> {
        let mut authenticated_native_facts = crate::foreign::NativeAuthenticationMemo::default();
        self.authenticate_with_native_memo(committed, &mut authenticated_native_facts, work)
    }

    /// Reuses only native self-authentication within one caller's admission.
    /// Source origins remain authenticated against this contract's source table.
    pub(crate) fn authenticate_with_native_memo(
        &self,
        committed: bool,
        authenticated_native_facts: &mut crate::foreign::NativeAuthenticationMemo,
        work: &mut TypeWorkBudget,
    ) -> Result<(), crate::resolved::ResolvedBuildFailure> {
        use crate::resolved::ResolvedBuildFailure as Failure;
        let mut authenticated_native_origins: Vec<&Arc<crate::foreign::ForeignModuleFact>> =
            Vec::new();
        work.charge(self.sources.len())
            .map_err(|()| Failure::TypeResource)?;
        let mut modules = HashSet::new();
        let mut source_ids = HashSet::new();
        modules
            .try_reserve(self.sources.len())
            .map_err(|_| Failure::TypeResource)?;
        source_ids
            .try_reserve(self.sources.len())
            .map_err(|_| Failure::TypeResource)?;
        for (module, source) in &self.sources {
            if !modules.insert(*module) || !source_ids.insert(source.id()) {
                return Err(Failure::InvalidState);
            }
        }
        work.charge(
            self.declarations
                .len()
                .checked_mul(3)
                .ok_or(Failure::TypeResource)?,
        )
        .map_err(|()| Failure::TypeResource)?;
        let mut associated_interfaces = HashMap::new();
        let mut associated_effects = HashMap::new();
        associated_interfaces
            .try_reserve(self.declarations.len())
            .map_err(|_| Failure::TypeResource)?;
        associated_effects
            .try_reserve(self.declarations.len())
            .map_err(|_| Failure::TypeResource)?;
        for declaration in &self.declarations {
            let fact = &declaration.fact;
            let checked_application = &declaration.provider_application;
            let interface = checked_application.interface();
            let provided = fact.provided.instance.effect();
            if interface.module() != fact.id.module()
                || provided.module() != fact.id.module()
                || associated_interfaces
                    .insert(interface, fact.id)
                    .is_some_and(|owner| owner != fact.id)
                || associated_effects
                    .insert(provided, fact.id)
                    .is_some_and(|owner| owner != fact.id)
            {
                return Err(Failure::InvalidState);
            }
            let canonical = &declaration.acquire.canonical;
            let signature = canonical
                .owner_signature(crate::resolved::OwnerId::Interface(interface))
                .ok_or(Failure::InvalidState)?;
            if signature.parameters.len() != checked_application.arguments().len() {
                return Err(Failure::InvalidState);
            }
            authenticate_provider_application_witness(fact, checked_application, work)?;
            if fact.id.module() != self.module || fact.family.module() != self.module {
                return Err(Failure::InvalidState);
            }
            let origin = authenticate_contract_origin(&fact.origin, &self.sources, work)?;
            work.charge(self.sources.len())
                .map_err(|()| Failure::TypeResource)?;
            if !self
                .sources
                .iter()
                .any(|(module, source)| *module == self.module && source.id() == origin)
            {
                return Err(Failure::InvalidState);
            }
            for (ordinal, lifecycle) in [(0, &declaration.acquire), (1, &declaration.finish)] {
                if lifecycle.template != ProviderTemplateId::new(fact.id, ordinal)
                    || lifecycle.phase
                        != if ordinal == 0 {
                            Phase::Acquire
                        } else {
                            Phase::Finish
                        }
                    || lifecycle.parameter.module() != Some(self.module)
                    || lifecycle.formals.len() != fact.parameters.len()
                {
                    return Err(Failure::InvalidState);
                }
                work.charge(
                    lifecycle
                        .formals
                        .len()
                        .checked_add(2)
                        .ok_or(Failure::TypeResource)?,
                )
                .map_err(|()| Failure::TypeResource)?;
                let mut generated = HashSet::new();
                generated
                    .try_reserve(lifecycle.formals.len() + 2)
                    .map_err(|_| Failure::TypeResource)?;
                if !matches!(lifecycle.hidden_answer, TypeVariableId::Generated(_))
                    || !generated.insert(lifecycle.hidden_answer)
                {
                    return Err(Failure::InvalidState);
                }
                let hidden_row = match lifecycle.hidden_row {
                    EffectRowVariable::Rigid(row) => row,
                    _ => return Err(Failure::InvalidState),
                };
                if !matches!(hidden_row, TypeVariableId::Generated(_))
                    || !generated.insert(hidden_row)
                {
                    return Err(Failure::InvalidState);
                }
                for ((source, actual), parameter) in lifecycle.formals.iter().zip(&fact.parameters)
                {
                    if *source != parameter.id
                        || !matches!(actual, TypeVariableId::Generated(_))
                        || !generated.insert(*actual)
                    {
                        return Err(Failure::InvalidState);
                    }
                }
                authenticate_contract_origin(
                    lifecycle.parameter_origin.as_origin(),
                    &self.sources,
                    work,
                )?;
                lifecycle
                    .externals
                    .authenticate_publication(committed, work)
                    .map_err(contract_validation_failure)?;
                for origin in lifecycle.externals.defining_origins() {
                    authenticate_contract_origin(origin, &self.sources, work)?;
                }
                authenticate_contract_native_registry(
                    &lifecycle.canonical,
                    fact,
                    &self.sources,
                    authenticated_native_facts,
                    &mut authenticated_native_origins,
                    work,
                )?;
            }
            declaration
                .handlers
                .authenticate(fact, committed, work)
                .map_err(contract_validation_failure)?;
            for origin in declaration.handlers.defining_origins() {
                authenticate_contract_origin(origin, &self.sources, work)?;
            }
            authenticate_contract_native_registry(
                declaration.handlers.canonical_registry(),
                fact,
                &self.sources,
                authenticated_native_facts,
                &mut authenticated_native_origins,
                work,
            )?;
        }
        Ok(())
    }
    pub(crate) fn authenticate_linked_native_facts(
        &self,
        linked: &crate::resolved::ResolvedRegistry,
        work: &mut TypeWorkBudget,
    ) -> Result<(), crate::resolved::ResolvedBuildFailure> {
        use crate::resolved::ResolvedBuildFailure as Failure;
        work.charge(
            self.declarations
                .len()
                .checked_mul(4)
                .ok_or(Failure::TypeResource)?,
        )
        .map_err(|()| Failure::TypeResource)?;
        for declaration in &self.declarations {
            for canonical in [
                &*declaration.acquire.canonical,
                &*declaration.finish.canonical,
                declaration.handlers.canonical_registry(),
            ] {
                for native in canonical.foreign_modules() {
                    work.charge(1).map_err(|()| Failure::TypeResource)?;
                    let mut found = false;
                    for actual in linked.foreign_modules() {
                        work.charge(1).map_err(|()| Failure::TypeResource)?;
                        if actual.admission.module_id == native.admission.module_id {
                            if !Arc::ptr_eq(actual, native) {
                                return Err(Failure::InvalidState);
                            }
                            found = true;
                        }
                    }
                    if !found {
                        return Err(Failure::InvalidState);
                    }
                }
            }
        }
        Ok(())
    }

    pub(crate) fn module(&self) -> crate::module::ModuleId {
        self.module
    }
    pub(crate) fn resource_contracts(
        &self,
    ) -> impl Iterator<
        Item = (
            &str,
            bool,
            &std::sync::Arc<crate::resolved::ResourceTypeFact>,
        ),
    > {
        self.declarations.iter().map(|declaration| {
            (
                declaration.spelling.as_str(),
                declaration.public,
                &declaration.fact,
            )
        })
    }
}
impl CheckedLifecycleTemplate {
    fn authenticate_state_associations(&self, work: &mut TypeWorkBudget) -> Result<(), TypeError> {
        work.charge(self.associations.len())
            .map_err(|()| type_resource())?;
        let mut borrowed = Vec::new();
        borrowed
            .try_reserve_exact(self.associations.len())
            .map_err(|_| type_resource())?;
        borrowed.extend(self.associations.iter().map(|association| {
            crate::core::provider::DraftStateAssociation {
                definition: association.definition,
                family: association.family,
                parameters: &association.parameters,
                state: &association.state,
            }
        }));
        crate::core::provider::check_original_state_access_associations(
            &self.draft.core,
            &borrowed,
            work,
        )
        .map_err(contract_validation_failure)
        .map_err(super::resolved_build_error)
    }
    fn original_authority(&self) -> &crate::core::provider::LifecycleOriginal {
        &self.original
    }
    fn authenticate_contract(
        &self,
        fact: &crate::resolved::ResourceTypeFact,
        work: &mut TypeWorkBudget,
    ) -> Result<(), LifecycleDraftCheckError> {
        let phase = match self.draft.phase {
            Phase::Acquire => crate::core::provider::LifecyclePhase::Acquire,
            Phase::Finish => crate::core::provider::LifecyclePhase::Finish,
            _ => return Err(LifecycleDraftCheckError::InvalidEntry),
        };
        crate::core::provider::check_lifecycle_entry(
            &self.draft.core,
            &crate::core::provider::LifecycleEntryContext {
                definition: crate::core::provider::LifecycleDefinitionView::retained(
                    fact,
                    self.draft.parameter,
                    self.parameter_origin.as_origin(),
                ),
                template: self.draft.id,
                phase,
                body: self.draft.body,
                parameter: self.draft.parameter,
                hidden_answer: self.draft.hidden_answer,
                hidden_row: self.draft.hidden_row,
                formal_parameters: &self.draft.formal_parameters,
            },
            work,
        )
        .map_err(LifecycleDraftCheckError::Core)?;
        let occurrences = &self
            .draft
            .staged_externals
            .as_ref()
            .ok_or(LifecycleDraftCheckError::InvalidEntry)?
            .occurrences;
        work.charge(occurrences.len())
            .map_err(|()| LifecycleDraftCheckError::Resource)?;
        if occurrences
            .iter()
            .any(|occurrence| occurrence.node.is_none())
        {
            return Err(LifecycleDraftCheckError::InvalidEntry);
        }
        self.externals
            .authenticate_owners(
                &self.draft.core,
                occurrences.iter().map(|occurrence| {
                    (
                        occurrence.node.expect("checked above"),
                        &occurrence.occurrence,
                    )
                }),
                work,
            )
            .map_err(LifecycleDraftCheckError::Core)
    }
    fn contract_certificate(
        &self,
        fact: &crate::resolved::ResourceTypeFact,
        work: &mut TypeWorkBudget,
    ) -> Result<LifecycleContractCertificate, LifecycleDraftCheckError> {
        self.authenticate_contract(fact, work)?;
        work.charge(self.draft.formal_parameters.len())
            .map_err(|()| LifecycleDraftCheckError::Resource)?;
        let mut formals = Vec::new();
        formals
            .try_reserve_exact(self.draft.formal_parameters.len())
            .map_err(|_| LifecycleDraftCheckError::Resource)?;
        formals.extend(
            self.draft
                .formal_parameters
                .iter()
                .map(|(source, generated, _)| (*source, *generated)),
        );
        Ok(LifecycleContractCertificate {
            template: self.draft.id,
            phase: self.draft.phase,
            parameter: self.draft.parameter,
            parameter_origin: Arc::clone(&self.parameter_origin),
            hidden_answer: self.draft.hidden_answer,
            hidden_row: self.draft.hidden_row,
            formals,
            canonical: Arc::clone(&self.canonical),
            externals: Arc::clone(&self.externals),
        })
    }
}

pub(super) fn contract_validation_failure(
    failure: crate::core::ValidationError,
) -> crate::resolved::ResolvedBuildFailure {
    if failure.reason() == crate::core::ValidationReason::Resource {
        crate::resolved::ResolvedBuildFailure::TypeResource
    } else {
        crate::resolved::ResolvedBuildFailure::InvalidState
    }
}
fn authenticate_contract_origin(
    origin: &crate::source::Origin,
    sources: &[(
        crate::module::ModuleId,
        std::sync::Arc<crate::source::SourceFile>,
    )],
    work: &mut TypeWorkBudget,
) -> Result<crate::source::SourceId, crate::resolved::ResolvedBuildFailure> {
    use crate::resolved::ResolvedBuildFailure as Failure;
    let validate = |span: crate::source::Span, work: &mut TypeWorkBudget| {
        work.charge(sources.len())
            .map_err(|()| Failure::TypeResource)?;
        let source = sources
            .iter()
            .find(|(_, source)| source.id() == span.source())
            .ok_or(Failure::InvalidState)?;
        source
            .1
            .span(span.range())
            .map_err(|_| Failure::InvalidState)?;
        Ok::<_, Failure>(())
    };
    let mut current = origin;
    loop {
        work.charge(1).map_err(|()| Failure::TypeResource)?;
        match current {
            crate::source::Origin::Source(span) => {
                validate(*span, work)?;
                return Ok(span.source());
            }
            crate::source::Origin::Generated { cause, .. } => current = cause,
            crate::source::Origin::Related { primary, related } => {
                work.charge(related.len())
                    .map_err(|()| Failure::TypeResource)?;
                for span in related {
                    validate(*span, work)?;
                }
                current = primary;
            }
        }
    }
}
fn authenticate_contract_native_registry<'a>(
    registry: &'a crate::resolved::ResolvedRegistry,
    fact: &crate::resolved::ResourceTypeFact,
    sources: &[(
        crate::module::ModuleId,
        std::sync::Arc<crate::source::SourceFile>,
    )],
    authenticated: &mut crate::foreign::NativeAuthenticationMemo,
    authenticated_origins: &mut Vec<&'a Arc<crate::foreign::ForeignModuleFact>>,
    work: &mut TypeWorkBudget,
) -> Result<(), crate::resolved::ResolvedBuildFailure> {
    use crate::resolved::ResolvedBuildFailure as Failure;
    let mut registered = false;
    for native in registry.foreign_modules() {
        work.charge(
            native
                .effects
                .len()
                .checked_add(1)
                .ok_or(Failure::TypeResource)?,
        )
        .map_err(|()| Failure::TypeResource)?;
        registered |= native.effects.contains(&fact.interpreted.instance.effect());
        authenticated
            .authenticate(native, work)
            .map_err(|failure| {
                if failure.is_resource_exhaustion() {
                    Failure::TypeResource
                } else {
                    Failure::InvalidState
                }
            })?;
        work.charge(authenticated_origins.len())
            .map_err(|()| Failure::TypeResource)?;
        if !authenticated_origins
            .iter()
            .any(|previous| Arc::ptr_eq(previous, native))
        {
            // A caller's native memo cannot certify this source table. Retain
            // origin evidence only after all source mappings authenticate here.
            let source_id = authenticate_contract_origin(&native.admission.origin, sources, work)?;
            work.charge(sources.len())
                .map_err(|()| Failure::TypeResource)?;
            if !sources.iter().any(|(module, source)| {
                *module == native.admission.module_id && source.id() == source_id
            }) {
                return Err(Failure::InvalidState);
            }
            work.charge(native.operations.len())
                .map_err(|()| Failure::TypeResource)?;
            for operation in &native.operations {
                authenticate_contract_origin(&operation.origin, sources, work)?;
            }
            if let Some(access) = &native.state_access {
                authenticate_contract_origin(&access.origin, sources, work)?;
            }
            work.charge(1).map_err(|()| Failure::TypeResource)?;
            authenticated_origins
                .try_reserve_exact(1)
                .map_err(|_| Failure::TypeResource)?;
            authenticated_origins.push(native);
        }
    }
    if !registered {
        return Err(Failure::InvalidState);
    }
    Ok(())
}

struct CheckedProviderDeclaration {
    provider_application: std::sync::Arc<crate::interface::InterfaceApplication>,
    methods: std::sync::Arc<[(MethodId, OperationId)]>,
    spelling: String,
    public: bool,
    fact: std::sync::Arc<crate::resolved::ResourceTypeFact>,
    acquire: CheckedLifecycleTemplate,
    finish: CheckedLifecycleTemplate,
    handlers: CheckedConditionalHandler,
}

// Equality identifies the one immutable independently admitted defining proof.
// Equal copied headers or separately compiled graphs do not share authority.
impl PartialEq for CheckedProviderGroup {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self, other)
    }
}
impl Eq for CheckedProviderGroup {}

impl CheckedProviderGroup {
    /// Authenticates unpublished original code against this exact local
    /// transaction. Empty slots alone do not authenticate their selected facts.
    pub(super) fn local_template_view<'a>(
        &'a self,
        certificate: &Arc<CheckedProviderContracts>,
        facts: crate::resolved::ProviderExternalFacts<'a>,
        publication: &'a PendingEvidencePublication,
        work: &mut TypeWorkBudget,
    ) -> Result<(), TypeError> {
        if !Arc::ptr_eq(&self.contracts, certificate) || self.module != certificate.module {
            return Err(invalid_state());
        }
        certificate
            .authenticate(false, work)
            .map_err(super::resolved_build_error)?;
        work.charge(self.declarations.len())
            .map_err(|()| type_resource())?;
        for (declaration, contract) in self.declarations.iter().zip(&certificate.declarations) {
            for (lifecycle, original) in [
                (&declaration.acquire, &contract.acquire),
                (&declaration.finish, &contract.finish),
            ] {
                lifecycle
                    .externals
                    .authenticate_pending(
                        publication,
                        facts,
                        &original.canonical,
                        self.module,
                        work,
                    )
                    .map_err(contract_validation_failure)
                    .map_err(super::resolved_build_error)?;
            }
            declaration
                .handlers
                .template
                .authenticate_pending(
                    publication,
                    facts,
                    contract.handlers.canonical_registry(),
                    self.module,
                    work,
                )
                .map_err(contract_validation_failure)
                .map_err(super::resolved_build_error)?;
        }
        self.authenticate_code_relations(certificate, work)
            .map_err(super::resolved_build_error)?;
        Ok(())
    }

    /// Authenticates the separately supplied immutable code against the
    /// canonical certificate, then checks its actual entry and graph relations.
    pub(crate) fn authenticate_code(
        &self,
        certificate: &std::sync::Arc<CheckedProviderContracts>,
        work: &mut TypeWorkBudget,
    ) -> Result<(), crate::resolved::ResolvedBuildFailure> {
        use crate::resolved::ResolvedBuildFailure as Failure;
        if !Arc::ptr_eq(&self.contracts, certificate) || self.module != certificate.module {
            return Err(Failure::InvalidState);
        }
        certificate.authenticate(true, work)?;
        self.authenticate_code_relations(certificate, work)
    }

    fn authenticate_code_relations(
        &self,
        certificate: &Arc<CheckedProviderContracts>,
        work: &mut TypeWorkBudget,
    ) -> Result<(), crate::resolved::ResolvedBuildFailure> {
        use crate::resolved::ResolvedBuildFailure as Failure;
        work.charge(self.declarations.len())
            .map_err(|()| Failure::TypeResource)?;
        if self.declarations.len() != certificate.declarations.len() {
            return Err(Failure::InvalidState);
        }
        for (code, contract) in self.declarations.iter().zip(&certificate.declarations) {
            authenticate_original_relation(code, contract, work)?;
        }
        Ok(())
    }
    pub(crate) fn contracts(&self) -> &std::sync::Arc<CheckedProviderContracts> {
        &self.contracts
    }
    pub(crate) fn module(&self) -> crate::module::ModuleId {
        self.module
    }
}

impl std::fmt::Debug for CheckedProviderGroup {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("CheckedProviderGroup")
            .field("module", &self.module)
            .field("declarations", &self.declarations.len())
            .finish_non_exhaustive()
    }
}

fn declaration_template_source<'a>(
    declaration: &'a CheckedProviderDeclaration,
    work: &mut TypeWorkBudget,
) -> Result<ProviderTemplateSource<'a>, TypeError> {
    fn lifecycle<'a>(
        entry: &'a CheckedLifecycleTemplate,
        work: &mut TypeWorkBudget,
    ) -> Result<LifecycleTemplateSource<'a>, TypeError> {
        entry.authenticate_state_associations(work)?;
        Ok(LifecycleTemplateSource {
            original: entry.original_authority(),
            program: &entry.draft.core,
            body: entry.draft.body,
            occurrences: &entry
                .draft
                .staged_externals
                .as_ref()
                .ok_or_else(invalid_state)?
                .occurrences,
        })
    }
    Ok(ProviderTemplateSource {
        fact: &declaration.fact,
        acquire: lifecycle(&declaration.acquire, work)?,
        finish: lifecycle(&declaration.finish, work)?,
        handler: &declaration.handlers.template,
        handler_occurrences: &declaration.handlers.staged_externals.occurrences,
        methods: &declaration.methods,
    })
}

fn prepared_declaration_template_source(
    declaration: &CheckedProviderDeclaration,
) -> Result<ProviderTemplateSource<'_>, TypeError> {
    fn lifecycle(
        entry: &CheckedLifecycleTemplate,
    ) -> Result<LifecycleTemplateSource<'_>, TypeError> {
        Ok(LifecycleTemplateSource {
            original: entry.original_authority(),
            program: &entry.draft.core,
            body: entry.draft.body,
            occurrences: &entry
                .draft
                .staged_externals
                .as_ref()
                .ok_or_else(invalid_state)?
                .occurrences,
        })
    }
    Ok(ProviderTemplateSource {
        fact: &declaration.fact,
        acquire: lifecycle(&declaration.acquire)?,
        finish: lifecycle(&declaration.finish)?,
        handler: &declaration.handlers.template,
        handler_occurrences: &declaration.handlers.staged_externals.occurrences,
        methods: &declaration.methods,
    })
}

fn authenticate_original_relation(
    code: &CheckedProviderDeclaration,
    contract: &ProviderDeclarationContract,
    work: &mut TypeWorkBudget,
) -> Result<(), crate::resolved::ResolvedBuildFailure> {
    use crate::resolved::ResolvedBuildFailure as Failure;
    if !Arc::ptr_eq(&code.fact, &contract.fact)
        || !Arc::ptr_eq(&code.provider_application, &contract.provider_application)
        || !Arc::ptr_eq(&code.methods, &contract.methods)
        || code.public != contract.public
    {
        return Err(Failure::InvalidState);
    }
    for (entry, proof) in [
        (&code.acquire, &contract.acquire),
        (&code.finish, &contract.finish),
    ] {
        work.charge(entry.draft.formal_parameters.len())
            .map_err(|()| Failure::TypeResource)?;
        if entry.draft.id != proof.template
            || entry.draft.phase != proof.phase
            || entry.draft.parameter != proof.parameter
            || entry.draft.hidden_answer != proof.hidden_answer
            || entry.draft.hidden_row != proof.hidden_row
            || !Arc::ptr_eq(&entry.parameter_origin, &proof.parameter_origin)
            || !Arc::ptr_eq(&entry.canonical, &proof.canonical)
            || !Arc::ptr_eq(&entry.externals, &proof.externals)
            || entry.draft.formal_parameters.len() != proof.formals.len()
            || !entry
                .draft
                .formal_parameters
                .iter()
                .zip(&proof.formals)
                .all(|((source, actual, _), expected)| (*source, *actual) == *expected)
        {
            return Err(Failure::InvalidState);
        }
        entry
            .authenticate_contract(&contract.fact, work)
            .map_err(|failure| match failure {
                LifecycleDraftCheckError::Resource => Failure::TypeResource,
                LifecycleDraftCheckError::Core(error) => contract_validation_failure(error),
                LifecycleDraftCheckError::InvalidEntry => Failure::InvalidState,
            })?;
    }
    if !code
        .handlers
        .template
        .authenticates_certificate(&contract.handlers)
    {
        return Err(Failure::InvalidState);
    }
    let occurrences = &code.handlers.staged_externals.occurrences;
    work.charge(occurrences.len())
        .map_err(|()| Failure::TypeResource)?;
    if occurrences
        .iter()
        .any(|occurrence| occurrence.node.is_none())
    {
        return Err(Failure::InvalidState);
    }
    code.handlers
        .template
        .authenticate_contract(
            &contract.fact,
            occurrences.iter().map(|occurrence| {
                (
                    occurrence.node.expect("checked above"),
                    &occurrence.occurrence,
                )
            }),
            work,
        )
        .map_err(contract_validation_failure)?;
    Ok(())
}

impl PreparedProviderOriginal {
    pub(super) fn authenticate_pending(
        &self,
        facts: crate::resolved::ProviderExternalFacts<'_>,
        publication: &PendingEvidencePublication,
        work: &mut TypeWorkBudget,
    ) -> Result<(), TypeError> {
        for (entry, proof) in [
            (&self.declaration.acquire, &self.contract.acquire),
            (&self.declaration.finish, &self.contract.finish),
        ] {
            entry
                .externals
                .authenticate_pending(
                    publication,
                    facts,
                    &proof.canonical,
                    self.declaration.fact.id.module(),
                    work,
                )
                .map_err(contract_validation_failure)
                .map_err(super::resolved_build_error)?;
        }
        self.declaration
            .handlers
            .template
            .authenticate_pending(
                publication,
                facts,
                self.contract.handlers.canonical_registry(),
                self.declaration.fact.id.module(),
                work,
            )
            .map_err(contract_validation_failure)
            .map_err(super::resolved_build_error)?;
        authenticate_original_relation(&self.declaration, &self.contract, work)
            .map_err(super::resolved_build_error)
    }
}

pub(super) fn check_module_provider_group(
    module: &crate::resolved::ResolvedModule,
    defining: Option<&std::sync::Arc<crate::resolved::ProviderDefiningFacts>>,
    publication: &mut crate::evidence::PendingEvidencePublication,
    type_work: &mut TypeWorkBudget,
    coverage_work: &mut super::UsefulnessBudget,
    constraint_work: &mut super::InterfaceConstraintBudget,
) -> Result<Option<std::sync::Arc<CheckedProviderGroup>>, TypeError> {
    if module.resources().is_empty() {
        return Ok(None);
    }
    let preparation = prepare_module_provider_originals(
        module,
        defining,
        type_work,
        coverage_work,
        constraint_work,
    )?;
    let mut components = Vec::new();
    type_work
        .charge(module.resources().len())
        .map_err(|()| type_resource())?;
    components
        .try_reserve_exact(module.resources().len())
        .map_err(|_| type_resource())?;
    for index in 0..module.resources().len() {
        components.push(check_module_provider_original(
            module,
            &preparation,
            index,
            defining,
            publication,
            type_work,
            coverage_work,
            constraint_work,
        )?);
    }
    finish_module_provider_originals(module, &components, type_work).map(Some)
}

/// Private original preparation; no incomplete source group can be exported.
pub(super) struct ModuleProviderOriginals {
    registry: Arc<crate::resolved::ResolvedRegistry>,
    headers: Vec<ProviderHeader>,
    native_authentication: crate::foreign::NativeAuthenticationSession,
}

pub(super) fn prepare_module_provider_originals(
    module: &ResolvedModule,
    defining: Option<&Arc<crate::resolved::ProviderDefiningFacts>>,
    type_work: &mut TypeWorkBudget,
    coverage_work: &mut super::UsefulnessBudget,
    constraint_work: &mut super::InterfaceConstraintBudget,
) -> Result<ModuleProviderOriginals, TypeError> {
    // Every declaration in this group borrows the same immutable module. Share
    // its authenticated source inventory and template registry; each compiler
    // context and each final Core admission still checks its own occurrence.
    module
        .authenticate_owner_definitions(type_work)
        .map_err(super::resolved_build_error)?;
    let registry = Arc::new(
        module
            .registry()
            .provider_template_view(module.imported_facts(), type_work)
            .map_err(super::resolved_build_error)?,
    );
    type_work
        .charge(module.resources().len())
        .map_err(|()| type_resource())?;
    let mut headers = Vec::new();
    headers
        .try_reserve_exact(module.resources().len())
        .map_err(|_| type_resource())?;
    for definition in module.resources() {
        headers.push(with_module_provider_compiler(
            module,
            &registry,
            defining,
            type_work,
            coverage_work,
            constraint_work,
            |compiler| compiler.check_provider_header(module, definition),
        )?);
    }
    Ok(ModuleProviderOriginals {
        registry,
        headers,
        native_authentication: crate::foreign::NativeAuthenticationSession::default(),
    })
}

/// One checked original and its immutable certificate. Readiness permits only
/// source preparation; final Core requires membership in the complete group.
pub(crate) struct PreparedProviderOriginal {
    declaration: Arc<CheckedProviderDeclaration>,
    contract: Arc<ProviderDeclarationContract>,
}

#[allow(clippy::too_many_arguments)]
pub(super) fn check_module_provider_original(
    module: &ResolvedModule,
    preparation: &ModuleProviderOriginals,
    index: usize,
    defining: Option<&Arc<crate::resolved::ProviderDefiningFacts>>,
    publication: &mut PendingEvidencePublication,
    type_work: &mut TypeWorkBudget,
    coverage_work: &mut super::UsefulnessBudget,
    constraint_work: &mut super::InterfaceConstraintBudget,
) -> Result<Arc<PreparedProviderOriginal>, TypeError> {
    let definition = module.resources().get(index).ok_or_else(invalid_state)?;
    let header = preparation.headers.get(index).ok_or_else(invalid_state)?;
    let mut acquire = with_module_provider_compiler(
        module,
        &preparation.registry,
        defining,
        type_work,
        coverage_work,
        constraint_work,
        |compiler| {
            compiler
                .type_work
                .charge(preparation.headers.len())
                .map_err(|()| type_resource())?;
            let mut associations = Vec::new();
            associations
                .try_reserve_exact(preparation.headers.len())
                .map_err(|_| type_resource())?;
            for header in &preparation.headers {
                associations.push(
                    header
                        .state_association
                        .clone_with_budget(&mut compiler.type_work)?,
                );
            }
            compiler.compile_provider_lifecycle_with_externals_and_associations(
                definition,
                header,
                Phase::Acquire,
                module.imported_facts(),
                associations,
            )
        },
    )?
    .admit_from_defining_module_with_native_memo(
        module,
        Some(&preparation.native_authentication),
        type_work,
    )
    .map_err(module_provider_failure)?;

    let mut finish = with_module_provider_compiler(
        module,
        &preparation.registry,
        defining,
        type_work,
        coverage_work,
        constraint_work,
        |compiler| {
            compiler
                .type_work
                .charge(preparation.headers.len())
                .map_err(|()| type_resource())?;
            let mut associations = Vec::new();
            associations
                .try_reserve_exact(preparation.headers.len())
                .map_err(|_| type_resource())?;
            for header in &preparation.headers {
                associations.push(
                    header
                        .state_association
                        .clone_with_budget(&mut compiler.type_work)?,
                );
            }
            compiler.compile_provider_lifecycle_with_externals_and_associations(
                definition,
                header,
                Phase::Finish,
                module.imported_facts(),
                associations,
            )
        },
    )?
    .admit_from_defining_module_with_native_memo(
        module,
        Some(&preparation.native_authentication),
        type_work,
    )
    .map_err(module_provider_failure)?;

    let handler = with_module_provider_compiler(
        module,
        &preparation.registry,
        defining,
        type_work,
        coverage_work,
        constraint_work,
        |compiler| compiler.compile_provider_handler(definition, header, module.imported_facts()),
    )?;
    type_work
        .charge(
            module
                .defining_sources()
                .len()
                .checked_mul(2)
                .ok_or_else(type_resource)?,
        )
        .map_err(|()| type_resource())?;
    let mut sources = Vec::new();
    let mut module_sources = Vec::new();
    sources
        .try_reserve_exact(module.defining_sources().len())
        .map_err(|_| type_resource())?;
    module_sources
        .try_reserve_exact(module.defining_sources().len())
        .map_err(|_| type_resource())?;
    for (id, source) in module.defining_sources() {
        sources.push(&**source);
        module_sources.push((*id, source.id()));
    }
    let mut handlers = handler
        .admit_with_native_memo(
            module,
            &sources,
            &module_sources,
            Some(&preparation.native_authentication),
            type_work,
        )
        .map_err(module_provider_failure)?;

    let fact = Arc::new(
        crate::resolved::ResourceTypeFact::from_definition_with_budget(definition, type_work)
            .map_err(|()| type_resource())?,
    );
    for staged in [
        acquire
            .draft
            .staged_externals
            .as_mut()
            .ok_or_else(invalid_state)?,
        finish
            .draft
            .staged_externals
            .as_mut()
            .ok_or_else(invalid_state)?,
        &mut handlers.staged_externals,
    ] {
        publication
            .append(std::mem::take(&mut staged.publication), constraint_work)
            .map_err(|failure| selection_failure(failure, None))?;
    }
    type_work
        .charge(definition.spelling.len())
        .map_err(|()| type_resource())?;
    let mut spelling = String::new();
    spelling
        .try_reserve_exact(definition.spelling.len())
        .map_err(|_| type_resource())?;
    spelling.push_str(&definition.spelling);
    type_work
        .charge(header.methods.len())
        .map_err(|()| type_resource())?;
    let mut methods = Vec::new();
    methods
        .try_reserve_exact(header.methods.len())
        .map_err(|_| type_resource())?;
    methods.extend_from_slice(&header.methods);
    type_work.charge(1).map_err(|()| type_resource())?;
    let declaration = Arc::new(CheckedProviderDeclaration {
        methods: Arc::from(methods.into_boxed_slice()),
        provider_application: Arc::new(
            header
                .provider_application
                .clone_with_budget(type_work)
                .map_err(|()| type_resource())?,
        ),
        spelling,
        public: definition.public,
        fact,
        acquire,
        finish,
        handlers,
    });
    let acquire = declaration
        .acquire
        .contract_certificate(&declaration.fact, type_work)
        .map_err(module_provider_failure)?;
    let finish = declaration
        .finish
        .contract_certificate(&declaration.fact, type_work)
        .map_err(module_provider_failure)?;
    let occurrences = &declaration.handlers.staged_externals.occurrences;
    type_work
        .charge(occurrences.len())
        .map_err(|()| type_resource())?;
    if occurrences
        .iter()
        .any(|occurrence| occurrence.node.is_none())
    {
        return Err(invalid_state());
    }
    declaration
        .handlers
        .template
        .authenticate_contract(
            &declaration.fact,
            occurrences.iter().map(|occurrence| {
                (
                    occurrence.node.expect("checked above"),
                    &occurrence.occurrence,
                )
            }),
            type_work,
        )
        .map_err(|failure| module_provider_failure(LifecycleDraftCheckError::Core(failure)))?;
    type_work
        .charge(declaration.spelling.len())
        .map_err(|()| type_resource())?;
    let mut spelling = String::new();
    spelling
        .try_reserve_exact(declaration.spelling.len())
        .map_err(|_| type_resource())?;
    spelling.push_str(&declaration.spelling);
    type_work.charge(1).map_err(|()| type_resource())?;
    let contract = Arc::new(ProviderDeclarationContract {
        methods: Arc::clone(&declaration.methods),
        provider_application: Arc::clone(&declaration.provider_application),
        spelling,
        public: declaration.public,
        fact: Arc::clone(&declaration.fact),
        acquire,
        finish,
        handlers: declaration.handlers.template.contract_certificate(),
    });
    type_work.charge(1).map_err(|()| type_resource())?;
    let component = Arc::new(PreparedProviderOriginal {
        declaration,
        contract,
    });
    Ok(component)
}

pub(super) fn finish_module_provider_originals(
    module: &ResolvedModule,
    components: &[Arc<PreparedProviderOriginal>],
    type_work: &mut TypeWorkBudget,
) -> Result<Arc<CheckedProviderGroup>, TypeError> {
    if components.len() != module.resources().len() {
        return Err(invalid_state());
    }
    type_work
        .charge(components.len().checked_mul(2).ok_or_else(type_resource)?)
        .map_err(|()| type_resource())?;
    let mut declarations = Vec::new();
    let mut contracts = Vec::new();
    declarations
        .try_reserve_exact(components.len())
        .map_err(|_| type_resource())?;
    contracts
        .try_reserve_exact(components.len())
        .map_err(|_| type_resource())?;
    for (definition, component) in module.resources().iter().zip(components) {
        type_work.charge(1).map_err(|()| type_resource())?;
        if definition.id != component.declaration.fact.id
            || definition.id != component.contract.fact.id
        {
            return Err(invalid_state());
        }
        if !Arc::ptr_eq(&component.declaration.fact, &component.contract.fact)
            || !Arc::ptr_eq(
                &component.declaration.provider_application,
                &component.contract.provider_application,
            )
            || !Arc::ptr_eq(&component.declaration.methods, &component.contract.methods)
            || component.declaration.public != component.contract.public
        {
            return Err(invalid_state());
        }
        declarations.push(Arc::clone(&component.declaration));
        contracts.push(Arc::clone(&component.contract));
    }

    type_work
        .charge(module.defining_sources().len())
        .map_err(|()| type_resource())?;
    let mut sources = Vec::new();
    sources
        .try_reserve_exact(module.defining_sources().len())
        .map_err(|_| type_resource())?;
    sources.extend(
        module
            .defining_sources()
            .iter()
            .map(|(id, source)| (*id, Arc::clone(source))),
    );
    let contracts = Arc::new(CheckedProviderContracts {
        module: module.module(),
        declarations: contracts,
        sources,
    });
    Ok(Arc::new(CheckedProviderGroup {
        contracts,
        module: module.module(),
        declarations,
    }))
}

fn module_provider_failure(failure: LifecycleDraftCheckError) -> TypeError {
    match failure {
        LifecycleDraftCheckError::Resource => type_resource(),
        LifecycleDraftCheckError::Core(failure)
            if failure.reason() == crate::core::ValidationReason::Resource =>
        {
            type_resource()
        }
        LifecycleDraftCheckError::InvalidEntry | LifecycleDraftCheckError::Core(_) => {
            invalid_state()
        }
    }
}

fn with_module_provider_compiler<T>(
    module: &crate::resolved::ResolvedModule,
    registry: &Arc<crate::resolved::ResolvedRegistry>,
    defining: Option<&std::sync::Arc<crate::resolved::ProviderDefiningFacts>>,
    type_work: &mut TypeWorkBudget,
    coverage_work: &mut super::UsefulnessBudget,
    constraint_work: &mut super::InterfaceConstraintBudget,
    check: impl FnOnce(&mut CoreElaborator<EffectOperationFamily>) -> Result<T, TypeError>,
) -> Result<T, TypeError> {
    let compiler_result =
        CoreElaborator::<EffectOperationFamily>::for_module_with_registry_and_work(
            module,
            Arc::clone(registry),
            type_work,
            coverage_work.clone(),
        );

    let mut compiler = compiler_result?;
    compiler.provider_defining_facts = defining.map(Arc::clone);
    std::mem::swap(&mut compiler.constraint_work, constraint_work);
    let result = (|| {
        if let Some(defining) = defining {
            compiler
                .type_work
                .charge(defining.globals.len())
                .map_err(|()| type_resource())?;
            for global in &defining.globals {
                let quantified = super::clone_kinded_type_parameters_with_budget(
                    &global.scheme.type_parameters,
                    &mut compiler.type_work,
                )
                .map_err(|()| type_resource())?
                .into_boxed_slice();
                let body = IterativeTypeOwner::new(
                    super::clone_type_with_budget(
                        &global.scheme.value_type,
                        &mut compiler.type_work,
                    )
                    .map_err(|()| type_resource())?,
                );
                let provenance = super::at_span_provenance_with_budget(
                    &body,
                    global.origin.as_origin().primary_span(),
                    &mut compiler.type_work,
                )
                .map_err(|()| type_resource())?;
                if compiler.base_context.insert_with_provenance(
                    global.binder,
                    body.into_inner(),
                    provenance,
                )? {
                    return Err(invalid_state());
                }
                compiler
                    .base_context
                    .set_quantified(global.binder, quantified)?;
            }
        }
        check(&mut compiler)
    })();

    *type_work = std::mem::take(&mut compiler.type_work);
    *coverage_work = std::mem::take(&mut compiler.coverage_work);
    std::mem::swap(&mut compiler.constraint_work, constraint_work);
    result
}

#[derive(Debug)]
enum LifecycleDraftCheckError {
    Resource,
    InvalidEntry,
    Core(crate::core::ValidationError),
}

impl LifecycleTemplateDraft {
    #[cfg(test)]
    fn check_flow(
        &self,
        definition: &ResolvedResourceDefinition,
        work: &mut TypeWorkBudget,
    ) -> Result<(), LifecycleDraftCheckError> {
        self.check_flow_with_associations(definition, &[], work)
    }

    #[cfg(test)]
    fn check_flow_with_associations(
        &self,
        definition: &ResolvedResourceDefinition,
        associations: &[crate::core::provider::DraftStateAssociation<'_>],
        work: &mut TypeWorkBudget,
    ) -> Result<(), LifecycleDraftCheckError> {
        self.check_flow_with_external_context(definition, associations, None, work)
    }

    fn check_flow_with_external_context(
        &self,
        definition: &ResolvedResourceDefinition,
        associations: &[crate::core::provider::DraftStateAssociation<'_>],
        externals: Option<&crate::core::provider::AuthenticatedProviderExternals<'_>>,
        work: &mut TypeWorkBudget,
    ) -> Result<(), LifecycleDraftCheckError> {
        crate::core::provider::check_lifecycle_entry(
            &self.core,
            &crate::core::provider::LifecycleEntryContext {
                definition: crate::core::provider::LifecycleDefinitionView::source(
                    definition,
                    match self.phase {
                        Phase::Acquire => crate::core::provider::LifecyclePhase::Acquire,
                        Phase::Finish => crate::core::provider::LifecyclePhase::Finish,
                        _ => return Err(LifecycleDraftCheckError::InvalidEntry),
                    },
                ),
                template: self.id,
                phase: match self.phase {
                    Phase::Acquire => crate::core::provider::LifecyclePhase::Acquire,
                    Phase::Finish => crate::core::provider::LifecyclePhase::Finish,
                    _ => return Err(LifecycleDraftCheckError::InvalidEntry),
                },
                body: self.body,
                parameter: self.parameter,
                hidden_answer: self.hidden_answer,
                hidden_row: self.hidden_row,
                formal_parameters: &self.formal_parameters,
            },
            work,
        )
        .map_err(LifecycleDraftCheckError::Core)?;
        let mut substitutions = OwnerReplacementBuffer::new();
        for (source, generated, kind) in &self.formal_parameters {
            substitutions
                .insert_fresh(*source, *generated, kind, work)
                .map_err(|_| LifecycleDraftCheckError::Resource)?;
        }
        let mut arguments = OwnedTypeBuffer(Vec::new());
        work.charge(definition.interpreted.instance.arguments().len())
            .map_err(|()| LifecycleDraftCheckError::Resource)?;
        arguments
            .try_reserve(definition.interpreted.instance.arguments().len())
            .map_err(|_| LifecycleDraftCheckError::Resource)?;
        for argument in definition.interpreted.instance.arguments() {
            let crate::types::KindedArgument::TypeArg(argument) = argument else {
                // Native declarations have authenticated Type coordinates.
                // A row cannot be projected away or passed as a native slot.
                return Err(LifecycleDraftCheckError::InvalidEntry);
            };
            arguments.push(
                substitutions
                    .substitute(argument, work)
                    .map_err(|_| LifecycleDraftCheckError::Resource)?,
            );
        }
        let native = crate::types::EffectInstance::from_type_arguments_with_budget(
            definition.interpreted.instance.effect(),
            arguments.into_boxed_slice(),
            work,
        )
        .map_err(|_| LifecycleDraftCheckError::Resource)?;
        let state = IterativeTypeOwner::new(
            substitutions
                .substitute(&definition.state.ty, work)
                .map_err(|_| LifecycleDraftCheckError::Resource)?,
        );
        let context = crate::core::provider::LifecycleFlowContext {
            phase: match self.phase {
                Phase::Acquire => crate::core::provider::LifecyclePhase::Acquire,
                Phase::Finish => crate::core::provider::LifecyclePhase::Finish,
                _ => return Err(LifecycleDraftCheckError::InvalidEntry),
            },
            body: self.body,
            parameter: self.parameter,
            native: &native,
            state: &state,
        };
        if let Some(externals) = externals {
            crate::core::provider::check_lifecycle_flow_with_externals(
                &self.core,
                &context,
                externals,
                associations,
                work,
            )
        } else {
            crate::core::provider::check_lifecycle_flow_with_associations(
                &self.core,
                &context,
                associations,
                work,
            )
        }
        .map_err(LifecycleDraftCheckError::Core)
    }
}

impl CoreElaborator<EffectOperationFamily> {
    fn install_provider_imports(
        &mut self,
        imported: &crate::resolved::ImportedFacts,
    ) -> Result<(), TypeError> {
        let mut selector = EvidenceSelector::new();
        for interface in imported.interface_imports() {
            selector
                .add_imported_interface_fact(
                    &self.registry,
                    &interface.fact,
                    &mut self.constraint_work,
                    &mut self.type_work,
                )
                .map_err(|failure| selection_failure(failure, None))?;
        }
        for global in imported.globals() {
            selector
                .add_imported_scheme(global, &mut self.constraint_work, &mut self.type_work)
                .map_err(|failure| selection_failure(failure, None))?;
        }
        for implementation in imported.implementations() {
            selector
                .add_implementation_fact(
                    &self.registry,
                    implementation,
                    &mut self.constraint_work,
                    &mut self.type_work,
                )
                .map_err(|failure| selection_failure(failure, None))?;
        }
        if let Some(defining) = &self.provider_defining_facts {
            self.type_work
                .charge(
                    defining
                        .interfaces
                        .len()
                        .checked_add(defining.globals.len())
                        .and_then(|count| count.checked_add(defining.implementations.len()))
                        .ok_or_else(type_resource)?,
                )
                .map_err(|()| type_resource())?;
            for interface in &defining.interfaces {
                selector
                    .add_interface_fact(
                        &self.registry,
                        interface,
                        &mut self.constraint_work,
                        &mut self.type_work,
                    )
                    .map_err(|failure| selection_failure(failure, None))?;
            }
            for global in &defining.globals {
                selector
                    .add_completed_provider_scheme(
                        crate::resolved::ProviderGlobalFact::Defining(global),
                        &mut self.constraint_work,
                        &mut self.type_work,
                    )
                    .map_err(|failure| selection_failure(failure, None))?;
            }
            for implementation in &defining.implementations {
                selector
                    .add_completed_local_implementation_fact(
                        &self.registry,
                        implementation,
                        &mut self.constraint_work,
                        &mut self.type_work,
                    )
                    .map_err(|failure| selection_failure(failure, None))?;
            }
        }
        self.selection = Some(selector);
        Ok(())
    }

    /// Source checking only. The shared continuation/direct-demand row equation
    /// is retained separately until its specialization contract is established.
    /// This draft cannot enter the template table or confer Core authority.
    #[cfg(test)]
    fn check_provider_handler_source(
        mut self,
        definition: &ResolvedResourceDefinition,
        header: &ProviderHeader,
        imported: &crate::resolved::ImportedFacts,
    ) -> Result<HandlerSourceDraft, TypeError> {
        let prepared = self.prepare_provider_handler_source(definition, header, imported)?;
        let pending_rows = self.cleanup_rows.take_provider_pending(
            &self.builder,
            prepared.clauses[0].body,
            &mut self.type_work,
        )?;
        Ok(HandlerSourceDraft {
            id: prepared.id,
            handler: prepared.handler,
            hidden_answer: prepared.hidden_answer,
            hidden_row: prepared.hidden_row,
            state_parameter: prepared.state_parameter,
            direct_demands: prepared.direct_demands,
            clauses: prepared.clauses,
            builder: self.builder,
            occurrences: self.provider_global_occurrences,
            pending_rows,
            #[cfg(test)]
            compile_work: self.type_work.used(),
        })
    }

    fn provider_original_row_contexts(
        &mut self,
        definition: &ResolvedResourceDefinition,
    ) -> Result<Vec<HashMap<TypeVariableId, EffectRow>>, TypeError> {
        // The first parameter is the nominal identity. Preserve the closed
        // provider path without another metadata traversal or allocation.
        if definition.parameters.len() <= 1 {
            return Ok(Vec::new());
        }
        self.type_work
            .charge(definition.parameters.len() - 1)
            .map_err(|()| type_resource())?;
        let row_count = definition.parameters[1..]
            .iter()
            .filter(|parameter| parameter.kind == Kind::EffectRow)
            .count();
        if row_count == 0 {
            return Ok(Vec::new());
        }
        let mut own_rows = HashSet::new();
        self.type_work
            .charge(definition.parameters.len() - 1)
            .map_err(|()| type_resource())?;
        own_rows
            .try_reserve(row_count)
            .map_err(|_| type_resource())?;
        for parameter in &definition.parameters[1..] {
            if parameter.kind == Kind::EffectRow && !own_rows.insert(parameter.id) {
                return Err(invalid_state());
            }
        }
        let mut contexts = Vec::new();
        for ty in [
            &definition.input.ty,
            &definition.state.ty,
            &definition.result.ty,
        ] {
            self.retain_provider_original_row_context(
                ty,
                &own_rows,
                &mut contexts,
                definition.span,
            )?;
        }
        let count = self
            .registry
            .effect(definition.provided.instance.effect())
            .ok_or_else(invalid_state)?
            .operations
            .len();
        self.type_work.charge(count).map_err(|()| type_resource())?;
        for index in 0..count {
            let operation = self
                .registry
                .effect(definition.provided.instance.effect())
                .ok_or_else(invalid_state)?
                .operations
                .get(index)
                .ok_or_else(invalid_state)?
                .id;
            // The canonical operation signature authenticates the effect,
            // ordinal and complete owner substitution. Its outer arrow is pure.
            let (domain, result) = self.operation_signature(
                &definition.provided.instance,
                operation,
                definition.span,
            )?;
            let domain = IterativeTypeOwner::new(domain);
            let result = IterativeTypeOwner::new(result);
            self.retain_provider_original_row_context(
                &domain,
                &own_rows,
                &mut contexts,
                definition.span,
            )?;
            self.retain_provider_original_row_context(
                &result,
                &own_rows,
                &mut contexts,
                definition.span,
            )?;
        }
        Ok(contexts)
    }

    fn retain_provider_original_row_context(
        &mut self,
        ty: &Type,
        own_rows: &HashSet<TypeVariableId>,
        contexts: &mut Vec<HashMap<TypeVariableId, EffectRow>>,
        span: Span,
    ) -> Result<(), TypeError> {
        let mut collected = HashMap::new();
        self.qualify_scheme_row_replacements(ty, &HashMap::new(), &mut collected, true)?;
        let mut own = HashMap::new();
        let mut free = HashMap::new();
        self.type_work
            .charge(collected.len())
            .map_err(|()| type_resource())?;
        for (binder, row) in collected {
            let destination = if own_rows.contains(&binder) {
                &mut own
            } else {
                &mut free
            };
            destination.try_reserve(1).map_err(|_| type_resource())?;
            destination.insert(binder, row);
        }
        if !crate::types::rigid_row_requirements_entailed_with_budget(
            &free,
            &self.expected_scheme_rows,
            &mut self.type_work,
        )
        .map_err(|()| type_resource())?
        {
            return Err(row_exclusion_error(span, Some(span)));
        }
        if !own.is_empty() {
            self.type_work.charge(1).map_err(|()| type_resource())?;
            contexts.try_reserve(1).map_err(|_| type_resource())?;
            contexts.push(own);
        }
        Ok(())
    }

    fn prepare_provider_handler_source(
        &mut self,
        definition: &ResolvedResourceDefinition,
        header: &ProviderHeader,
        imported: &crate::resolved::ImportedFacts,
    ) -> Result<PreparedHandlerSource, TypeError> {
        self.install_provider_imports(imported)?;
        let id = ProviderTemplateId::new(definition.id, 2);
        let hidden_answer = self.fresh_type_variable(&Kind::Type, definition.span)?;
        let hidden_row = self.fresh_type_variable(&Kind::EffectRow, definition.span)?;
        let declaration = self
            .registry
            .effect(definition.interpreted.instance.effect())
            .ok_or_else(invalid_state)?;
        self.type_work
            .charge(declaration.operations.len())
            .map_err(|()| type_resource())?;
        let mut operations = Vec::new();
        operations
            .try_reserve_exact(declaration.operations.len())
            .map_err(|_| type_resource())?;
        for operation in &declaration.operations {
            let fact = self
                .registry
                .foreign_operation(operation.id)
                .ok_or_else(invalid_state)?;
            if fact.role == ForeignOperationRole::Borrow {
                operations.push(operation.id);
            }
        }
        let native = clone_effect_instance_with_budget(
            &definition.interpreted.instance,
            &mut self.type_work,
        )
        .map_err(|error| TypeError::Internal(error.into()))?;
        let mut associations = Vec::new();
        self.type_work.charge(1).map_err(|()| type_resource())?;
        associations
            .try_reserve_exact(1)
            .map_err(|_| type_resource())?;
        associations.push(
            header
                .state_association
                .clone_with_budget(&mut self.type_work)?,
        );
        self.provider_occurrence_template = Some(id);
        self.provider_context = Some(CheckingContext {
            native,
            phase: Phase::Handler,
            operations: operations.into_boxed_slice(),
            state_associations: associations,
        });
        let marker = self.evidence_marker()?;
        let mut context = self.base_context.clone();
        reserve_context_entry(&mut context, &mut self.type_work).map_err(|()| type_resource())?;
        let state = &definition.handlers_binder;
        let state_type = IterativeTypeOwner::new(self.clone_type(&definition.state.ty)?);
        let provenance = self.at_span_provenance(&state_type, state.origin.primary_span())?;
        if context.insert_with_provenance(state.id, state_type.into_inner(), provenance)? {
            return Err(invalid_state());
        }
        let state_type = self.clone_type(&definition.state.ty)?;
        let state_parameter =
            self.builder
                .resolved_binder(state.id, state_type, state.origin.clone())?;
        let checkpoint = self.builder.type_rewrite_checkpoint();
        let original_rows = self.provider_original_row_contexts(definition)?;
        let row_depth = self.expected_scheme_rows.len();
        self.type_work
            .charge(original_rows.len())
            .map_err(|()| type_resource())?;
        self.expected_scheme_rows
            .try_reserve(original_rows.len())
            .map_err(|_| type_resource())?;
        self.expected_scheme_rows.extend(original_rows);
        let checked = self.check_effect_clauses(
            &definition.provided.instance,
            &definition.handlers,
            definition.span,
            &mut context,
            &Type::Variable(hidden_answer),
            EffectRow::empty(),
        );
        self.expected_scheme_rows.truncate(row_depth);
        let (handler, direct_demands, clauses) = checked?;
        self.close_evidence_obligations(marker)?;
        self.zonk_builder_types_since(Some(checkpoint), false)
            .map_err(TypeError::Internal)?;
        let direct_demands = self.zonk_effect_row(&direct_demands)?;
        Ok(PreparedHandlerSource {
            id,
            handler,
            hidden_answer,
            hidden_row: EffectRowVariable::rigid(hidden_row),
            state_parameter,
            direct_demands,
            clauses,
        })
    }

    fn compile_provider_handler(
        &mut self,
        definition: &ResolvedResourceDefinition,
        header: &ProviderHeader,
        imported: &crate::resolved::ImportedFacts,
    ) -> Result<CompiledHandlerDraft, TypeError> {
        let prepared = self.prepare_provider_handler_source(definition, header, imported)?;
        let publication = self.prepare_evidence_publication()?;
        self.type_work
            .charge(
                prepared
                    .clauses
                    .len()
                    .checked_mul(2)
                    .ok_or_else(type_resource)?,
            )
            .map_err(|()| type_resource())?;
        let mut roots = Vec::new();
        roots
            .try_reserve_exact(prepared.clauses.len())
            .map_err(|_| type_resource())?;
        roots.extend(prepared.clauses.iter().map(|clause| clause.body));
        let mut patterns = Vec::new();
        patterns
            .try_reserve_exact(prepared.clauses.len())
            .map_err(|_| type_resource())?;
        patterns.extend(prepared.clauses.iter().map(|clause| &*clause.pattern));
        let pending_rows = self.cleanup_rows.take_provider_pending(
            &self.builder,
            roots[0],
            &mut self.type_work,
        )?;
        let lowered = self.lower_provider_source_forest_with_pending(
            &roots,
            imported,
            publication,
            &OwnerReplacementBuffer::new(),
            &[&prepared.state_parameter],
            &patterns,
            pending_rows,
        )?;
        let mut clauses = Vec::new();
        self.type_work
            .charge(prepared.clauses.len())
            .map_err(|()| type_resource())?;
        clauses
            .try_reserve_exact(prepared.clauses.len())
            .map_err(|_| type_resource())?;
        let mut patterns = lowered.patterns;
        patterns.0.reverse();
        for (source, body) in prepared.clauses.into_iter().zip(lowered.roots) {
            let pattern = patterns.pop().ok_or_else(invalid_state)?.into_inner();
            clauses.push(crate::core::effect::EffectClause::new(
                source.operation,
                source.resume,
                crate::core::CoreMatchArm::new(pattern, body, source.origin),
            ));
        }
        let mut states = lowered.states;
        let state = states.pop().ok_or_else(invalid_state)?;
        if !states.is_empty() || !patterns.is_empty() {
            return Err(invalid_state());
        }
        Ok(CompiledHandlerDraft {
            #[cfg(test)]
            compile_work: self.type_work.used(),
            fragment: crate::core::provider::HandlerFragmentDraft {
                defining_facts: self.provider_defining_facts.as_ref().map(Arc::clone),
                program: lowered.core,
                template: prepared.id,
                handler: prepared.handler,
                state,
                hidden: [
                    (prepared.hidden_answer, Kind::Type),
                    (
                        match prepared.hidden_row {
                            EffectRowVariable::Rigid(id) => id,
                            _ => return Err(invalid_state()),
                        },
                        Kind::EffectRow,
                    ),
                ],
                clauses: clauses.into_boxed_slice(),
                direct_demands: prepared.direct_demands,
                pending_rows: lowered.pending_rows,
            },
            staged_externals: lowered.staged,
        })
    }

    #[cfg(test)]
    fn compile_provider_lifecycle(
        &mut self,
        definition: &ResolvedResourceDefinition,
        header: &ProviderHeader,
        phase: Phase,
    ) -> Result<LifecycleTemplateDraft, TypeError> {
        self.compile_provider_lifecycle_with_associations(definition, header, phase, Vec::new())
    }

    #[cfg(test)]
    fn compile_provider_lifecycle_with_externals(
        &mut self,
        definition: &ResolvedResourceDefinition,
        header: &ProviderHeader,
        phase: Phase,
        imported: &crate::resolved::ImportedFacts,
    ) -> Result<LifecycleTemplateDraft, TypeError> {
        self.compile_provider_lifecycle_with_externals_and_associations(
            definition,
            header,
            phase,
            imported,
            Vec::new(),
        )
    }

    fn compile_provider_lifecycle_with_externals_and_associations(
        &mut self,
        definition: &ResolvedResourceDefinition,
        header: &ProviderHeader,
        phase: Phase,
        imported: &crate::resolved::ImportedFacts,
        state_associations: Vec<HeaderStateAssociation>,
    ) -> Result<LifecycleTemplateDraft, TypeError> {
        self.compile_provider_lifecycle_context(
            definition,
            header,
            phase,
            state_associations,
            Some(imported),
        )
    }

    #[cfg(test)]
    fn compile_provider_lifecycle_with_associations(
        &mut self,
        definition: &ResolvedResourceDefinition,
        header: &ProviderHeader,
        phase: Phase,
        state_associations: Vec<HeaderStateAssociation>,
    ) -> Result<LifecycleTemplateDraft, TypeError> {
        self.compile_provider_lifecycle_context(definition, header, phase, state_associations, None)
    }

    fn compile_provider_lifecycle_context(
        &mut self,
        definition: &ResolvedResourceDefinition,
        header: &ProviderHeader,
        phase: Phase,
        state_associations: Vec<HeaderStateAssociation>,
        imported: Option<&crate::resolved::ImportedFacts>,
    ) -> Result<LifecycleTemplateDraft, TypeError> {
        if let Some(imported) = imported {
            self.install_provider_imports(imported)?;
        }
        self.type_work
            .charge(state_associations.len())
            .map_err(|()| type_resource())?;
        let mut families = std::collections::HashSet::new();
        families
            .try_reserve(state_associations.len())
            .map_err(|_| type_resource())?;
        for association in &state_associations {
            if association.definition.module() != definition.id.module()
                || association.family.module() != definition.id.module()
                || !families.insert(association.family)
            {
                return Err(invalid_state());
            }
        }
        let (ordinal, parameter, input, expression, error, authorized) = match phase {
            Phase::Acquire => (
                0,
                &definition.acquire_binder,
                &definition.input.ty,
                &definition.acquire,
                &header.input_error,
                &header.acquire,
            ),
            Phase::Finish => (
                1,
                &definition.finish_binder,
                &definition.state.ty,
                &definition.finish,
                &header.completion_error,
                &header.finish,
            ),
            _ => return Err(invalid_state()),
        };
        self.check_provider_lifecycle_profile(expression)?;
        let id = ProviderTemplateId::new(definition.id, ordinal);
        self.type_work
            .charge(authorized.len())
            .map_err(|()| type_resource())?;
        let mut operations = Vec::new();
        operations
            .try_reserve_exact(authorized.len())
            .map_err(|_| type_resource())?;
        operations.extend(authorized.iter().map(|(operation, _)| *operation));
        // Recording lives for this consumed template transaction. Callable
        // checking still clears native permission through FinishFunction.
        self.type_work.charge(1).map_err(|()| type_resource())?;
        self.provider_occurrence_template = Some(id);
        self.provider_context = Some(CheckingContext {
            native: clone_effect_instance_with_budget(
                &definition.interpreted.instance,
                &mut self.type_work,
            )
            .map_err(|error| TypeError::Internal(error.into()))?,
            phase,
            operations: operations.into_boxed_slice(),
            state_associations,
        });
        let evidence_marker = imported.map(|_| self.evidence_marker()).transpose()?;
        let mut context = self.base_context.clone();
        reserve_context_entry(&mut context, &mut self.type_work).map_err(|()| type_resource())?;
        let input_type = self.clone_type(input)?;
        let provenance = self.at_span_provenance(input, parameter.origin.primary_span())?;
        if context.insert_with_provenance(parameter.id, input_type, provenance)? {
            return Err(invalid_state());
        }
        let parameter_type = self.clone_type(input)?;
        let parameter_node =
            self.builder
                .resolved_binder(parameter.id, parameter_type, parameter.origin.clone())?;
        let original_rows = self.provider_original_row_contexts(definition)?;
        let row_depth = self.expected_scheme_rows.len();
        self.type_work
            .charge(original_rows.len())
            .map_err(|()| type_resource())?;
        self.expected_scheme_rows
            .try_reserve(original_rows.len())
            .map_err(|_| type_resource())?;
        self.expected_scheme_rows.extend(original_rows);
        let body = self.elaborate_expression_with_context(
            ElaborationTask::Synthesize {
                expression,
                cause: None,
            },
            &mut context,
        );
        self.expected_scheme_rows.truncate(row_depth);
        let body = TypedNodeOwner::new(body?);
        let report = body.ty.outer_nominal().ok_or_else(|| {
            contract_error(
                expression.span,
                "lifecycle result must have a determined authenticated report codec",
            )
        })?;
        self.type_work
            .charge(authorized.len())
            .map_err(|()| type_resource())?;
        if !authorized.iter().any(|(_, allowed)| *allowed == report) {
            return Err(contract_error(
                expression.span,
                "lifecycle result nominal is not a registered role/state codec",
            ));
        }
        let expected = IterativeTypeOwner::new(Type::apply_arguments(
            Type::Nominal(report),
            [
                self.clone_type(&definition.state.ty)?,
                self.clone_type(error)?,
            ],
        ));
        match self.unify(&body.ty, &expected) {
            Ok(()) => {}
            Err(UnificationFailure::Resource) => return Err(type_resource()),
            Err(UnificationFailure::Invariant) => return Err(invalid_state()),
            Err(UnificationFailure::Kind { context, span }) => {
                return Err(TypeError::Internal(ElaborationFailure::Kind {
                    context,
                    span,
                }));
            }
            Err(UnificationFailure::RowExclusion) => {
                return Err(row_exclusion_error(expression.span, None));
            }
            Err(UnificationFailure::Mismatch | UnificationFailure::Infinite) => {
                return Err(contract_error(
                    expression.span,
                    "lifecycle report state and independent error must match the declaration",
                ));
            }
        }
        if body.effects.tail().is_some() {
            return Err(contract_error(
                expression.span,
                "lifecycle template has an unresolved outward effect row",
            ));
        }
        for effect in body.effects.known() {
            if compare_effect_instances_with_budget(
                effect,
                &definition.interpreted.instance,
                &mut self.type_work,
            )
            .map_err(|()| type_resource())?
                != std::cmp::Ordering::Equal
            {
                return Err(contract_error(
                    expression.span,
                    "lifecycle template must be synchronous after its explicit native interpretation",
                ));
            }
        }
        let body_node = body.node;
        let function_type =
            lifecycle_function_type(input, &body.ty, &body.effects, &mut self.type_work)?;
        let function_type_for_node = self.clone_type(&function_type)?;
        let function = self.builder.function(
            parameter_node,
            body_node,
            function_type_for_node,
            definition.origin.clone(),
        )?;
        self.type_work
            .charge(
                definition
                    .parameters
                    .len()
                    .saturating_mul(3)
                    .saturating_add(4),
            )
            .map_err(|()| type_resource())?;
        let mut substitutions = OwnerReplacementBuffer::new();
        let mut formal_parameters = Vec::new();
        formal_parameters
            .try_reserve_exact(definition.parameters.len())
            .map_err(|_| type_resource())?;
        let mut parameters = Vec::new();
        parameters
            .try_reserve_exact(definition.parameters.len().saturating_add(2))
            .map_err(|_| type_resource())?;
        for parameter in &definition.parameters {
            let generated = self.fresh_type_variable(&parameter.kind, definition.span)?;
            substitutions.insert_fresh(
                parameter.id,
                generated,
                &parameter.kind,
                &mut self.type_work,
            )?;
            formal_parameters.push((
                parameter.id,
                generated,
                clone_kind_with_budget(&parameter.kind, &mut self.type_work)
                    .map_err(|()| type_resource())?,
            ));
            parameters.push((
                generated,
                clone_kind_with_budget(&parameter.kind, &mut self.type_work)
                    .map_err(|()| type_resource())?,
            ));
        }
        let hidden_answer = self.fresh_type_variable(&Kind::Type, definition.span)?;
        let hidden_row_parameter = self.fresh_type_variable(&Kind::EffectRow, definition.span)?;
        parameters.extend([
            (hidden_answer, Kind::Type),
            (hidden_row_parameter, Kind::EffectRow),
        ]);
        if let Some(marker) = evidence_marker {
            self.close_evidence_obligations(marker)?;
        }
        let publication = imported
            .map(|_| self.prepare_evidence_publication())
            .transpose()?;
        self.zonk_builder_types().map_err(TypeError::Internal)?;
        {
            let work = RefCell::new(&mut self.type_work);
            self.builder.rewrite_types_and_rows(
                None,
                |ty| {
                    substitutions
                        .substitute(ty, &mut work.borrow_mut())
                        .map_err(|_| BuildError::TypeWorkExceeded)
                },
                |row| {
                    substitutions
                        .substitute_row(row, &mut work.borrow_mut())
                        .map_err(|_| BuildError::TypeWorkExceeded)
                },
            )?;
        }
        let function_type = IterativeTypeOwner::new(self.zonk(&function_type)?);
        let scheme = lifecycle_template_scheme(
            &function_type,
            &substitutions,
            &parameters,
            &mut self.type_work,
        )?;
        let root = self.builder.type_abstraction(
            parameters,
            function,
            scheme,
            definition.origin.clone(),
        )?;
        let mut body_node = body_node;
        let (core, staged_externals) = if let Some(imported) = imported {
            self.lower_provider_source_draft(
                root,
                &mut body_node,
                imported,
                publication.ok_or_else(invalid_state)?,
                &substitutions,
            )?
        } else {
            let placeholder = CoreBuilder::<EffectOperationFamily>::with_registry_for_family(
                Arc::clone(&self.registry),
            );
            (
                std::mem::replace(&mut self.builder, placeholder).finish(root)?,
                None,
            )
        };
        Ok(LifecycleTemplateDraft {
            id,
            phase,
            parameter: parameter.id,
            body: body_node,
            hidden_answer,
            hidden_row: EffectRowVariable::rigid(hidden_row_parameter),
            formal_parameters: formal_parameters.into_boxed_slice(),
            core,
            staged_externals,
            defining_facts: self.provider_defining_facts.as_ref().map(Arc::clone),
            #[cfg(test)]
            compile_work: self.type_work.used(),
        })
    }
}

fn lifecycle_function_type(
    input: &Type,
    result: &Type,
    row: &EffectRow,
    work: &mut TypeWorkBudget,
) -> Result<IterativeTypeOwner, TypeError> {
    let input =
        IterativeTypeOwner::new(clone_type_with_budget(input, work).map_err(|()| type_resource())?);
    let result = IterativeTypeOwner::new(
        clone_type_with_budget(result, work).map_err(|()| type_resource())?,
    );
    let row = clone_effect_row_with_budget(row, work).map_err(|()| type_resource())?;
    Ok(IterativeTypeOwner::new(Type::function_computation(
        input.into_inner(),
        ComputationType::new(result.into_inner(), row),
    )))
}

fn lifecycle_template_scheme(
    function: &Type,
    substitutions: &OwnerReplacementBuffer,
    parameters: &[(TypeVariableId, Kind)],
    work: &mut TypeWorkBudget,
) -> Result<Type, TypeError> {
    let function = IterativeTypeOwner::new(substitutions.substitute(function, work)?);
    let parameters = clone_kinded_type_parameters_with_budget(parameters, work)
        .map_err(|()| type_resource())?
        .into_boxed_slice();
    Ok(Type::Forall(parameters, Box::new(function.into_inner())))
}

impl Drop for ProviderHeader {
    fn drop(&mut self) {
        discard_type_iteratively(std::mem::replace(&mut self.input_error, Type::Unit));
        discard_type_iteratively(std::mem::replace(&mut self.completion_error, Type::Unit));
    }
}

#[cfg(test)]
#[derive(Default)]
struct ProviderSubstitutions(HashMap<TypeVariableId, Type>);
#[cfg(test)]
impl ProviderSubstitutions {
    fn insert_discarding_replaced(&mut self, parameter: TypeVariableId, ty: Type) {
        if let Some(displaced) = self.0.insert(parameter, ty) {
            discard_type_iteratively(displaced);
        }
    }
}

#[cfg(test)]
impl std::ops::Deref for ProviderSubstitutions {
    type Target = HashMap<TypeVariableId, Type>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
#[cfg(test)]
impl Drop for ProviderSubstitutions {
    fn drop(&mut self) {
        for (_, ty) in self.0.drain() {
            discard_type_iteratively(ty);
        }
    }
}

#[cfg(test)]
fn retain_state_access_arguments(
    parameters: &[TypeVariableId],
    arguments: &[&Type],
    work: &mut TypeWorkBudget,
) -> Result<(ProviderSubstitutions, OwnedTypeBuffer), TypeError> {
    if parameters.len() != arguments.len() {
        return Err(invalid_state());
    }
    let mut substitutions = ProviderSubstitutions::default();
    work.charge(arguments.len().checked_mul(2).ok_or_else(type_resource)?)
        .map_err(|()| type_resource())?;
    substitutions
        .0
        .try_reserve(arguments.len())
        .map_err(|_| type_resource())?;
    let mut retained_arguments = OwnedTypeBuffer(Vec::new());
    retained_arguments
        .try_reserve(arguments.len())
        .map_err(|_| type_resource())?;
    for (parameter, argument) in parameters.iter().zip(arguments.iter().copied()) {
        let replacement = IterativeTypeOwner::new(
            clone_type_with_budget(argument, work).map_err(|()| type_resource())?,
        );
        retained_arguments
            .push(clone_type_with_budget(argument, work).map_err(|()| type_resource())?);
        match substitutions.0.entry(*parameter) {
            std::collections::hash_map::Entry::Vacant(entry) => {
                entry.insert(replacement.into_inner());
            }
            std::collections::hash_map::Entry::Occupied(_) => return Err(invalid_state()),
        }
    }
    Ok((substitutions, retained_arguments))
}

pub(super) fn ordinary_state_unavailable(span: Span) -> TypeError {
    contract_error(
        span,
        "controlled native state is unavailable in ordinary callable types or captures",
    )
}

fn contract_error(span: Span, message: &'static str) -> TypeError {
    inference_failure(TypeReason::Argument, span, message)
}

pub(super) fn nominal_arguments<'a>(
    ty: &'a Type,
    budget: &mut TypeWorkBudget,
) -> Result<(NominalTypeId, Vec<&'a Type>), TypeError> {
    let mut head = ty;
    let mut arguments = Vec::new();
    while let Type::Application(function, argument) = head {
        budget.charge(1).map_err(|()| type_resource())?;
        arguments.try_reserve(1).map_err(|_| type_resource())?;
        arguments.push(argument.as_ref());
        head = function;
    }
    arguments.reverse();
    match head {
        Type::Nominal(id) => Ok((*id, arguments)),
        _ => Err(invalid_state()),
    }
}

impl<F: CoreLoweringFamily> CoreElaborator<F> {
    fn check_provider_lifecycle_profile(&mut self, root: &ResolvedExpr) -> Result<(), TypeError> {
        enum Item<'a> {
            Expression(&'a ResolvedExpr),
            Block(&'a crate::resolved::ResolvedBlock),
            Declaration(&'a crate::resolved::ResolvedLocalDeclaration),
        }
        let mut pending = Vec::new();
        pending.try_reserve(1).map_err(|_| type_resource())?;
        pending.push(Item::Expression(root));
        while let Some(item) = pending.pop() {
            self.type_work.charge(1).map_err(|()| type_resource())?;
            pending.try_reserve(3).map_err(|_| type_resource())?;
            match item {
                Item::Block(block) => {
                    self.type_work
                        .charge(block.declarations.len())
                        .map_err(|()| type_resource())?;
                    pending
                        .try_reserve(block.declarations.len().saturating_add(1))
                        .map_err(|_| type_resource())?;
                    pending.push(Item::Expression(&block.result));
                    pending.extend(block.declarations.iter().map(Item::Declaration));
                }
                Item::Declaration(crate::resolved::ResolvedLocalDeclaration::Binding(binding)) => {
                    pending.push(Item::Expression(&binding.initializer))
                }
                Item::Declaration(crate::resolved::ResolvedLocalDeclaration::Recursive(group)) => {
                    self.type_work
                        .charge(group.members.len())
                        .map_err(|()| type_resource())?;
                    pending
                        .try_reserve(group.members.len())
                        .map_err(|_| type_resource())?;
                    pending.extend(
                        group
                            .members
                            .iter()
                            .map(|member| Item::Expression(&member.initializer)),
                    );
                }
                Item::Declaration(crate::resolved::ResolvedLocalDeclaration::Evidence(source)) => {
                    self.type_work
                        .charge(source.method_groups.len())
                        .map_err(|()| type_resource())?;
                    for group in &source.method_groups {
                        self.type_work
                            .charge(group.equations.len())
                            .map_err(|()| type_resource())?;
                        pending
                            .try_reserve(group.equations.len())
                            .map_err(|_| type_resource())?;
                        pending.extend(
                            group
                                .equations
                                .iter()
                                .map(|equation| Item::Expression(&equation.body)),
                        );
                    }
                }
                Item::Declaration(crate::resolved::ResolvedLocalDeclaration::Newtype(_)) => {}
                Item::Expression(expression) => match &expression.kind {
                    ResolvedExprKind::Handle(_)
                    | ResolvedExprKind::Resume(_)
                    | ResolvedExprKind::Discard(_)
                    | ResolvedExprKind::Cleanup(_)
                    | ResolvedExprKind::Resource(_)
                    | ResolvedExprKind::ProviderResource(_) => {
                        return Err(contract_error(
                            expression.span,
                            "lifecycle templates cannot contain source handlers, continuations, cleanup or nested resources",
                        ));
                    }
                    ResolvedExprKind::Block(block) => pending.push(Item::Block(block)),
                    ResolvedExprKind::Function(function) => {
                        pending.push(Item::Block(&function.body))
                    }
                    ResolvedExprKind::Apply(application) => {
                        pending.push(Item::Expression(&application.argument));
                        pending.push(Item::Expression(&application.function));
                    }
                    ResolvedExprKind::Add(binary)
                    | ResolvedExprKind::Multiply(binary)
                    | ResolvedExprKind::Equal(binary) => {
                        pending.push(Item::Expression(&binary.left));
                        pending.push(Item::Expression(&binary.right));
                    }
                    ResolvedExprKind::Tuple(elements) => {
                        self.type_work
                            .charge(elements.len())
                            .map_err(|()| type_resource())?;
                        pending
                            .try_reserve(elements.len())
                            .map_err(|_| type_resource())?;
                        pending.extend(elements.iter().map(Item::Expression));
                    }
                    ResolvedExprKind::Match(matched) => {
                        self.type_work
                            .charge(matched.arms.len())
                            .map_err(|()| type_resource())?;
                        pending
                            .try_reserve(matched.arms.len().saturating_add(1))
                            .map_err(|_| type_resource())?;
                        pending.push(Item::Expression(&matched.scrutinee));
                        pending.extend(matched.arms.iter().map(|arm| Item::Expression(&arm.body)));
                    }
                    ResolvedExprKind::Perform(request) => {
                        pending.push(Item::Expression(&request.operand))
                    }
                    ResolvedExprKind::String(_)
                    | ResolvedExprKind::Integer(_)
                    | ResolvedExprKind::Boolean(_)
                    | ResolvedExprKind::Unit
                    | ResolvedExprKind::Occurrence(_)
                    | ResolvedExprKind::Constructor(_) => {}
                },
            }
        }
        Ok(())
    }

    fn check_provider_header(
        &mut self,
        module: &ResolvedModule,
        definition: &ResolvedResourceDefinition,
    ) -> Result<ProviderHeader, TypeError> {
        let registry = Arc::clone(&self.registry);
        let owner = definition.parameters.first().ok_or_else(invalid_state)?;
        if owner.kind != Kind::Type || definition.answer.kind != Kind::Type {
            return Err(contract_error(
                definition.span,
                "resource identity and answer parameters must have kind Type",
            ));
        }
        let (state_id, state_arguments) =
            nominal_arguments(&definition.state.ty, &mut self.type_work)?;
        let state = registry.foreign_state(state_id).ok_or_else(|| {
            contract_error(
                definition.state.span,
                "resource state must be an authenticated opaque native state",
            )
        })?;
        if state_arguments.len() != state.parameter_count
            || state_arguments.get(state.owned_identity_position).copied()
                != Some(&Type::Variable(owner.id))
        {
            return Err(contract_error(
                definition.state.span,
                "native state must own the first resource identity parameter",
            ));
        }
        let interpreted = registry
            .effect(definition.interpreted.instance.effect())
            .ok_or_else(invalid_state)?;
        if !registry.foreign_effect(interpreted.id) {
            return Err(contract_error(
                definition.interpreted.span,
                "resource interpretation requires an authenticated native effect",
            ));
        }
        let mut acquire = Vec::new();
        let mut finish = Vec::new();
        acquire
            .try_reserve_exact(interpreted.operations.len())
            .map_err(|_| type_resource())?;
        finish
            .try_reserve_exact(interpreted.operations.len())
            .map_err(|_| type_resource())?;
        for operation in &interpreted.operations {
            self.type_work.charge(1).map_err(|()| type_resource())?;
            let fact = registry
                .foreign_operation(operation.id)
                .ok_or_else(invalid_state)?;
            if definition
                .interpreted
                .instance
                .arguments()
                .get(fact.owned_identity_position)
                != Some(&crate::types::KindedArgument::TypeArg(Type::Variable(
                    owner.id,
                )))
            {
                return Err(contract_error(
                    definition.interpreted.span,
                    "interpreted native effect must own the resource identity",
                ));
            }
            let codec = match (&fact.role, &fact.result) {
                (
                    ForeignOperationRole::Acquire,
                    ForeignResultFact::Acquire { state, report, .. },
                ) if *state == state_id => Some((true, *report)),
                (ForeignOperationRole::Finish, ForeignResultFact::Finish { state, report, .. })
                    if *state == state_id =>
                {
                    Some((false, *report))
                }
                _ => None,
            };
            if let Some((acquiring, codec)) = codec {
                let (domain, result) = self.operation_signature(
                    &definition.interpreted.instance,
                    operation.id,
                    definition.span,
                )?;
                discard_type_iteratively(domain);
                let result = IterativeTypeOwner::new(result);
                let (report, arguments) = nominal_arguments(&result, &mut self.type_work)?;
                if report != codec
                    || arguments.len() != 2
                    || !same_type_with_budget(
                        arguments[0],
                        &definition.state.ty,
                        &mut self.type_work,
                    )
                    .map_err(|()| type_resource())?
                {
                    return Err(contract_error(
                        definition.state.span,
                        "native lifecycle state lineage must match the declared state exactly",
                    ));
                }
                if acquiring {
                    acquire.push((operation.id, codec));
                } else {
                    finish.push((operation.id, codec));
                }
            }
        }
        if acquire.is_empty() || finish.is_empty() {
            return Err(contract_error(
                definition.span,
                "resource state requires registered acquiring and finishing operations",
            ));
        }
        let (scope, result_arguments) =
            nominal_arguments(&definition.result.ty, &mut self.type_work)?;
        if result_arguments.len() != 3
            || result_arguments[2] != &Type::Variable(definition.answer.id)
        {
            return Err(contract_error(
                definition.result.span,
                "resource result requires acquisition error, completion error and independent answer parameters",
            ));
        }
        let input_error = self.clone_type(result_arguments[0])?;
        let completion_error = self.clone_type(result_arguments[1])?;
        let (_scope_constructors, _completion_constructors) =
            self.check_provider_report(scope, definition.result.span)?;
        let provided = registry
            .effect(definition.provided.instance.effect())
            .ok_or_else(invalid_state)?;
        if registry.foreign_effect(provided.id)
            || definition.handlers.len() != provided.operations.len()
        {
            return Err(contract_error(
                definition.provided.span,
                "resource provides a complete ordinary source effect",
            ));
        }
        first_invalid_handler_operation_with_budget(
            provided.id,
            provided.operations.len(),
            definition.handlers.iter().map(|clause| clause.operation),
            &mut self.type_work,
        )
        .map_err(|()| type_resource())?
        .map_or(Ok(()), |_| {
            Err(contract_error(
                definition.span,
                "resource handler clauses must cover each associated operation exactly once",
            ))
        })?;
        let interface_id = definition.provider.interface.id;
        let local = module
            .interfaces()
            .iter()
            .find(|interface| interface.id == interface_id);
        let imported = module.imported_facts().interface(interface_id);
        self.type_work
            .charge(local.map_or_else(
                || imported.map_or(0, |interface| interface.methods.len()),
                |interface| interface.methods.len(),
            ))
            .map_err(|()| type_resource())?;
        let (parameters, methods): (&[_], Vec<_>) = if let Some(interface) = local {
            (
                interface.parameters.as_ref(),
                interface
                    .methods
                    .iter()
                    .map(|method| (method.id, method.spelling.as_str(), &method.annotation.ty))
                    .collect(),
            )
        } else if let Some(interface) = imported {
            (
                interface.parameters.as_ref(),
                interface
                    .methods
                    .iter()
                    .map(|method| (method.id, method.spelling.as_str(), &method.value_type))
                    .collect(),
            )
        } else {
            return Err(invalid_state());
        };
        if methods.len() != provided.operations.len()
            || parameters.len() != definition.provider.arguments.len()
        {
            return Err(contract_error(
                definition.provider.span,
                "provider methods must match the complete associated effect",
            ));
        }
        self.type_work
            .charge(parameters.len().saturating_add(methods.len()))
            .map_err(|()| type_resource())?;
        let mut substitutions = OwnerReplacementBuffer::new();
        for (parameter, argument) in parameters.iter().zip(&definition.provider.arguments) {
            substitutions.insert_cloned(parameter.id, &argument.ty, &mut self.type_work)?;
        }
        let mut associations = Vec::new();
        associations
            .try_reserve_exact(methods.len())
            .map_err(|_| type_resource())?;
        for (method, spelling, signature) in methods {
            let operation = provided
                .operations
                .iter()
                .find(|operation| operation.spelling == spelling)
                .ok_or_else(|| {
                    contract_error(
                        definition.provider.span,
                        "provider method has no matching associated operation",
                    )
                })?;
            let (domain, result) = self.operation_signature(
                &definition.provided.instance,
                operation.id,
                definition.span,
            )?;
            let expected = IterativeTypeOwner::new(Type::function_computation(
                domain,
                ComputationType::new(
                    result,
                    EffectRow::singleton(
                        clone_effect_instance_with_budget(
                            &definition.provided.instance,
                            &mut self.type_work,
                        )
                        .map_err(|error| TypeError::Internal(error.into()))?,
                    ),
                ),
            ));
            let actual =
                IterativeTypeOwner::new(substitutions.substitute(signature, &mut self.type_work)?);
            if !same_type_with_budget(&actual, &expected, &mut self.type_work)
                .map_err(|()| type_resource())?
            {
                return Err(contract_error(
                    definition.provider.span,
                    "provider method type and row must equal its associated operation and exact effect instance",
                ));
            }
            associations.push((method, operation.id));
        }
        self.type_work
            .charge(definition.parameters.len())
            .map_err(|()| type_resource())?;
        let mut parameters = Vec::new();
        parameters
            .try_reserve_exact(definition.parameters.len())
            .map_err(|_| type_resource())?;
        parameters.extend(definition.parameters.iter().map(|parameter| parameter.id));
        let state_association = HeaderStateAssociation {
            definition: definition.id,
            family: definition.family,
            parameters: parameters.into_boxed_slice(),
            state: IterativeTypeOwner::new(self.clone_type(&definition.state.ty)?),
        };
        Ok(ProviderHeader {
            provider_application: crate::interface::InterfaceApplication::new_kinded(
                definition.provider.interface.id,
                crate::types::clone_kinded_arguments_with_budget(
                    definition
                        .provider
                        .arguments
                        .iter()
                        .map(|argument| &argument.ty),
                    &mut self.type_work,
                )
                .map_err(|()| type_resource())?,
            ),
            state_association,
            acquire,
            finish,
            input_error,
            completion_error,
            methods: associations,
            #[cfg(test)]
            scope_constructors: _scope_constructors,
            #[cfg(test)]
            completion_constructors: _completion_constructors,
        })
    }

    fn check_provider_report(
        &mut self,
        scope: NominalTypeId,
        span: Span,
    ) -> Result<([ConstructorId; 2], [ConstructorId; 3]), TypeError> {
        let registry = Arc::clone(&self.registry);
        let nominal = registry
            .nominals()
            .iter()
            .find(|nominal| nominal.id == scope)
            .ok_or_else(invalid_state)?;
        let parameters = registry
            .nominal_parameters(scope)
            .ok_or_else(invalid_state)?;
        if parameters.len() != 3
            || nominal.constructors.len() != 2
            || parameters
                .iter()
                .any(|parameter| parameter.kind != Kind::Type)
        {
            return Err(contract_error(
                span,
                "resource scope report requires failure and completed alternatives",
            ));
        }
        let scope_constructors = [nominal.constructors[0], nominal.constructors[1]];
        self.type_work.charge(4).map_err(|()| type_resource())?;
        if registry
            .constructor(scope_constructors[0])
            .and_then(|constructor| constructor.payload.as_ref())
            != Some(&Type::Variable(parameters[0].id))
        {
            return Err(contract_error(
                span,
                "scope report ordinal zero must contain its formal acquisition error",
            ));
        }
        let Some(Type::Tuple(elements)) = registry
            .constructor(scope_constructors[1])
            .and_then(|constructor| constructor.payload.as_ref())
        else {
            return Err(contract_error(
                span,
                "scope report ordinal one must contain answer and completion",
            ));
        };
        if elements.len() != 2 || elements[0] != Type::Variable(parameters[2].id) {
            return Err(contract_error(
                span,
                "scope completed payload must retain the formal answer",
            ));
        }
        let (completion, arguments) = nominal_arguments(&elements[1], &mut self.type_work)?;
        if arguments.as_slice() != [&Type::Variable(parameters[1].id)] {
            return Err(contract_error(
                span,
                "completion report must retain the formal completion error",
            ));
        }
        let nominal = registry
            .nominals()
            .iter()
            .find(|nominal| nominal.id == completion)
            .ok_or_else(invalid_state)?;
        let parameters = registry
            .nominal_parameters(completion)
            .ok_or_else(invalid_state)?;
        if parameters.len() != 1
            || parameters[0].kind != Kind::Type
            || nominal.constructors.len() != 3
        {
            return Err(contract_error(
                span,
                "completion report requires closed, consumed-error and retained-error alternatives",
            ));
        }
        for (ordinal, id) in nominal.constructors.iter().enumerate() {
            self.type_work.charge(1).map_err(|()| type_resource())?;
            match registry
                .constructor(*id)
                .ok_or_else(invalid_state)?
                .payload
                .as_ref()
            {
                None if ordinal == 0 => {}
                Some(Type::Variable(parameter))
                    if ordinal != 0 && *parameter == parameters[0].id => {}
                _ => {
                    return Err(contract_error(
                        span,
                        "completion report errors must be independent values",
                    ));
                }
            }
        }
        Ok((
            scope_constructors,
            [
                nominal.constructors[0],
                nominal.constructors[1],
                nominal.constructors[2],
            ],
        ))
    }
}

#[cfg(test)]
mod tests {
    mod access;
    mod external;
    mod handler;
    use super::*;
    use crate::{
        foreign::{ForeignRegistrations, sqlite_manifest},
        module::{ForeignRegistrationId, ModuleGraph, ModuleRoots, load_module_graph},
        resolve::{DependencyExports, resolve_module},
    };
    use std::{
        fs,
        sync::atomic::{AtomicU64, Ordering},
    };

    const SOURCE: &str = "import @foreign.sqlite as Native\npub type Completion<E> = Closed\n| ConsumedError(E)\n| RetainedError(E)\npub type Scope<I, E, T> = NotAcquired(I)\n| Completed(T, Completion<E>)\npub interface Reader<R> {\nread : Connection<R> -> Native.Error ! {Ops<R>}\n}\npub effect Ops<R> {\nread : Connection<R> -> Native.Error\n}\npub resource Connection<R> {\ninput Native.OpenConfig\nstate Native.ConnectionState<R>\nresult Scope<Native.OpenError, Native.CloseError, T> for <T>\nprovider Reader<R>\neffect Ops<R>\ninterpret Native.Connection<R>\nacquire config => perform Native.Connection<R>.open config\nfinish state => perform Native.Connection<R>.close state\nhandlers state {\nread db => resume (perform Native.Connection<R>.diagnostic state)\n}\n}\n";
    static IDS: AtomicU64 = AtomicU64::new(0);

    fn deep_assembly_type() -> IterativeTypeOwner {
        let mut ty = IterativeTypeOwner::new(Type::Unit);
        for _ in 0..32_000 {
            ty = IterativeTypeOwner::new(Type::Function(
                Box::new(Type::Unit),
                Box::new(ty.into_inner()),
            ));
        }
        ty
    }

    #[test]
    fn resource_fact_partial_assembly_drains_deep_metadata_on_late_refusal() {
        let fixture = Fixture::new(SOURCE);
        let mut definition = fixture.resolved.resources()[0].clone();
        discard_type_iteratively(std::mem::replace(
            &mut definition.input.ty,
            deep_assembly_type().into_inner(),
        ));
        discard_type_iteratively(std::mem::replace(
            &mut definition.state.ty,
            deep_assembly_type().into_inner(),
        ));
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(move || {
                let mut measured = TypeWorkBudget::unbounded();
                drop(
                    crate::resolved::ResourceTypeFact::from_definition_with_budget(
                        &definition,
                        &mut measured,
                    )
                    .unwrap(),
                );
                let cost = measured.used();
                assert!(cost > 128_000);
                for prefix in [0, 13] {
                    let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
                    short.charge(prefix).unwrap();
                    assert!(
                        crate::resolved::ResourceTypeFact::from_definition_with_budget(
                            &definition,
                            &mut short
                        )
                        .is_err()
                    );
                    for _ in 0..2 {
                        let mut exact = TypeWorkBudget::with_limit(prefix + cost);
                        exact.charge(prefix).unwrap();
                        drop(
                            crate::resolved::ResourceTypeFact::from_definition_with_budget(
                                &definition,
                                &mut exact,
                            )
                            .unwrap(),
                        );
                        assert_eq!(exact.used(), prefix + cost);
                    }
                }
                crate::resolved::discard_resolved_resource_definition(definition);
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn lifecycle_function_assembly_late_failure_drains_deep_sibling_types() {
        const CHILD: &str = "ASH_LIFECYCLE_FUNCTION_ASSEMBLY_CHILD";
        if std::env::var_os(CHILD).is_none() {
            for window in ["result", "row"] {
                let output = std::process::Command::new(std::env::current_exe().unwrap()).args(["--exact", "elaborate::provider::tests::lifecycle_function_assembly_late_failure_drains_deep_sibling_types", "--nocapture"]).env(CHILD, window).output().unwrap();
                eprintln!("{}", String::from_utf8_lossy(&output.stderr));
                assert!(
                    output.status.success(),
                    "{window} sibling window failed: {}",
                    String::from_utf8_lossy(&output.stderr)
                );
            }
            return;
        }
        let window = std::env::var(CHILD).unwrap();
        std::thread::Builder::new().stack_size(256 * 1024).spawn(move || {
            // Untrusted metadata isolates the actual production assembly
            // helper. This exceeds Core admission depth and is not a program.
            let input = deep_assembly_type();
            let result = deep_assembly_type();
            let row = EffectRow::empty();
            let mut input_work = TypeWorkBudget::unbounded();
            drop(IterativeTypeOwner::new(clone_type_with_budget(&input, &mut input_work).unwrap()));
            let mut result_work = TypeWorkBudget::unbounded();
            drop(IterativeTypeOwner::new(clone_type_with_budget(&result, &mut result_work).unwrap()));
            let before_failure = input_work.used() + if window == "row" { result_work.used() } else { 0 };
            let mut measured = TypeWorkBudget::unbounded();
            drop(lifecycle_function_type(&input, &result, &row, &mut measured).unwrap());
            let cost = measured.used();
            assert!(before_failure > 32_000 && cost > before_failure);
            for prefix in [0, 13] {
                eprintln!("function assembly {window}: prefix={prefix}, late boundary={before_failure}, total={cost}");
                let mut late = TypeWorkBudget::with_limit(prefix + before_failure);
                late.charge(prefix).unwrap();
                assert!(matches!(lifecycle_function_type(&input, &result, &row, &mut late), Err(TypeError::Internal(ElaborationFailure::TypeResourceExhausted))));
                assert_eq!(late.used(), prefix + before_failure);
                let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
                short.charge(prefix).unwrap();
                assert!(lifecycle_function_type(&input, &result, &row, &mut short).is_err());
                for _ in 0..2 {
                    let mut exact = TypeWorkBudget::with_limit(prefix + cost);
                    exact.charge(prefix).unwrap();
                    drop(lifecycle_function_type(&input, &result, &row, &mut exact).unwrap());
                    assert_eq!(exact.used(), prefix + cost);
                }
            }
        }).unwrap().join().unwrap();
    }

    #[test]
    fn lifecycle_scheme_assembly_late_failure_drains_substituted_function_type() {
        const CHILD: &str = "ASH_LIFECYCLE_SCHEME_ASSEMBLY_CHILD";
        if std::env::var_os(CHILD).is_none() {
            let output = std::process::Command::new(std::env::current_exe().unwrap()).args(["--exact", "elaborate::provider::tests::lifecycle_scheme_assembly_late_failure_drains_substituted_function_type", "--nocapture"]).env(CHILD, "1").output().unwrap();
            eprintln!("{}", String::from_utf8_lossy(&output.stderr));
            assert!(
                output.status.success(),
                "scheme assembly window failed: {}",
                String::from_utf8_lossy(&output.stderr)
            );
            return;
        }
        std::thread::Builder::new().stack_size(256 * 1024).spawn(|| {
            // Private deep metadata tests ownership at the actual template
            // assembly boundary; it carries no source or Core admission.
            let function = deep_assembly_type();
            let substitutions = OwnerReplacementBuffer::new();
            let parameters = [(TypeVariableId::generated(991), Kind::Type)];
            let mut substitution_work = TypeWorkBudget::unbounded();
            drop(IterativeTypeOwner::new(substitutions.substitute(&function, &mut substitution_work).unwrap()));
            let mut measured = TypeWorkBudget::unbounded();
            drop(IterativeTypeOwner::new(lifecycle_template_scheme(&function, &substitutions, &parameters, &mut measured).unwrap()));
            let cost = measured.used();
            assert!(substitution_work.used() > 32_000 && cost > substitution_work.used());
            for prefix in [0, 13] {
                for allowance in [substitution_work.used(), cost - 1] {
                    eprintln!("scheme assembly: prefix={prefix}, substitution boundary={}, allowance={allowance}, total={cost}", substitution_work.used());
                    let mut late = TypeWorkBudget::with_limit(prefix + allowance);
                    late.charge(prefix).unwrap();
                    assert!(matches!(lifecycle_template_scheme(&function, &substitutions, &parameters, &mut late), Err(TypeError::Internal(ElaborationFailure::TypeResourceExhausted))));
                    assert_eq!(late.used(), prefix + allowance);
                }
                for _ in 0..2 {
                    let mut exact = TypeWorkBudget::with_limit(prefix + cost);
                    exact.charge(prefix).unwrap();
                    drop(IterativeTypeOwner::new(lifecycle_template_scheme(&function, &substitutions, &parameters, &mut exact).unwrap()));
                    assert_eq!(exact.used(), prefix + cost);
                }
            }
        }).unwrap().join().unwrap();
    }

    #[test]
    fn lifecycle_entry_rejects_answer_binder_aliased_to_resource_formal() {
        let fixture = Fixture::new(SOURCE);
        let definition = &fixture.resolved.resources()[0];
        let header = fixture
            .elaborator()
            .check_provider_header(&fixture.resolved, definition)
            .unwrap();
        for phase in [Phase::Acquire, Phase::Finish] {
            let draft = fixture
                .elaborator()
                .compile_provider_lifecycle(definition, &header, phase)
                .unwrap();
            let mut changed = definition.clone();
            changed.answer.id = changed.parameters[0].id;
            let Type::Application(_, answer) = &mut changed.result.ty else {
                unreachable!()
            };
            **answer = Type::Variable(changed.answer.id);
            assert!(
                draft
                    .check_flow(&changed, &mut TypeWorkBudget::unbounded())
                    .is_err(),
                "accepted {phase:?} answer/resource alias"
            );
        }
    }

    #[test]
    fn lifecycle_entry_rejects_core_envelopes_source_codec_and_exact_error_mutations() {
        use crate::core::provider::{EntryMutation, mutate_entry_for_test};
        let fixture = Fixture::new(SOURCE);
        let definition = &fixture.resolved.resources()[0];
        let header = fixture
            .elaborator()
            .check_provider_header(&fixture.resolved, definition)
            .unwrap();
        let mut admitted = Vec::new();
        for mutation in 0..10 {
            let mut canonical = definition.clone();
            let mut draft = fixture
                .elaborator()
                .compile_provider_lifecycle(definition, &header, Phase::Finish)
                .unwrap();
            match mutation {
                0 => mutate_entry_for_test(&mut draft.core, EntryMutation::RootType),
                1 => mutate_entry_for_test(&mut draft.core, EntryMutation::FunctionType),
                2 => mutate_entry_for_test(&mut draft.core, EntryMutation::RootRow),
                3 => mutate_entry_for_test(&mut draft.core, EntryMutation::FunctionRow),
                4 => {
                    let Type::Application(scope, _) = &mut canonical.result.ty else {
                        unreachable!()
                    };
                    let Type::Application(scope, _) = scope.as_mut() else {
                        unreachable!()
                    };
                    let Type::Application(head, _) = scope.as_mut() else {
                        unreachable!()
                    };
                    **head = Type::Nominal(definition.family);
                }
                5 => {
                    let Type::Application(_, answer) = &mut canonical.result.ty else {
                        unreachable!()
                    };
                    **answer = Type::Int;
                }
                6 => {
                    let Type::Application(scope, _) = &mut canonical.result.ty else {
                        unreachable!()
                    };
                    let Type::Application(_, error) = scope.as_mut() else {
                        unreachable!()
                    };
                    **error = Type::Application(Box::new((**error).clone()), Box::new(Type::Int));
                    mutate_entry_for_test(&mut draft.core, EntryMutation::ErrorApplication);
                }
                7 => {
                    canonical.interpreted.instance = crate::types::EffectInstance::new(
                        definition.interpreted.instance.effect(),
                        Box::new([Type::Int]),
                    )
                }
                8 => canonical.origin = Origin::Source(definition.state.span),
                9 => canonical.finish_binder.origin = Origin::Source(definition.state.span),
                _ => unreachable!(),
            }
            if draft
                .check_flow(&canonical, &mut TypeWorkBudget::unbounded())
                .is_ok()
            {
                admitted.push(mutation);
            }
        }
        assert!(
            admitted.is_empty(),
            "admitted incoherent declaration entries: {admitted:?}"
        );
    }

    #[test]
    fn lifecycle_entry_rejects_coherent_resolved_parameter_classes_for_both_phases() {
        for phase in [Phase::Acquire, Phase::Finish] {
            let fixture = Fixture::new(SOURCE);
            let definition = &fixture.resolved.resources()[0];
            let header = fixture
                .elaborator()
                .check_provider_header(&fixture.resolved, definition)
                .unwrap();
            for position in 0..3 {
                let mut draft = fixture
                    .elaborator()
                    .compile_provider_lifecycle(definition, &header, phase)
                    .unwrap();
                let original = match position {
                    0 => draft.formal_parameters[0].1,
                    1 => draft.hidden_answer,
                    _ => {
                        let EffectRowVariable::Rigid(id) = draft.hidden_row else {
                            unreachable!()
                        };
                        id
                    }
                };
                let actual = TypeVariableId::resolved(definition.id.module(), 999);
                crate::core::provider::mutate_entry_for_test(
                    &mut draft.core,
                    crate::core::provider::EntryMutation::ParameterClass(vec![(original, actual)]),
                );
                match position {
                    0 => draft.formal_parameters[0].1 = actual,
                    1 => draft.hidden_answer = actual,
                    _ => draft.hidden_row = EffectRowVariable::rigid(actual),
                }
                assert!(
                    draft
                        .check_flow(definition, &mut TypeWorkBudget::unbounded())
                        .is_err(),
                    "accepted coherent {phase:?} parameter class {position}"
                );
            }
        }
    }

    #[test]
    fn lifecycle_entry_checks_statement_finish_ordered_formals_and_acquire_input() {
        let fixture = Fixture::with_registrations(
            &format!("import @foreign.provider as Provider\n{SOURCE}\n{STATEMENT}"),
            ForeignRegistrations::new([
                sqlite_manifest(ForeignRegistrationId::new(991)).unwrap(),
                crate::foreign::provider_manifest(ForeignRegistrationId::new(992)).unwrap(),
            ])
            .unwrap(),
        );
        let definition = &fixture.resolved.resources()[1];
        let header = fixture
            .elaborator()
            .check_provider_header(&fixture.resolved, definition)
            .unwrap();
        let draft = fixture
            .elaborator()
            .compile_provider_lifecycle(definition, &header, Phase::Finish)
            .unwrap();
        draft
            .check_flow(definition, &mut TypeWorkBudget::unbounded())
            .unwrap();
        for mutation in 0..2 {
            let mut draft = fixture
                .elaborator()
                .compile_provider_lifecycle(definition, &header, Phase::Finish)
                .unwrap();
            if mutation == 0 {
                draft.formal_parameters.swap(0, 1);
            } else {
                draft.formal_parameters[1].1 = draft.formal_parameters[0].1;
            }
            assert!(
                draft
                    .check_flow(definition, &mut TypeWorkBudget::unbounded())
                    .is_err()
            );
        }
        let connection = &fixture.resolved.resources()[0];
        let header = fixture
            .elaborator()
            .check_provider_header(&fixture.resolved, connection)
            .unwrap();
        let draft = fixture
            .elaborator()
            .compile_provider_lifecycle(connection, &header, Phase::Acquire)
            .unwrap();
        let mut changed = connection.clone();
        changed.input.ty = Type::Int;
        assert!(
            draft
                .check_flow(&changed, &mut TypeWorkBudget::unbounded())
                .is_err()
        );
    }

    #[test]
    fn lifecycle_entry_rejects_transplanted_template_hidden_binders_and_header_types() {
        let fixture = Fixture::new(SOURCE);
        let definition = &fixture.resolved.resources()[0];
        let header = fixture
            .elaborator()
            .check_provider_header(&fixture.resolved, definition)
            .unwrap();
        let mut admitted = Vec::new();
        for mutation in 0..8 {
            let mut canonical = definition.clone();
            let mut draft = fixture
                .elaborator()
                .compile_provider_lifecycle(definition, &header, Phase::Finish)
                .unwrap();
            match mutation {
                0 => {
                    draft.id = ProviderTemplateId::new(
                        crate::resolved::ResourceDefinitionId::new(definition.id.module(), 99),
                        1,
                    )
                }
                1 => draft.id = ProviderTemplateId::new(definition.id, 0),
                2 => draft.hidden_answer = draft.formal_parameters[0].1,
                3 => draft.hidden_row = EffectRowVariable::rigid(draft.hidden_answer),
                4 => draft.formal_parameters[0].0 = definition.answer.id,
                5 => draft.formal_parameters[0].2 = Kind::EffectRow,
                6 => canonical.finish_binder.id = definition.acquire_binder.id,
                7 => canonical.state.ty = Type::Int,
                _ => unreachable!(),
            }
            if draft
                .check_flow(&canonical, &mut TypeWorkBudget::unbounded())
                .is_ok()
            {
                admitted.push(mutation);
            }
        }
        assert!(
            admitted.is_empty(),
            "admitted invalid lifecycle entries: {admitted:?}"
        );
    }

    #[test]
    fn lifecycle_report_rejects_consumed_success_and_failure_role_swaps() {
        let finish = "finish state => match (perform Native.Connection<R>.close state) {\nNative.Consumed => Native.Consumed\nNative.ConsumedFailure(error) => Native.ConsumedFailure error\nNative.Retained(held, error) => Native.Retained(held, error)\n}";
        for replacement in [
            finish.replace("Native.Consumed => Native.Consumed", "Native.Consumed => Native.ConsumedFailure (Native.CloseFailure Native.ConversionFailure)"),
            finish.replace("Native.ConsumedFailure(error) => Native.ConsumedFailure error", "Native.ConsumedFailure(error) => Native.Consumed"),
        ] {
            let fixture = Fixture::new(&SOURCE.replace("finish state => perform Native.Connection<R>.close state", &replacement));
            let definition = &fixture.resolved.resources()[0];
            let header = fixture.elaborator().check_provider_header(&fixture.resolved, definition).unwrap();
            let draft = fixture.elaborator().compile_provider_lifecycle(definition, &header, Phase::Finish).unwrap();
            assert!(draft.check_flow(definition, &mut TypeWorkBudget::unbounded()).is_err(), "accepted {replacement}");
        }
    }

    #[test]
    fn lifecycle_report_permits_independent_pure_error_mapping() {
        let source = SOURCE.replace("finish state => perform Native.Connection<R>.close state", "finish state => match (perform Native.Connection<R>.close state) {\nNative.Consumed => Native.Consumed\nNative.ConsumedFailure(error) => Native.ConsumedFailure (Native.CloseFailure Native.ConversionFailure)\nNative.Retained(held, error) => Native.Retained(held, Native.CloseFailure Native.ConversionFailure)\n}");
        let fixture = Fixture::new(&source);
        let definition = &fixture.resolved.resources()[0];
        let header = fixture
            .elaborator()
            .check_provider_header(&fixture.resolved, definition)
            .unwrap();
        let draft = fixture
            .elaborator()
            .compile_provider_lifecycle(definition, &header, Phase::Finish)
            .unwrap();
        draft
            .check_flow(definition, &mut TypeWorkBudget::unbounded())
            .unwrap();
    }

    #[test]
    fn provider_state_scan_charges_nullary_row_labels_cumulatively() {
        let fixture = Fixture::new(SOURCE);
        let row = |width| {
            Type::EffectfulFunction(
                Box::new(Type::Unit),
                Box::new(ComputationType::new(
                    Type::Int,
                    EffectRow::closed(
                        (0..width)
                            .map(|ordinal| {
                                crate::types::EffectInstance::new(
                                    crate::types::EffectId::new(fixture.resolved.module(), ordinal),
                                    Box::new([]),
                                )
                            })
                            .collect(),
                    ),
                )),
            )
        };
        let narrow = row(0);
        let wide = row(64);
        let mut measured = fixture.elaborator();
        measured.type_work = TypeWorkBudget::unbounded();
        assert!(!measured.contains_provider_state(&narrow).unwrap());
        let narrow_cost = measured.type_work.used();
        measured.type_work = TypeWorkBudget::unbounded();
        assert!(!measured.contains_provider_state(&wide).unwrap());
        let cost = measured.type_work.used();
        assert_eq!(cost, narrow_cost + 64);
        for prefix in [0, 13] {
            let mut short = fixture.elaborator();
            short.type_work = TypeWorkBudget::with_limit(prefix + cost - 1);
            short.type_work.charge(prefix).unwrap();
            assert!(short.contains_provider_state(&wide).is_err());
            for _ in 0..2 {
                let mut exact = fixture.elaborator();
                exact.type_work = TypeWorkBudget::with_limit(prefix + cost);
                exact.type_work.charge(prefix).unwrap();
                assert!(!exact.contains_provider_state(&wide).unwrap());
                assert_eq!(exact.type_work.used(), prefix + cost);
            }
        }
    }

    #[test]
    fn direct_state_access_arguments_precharge_both_retained_carriers() {
        let mut short = TypeWorkBudget::with_limit(1);
        assert!(
            retain_state_access_arguments(&[TypeVariableId::new(0)], &[&Type::Int], &mut short,)
                .is_err()
        );
        assert_eq!(
            short.used(),
            0,
            "carrier refusal must precede either allocation"
        );
        let mut measured = TypeWorkBudget::with_limit(usize::MAX);
        drop(
            retain_state_access_arguments(&[TypeVariableId::new(0)], &[&Type::Int], &mut measured)
                .unwrap(),
        );
        assert_eq!(measured.used(), 4);
        let mut exact = TypeWorkBudget::with_limit(4);
        drop(
            retain_state_access_arguments(&[TypeVariableId::new(0)], &[&Type::Int], &mut exact)
                .unwrap(),
        );
        let mut one_short = TypeWorkBudget::with_limit(3);
        assert!(retain_state_access_arguments(
            &[TypeVariableId::new(0)], &[&Type::Int], &mut one_short,
        ).is_err());
        let mut prefixed = TypeWorkBudget::with_limit(5);
        prefixed.charge(1).unwrap();
        drop(
            retain_state_access_arguments(&[TypeVariableId::new(0)], &[&Type::Int], &mut prefixed)
                .unwrap(),
        );
        assert_eq!(prefixed.used(), 5);
    }

    #[test]
    fn direct_state_access_arguments_deep_failure_and_duplicate_drop_on_small_stack() {
        const CHILD: &str = "ASH_STATE_ACCESS_ARGUMENT_DROP_CHILD";
        if std::env::var_os(CHILD).is_none() {
            let output = std::process::Command::new(std::env::current_exe().unwrap())
                .args(["--exact", "elaborate::provider::tests::direct_state_access_arguments_deep_failure_and_duplicate_drop_on_small_stack", "--nocapture"])
                .env(CHILD, "1")
                .output()
                .unwrap();
            assert!(
                output.status.success(),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
            return;
        }
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut deep = IterativeTypeOwner::new(Type::Int);
                for _ in 0..8192 {
                    deep = IterativeTypeOwner::new(Type::Application(
                        Box::new(deep.into_inner()),
                        Box::new(Type::Int),
                    ));
                }
                let mut measured = TypeWorkBudget::with_limit(usize::MAX);
                drop(
                    clone_type_with_budget(&deep, &mut measured)
                        .map(IterativeTypeOwner::new)
                        .unwrap(),
                );
                let mut late = TypeWorkBudget::with_limit(2 + measured.used());
                assert!(
                    retain_state_access_arguments(&[TypeVariableId::new(0)], &[&deep], &mut late,)
                        .is_err()
                );
                let mut duplicate = TypeWorkBudget::with_limit(usize::MAX);
                assert!(
                    retain_state_access_arguments(
                        &[TypeVariableId::new(0), TypeVariableId::new(0)],
                        &[&deep, &deep],
                        &mut duplicate,
                    )
                    .is_err()
                );
            })
            .unwrap()
            .join()
            .unwrap();
    }

    struct Fixture {
        graph: ModuleGraph,
        resolved: ResolvedModule,
    }
    impl Fixture {
        fn new(source: &str) -> Self {
            Self::with_registrations(
                source,
                ForeignRegistrations::new([
                    sqlite_manifest(ForeignRegistrationId::new(991)).unwrap()
                ])
                .unwrap(),
            )
        }
        fn with_registrations(source: &str, registrations: ForeignRegistrations) -> Self {
            Self::with_modules(source, &[], registrations)
        }
        fn with_modules(
            source: &str,
            modules: &[(&str, &str)],
            registrations: ForeignRegistrations,
        ) -> Self {
            let path = std::env::temp_dir().join(format!(
                "ash-provider-template-{}-{}",
                std::process::id(),
                IDS.fetch_add(1, Ordering::Relaxed)
            ));
            fs::create_dir_all(&path).unwrap();
            let entry = path.join("entry.ash");
            fs::write(&entry, source).unwrap();
            for (name, text) in modules {
                fs::write(path.join(name), text).unwrap();
            }
            let roots = ModuleRoots::empty().with_foreign_registrations(registrations);
            let graph = load_module_graph(&entry, &roots).unwrap();
            let mut checked = Vec::<CheckedModule>::new();
            for module in &graph.modules()[..graph.modules().len() - 1] {
                let dependencies = module
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
                checked.push(check_module(resolve_module(module, &dependencies).unwrap()).unwrap());
            }
            let module = graph.modules().last().unwrap();
            let dependencies = module
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
            let resolved = resolve_module(module, &dependencies).unwrap();
            fs::remove_dir_all(path).unwrap();
            Self { graph, resolved }
        }
        fn elaborator(&self) -> EffectElaborator {
            let mut budget = TypeWorkBudget::default();
            let registry = Arc::new(
                self.resolved
                    .registry()
                    .provider_template_view(self.resolved.imported_facts(), &mut budget)
                    .unwrap(),
            );
            CoreElaborator::for_module_with_registry(
                &self.resolved,
                registry,
                budget,
                UsefulnessBudget::default(),
            )
            .unwrap()
        }
    }
    #[test]
    fn lifecycle_owned_admission_uses_resolver_provenance_after_loader_disposal() {
        let fixture = Fixture::new(SOURCE);
        let header = fixture
            .elaborator()
            .check_provider_header(&fixture.resolved, &fixture.resolved.resources()[0])
            .unwrap();
        let draft = fixture
            .elaborator()
            .compile_provider_lifecycle_with_externals(
                &fixture.resolved.resources()[0],
                &header,
                Phase::Acquire,
                fixture.resolved.imported_facts(),
            )
            .unwrap();
        let Fixture { graph, resolved } = fixture;
        let admitted_sources = resolved
            .defining_sources()
            .iter()
            .map(|(module, source)| (*module, source.id()))
            .collect::<Vec<_>>();
        assert_eq!(admitted_sources.len(), graph.modules().len());
        drop(graph);
        let checked = draft
            .admit_from_defining_module(&resolved, &mut TypeWorkBudget::unbounded())
            .unwrap();
        drop(resolved);
        assert_eq!(
            checked.draft.id.definition().module(),
            admitted_sources[0].0
        );
    }

    #[test]
    fn normal_provider_declaration_links_ordinary_entry_with_separate_code() {
        let fixture = Fixture::new(&format!("{SOURCE}\nmain : Unit -> Int\nmain () = 42\n"));
        let mut checked = Vec::<CheckedModule>::new();
        for loaded in fixture.graph.modules() {
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
            checked.push(check_module(resolve_module(loaded, &dependencies).unwrap()).unwrap());
        }
        let linked = super::super::link_modules(checked, fixture.graph.entry()).unwrap();
        let validated = crate::validate_linked_facts_for_test(linked).unwrap();
        let mut elaborator =
            super::super::EffectElaborator::for_module_program(&validated).unwrap();
        let typed = elaborator
            .synthesize_effect_module_program(&validated)
            .unwrap();
        let core = elaborator.finish(typed.node).unwrap();
        let sources = fixture
            .graph
            .modules()
            .iter()
            .map(|module| module.source())
            .collect::<Vec<_>>();
        let module_sources = fixture
            .graph
            .modules()
            .iter()
            .map(|module| (module.id(), module.source().id()))
            .collect::<Vec<_>>();
        let mut alternate = super::super::EffectElaborator::for_module_program(&validated).unwrap();
        let typed = alternate
            .synthesize_effect_module_program(&validated)
            .unwrap();
        let alternate = alternate.finish(typed.node).unwrap();
        assert_eq!(
            match crate::core::validate_effect(alternate, &sources) {
                Err(error) => error.reason(),
                Ok(_) => panic!("independent Core accepted inconsistent provider metadata"),
            },
            crate::core::ValidationReason::Registry
        );
        let mut erased = super::super::EffectElaborator::for_module_program(&validated).unwrap();
        let typed = erased.synthesize_effect_module_program(&validated).unwrap();
        let mut erased = erased.finish(typed.node).unwrap();
        crate::core::erase_provider_certificates_for_test(&mut erased);
        assert_eq!(
            match crate::core::validate_effect_modules(erased, &sources, &module_sources) {
                Err(error) => error.reason(),
                Ok(_) => panic!("independent Core accepted inconsistent provider metadata"),
            },
            crate::core::ValidationReason::Registry
        );
        for mutation in 0..12 {
            let mut candidate =
                super::super::EffectElaborator::for_module_program(&validated).unwrap();
            let typed = candidate
                .synthesize_effect_module_program(&validated)
                .unwrap();
            let mut candidate = candidate.finish(typed.node).unwrap();
            assert!(crate::core::corrupt_provider_core_closure_for_test(
                &mut candidate,
                mutation,
                validated.result().span,
            ));
            assert_eq!(
                match crate::core::validate_effect_modules(candidate, &sources, &module_sources) {
                    Err(error) => error.reason(),
                    Ok(_) => panic!("independent Core accepted inconsistent provider metadata"),
                },
                crate::core::ValidationReason::Registry,
                "final Core closure mutation {mutation}",
            );
        }
        let mut native = super::super::EffectElaborator::for_module_program(&validated).unwrap();
        let typed = native.synthesize_effect_module_program(&validated).unwrap();
        let mut native = native.finish(typed.node).unwrap();
        crate::core::erase_registered_foreign_facts_for_test(&mut native);
        assert_eq!(
            match crate::core::validate_effect_modules(native, &sources, &module_sources) {
                Err(error) => error.reason(),
                Ok(_) => panic!("independent Core accepted inconsistent provider metadata"),
            },
            crate::core::ValidationReason::Registry,
        );
        let mut wrong_sources = module_sources.clone();
        let defining = wrong_sources
            .iter_mut()
            .find(|(module, _)| *module == fixture.graph.entry())
            .unwrap();
        defining.1 = sources
            .iter()
            .find(|source| source.id() != defining.1)
            .unwrap()
            .id();
        let mut wrong = super::super::EffectElaborator::for_module_program(&validated).unwrap();
        let typed = wrong.synthesize_effect_module_program(&validated).unwrap();
        let wrong = wrong.finish(typed.node).unwrap();
        assert_eq!(
            match crate::core::validate_effect_modules(wrong, &sources, &wrong_sources) {
                Err(error) => error.reason(),
                Ok(_) => panic!("independent Core accepted inconsistent provider metadata"),
            },
            crate::core::ValidationReason::Registry,
        );
        let mut measured = TypeWorkBudget::unbounded();
        crate::core::check_ordinary_effect_modules_with_budget_for_test(
            &core,
            &sources,
            &module_sources,
            &mut measured,
        )
        .unwrap();
        let exact = measured.used();
        assert!(exact > 0);
        for prefix in [0, 17] {
            for succeeds in [false, true, true] {
                let mut work = TypeWorkBudget::with_limit(prefix + exact - usize::from(!succeeds));
                work.charge(prefix).unwrap();
                let result = crate::core::check_ordinary_effect_modules_with_budget_for_test(
                    &core,
                    &sources,
                    &module_sources,
                    &mut work,
                );
                if succeeds {
                    result.unwrap();
                    assert_eq!(work.used(), prefix + exact);
                } else {
                    assert_eq!(
                        result.unwrap_err().reason(),
                        crate::core::ValidationReason::Resource
                    );
                    assert!(work.used() >= prefix && work.used() < prefix + exact);
                }
            }
        }
        let core = crate::core::validate_effect_modules(core, &sources, &module_sources).unwrap();
        assert_eq!(
            crate::eval::evaluate_effect(&core)
                .unwrap()
                .value
                .to_string(),
            "42"
        );
    }

    #[test]
    fn provider_application_witness_refuses_coherent_fact_and_written_mirror_forgery() {
        let fixture = Fixture::new(SOURCE);
        let definition = &fixture.resolved.resources()[0];
        let header = fixture
            .elaborator()
            .check_provider_header(&fixture.resolved, definition)
            .unwrap();
        let mut work = TypeWorkBudget::unbounded();
        let mut fact =
            crate::resolved::ResourceTypeFact::from_definition_with_budget(definition, &mut work)
                .unwrap();
        authenticate_provider_application_witness(&fact, &header.provider_application, &mut work)
            .unwrap();
        let original = fact
            .provider_application
            .clone_with_budget(&mut work)
            .unwrap();
        fact.provider_application.arguments_mut_for_summary_test()[0] =
            crate::types::KindedArgument::TypeArg(Type::Int);
        assert_eq!(
            authenticate_provider_application_witness(
                &fact,
                &header.provider_application,
                &mut work
            ),
            Err(crate::resolved::ResolvedBuildFailure::InvalidState)
        );
        let written = crate::types::IterativeArgumentOwner::new(std::mem::replace(
            &mut fact.provider.arguments[0].ty,
            crate::types::KindedArgument::TypeArg(Type::Int),
        ));
        assert_eq!(
            authenticate_provider_application_witness(
                &fact,
                &header.provider_application,
                &mut work
            ),
            Err(crate::resolved::ResolvedBuildFailure::InvalidState)
        );
        // The independently checked header was captured before either fact
        // field changed and remains the original application authority.
        fact.provider.arguments[0].ty = written.into_inner();
        fact.provider_application = original;
        authenticate_provider_application_witness(&fact, &header.provider_application, &mut work)
            .unwrap();
        fact.provider_application.arguments_mut_for_summary_test()[0] =
            crate::types::KindedArgument::RowArg(EffectRow::empty());
        assert_eq!(
            authenticate_provider_application_witness(
                &fact,
                &header.provider_application,
                &mut work
            ),
            Err(crate::resolved::ResolvedBuildFailure::InvalidState)
        );
    }

    #[test]
    fn normal_provider_link_requires_separate_code_and_canonical_closure() {
        for mutation in 0..7 {
            let fixture = Fixture::new(&format!("{SOURCE}\nmain : Unit -> Int\nmain () = 42\n"));
            let mut checked = Vec::<CheckedModule>::new();
            for loaded in fixture.graph.modules() {
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
                checked.push(check_module(resolve_module(loaded, &dependencies).unwrap()).unwrap());
            }
            if mutation == 5 {
                let entry = checked
                    .iter_mut()
                    .find(|module| module.module() == fixture.graph.entry())
                    .unwrap();
                let code = entry.take_provider_code_for_test().unwrap();
                entry
                    .exports()
                    .authenticate(
                        &mut TypeWorkBudget::unbounded(),
                        &mut InterfaceConstraintBudget::with_limit(usize::MAX),
                    )
                    .unwrap();
                drop(code);
                assert!(matches!(
                    super::super::link_modules(checked, fixture.graph.entry()),
                    Err(TypeError::Internal(ElaborationFailure::InvalidState))
                ));
            } else {
                let mut linked =
                    super::super::link_modules(checked, fixture.graph.entry()).unwrap();
                assert!(
                    linked.corrupt_provider_contract_closure_for_test(if mutation == 6 {
                        5
                    } else {
                        mutation
                    })
                );
                assert!(
                    crate::validate_linked_facts_for_test(linked).is_err(),
                    "closure mutation {mutation}"
                );
            }
        }
    }

    #[test]
    fn normal_provider_retained_code_refuses_wrong_template_and_hidden_owner() {
        for mutation in 0..4 {
            let fixture = Fixture::new(&format!("{SOURCE}\nmain : Unit -> Int\nmain () = 42\n"));
            let build = || {
                let mut modules = Vec::<CheckedModule>::new();
                for loaded in fixture.graph.modules() {
                    let dependencies = loaded
                        .dependencies()
                        .iter()
                        .map(|edge| {
                            DependencyExports::new(
                                edge,
                                modules
                                    .iter()
                                    .find(|module| module.module() == edge.target())
                                    .unwrap()
                                    .exports(),
                            )
                            .unwrap()
                        })
                        .collect::<Vec<_>>();
                    modules.push(
                        check_module(resolve_module(loaded, &dependencies).unwrap()).unwrap(),
                    );
                }
                modules
            };
            let positive = super::super::link_modules(build(), fixture.graph.entry()).unwrap();
            crate::validate_linked_facts_for_test(positive).unwrap();
            let mut modules = build();
            let checked = modules
                .iter_mut()
                .find(|module| module.module() == fixture.graph.entry())
                .unwrap();
            let mut code = checked.take_provider_code_for_test().unwrap();
            let certificate = Arc::clone(code.contracts());
            let owned =
                Arc::get_mut(&mut code).expect("only code ownership is retained separately");
            let declaration = Arc::get_mut(&mut owned.declarations[0])
                .expect("original declaration is uniquely retained");
            match mutation {
                0 => declaration.acquire.draft.id = declaration.finish.draft.id,
                1 => {
                    declaration.acquire.draft.hidden_answer =
                        TypeVariableId::resolved(owned.module, u32::MAX)
                }
                2 => crate::core::provider::mutate_entry_for_test(
                    &mut declaration.finish.draft.core,
                    crate::core::provider::EntryMutation::RootType,
                ),
                3 => {
                    declaration.acquire.draft.hidden_row =
                        EffectRowVariable::Rigid(declaration.acquire.draft.hidden_answer)
                }
                _ => unreachable!(),
            }
            assert!(matches!(
                code.authenticate_code(&certificate, &mut TypeWorkBudget::unbounded()),
                Err(crate::resolved::ResolvedBuildFailure::InvalidState)
            ));
            checked.restore_provider_code_for_test(code);
            assert!(
                matches!(
                    super::super::link_modules(modules, fixture.graph.entry()),
                    Err(TypeError::Internal(ElaborationFailure::InvalidState))
                ),
                "mutated template {mutation} must refuse defining summary/code linkage"
            );
        }
    }

    #[test]
    fn normal_provider_same_id_fresh_code_cannot_replace_the_defining_certificate() {
        let fixture = Fixture::new(&format!("{SOURCE}\nmain : Unit -> Int\nmain () = 42\n"));
        let build = || {
            let mut modules = Vec::<CheckedModule>::new();
            for loaded in fixture.graph.modules() {
                let dependencies = loaded
                    .dependencies()
                    .iter()
                    .map(|edge| {
                        DependencyExports::new(
                            edge,
                            modules
                                .iter()
                                .find(|module| module.module() == edge.target())
                                .unwrap()
                                .exports(),
                        )
                        .unwrap()
                    })
                    .collect::<Vec<_>>();
                modules.push(check_module(resolve_module(loaded, &dependencies).unwrap()).unwrap());
            }
            modules
        };
        let positive = super::super::link_modules(build(), fixture.graph.entry()).unwrap();
        crate::validate_linked_facts_for_test(positive).unwrap();
        let mut original = build();
        let mut replacement = build();
        let original_summary = original
            .iter()
            .find(|module| module.module() == fixture.graph.entry())
            .unwrap()
            .exports();
        let replacement_summary = replacement
            .iter()
            .find(|module| module.module() == fixture.graph.entry())
            .unwrap()
            .exports();
        let mut imported = crate::resolved::ImportedFacts::default();
        let mut work = TypeWorkBudget::unbounded();
        imported
            .retain_provider_contracts(original_summary, &mut work)
            .unwrap();
        imported
            .retain_provider_contracts(original_summary, &mut work)
            .unwrap();
        assert!(matches!(
            imported.retain_provider_contracts(replacement_summary, &mut work),
            Err(crate::resolved::ResolvedBuildFailure::InvalidState)
        ));

        let donor = replacement
            .iter_mut()
            .find(|module| module.module() == fixture.graph.entry())
            .unwrap()
            .take_provider_code_for_test()
            .unwrap();
        let defining = original
            .iter_mut()
            .find(|module| module.module() == fixture.graph.entry())
            .unwrap();
        let code = defining.take_provider_code_for_test().unwrap();
        assert_eq!(code.module, donor.module);
        assert_eq!(
            code.declarations[0].acquire.draft.id,
            donor.declarations[0].acquire.draft.id
        );
        assert!(!Arc::ptr_eq(code.contracts(), donor.contracts()));
        assert!(matches!(
            donor.authenticate_code(code.contracts(), &mut TypeWorkBudget::unbounded()),
            Err(crate::resolved::ResolvedBuildFailure::InvalidState)
        ));
        defining.restore_provider_code_for_test(donor);
        assert!(
            matches!(
                super::super::link_modules(original, fixture.graph.entry()),
                Err(TypeError::Internal(ElaborationFailure::InvalidState))
            ),
            "same-ID code must authenticate against the original defining certificate"
        );
    }

    #[test]
    fn normal_provider_linked_authentication_has_exact_shared_budgets_and_fresh_retry() {
        let fixture = Fixture::new(&format!("{SOURCE}\nmain : Unit -> Int\nmain () = 42\n"));
        let build = || {
            let mut modules = Vec::<CheckedModule>::new();
            for loaded in fixture.graph.modules() {
                let dependencies = loaded
                    .dependencies()
                    .iter()
                    .map(|edge| {
                        DependencyExports::new(
                            edge,
                            modules
                                .iter()
                                .find(|module| module.module() == edge.target())
                                .unwrap()
                                .exports(),
                        )
                        .unwrap()
                    })
                    .collect::<Vec<_>>();
                modules.push(check_module(resolve_module(loaded, &dependencies).unwrap()).unwrap());
            }
            super::super::link_modules(modules, fixture.graph.entry()).unwrap()
        };
        let mut types = TypeWorkBudget::unbounded();
        let mut constraints = InterfaceConstraintBudget::with_limit(usize::MAX);
        crate::evidence_validation::validate_interface_evidence_with_budget(
            build(),
            &mut constraints,
            &mut types,
        )
        .unwrap();
        let costs = [types.used(), constraints.used()];
        assert!(costs.iter().all(|cost| *cost > 0));
        for (axis, cost) in costs.into_iter().enumerate() {
            for prefix in [0, 19] {
                for succeeds in [false, true, true] {
                    let limit = prefix + cost - usize::from(!succeeds);
                    let mut types =
                        TypeWorkBudget::with_limit(if axis == 0 { limit } else { usize::MAX });
                    let mut constraints = InterfaceConstraintBudget::with_limit(if axis == 1 {
                        limit
                    } else {
                        usize::MAX
                    });
                    if axis == 0 {
                        types.charge(prefix).unwrap();
                    } else {
                        constraints.charge(prefix).unwrap();
                    }
                    let result =
                        crate::evidence_validation::validate_interface_evidence_with_budget(
                            build(),
                            &mut constraints,
                            &mut types,
                        );
                    let used = if axis == 0 {
                        types.used()
                    } else {
                        constraints.used()
                    };
                    if succeeds {
                        result.unwrap();
                        assert_eq!(used, prefix + cost);
                    } else {
                        let error = match result {
                            Err(error) => error,
                            Ok(_) => panic!("one-short linked admission unexpectedly succeeded"),
                        };
                        assert_eq!(
                            error.reason(),
                            if axis == 0 {
                                crate::evidence_validation::EvidenceValidationReason::TypeResourceExhausted
                            } else {
                                crate::evidence_validation::EvidenceValidationReason::ConstraintResourceExhausted
                            }
                        );
                        assert!(used > prefix && used <= limit);
                    }
                }
            }
        }
    }

    #[test]
    fn normal_provider_helpers_use_completed_local_facts() {
        let source = SOURCE.replace(
            "read db => resume (perform Native.Connection<R>.diagnostic state)",
            "read db => resume (relay (perform Native.Connection<R>.diagnostic state))",
        );
        let source =
            format!("{source}\nrelay : Native.Error -> Native.Error\nrelay error = error\n");
        let fixture = Fixture::new(&source);
        check_module(fixture.resolved).unwrap();
    }

    #[test]
    fn normal_provider_helpers_use_imported_facts() {
        let source = SOURCE.replace(
            "read db => resume (perform Native.Connection<R>.diagnostic state)",
            "read db => resume (relay (perform Native.Connection<R>.diagnostic state))",
        );
        let source = format!("import helper (relay)\n{source}");
        let fixture = Fixture::with_modules(
            &source,
            &[(
                "helper.ash",
                "import @foreign.sqlite as Native\npub relay : Native.Error -> Native.Error\nrelay error = error\n",
            )],
            ForeignRegistrations::new([sqlite_manifest(ForeignRegistrationId::new(991)).unwrap()])
                .unwrap(),
        );
        check_module(fixture.resolved).unwrap();
    }

    #[test]
    fn normal_provider_exports_are_bodyfree_after_defining_code_disposal() {
        let Fixture { graph, resolved } = Fixture::new(SOURCE);
        let exports = check_module(resolved).unwrap().into_exports();
        drop(graph);
        let churn = (0..256)
            .map(|index| {
                crate::source::SourceFile::new(format!("churn-{index}.ash"), "val x = 1").unwrap()
            })
            .collect::<Vec<_>>();
        assert_eq!(exports.resource_types().count(), 1);
        let fact = exports.resource_type("Connection").unwrap();
        assert_eq!(fact.id.module(), exports.module());
        exports
            .authenticate(
                &mut TypeWorkBudget::unbounded(),
                &mut InterfaceConstraintBudget::with_limit(usize::MAX),
            )
            .unwrap();
        drop(churn);
    }

    #[test]
    fn normal_provider_client_checks_after_defining_code_and_loaded_body_disposal() {
        let Fixture { graph, resolved } = Fixture::with_modules(
            "pub import provider (Connection as Alias)\n",
            &[("provider.ash", SOURCE)],
            ForeignRegistrations::new([sqlite_manifest(ForeignRegistrationId::new(991)).unwrap()])
                .unwrap(),
        );
        drop(resolved);
        let client = graph
            .modules()
            .iter()
            .find(|module| module.id() == graph.entry())
            .unwrap()
            .clone();
        let mut summaries = Vec::<crate::resolved::ExportSummary>::new();
        for loaded in graph
            .modules()
            .iter()
            .filter(|module| module.id() != graph.entry())
        {
            let dependencies = loaded
                .dependencies()
                .iter()
                .map(|edge| {
                    DependencyExports::new(
                        edge,
                        summaries
                            .iter()
                            .find(|summary| summary.module() == edge.target())
                            .unwrap(),
                    )
                    .unwrap()
                })
                .collect::<Vec<_>>();
            // Conversion consumes and disposes the actual defining Core owner.
            summaries.push(
                check_module(resolve_module(loaded, &dependencies).unwrap())
                    .unwrap()
                    .into_exports(),
            );
        }
        drop(graph);
        let churn = (0..256)
            .map(|index| {
                crate::source::SourceFile::new(
                    format!("disposed-provider-{index}.ash"),
                    "main () = 0",
                )
                .unwrap()
            })
            .collect::<Vec<_>>();
        let dependencies = client
            .dependencies()
            .iter()
            .map(|edge| {
                DependencyExports::new(
                    edge,
                    summaries
                        .iter()
                        .find(|summary| summary.module() == edge.target())
                        .unwrap(),
                )
                .unwrap()
            })
            .collect::<Vec<_>>();
        let checked = check_module(resolve_module(&client, &dependencies).unwrap()).unwrap();
        let fact = checked.exports().resource_type("Alias").unwrap();
        assert_ne!(fact.id.module(), checked.module());
        checked
            .exports()
            .authenticate(
                &mut TypeWorkBudget::unbounded(),
                &mut InterfaceConstraintBudget::with_limit(usize::MAX),
            )
            .unwrap();
        drop(churn);
    }

    #[test]
    fn normal_provider_import_alias_diamond_preserves_one_canonical_contract() {
        let registrations =
            ForeignRegistrations::new([sqlite_manifest(ForeignRegistrationId::new(991)).unwrap()])
                .unwrap();
        let Fixture { graph, resolved } = Fixture::with_modules(
            "pub import left (LeftConnection as First)\npub import right (RightConnection as Second)\n",
            &[
                ("provider.ash", SOURCE),
                (
                    "left.ash",
                    "pub import provider (Connection as LeftConnection)\n",
                ),
                (
                    "right.ash",
                    "pub import provider (Connection as RightConnection)\n",
                ),
            ],
            registrations,
        );
        let exports = check_module(resolved).unwrap().into_exports();
        drop(graph);
        let first = exports.resource_type("First").unwrap();
        let second = exports.resource_type("Second").unwrap();
        assert!(Arc::ptr_eq(first, second));
        assert_ne!(first.id.module(), exports.module());
        exports
            .authenticate(
                &mut TypeWorkBudget::unbounded(),
                &mut InterfaceConstraintBudget::with_limit(usize::MAX),
            )
            .unwrap();
    }

    #[test]
    fn normal_provider_connection_statement_group_publishes_together() {
        let Fixture { graph, resolved } = Fixture::with_registrations(
            &format!("import @foreign.provider as Provider\n{SOURCE}\n{STATEMENT}"),
            ForeignRegistrations::new([
                sqlite_manifest(ForeignRegistrationId::new(991)).unwrap(),
                crate::foreign::provider_manifest(ForeignRegistrationId::new(992)).unwrap(),
            ])
            .unwrap(),
        );
        let exports = check_module(resolved).unwrap().into_exports();
        drop(graph);
        assert_eq!(exports.resource_types().count(), 2);
        exports
            .authenticate(
                &mut TypeWorkBudget::unbounded(),
                &mut InterfaceConstraintBudget::with_limit(usize::MAX),
            )
            .unwrap();
    }

    #[test]
    fn canonical_native_provider_header_checks_without_opening_client_instances() {
        let fixture = Fixture::new(SOURCE);
        let header = fixture
            .elaborator()
            .check_provider_header(&fixture.resolved, &fixture.resolved.resources()[0])
            .unwrap();
        assert_ne!(header.acquire, header.finish);
        assert_eq!(header.methods.len(), 1);
        assert_eq!(header.scope_constructors[0].constructor(), 0);
        assert_eq!(header.completion_constructors[2].constructor(), 2);
        assert!(header.input_error.outer_nominal().is_some());
        assert!(header.completion_error.outer_nominal().is_some());
        assert_eq!(fixture.graph.modules().len(), 2);
        check_module(Fixture::new(SOURCE).resolved).expect("normal module declaration checking");
    }

    #[test]
    fn provider_header_rejects_wrong_owned_state_method_row_and_report_types() {
        let cases = [
            SOURCE.replace(
                "state Native.ConnectionState<R>",
                "state Native.ConnectionState<Int>",
            ),
            SOURCE.replace("state Native.ConnectionState<R>", "state Native.OpenConfig"),
            SOURCE.replace(" ! {Ops<R>}", ""),
            SOURCE.replace(
                "read : Connection<R> -> Native.Error !",
                "read : Connection<R> -> Int !",
            ),
            SOURCE.replace(
                "Scope<Native.OpenError, Native.CloseError, T>",
                "Scope<Native.OpenError, Native.CloseError, Int>",
            ),
            SOURCE.replace("interpret Native.Connection<R>", "interpret Ops<R>"),
        ];
        for source in cases {
            let fixture = Fixture::new(&source);
            assert!(
                fixture
                    .elaborator()
                    .check_provider_header(&fixture.resolved, &fixture.resolved.resources()[0])
                    .is_err(),
                "accepted {source}"
            );
        }
    }

    #[test]
    fn report_constructor_order_is_a_checked_codec_contract() {
        for source in [
            SOURCE.replace(
                "pub type Scope<I, E, T> = NotAcquired(I)\n| Completed(T, Completion<E>)",
                "pub type Scope<I, E, T> = Completed(T, Completion<E>)\n| NotAcquired(I)",
            ),
            SOURCE.replace(
                "pub type Completion<E> = Closed\n| ConsumedError(E)",
                "pub type Completion<E> = ConsumedError(E)\n| Closed",
            ),
            SOURCE.replace("NotAcquired(I)", "NotAcquired(Native.OpenError)"),
        ] {
            let fixture = Fixture::new(&source);
            assert!(
                fixture
                    .elaborator()
                    .check_provider_header(&fixture.resolved, &fixture.resolved.resources()[0])
                    .is_err(),
                "accepted {source}"
            );
        }
    }

    #[test]
    fn header_checking_has_a_cumulative_exact_budget_and_does_not_publish_on_failure() {
        let fixture = Fixture::new(SOURCE);
        let mut elaborator = fixture.elaborator();
        elaborator.type_work = TypeWorkBudget::with_limit(usize::MAX);
        elaborator
            .check_provider_header(&fixture.resolved, &fixture.resolved.resources()[0])
            .unwrap();
        let exact = elaborator.type_work.used();
        let mut short = fixture.elaborator();
        short.type_work = TypeWorkBudget::with_limit(exact - 1);
        assert!(
            short
                .check_provider_header(&fixture.resolved, &fixture.resolved.resources()[0])
                .is_err()
        );
        let mut retry = fixture.elaborator();
        retry.type_work = TypeWorkBudget::with_limit(exact);
        retry
            .check_provider_header(&fixture.resolved, &fixture.resolved.resources()[0])
            .unwrap();
        assert_eq!(retry.type_work.used(), exact);
    }

    #[test]
    fn lifecycle_templates_clear_privilege_at_source_callable_boundaries() {
        for (phase, source) in [
            (Phase::Acquire, SOURCE.replace("acquire config => perform Native.Connection<R>.open config", "acquire config => {\nlet f = fn(c) {\nperform Native.Connection<R>.open c\n}\nf config\n}")),
            (Phase::Finish, SOURCE.replace("finish state => perform Native.Connection<R>.close state", "finish state => {\nlet f = fn(s) {\nperform Native.Connection<R>.close s\n}\nf state\n}")),
        ] {
            let fixture = Fixture::new(&source);
            let header = fixture.elaborator().check_provider_header(&fixture.resolved, &fixture.resolved.resources()[0]).unwrap();
            assert!(fixture.elaborator().compile_provider_lifecycle(&fixture.resolved.resources()[0], &header, phase).is_err());
        }
    }

    #[test]
    fn lifecycle_state_cannot_be_captured_or_passed_through_a_pure_identity() {
        for replacement in [
            "finish state => {\nlet ignored = fn(()) {\nlet held = state\n42\n}\nperform Native.Connection<R>.close state\n}",
            "finish state => {\nlet same = fn(x) {\nx\n}\nperform Native.Connection<R>.close (same state)\n}",
        ] {
            let source = SOURCE.replace(
                "finish state => perform Native.Connection<R>.close state",
                replacement,
            );
            let fixture = Fixture::new(&source);
            let header = fixture
                .elaborator()
                .check_provider_header(&fixture.resolved, &fixture.resolved.resources()[0])
                .unwrap();
            assert!(
                fixture
                    .elaborator()
                    .compile_provider_lifecycle(
                        &fixture.resolved.resources()[0],
                        &header,
                        Phase::Finish
                    )
                    .is_err()
            );
        }
    }

    #[test]
    fn lifecycle_templates_reject_wrong_native_roles() {
        for (phase, source) in [
            (
                Phase::Acquire,
                SOURCE.replace(".open config", ".close config"),
            ),
            (
                Phase::Finish,
                SOURCE.replace(".close state", ".diagnostic state"),
            ),
        ] {
            let fixture = Fixture::new(&source);
            let header = fixture
                .elaborator()
                .check_provider_header(&fixture.resolved, &fixture.resolved.resources()[0])
                .unwrap();
            assert!(
                fixture
                    .elaborator()
                    .compile_provider_lifecycle(&fixture.resolved.resources()[0], &header, phase)
                    .is_err()
            );
        }
    }

    #[test]
    fn lifecycle_templates_reject_handled_control_and_cleanup_before_publication() {
        let source = SOURCE.replace(
            "pub interface Reader",
            "pub effect Plain {\nvalue : Int -> Int\n}\npub interface Reader",
        );
        for source in [
            source.replace("acquire config => perform Native.Connection<R>.open config", "acquire config => {\nlet ignored = handle (perform Plain.value 0) with Plain {\nvalue n => resume n\n}\nperform Native.Connection<R>.open config\n}"),
            SOURCE.replace("acquire config => perform Native.Connection<R>.open config", "acquire config => cleanup fn(ignored) {\n()\n} {\nperform Native.Connection<R>.open config\n}"),
        ] {
            let fixture = Fixture::new(&source);
            let header = fixture.elaborator().check_provider_header(&fixture.resolved, &fixture.resolved.resources()[0]).unwrap();
            assert!(fixture.elaborator().compile_provider_lifecycle(&fixture.resolved.resources()[0], &header, Phase::Acquire).is_err());
        }
    }

    #[test]
    fn lifecycle_drafts_retain_generic_identities_without_final_program_admission() {
        let fixture = Fixture::new(SOURCE);
        let header = fixture
            .elaborator()
            .check_provider_header(&fixture.resolved, &fixture.resolved.resources()[0])
            .unwrap();
        for phase in [Phase::Acquire, Phase::Finish] {
            let draft = fixture
                .elaborator()
                .compile_provider_lifecycle(&fixture.resolved.resources()[0], &header, phase)
                .unwrap();
            assert_eq!(draft.id.definition(), fixture.resolved.resources()[0].id);
            assert_eq!(draft.phase, phase);
            assert!(draft.parameter.module().is_some());
            assert_ne!(
                draft.hidden_row,
                EffectRowVariable::rigid(draft.hidden_answer)
            );
            assert_eq!(draft.formal_parameters.len(), 1);
            let sources = fixture
                .graph
                .modules()
                .iter()
                .map(|module| module.source())
                .collect::<Vec<_>>();
            let module_sources = fixture
                .graph
                .modules()
                .iter()
                .map(|module| (module.id(), module.source().id()))
                .collect::<Vec<_>>();
            let canonical = fixture.elaborator().registry;
            let core = crate::core::validate::validate_provider_structure(
                draft.core,
                &sources,
                &module_sources,
                &canonical,
            )
            .unwrap();
            let error =
                crate::core::validate_effect_modules(core, &sources, &module_sources).unwrap_err();
            assert_eq!(error.reason(), crate::core::ValidationReason::Registry);
        }
    }

    #[test]
    fn contextual_structure_rejects_changed_imported_kind_and_native_admission() {
        let fixture = Fixture::new(SOURCE);
        let header = fixture
            .elaborator()
            .check_provider_header(&fixture.resolved, &fixture.resolved.resources()[0])
            .unwrap();
        let sources = fixture
            .graph
            .modules()
            .iter()
            .map(|module| module.source())
            .collect::<Vec<_>>();
        let module_sources = fixture
            .graph
            .modules()
            .iter()
            .map(|module| (module.id(), module.source().id()))
            .collect::<Vec<_>>();
        for mutation in 0..3 {
            let draft = fixture
                .elaborator()
                .compile_provider_lifecycle(
                    &fixture.resolved.resources()[0],
                    &header,
                    Phase::Acquire,
                )
                .unwrap();
            let mut work = TypeWorkBudget::default();
            let mut canonical = fixture
                .resolved
                .registry()
                .provider_template_view(fixture.resolved.imported_facts(), &mut work)
                .unwrap();
            match mutation {
                0 => canonical.mutate_provider_state_kind_for_test(false),
                1 => canonical.mutate_provider_state_kind_for_test(true),
                _ => canonical.remove_provider_admission_for_test(),
            }
            let error = crate::core::validate::validate_provider_structure(
                draft.core,
                &sources,
                &module_sources,
                &canonical,
            )
            .unwrap_err();
            assert_eq!(error.reason(), crate::core::ValidationReason::Registry);
        }
        // Even a coherently corrupted draft/context cannot replace the kind
        // retained in the authenticated native registration certificate.
        let mut work = TypeWorkBudget::default();
        let mut canonical = fixture
            .resolved
            .registry()
            .provider_template_view(fixture.resolved.imported_facts(), &mut work)
            .unwrap();
        canonical.mutate_provider_state_kind_for_test(false);
        assert!(
            !canonical
                .same_provider_metadata(&canonical, &mut work)
                .unwrap()
        );
    }

    #[test]
    fn contextual_metadata_rejects_annotation_only_origin_changes() {
        let fixture = Fixture::new(SOURCE);
        let missing = crate::source::SourceFile::new("missing-provider-origin.ash", "x").unwrap();
        let missing_span = missing
            .span(crate::source::ByteRange::new(0, 1).unwrap())
            .unwrap();
        for origin in [
            Origin::Source(fixture.resolved.resources()[0].span),
            Origin::Source(missing_span),
        ] {
            let mut work = TypeWorkBudget::default();
            let mut altered = fixture
                .resolved
                .registry()
                .provider_template_view(fixture.resolved.imported_facts(), &mut work)
                .unwrap();
            let canonical = fixture.elaborator().registry;
            altered.mutate_provider_annotation_origin_for_test(origin);
            assert!(
                !altered
                    .same_provider_metadata(&canonical, &mut work)
                    .unwrap()
            );
        }
    }

    #[test]
    fn contextual_structure_keeps_external_global_admission_closed() {
        let source = SOURCE.replace("pub interface Reader", "fn prepare_config(config : Native.OpenConfig) -> Native.OpenConfig {\nconfig\n}\npub interface Reader")
            .replace(".open config", ".open (prepare_config config)");
        let fixture = Fixture::new(&source);
        let header = fixture
            .elaborator()
            .check_provider_header(&fixture.resolved, &fixture.resolved.resources()[0])
            .unwrap();
        let mut elaborator = fixture.elaborator();
        // Give the checker the declared helper type, without its executable
        // graph or a checked external-global certificate. Structural Core
        // admission must still reject the resulting free global occurrence.
        let prepared = elaborator
            .prepare_definition_views(
                fixture.resolved.definitions().iter(),
                None,
                elaborator.base_context.clone(),
            )
            .unwrap();
        elaborator.base_context = prepared.context.clone();
        drop(prepared);
        let draft = elaborator
            .compile_provider_lifecycle(&fixture.resolved.resources()[0], &header, Phase::Acquire)
            .unwrap();
        let sources = fixture
            .graph
            .modules()
            .iter()
            .map(|module| module.source())
            .collect::<Vec<_>>();
        let module_sources = fixture
            .graph
            .modules()
            .iter()
            .map(|module| (module.id(), module.source().id()))
            .collect::<Vec<_>>();
        let canonical = fixture.elaborator().registry;
        assert!(
            crate::core::validate::validate_provider_structure(
                draft.core,
                &sources,
                &module_sources,
                &canonical
            )
            .is_err()
        );
    }

    #[test]
    fn contextual_effect_binder_retention_has_an_exact_cumulative_budget() {
        let fixture = Fixture::new(SOURCE);
        let mut measured = TypeWorkBudget::with_limit(usize::MAX);
        let registry = fixture
            .resolved
            .registry()
            .provider_template_view(fixture.resolved.imported_facts(), &mut measured)
            .unwrap();
        for effect in registry.effects() {
            for parameter in &effect.parameters {
                assert!(registry.type_variable(parameter.id).is_some());
            }
        }
        let exact = measured.used();
        let mut short = TypeWorkBudget::with_limit(exact - 1);
        assert!(
            fixture
                .resolved
                .registry()
                .provider_template_view(fixture.resolved.imported_facts(), &mut short)
                .is_err()
        );
        let mut retry = TypeWorkBudget::with_limit(exact);
        fixture
            .resolved
            .registry()
            .provider_template_view(fixture.resolved.imported_facts(), &mut retry)
            .unwrap();
        assert_eq!(retry.used(), exact);
    }

    #[test]
    fn independent_lifecycle_flow_rejects_fabricated_finish_duplicate_finish_and_guard_loss() {
        for (phase, source) in [
            (Phase::Finish, SOURCE.replace("finish state => perform Native.Connection<R>.close state", "finish state => Native.Consumed")),
            (Phase::Finish, SOURCE.replace("finish state => perform Native.Connection<R>.close state", "finish state => {\nlet ignored = perform Native.Connection<R>.close state\nperform Native.Connection<R>.close state\n}")),
            (Phase::Finish, SOURCE.replace("finish state => perform Native.Connection<R>.close state", "finish state => {\nlet reply = perform Native.Connection<R>.close state\nlet held = state\nreply\n}")),
            (Phase::Acquire, SOURCE.replace("acquire config => perform Native.Connection<R>.open config", "acquire config => {\nlet ignored = perform Native.Connection<R>.open config\nperform Native.Connection<R>.open config\n}")),
            (Phase::Acquire, SOURCE.replace("acquire config => perform Native.Connection<R>.open config", "acquire config => {\nlet ignored = perform Native.Connection<R>.open config\nNative.Refused (Native.OpenFailure Native.AllocationFailure)\n}")),
        ] {
            let fixture = Fixture::new(&source);
            let header = fixture.elaborator().check_provider_header(&fixture.resolved, &fixture.resolved.resources()[0]).unwrap();
            let draft = fixture.elaborator().compile_provider_lifecycle(&fixture.resolved.resources()[0], &header, phase).unwrap();
            assert!(draft.check_flow(&fixture.resolved.resources()[0], &mut TypeWorkBudget::default()).is_err(), "accepted {source}");
        }
    }

    #[test]
    fn independent_lifecycle_flow_preserves_current_state_aliases() {
        let source = SOURCE.replace(
            "finish state => perform Native.Connection<R>.close state",
            "finish state => {\nlet held = state\nperform Native.Connection<R>.close held\n}",
        );
        let fixture = Fixture::new(&source);
        let header = fixture
            .elaborator()
            .check_provider_header(&fixture.resolved, &fixture.resolved.resources()[0])
            .unwrap();
        for phase in [Phase::Acquire, Phase::Finish] {
            let draft = fixture
                .elaborator()
                .compile_provider_lifecycle(&fixture.resolved.resources()[0], &header, phase)
                .unwrap();
            draft
                .check_flow(
                    &fixture.resolved.resources()[0],
                    &mut TypeWorkBudget::default(),
                )
                .unwrap();
        }
    }

    #[test]
    fn independent_lifecycle_flow_preserves_authenticated_outcomes_through_matches() {
        let source = SOURCE
            .replace("acquire config => perform Native.Connection<R>.open config", "acquire config => match (perform Native.Connection<R>.open config) {\nNative.Acquired(held) => Native.Acquired held\nNative.Refused(error) => Native.Refused error\n}")
            .replace("finish state => perform Native.Connection<R>.close state", "finish state => match (perform Native.Connection<R>.close state) {\nNative.Consumed => Native.Consumed\nNative.ConsumedFailure(error) => Native.ConsumedFailure error\nNative.Retained(held, error) => Native.Retained(held, error)\n}");
        let fixture = Fixture::new(&source);
        let header = fixture
            .elaborator()
            .check_provider_header(&fixture.resolved, &fixture.resolved.resources()[0])
            .unwrap();
        for phase in [Phase::Acquire, Phase::Finish] {
            let draft = fixture
                .elaborator()
                .compile_provider_lifecycle(&fixture.resolved.resources()[0], &header, phase)
                .unwrap();
            draft
                .check_flow(
                    &fixture.resolved.resources()[0],
                    &mut TypeWorkBudget::default(),
                )
                .unwrap();
        }
    }

    #[test]
    fn independent_lifecycle_flow_has_a_shared_exact_budget_with_prefix_work() {
        let fixture = Fixture::new(SOURCE);
        let header = fixture
            .elaborator()
            .check_provider_header(&fixture.resolved, &fixture.resolved.resources()[0])
            .unwrap();
        for phase in [Phase::Acquire, Phase::Finish] {
            let draft = fixture
                .elaborator()
                .compile_provider_lifecycle(&fixture.resolved.resources()[0], &header, phase)
                .unwrap();
            let mut measured = TypeWorkBudget::with_limit(usize::MAX);
            measured.charge(11).unwrap();
            draft
                .check_flow(&fixture.resolved.resources()[0], &mut measured)
                .unwrap();
            let exact = measured.used();
            let mut short = TypeWorkBudget::with_limit(exact - 1);
            short.charge(11).unwrap();
            let error = draft
                .check_flow(&fixture.resolved.resources()[0], &mut short)
                .unwrap_err();
            match error {
                LifecycleDraftCheckError::Resource => {}
                LifecycleDraftCheckError::Core(error) => {
                    assert_eq!(error.reason(), crate::core::ValidationReason::Resource)
                }
                LifecycleDraftCheckError::InvalidEntry => {
                    panic!("budget exhaustion changed entry authority")
                }
            }
            let mut retry = TypeWorkBudget::with_limit(exact);
            retry.charge(11).unwrap();
            draft
                .check_flow(&fixture.resolved.resources()[0], &mut retry)
                .unwrap();
            assert_eq!(retry.used(), exact);
        }
    }

    #[test]
    fn independent_lifecycle_flow_rejects_native_role_identity_and_callable_mutations() {
        let source = SOURCE.replace("finish state => perform Native.Connection<R>.close state", "finish state => {\nlet ignored : Native.OpenConfig -> Int = fn(config) {\n42\n}\nperform Native.Connection<R>.close state\n}");
        let fixture = Fixture::new(&source);
        let header = fixture
            .elaborator()
            .check_provider_header(&fixture.resolved, &fixture.resolved.resources()[0])
            .unwrap();
        for mutation in [
            crate::core::provider::LifecycleMutation::BorrowRole,
            crate::core::provider::LifecycleMutation::OtherIdentity,
            crate::core::provider::LifecycleMutation::CallableBody,
        ] {
            let mut draft = fixture
                .elaborator()
                .compile_provider_lifecycle(
                    &fixture.resolved.resources()[0],
                    &header,
                    Phase::Finish,
                )
                .unwrap();
            draft
                .check_flow(
                    &fixture.resolved.resources()[0],
                    &mut TypeWorkBudget::default(),
                )
                .unwrap();
            crate::core::provider::mutate_lifecycle_for_test(&mut draft.core, mutation);
            assert!(
                draft
                    .check_flow(
                        &fixture.resolved.resources()[0],
                        &mut TypeWorkBudget::default()
                    )
                    .is_err()
            );
        }
    }

    #[test]
    fn independent_lifecycle_flow_rejects_transplanted_parameter_phase_and_formal_mapping() {
        let fixture = Fixture::new(SOURCE);
        let header = fixture
            .elaborator()
            .check_provider_header(&fixture.resolved, &fixture.resolved.resources()[0])
            .unwrap();
        for mutation in 0..3 {
            let mut draft = fixture
                .elaborator()
                .compile_provider_lifecycle(
                    &fixture.resolved.resources()[0],
                    &header,
                    Phase::Finish,
                )
                .unwrap();
            match mutation {
                0 => draft.parameter = fixture.resolved.resources()[0].acquire_binder.id,
                1 => draft.phase = Phase::Acquire,
                _ => draft.formal_parameters[0].1 = draft.hidden_answer,
            }
            assert!(
                draft
                    .check_flow(
                        &fixture.resolved.resources()[0],
                        &mut TypeWorkBudget::default()
                    )
                    .is_err()
            );
        }
    }

    #[test]
    fn independent_lifecycle_flow_charges_wide_native_fact_catalog() {
        use crate::foreign::{
            ForeignEffectDeclaration, ForeignManifest, ForeignManifestSchema,
            ForeignOperationDeclaration, ForeignResultRelation, ForeignTypeDeclaration,
        };
        const WIDTH: usize = 64;
        let wide = ForeignManifest::new(
            "@foreign.wide",
            ForeignRegistrationId::new(990),
            ForeignManifestSchema {
                foundation: None,
                types: vec![ForeignTypeDeclaration {
                    name: "WideState".into(),
                    parameters: vec!["R".into()],
                    category: crate::foreign::ForeignTypeCategory::State,
                    constructors: vec![],
                }],
                effects: vec![ForeignEffectDeclaration {
                    name: "Wide".into(),
                    parameters: vec!["R".into()],
                    operations: (0..WIDTH)
                        .map(|index| ForeignOperationDeclaration {
                            name: format!("probe{index}"),
                            signature: "WideState<R> -> Int".into(),
                            role: ForeignOperationRole::Borrow,
                            owned_identity_position: 0,
                            state_operands: vec![vec![]],
                            retained_arguments: vec![],
                            result: ForeignResultRelation::Independent,
                        })
                        .collect(),
                }],
                state_access: None,
            },
        )
        .unwrap();
        let narrow = Fixture::new(SOURCE);
        let wide = Fixture::with_registrations(
            &format!("import @foreign.wide as Wide\n{SOURCE}"),
            ForeignRegistrations::new([
                sqlite_manifest(ForeignRegistrationId::new(991)).unwrap(),
                wide,
            ])
            .unwrap(),
        );
        let measure = |fixture: &Fixture| {
            let definition = &fixture.resolved.resources()[0];
            let header = fixture
                .elaborator()
                .check_provider_header(&fixture.resolved, definition)
                .unwrap();
            let draft = fixture
                .elaborator()
                .compile_provider_lifecycle(definition, &header, Phase::Finish)
                .unwrap();
            let mut measured = TypeWorkBudget::with_limit(usize::MAX);
            draft.check_flow(definition, &mut measured).unwrap();
            let exact = measured.used();
            let mut admitted = TypeWorkBudget::with_limit(exact);
            draft.check_flow(definition, &mut admitted).unwrap();
            assert_eq!(admitted.used(), exact);
            let mut short = TypeWorkBudget::with_limit(exact - 1);
            match draft.check_flow(definition, &mut short).unwrap_err() {
                LifecycleDraftCheckError::Resource => {}
                LifecycleDraftCheckError::Core(error) => {
                    assert_eq!(error.reason(), crate::core::ValidationReason::Resource);
                }
                LifecycleDraftCheckError::InvalidEntry => panic!("unexpected invalid entry"),
            }
            exact
        };
        let narrow_work = measure(&narrow);
        let wide_work = measure(&wide);
        assert!(
            wide_work >= narrow_work + WIDTH + 2,
            "native catalog scans were not charged: narrow={narrow_work}, wide={wide_work}"
        );
    }

    #[test]
    fn direct_state_access_draft_uses_the_accessed_resource_association() {
        let fixture = Fixture::with_registrations(
            &format!(
                "import @foreign.provider as Provider\n{SOURCE}\n{}",
                STATEMENT
            ),
            ForeignRegistrations::new([
                sqlite_manifest(ForeignRegistrationId::new(991)).unwrap(),
                crate::foreign::provider_manifest(ForeignRegistrationId::new(992)).unwrap(),
            ])
            .unwrap(),
        );
        let mut checker = fixture.elaborator();
        let connection = &fixture.resolved.resources()[0];
        let statement = &fixture.resolved.resources()[1];
        let connection_header = checker
            .check_provider_header(&fixture.resolved, connection)
            .unwrap();
        let statement_header = checker
            .check_provider_header(&fixture.resolved, statement)
            .unwrap();
        let associations = vec![
            connection_header
                .state_association
                .clone_with_budget(&mut checker.type_work)
                .unwrap(),
        ];
        let draft = fixture
            .elaborator()
            .compile_provider_lifecycle_with_associations(
                statement,
                &statement_header,
                Phase::Acquire,
                associations,
            )
            .unwrap();
        let (ty, effects, access) =
            crate::core::provider::state_access_for_test(&draft.core).unwrap();
        assert_eq!(access.definition(), connection.id);
        assert_eq!(ty.outer_nominal(), connection.state.ty.outer_nominal());
        assert_ne!(ty.outer_nominal(), statement.state.ty.outer_nominal());
        assert_eq!(access.arguments().len(), 1);
        assert!(effects.is_empty());
    }

    const STATEMENT: &str = "pub interface StatementReader<S, C> {\ncolumn : Statement<S, C> -> Native.Result<Int> ! {StatementOps<S, C>}\n}\npub effect StatementOps<S, C> {\ncolumn : Statement<S, C> -> Native.Result<Int>\n}\npub resource Statement<S, C> {\ninput (Connection<C>, Bytes)\nstate Native.StatementState<S, C>\nresult Scope<Native.PrepareError, Native.FinalizeError, T> for <T>\nprovider StatementReader<S, C>\neffect StatementOps<S, C>\ninterpret Native.Statement<S, C>\nacquire config => match config {\n(db, sql) => perform Native.Statement<S, C>.prepare (Provider.state_of db, sql)\n}\nfinish state => perform Native.Statement<S, C>.finalize state\nhandlers state {\ncolumn stmt => resume (perform Native.Statement<S, C>.column_int (state, 0))\n}\n}\n";

    #[test]
    fn direct_state_access_draft_rejects_first_class_callable_and_wrong_operand_paths() {
        for statement in [
            STATEMENT.replace("Provider.state_of db", "{\nlet reveal = Provider.state_of\nreveal db\n}"),
            STATEMENT.replace("Provider.state_of db", "{\nlet reader : Connection<C> -> Int = fn(value) {\nlet ignored = Provider.state_of value\n42\n}\nProvider.state_of db\n}"),
            STATEMENT.replace("Provider.state_of db", "Provider.state_of sql"),
        ] {
            let fixture = Fixture::with_registrations(
                &format!("import @foreign.provider as Provider\n{SOURCE}\n{statement}"),
                ForeignRegistrations::new([
                    sqlite_manifest(ForeignRegistrationId::new(991)).unwrap(),
                    crate::foreign::provider_manifest(ForeignRegistrationId::new(992)).unwrap(),
                ]).unwrap(),
            );
            let mut checker = fixture.elaborator();
            let connection_header = checker.check_provider_header(&fixture.resolved, &fixture.resolved.resources()[0]).unwrap();
            let statement_header = checker.check_provider_header(&fixture.resolved, &fixture.resolved.resources()[1]).unwrap();
            let associations = vec![connection_header.state_association.clone_with_budget(&mut checker.type_work).unwrap()];
            assert!(fixture.elaborator().compile_provider_lifecycle_with_associations(&fixture.resolved.resources()[1], &statement_header, Phase::Acquire, associations).is_err(), "accepted {statement}");
        }
    }

    #[test]
    fn direct_state_access_draft_preserves_targeted_import_identity_and_needs_association() {
        let fixture = Fixture::with_registrations(
            &format!(
                "import @foreign.provider (state_of as reveal)\n{SOURCE}\n{}",
                STATEMENT.replace("Provider.state_of", "reveal")
            ),
            ForeignRegistrations::new([
                sqlite_manifest(ForeignRegistrationId::new(991)).unwrap(),
                crate::foreign::provider_manifest(ForeignRegistrationId::new(992)).unwrap(),
            ])
            .unwrap(),
        );
        let mut checker = fixture.elaborator();
        let connection_header = checker
            .check_provider_header(&fixture.resolved, &fixture.resolved.resources()[0])
            .unwrap();
        let statement = &fixture.resolved.resources()[1];
        let statement_header = checker
            .check_provider_header(&fixture.resolved, statement)
            .unwrap();
        assert!(
            fixture
                .elaborator()
                .compile_provider_lifecycle(statement, &statement_header, Phase::Acquire)
                .is_err()
        );
        let associations = vec![
            connection_header
                .state_association
                .clone_with_budget(&mut checker.type_work)
                .unwrap(),
        ];
        let draft = fixture
            .elaborator()
            .compile_provider_lifecycle_with_associations(
                statement,
                &statement_header,
                Phase::Acquire,
                associations,
            )
            .unwrap();
        let (_, _, access) = crate::core::provider::state_access_for_test(&draft.core).unwrap();
        assert!(checker.is_provider_state_access(access.method()).unwrap());
        assert_eq!(access.definition(), fixture.resolved.resources()[0].id);
    }

    #[test]
    fn independent_lifecycle_flow_long_alias_chain_and_late_failure_drop_on_small_stack() {
        let mut finish = String::from("finish state => {\nlet held0 = state\n");
        for index in 1..256 {
            finish.push_str(&format!("let held{index} = held{}\n", index - 1));
        }
        finish.push_str("perform Native.Connection<R>.close held255\n}");
        let fixture = Fixture::new(&SOURCE.replace(
            "finish state => perform Native.Connection<R>.close state",
            &finish,
        ));
        let header = fixture
            .elaborator()
            .check_provider_header(&fixture.resolved, &fixture.resolved.resources()[0])
            .unwrap();
        let draft = fixture
            .elaborator()
            .compile_provider_lifecycle(&fixture.resolved.resources()[0], &header, Phase::Finish)
            .unwrap();
        let definition = fixture.resolved.resources()[0].clone();
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(move || {
                let mut measured = TypeWorkBudget::with_limit(usize::MAX);
                draft.check_flow(&definition, &mut measured).unwrap();
                let mut short = TypeWorkBudget::with_limit(measured.used() - 1);
                assert!(matches!(
                    draft.check_flow(&definition, &mut short),
                    Err(LifecycleDraftCheckError::Core(error))
                        if error.reason() == crate::core::ValidationReason::Resource
                ));
                drop(draft);
                drop(definition);
            })
            .unwrap()
            .join()
            .unwrap();
    }
}

#[cfg(test)]
mod storage_tests {
    use super::ProviderSubstitutions;
    use crate::types::{Type, TypeVariableId, reset_type_discard_observation, type_discard_visits};

    #[test]
    fn provider_substitution_replacement_and_drop_dispose_exact_owned_trees() {
        const DEPTH: usize = 32_768;
        let mut deep = Type::Unit;
        for _ in 0..DEPTH {
            deep = Type::Application(Box::new(deep), Box::new(Type::Unit));
        }
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(move || {
                let mut types = ProviderSubstitutions::default();
                types.0.try_reserve(1).unwrap();
                let parameter = TypeVariableId::Generated(0);
                types.insert_discarding_replaced(parameter, deep);
                reset_type_discard_observation();
                types.insert_discarding_replaced(parameter, Type::Int);
                assert_eq!(type_discard_visits(), 2 * DEPTH + 1);
                assert_eq!(types.0.len(), 1);
                assert!(matches!(types.0.get(&parameter), Some(Type::Int)));
                drop(types);
                assert_eq!(type_discard_visits(), 2 * DEPTH + 2);
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
