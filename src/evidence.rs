//! Checked interface-evidence selection.

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use crate::{
    interface::{
        CheckedImplementation, ConstrainedScheme, EvidenceNode, EvidenceSelection,
        EvidenceSelectionBuilder, EvidenceSlotHandle, EvidenceSubstitution, HeadMatchFailure,
        ImplId, ImplMethodId, InterfaceConstraintBudget, InterfaceId, InterfaceOperationWork,
        InterfaceReason, MethodId, RequirementId, match_implementation_head_in_environment,
    },
    kind::{
        CanonicalEnvironmentFailure, KindEnvironments, KindFailure,
        canonical_body_free_environments, canonical_type_variable_kind,
    },
    resolved::{
        BinderId, CheckedGlobalScheme, CheckedInterfaceFact, ImportedGlobalScheme,
        ImportedImplementationFact, ResolvedImplementation, ResolvedRegistry, ResolvedTypeVariable,
    },
    source::Span,
    types::{
        IterativeTypeOwner, Kind, NominalTypeId, Type, TypeVariableId, TypeWorkBudget,
        clone_kind_with_budget, clone_type_with_budget, discard_type_iteratively,
        same_kind_with_charge, same_kinded_type_parameters_with_charge,
        substitute_type_variables_with,
    },
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum SelectionFailure {
    Reason(InterfaceReason),
    TypeResource,
    ConstraintResource,
    InvalidState,
}

#[derive(Debug, Eq, PartialEq)]
pub(crate) struct SelectionError {
    failure: SelectionFailure,
    span: Option<Span>,
    declaration_span: Option<Span>,
    import_span: Option<Span>,
    causes: Vec<SelectionCause>,
}

impl SelectionError {
    pub(crate) const fn failure(&self) -> SelectionFailure {
        self.failure
    }

    pub(crate) const fn span(&self) -> Option<Span> {
        self.span
    }

    pub(crate) const fn declaration_span(&self) -> Option<Span> {
        self.declaration_span
    }

    pub(crate) const fn import_span(&self) -> Option<Span> {
        self.import_span
    }

    pub(crate) fn causes(&self) -> &[SelectionCause] {
        &self.causes
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum SelectionCauseKind {
    Interface,
    Implementation,
    ImplementationMethod,
    ImplementationImport,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct SelectionCause {
    kind: SelectionCauseKind,
    span: Span,
}

impl SelectionCause {
    pub(crate) const fn kind(self) -> SelectionCauseKind {
        self.kind
    }

    pub(crate) const fn span(self) -> Span {
        self.span
    }
}

#[derive(Debug)]
struct MethodEntry {
    id: MethodId,
    type_parameters: Box<[(TypeVariableId, Kind)]>,
    value_type: Type,
    span: Span,
}

impl Drop for MethodEntry {
    fn drop(&mut self) {
        discard_type_iteratively(std::mem::replace(&mut self.value_type, Type::Unit));
    }
}

#[derive(Debug)]
struct InterfaceEntry {
    id: InterfaceId,
    parameter: TypeVariableId,
    parameter_kind: Kind,
    methods: Box<[MethodEntry]>,
    method_ids: Box<[MethodId]>,
    span: Span,
}

#[derive(Debug)]
struct SchemeEntry {
    scheme: ConstrainedScheme,
    declaration_span: Span,
}

#[derive(Debug)]
struct RequirementEntry {
    id: RequirementId,
    interface: InterfaceId,
    argument: Type,
}

impl Drop for RequirementEntry {
    fn drop(&mut self) {
        discard_type_iteratively(std::mem::replace(&mut self.argument, Type::Unit));
    }
}

#[derive(Debug)]
struct ImplementationEntry {
    id: ImplId,
    interface: InterfaceId,
    parameters: Box<[TypeVariableId]>,
    argument: Type,
    prerequisites: Box<[RequirementEntry]>,
    methods: Box<[ImplMethodId]>,
    span: Span,
    method_spans: Vec<Span>,
    import_spans: Box<[Span]>,
}

impl Drop for ImplementationEntry {
    fn drop(&mut self) {
        discard_type_iteratively(std::mem::replace(&mut self.argument, Type::Unit));
    }
}

#[derive(Debug)]
struct PendingObligation {
    interface: InterfaceId,
    argument: Type,
    method_arguments: Box<[Type]>,
    method_rigidity: Option<MethodRigidityCondition>,
    slot: EvidenceSlotHandle,
    span: Span,
    declaration_span: Option<Span>,
    import_span: Option<Span>,
}

/// Diagnostic location retained until selection determines whether a same-method
/// occurrence is an exact-current recursive dispatch.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct MethodRigiditySite {
    occurrence_span: Span,
    application_span: Option<Span>,
    argument_span: Option<Span>,
}

impl MethodRigiditySite {
    pub(crate) const fn occurrence(occurrence_span: Span) -> Self {
        Self {
            occurrence_span,
            application_span: None,
            argument_span: None,
        }
    }

    pub(crate) const fn application(
        occurrence_span: Span,
        application_span: Span,
        argument_span: Span,
    ) -> Self {
        Self {
            occurrence_span,
            application_span: Some(application_span),
            argument_span: Some(argument_span),
        }
    }

    pub(crate) const fn occurrence_span(self) -> Span {
        self.occurrence_span
    }

    pub(crate) const fn application_span(self) -> Option<Span> {
        self.application_span
    }

    pub(crate) const fn argument_span(self) -> Option<Span> {
        self.argument_span
    }

    pub(crate) fn matches_failure_span(self, span: Span) -> bool {
        self.application_span == Some(span) || self.argument_span == Some(span)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct MethodRigidityTarget {
    marker: usize,
    failure_span: Span,
}

impl MethodRigidityTarget {
    pub(crate) const fn new(marker: usize, failure_span: Span) -> Self {
        Self {
            marker,
            failure_span,
        }
    }

    #[cfg(test)]
    pub(crate) const fn failure_span(self) -> Span {
        self.failure_span
    }
}

/// Same-method rigid arguments that become relevant only after exact-current
/// evidence wins selection.
#[derive(Debug)]
pub(crate) struct MethodRigidityCondition {
    rigid_arguments: Box<[Type]>,
    site: MethodRigiditySite,
}

#[derive(Debug)]
pub(crate) struct MethodObligationMetadata {
    method_arguments: Box<[Type]>,
    method_rigidity: Option<MethodRigidityCondition>,
}

impl MethodObligationMetadata {
    pub(crate) const fn new(
        method_arguments: Box<[Type]>,
        method_rigidity: Option<MethodRigidityCondition>,
    ) -> Self {
        Self {
            method_arguments,
            method_rigidity,
        }
    }
}

impl MethodRigidityCondition {
    pub(crate) const fn new(rigid_arguments: Box<[Type]>, site: MethodRigiditySite) -> Self {
        Self {
            rigid_arguments,
            site,
        }
    }
}

impl Drop for MethodRigidityCondition {
    fn drop(&mut self) {
        for argument in std::mem::take(&mut self.rigid_arguments).into_vec() {
            discard_type_iteratively(argument);
        }
    }
}

#[derive(Debug)]
struct SelectedMethodRigidity {
    selected_index: usize,
    condition: MethodRigidityCondition,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct MethodRigidityCheck<'a> {
    method_arguments: &'a [Type],
    rigid_arguments: &'a [Type],
    site: MethodRigiditySite,
}

impl<'a> MethodRigidityCheck<'a> {
    #[cfg(test)]
    pub(crate) const fn for_test(
        method_arguments: &'a [Type],
        rigid_arguments: &'a [Type],
        site: MethodRigiditySite,
    ) -> Self {
        Self {
            method_arguments,
            rigid_arguments,
            site,
        }
    }

    pub(crate) const fn method_arguments(self) -> &'a [Type] {
        self.method_arguments
    }

    pub(crate) const fn rigid_arguments(self) -> &'a [Type] {
        self.rigid_arguments
    }

    pub(crate) const fn site(self) -> MethodRigiditySite {
        self.site
    }
}

#[derive(Debug)]
pub(crate) struct SelectionSite {
    slot: EvidenceSlotHandle,
    span: Span,
    declaration_span: Option<Span>,
    import_span: Option<Span>,
}

impl SelectionSite {
    pub(crate) const fn contextual(
        slot: EvidenceSlotHandle,
        span: Span,
        declaration_span: Span,
        import_span: Option<Span>,
    ) -> Self {
        Self {
            slot,
            span,
            declaration_span: Some(declaration_span),
            import_span,
        }
    }

    #[cfg(test)]
    const fn plain(slot: EvidenceSlotHandle, span: Span) -> Self {
        Self {
            slot,
            span,
            declaration_span: None,
            import_span: None,
        }
    }
}

impl Drop for PendingObligation {
    fn drop(&mut self) {
        discard_type_iteratively(std::mem::replace(&mut self.argument, Type::Unit));
        for argument in std::mem::take(&mut self.method_arguments).into_vec() {
            discard_type_iteratively(argument);
        }
    }
}

#[derive(Debug)]
struct SelectedOccurrence {
    checked_argument: Type,
    method_arguments: Box<[Type]>,
    selection: Option<EvidenceSelection>,
    slot: Option<EvidenceSlotHandle>,
}

impl Drop for SelectedOccurrence {
    fn drop(&mut self) {
        discard_type_iteratively(std::mem::replace(&mut self.checked_argument, Type::Unit));
        for argument in std::mem::take(&mut self.method_arguments).into_vec() {
            discard_type_iteratively(argument);
        }
    }
}

/// Fully zonked occurrence facts staged before checked-module publication.
#[derive(Debug)]
pub(crate) struct PendingEvidencePublication {
    occurrences: Vec<SelectedOccurrence>,
    slot_ids: HashSet<usize>,
}

impl PendingEvidencePublication {
    pub(crate) fn contains(&self, slot: &crate::interface::EvidenceSlot) -> bool {
        self.slot_ids.contains(&slot.storage_id())
    }

    fn preflight(&mut self) -> Result<(), SelectionFailure> {
        if self.occurrences.len() != self.slot_ids.len() {
            return Err(SelectionFailure::InvalidState);
        }
        for occurrence in &self.occurrences {
            let slot = occurrence
                .slot
                .as_ref()
                .ok_or(SelectionFailure::InvalidState)?;
            let slot_id = slot.storage_id();
            if occurrence.selection.is_none() || !slot.is_empty() || !self.slot_ids.remove(&slot_id)
            {
                return Err(SelectionFailure::InvalidState);
            }
        }
        if self.slot_ids.is_empty() {
            Ok(())
        } else {
            Err(SelectionFailure::InvalidState)
        }
    }

    pub(crate) fn publish(mut self) -> Result<(), SelectionFailure> {
        self.preflight()?;
        while let Some(mut occurrence) = self.occurrences.pop() {
            let checked_argument = std::mem::replace(&mut occurrence.checked_argument, Type::Unit);
            let method_arguments = std::mem::take(&mut occurrence.method_arguments);
            let selection = occurrence
                .selection
                .take()
                .expect("publication preflight authenticates every selection");
            occurrence
                .slot
                .take()
                .expect("publication preflight authenticates every slot")
                .fill_preflighted(checked_argument, method_arguments, selection);
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct SelectionMethod<'a> {
    interface: InterfaceId,
    interface_parameter: TypeVariableId,
    interface_parameter_kind: &'a Kind,
    type_parameters: &'a [(TypeVariableId, Kind)],
    value_type: &'a Type,
    declaration_span: Span,
}

impl<'a> SelectionMethod<'a> {
    pub(crate) const fn interface(self) -> InterfaceId {
        self.interface
    }

    pub(crate) const fn interface_parameter(self) -> TypeVariableId {
        self.interface_parameter
    }

    pub(crate) const fn interface_parameter_kind(self) -> &'a Kind {
        self.interface_parameter_kind
    }

    pub(crate) const fn value_type(self) -> &'a Type {
        self.value_type
    }

    pub(crate) const fn type_parameters(self) -> &'a [(TypeVariableId, Kind)] {
        self.type_parameters
    }

    pub(crate) const fn declaration_span(self) -> Span {
        self.declaration_span
    }
}

/// The owned fact registry, dynamic evidence scope, and pending slot queue.
#[derive(Debug, Default)]
pub(crate) struct EvidenceSelector {
    interfaces: Vec<InterfaceEntry>,
    interface_indices: HashMap<InterfaceId, usize>,
    method_indices: HashMap<MethodId, (usize, usize)>,
    schemes: Vec<SchemeEntry>,
    scheme_indices: HashMap<BinderId, usize>,
    implementations: Vec<ImplementationEntry>,
    implementation_indices: HashMap<ImplId, usize>,
    implementation_candidates: HashMap<InterfaceId, Vec<usize>>,
    abstracts: Vec<RequirementEntry>,
    current: Option<ImplId>,
    pending: Vec<PendingObligation>,
    pending_method_rigidity_count: usize,
    selected: Vec<SelectedOccurrence>,
    method_rigidities: Vec<SelectedMethodRigidity>,
}

struct ImplementationCandidateAuthentication<'a, P> {
    parameter_records: &'a [ResolvedTypeVariable],
    interface: InterfaceId,
    argument: &'a Type,
    prerequisites: P,
    span: Span,
}

impl EvidenceSelector {
    pub(crate) fn new() -> Self {
        Self {
            interfaces: Vec::new(),
            interface_indices: HashMap::new(),
            method_indices: HashMap::new(),
            schemes: Vec::new(),
            scheme_indices: HashMap::new(),
            implementations: Vec::new(),
            implementation_indices: HashMap::new(),
            implementation_candidates: HashMap::new(),
            abstracts: Vec::new(),
            current: None,
            pending: Vec::new(),
            pending_method_rigidity_count: 0,
            selected: Vec::new(),
            method_rigidities: Vec::new(),
        }
    }

    pub(crate) fn add_interface_fact(
        &mut self,
        registry: &ResolvedRegistry,
        fact: &CheckedInterfaceFact,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(), SelectionFailure> {
        self.add_interface_fact_parts(registry, fact, constraint_work, type_work)
    }

    pub(crate) fn add_imported_interface_fact(
        &mut self,
        registry: &ResolvedRegistry,
        fact: &CheckedInterfaceFact,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(), SelectionFailure> {
        self.add_interface_fact_parts(registry, fact, constraint_work, type_work)
    }

    fn add_interface_fact_parts(
        &mut self,
        registry: &ResolvedRegistry,
        fact: &CheckedInterfaceFact,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(), SelectionFailure> {
        let canonical =
            canonical_type_variable_kind(registry, fact.parameter.id, fact.span, constraint_work)
                .map_err(map_ingress_kind_failure)?;
        let equal = same_kind_with_charge(canonical, &fact.parameter.kind, || {
            constraint_work.charge(1)
        })
        .map_err(|()| SelectionFailure::ConstraintResource)?;
        if !equal {
            return Err(SelectionFailure::InvalidState);
        }
        let ingress_records = fact
            .methods
            .len()
            .checked_add(1)
            .ok_or(SelectionFailure::ConstraintResource)?;
        constraint_work
            .charge(ingress_records)
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        if self.interface_indices.contains_key(&fact.id) {
            return Err(SelectionFailure::InvalidState);
        }
        let mut incoming_methods = HashSet::new();
        incoming_methods
            .try_reserve(fact.methods.len())
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        for method in &fact.methods {
            if self.method_indices.contains_key(&method.id) || !incoming_methods.insert(method.id) {
                return Err(SelectionFailure::InvalidState);
            }
        }
        type_work
            .charge(1)
            .map_err(|()| SelectionFailure::TypeResource)?;
        let parameter_kind = clone_kind_with_budget(canonical, type_work)
            .map_err(|()| SelectionFailure::TypeResource)?;
        let mut methods = Vec::new();
        let mut method_ids = Vec::new();
        methods
            .try_reserve(fact.methods.len())
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        method_ids
            .try_reserve(fact.methods.len())
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        for method in &fact.methods {
            constraint_work
                .charge_type(&method.value_type)
                .map_err(|()| SelectionFailure::ConstraintResource)?;
            constraint_work
                .charge(method.type_parameters.len())
                .map_err(|()| SelectionFailure::ConstraintResource)?;
            type_work
                .charge(method.type_parameters.len())
                .map_err(|()| SelectionFailure::TypeResource)?;
            let mut type_parameters = Vec::new();
            let mut seen = HashSet::new();
            type_parameters
                .try_reserve(method.type_parameters.len())
                .map_err(|_| SelectionFailure::ConstraintResource)?;
            seen.try_reserve(method.type_parameters.len())
                .map_err(|_| SelectionFailure::ConstraintResource)?;
            for parameter in method.type_parameters() {
                if parameter.id == fact.parameter.id || !seen.insert(parameter.id) {
                    return Err(SelectionFailure::InvalidState);
                }
                let canonical = canonical_type_variable_kind(
                    registry,
                    parameter.id,
                    method.span,
                    constraint_work,
                )
                .map_err(map_ingress_kind_failure)?;
                if !same_kind_with_charge(canonical, &parameter.kind, || constraint_work.charge(1))
                    .map_err(|()| SelectionFailure::ConstraintResource)?
                {
                    return Err(SelectionFailure::InvalidState);
                }
                type_parameters.push((
                    parameter.id,
                    clone_kind_with_budget(canonical, type_work)
                        .map_err(|()| SelectionFailure::TypeResource)?,
                ));
            }
            methods.push(MethodEntry {
                id: method.id,
                type_parameters: type_parameters.into_boxed_slice(),
                value_type: clone_type_with_budget(&method.value_type, type_work)
                    .map_err(|()| SelectionFailure::TypeResource)?,
                span: method.span,
            });
            method_ids.push(method.id);
        }
        self.interfaces
            .try_reserve(1)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        self.interface_indices
            .try_reserve(1)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        self.method_indices
            .try_reserve(fact.methods.len())
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        let interface_index = self.interfaces.len();
        for (method_index, method) in methods.iter().enumerate() {
            let _ = self
                .method_indices
                .insert(method.id, (interface_index, method_index));
        }
        let _ = self.interface_indices.insert(fact.id, interface_index);
        self.interfaces.push(InterfaceEntry {
            id: fact.id,
            parameter: fact.parameter.id,
            parameter_kind,
            methods: methods.into_boxed_slice(),
            method_ids: method_ids.into_boxed_slice(),
            span: fact.span,
        });
        Ok(())
    }

    pub(crate) fn add_scheme(
        &mut self,
        fact: &CheckedGlobalScheme,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(), SelectionFailure> {
        self.add_scheme_parts(
            fact.binder,
            &fact.scheme,
            fact.origin.primary_span(),
            constraint_work,
            type_work,
        )
    }

    pub(crate) fn add_imported_scheme(
        &mut self,
        fact: &ImportedGlobalScheme,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(), SelectionFailure> {
        self.add_scheme_parts(
            fact.binder,
            &fact.scheme,
            fact.origin.primary_span(),
            constraint_work,
            type_work,
        )
    }

    fn add_scheme_parts(
        &mut self,
        binder: BinderId,
        scheme: &ConstrainedScheme,
        declaration_span: Span,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(), SelectionFailure> {
        if self.scheme_indices.contains_key(&binder) {
            return Err(SelectionFailure::InvalidState);
        }
        constraint_work
            .charge(
                scheme
                    .type_parameters
                    .len()
                    .saturating_add(scheme.requirements.len())
                    .saturating_add(1),
            )
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        constraint_work
            .charge_type(&scheme.value_type)
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        for requirement in &scheme.requirements {
            constraint_work
                .charge_type(&requirement.argument)
                .map_err(|()| SelectionFailure::ConstraintResource)?;
        }
        let scheme = scheme
            .clone_with_budget(type_work)
            .map_err(|()| SelectionFailure::TypeResource)?;
        self.schemes
            .try_reserve(1)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        self.scheme_indices
            .try_reserve(1)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        let scheme_index = self.schemes.len();
        if self.scheme_indices.insert(binder, scheme_index).is_some() {
            return Err(SelectionFailure::InvalidState);
        }
        self.schemes.push(SchemeEntry {
            scheme,
            declaration_span,
        });
        Ok(())
    }

    pub(crate) fn add_implementation_fact(
        &mut self,
        registry: &ResolvedRegistry,
        imported: &ImportedImplementationFact,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(), SelectionFailure> {
        let fact = &imported.fact;
        if self.implementation_indices.contains_key(&fact.id) {
            return Err(SelectionFailure::InvalidState);
        }
        let parameters = self.authenticate_implementation_candidate(
            registry,
            ImplementationCandidateAuthentication {
                parameter_records: &fact.head_parameters,
                interface: fact.interface,
                argument: &fact.argument,
                prerequisites: fact
                    .prerequisites
                    .iter()
                    .map(|prerequisite| (prerequisite.interface, &prerequisite.argument)),
                span: fact.span,
            },
            constraint_work,
        )?;
        constraint_work
            .charge(
                fact.head_parameters
                    .len()
                    .saturating_add(fact.prerequisites.len())
                    .saturating_add(fact.methods.len().saturating_mul(2))
                    .saturating_add(imported.authorization().hops().len())
                    .saturating_add(1),
            )
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        constraint_work
            .charge_type(&fact.argument)
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        let mut prerequisites = Vec::new();
        let mut methods = Vec::new();
        let mut method_spans = Vec::new();
        let mut import_spans = Vec::new();
        prerequisites
            .try_reserve(fact.prerequisites.len())
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        methods
            .try_reserve(fact.methods.len())
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        method_spans
            .try_reserve(fact.methods.len())
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        import_spans
            .try_reserve_exact(imported.authorization().hops().len())
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        let staged_candidate_bucket = self.reserve_implementation_publication(fact.interface)?;
        for prerequisite in &fact.prerequisites {
            constraint_work
                .charge_type(&prerequisite.argument)
                .map_err(|()| SelectionFailure::ConstraintResource)?;
            prerequisites.push(RequirementEntry {
                id: prerequisite.id,
                interface: prerequisite.interface,
                argument: clone_type_with_budget(&prerequisite.argument, type_work)
                    .map_err(|()| SelectionFailure::TypeResource)?,
            });
        }
        methods.extend(fact.methods.iter().map(|method| method.id));
        method_spans.extend(fact.methods.iter().map(|method| method.span));
        import_spans.extend(
            imported
                .authorization()
                .hops()
                .iter()
                .map(|hop| hop.import_span),
        );
        let argument = IterativeTypeOwner::new(
            clone_type_with_budget(&fact.argument, type_work)
                .map_err(|()| SelectionFailure::TypeResource)?,
        );
        let entry = ImplementationEntry {
            id: fact.id,
            interface: fact.interface,
            parameters: parameters.into_boxed_slice(),
            argument: argument.into_inner(),
            prerequisites: prerequisites.into_boxed_slice(),
            methods: methods.into_boxed_slice(),
            span: fact.span,
            method_spans,
            import_spans: import_spans.into_boxed_slice(),
        };
        self.publish_implementation(entry, staged_candidate_bucket)?;
        Ok(())
    }

    pub(crate) fn add_local_implementation(
        &mut self,
        registry: &ResolvedRegistry,
        resolved: &ResolvedImplementation,
        checked: &CheckedImplementation,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(), SelectionFailure> {
        if resolved.id != checked.id
            || resolved.interface.id != checked.interface
            || !resolved.prerequisite_only_parameters.is_empty()
            || checked.methods.len() != resolved.method_groups.len()
        {
            return Err(SelectionFailure::InvalidState);
        }
        if self.implementation_indices.contains_key(&checked.id) {
            return Err(SelectionFailure::InvalidState);
        }
        let parameters = self.authenticate_implementation_candidate(
            registry,
            ImplementationCandidateAuthentication {
                parameter_records: &resolved.head_parameters,
                interface: resolved.interface.id,
                argument: &resolved.argument.ty,
                prerequisites: resolved
                    .prerequisites
                    .iter()
                    .map(|prerequisite| (prerequisite.interface.id, &prerequisite.argument.ty)),
                span: resolved.span,
            },
            constraint_work,
        )?;
        constraint_work
            .charge(
                resolved
                    .head_parameters
                    .len()
                    .saturating_add(resolved.prerequisites.len())
                    .saturating_add(checked.methods.len().saturating_mul(2))
                    .saturating_add(1),
            )
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        let mut method_spans = Vec::new();
        method_spans
            .try_reserve(checked.methods.len())
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        for method in &checked.methods {
            let source = resolved
                .method_groups
                .get(method.source_group)
                .ok_or(SelectionFailure::InvalidState)?;
            if source.identity != Some(method.id)
                || source.method != Some(method.method)
                || source.binder.id != method.binder
                || method.id.implementation() != checked.id
                || method.id.method() != method.method
            {
                return Err(SelectionFailure::InvalidState);
            }
            method_spans.push(source.span);
        }
        constraint_work
            .charge_type(&resolved.argument.ty)
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        let mut prerequisites = Vec::new();
        let mut methods = Vec::new();
        prerequisites
            .try_reserve(resolved.prerequisites.len())
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        methods
            .try_reserve(checked.methods.len())
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        let staged_candidate_bucket = self.reserve_implementation_publication(checked.interface)?;
        for prerequisite in &resolved.prerequisites {
            constraint_work
                .charge_type(&prerequisite.argument.ty)
                .map_err(|()| SelectionFailure::ConstraintResource)?;
            prerequisites.push(RequirementEntry {
                id: prerequisite.id,
                interface: prerequisite.interface.id,
                argument: clone_type_with_budget(&prerequisite.argument.ty, type_work)
                    .map_err(|()| SelectionFailure::TypeResource)?,
            });
        }
        methods.extend(checked.methods.iter().map(|method| method.id));
        let argument = IterativeTypeOwner::new(
            clone_type_with_budget(&resolved.argument.ty, type_work)
                .map_err(|()| SelectionFailure::TypeResource)?,
        );
        let entry = ImplementationEntry {
            id: checked.id,
            interface: checked.interface,
            parameters: parameters.into_boxed_slice(),
            argument: argument.into_inner(),
            prerequisites: prerequisites.into_boxed_slice(),
            methods: methods.into_boxed_slice(),
            span: resolved.span,
            method_spans,
            import_spans: Box::new([]),
        };
        self.publish_implementation(entry, staged_candidate_bucket)?;
        Ok(())
    }

    /// Reserves every selector destination before retained implementation Types
    /// are cloned. A new candidate bucket stays local until publication.
    fn reserve_implementation_publication(
        &mut self,
        interface: InterfaceId,
    ) -> Result<Option<Vec<usize>>, SelectionFailure> {
        self.implementations
            .try_reserve(1)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        self.implementation_indices
            .try_reserve(1)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        if let Some(candidates) = self.implementation_candidates.get_mut(&interface) {
            candidates
                .try_reserve(1)
                .map_err(|_| SelectionFailure::ConstraintResource)?;
            return Ok(None);
        }
        self.implementation_candidates
            .try_reserve(1)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        let mut candidates = Vec::new();
        candidates
            .try_reserve(1)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        Ok(Some(candidates))
    }

    /// Publishes a fully authenticated and retained implementation without any
    /// remaining fallible allocation or validation.
    fn publish_implementation(
        &mut self,
        entry: ImplementationEntry,
        staged_candidate_bucket: Option<Vec<usize>>,
    ) -> Result<(), SelectionFailure> {
        let implementation_index = self.implementations.len();
        let interface = entry.interface;
        let implementation = entry.id;
        if self.implementation_indices.contains_key(&implementation) {
            return Err(SelectionFailure::InvalidState);
        }
        if staged_candidate_bucket.is_some()
            == self.implementation_candidates.contains_key(&interface)
        {
            return Err(SelectionFailure::InvalidState);
        }
        if staged_candidate_bucket.is_none() {
            self.implementation_candidates
                .get_mut(&interface)
                .ok_or(SelectionFailure::InvalidState)?
                .push(implementation_index);
        }
        self.implementations.push(entry);
        let displaced = self
            .implementation_indices
            .insert(implementation, implementation_index);
        debug_assert!(displaced.is_none());
        if let Some(mut candidates) = staged_candidate_bucket {
            candidates.push(implementation_index);
            let displaced = self.implementation_candidates.insert(interface, candidates);
            debug_assert!(displaced.is_none());
        }
        Ok(())
    }

    pub(crate) fn method(&self, id: MethodId) -> Option<SelectionMethod<'_>> {
        let (interface_index, method_index) = *self.method_indices.get(&id)?;
        let interface = self.interfaces.get(interface_index)?;
        let method = interface.methods.get(method_index)?;
        Some(SelectionMethod {
            interface: interface.id,
            interface_parameter: interface.parameter,
            interface_parameter_kind: &interface.parameter_kind,
            type_parameters: &method.type_parameters,
            value_type: &method.value_type,
            declaration_span: method.span,
        })
    }

    pub(crate) fn scheme(&self, binder: BinderId) -> Option<&ConstrainedScheme> {
        let index = *self.scheme_indices.get(&binder)?;
        self.schemes.get(index).map(|entry| &entry.scheme)
    }

    pub(crate) fn scheme_declaration_span(&self, binder: BinderId) -> Option<Span> {
        let index = *self.scheme_indices.get(&binder)?;
        let entry = self.schemes.get(index)?;
        Some(entry.declaration_span)
    }

    pub(crate) fn clear_scope(&mut self) {
        self.abstracts.clear();
        self.current = None;
    }

    pub(crate) fn method_rigidity_count(&self) -> usize {
        self.method_rigidities.len()
    }

    pub(crate) fn method_rigidity(&self, index: usize) -> Option<MethodRigidityCheck<'_>> {
        let selected = self.method_rigidities.get(index)?;
        let occurrence = self.selected.get(selected.selected_index)?;
        Some(MethodRigidityCheck {
            method_arguments: &occurrence.method_arguments,
            rigid_arguments: &selected.condition.rigid_arguments,
            site: selected.condition.site,
        })
    }

    pub(crate) fn clear_method_rigidities(&mut self) {
        self.method_rigidities.clear();
    }

    pub(crate) fn enter_global_scope(
        &mut self,
        binder: BinderId,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(), SelectionFailure> {
        let scheme = self.scheme(binder).ok_or(SelectionFailure::InvalidState)?;
        let mut abstracts = Vec::new();
        constraint_work
            .charge(scheme.requirements.len())
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        abstracts
            .try_reserve(scheme.requirements.len())
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        for requirement in &scheme.requirements {
            constraint_work
                .charge(1)
                .and_then(|()| constraint_work.charge_type(&requirement.argument))
                .map_err(|()| SelectionFailure::ConstraintResource)?;
            abstracts.push(RequirementEntry {
                id: requirement.id,
                interface: requirement.interface,
                argument: clone_type_with_budget(&requirement.argument, type_work)
                    .map_err(|()| SelectionFailure::TypeResource)?,
            });
        }
        self.abstracts = abstracts;
        self.current = None;
        Ok(())
    }

    pub(crate) fn enter_implementation_scope(
        &mut self,
        implementation: ImplId,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(), SelectionFailure> {
        let implementation_index = *self
            .implementation_indices
            .get(&implementation)
            .ok_or(SelectionFailure::InvalidState)?;
        let implementation = self
            .implementations
            .get(implementation_index)
            .ok_or(SelectionFailure::InvalidState)?;
        let mut abstracts = Vec::new();
        constraint_work
            .charge(implementation.prerequisites.len())
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        abstracts
            .try_reserve(implementation.prerequisites.len())
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        for prerequisite in &implementation.prerequisites {
            constraint_work
                .charge(1)
                .and_then(|()| constraint_work.charge_type(&prerequisite.argument))
                .map_err(|()| SelectionFailure::ConstraintResource)?;
            abstracts.push(RequirementEntry {
                id: prerequisite.id,
                interface: prerequisite.interface,
                argument: clone_type_with_budget(&prerequisite.argument, type_work)
                    .map_err(|()| SelectionFailure::TypeResource)?,
            });
        }
        self.abstracts = abstracts;
        self.current = Some(implementation.id);
        Ok(())
    }

    #[cfg(test)]
    pub(crate) fn push_abstract(
        &mut self,
        id: RequirementId,
        interface: InterfaceId,
        argument: Type,
        constraint_work: &mut InterfaceConstraintBudget,
    ) -> Result<(), SelectionFailure> {
        let argument = IterativeTypeOwner::new(argument);
        constraint_work
            .charge(1)
            .and_then(|()| constraint_work.charge_type(&argument))
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        self.abstracts
            .try_reserve(1)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        self.abstracts.push(RequirementEntry {
            id,
            interface,
            argument: argument.into_inner(),
        });
        Ok(())
    }

    pub(crate) const fn pending_marker(&self) -> usize {
        self.pending.len()
    }

    #[cfg(test)]
    pub(crate) fn push_obligation(
        &mut self,
        interface: InterfaceId,
        argument: Type,
        slot: EvidenceSlotHandle,
        span: Span,
        constraint_work: &mut InterfaceConstraintBudget,
    ) -> Result<(), SelectionFailure> {
        self.push_owned_obligation(
            interface,
            argument,
            SelectionSite::plain(slot, span),
            constraint_work,
        )
    }

    pub(crate) fn push_owned_obligation(
        &mut self,
        interface: InterfaceId,
        argument: Type,
        site: SelectionSite,
        constraint_work: &mut InterfaceConstraintBudget,
    ) -> Result<(), SelectionFailure> {
        let argument = IterativeTypeOwner::new(argument);
        constraint_work
            .charge(1)
            .and_then(|()| constraint_work.charge_type(&argument))
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        self.pending
            .try_reserve(1)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        self.pending.push(PendingObligation {
            interface,
            argument: argument.into_inner(),
            method_arguments: Box::new([]),
            method_rigidity: None,
            slot: site.slot,
            span: site.span,
            declaration_span: site.declaration_span,
            import_span: site.import_span,
        });
        Ok(())
    }

    pub(crate) fn push_cloned_obligation(
        &mut self,
        interface: InterfaceId,
        argument: &Type,
        metadata: MethodObligationMetadata,
        site: SelectionSite,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(), SelectionFailure> {
        let MethodObligationMetadata {
            method_arguments,
            method_rigidity,
        } = metadata;
        if method_rigidity
            .as_ref()
            .is_some_and(|rigidity| rigidity.rigid_arguments.len() != method_arguments.len())
        {
            return Err(SelectionFailure::InvalidState);
        }
        let pending_method_rigidity_count = if method_rigidity.is_some() {
            self.pending_method_rigidity_count
                .checked_add(1)
                .ok_or(SelectionFailure::ConstraintResource)?
        } else {
            self.pending_method_rigidity_count
        };
        let rigidity_work = match &method_rigidity {
            Some(rigidity) => rigidity
                .rigid_arguments
                .len()
                .checked_add(1)
                .ok_or(SelectionFailure::ConstraintResource)?,
            None => 0,
        };
        let retained_work = method_arguments
            .len()
            .checked_add(1)
            .and_then(|work| work.checked_add(rigidity_work))
            .ok_or(SelectionFailure::ConstraintResource)?;
        constraint_work
            .charge(retained_work)
            .and_then(|()| constraint_work.charge_type(argument))
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        for method_argument in &method_arguments {
            constraint_work
                .charge_type(method_argument)
                .map_err(|()| SelectionFailure::ConstraintResource)?;
        }
        let argument = IterativeTypeOwner::new(
            clone_type_with_budget(argument, type_work)
                .map_err(|()| SelectionFailure::TypeResource)?,
        );
        self.pending
            .try_reserve(1)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        self.pending.push(PendingObligation {
            interface,
            argument: argument.into_inner(),
            method_arguments,
            method_rigidity,
            slot: site.slot,
            span: site.span,
            declaration_span: site.declaration_span,
            import_span: site.import_span,
        });
        self.pending_method_rigidity_count = pending_method_rigidity_count;
        Ok(())
    }

    pub(crate) fn close_with_registry<F>(
        &mut self,
        registry: &ResolvedRegistry,
        marker: usize,
        zonk: F,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(), SelectionError>
    where
        F: FnMut(Type, &mut TypeWorkBudget) -> Result<Type, SelectionFailure>,
    {
        self.close_with_authority(registry, marker, zonk, constraint_work, type_work)
    }

    pub(crate) fn close_method_rigidity_with_registry<F>(
        &mut self,
        registry: &ResolvedRegistry,
        target: MethodRigidityTarget,
        mut zonk: F,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<bool, SelectionError>
    where
        F: FnMut(Type, &mut TypeWorkBudget) -> Result<Type, SelectionFailure>,
    {
        let invalid = || SelectionError {
            failure: SelectionFailure::InvalidState,
            span: None,
            declaration_span: None,
            import_span: None,
            causes: Vec::new(),
        };
        if target.marker > self.pending.len() || !self.method_rigidities.is_empty() {
            return Err(invalid());
        }
        if self.pending_method_rigidity_count == 0 {
            return Ok(false);
        }
        let pending_count = self.pending.len() - target.marker;
        constraint_work
            .charge(pending_count)
            .map_err(|()| SelectionError {
                failure: SelectionFailure::ConstraintResource,
                span: None,
                declaration_span: None,
                import_span: None,
                causes: Vec::new(),
            })?;
        let mut matching_index = None;
        for (offset, obligation) in self.pending[target.marker..].iter().enumerate() {
            if obligation
                .method_rigidity
                .as_ref()
                .is_some_and(|condition| condition.site.matches_failure_span(target.failure_span))
            {
                if matching_index.is_some() {
                    return Err(invalid());
                }
                matching_index = Some(target.marker + offset);
            }
        }
        let Some(matching_index) = matching_index else {
            return Ok(false);
        };
        let obligation = self.pending.get(matching_index).ok_or_else(invalid)?;
        let condition = obligation.method_rigidity.as_ref().ok_or_else(invalid)?;
        if condition.rigid_arguments.len() != obligation.method_arguments.len() {
            return Err(invalid());
        }
        let shifted_records = self
            .pending
            .len()
            .checked_sub(matching_index)
            .and_then(|count| count.checked_sub(1))
            .ok_or_else(invalid)?;
        let retained_work = shifted_records.checked_add(2).ok_or(SelectionError {
            failure: SelectionFailure::ConstraintResource,
            span: None,
            declaration_span: None,
            import_span: None,
            causes: Vec::new(),
        })?;
        constraint_work
            .charge(retained_work)
            .map_err(|()| SelectionError {
                failure: SelectionFailure::ConstraintResource,
                span: None,
                declaration_span: None,
                import_span: None,
                causes: Vec::new(),
            })?;
        self.selected.try_reserve(1).map_err(|_| SelectionError {
            failure: SelectionFailure::ConstraintResource,
            span: None,
            declaration_span: None,
            import_span: None,
            causes: Vec::new(),
        })?;
        self.method_rigidities
            .try_reserve(1)
            .map_err(|_| SelectionError {
                failure: SelectionFailure::ConstraintResource,
                span: None,
                declaration_span: None,
                import_span: None,
                causes: Vec::new(),
            })?;
        let interface = obligation.interface;
        let span = obligation.span;
        let declaration_span = obligation.declaration_span;
        let import_span = obligation.import_span;
        let argument = clone_type_with_budget(&obligation.argument, type_work).map_err(|()| {
            SelectionError {
                failure: SelectionFailure::TypeResource,
                span: Some(span),
                declaration_span,
                import_span,
                causes: Vec::new(),
            }
        })?;
        let argument = zonk(argument, type_work).map_err(|failure| SelectionError {
            failure,
            span: Some(span),
            declaration_span,
            import_span,
            causes: Vec::new(),
        })?;
        let mut causes = Vec::new();
        let (checked_argument, selection) = match self.select_owned(
            registry,
            interface,
            argument,
            &mut causes,
            constraint_work,
            type_work,
        ) {
            Ok(selection) => selection,
            Err(failure) => {
                let causes = if matches!(failure, SelectionFailure::Reason(_)) {
                    causes
                } else {
                    Vec::new()
                };
                return Err(SelectionError {
                    failure,
                    span: Some(span),
                    declaration_span,
                    import_span,
                    causes,
                });
            }
        };
        let selected_index = self.selected.len();
        let exact_current = self.current.is_some_and(|current| {
            matches!(
                selection.node(selection.root()),
                Some(EvidenceNode::Implementation { implementation, .. })
                    if implementation == current
            )
        });
        let pending_method_rigidity_count = self
            .pending_method_rigidity_count
            .checked_sub(1)
            .ok_or_else(invalid)?;
        let selected_condition = if exact_current {
            Some(
                self.pending
                    .get_mut(matching_index)
                    .and_then(|obligation| obligation.method_rigidity.take())
                    .ok_or_else(invalid)?,
            )
        } else {
            None
        };
        let mut obligation = self.pending.remove(matching_index);
        self.pending_method_rigidity_count = pending_method_rigidity_count;
        if let Some(condition) = selected_condition {
            self.method_rigidities.push(SelectedMethodRigidity {
                selected_index,
                condition,
            });
        }
        self.selected.push(SelectedOccurrence {
            checked_argument,
            method_arguments: std::mem::take(&mut obligation.method_arguments),
            selection: Some(selection),
            slot: Some(obligation.slot.clone()),
        });
        Ok(true)
    }

    #[cfg(test)]
    pub(crate) fn close<F>(
        &mut self,
        marker: usize,
        mut zonk: F,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(), SelectionError>
    where
        F: FnMut(Type, &mut TypeWorkBudget) -> Result<Type, SelectionFailure>,
    {
        let registry = self.canonical_registry_for_test();
        self.close_with_authority(&registry, marker, &mut zonk, constraint_work, type_work)?;
        let publication = self
            .prepare_publication(&mut zonk, constraint_work, type_work)
            .map_err(|failure| SelectionError {
                failure,
                span: None,
                declaration_span: None,
                import_span: None,
                causes: Vec::new(),
            })?;
        publication.publish().map_err(|failure| SelectionError {
            failure,
            span: None,
            declaration_span: None,
            import_span: None,
            causes: Vec::new(),
        })
    }

    fn close_with_authority<F>(
        &mut self,
        registry: &ResolvedRegistry,
        marker: usize,
        mut zonk: F,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(), SelectionError>
    where
        F: FnMut(Type, &mut TypeWorkBudget) -> Result<Type, SelectionFailure>,
    {
        if marker > self.pending.len() {
            return Err(SelectionError {
                failure: SelectionFailure::InvalidState,
                span: None,
                declaration_span: None,
                import_span: None,
                causes: Vec::new(),
            });
        }
        if !self.method_rigidities.is_empty() {
            return Err(SelectionError {
                failure: SelectionFailure::InvalidState,
                span: None,
                declaration_span: None,
                import_span: None,
                causes: Vec::new(),
            });
        }
        let conditional_count = self.pending[marker..]
            .iter()
            .filter(|obligation| obligation.method_rigidity.is_some())
            .count();
        constraint_work
            .charge(
                (self.pending.len() - marker)
                    .checked_add(conditional_count)
                    .ok_or(SelectionError {
                        failure: SelectionFailure::ConstraintResource,
                        span: None,
                        declaration_span: None,
                        import_span: None,
                        causes: Vec::new(),
                    })?,
            )
            .map_err(|()| SelectionError {
                failure: SelectionFailure::ConstraintResource,
                span: None,
                declaration_span: None,
                import_span: None,
                causes: Vec::new(),
            })?;
        self.method_rigidities
            .try_reserve(conditional_count)
            .map_err(|_| SelectionError {
                failure: SelectionFailure::ConstraintResource,
                span: None,
                declaration_span: None,
                import_span: None,
                causes: Vec::new(),
            })?;
        self.pending[marker..].reverse();
        while self.pending.len() > marker {
            let mut obligation = self.pending.pop().ok_or(SelectionError {
                failure: SelectionFailure::InvalidState,
                span: None,
                declaration_span: None,
                import_span: None,
                causes: Vec::new(),
            })?;
            if obligation.method_rigidity.is_some() {
                self.pending_method_rigidity_count = self
                    .pending_method_rigidity_count
                    .checked_sub(1)
                    .ok_or(SelectionError {
                        failure: SelectionFailure::InvalidState,
                        span: Some(obligation.span),
                        declaration_span: obligation.declaration_span,
                        import_span: obligation.import_span,
                        causes: Vec::new(),
                    })?;
            }
            let argument = std::mem::replace(&mut obligation.argument, Type::Unit);
            let argument = zonk(argument, type_work).map_err(|failure| SelectionError {
                failure,
                span: Some(obligation.span),
                declaration_span: obligation.declaration_span,
                import_span: obligation.import_span,
                causes: Vec::new(),
            })?;
            let mut causes = Vec::new();
            let (checked_argument, selection) = match self.select_owned(
                registry,
                obligation.interface,
                argument,
                &mut causes,
                constraint_work,
                type_work,
            ) {
                Ok(selection) => selection,
                Err(failure) => {
                    let causes = if matches!(failure, SelectionFailure::Reason(_)) {
                        causes
                    } else {
                        Vec::new()
                    };
                    return Err(SelectionError {
                        failure,
                        span: Some(obligation.span),
                        declaration_span: obligation.declaration_span,
                        import_span: obligation.import_span,
                        causes,
                    });
                }
            };
            self.selected.try_reserve(1).map_err(|_| SelectionError {
                failure: SelectionFailure::ConstraintResource,
                span: Some(obligation.span),
                declaration_span: obligation.declaration_span,
                import_span: obligation.import_span,
                causes: Vec::new(),
            })?;
            let selected_index = self.selected.len();
            let exact_current = self.current.is_some_and(|current| {
                matches!(
                    selection.node(selection.root()),
                    Some(EvidenceNode::Implementation { implementation, .. })
                        if implementation == current
                )
            });
            if exact_current && let Some(condition) = obligation.method_rigidity.take() {
                if condition.rigid_arguments.len() != obligation.method_arguments.len() {
                    return Err(SelectionError {
                        failure: SelectionFailure::InvalidState,
                        span: Some(obligation.span),
                        declaration_span: obligation.declaration_span,
                        import_span: obligation.import_span,
                        causes: Vec::new(),
                    });
                }
                self.method_rigidities.push(SelectedMethodRigidity {
                    selected_index,
                    condition,
                });
            }
            self.selected.push(SelectedOccurrence {
                checked_argument,
                method_arguments: std::mem::take(&mut obligation.method_arguments),
                selection: Some(selection),
                slot: Some(obligation.slot.clone()),
            });
        }
        Ok(())
    }

    pub(crate) fn prepare_publication<F>(
        &mut self,
        mut zonk: F,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<PendingEvidencePublication, SelectionFailure>
    where
        F: FnMut(Type, &mut TypeWorkBudget) -> Result<Type, SelectionFailure>,
    {
        if !self.pending.is_empty()
            || self.pending_method_rigidity_count != 0
            || !self.method_rigidities.is_empty()
        {
            return Err(SelectionFailure::InvalidState);
        }
        let method_argument_count = self.selected.iter().try_fold(0usize, |total, selected| {
            total.checked_add(selected.method_arguments.len())
        });
        let retained_work = method_argument_count
            .and_then(|count| {
                self.selected
                    .len()
                    .checked_mul(2)
                    .and_then(|fixed| count.checked_add(fixed))
            })
            .ok_or(SelectionFailure::ConstraintResource)?;
        constraint_work
            .charge(retained_work)
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        let mut occurrences = Vec::new();
        let mut slot_ids = HashSet::new();
        occurrences
            .try_reserve(self.selected.len())
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        slot_ids
            .try_reserve(self.selected.len())
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        for mut selected in self.selected.drain(..) {
            let checked_argument = IterativeTypeOwner::new(zonk(
                std::mem::replace(&mut selected.checked_argument, Type::Unit),
                type_work,
            )?);
            if !same_type_with_constraint_budget(
                &checked_argument,
                selected
                    .selection
                    .as_ref()
                    .ok_or(SelectionFailure::InvalidState)?
                    .argument(),
                constraint_work,
            )
            .map_err(|()| SelectionFailure::ConstraintResource)?
            {
                return Err(SelectionFailure::InvalidState);
            }
            let mut method_arguments = Vec::new();
            type_work
                .charge(selected.method_arguments.len())
                .map_err(|()| SelectionFailure::TypeResource)?;
            method_arguments
                .try_reserve(selected.method_arguments.len())
                .map_err(|_| SelectionFailure::TypeResource)?;
            for argument in std::mem::take(&mut selected.method_arguments).into_vec() {
                match zonk(argument, type_work) {
                    Ok(argument) => method_arguments.push(argument),
                    Err(failure) => {
                        for argument in method_arguments {
                            discard_type_iteratively(argument);
                        }
                        return Err(failure);
                    }
                }
            }
            let Some(slot) = selected.slot.take() else {
                for argument in method_arguments {
                    discard_type_iteratively(argument);
                }
                return Err(SelectionFailure::InvalidState);
            };
            let slot_id = slot.storage_id();
            if !slot.is_empty() || !slot_ids.insert(slot_id) {
                for argument in method_arguments {
                    discard_type_iteratively(argument);
                }
                return Err(SelectionFailure::InvalidState);
            }
            occurrences.push(SelectedOccurrence {
                checked_argument: checked_argument.into_inner(),
                method_arguments: method_arguments.into_boxed_slice(),
                selection: selected.selection.take(),
                slot: Some(slot),
            });
        }
        Ok(PendingEvidencePublication {
            occurrences,
            slot_ids,
        })
    }

    #[cfg(test)]
    pub(crate) fn select(
        &self,
        interface: InterfaceId,
        argument: &Type,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<EvidenceSelection, SelectionFailure> {
        let argument = clone_type_with_budget(argument, type_work)
            .map_err(|()| SelectionFailure::TypeResource)?;
        let registry = self.canonical_registry_for_test();
        let mut causes = Vec::new();
        let (checked_argument, selection) = self.select_owned(
            &registry,
            interface,
            argument,
            &mut causes,
            constraint_work,
            type_work,
        )?;
        discard_type_iteratively(checked_argument);
        Ok(selection)
    }

    #[cfg(test)]
    fn select_owned_for_test(
        &self,
        interface: InterfaceId,
        argument: Type,
        causes: &mut Vec<SelectionCause>,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(Type, EvidenceSelection), SelectionFailure> {
        let registry = self.canonical_registry_for_test();
        self.select_owned(
            &registry,
            interface,
            argument,
            causes,
            constraint_work,
            type_work,
        )
    }

    fn select_owned(
        &self,
        registry: &ResolvedRegistry,
        interface: InterfaceId,
        argument: Type,
        causes: &mut Vec<SelectionCause>,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(Type, EvidenceSelection), SelectionFailure> {
        causes.clear();
        let argument = IterativeTypeOwner::new(argument);
        if matches!(&*argument, Type::Inference(_)) {
            let interface_entry = self.interface_entry(interface)?;
            retain_selection_cause(
                causes,
                SelectionCauseKind::Interface,
                interface_entry.span,
                constraint_work,
            )?;
            return Err(SelectionFailure::Reason(InterfaceReason::Ambiguous));
        }
        if matches!(&*argument, Type::Forall(_, _)) {
            return Err(SelectionFailure::InvalidState);
        }
        let mut builder = EvidenceSelectionBuilder::new();
        let mut checked_goal = Goal {
            interface,
            argument: argument.into_inner(),
        };
        let work_argument = clone_type_with_budget(&checked_goal.argument, type_work)
            .map_err(|()| SelectionFailure::TypeResource)?;
        let mut work = SelectionWork::new(
            Goal {
                interface,
                argument: work_argument,
            },
            0,
            constraint_work,
        )?;
        let mut results = Vec::new();
        let mut active = std::collections::HashSet::new();
        while let Some(task) = work.pop() {
            match task {
                SelectionTask::Select {
                    mut goal,
                    cause_marker,
                } => {
                    if cause_marker > causes.len() {
                        return Err(SelectionFailure::InvalidState);
                    }
                    causes.truncate(cause_marker);
                    let interface_entry = self.interface_entry(goal.interface)?;
                    retain_selection_cause(
                        causes,
                        SelectionCauseKind::Interface,
                        interface_entry.span,
                        constraint_work,
                    )?;
                    let key = goal_key(goal.interface, &goal.argument, constraint_work)?;
                    let goal_environments = canonical_body_free_environments(
                        registry,
                        &[],
                        &[&goal.argument],
                        interface_entry.span,
                        constraint_work,
                        type_work,
                    )
                    .map_err(map_ingress_environment_failure)?;
                    let interface_methods = interface_entry.method_ids.as_ref();
                    let mut abstract_match = None;
                    for requirement in &self.abstracts {
                        constraint_work
                            .charge(1)
                            .map_err(|()| SelectionFailure::ConstraintResource)?;
                        if requirement.interface == goal.interface
                            && same_type_with_constraint_budget(
                                &requirement.argument,
                                &goal.argument,
                                constraint_work,
                            )
                            .map_err(|()| SelectionFailure::ConstraintResource)?
                        {
                            abstract_match = Some(requirement.id);
                            break;
                        }
                    }
                    if let Some(requirement) = abstract_match {
                        reserve_selection_result(&mut results, constraint_work)?;
                        let node = builder
                            .push_abstract(requirement, interface_methods, constraint_work)
                            .map_err(|()| SelectionFailure::ConstraintResource)?;
                        results.push(node);
                        continue;
                    }

                    if let Some(current) = self.current {
                        constraint_work
                            .charge(1)
                            .map_err(|()| SelectionFailure::ConstraintResource)?;
                        let implementation_index = *self
                            .implementation_indices
                            .get(&current)
                            .ok_or(SelectionFailure::InvalidState)?;
                        let implementation = self
                            .implementations
                            .get(implementation_index)
                            .ok_or(SelectionFailure::InvalidState)?;
                        if implementation.interface == goal.interface
                            && same_type_with_constraint_budget(
                                &implementation.argument,
                                &goal.argument,
                                constraint_work,
                            )
                            .map_err(|()| SelectionFailure::ConstraintResource)?
                        {
                            reserve_selection_result(&mut results, constraint_work)?;
                            let substitution = self
                                .match_head(
                                    registry,
                                    &goal_environments,
                                    implementation,
                                    &goal.argument,
                                    constraint_work,
                                    type_work,
                                )
                                .map_err(map_head_failure)?
                                .ok_or(SelectionFailure::InvalidState)?;
                            let mut prerequisites = Vec::new();
                            constraint_work
                                .charge(implementation.prerequisites.len())
                                .map_err(|()| SelectionFailure::ConstraintResource)?;
                            prerequisites
                                .try_reserve(implementation.prerequisites.len())
                                .map_err(|_| SelectionFailure::ConstraintResource)?;
                            for prerequisite in &implementation.prerequisites {
                                constraint_work
                                    .charge(1)
                                    .map_err(|()| SelectionFailure::ConstraintResource)?;
                                prerequisites.push(
                                    builder
                                        .push_abstract(
                                            prerequisite.id,
                                            self.interface_methods(prerequisite.interface)?,
                                            constraint_work,
                                        )
                                        .map_err(|()| SelectionFailure::ConstraintResource)?,
                                );
                            }
                            let node = builder
                                .push_implementation(
                                    implementation.id,
                                    substitution,
                                    &prerequisites,
                                    &implementation.methods,
                                    constraint_work,
                                )
                                .map_err(|()| SelectionFailure::ConstraintResource)?;
                            results.push(node);
                            continue;
                        }
                    }

                    charge_goal_key(&key, constraint_work)?;
                    if active.contains(&key) {
                        return Err(SelectionFailure::Reason(InterfaceReason::Cycle));
                    }
                    charge_goal_key(&key, constraint_work)?;
                    active
                        .try_reserve(1)
                        .map_err(|_| SelectionFailure::ConstraintResource)?;
                    let key = Arc::new(key);
                    active.insert(Arc::clone(&key));

                    let mut selected = None;
                    let candidates = self
                        .implementation_candidates
                        .get(&goal.interface)
                        .map(Vec::as_slice)
                        .unwrap_or_default();
                    for &candidate_index in candidates {
                        charge_candidate_inspection(constraint_work)?;
                        let implementation = self
                            .implementations
                            .get(candidate_index)
                            .ok_or(SelectionFailure::InvalidState)?;
                        if Some(implementation.id) == self.current {
                            continue;
                        }
                        let substitution = self
                            .match_head(
                                registry,
                                &goal_environments,
                                implementation,
                                &goal.argument,
                                constraint_work,
                                type_work,
                            )
                            .map_err(map_head_failure)?;
                        if let Some(substitution) = substitution {
                            selected = Some((candidate_index, substitution));
                            break;
                        }
                    }
                    let Some((candidate_index, substitution)) = selected else {
                        charge_goal_key(&key, constraint_work)?;
                        if !active.remove(&key) {
                            return Err(SelectionFailure::InvalidState);
                        }
                        return Err(SelectionFailure::Reason(InterfaceReason::Unsatisfied));
                    };
                    let implementation = &self.implementations[candidate_index];
                    for &import_span in &implementation.import_spans {
                        retain_selection_cause(
                            causes,
                            SelectionCauseKind::ImplementationImport,
                            import_span,
                            constraint_work,
                        )?;
                    }
                    retain_selection_cause(
                        causes,
                        SelectionCauseKind::Implementation,
                        implementation.span,
                        constraint_work,
                    )?;
                    for &method_span in &implementation.method_spans {
                        retain_selection_cause(
                            causes,
                            SelectionCauseKind::ImplementationMethod,
                            method_span,
                            constraint_work,
                        )?;
                    }
                    let prerequisite_cause_marker = causes.len();
                    let replacements = replacement_map(&substitution, type_work)?;
                    let result_start = results.len();
                    work.push(
                        SelectionTask::Finish {
                            key,
                            candidate_index,
                            substitution,
                            result_start,
                        },
                        constraint_work,
                    )?;
                    for prerequisite in implementation.prerequisites.iter().rev() {
                        let argument = substitute_type_variables_with(
                            &prerequisite.argument,
                            replacements.as_map(),
                            |cells| type_work.charge(cells),
                        )
                        .map_err(|()| SelectionFailure::TypeResource)?;
                        let goal = Goal {
                            interface: prerequisite.interface,
                            argument,
                        };
                        charge_prerequisite_goal(&goal.argument, constraint_work)?;
                        work.push(
                            SelectionTask::Select {
                                goal,
                                cause_marker: prerequisite_cause_marker,
                            },
                            constraint_work,
                        )?;
                    }
                    discard_type_iteratively(std::mem::replace(&mut goal.argument, Type::Unit));
                }
                SelectionTask::Finish {
                    key,
                    candidate_index,
                    substitution,
                    result_start,
                } => {
                    charge_goal_key(&key, constraint_work)?;
                    if !active.remove(&key) || result_start > results.len() {
                        return Err(SelectionFailure::InvalidState);
                    }
                    let implementation = self
                        .implementations
                        .get(candidate_index)
                        .ok_or(SelectionFailure::InvalidState)?;
                    let result_count = results.len() - result_start;
                    if result_count != implementation.prerequisites.len() {
                        return Err(SelectionFailure::InvalidState);
                    }
                    reserve_selection_result(&mut results, constraint_work)?;
                    let prerequisites = &results[result_start..];
                    let node = builder
                        .push_implementation(
                            implementation.id,
                            substitution,
                            prerequisites,
                            &implementation.methods,
                            constraint_work,
                        )
                        .map_err(|()| SelectionFailure::ConstraintResource)?;
                    results.truncate(result_start);
                    results.push(node);
                }
            }
        }
        if !active.is_empty() || results.len() != 1 {
            return Err(SelectionFailure::InvalidState);
        }
        let checked_argument =
            IterativeTypeOwner::new(std::mem::replace(&mut checked_goal.argument, Type::Unit));
        if constraint_work
            .charge(1)
            .and_then(|()| constraint_work.charge_type(&checked_argument))
            .is_err()
        {
            return Err(SelectionFailure::ConstraintResource);
        }
        let selection_argument = match clone_type_with_budget(&checked_argument, type_work) {
            Ok(argument) => argument,
            Err(()) => return Err(SelectionFailure::TypeResource),
        };
        let selection = match builder.finish(results[0], interface, selection_argument) {
            Ok(selection) => selection,
            Err(()) => return Err(SelectionFailure::InvalidState),
        };
        Ok((checked_argument.into_inner(), selection))
    }

    fn interface_entry(&self, interface: InterfaceId) -> Result<&InterfaceEntry, SelectionFailure> {
        self.interface_indices
            .get(&interface)
            .and_then(|index| self.interfaces.get(*index))
            .ok_or(SelectionFailure::InvalidState)
    }

    fn match_head(
        &self,
        registry: &ResolvedRegistry,
        goal_environments: &KindEnvironments<'_>,
        implementation: &ImplementationEntry,
        goal: &Type,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<Option<Box<[EvidenceSubstitution]>>, HeadMatchFailure> {
        match_implementation_head_in_environment(
            registry,
            InterfaceOperationWork::new(implementation.span, constraint_work, type_work),
            goal_environments,
            &implementation.parameters,
            &implementation.argument,
            goal,
        )
    }

    fn authenticate_implementation_candidate<'a, P>(
        &self,
        registry: &'a ResolvedRegistry,
        candidate: ImplementationCandidateAuthentication<'a, P>,
        constraint_work: &mut InterfaceConstraintBudget,
    ) -> Result<Vec<TypeVariableId>, SelectionFailure>
    where
        P: ExactSizeIterator<Item = (InterfaceId, &'a Type)>,
    {
        let ImplementationCandidateAuthentication {
            parameter_records,
            interface,
            argument,
            prerequisites,
            span,
        } = candidate;
        constraint_work
            .charge(parameter_records.len())
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        let mut parameters = Vec::new();
        let mut parameter_set = HashSet::new();
        parameters
            .try_reserve(parameter_records.len())
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        parameter_set
            .try_reserve(parameter_records.len())
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        for parameter in parameter_records {
            constraint_work
                .charge(1)
                .map_err(|()| SelectionFailure::ConstraintResource)?;
            if !parameter_set.insert(parameter.id) {
                return Err(SelectionFailure::InvalidState);
            }
            canonical_type_variable_kind(registry, parameter.id, span, constraint_work)
                .map_err(map_ingress_kind_failure)?;
            parameters.push(parameter.id);
        }

        let relation_count = prerequisites
            .len()
            .checked_add(1)
            .ok_or(SelectionFailure::ConstraintResource)?;
        constraint_work
            .charge(relation_count)
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        let mut roots = Vec::new();
        roots
            .try_reserve(relation_count)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        constraint_work
            .charge(1)
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        self.interface_entry(interface)?;
        roots.push(argument);
        for (relation_interface, relation_argument) in prerequisites {
            constraint_work
                .charge(1)
                .map_err(|()| SelectionFailure::ConstraintResource)?;
            self.interface_entry(relation_interface)?;
            roots.push(relation_argument);
        }
        validate_candidate_scope(&parameter_set, &roots, constraint_work)?;
        Ok(parameters)
    }

    fn interface_methods(&self, interface: InterfaceId) -> Result<&[MethodId], SelectionFailure> {
        self.interface_entry(interface)
            .map(|entry| entry.method_ids.as_ref())
    }

    #[cfg(test)]
    fn add_interface_raw(
        &mut self,
        id: InterfaceId,
        parameter: TypeVariableId,
        methods: Vec<(MethodId, Type)>,
    ) {
        let file = crate::source::SourceFile::new("selection-fixture.ash", "x")
            .expect("selection fixture source");
        let span = file
            .span(crate::source::ByteRange::new(0, 1).expect("selection fixture range"))
            .expect("selection fixture span");
        let method_ids = methods.iter().map(|(id, _)| *id).collect();
        let methods: Vec<MethodEntry> = methods
            .into_iter()
            .map(|(id, value_type)| MethodEntry {
                id,
                type_parameters: Box::new([]),
                value_type,
                span,
            })
            .collect();
        let interface_index = self.interfaces.len();
        for (method_index, method) in methods.iter().enumerate() {
            assert!(
                self.method_indices
                    .insert(method.id, (interface_index, method_index))
                    .is_none()
            );
        }
        assert!(self.interface_indices.insert(id, interface_index).is_none());
        self.interfaces.push(InterfaceEntry {
            id,
            parameter,
            parameter_kind: Kind::Type,
            methods: methods.into_boxed_slice(),
            method_ids,
            span,
        });
    }

    #[cfg(test)]
    fn canonical_registry_for_test(&self) -> ResolvedRegistry {
        let mut binders = HashMap::new();
        let mut nominal_arities = HashMap::new();
        let mut roots = Vec::new();
        for interface in &self.interfaces {
            binders
                .entry(interface.parameter)
                .or_insert_with(|| (interface.parameter_kind.clone(), interface.span));
        }
        for implementation in &self.implementations {
            roots.push(&implementation.argument);
            for parameter in &implementation.parameters {
                binders
                    .entry(*parameter)
                    .or_insert((Kind::Type, implementation.span));
            }
            roots.extend(
                implementation
                    .prerequisites
                    .iter()
                    .map(|prerequisite| &prerequisite.argument),
            );
        }
        roots.extend(self.abstracts.iter().map(|abstract_| &abstract_.argument));
        roots.extend(self.pending.iter().map(|obligation| &obligation.argument));
        let mut pending = roots;
        while let Some(ty) = pending.pop() {
            let mut function = ty;
            let mut arity = 0usize;
            while let Type::Application(next, _) = function {
                arity = arity
                    .checked_add(1)
                    .expect("a test fixture application arity should fit usize");
                function = next;
            }
            if let Type::Nominal(id) = function {
                nominal_arities
                    .entry(*id)
                    .and_modify(|known: &mut usize| *known = (*known).max(arity))
                    .or_insert(arity);
            }
            match ty {
                Type::Application(function, argument) | Type::Function(function, argument) => {
                    pending.push(argument);
                    pending.push(function);
                }
                Type::Tuple(elements) => pending.extend(elements.iter().rev()),
                Type::Forall(_, body) => pending.push(body),
                Type::Int
                | Type::Bool
                | Type::Unit
                | Type::Nominal(_)
                | Type::Variable(_)
                | Type::Inference(_) => {}
            }
        }
        let fallback_span = self
            .interfaces
            .first()
            .map(|interface| interface.span)
            .or_else(|| {
                self.implementations
                    .first()
                    .map(|implementation| implementation.span)
            })
            .or_else(|| self.pending.first().map(|obligation| obligation.span))
            .expect(
                "a selection fixture should retain an interface, implementation, or obligation",
            );
        let mut used_ids = binders
            .keys()
            .copied()
            .collect::<std::collections::HashSet<_>>();
        let mut next_generated = u32::MAX;
        let mut nominal_parameters = Vec::new();
        let mut nominals = Vec::new();
        for (id, arity) in nominal_arities {
            let mut parameters = Vec::new();
            for _ in 0..arity {
                let parameter = loop {
                    let candidate = TypeVariableId::generated(next_generated);
                    next_generated = next_generated
                        .checked_sub(1)
                        .expect("the test nominal parameter inventory should fit");
                    if used_ids.insert(candidate) {
                        break candidate;
                    }
                };
                parameters.push(crate::resolved::ResolvedTypeVariable {
                    id: parameter,
                    spelling: "A".to_owned(),
                    kind: Kind::Type,
                    origin: crate::source::Origin::Source(fallback_span),
                });
            }
            nominals.push(crate::resolved::ResolvedNominalType {
                id,
                spelling: "Nominal".to_owned(),
                constructors: Box::new([]),
                origin: crate::source::Origin::Source(fallback_span),
            });
            nominal_parameters.push((id, parameters));
        }
        ResolvedRegistry::new(nominals, Vec::new())
            .with_type_parameters(nominal_parameters)
            .with_additional_type_variables(binders.into_iter().map(|(id, (kind, span))| {
                crate::resolved::ResolvedTypeVariable {
                    id,
                    spelling: "T".to_owned(),
                    kind,
                    origin: crate::source::Origin::Source(span),
                }
            }))
    }

    #[cfg(test)]
    fn add_implementation_raw(&mut self, implementation: ImplementationEntry) {
        let index = self.implementations.len();
        assert!(
            self.implementation_indices
                .insert(implementation.id, index)
                .is_none()
        );
        self.implementation_candidates
            .entry(implementation.interface)
            .or_default()
            .push(index);
        self.implementations.push(implementation);
    }
}

fn map_head_failure(failure: HeadMatchFailure) -> SelectionFailure {
    match failure {
        HeadMatchFailure::InvalidState => SelectionFailure::InvalidState,
        HeadMatchFailure::ConstraintResource => SelectionFailure::ConstraintResource,
        HeadMatchFailure::TypeResource => SelectionFailure::TypeResource,
    }
}

fn map_ingress_environment_failure(failure: CanonicalEnvironmentFailure) -> SelectionFailure {
    match failure {
        CanonicalEnvironmentFailure::ConstraintResource => SelectionFailure::ConstraintResource,
        CanonicalEnvironmentFailure::TypeResource => SelectionFailure::TypeResource,
        CanonicalEnvironmentFailure::InvalidState => SelectionFailure::InvalidState,
    }
}

fn map_ingress_kind_failure(failure: KindFailure) -> SelectionFailure {
    match failure {
        KindFailure::Resource(_) => SelectionFailure::ConstraintResource,
        KindFailure::Internal(_) | KindFailure::Source(_) => SelectionFailure::InvalidState,
    }
}

fn validate_candidate_scope(
    allowed: &HashSet<TypeVariableId>,
    roots: &[&Type],
    constraint_work: &mut InterfaceConstraintBudget,
) -> Result<(), SelectionFailure> {
    constraint_work
        .charge(roots.len())
        .map_err(|()| SelectionFailure::ConstraintResource)?;
    let mut pending = Vec::new();
    pending
        .try_reserve(roots.len())
        .map_err(|_| SelectionFailure::ConstraintResource)?;
    pending.extend(roots.iter().rev().copied());
    while let Some(ty) = pending.pop() {
        constraint_work
            .charge(1)
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        match ty {
            Type::Variable(variable) => {
                constraint_work
                    .charge(1)
                    .map_err(|()| SelectionFailure::ConstraintResource)?;
                if !allowed.contains(variable) {
                    return Err(SelectionFailure::InvalidState);
                }
            }
            Type::Application(function, argument) | Type::Function(function, argument) => {
                constraint_work
                    .charge(2)
                    .map_err(|()| SelectionFailure::ConstraintResource)?;
                pending
                    .try_reserve(2)
                    .map_err(|_| SelectionFailure::ConstraintResource)?;
                pending.push(argument);
                pending.push(function);
            }
            Type::Tuple(elements) if elements.len() >= 2 => {
                constraint_work
                    .charge(elements.len())
                    .map_err(|()| SelectionFailure::ConstraintResource)?;
                pending
                    .try_reserve(elements.len())
                    .map_err(|_| SelectionFailure::ConstraintResource)?;
                pending.extend(elements.iter().rev());
            }
            Type::Tuple(_) | Type::Inference(_) | Type::Forall(_, _) => {
                return Err(SelectionFailure::InvalidState);
            }
            Type::Int | Type::Bool | Type::Unit | Type::Nominal(_) => {}
        }
    }
    Ok(())
}

#[derive(Debug)]
struct ReplacementMap {
    values: HashMap<TypeVariableId, Type>,
}

impl Drop for ReplacementMap {
    fn drop(&mut self) {
        for (_, value) in self.values.drain() {
            discard_type_iteratively(value);
        }
    }
}

impl ReplacementMap {
    fn new() -> Self {
        Self {
            values: HashMap::new(),
        }
    }

    fn try_reserve(&mut self, additional: usize) -> Result<(), std::collections::TryReserveError> {
        self.values.try_reserve(additional)
    }

    fn try_insert_unique(
        &mut self,
        parameter: TypeVariableId,
        argument: IterativeTypeOwner,
    ) -> Result<(), SelectionFailure> {
        if let Some(displaced) = self.values.insert(parameter, argument.into_inner()) {
            discard_type_iteratively(displaced);
            return Err(SelectionFailure::InvalidState);
        }
        Ok(())
    }

    fn as_map(&self) -> &HashMap<TypeVariableId, Type> {
        &self.values
    }
}

fn replacement_map(
    substitution: &[EvidenceSubstitution],
    type_work: &mut TypeWorkBudget,
) -> Result<ReplacementMap, SelectionFailure> {
    let mut replacements = ReplacementMap::new();
    type_work
        .charge(substitution.len())
        .map_err(|()| SelectionFailure::TypeResource)?;
    replacements
        .try_reserve(substitution.len())
        .map_err(|_| SelectionFailure::TypeResource)?;
    for binding in substitution {
        let argument = IterativeTypeOwner::new(
            clone_type_with_budget(binding.argument(), type_work)
                .map_err(|()| SelectionFailure::TypeResource)?,
        );
        replacements.try_insert_unique(binding.parameter(), argument)?;
    }
    Ok(replacements)
}

#[derive(Debug)]
struct Goal {
    interface: InterfaceId,
    argument: Type,
}

impl Drop for Goal {
    fn drop(&mut self) {
        discard_type_iteratively(std::mem::replace(&mut self.argument, Type::Unit));
    }
}

#[derive(Debug)]
enum SelectionTask {
    Select {
        goal: Goal,
        cause_marker: usize,
    },
    Finish {
        key: Arc<GoalKey>,
        candidate_index: usize,
        substitution: Box<[EvidenceSubstitution]>,
        result_start: usize,
    },
}

#[derive(Debug)]
struct SelectionWork(Vec<SelectionTask>);

impl SelectionWork {
    fn new(
        goal: Goal,
        cause_marker: usize,
        constraint_work: &mut InterfaceConstraintBudget,
    ) -> Result<Self, SelectionFailure> {
        constraint_work
            .charge(1)
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        let mut tasks = Vec::new();
        tasks
            .try_reserve(1)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        tasks.push(SelectionTask::Select { goal, cause_marker });
        Ok(Self(tasks))
    }

    fn push(
        &mut self,
        task: SelectionTask,
        constraint_work: &mut InterfaceConstraintBudget,
    ) -> Result<(), SelectionFailure> {
        constraint_work
            .charge(1)
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        self.0
            .try_reserve(1)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        self.0.push(task);
        Ok(())
    }

    fn pop(&mut self) -> Option<SelectionTask> {
        self.0.pop()
    }
}

fn reserve_selection_result<T>(
    results: &mut Vec<T>,
    constraint_work: &mut InterfaceConstraintBudget,
) -> Result<(), SelectionFailure> {
    constraint_work
        .charge(1)
        .map_err(|()| SelectionFailure::ConstraintResource)?;
    results
        .try_reserve(1)
        .map_err(|_| SelectionFailure::ConstraintResource)
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct GoalKey {
    interface: InterfaceId,
    cells: Box<[GoalCell]>,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum GoalCell {
    Int,
    Bool,
    Unit,
    Nominal(NominalTypeId),
    Application,
    Tuple(usize),
    Function,
    Variable(TypeVariableId),
}

fn goal_key(
    interface: InterfaceId,
    argument: &Type,
    constraint_work: &mut InterfaceConstraintBudget,
) -> Result<GoalKey, SelectionFailure> {
    if matches!(argument, Type::Inference(_)) {
        return Err(SelectionFailure::Reason(InterfaceReason::Ambiguous));
    }
    let mut pending = Vec::new();
    let mut cells = Vec::new();
    constraint_work
        .charge(1)
        .map_err(|()| SelectionFailure::ConstraintResource)?;
    pending
        .try_reserve(1)
        .map_err(|_| SelectionFailure::ConstraintResource)?;
    pending.push(argument);
    while let Some(ty) = pending.pop() {
        constraint_work
            .charge(1)
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        cells
            .try_reserve(1)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        match ty {
            Type::Int => cells.push(GoalCell::Int),
            Type::Bool => cells.push(GoalCell::Bool),
            Type::Unit => cells.push(GoalCell::Unit),
            Type::Nominal(id) => cells.push(GoalCell::Nominal(*id)),
            Type::Application(function, argument) => {
                cells.push(GoalCell::Application);
                constraint_work
                    .charge(2)
                    .map_err(|()| SelectionFailure::ConstraintResource)?;
                pending
                    .try_reserve(2)
                    .map_err(|_| SelectionFailure::ConstraintResource)?;
                pending.push(argument);
                pending.push(function);
            }
            Type::Tuple(elements) => {
                cells.push(GoalCell::Tuple(elements.len()));
                constraint_work
                    .charge(elements.len())
                    .map_err(|()| SelectionFailure::ConstraintResource)?;
                pending
                    .try_reserve(elements.len())
                    .map_err(|_| SelectionFailure::ConstraintResource)?;
                pending.extend(elements.iter().rev());
            }
            Type::Function(domain, codomain) => {
                cells.push(GoalCell::Function);
                constraint_work
                    .charge(2)
                    .map_err(|()| SelectionFailure::ConstraintResource)?;
                pending
                    .try_reserve(2)
                    .map_err(|_| SelectionFailure::ConstraintResource)?;
                pending.push(codomain);
                pending.push(domain);
            }
            Type::Variable(id) => cells.push(GoalCell::Variable(*id)),
            Type::Inference(_) => {
                return Err(SelectionFailure::Reason(InterfaceReason::Ambiguous));
            }
            Type::Forall(_, _) => return Err(SelectionFailure::InvalidState),
        }
    }
    Ok(GoalKey {
        interface,
        cells: cells.into_boxed_slice(),
    })
}

fn charge_goal_key(
    key: &GoalKey,
    constraint_work: &mut InterfaceConstraintBudget,
) -> Result<(), SelectionFailure> {
    constraint_work
        .charge(key.cells.len().saturating_add(1))
        .map_err(|()| SelectionFailure::ConstraintResource)
}

fn charge_candidate_inspection(
    constraint_work: &mut InterfaceConstraintBudget,
) -> Result<(), SelectionFailure> {
    constraint_work
        .charge(1)
        .map_err(|()| SelectionFailure::ConstraintResource)
}

fn charge_prerequisite_goal(
    argument: &Type,
    constraint_work: &mut InterfaceConstraintBudget,
) -> Result<(), SelectionFailure> {
    constraint_work
        .charge(1)
        .and_then(|()| constraint_work.charge_type(argument))
        .map_err(|()| SelectionFailure::ConstraintResource)
}

fn retain_selection_cause(
    causes: &mut Vec<SelectionCause>,
    kind: SelectionCauseKind,
    span: Span,
    constraint_work: &mut InterfaceConstraintBudget,
) -> Result<(), SelectionFailure> {
    constraint_work
        .charge(1)
        .map_err(|()| SelectionFailure::ConstraintResource)?;
    causes
        .try_reserve(1)
        .map_err(|_| SelectionFailure::ConstraintResource)?;
    causes.push(SelectionCause { kind, span });
    Ok(())
}

fn same_type_with_constraint_budget(
    left: &Type,
    right: &Type,
    constraint_work: &mut InterfaceConstraintBudget,
) -> Result<bool, ()> {
    constraint_work.charge(1)?;
    let mut pending = Vec::new();
    pending.try_reserve(1).map_err(|_| ())?;
    pending.push((left, right));
    while let Some((left, right)) = pending.pop() {
        constraint_work.charge(1)?;
        match (left, right) {
            (Type::Int, Type::Int) | (Type::Bool, Type::Bool) | (Type::Unit, Type::Unit) => {}
            (Type::Nominal(left), Type::Nominal(right)) if left == right => {}
            (Type::Variable(left), Type::Variable(right)) if left == right => {}
            (Type::Inference(left), Type::Inference(right)) if left == right => {}
            (
                Type::Application(left_function, left_argument),
                Type::Application(right_function, right_argument),
            ) => {
                constraint_work.charge(2)?;
                pending.try_reserve(2).map_err(|_| ())?;
                pending.push((left_argument, right_argument));
                pending.push((left_function, right_function));
            }
            (Type::Forall(left_parameters, left), Type::Forall(right_parameters, right)) => {
                if !same_kinded_type_parameters_with_charge(
                    left_parameters,
                    right_parameters,
                    |work| constraint_work.charge(work),
                )? {
                    return Ok(false);
                }
                constraint_work.charge(1)?;
                pending.try_reserve(1).map_err(|_| ())?;
                pending.push((left, right));
            }
            (Type::Tuple(left), Type::Tuple(right)) if left.len() == right.len() => {
                constraint_work.charge(left.len())?;
                pending.try_reserve(left.len()).map_err(|_| ())?;
                pending.extend(left.iter().zip(right).rev());
            }
            (
                Type::Function(left_domain, left_codomain),
                Type::Function(right_domain, right_codomain),
            ) => {
                constraint_work.charge(2)?;
                pending.try_reserve(2).map_err(|_| ())?;
                pending.push((left_codomain, right_codomain));
                pending.push((left_domain, right_domain));
            }
            _ => return Ok(false),
        }
    }
    Ok(true)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        interface::{
            CheckedImplMethod, CheckedRequirement, EvidenceNode, EvidenceSlot, RequirementOwner,
        },
        module::ModuleId,
        resolved::{
            Binder, BinderId, CheckedImplementationFact, CheckedImplementationMethodFact,
            CheckedInterfaceFact, CheckedInterfaceMethodFact, ImplementationAuthorization,
            ImplementationRouteHop, ResolvedImplementation, ResolvedImplementationMethodGroup,
            ResolvedInterfaceOccurrence, ResolvedNominalType, ResolvedRequirement, ResolvedType,
            ResolvedTypeProvenance, ResolvedTypeProvenanceNode, ResolvedTypeVariable,
        },
        source::{ByteRange, Origin, SourceFile},
    };

    fn ids() -> (InterfaceId, MethodId, RequirementId) {
        let module = ModuleId::new(1);
        let interface = InterfaceId::new(module, 0);
        let method = MethodId::new(interface, 0);
        let requirement =
            RequirementId::new(RequirementOwner::Global(BinderId::resolved(module, 0)), 0);
        (interface, method, requirement)
    }

    fn interface_fact_with_kind(kind: Kind) -> CheckedInterfaceFact {
        let file = SourceFile::new("selection-kind-fixture.ash", "Interface")
            .expect("interface fixture source");
        let span = file
            .span(ByteRange::new(0, 9).expect("interface fixture range"))
            .expect("interface fixture span");
        let interface = InterfaceId::new(ModuleId::from(file.id()), 0);
        CheckedInterfaceFact {
            id: interface,
            spelling: "Interface".to_owned(),
            parameter: ResolvedTypeVariable {
                id: TypeVariableId::resolved(ModuleId::from(file.id()), 0),
                spelling: "F".to_owned(),
                kind,
                origin: Origin::Source(span),
            },
            methods: Box::new([]),
            origin: Origin::Source(span),
            span,
        }
    }

    fn registry_for_interface_fact(fact: &CheckedInterfaceFact) -> ResolvedRegistry {
        let mut variables = vec![ResolvedTypeVariable {
            id: fact.parameter.id,
            spelling: fact.parameter.spelling.clone(),
            kind: fact.parameter.kind.clone(),
            origin: fact.parameter.origin.clone(),
        }];
        for method in &fact.methods {
            variables.extend(method.type_parameters().iter().map(|parameter| {
                ResolvedTypeVariable {
                    id: parameter.id,
                    spelling: parameter.spelling.clone(),
                    kind: parameter.kind.clone(),
                    origin: parameter.origin.clone(),
                }
            }));
        }
        ResolvedRegistry::new(Vec::new(), Vec::new()).with_additional_type_variables(variables)
    }

    struct IsolatedRigidityFixture {
        selector: EvidenceSelector,
        registry: ResolvedRegistry,
        target: MethodRigidityTarget,
        missing_interface: InterfaceId,
        repeat_interface: InterfaceId,
        current: ImplId,
        missing_slot: EvidenceSlot,
        repeat_slot: EvidenceSlot,
    }

    fn isolated_rigidity_fixture() -> IsolatedRigidityFixture {
        let module = ModuleId::new(111);
        let missing_interface = InterfaceId::new(module, 0);
        let repeat_interface = InterfaceId::new(module, 1);
        let missing_method = MethodId::new(missing_interface, 0);
        let repeat_method = MethodId::new(repeat_interface, 0);
        let current = ImplId::new(module, 0);
        let source = SourceFile::new("isolated-method-rigidity.ash", "missing repeat argument")
            .expect("the isolated rigidity source should fit");
        let missing_span = source
            .span(ByteRange::new(0, 7).expect("the missing range should be ordered"))
            .expect("the missing span should fit");
        let occurrence_span = source
            .span(ByteRange::new(8, 14).expect("the repeat range should be ordered"))
            .expect("the repeat occurrence span should fit");
        let application_span = source
            .span(ByteRange::new(8, 23).expect("the application range should be ordered"))
            .expect("the application span should fit");
        let argument_span = source
            .span(ByteRange::new(15, 23).expect("the argument range should be ordered"))
            .expect("the argument span should fit");
        let mut selector = EvidenceSelector::new();
        selector.add_interface_raw(
            missing_interface,
            TypeVariableId::resolved(module, 0),
            vec![(missing_method, Type::Unit)],
        );
        selector.add_interface_raw(
            repeat_interface,
            TypeVariableId::resolved(module, 1),
            vec![(repeat_method, Type::Unit)],
        );
        selector.add_implementation_raw(implementation(
            current,
            repeat_interface,
            Vec::new(),
            Type::Int,
            Vec::new(),
            vec![ImplMethodId::new(current, repeat_method)],
        ));
        let registry = selector.canonical_registry_for_test();
        selector
            .enter_implementation_scope(
                current,
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            )
            .expect("the current implementation scope should fit");
        let marker = selector.pending_marker();
        let missing_slot = EvidenceSlot::empty();
        selector
            .push_owned_obligation(
                missing_interface,
                Type::Int,
                SelectionSite::plain(missing_slot.handle(), missing_span),
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the unrelated missing obligation should stage first");
        let repeat_slot = EvidenceSlot::empty();
        selector
            .push_cloned_obligation(
                repeat_interface,
                &Type::Int,
                MethodObligationMetadata::new(
                    Box::new([Type::Bool]),
                    Some(MethodRigidityCondition::new(
                        Box::new([Type::Int]),
                        MethodRigiditySite::application(
                            occurrence_span,
                            application_span,
                            argument_span,
                        ),
                    )),
                ),
                SelectionSite::plain(repeat_slot.handle(), occurrence_span),
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            )
            .expect("the matching conditional obligation should stage second");
        IsolatedRigidityFixture {
            selector,
            registry,
            target: MethodRigidityTarget::new(marker, application_span),
            missing_interface,
            repeat_interface,
            current,
            missing_slot,
            repeat_slot,
        }
    }

    fn assert_isolated_rigidity_fixture_unmodified(fixture: &IsolatedRigidityFixture) {
        assert_eq!(fixture.selector.pending.len(), 2);
        assert_eq!(
            fixture.selector.pending[0].interface,
            fixture.missing_interface
        );
        assert_eq!(
            fixture.selector.pending[1].interface,
            fixture.repeat_interface
        );
        assert_eq!(fixture.selector.pending_method_rigidity_count, 1);
        assert!(fixture.selector.selected.is_empty());
        assert_eq!(fixture.selector.method_rigidity_count(), 0);
        assert!(fixture.missing_slot.selection().is_none());
        assert!(fixture.repeat_slot.selection().is_none());
    }

    #[test]
    fn isolated_method_rigidity_close_skips_earlier_unrelated_selection_failure() {
        let IsolatedRigidityFixture {
            mut selector,
            registry,
            target,
            missing_interface,
            repeat_interface: _,
            current,
            missing_slot,
            repeat_slot,
        } = isolated_rigidity_fixture();

        assert!(
            selector
                .close_method_rigidity_with_registry(
                    &registry,
                    target,
                    |ty, _| Ok(ty),
                    &mut InterfaceConstraintBudget::default(),
                    &mut TypeWorkBudget::default(),
                )
                .expect("only the matching exact-current obligation should close")
        );

        assert_eq!(selector.pending.len(), 1);
        assert_eq!(selector.pending[0].interface, missing_interface);
        assert_eq!(selector.pending_method_rigidity_count, 0);
        assert_eq!(selector.selected.len(), 1);
        assert_eq!(selector.method_rigidity_count(), 1);
        let check = selector
            .method_rigidity(0)
            .expect("the matching occurrence should retain one rigidity relation");
        assert_eq!(check.method_arguments(), &[Type::Bool]);
        assert_eq!(check.rigid_arguments(), &[Type::Int]);
        let selection = selector.selected[0]
            .selection
            .as_ref()
            .expect("the matching occurrence should retain private selection");
        assert!(matches!(
            selection.node(selection.root()),
            Some(EvidenceNode::Implementation { implementation, .. })
                if implementation == current
        ));
        assert!(missing_slot.selection().is_none());
        assert!(repeat_slot.selection().is_none());
        assert!(matches!(
            selector.prepare_publication(
                |ty, _| Ok(ty),
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            ),
            Err(SelectionFailure::InvalidState)
        ));
        assert!(missing_slot.selection().is_none());
        assert!(repeat_slot.selection().is_none());
    }

    #[test]
    fn isolated_method_rigidity_close_has_exact_atomic_retry_boundaries() {
        const EXACT_CONSTRAINT_WORK: usize = 25;
        const EXACT_TYPE_WORK: usize = 3;

        let mut measured = isolated_rigidity_fixture();
        let mut no_condition = EvidenceSelector::new();
        assert!(
            !no_condition
                .close_method_rigidity_with_registry(
                    &measured.registry,
                    MethodRigidityTarget::new(0, measured.target.failure_span()),
                    |ty, _| Ok(ty),
                    &mut InterfaceConstraintBudget::with_limit(0),
                    &mut TypeWorkBudget::with_limit(0),
                )
                .expect("the no-condition fast path should consume no resource")
        );
        let mut measured_constraints = InterfaceConstraintBudget::default();
        let mut measured_types = TypeWorkBudget::default();
        assert!(
            measured
                .selector
                .close_method_rigidity_with_registry(
                    &measured.registry,
                    measured.target,
                    |ty, _| Ok(ty),
                    &mut measured_constraints,
                    &mut measured_types,
                )
                .expect("the measured isolated close should select exact-current evidence")
        );
        let exact_constraints = measured_constraints.used();
        let exact_types = measured_types.used();
        assert_eq!(exact_constraints, EXACT_CONSTRAINT_WORK);
        assert_eq!(exact_types, EXACT_TYPE_WORK);

        let mut constraint_short = isolated_rigidity_fixture();
        let error = constraint_short
            .selector
            .close_method_rigidity_with_registry(
                &constraint_short.registry,
                constraint_short.target,
                |ty, _| Ok(ty),
                &mut InterfaceConstraintBudget::with_limit(exact_constraints - 1),
                &mut TypeWorkBudget::with_limit(exact_types),
            )
            .expect_err("one-short constraint work should reject before selector mutation");
        assert_eq!(error.failure(), SelectionFailure::ConstraintResource);
        assert_isolated_rigidity_fixture_unmodified(&constraint_short);
        let mut exact_constraint_retry = InterfaceConstraintBudget::with_limit(exact_constraints);
        let mut exact_type_retry = TypeWorkBudget::with_limit(exact_types);
        assert!(
            constraint_short
                .selector
                .close_method_rigidity_with_registry(
                    &constraint_short.registry,
                    constraint_short.target,
                    |ty, _| Ok(ty),
                    &mut exact_constraint_retry,
                    &mut exact_type_retry,
                )
                .expect("the exact retry should close only the matching obligation")
        );
        assert_eq!(exact_constraint_retry.used(), exact_constraints);
        assert_eq!(exact_type_retry.used(), exact_types);

        let mut type_short = isolated_rigidity_fixture();
        let error = type_short
            .selector
            .close_method_rigidity_with_registry(
                &type_short.registry,
                type_short.target,
                |ty, _| Ok(ty),
                &mut InterfaceConstraintBudget::with_limit(exact_constraints),
                &mut TypeWorkBudget::with_limit(exact_types - 1),
            )
            .expect_err("one-short type work should reject before selector mutation");
        assert_eq!(error.failure(), SelectionFailure::TypeResource);
        assert_isolated_rigidity_fixture_unmodified(&type_short);
        let mut exact_constraint_retry = InterfaceConstraintBudget::with_limit(exact_constraints);
        let mut exact_type_retry = TypeWorkBudget::with_limit(exact_types);
        assert!(
            type_short
                .selector
                .close_method_rigidity_with_registry(
                    &type_short.registry,
                    type_short.target,
                    |ty, _| Ok(ty),
                    &mut exact_constraint_retry,
                    &mut exact_type_retry,
                )
                .expect("the exact type retry should preserve the matching relation")
        );
        assert_eq!(exact_constraint_retry.used(), exact_constraints);
        assert_eq!(exact_type_retry.used(), exact_types);

        let mut invalid = isolated_rigidity_fixture();
        let invalid_target = MethodRigidityTarget::new(
            invalid.selector.pending.len() + 1,
            invalid.target.failure_span(),
        );
        let error = invalid
            .selector
            .close_method_rigidity_with_registry(
                &invalid.registry,
                invalid_target,
                |ty, _| Ok(ty),
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            )
            .expect_err("an invalid marker should reject without selector mutation");
        assert_eq!(error.failure(), SelectionFailure::InvalidState);
        assert_isolated_rigidity_fixture_unmodified(&invalid);

        let mut duplicate = isolated_rigidity_fixture();
        let duplicate_site = duplicate.selector.pending[1]
            .method_rigidity
            .as_ref()
            .expect("the fixture should retain the matching condition")
            .site;
        let duplicate_slot = EvidenceSlot::empty();
        duplicate
            .selector
            .push_cloned_obligation(
                duplicate.repeat_interface,
                &Type::Int,
                MethodObligationMetadata::new(
                    Box::new([Type::Bool]),
                    Some(MethodRigidityCondition::new(
                        Box::new([Type::Int]),
                        duplicate_site,
                    )),
                ),
                SelectionSite::plain(duplicate_slot.handle(), duplicate_site.occurrence_span()),
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            )
            .expect("the duplicate matching condition should stage");
        let error = duplicate
            .selector
            .close_method_rigidity_with_registry(
                &duplicate.registry,
                duplicate.target,
                |ty, _| Ok(ty),
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            )
            .expect_err("two matching source sites should reject without selection");
        assert_eq!(error.failure(), SelectionFailure::InvalidState);
        assert_eq!(duplicate.selector.pending.len(), 3);
        assert_eq!(duplicate.selector.pending_method_rigidity_count, 2);
        assert!(duplicate.selector.selected.is_empty());
        assert_eq!(duplicate.selector.method_rigidity_count(), 0);
        assert!(duplicate.missing_slot.selection().is_none());
        assert!(duplicate.repeat_slot.selection().is_none());
        assert!(duplicate_slot.selection().is_none());
    }

    #[test]
    fn isolated_method_rigidity_close_charges_the_exact_removal_shift() {
        const EXACT_CONSTRAINT_WORK: usize = 27;
        const EXACT_TYPE_WORK: usize = 3;

        let mut fixture = isolated_rigidity_fixture();
        let trailing_slot = EvidenceSlot::empty();
        fixture
            .selector
            .push_owned_obligation(
                fixture.missing_interface,
                Type::Bool,
                SelectionSite::plain(trailing_slot.handle(), fixture.target.failure_span()),
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the trailing unrelated obligation should stage");

        let error = fixture
            .selector
            .close_method_rigidity_with_registry(
                &fixture.registry,
                fixture.target,
                |ty, _| Ok(ty),
                &mut InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK - 1),
                &mut TypeWorkBudget::with_limit(EXACT_TYPE_WORK),
            )
            .expect_err("one-short shifted removal should reject without selector mutation");
        assert_eq!(error.failure(), SelectionFailure::ConstraintResource);
        assert_eq!(fixture.selector.pending.len(), 3);
        assert_eq!(fixture.selector.pending[0].argument, Type::Int);
        assert_eq!(fixture.selector.pending[1].argument, Type::Int);
        assert_eq!(fixture.selector.pending[2].argument, Type::Bool);
        assert_eq!(fixture.selector.pending_method_rigidity_count, 1);
        assert!(fixture.selector.selected.is_empty());
        assert_eq!(fixture.selector.method_rigidity_count(), 0);
        assert!(fixture.missing_slot.selection().is_none());
        assert!(fixture.repeat_slot.selection().is_none());
        assert!(trailing_slot.selection().is_none());

        let mut exact_constraints = InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK);
        let mut exact_types = TypeWorkBudget::with_limit(EXACT_TYPE_WORK);
        assert!(
            fixture
                .selector
                .close_method_rigidity_with_registry(
                    &fixture.registry,
                    fixture.target,
                    |ty, _| Ok(ty),
                    &mut exact_constraints,
                    &mut exact_types,
                )
                .expect("the exact shifted-removal retry should succeed")
        );
        assert_eq!(exact_constraints.used(), EXACT_CONSTRAINT_WORK);
        assert_eq!(exact_types.used(), EXACT_TYPE_WORK);
        assert_eq!(fixture.selector.pending.len(), 2);
        assert_eq!(fixture.selector.pending[0].argument, Type::Int);
        assert_eq!(fixture.selector.pending[1].argument, Type::Bool);
        assert_eq!(fixture.selector.pending_method_rigidity_count, 0);
        assert_eq!(fixture.selector.selected.len(), 1);
        assert_eq!(fixture.selector.method_rigidity_count(), 1);
        assert!(fixture.missing_slot.selection().is_none());
        assert!(fixture.repeat_slot.selection().is_none());
        assert!(trailing_slot.selection().is_none());
    }

    #[test]
    fn interface_selector_method_scheme_has_exact_atomic_dual_boundaries() {
        let setup = || {
            let mut fact = interface_fact_with_kind(Kind::Type);
            let method_parameter = TypeVariableId::resolved(fact.id.module(), 1);
            fact.methods = Box::new([CheckedInterfaceMethodFact {
                id: MethodId::new(fact.id, 0),
                spelling: "apply".to_owned(),
                type_parameters: Box::new([ResolvedTypeVariable {
                    id: method_parameter,
                    spelling: "F".to_owned(),
                    kind: Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)),
                    origin: Origin::Source(fact.span),
                }]),
                value_type: Type::Function(
                    Box::new(Type::Variable(fact.parameter.id)),
                    Box::new(Type::Application(
                        Box::new(Type::Variable(method_parameter)),
                        Box::new(Type::Variable(fact.parameter.id)),
                    )),
                ),
                origin: Origin::Source(fact.span),
                span: fact.span,
            }]);
            let registry = registry_for_interface_fact(&fact);
            (fact, registry, method_parameter)
        };
        let run = |constraint_limit, type_limit| {
            let (fact, registry, method_parameter) = setup();
            let mut selector = EvidenceSelector::new();
            let mut constraints = InterfaceConstraintBudget::with_limit(constraint_limit);
            let mut types = TypeWorkBudget::with_limit(type_limit);
            let result =
                selector.add_interface_fact(&registry, &fact, &mut constraints, &mut types);
            (
                result,
                selector,
                method_parameter,
                constraints.used(),
                types.used(),
            )
        };

        let (measured, selector, method_parameter, exact_constraints, exact_types) =
            run(usize::MAX, usize::MAX);
        measured.expect("the measured method scheme should publish atomically");
        let method = selector
            .method(selector.interfaces[0].methods[0].id)
            .expect("the selector should retain the method scheme");
        assert_eq!(
            method.type_parameters(),
            &[(
                method_parameter,
                Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type))
            )]
        );

        let (constraint_short, selector, _, _, _) = run(exact_constraints - 1, exact_types);
        assert!(matches!(
            constraint_short,
            Err(SelectionFailure::ConstraintResource)
        ));
        assert!(selector.interfaces.is_empty());

        let (type_short, selector, _, _, _) = run(exact_constraints, exact_types - 1);
        assert!(matches!(type_short, Err(SelectionFailure::TypeResource)));
        assert!(selector.interfaces.is_empty());

        let (exact, selector, _, used_constraints, used_types) =
            run(exact_constraints, exact_types);
        exact.expect("the exact method-scheme budgets should publish atomically");
        assert_eq!(used_constraints, exact_constraints);
        assert_eq!(used_types, exact_types);
        assert_eq!(selector.interfaces.len(), 1);
    }

    #[test]
    fn publication_preflight_rejects_without_partially_filling_an_earlier_slot() {
        let (interface, _, requirement) = ids();
        let mut budget = InterfaceConstraintBudget::default();
        let mut builder = EvidenceSelectionBuilder::new();
        let root = builder
            .push_abstract(requirement, &[], &mut budget)
            .expect("one abstract evidence node should fit");
        let selection = builder
            .finish(root, interface, Type::Int)
            .expect("the abstract selection should have one valid root");
        let first = EvidenceSlot::empty();
        let second = EvidenceSlot::empty();
        let first_handle = first.handle();
        let second_handle = second.handle();
        second_handle
            .fill(Type::Int, Box::new([]), selection.clone())
            .expect("the second slot should begin filled for the invalid fixture");
        let mut slot_ids = HashSet::new();
        slot_ids
            .try_reserve(2)
            .expect("two preflight fixture identities should fit");
        slot_ids.insert(first_handle.storage_id());
        slot_ids.insert(second_handle.storage_id());
        let publication = PendingEvidencePublication {
            occurrences: vec![
                SelectedOccurrence {
                    checked_argument: Type::Int,
                    method_arguments: Box::new([Type::Bool]),
                    selection: Some(selection.clone()),
                    slot: Some(first_handle),
                },
                SelectedOccurrence {
                    checked_argument: Type::Int,
                    method_arguments: Box::new([]),
                    selection: Some(selection),
                    slot: Some(second_handle),
                },
            ],
            slot_ids,
        };

        assert_eq!(publication.publish(), Err(SelectionFailure::InvalidState));
        assert!(first.selection().is_none());
        assert!(first.method_arguments().is_empty());
        assert!(second.selection().is_some());
    }

    #[test]
    fn pending_method_arguments_have_exact_atomic_publication_boundaries() {
        // Two method arguments plus two occurrence/slot carrier records, then
        // the exact two-unit comparison of the checked and selected Int goal.
        const EXACT_CONSTRAINT_WORK: usize = 2 + 2 + 2;
        // The ordered method-argument vector owns two retained Type carriers;
        // the identity zonk fixture performs no additional Type cloning.
        const EXACT_TYPE_WORK: usize = 2;

        let run = |constraint_limit, type_limit| {
            let (interface, _, requirement) = ids();
            let mut builder = EvidenceSelectionBuilder::new();
            let root = builder
                .push_abstract(requirement, &[], &mut InterfaceConstraintBudget::default())
                .expect("one abstract evidence node should fit");
            let selection = builder
                .finish(root, interface, Type::Int)
                .expect("the pending selection should have one valid root");
            let slot = EvidenceSlot::empty();
            let mut selector = EvidenceSelector::new();
            selector.selected.push(SelectedOccurrence {
                checked_argument: Type::Int,
                method_arguments: Box::new([Type::Bool, Type::Int]),
                selection: Some(selection),
                slot: Some(slot.handle()),
            });
            let mut constraints = InterfaceConstraintBudget::with_limit(constraint_limit);
            let mut types = TypeWorkBudget::with_limit(type_limit);
            let result = selector.prepare_publication(
                |argument, _| Ok(argument),
                &mut constraints,
                &mut types,
            );
            (result, slot, constraints.used(), types.used())
        };

        let (constraint_short, slot, _, _) = run(EXACT_CONSTRAINT_WORK - 1, EXACT_TYPE_WORK);
        assert!(matches!(
            constraint_short,
            Err(SelectionFailure::ConstraintResource)
        ));
        assert!(slot.selection().is_none());

        let (type_short, slot, _, _) = run(EXACT_CONSTRAINT_WORK, EXACT_TYPE_WORK - 1);
        assert!(matches!(type_short, Err(SelectionFailure::TypeResource)));
        assert!(slot.selection().is_none());

        let (exact, slot, constraints, types) = run(EXACT_CONSTRAINT_WORK, EXACT_TYPE_WORK);
        exact
            .expect("the exact pending-publication budgets should stage the occurrence")
            .publish()
            .expect("a preflighted exact occurrence should publish");
        assert_eq!(constraints, EXACT_CONSTRAINT_WORK);
        assert_eq!(types, EXACT_TYPE_WORK);
        assert_eq!(slot.method_arguments(), &[Type::Bool, Type::Int]);
        assert!(slot.selection().is_some());
    }

    #[test]
    fn conditional_method_rigidity_ingress_has_exact_atomic_retry_boundaries() {
        // One method argument, one occurrence record, one rigid argument, one
        // condition record, plus the two-record traversals of the retained
        // interface Int and fresh method Bool arguments.
        const EXACT_CONSTRAINT_WORK: usize = 8;
        // Only the interface argument is cloned at this ownership boundary.
        const EXACT_TYPE_WORK: usize = 1;
        let (interface, _, _) = ids();
        let source = SourceFile::new("method-rigidity-ingress.ash", "use")
            .expect("the ingress source should fit");
        let span = source
            .span(ByteRange::new(0, 3).expect("the ingress range should be ordered"))
            .expect("the ingress span should fit");
        let slot = EvidenceSlot::empty();
        let mut selector = EvidenceSelector::new();

        let mut short_constraints =
            InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK - 1);
        assert_eq!(
            selector.push_cloned_obligation(
                interface,
                &Type::Int,
                MethodObligationMetadata::new(
                    Box::new([Type::Bool]),
                    Some(MethodRigidityCondition::new(
                        Box::new([Type::Bool]),
                        MethodRigiditySite::application(span, span, span),
                    )),
                ),
                SelectionSite::plain(slot.handle(), span),
                &mut short_constraints,
                &mut TypeWorkBudget::with_limit(EXACT_TYPE_WORK),
            ),
            Err(SelectionFailure::ConstraintResource)
        );
        assert!(selector.pending.is_empty());
        assert_eq!(selector.pending_method_rigidity_count, 0);
        assert!(slot.selection().is_none());

        assert_eq!(
            selector.push_cloned_obligation(
                interface,
                &Type::Int,
                MethodObligationMetadata::new(
                    Box::new([Type::Bool]),
                    Some(MethodRigidityCondition::new(
                        Box::new([Type::Bool]),
                        MethodRigiditySite::application(span, span, span),
                    )),
                ),
                SelectionSite::plain(slot.handle(), span),
                &mut InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK),
                &mut TypeWorkBudget::with_limit(EXACT_TYPE_WORK - 1),
            ),
            Err(SelectionFailure::TypeResource)
        );
        assert!(selector.pending.is_empty());
        assert_eq!(selector.pending_method_rigidity_count, 0);
        assert!(slot.selection().is_none());

        let mut exact_constraints = InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK);
        let mut exact_types = TypeWorkBudget::with_limit(EXACT_TYPE_WORK);
        selector
            .push_cloned_obligation(
                interface,
                &Type::Int,
                MethodObligationMetadata::new(
                    Box::new([Type::Bool]),
                    Some(MethodRigidityCondition::new(
                        Box::new([Type::Bool]),
                        MethodRigiditySite::application(span, span, span),
                    )),
                ),
                SelectionSite::plain(slot.handle(), span),
                &mut exact_constraints,
                &mut exact_types,
            )
            .expect("the exact conditional ingress budgets should retain one obligation");
        assert_eq!(exact_constraints.used(), EXACT_CONSTRAINT_WORK);
        assert_eq!(exact_types.used(), EXACT_TYPE_WORK);
        assert_eq!(selector.pending.len(), 1);
        assert_eq!(selector.pending_method_rigidity_count, 1);
        assert!(slot.selection().is_none());
    }

    #[test]
    fn wide_conditional_method_rigidity_ingress_is_exact_and_atomic() {
        const WIDTH: usize = 1_024;
        const EXACT_CONSTRAINT_WORK: usize = WIDTH * 4 + 4;
        const EXACT_TYPE_WORK: usize = 1;
        let (interface, _, _) = ids();
        let source = SourceFile::new("wide-method-rigidity-ingress.ash", "use")
            .expect("the wide ingress source should fit");
        let span = source
            .span(ByteRange::new(0, 3).expect("the wide ingress range should be ordered"))
            .expect("the wide ingress span should fit");
        let slot = EvidenceSlot::empty();
        let make_arguments = || vec![Type::Bool; WIDTH].into_boxed_slice();

        let mut short = EvidenceSelector::new();
        assert_eq!(
            short.push_cloned_obligation(
                interface,
                &Type::Int,
                MethodObligationMetadata::new(
                    make_arguments(),
                    Some(MethodRigidityCondition::new(
                        make_arguments(),
                        MethodRigiditySite::application(span, span, span),
                    )),
                ),
                SelectionSite::plain(slot.handle(), span),
                &mut InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK - 1),
                &mut TypeWorkBudget::with_limit(EXACT_TYPE_WORK),
            ),
            Err(SelectionFailure::ConstraintResource)
        );
        assert!(short.pending.is_empty());
        assert!(slot.selection().is_none());

        let mut exact = EvidenceSelector::new();
        let mut exact_constraints = InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK);
        exact
            .push_cloned_obligation(
                interface,
                &Type::Int,
                MethodObligationMetadata::new(
                    make_arguments(),
                    Some(MethodRigidityCondition::new(
                        make_arguments(),
                        MethodRigiditySite::application(span, span, span),
                    )),
                ),
                SelectionSite::plain(slot.handle(), span),
                &mut exact_constraints,
                &mut TypeWorkBudget::with_limit(EXACT_TYPE_WORK),
            )
            .expect("the exact wide conditional ingress budget should fit");
        assert_eq!(exact_constraints.used(), EXACT_CONSTRAINT_WORK);
        assert_eq!(exact.pending.len(), 1);
        assert_eq!(exact.pending_method_rigidity_count, 1);
        assert!(slot.selection().is_none());
    }

    #[test]
    fn deep_method_rigidity_condition_failure_discards_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("deep-method-rigidity-condition".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let (interface, _, _) = ids();
                let source = SourceFile::new("deep-method-rigidity.ash", "use")
                    .expect("the deep condition source should fit");
                let span = source
                    .span(ByteRange::new(0, 3).expect("the deep range should be ordered"))
                    .expect("the deep span should fit");
                let slot = EvidenceSlot::empty();
                let mut selector = EvidenceSelector::new();
                assert_eq!(
                    selector.push_cloned_obligation(
                        interface,
                        &Type::Int,
                        MethodObligationMetadata::new(
                            Box::new([Type::Bool]),
                            Some(MethodRigidityCondition::new(
                                Box::new([deep_value_type(DEPTH)]),
                                MethodRigiditySite::application(span, span, span),
                            )),
                        ),
                        SelectionSite::plain(slot.handle(), span),
                        &mut InterfaceConstraintBudget::with_limit(0),
                        &mut TypeWorkBudget::default(),
                    ),
                    Err(SelectionFailure::ConstraintResource)
                );
                assert!(selector.pending.is_empty());
                assert!(slot.selection().is_none());
            })
            .expect("the small-stack condition thread should start")
            .join()
            .expect("a rejected deep rigidity condition must dismantle iteratively");
    }

    #[test]
    fn selected_deep_method_rigidity_condition_discards_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("selected-deep-method-rigidity-condition".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("selected-deep-method-rigidity.ash", "use")
                    .expect("the selected deep condition source should fit");
                let span = source
                    .span(ByteRange::new(0, 3).expect("the selected deep range is ordered"))
                    .expect("the selected deep span should fit");
                let mut selector = EvidenceSelector::new();
                selector.selected.push(SelectedOccurrence {
                    checked_argument: Type::Int,
                    method_arguments: Box::new([Type::Bool]),
                    selection: None,
                    slot: None,
                });
                selector.method_rigidities.push(SelectedMethodRigidity {
                    selected_index: 0,
                    condition: MethodRigidityCondition::new(
                        Box::new([deep_value_type(DEPTH)]),
                        MethodRigiditySite::application(span, span, span),
                    ),
                });
                drop(selector);
            })
            .expect("the selected small-stack condition thread should start")
            .join()
            .expect("a selected deep rigidity condition must dismantle iteratively");
    }

    #[test]
    fn conditional_method_rigidity_is_gated_by_selected_exact_current_identity() {
        let (interface, method, _) = ids();
        let module = interface.module();
        let current = ImplId::new(module, 0);
        let prerequisite = RequirementId::new(RequirementOwner::Impl(current), 0);
        let source = SourceFile::new("conditional-rigidity-selection.ash", "use")
            .expect("the conditional selection source should fit");
        let span = source
            .span(ByteRange::new(0, 3).expect("the conditional range should be ordered"))
            .expect("the conditional span should fit");

        let mut abstract_selector = EvidenceSelector::new();
        abstract_selector.add_interface_raw(
            interface,
            TypeVariableId::new(0),
            vec![(method, Type::Unit)],
        );
        abstract_selector.add_implementation_raw(implementation(
            current,
            interface,
            Vec::new(),
            Type::Int,
            vec![(prerequisite, interface, Type::Int)],
            vec![ImplMethodId::new(current, method)],
        ));
        let abstract_registry = abstract_selector.canonical_registry_for_test();
        abstract_selector
            .enter_implementation_scope(
                current,
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            )
            .expect("the identity-equal prerequisite scope should fit");
        let abstract_marker = abstract_selector.pending_marker();
        let abstract_slot = EvidenceSlot::empty();
        abstract_selector
            .push_cloned_obligation(
                interface,
                &Type::Int,
                MethodObligationMetadata::new(
                    Box::new([Type::Bool]),
                    Some(MethodRigidityCondition::new(
                        Box::new([Type::Int]),
                        MethodRigiditySite::application(span, span, span),
                    )),
                ),
                SelectionSite::plain(abstract_slot.handle(), span),
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            )
            .expect("the abstract-dispatch conditional occurrence should stage");
        abstract_selector
            .close_with_registry(
                &abstract_registry,
                abstract_marker,
                |ty, _| Ok(ty),
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            )
            .expect("abstract evidence should retain its existing priority");
        assert_eq!(abstract_selector.method_rigidity_count(), 0);
        assert_eq!(abstract_selector.pending_method_rigidity_count, 0);
        let abstract_selection = abstract_selector.selected[0]
            .selection
            .as_ref()
            .expect("the abstract occurrence should retain private selection");
        assert!(matches!(
            abstract_selection.node(abstract_selection.root()),
            Some(EvidenceNode::Abstract {
                requirement: selected,
                ..
            }) if selected == prerequisite
        ));
        assert!(abstract_slot.selection().is_none());
        abstract_selector
            .prepare_publication(
                |ty, _| Ok(ty),
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            )
            .expect("abstract dispatch needs no rigidity relation")
            .publish()
            .expect("the abstract occurrence should publish atomically");
        assert_eq!(abstract_slot.method_arguments(), &[Type::Bool]);

        let mut current_selector = EvidenceSelector::new();
        current_selector.add_interface_raw(
            interface,
            TypeVariableId::new(0),
            vec![(method, Type::Unit)],
        );
        current_selector.add_implementation_raw(implementation(
            current,
            interface,
            Vec::new(),
            Type::Int,
            Vec::new(),
            vec![ImplMethodId::new(current, method)],
        ));
        let current_registry = current_selector.canonical_registry_for_test();
        current_selector
            .enter_implementation_scope(
                current,
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            )
            .expect("the exact-current scope should fit");
        let current_marker = current_selector.pending_marker();
        let current_slot = EvidenceSlot::empty();
        current_selector
            .push_cloned_obligation(
                interface,
                &Type::Int,
                MethodObligationMetadata::new(
                    Box::new([Type::Bool]),
                    Some(MethodRigidityCondition::new(
                        Box::new([Type::Int]),
                        MethodRigiditySite::application(span, span, span),
                    )),
                ),
                SelectionSite::plain(current_slot.handle(), span),
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            )
            .expect("the exact-current conditional occurrence should stage");
        current_selector
            .close_with_registry(
                &current_registry,
                current_marker,
                |ty, _| Ok(ty),
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            )
            .expect("the exact-current implementation should select unchanged");
        assert_eq!(current_selector.method_rigidity_count(), 1);
        let check = current_selector
            .method_rigidity(0)
            .expect("exact-current selection should expose one private rigidity check");
        assert_eq!(check.method_arguments(), &[Type::Bool]);
        assert_eq!(check.rigid_arguments(), &[Type::Int]);
        assert_eq!(
            check.site(),
            MethodRigiditySite::application(span, span, span)
        );
        assert!(current_slot.selection().is_none());
        assert!(matches!(
            current_selector.prepare_publication(
                |ty, _| Ok(ty),
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            ),
            Err(SelectionFailure::InvalidState)
        ));
        assert!(current_slot.selection().is_none());
    }

    #[test]
    fn pending_method_argument_zonk_failure_discards_staged_types_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("pending-method-argument-zonk-failure".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let (interface, _, requirement) = ids();
                let mut builder = EvidenceSelectionBuilder::new();
                let root = builder
                    .push_abstract(requirement, &[], &mut InterfaceConstraintBudget::default())
                    .expect("one abstract evidence node should fit");
                let selection = builder
                    .finish(root, interface, Type::Int)
                    .expect("the pending selection should have one valid root");
                let slot = EvidenceSlot::empty();
                let mut selector = EvidenceSelector::new();
                selector.selected.push(SelectedOccurrence {
                    checked_argument: Type::Int,
                    method_arguments: Box::new([deep_value_type(DEPTH), Type::Bool]),
                    selection: Some(selection),
                    slot: Some(slot.handle()),
                });
                let mut zonk_calls = 0;
                let result = selector.prepare_publication(
                    |argument, _| {
                        zonk_calls += 1;
                        if zonk_calls == 3 {
                            discard_type_iteratively(argument);
                            Err(SelectionFailure::TypeResource)
                        } else {
                            Ok(argument)
                        }
                    },
                    &mut InterfaceConstraintBudget::default(),
                    &mut TypeWorkBudget::default(),
                );
                assert!(matches!(result, Err(SelectionFailure::TypeResource)));
                assert_eq!(zonk_calls, 3);
                assert!(slot.selection().is_none());
            })
            .expect("the small-stack publication thread should start")
            .join()
            .expect("staged method arguments must be dismantled iteratively on zonk failure");
    }

    #[test]
    fn interface_selector_retains_kinds_at_exact_atomic_boundaries() {
        fn exercise(imported: bool) {
            // One canonical binder lookup, three Kind-pair cells, and one
            // retained interface carrier record.
            const EXACT_CONSTRAINT_WORK: usize = 5;
            // One retained binder record plus the three nodes in Type -> Type.
            const EXACT_TYPE_WORK: usize = 4;
            let kind = Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));
            let fact = interface_fact_with_kind(kind.clone());
            let registry = registry_for_interface_fact(&fact);

            let mut measured_selector = EvidenceSelector::new();
            let mut measured_constraints = InterfaceConstraintBudget::default();
            let mut measured_types = TypeWorkBudget::default();
            let measured = if imported {
                measured_selector.add_imported_interface_fact(
                    &registry,
                    &fact,
                    &mut measured_constraints,
                    &mut measured_types,
                )
            } else {
                measured_selector.add_interface_fact(
                    &registry,
                    &fact,
                    &mut measured_constraints,
                    &mut measured_types,
                )
            };
            measured.expect("the generous interface ingress budgets should fit");
            assert_eq!(measured_constraints.used(), EXACT_CONSTRAINT_WORK);
            assert_eq!(measured_types.used(), EXACT_TYPE_WORK);

            let mut constraint_short_selector = EvidenceSelector::new();
            let constraint_short = if imported {
                constraint_short_selector.add_imported_interface_fact(
                    &registry,
                    &fact,
                    &mut InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK - 1),
                    &mut TypeWorkBudget::with_limit(EXACT_TYPE_WORK),
                )
            } else {
                constraint_short_selector.add_interface_fact(
                    &registry,
                    &fact,
                    &mut InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK - 1),
                    &mut TypeWorkBudget::with_limit(EXACT_TYPE_WORK),
                )
            };
            assert_eq!(constraint_short, Err(SelectionFailure::ConstraintResource));
            assert!(constraint_short_selector.interfaces.is_empty());
            assert!(constraint_short_selector.interface_indices.is_empty());
            assert!(constraint_short_selector.method_indices.is_empty());

            let mut short_selector = EvidenceSelector::new();
            let mut short_type = TypeWorkBudget::default();
            short_type
                .charge(crate::types::TYPE_WORK_LIMIT - (EXACT_TYPE_WORK - 1))
                .expect("test setup leaves one fewer retained unit");
            let short = if imported {
                short_selector.add_imported_interface_fact(
                    &registry,
                    &fact,
                    &mut InterfaceConstraintBudget::default(),
                    &mut short_type,
                )
            } else {
                short_selector.add_interface_fact(
                    &registry,
                    &fact,
                    &mut InterfaceConstraintBudget::default(),
                    &mut short_type,
                )
            };
            assert_eq!(short, Err(SelectionFailure::TypeResource));
            assert!(short_selector.interfaces.is_empty());
            assert!(short_selector.interface_indices.is_empty());
            assert!(short_selector.method_indices.is_empty());

            let mut exact_selector = EvidenceSelector::new();
            let mut exact_constraints =
                InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK);
            let mut exact_type = TypeWorkBudget::with_limit(EXACT_TYPE_WORK);
            let exact = if imported {
                exact_selector.add_imported_interface_fact(
                    &registry,
                    &fact,
                    &mut exact_constraints,
                    &mut exact_type,
                )
            } else {
                exact_selector.add_interface_fact(
                    &registry,
                    &fact,
                    &mut exact_constraints,
                    &mut exact_type,
                )
            };
            assert_eq!(exact, Ok(()));
            assert_eq!(exact_selector.interfaces[0].parameter_kind, kind);
            assert_eq!(exact_constraints.used(), EXACT_CONSTRAINT_WORK);
            assert_eq!(exact_type.charge(1), Err(()));
        }

        exercise(false);
        exercise(true);
    }

    #[test]
    fn duplicate_incoming_interface_method_id_is_rejected_without_publication() {
        let mut fact = interface_fact_with_kind(Kind::Type);
        let method = MethodId::new(fact.id, 0);
        fact.methods = (0..2)
            .map(|_| CheckedInterfaceMethodFact {
                id: method,
                spelling: "method".into(),
                type_parameters: Box::new([]),
                value_type: Type::Unit,
                origin: Origin::Source(fact.span),
                span: fact.span,
            })
            .collect::<Vec<_>>()
            .into_boxed_slice();
        let registry = registry_for_interface_fact(&fact);
        let mut selector = EvidenceSelector::new();

        assert_eq!(
            selector.add_interface_fact(
                &registry,
                &fact,
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            ),
            Err(SelectionFailure::InvalidState),
        );
        assert!(selector.interfaces.is_empty());
        assert!(selector.interface_indices.is_empty());
        assert!(selector.method_indices.is_empty());
    }

    #[test]
    fn local_and_imported_implementation_ingress_have_exact_atomic_boundaries() {
        // Both paths authenticate the head interface and structural scope,
        // retain one carrier record, and clone one primitive head. Imported
        // ingress additionally retains one authorization hop.
        const LOCAL_CONSTRAINT_WORK: usize = 7;
        const IMPORTED_CONSTRAINT_WORK: usize = LOCAL_CONSTRAINT_WORK + 1;
        const TYPE_WORK: usize = 1;

        let source = SourceFile::new("atomic-implementation-ingress.ash", "impl")
            .expect("the ingress fixture source should fit");
        let span = source
            .span(ByteRange::new(0, 4).expect("the ingress fixture range is ordered"))
            .expect("the ingress fixture span should fit");
        let module = ModuleId::new(53);
        let interface = InterfaceId::new(module, 0);
        let interface_parameter = TypeVariableId::resolved(module, 0);
        let implementation = ImplId::new(module, 0);

        let mut authority_selector = EvidenceSelector::new();
        authority_selector.add_interface_raw(interface, interface_parameter, Vec::new());
        let registry = authority_selector.canonical_registry_for_test();

        let imported = ImportedImplementationFact {
            fact: CheckedImplementationFact {
                id: implementation,
                interface,
                head_parameters: Box::new([]),
                argument: Type::Int,
                prerequisites: Box::new([]),
                methods: Box::new([]),
                origin: Origin::Source(span),
                span,
            },
            authorization: ImplementationAuthorization::from_hops(vec![ImplementationRouteHop {
                from: ModuleId::new(1),
                to: module,
                import_span: span,
            }]),
            public_authorization: None,
        };
        let resolved = ResolvedImplementation {
            id: implementation,
            public: false,
            interface: ResolvedInterfaceOccurrence {
                id: interface,
                spelling: "I".into(),
                origin: Origin::Source(span),
            },
            argument: ResolvedType {
                ty: Type::Int,
                provenance: ResolvedTypeProvenance::new(
                    vec![ResolvedTypeProvenanceNode::Fact(span)],
                    0,
                ),
                origin: Origin::Source(span),
                span,
            },
            head_parameters: Box::new([]),
            prerequisite_only_parameters: Box::new([]),
            prerequisites: Box::new([]),
            method_groups: Box::new([]),
            span,
        };
        let checked = CheckedImplementation {
            source_index: 0,
            id: implementation,
            interface,
            methods: Box::new([]),
        };

        let assert_empty = |selector: &EvidenceSelector| {
            assert!(selector.implementations.is_empty());
            assert!(selector.implementation_indices.is_empty());
            assert!(selector.implementation_candidates.is_empty());
        };

        let mut measured_imported = EvidenceSelector::new();
        measured_imported.add_interface_raw(interface, interface_parameter, Vec::new());
        let mut imported_constraints = InterfaceConstraintBudget::default();
        let mut imported_types = TypeWorkBudget::default();
        measured_imported
            .add_implementation_fact(
                &registry,
                &imported,
                &mut imported_constraints,
                &mut imported_types,
            )
            .expect("the measured imported implementation should publish");
        let imported_constraint_limit = imported_constraints.used();
        let imported_type_limit = imported_types.used();
        assert_eq!(imported_constraint_limit, IMPORTED_CONSTRAINT_WORK);
        assert_eq!(imported_type_limit, TYPE_WORK);

        let mut imported_constraint_short = EvidenceSelector::new();
        imported_constraint_short.add_interface_raw(interface, interface_parameter, Vec::new());
        assert_eq!(
            imported_constraint_short.add_implementation_fact(
                &registry,
                &imported,
                &mut InterfaceConstraintBudget::with_limit(imported_constraint_limit - 1),
                &mut TypeWorkBudget::with_limit(imported_type_limit),
            ),
            Err(SelectionFailure::ConstraintResource)
        );
        assert_empty(&imported_constraint_short);

        let mut imported_type_short = EvidenceSelector::new();
        imported_type_short.add_interface_raw(interface, interface_parameter, Vec::new());
        assert_eq!(
            imported_type_short.add_implementation_fact(
                &registry,
                &imported,
                &mut InterfaceConstraintBudget::with_limit(imported_constraint_limit),
                &mut TypeWorkBudget::with_limit(imported_type_limit - 1),
            ),
            Err(SelectionFailure::TypeResource)
        );
        assert_empty(&imported_type_short);

        let mut imported_exact = EvidenceSelector::new();
        imported_exact.add_interface_raw(interface, interface_parameter, Vec::new());
        imported_exact
            .add_implementation_fact(
                &registry,
                &imported,
                &mut InterfaceConstraintBudget::with_limit(IMPORTED_CONSTRAINT_WORK),
                &mut TypeWorkBudget::with_limit(TYPE_WORK),
            )
            .expect("the exact imported ingress budgets should publish atomically");

        let mut measured_local = EvidenceSelector::new();
        measured_local.add_interface_raw(interface, interface_parameter, Vec::new());
        let mut local_constraints = InterfaceConstraintBudget::default();
        let mut local_types = TypeWorkBudget::default();
        measured_local
            .add_local_implementation(
                &registry,
                &resolved,
                &checked,
                &mut local_constraints,
                &mut local_types,
            )
            .expect("the measured local implementation should publish");
        let local_constraint_limit = local_constraints.used();
        let local_type_limit = local_types.used();
        assert_eq!(local_constraint_limit, LOCAL_CONSTRAINT_WORK);
        assert_eq!(local_type_limit, TYPE_WORK);

        let mut local_constraint_short = EvidenceSelector::new();
        local_constraint_short.add_interface_raw(interface, interface_parameter, Vec::new());
        assert_eq!(
            local_constraint_short.add_local_implementation(
                &registry,
                &resolved,
                &checked,
                &mut InterfaceConstraintBudget::with_limit(local_constraint_limit - 1),
                &mut TypeWorkBudget::with_limit(local_type_limit),
            ),
            Err(SelectionFailure::ConstraintResource)
        );
        assert_empty(&local_constraint_short);

        let mut local_type_short = EvidenceSelector::new();
        local_type_short.add_interface_raw(interface, interface_parameter, Vec::new());
        assert_eq!(
            local_type_short.add_local_implementation(
                &registry,
                &resolved,
                &checked,
                &mut InterfaceConstraintBudget::with_limit(local_constraint_limit),
                &mut TypeWorkBudget::with_limit(local_type_limit - 1),
            ),
            Err(SelectionFailure::TypeResource)
        );
        assert_empty(&local_type_short);

        let mut local_exact = EvidenceSelector::new();
        local_exact.add_interface_raw(interface, interface_parameter, Vec::new());
        local_exact
            .add_local_implementation(
                &registry,
                &resolved,
                &checked,
                &mut InterfaceConstraintBudget::with_limit(LOCAL_CONSTRAINT_WORK),
                &mut TypeWorkBudget::with_limit(TYPE_WORK),
            )
            .expect("the exact local ingress budgets should publish atomically");
    }

    #[test]
    fn higher_kinded_implementation_ingress_has_exact_atomic_and_scope_boundaries() {
        // Candidate authentication is:
        //   1 parameter slot + 1 parameter scan + 1 canonical lookup
        //   + 2 relation slots + 2 interface lookups
        //   + 2 root slots + 2 * 6 application/child scope cells = 21.
        // Imported carrier retention adds 6 flat records (including one
        // method ID/span pair) and two 6-cell constraint traversals; local
        // retention adds 5 flat records and the same traversals. Retention
        // clones the two 3-node Types.
        const AUTHENTICATION_WORK: usize = 21;
        const RELATION_CONSTRAINT_WORK: usize = 6 + 6;
        const RELATION_TYPE_CELLS: usize = 3 + 3;
        const IMPORTED_CARRIER_WORK: usize = 6;
        const LOCAL_CARRIER_WORK: usize = 5;
        const IMPORTED_CONSTRAINT_WORK: usize =
            AUTHENTICATION_WORK + IMPORTED_CARRIER_WORK + RELATION_CONSTRAINT_WORK;
        const LOCAL_CONSTRAINT_WORK: usize =
            AUTHENTICATION_WORK + LOCAL_CARRIER_WORK + RELATION_CONSTRAINT_WORK;
        const RETAINED_TYPE_WORK: usize = RELATION_TYPE_CELLS;
        const LATE_TYPE_SHORT_WORK: usize = RETAINED_TYPE_WORK - 1;

        let source = SourceFile::new("higher-kinded-ingress.ash", "implementation")
            .expect("the higher-kinded ingress source should fit");
        let span = source
            .span(ByteRange::new(0, 14).expect("the ingress range is ordered"))
            .expect("the ingress span should fit");
        let module = ModuleId::new(93);
        let interface = InterfaceId::new(module, 0);
        let interface_parameter = TypeVariableId::resolved(module, 0);
        let function = TypeVariableId::resolved(module, 1);
        let outside = TypeVariableId::resolved(module, 2);
        let implementation = ImplId::new(module, 0);
        let method = MethodId::new(interface, 0);
        let implementation_method = ImplMethodId::new(implementation, method);
        let method_binder = BinderId::resolved(module, 10);
        let prerequisite = RequirementId::new(RequirementOwner::Impl(implementation), 0);
        let function_kind = Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));
        let registry = ResolvedRegistry::new(Vec::new(), Vec::new())
            .with_additional_type_variables([
                ResolvedTypeVariable {
                    id: interface_parameter,
                    spelling: "A".into(),
                    kind: Kind::Type,
                    origin: Origin::Source(span),
                },
                ResolvedTypeVariable {
                    id: function,
                    spelling: "F".into(),
                    kind: function_kind.clone(),
                    origin: Origin::Source(span),
                },
                ResolvedTypeVariable {
                    id: outside,
                    spelling: "G".into(),
                    kind: function_kind.clone(),
                    origin: Origin::Source(span),
                },
            ]);
        let parameter = |id| ResolvedTypeVariable {
            id,
            spelling: if id == function { "F" } else { "G" }.into(),
            kind: function_kind.clone(),
            origin: Origin::Source(span),
        };
        let application =
            |id, argument| Type::Application(Box::new(Type::Variable(id)), Box::new(argument));
        let resolved_type = |ty| ResolvedType {
            ty,
            provenance: ResolvedTypeProvenance::new(
                vec![ResolvedTypeProvenanceNode::Fact(span)],
                0,
            ),
            origin: Origin::Source(span),
            span,
        };
        let imported = |parameters: Vec<ResolvedTypeVariable>, prerequisite_argument| {
            ImportedImplementationFact {
                fact: CheckedImplementationFact {
                    id: implementation,
                    interface,
                    head_parameters: parameters.into_boxed_slice(),
                    argument: application(function, Type::Int),
                    prerequisites: vec![CheckedRequirement {
                        id: prerequisite,
                        interface,
                        argument: prerequisite_argument,
                        origin: Origin::Source(span),
                        span,
                    }]
                    .into_boxed_slice(),
                    methods: vec![CheckedImplementationMethodFact {
                        id: implementation_method,
                        method,
                        binder: method_binder,
                        scheme: ConstrainedScheme {
                            type_parameters: Box::new([]),
                            requirements: Box::new([]),
                            value_type: Type::Unit,
                        },
                        head_type_parameter_count: 0,
                        origin: Origin::Source(span),
                        span,
                    }]
                    .into_boxed_slice(),
                    origin: Origin::Source(span),
                    span,
                },
                authorization: ImplementationAuthorization::from_hops(vec![
                    ImplementationRouteHop {
                        from: ModuleId::new(1),
                        to: module,
                        import_span: span,
                    },
                ]),
                public_authorization: None,
            }
        };
        let resolved =
            |parameters: Vec<ResolvedTypeVariable>, prerequisite_argument| ResolvedImplementation {
                id: implementation,
                public: false,
                interface: ResolvedInterfaceOccurrence {
                    id: interface,
                    spelling: "Construct".into(),
                    origin: Origin::Source(span),
                },
                argument: resolved_type(application(function, Type::Int)),
                head_parameters: parameters.into_boxed_slice(),
                prerequisite_only_parameters: Box::new([]),
                prerequisites: vec![ResolvedRequirement {
                    id: prerequisite,
                    interface: ResolvedInterfaceOccurrence {
                        id: interface,
                        spelling: "Construct".into(),
                        origin: Origin::Source(span),
                    },
                    argument: resolved_type(prerequisite_argument),
                    span,
                }]
                .into_boxed_slice(),
                method_groups: vec![ResolvedImplementationMethodGroup {
                    method: Some(method),
                    identity: Some(implementation_method),
                    binder: Binder {
                        id: method_binder,
                        spelling: "construct".into(),
                        origin: Origin::Source(span),
                    },
                    equations: Box::new([]),
                    span,
                }]
                .into_boxed_slice(),
                span,
            };
        let checked = CheckedImplementation {
            source_index: 0,
            id: implementation,
            interface,
            methods: vec![CheckedImplMethod {
                source_group: 0,
                id: implementation_method,
                method,
                binder: method_binder,
            }]
            .into_boxed_slice(),
        };
        let valid_imported =
            || imported(vec![parameter(function)], application(function, Type::Bool));
        let valid_resolved =
            || resolved(vec![parameter(function)], application(function, Type::Bool));
        let selector = || {
            let mut selector = EvidenceSelector::new();
            selector.add_interface_raw(interface, interface_parameter, Vec::new());
            selector
        };
        let assert_empty = |selector: &EvidenceSelector| {
            assert!(selector.implementations.is_empty());
            assert!(selector.implementation_indices.is_empty());
            assert!(selector.implementation_candidates.is_empty());
        };

        let mut measured_imported = selector();
        let mut imported_constraints = InterfaceConstraintBudget::default();
        let mut imported_types = TypeWorkBudget::default();
        measured_imported
            .add_implementation_fact(
                &registry,
                &valid_imported(),
                &mut imported_constraints,
                &mut imported_types,
            )
            .expect("the measured imported higher-kinded fact should publish");
        assert_eq!(imported_constraints.used(), IMPORTED_CONSTRAINT_WORK);
        assert_eq!(imported_types.used(), RETAINED_TYPE_WORK);

        let mut imported_constraint_short = selector();
        assert_eq!(
            imported_constraint_short.add_implementation_fact(
                &registry,
                &valid_imported(),
                &mut InterfaceConstraintBudget::with_limit(IMPORTED_CONSTRAINT_WORK - 1),
                &mut TypeWorkBudget::with_limit(RETAINED_TYPE_WORK),
            ),
            Err(SelectionFailure::ConstraintResource)
        );
        assert_empty(&imported_constraint_short);

        let mut imported_type_short = selector();
        let mut imported_late_type_work = TypeWorkBudget::with_limit(RETAINED_TYPE_WORK - 1);
        assert_eq!(
            imported_type_short.add_implementation_fact(
                &registry,
                &valid_imported(),
                &mut InterfaceConstraintBudget::with_limit(IMPORTED_CONSTRAINT_WORK),
                &mut imported_late_type_work,
            ),
            Err(SelectionFailure::TypeResource)
        );
        assert_eq!(
            imported_late_type_work.used(),
            LATE_TYPE_SHORT_WORK,
            "the prerequisite and partial head clones must remain local on late failure"
        );
        assert_empty(&imported_type_short);

        let mut imported_exact = selector();
        imported_exact
            .add_implementation_fact(
                &registry,
                &valid_imported(),
                &mut InterfaceConstraintBudget::with_limit(IMPORTED_CONSTRAINT_WORK),
                &mut TypeWorkBudget::with_limit(RETAINED_TYPE_WORK),
            )
            .expect("the exact imported higher-kinded ingress budgets should fit");

        let mut measured_local = selector();
        let mut local_constraints = InterfaceConstraintBudget::default();
        let mut local_types = TypeWorkBudget::default();
        measured_local
            .add_local_implementation(
                &registry,
                &valid_resolved(),
                &checked,
                &mut local_constraints,
                &mut local_types,
            )
            .expect("the measured local higher-kinded fact should publish");
        assert_eq!(local_constraints.used(), LOCAL_CONSTRAINT_WORK);
        assert_eq!(local_types.used(), RETAINED_TYPE_WORK);

        let mut local_constraint_short = selector();
        assert_eq!(
            local_constraint_short.add_local_implementation(
                &registry,
                &valid_resolved(),
                &checked,
                &mut InterfaceConstraintBudget::with_limit(LOCAL_CONSTRAINT_WORK - 1),
                &mut TypeWorkBudget::with_limit(RETAINED_TYPE_WORK),
            ),
            Err(SelectionFailure::ConstraintResource)
        );
        assert_empty(&local_constraint_short);

        let mut local_type_short = selector();
        let mut local_late_type_work = TypeWorkBudget::with_limit(RETAINED_TYPE_WORK - 1);
        assert_eq!(
            local_type_short.add_local_implementation(
                &registry,
                &valid_resolved(),
                &checked,
                &mut InterfaceConstraintBudget::with_limit(LOCAL_CONSTRAINT_WORK),
                &mut local_late_type_work,
            ),
            Err(SelectionFailure::TypeResource)
        );
        assert_eq!(
            local_late_type_work.used(),
            LATE_TYPE_SHORT_WORK,
            "the local prerequisite and partial head clones must not publish"
        );
        assert_empty(&local_type_short);

        let mut local_exact = selector();
        local_exact
            .add_local_implementation(
                &registry,
                &valid_resolved(),
                &checked,
                &mut InterfaceConstraintBudget::with_limit(LOCAL_CONSTRAINT_WORK),
                &mut TypeWorkBudget::with_limit(RETAINED_TYPE_WORK),
            )
            .expect("the exact local higher-kinded ingress budgets should fit");

        let mut missing = selector();
        let missing_registry = ResolvedRegistry::new(Vec::new(), Vec::new())
            .with_additional_type_variables([ResolvedTypeVariable {
                id: interface_parameter,
                spelling: "A".into(),
                kind: Kind::Type,
                origin: Origin::Source(span),
            }]);
        assert_eq!(
            missing.add_implementation_fact(
                &missing_registry,
                &valid_imported(),
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            ),
            Err(SelectionFailure::InvalidState)
        );
        assert_empty(&missing);

        let mut duplicate = selector();
        assert_eq!(
            duplicate.add_local_implementation(
                &registry,
                &resolved(
                    vec![parameter(function), parameter(function)],
                    application(function, Type::Bool),
                ),
                &checked,
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            ),
            Err(SelectionFailure::InvalidState)
        );
        assert_empty(&duplicate);

        let mut out_of_scope = selector();
        assert_eq!(
            out_of_scope.add_implementation_fact(
                &registry,
                &imported(vec![parameter(function)], application(outside, Type::Bool)),
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            ),
            Err(SelectionFailure::InvalidState)
        );
        assert_empty(&out_of_scope);
    }

    #[test]
    fn imported_selector_kind_failure_is_stack_safe_and_atomic() {
        const DEPTH: usize = 32_768;
        const KIND_NODES: usize = 2 * DEPTH + 1;
        const EXACT_WORK: usize = 1 + KIND_NODES;

        std::thread::Builder::new()
            .name("deep-selector-kind-retention".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut kind = Kind::Type;
                for _ in 0..DEPTH {
                    kind = Kind::Arrow(Box::new(Kind::Type), Box::new(kind));
                }
                let fact = interface_fact_with_kind(kind);
                let registry = registry_for_interface_fact(&fact);
                let mut selector = EvidenceSelector::new();
                let mut type_work = TypeWorkBudget::default();
                type_work
                    .charge(crate::types::TYPE_WORK_LIMIT - (EXACT_WORK - 1))
                    .expect("test setup leaves one fewer retained unit");
                assert_eq!(
                    selector.add_imported_interface_fact(
                        &registry,
                        &fact,
                        &mut InterfaceConstraintBudget::default(),
                        &mut type_work,
                    ),
                    Err(SelectionFailure::TypeResource)
                );
                assert!(selector.interfaces.is_empty());
                assert!(selector.interface_indices.is_empty());
            })
            .expect("deep selector thread")
            .join()
            .expect("deep selector retention and teardown stay iterative");
    }

    fn implementation(
        id: ImplId,
        interface: InterfaceId,
        parameters: Vec<TypeVariableId>,
        argument: Type,
        prerequisites: Vec<(RequirementId, InterfaceId, Type)>,
        methods: Vec<ImplMethodId>,
    ) -> ImplementationEntry {
        let file = SourceFile::new("implementation-selection-fixture.ash", "x")
            .expect("implementation fixture source");
        let span = file
            .span(ByteRange::new(0, 1).expect("implementation fixture range"))
            .expect("implementation fixture span");
        let method_spans = vec![span; methods.len()];
        ImplementationEntry {
            id,
            interface,
            parameters: parameters.into_boxed_slice(),
            argument,
            prerequisites: prerequisites
                .into_iter()
                .map(|(id, interface, argument)| RequirementEntry {
                    id,
                    interface,
                    argument,
                })
                .collect(),
            methods: methods.into_boxed_slice(),
            span,
            method_spans,
            import_spans: Box::new([]),
        }
    }

    #[test]
    fn exact_abstract_requirement_shadows_concrete_search() {
        let (interface, method, requirement) = ids();
        let parameter = TypeVariableId::new(0);
        let mut selector = EvidenceSelector::new();
        selector.add_interface_raw(interface, parameter, vec![(method, Type::Unit)]);
        let concrete = ImplId::new(ModuleId::new(1), 0);
        selector.add_implementation_raw(implementation(
            concrete,
            interface,
            Vec::new(),
            Type::Int,
            Vec::new(),
            vec![ImplMethodId::new(concrete, method)],
        ));
        selector
            .push_abstract(
                requirement,
                interface,
                Type::Int,
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("abstract fixture");

        let mut measured_constraints = InterfaceConstraintBudget::default();
        let mut measured_types = TypeWorkBudget::default();
        let selection = selector
            .select(
                interface,
                &Type::Int,
                &mut measured_constraints,
                &mut measured_types,
            )
            .expect("exact abstract evidence");

        assert_eq!(
            selection.node(selection.root()),
            Some(EvidenceNode::Abstract {
                requirement,
                methods: &[method],
            })
        );
        assert_eq!(
            selector.select(
                interface,
                &Type::Int,
                &mut InterfaceConstraintBudget::with_limit(measured_constraints.used() - 1),
                &mut TypeWorkBudget::with_limit(measured_types.used()),
            ),
            Err(SelectionFailure::ConstraintResource)
        );
        selector
            .select(
                interface,
                &Type::Int,
                &mut InterfaceConstraintBudget::with_limit(measured_constraints.used()),
                &mut TypeWorkBudget::with_limit(measured_types.used()),
            )
            .expect("exact abstract-selection budgets");
    }

    #[test]
    fn generic_implementation_instantiates_prerequisites_in_order() {
        let module = ModuleId::new(2);
        let interface = InterfaceId::new(module, 0);
        let method = MethodId::new(interface, 0);
        let parameter = TypeVariableId::resolved(module, 0);
        let option = NominalTypeId::new(module, 0);
        let base = ImplId::new(module, 0);
        let generic = ImplId::new(module, 1);
        let prerequisite = RequirementId::new(RequirementOwner::Impl(generic), 0);
        let mut selector = EvidenceSelector::new();
        selector.add_interface_raw(interface, parameter, vec![(method, Type::Unit)]);
        selector.add_implementation_raw(implementation(
            base,
            interface,
            Vec::new(),
            Type::Int,
            Vec::new(),
            vec![ImplMethodId::new(base, method)],
        ));
        selector.add_implementation_raw(implementation(
            generic,
            interface,
            vec![parameter],
            Type::apply_arguments(Type::Nominal(option), [Type::Variable(parameter)]),
            vec![(prerequisite, interface, Type::Variable(parameter))],
            vec![ImplMethodId::new(generic, method)],
        ));

        let goal = Type::apply_arguments(Type::Nominal(option), [Type::Int]);
        let mut measured_constraints = InterfaceConstraintBudget::default();
        let mut measured_types = TypeWorkBudget::default();
        let selection = selector
            .select(
                interface,
                &goal,
                &mut measured_constraints,
                &mut measured_types,
            )
            .expect("generic evidence");

        let EvidenceNode::Implementation {
            implementation,
            substitution,
            prerequisites,
            methods,
        } = selection
            .node(selection.root())
            .expect("root implementation")
        else {
            panic!("concrete root")
        };
        assert_eq!(implementation, generic);
        assert_eq!(substitution.len(), 1);
        assert_eq!(substitution[0].parameter(), parameter);
        assert_eq!(substitution[0].argument(), &Type::Int);
        assert_eq!(methods, &[ImplMethodId::new(generic, method)]);
        assert_eq!(prerequisites.len(), 1);
        assert!(matches!(
            selection.node(prerequisites[0]),
            Some(EvidenceNode::Implementation {
                implementation,
                substitution: [],
                prerequisites: [],
                ..
            }) if implementation == base
        ));
        let constraint_limit = measured_constraints.used();
        let type_limit = measured_types.used();
        assert!(constraint_limit > 0);
        assert!(type_limit > 0);
        assert_eq!(
            selector.select(
                interface,
                &goal,
                &mut InterfaceConstraintBudget::with_limit(constraint_limit),
                &mut TypeWorkBudget::with_limit(type_limit - 1),
            ),
            Err(SelectionFailure::TypeResource)
        );
        assert_eq!(
            selector.select(
                interface,
                &goal,
                &mut InterfaceConstraintBudget::with_limit(constraint_limit - 1),
                &mut TypeWorkBudget::with_limit(type_limit),
            ),
            Err(SelectionFailure::ConstraintResource)
        );
        selector
            .select(
                interface,
                &goal,
                &mut InterfaceConstraintBudget::with_limit(constraint_limit),
                &mut TypeWorkBudget::with_limit(type_limit),
            )
            .expect("exact prerequisite-selection budgets");
    }

    #[test]
    fn full_higher_kinded_selection_has_exact_atomic_dual_limits() {
        // Constraint work is the additive sum of one close/initial task pair,
        // two canonical Option<T> goal environments, three head inspections
        // (ground mismatch, higher-kinded match, ground prerequisite), root
        // and prerequisite scheduling, two Finish/result nodes, and checked
        // argument publication.
        const CLOSE_AND_INITIAL_TASK_WORK: usize = 2;
        const GOAL_ENVIRONMENT_WORK: usize = 2 * 8;
        const HEAD_MATCH_WORK: usize = 18 + 32 + 18;
        const GOAL_CONTROL_AND_SCHEDULING_WORK: usize = 28 + 19;
        const FINISH_AND_RESULT_WORK: usize = 7 + 9;
        const CHECKED_ARGUMENT_PUBLICATION_WORK: usize = 7;
        // Two retained pending-publication carrier records plus the six-cell
        // exact comparison between checked and selected Option<Int> goals.
        const PENDING_PUBLICATION_WORK: usize = 2 + 6;
        const EXACT_CONSTRAINT_WORK: usize = CLOSE_AND_INITIAL_TASK_WORK
            + GOAL_ENVIRONMENT_WORK
            + HEAD_MATCH_WORK
            + GOAL_CONTROL_AND_SCHEDULING_WORK
            + FINISH_AND_RESULT_WORK
            + CHECKED_ARGUMENT_PUBLICATION_WORK
            + PENDING_PUBLICATION_WORK;

        // Type work retains the initial goal clone, both canonical nominal
        // environments, the authenticated F -> Option substitution, its
        // replacement index/value, the instantiated prerequisite, and the
        // final selection argument.
        const INITIAL_GOAL_CLONE_WORK: usize = 3;
        const GOAL_ENVIRONMENT_TYPE_WORK: usize = 2 * 4;
        const MATCHED_SUBSTITUTION_TYPE_WORK: usize = 1;
        const REPLACEMENT_INDEX_AND_VALUE_WORK: usize = 2;
        const PREREQUISITE_SUBSTITUTION_WORK: usize = 3;
        const SELECTION_ARGUMENT_WORK: usize = 3;
        const EXACT_TYPE_WORK: usize = INITIAL_GOAL_CLONE_WORK
            + GOAL_ENVIRONMENT_TYPE_WORK
            + MATCHED_SUBSTITUTION_TYPE_WORK
            + REPLACEMENT_INDEX_AND_VALUE_WORK
            + PREREQUISITE_SUBSTITUTION_WORK
            + SELECTION_ARGUMENT_WORK;

        let source = SourceFile::new("higher-kinded-selection-budget.ash", "selection")
            .expect("the higher-kinded selection source should fit");
        let span = source
            .span(ByteRange::new(0, 9).expect("the selection range is ordered"))
            .expect("the selection span should fit");
        let module = ModuleId::new(94);
        let interface = InterfaceId::new(module, 0);
        let method = MethodId::new(interface, 0);
        let interface_parameter = TypeVariableId::resolved(module, 0);
        let function = TypeVariableId::resolved(module, 1);
        let nominal_parameter = TypeVariableId::resolved(module, 2);
        let option = NominalTypeId::new(module, 0);
        let base = ImplId::new(module, 0);
        let generic = ImplId::new(module, 1);
        let prerequisite = RequirementId::new(RequirementOwner::Impl(generic), 0);
        let apply = |function, argument| Type::Application(Box::new(function), Box::new(argument));
        let option_of = |argument| apply(Type::Nominal(option), argument);
        let function_of = |argument| apply(Type::Variable(function), argument);
        let setup = || {
            let registry = ResolvedRegistry::new(
                vec![ResolvedNominalType {
                    id: option,
                    spelling: "Option".into(),
                    constructors: Box::new([]),
                    origin: Origin::Source(span),
                }],
                Vec::new(),
            )
            .with_type_parameters(vec![(
                option,
                vec![ResolvedTypeVariable {
                    id: nominal_parameter,
                    spelling: "A".into(),
                    kind: Kind::Type,
                    origin: Origin::Source(span),
                }],
            )])
            .with_additional_type_variables([
                ResolvedTypeVariable {
                    id: interface_parameter,
                    spelling: "A".into(),
                    kind: Kind::Type,
                    origin: Origin::Source(span),
                },
                ResolvedTypeVariable {
                    id: function,
                    spelling: "F".into(),
                    kind: Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)),
                    origin: Origin::Source(span),
                },
            ]);
            let mut selector = EvidenceSelector::new();
            selector.add_interface_raw(interface, interface_parameter, vec![(method, Type::Unit)]);
            selector.add_implementation_raw(implementation(
                base,
                interface,
                Vec::new(),
                option_of(Type::Bool),
                Vec::new(),
                vec![ImplMethodId::new(base, method)],
            ));
            selector.add_implementation_raw(implementation(
                generic,
                interface,
                vec![function],
                function_of(Type::Int),
                vec![(prerequisite, interface, function_of(Type::Bool))],
                vec![ImplMethodId::new(generic, method)],
            ));
            (selector, registry)
        };
        let run = |constraint_limit, type_limit| {
            let (mut selector, registry) = setup();
            let marker = selector.pending_marker();
            let slot = EvidenceSlot::empty();
            selector
                .push_obligation(
                    interface,
                    option_of(Type::Int),
                    slot.handle(),
                    span,
                    &mut InterfaceConstraintBudget::default(),
                )
                .expect("the full-selection obligation should queue");
            let mut constraints = InterfaceConstraintBudget::with_limit(constraint_limit);
            let mut types = TypeWorkBudget::with_limit(type_limit);
            let result = selector.close_with_registry(
                &registry,
                marker,
                |ty, _| Ok(ty),
                &mut constraints,
                &mut types,
            );
            let result = result.and_then(|()| {
                let publication = selector
                    .prepare_publication(|ty, _| Ok(ty), &mut constraints, &mut types)
                    .map_err(|failure| SelectionError {
                        failure,
                        span: None,
                        declaration_span: None,
                        import_span: None,
                        causes: Vec::new(),
                    })?;
                publication.publish().map_err(|failure| SelectionError {
                    failure,
                    span: None,
                    declaration_span: None,
                    import_span: None,
                    causes: Vec::new(),
                })
            });
            (result, slot, constraints.used(), types.used())
        };

        let (measured, slot, measured_constraints, measured_types) = run(usize::MAX, usize::MAX);
        measured.expect("the measured higher-kinded selection should fill its slot");
        let (_, selection) = slot.filled().expect("the measured slot should be filled");
        let EvidenceNode::Implementation {
            implementation,
            substitution,
            prerequisites,
            methods,
        } = selection
            .node(selection.root())
            .expect("the measured selection should retain a root")
        else {
            panic!("the higher-kinded candidate should produce concrete evidence")
        };
        assert_eq!(implementation, generic);
        assert_eq!(substitution.len(), 1);
        assert_eq!(substitution[0].parameter(), function);
        assert_eq!(substitution[0].argument(), &Type::Nominal(option));
        assert_eq!(methods, &[ImplMethodId::new(generic, method)]);
        assert!(matches!(
            selection.node(prerequisites[0]),
            Some(EvidenceNode::Implementation {
                implementation,
                prerequisites: [],
                ..
            }) if implementation == base
        ));
        assert_eq!(measured_constraints, EXACT_CONSTRAINT_WORK);
        assert_eq!(measured_types, EXACT_TYPE_WORK);

        let (constraint_short, constraint_slot, _, _) =
            run(EXACT_CONSTRAINT_WORK - 1, EXACT_TYPE_WORK);
        assert_eq!(
            constraint_short,
            Err(SelectionError {
                failure: SelectionFailure::ConstraintResource,
                span: None,
                declaration_span: None,
                import_span: None,
                causes: Vec::new(),
            })
        );
        assert!(constraint_slot.selection().is_none());

        let (type_short, type_slot, _, _) = run(EXACT_CONSTRAINT_WORK, EXACT_TYPE_WORK - 1);
        assert_eq!(
            type_short,
            Err(SelectionError {
                failure: SelectionFailure::TypeResource,
                span: Some(span),
                declaration_span: None,
                import_span: None,
                causes: Vec::new(),
            })
        );
        assert!(type_slot.selection().is_none());

        let (exact, exact_slot, exact_constraints, exact_types) =
            run(EXACT_CONSTRAINT_WORK, EXACT_TYPE_WORK);
        exact.expect("the exact higher-kinded selection budgets should fill the slot");
        assert!(exact_slot.selection().is_some());
        assert_eq!(exact_constraints, EXACT_CONSTRAINT_WORK);
        assert_eq!(exact_types, EXACT_TYPE_WORK);
    }

    #[test]
    fn exact_current_implementation_uses_declared_abstract_prerequisites() {
        let module = ModuleId::new(3);
        let interface = InterfaceId::new(module, 0);
        let method = MethodId::new(interface, 0);
        let parameter = TypeVariableId::resolved(module, 0);
        let option = NominalTypeId::new(module, 0);
        let current = ImplId::new(module, 0);
        let prerequisite = RequirementId::new(RequirementOwner::Impl(current), 0);
        let mut selector = EvidenceSelector::new();
        selector.add_interface_raw(interface, parameter, vec![(method, Type::Unit)]);
        selector.add_implementation_raw(implementation(
            current,
            interface,
            vec![parameter],
            Type::apply_arguments(Type::Nominal(option), [Type::Variable(parameter)]),
            vec![(prerequisite, interface, Type::Variable(parameter))],
            vec![ImplMethodId::new(current, method)],
        ));
        selector
            .enter_implementation_scope(
                current,
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            )
            .expect("implementation evidence scope");

        let component = selector
            .select(
                interface,
                &Type::Variable(parameter),
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            )
            .expect("declared prerequisite evidence");
        assert_eq!(
            component.node(component.root()),
            Some(EvidenceNode::Abstract {
                requirement: prerequisite,
                methods: &[method],
            })
        );

        let current_argument =
            Type::apply_arguments(Type::Nominal(option), [Type::Variable(parameter)]);
        let mut measured_constraints = InterfaceConstraintBudget::default();
        let mut measured_types = TypeWorkBudget::default();
        let selection = selector
            .select(
                interface,
                &current_argument,
                &mut measured_constraints,
                &mut measured_types,
            )
            .expect("rigid self evidence");
        let EvidenceNode::Implementation { prerequisites, .. } = selection
            .node(selection.root())
            .expect("current implementation")
        else {
            panic!("implementation root")
        };
        assert_eq!(prerequisites.len(), 1);
        assert_eq!(
            selection.node(prerequisites[0]),
            Some(EvidenceNode::Abstract {
                requirement: prerequisite,
                methods: &[method],
            })
        );
        let constraint_limit = measured_constraints.used();
        let type_limit = measured_types.used();
        assert!(constraint_limit > 0);
        assert!(type_limit > 0);
        assert_eq!(
            selector.select(
                interface,
                &current_argument,
                &mut InterfaceConstraintBudget::with_limit(constraint_limit),
                &mut TypeWorkBudget::with_limit(type_limit - 1),
            ),
            Err(SelectionFailure::TypeResource)
        );
        assert_eq!(
            selector.select(
                interface,
                &current_argument,
                &mut InterfaceConstraintBudget::with_limit(constraint_limit - 1),
                &mut TypeWorkBudget::with_limit(type_limit),
            ),
            Err(SelectionFailure::ConstraintResource)
        );
        selector
            .select(
                interface,
                &current_argument,
                &mut InterfaceConstraintBudget::with_limit(constraint_limit),
                &mut TypeWorkBudget::with_limit(type_limit),
            )
            .expect("exact current-implementation budgets");
    }

    #[test]
    fn undetermined_goal_is_ambiguous_before_candidate_or_active_goal_work() {
        let (interface, method, requirement) = ids();
        let mut selector = EvidenceSelector::new();
        selector.add_interface_raw(
            interface,
            TypeVariableId::new(0),
            vec![(method, Type::Unit)],
        );
        let candidate = ImplId::new(ModuleId::new(1), 0);
        selector.add_implementation_raw(implementation(
            candidate,
            interface,
            Vec::new(),
            Type::Int,
            Vec::new(),
            vec![ImplMethodId::new(candidate, method)],
        ));

        let mut causes = Vec::new();
        assert_eq!(
            selector.select_owned_for_test(
                interface,
                Type::Inference(crate::types::InferenceVariableId::new(0)),
                &mut causes,
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::with_limit(0),
            ),
            Err(SelectionFailure::Reason(InterfaceReason::Ambiguous))
        );
        assert_eq!(causes.len(), 1);
        assert_eq!(causes[0].kind(), SelectionCauseKind::Interface);

        let nested_inference = Type::Function(
            Box::new(Type::Inference(crate::types::InferenceVariableId::new(1))),
            Box::new(Type::Int),
        );
        selector
            .push_abstract(
                requirement,
                interface,
                nested_inference.clone(),
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the abstract fixture should fit");
        let mut nested_causes = Vec::new();
        assert_eq!(
            selector.select_owned_for_test(
                interface,
                nested_inference,
                &mut nested_causes,
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            ),
            Err(SelectionFailure::Reason(InterfaceReason::Ambiguous))
        );
        assert_eq!(nested_causes.len(), 1);
        assert_eq!(nested_causes[0].kind(), SelectionCauseKind::Interface);

        for (inference, nested_application) in [
            (
                crate::types::InferenceVariableId::new(2),
                Type::Application(
                    Box::new(Type::Inference(crate::types::InferenceVariableId::new(2))),
                    Box::new(Type::Int),
                ),
            ),
            (
                crate::types::InferenceVariableId::new(3),
                Type::Application(
                    Box::new(Type::Int),
                    Box::new(Type::Inference(crate::types::InferenceVariableId::new(3))),
                ),
            ),
        ] {
            let mut application_causes = Vec::new();
            assert_eq!(
                selector.select_owned_for_test(
                    interface,
                    nested_application,
                    &mut application_causes,
                    &mut InterfaceConstraintBudget::default(),
                    &mut TypeWorkBudget::default(),
                ),
                Err(SelectionFailure::Reason(InterfaceReason::Ambiguous)),
                "nested inference {inference:?} must fail before abstract/current/candidate/active work"
            );
            assert_eq!(application_causes.len(), 1);
            assert_eq!(application_causes[0].kind(), SelectionCauseKind::Interface);
        }

        assert_eq!(
            selector.select(
                interface,
                &Type::Inference(crate::types::InferenceVariableId::new(0)),
                &mut InterfaceConstraintBudget::with_limit(0),
                &mut TypeWorkBudget::with_limit(1),
            ),
            Err(SelectionFailure::ConstraintResource)
        );
        assert_eq!(
            selector.select(
                interface,
                &Type::Inference(crate::types::InferenceVariableId::new(0)),
                &mut InterfaceConstraintBudget::with_limit(1),
                &mut TypeWorkBudget::with_limit(1),
            ),
            Err(SelectionFailure::Reason(InterfaceReason::Ambiguous))
        );
    }

    #[test]
    fn goal_key_and_exact_type_matching_have_exact_deep_constraint_boundaries() {
        let interface = InterfaceId::new(ModuleId::new(10), 0);
        let argument = Type::Function(
            Box::new(Type::Tuple(vec![Type::Int, Type::Bool].into_boxed_slice())),
            Box::new(Type::Unit),
        );

        let mut key_budget = InterfaceConstraintBudget::default();
        let key = goal_key(interface, &argument, &mut key_budget).expect("measured goal key");
        let key_limit = key_budget.used();
        assert_eq!(key.cells.len(), 5);
        assert_eq!(
            goal_key(
                interface,
                &argument,
                &mut InterfaceConstraintBudget::with_limit(key_limit - 1),
            ),
            Err(SelectionFailure::ConstraintResource)
        );
        goal_key(
            interface,
            &argument,
            &mut InterfaceConstraintBudget::with_limit(key_limit),
        )
        .expect("exact goal-key budget");
        assert_eq!(
            charge_goal_key(
                &key,
                &mut InterfaceConstraintBudget::with_limit(key.cells.len()),
            ),
            Err(SelectionFailure::ConstraintResource)
        );
        let mut exact_active =
            InterfaceConstraintBudget::with_limit(key.cells.len().saturating_add(1));
        charge_goal_key(&key, &mut exact_active).expect("exact active-goal operation budget");
        assert_eq!(exact_active.used(), key.cells.len().saturating_add(1));

        let mut equality_budget = InterfaceConstraintBudget::default();
        assert_eq!(
            same_type_with_constraint_budget(&argument, &argument, &mut equality_budget),
            Ok(true)
        );
        let equality_limit = equality_budget.used();
        assert_eq!(
            same_type_with_constraint_budget(
                &argument,
                &argument,
                &mut InterfaceConstraintBudget::with_limit(equality_limit - 1),
            ),
            Err(())
        );
        assert_eq!(
            same_type_with_constraint_budget(
                &argument,
                &argument,
                &mut InterfaceConstraintBudget::with_limit(equality_limit),
            ),
            Ok(true)
        );
        assert_eq!(
            charge_candidate_inspection(&mut InterfaceConstraintBudget::with_limit(0)),
            Err(SelectionFailure::ConstraintResource)
        );
        charge_candidate_inspection(&mut InterfaceConstraintBudget::with_limit(1))
            .expect("one candidate-inspection unit");
        assert_eq!(
            charge_prerequisite_goal(&Type::Int, &mut InterfaceConstraintBudget::with_limit(2),),
            Err(SelectionFailure::ConstraintResource)
        );
        let mut exact_prerequisite = InterfaceConstraintBudget::with_limit(3);
        charge_prerequisite_goal(&Type::Int, &mut exact_prerequisite)
            .expect("one edge plus the retained prerequisite argument");
        assert_eq!(exact_prerequisite.used(), 3);
    }

    #[test]
    fn absent_candidate_is_unsatisfied() {
        let (interface, method, _) = ids();
        let mut selector = EvidenceSelector::new();
        selector.add_interface_raw(
            interface,
            TypeVariableId::new(0),
            vec![(method, Type::Unit)],
        );
        let mut measured = InterfaceConstraintBudget::default();
        assert_eq!(
            selector.select(
                interface,
                &Type::Int,
                &mut measured,
                &mut TypeWorkBudget::default(),
            ),
            Err(SelectionFailure::Reason(InterfaceReason::Unsatisfied))
        );
        assert_eq!(
            selector.select(
                interface,
                &Type::Int,
                &mut InterfaceConstraintBudget::with_limit(measured.used() - 1),
                &mut TypeWorkBudget::default(),
            ),
            Err(SelectionFailure::ConstraintResource)
        );
        assert_eq!(
            selector.select(
                interface,
                &Type::Int,
                &mut InterfaceConstraintBudget::with_limit(measured.used()),
                &mut TypeWorkBudget::default(),
            ),
            Err(SelectionFailure::Reason(InterfaceReason::Unsatisfied))
        );
    }

    #[test]
    fn every_same_interface_candidate_inspection_is_constraint_bounded() {
        const REJECTED: u32 = 128;
        // The rigid goal environment is discovered once per selection task.
        // Each rejected ground candidate owns one ordered inspection and six
        // first-order structural preflight/mismatch cells.
        const REJECTED_CANDIDATE_WORK: usize = 1 + 6;
        let (interface, method, _) = ids();
        let matching = ImplId::new(ModuleId::new(1), 1);
        let mut baseline = EvidenceSelector::new();
        baseline.add_interface_raw(
            interface,
            TypeVariableId::new(0),
            vec![(method, Type::Unit)],
        );
        baseline.add_implementation_raw(implementation(
            matching,
            interface,
            Vec::new(),
            Type::Int,
            Vec::new(),
            vec![ImplMethodId::new(matching, method)],
        ));
        let mut baseline_work = InterfaceConstraintBudget::default();
        baseline
            .select(
                interface,
                &Type::Int,
                &mut baseline_work,
                &mut TypeWorkBudget::default(),
            )
            .expect("first candidate");

        let mut selector = EvidenceSelector::new();
        selector.add_interface_raw(
            interface,
            TypeVariableId::new(0),
            vec![(method, Type::Unit)],
        );
        for declaration in 0..REJECTED {
            let candidate = ImplId::new(ModuleId::new(1), declaration);
            selector.add_implementation_raw(implementation(
                candidate,
                interface,
                Vec::new(),
                Type::Bool,
                Vec::new(),
                vec![ImplMethodId::new(candidate, method)],
            ));
        }
        let candidate = ImplId::new(ModuleId::new(1), REJECTED);
        selector.add_implementation_raw(implementation(
            candidate,
            interface,
            Vec::new(),
            Type::Int,
            Vec::new(),
            vec![ImplMethodId::new(candidate, method)],
        ));
        let mut measured = InterfaceConstraintBudget::default();
        selector
            .select(
                interface,
                &Type::Int,
                &mut measured,
                &mut TypeWorkBudget::default(),
            )
            .expect("second candidate");
        assert_eq!(
            measured.used(),
            baseline_work.used()
                + usize::try_from(REJECTED).expect("fixture width") * REJECTED_CANDIDATE_WORK,
            "each rejected ground candidate owns only inspection and structural comparison",
        );
        assert_eq!(
            selector.select(
                interface,
                &Type::Int,
                &mut InterfaceConstraintBudget::with_limit(measured.used() - 1),
                &mut TypeWorkBudget::default(),
            ),
            Err(SelectionFailure::ConstraintResource)
        );
    }

    #[test]
    fn ground_prerequisite_reentry_is_a_cycle_before_resource_exhaustion() {
        let module = ModuleId::new(4);
        let left = InterfaceId::new(module, 0);
        let right = InterfaceId::new(module, 1);
        let left_method = MethodId::new(left, 0);
        let right_method = MethodId::new(right, 0);
        let left_impl = ImplId::new(module, 0);
        let right_impl = ImplId::new(module, 1);
        let mut selector = EvidenceSelector::new();
        selector.add_interface_raw(
            left,
            TypeVariableId::new(0),
            vec![(left_method, Type::Unit)],
        );
        selector.add_interface_raw(
            right,
            TypeVariableId::new(1),
            vec![(right_method, Type::Unit)],
        );
        selector.add_implementation_raw(implementation(
            left_impl,
            left,
            Vec::new(),
            Type::Int,
            vec![(
                RequirementId::new(RequirementOwner::Impl(left_impl), 0),
                right,
                Type::Int,
            )],
            vec![ImplMethodId::new(left_impl, left_method)],
        ));
        selector.add_implementation_raw(implementation(
            right_impl,
            right,
            Vec::new(),
            Type::Int,
            vec![(
                RequirementId::new(RequirementOwner::Impl(right_impl), 0),
                left,
                Type::Int,
            )],
            vec![ImplMethodId::new(right_impl, right_method)],
        ));
        let mut measured = InterfaceConstraintBudget::default();
        assert_eq!(
            selector.select(
                left,
                &Type::Int,
                &mut measured,
                &mut TypeWorkBudget::default(),
            ),
            Err(SelectionFailure::Reason(InterfaceReason::Cycle))
        );
        let before_reentry = measured.used();
        assert_eq!(
            selector.select(
                left,
                &Type::Int,
                &mut InterfaceConstraintBudget::with_limit(before_reentry),
                &mut TypeWorkBudget::default(),
            ),
            Err(SelectionFailure::Reason(InterfaceReason::Cycle))
        );
    }

    #[test]
    fn failing_sibling_prerequisites_retain_only_the_first_declaration_order_path() {
        let module = ModuleId::new(14);
        let root = InterfaceId::new(module, 0);
        let first = InterfaceId::new(module, 1);
        let second = InterfaceId::new(module, 2);
        let root_method = MethodId::new(root, 0);
        let root_impl = ImplId::new(module, 0);
        let mut selector = EvidenceSelector::new();
        selector.add_interface_raw(
            root,
            TypeVariableId::new(0),
            vec![(root_method, Type::Unit)],
        );
        selector.add_interface_raw(first, TypeVariableId::new(1), Vec::new());
        selector.add_interface_raw(second, TypeVariableId::new(2), Vec::new());
        selector.add_implementation_raw(implementation(
            root_impl,
            root,
            Vec::new(),
            Type::Int,
            vec![
                (
                    RequirementId::new(RequirementOwner::Impl(root_impl), 0),
                    first,
                    Type::Int,
                ),
                (
                    RequirementId::new(RequirementOwner::Impl(root_impl), 1),
                    second,
                    Type::Int,
                ),
            ],
            vec![ImplMethodId::new(root_impl, root_method)],
        ));
        let root_span = selector.interface_entry(root).expect("root interface").span;
        let first_span = selector
            .interface_entry(first)
            .expect("first prerequisite interface")
            .span;
        let second_span = selector
            .interface_entry(second)
            .expect("second prerequisite interface")
            .span;
        let mut causes = Vec::new();

        let failure = selector.select_owned_for_test(
            root,
            Type::Int,
            &mut causes,
            &mut InterfaceConstraintBudget::default(),
            &mut TypeWorkBudget::default(),
        );

        assert_eq!(
            failure,
            Err(SelectionFailure::Reason(InterfaceReason::Unsatisfied))
        );
        let interface_spans = causes
            .iter()
            .filter(|cause| cause.kind() == SelectionCauseKind::Interface)
            .map(|cause| cause.span())
            .collect::<Vec<_>>();
        assert_eq!(interface_spans, vec![root_span, first_span]);
        assert!(!interface_spans.contains(&second_span));
    }

    #[test]
    fn concrete_selection_has_exact_constraint_and_type_work_boundaries() {
        let (interface, method, _) = ids();
        let implementation_id = ImplId::new(ModuleId::new(1), 0);
        let mut selector = EvidenceSelector::new();
        selector.add_interface_raw(
            interface,
            TypeVariableId::new(0),
            vec![(method, Type::Unit)],
        );
        selector.add_implementation_raw(implementation(
            implementation_id,
            interface,
            Vec::new(),
            Type::Int,
            Vec::new(),
            vec![ImplMethodId::new(implementation_id, method)],
        ));
        let mut constraints = InterfaceConstraintBudget::default();
        let mut types = TypeWorkBudget::default();
        selector
            .select(interface, &Type::Int, &mut constraints, &mut types)
            .expect("measured selection");
        let constraint_limit = constraints.used();
        let type_limit = types.used();
        assert_eq!(
            selector.select(
                interface,
                &Type::Int,
                &mut InterfaceConstraintBudget::with_limit(constraint_limit - 1),
                &mut TypeWorkBudget::with_limit(type_limit),
            ),
            Err(SelectionFailure::ConstraintResource)
        );
        assert_eq!(
            selector.select(
                interface,
                &Type::Int,
                &mut InterfaceConstraintBudget::with_limit(constraint_limit),
                &mut TypeWorkBudget::with_limit(type_limit - 1),
            ),
            Err(SelectionFailure::TypeResource)
        );
        selector
            .select(
                interface,
                &Type::Int,
                &mut InterfaceConstraintBudget::with_limit(constraint_limit),
                &mut TypeWorkBudget::with_limit(type_limit),
            )
            .expect("exact budgets");
    }

    #[test]
    fn transitive_import_causes_have_proportional_exact_boundaries() {
        let source = SourceFile::new("transitive-selection.ash", "abcdefghijklmnop")
            .expect("the transitive selection source should fit");
        let span = |start, end| {
            source
                .span(ByteRange::new(start, end).expect("the span should be ordered"))
                .expect("the span should belong to the fixture")
        };
        let first_hop = span(0, 2);
        let second_hop = span(3, 5);
        let definition = span(6, 8);
        let interface = InterfaceId::new(ModuleId::new(11), 0);
        let implementation_id = ImplId::new(ModuleId::new(11), 0);
        let imported = |hops| ImportedImplementationFact {
            fact: CheckedImplementationFact {
                id: implementation_id,
                interface,
                head_parameters: Box::new([]),
                argument: Type::Int,
                prerequisites: Box::new([]),
                methods: Box::new([]),
                origin: Origin::Source(definition),
                span: definition,
            },
            authorization: ImplementationAuthorization::from_hops(hops),
            public_authorization: None,
        };
        let one_hop = imported(vec![ImplementationRouteHop {
            from: ModuleId::new(1),
            to: ModuleId::new(11),
            import_span: first_hop,
        }]);
        let two_hops = imported(vec![
            ImplementationRouteHop {
                from: ModuleId::new(1),
                to: ModuleId::new(10),
                import_span: first_hop,
            },
            ImplementationRouteHop {
                from: ModuleId::new(10),
                to: ModuleId::new(11),
                import_span: second_hop,
            },
        ]);

        let mut one_selector = EvidenceSelector::new();
        one_selector.add_interface_raw(interface, TypeVariableId::new(0), Vec::new());
        let one_registry = one_selector.canonical_registry_for_test();
        let mut one_retention = InterfaceConstraintBudget::default();
        one_selector
            .add_implementation_fact(
                &one_registry,
                &one_hop,
                &mut one_retention,
                &mut TypeWorkBudget::default(),
            )
            .expect("one imported hop should be retained");

        let mut selector = EvidenceSelector::new();
        selector.add_interface_raw(interface, TypeVariableId::new(0), Vec::new());
        let registry = selector.canonical_registry_for_test();
        let mut retention = InterfaceConstraintBudget::default();
        let mut retention_types = TypeWorkBudget::default();
        selector
            .add_implementation_fact(&registry, &two_hops, &mut retention, &mut retention_types)
            .expect("both imported hops should be retained");
        assert_eq!(retention.used(), one_retention.used() + 1);
        let mut short_selector = EvidenceSelector::new();
        short_selector.add_interface_raw(interface, TypeVariableId::new(0), Vec::new());
        let short_registry = short_selector.canonical_registry_for_test();
        assert_eq!(
            short_selector.add_implementation_fact(
                &short_registry,
                &two_hops,
                &mut InterfaceConstraintBudget::with_limit(retention.used() - 1),
                &mut TypeWorkBudget::with_limit(retention_types.used()),
            ),
            Err(SelectionFailure::ConstraintResource)
        );
        let mut exact_selector = EvidenceSelector::new();
        exact_selector.add_interface_raw(interface, TypeVariableId::new(0), Vec::new());
        let exact_registry = exact_selector.canonical_registry_for_test();
        exact_selector
            .add_implementation_fact(
                &exact_registry,
                &two_hops,
                &mut InterfaceConstraintBudget::with_limit(retention.used()),
                &mut TypeWorkBudget::with_limit(retention_types.used()),
            )
            .expect("the exact two-hop retention budget should admit the implementation");

        let mut one_causes = Vec::new();
        let mut one_selection_work = InterfaceConstraintBudget::default();
        let mut one_selection_types = TypeWorkBudget::default();
        let (checked_argument, _) = one_selector
            .select_owned_for_test(
                interface,
                Type::Int,
                &mut one_causes,
                &mut one_selection_work,
                &mut one_selection_types,
            )
            .expect("the one-hop implementation should select");
        discard_type_iteratively(checked_argument);

        let mut causes = Vec::new();
        let mut selection_work = InterfaceConstraintBudget::default();
        let mut selection_types = TypeWorkBudget::default();
        let (checked_argument, _) = selector
            .select_owned_for_test(
                interface,
                Type::Int,
                &mut causes,
                &mut selection_work,
                &mut selection_types,
            )
            .expect("the transitive imported implementation should select");
        discard_type_iteratively(checked_argument);
        assert_eq!(selection_work.used(), one_selection_work.used() + 1);
        assert_eq!(selection_types.used(), one_selection_types.used());
        let import_causes = causes
            .iter()
            .filter(|cause| cause.kind() == SelectionCauseKind::ImplementationImport)
            .map(|cause| cause.span())
            .collect::<Vec<_>>();
        assert_eq!(import_causes, vec![first_hop, second_hop]);

        assert_eq!(
            selector.select_owned_for_test(
                interface,
                Type::Int,
                &mut Vec::new(),
                &mut InterfaceConstraintBudget::with_limit(selection_work.used() - 1),
                &mut TypeWorkBudget::with_limit(selection_types.used()),
            ),
            Err(SelectionFailure::ConstraintResource)
        );
        let (checked_argument, _) = selector
            .select_owned_for_test(
                interface,
                Type::Int,
                &mut Vec::new(),
                &mut InterfaceConstraintBudget::with_limit(selection_work.used()),
                &mut TypeWorkBudget::with_limit(selection_types.used()),
            )
            .expect("the exact cause-retention budget should select");
        discard_type_iteratively(checked_argument);
    }

    #[test]
    fn pending_obligation_retention_has_an_exact_constraint_boundary() {
        let (interface, _, _) = ids();
        let file = SourceFile::new("pending.ash", "x").expect("source");
        let span = file
            .span(ByteRange::new(0, 1).expect("range"))
            .expect("span");
        let mut short = EvidenceSelector::new();
        assert_eq!(
            short.push_obligation(
                interface,
                Type::Int,
                EvidenceSlot::empty().handle(),
                span,
                &mut InterfaceConstraintBudget::with_limit(2),
            ),
            Err(SelectionFailure::ConstraintResource)
        );
        let mut exact = EvidenceSelector::new();
        exact
            .push_obligation(
                interface,
                Type::Int,
                EvidenceSlot::empty().handle(),
                span,
                &mut InterfaceConstraintBudget::with_limit(3),
            )
            .expect("exact pending budget");
    }

    #[test]
    fn closing_obligation_transfer_has_an_exact_width_boundary_without_allocation() {
        const WIDTH: usize = 128;
        let (interface, _, _) = ids();
        let file = SourceFile::new("pending-close.ash", "x").expect("source");
        let span = file
            .span(ByteRange::new(0, 1).expect("range"))
            .expect("span");
        let mut selector = EvidenceSelector::new();
        let mut setup = InterfaceConstraintBudget::default();
        for _ in 0..WIDTH {
            selector
                .push_obligation(
                    interface,
                    Type::Int,
                    EvidenceSlot::empty().handle(),
                    span,
                    &mut setup,
                )
                .expect("pending fixture");
        }

        let short = selector
            .close(
                0,
                |argument, _| Ok(argument),
                &mut InterfaceConstraintBudget::with_limit(WIDTH - 1),
                &mut TypeWorkBudget::default(),
            )
            .expect_err("one missing transfer unit must reject before moving obligations");
        assert_eq!(short.failure(), SelectionFailure::ConstraintResource);
        assert_eq!(short.span(), None);
        assert_eq!(selector.pending.len(), WIDTH);

        let task_short = selector
            .close(
                0,
                |argument, _| Ok(argument),
                &mut InterfaceConstraintBudget::with_limit(WIDTH),
                &mut TypeWorkBudget::default(),
            )
            .expect_err("one missing task-slot unit should reject the first obligation");
        assert_eq!(task_short.failure(), SelectionFailure::ConstraintResource);
        assert_eq!(task_short.span(), Some(span));
        assert_eq!(selector.pending.len(), WIDTH - 1);

        let reached_first = selector
            .close(
                0,
                |argument, _| Ok(argument),
                &mut InterfaceConstraintBudget::with_limit(WIDTH),
                &mut TypeWorkBudget::default(),
            )
            .expect_err("transfer plus one task slot should reach the first obligation");
        assert_eq!(reached_first.failure(), SelectionFailure::InvalidState);
        assert_eq!(reached_first.span(), Some(span));
    }

    #[test]
    fn closure_zonks_then_fills_the_exact_structural_slot() {
        let (interface, method, _) = ids();
        let concrete = ImplId::new(ModuleId::new(1), 0);
        let mut selector = EvidenceSelector::new();
        selector.add_interface_raw(
            interface,
            TypeVariableId::new(0),
            vec![(method, Type::Unit)],
        );
        selector.add_implementation_raw(implementation(
            concrete,
            interface,
            Vec::new(),
            Type::Int,
            Vec::new(),
            vec![ImplMethodId::new(concrete, method)],
        ));
        let slot = EvidenceSlot::empty();
        let file = SourceFile::new("selection.ash", "x").expect("source");
        let span = file
            .span(ByteRange::new(0, 1).expect("range"))
            .expect("span");
        let mut constraints = InterfaceConstraintBudget::default();
        selector
            .push_obligation(
                interface,
                Type::Inference(crate::types::InferenceVariableId::new(0)),
                slot.handle(),
                span,
                &mut constraints,
            )
            .expect("pending obligation");

        let mut type_work = TypeWorkBudget::default();
        let close_constraint_start = constraints.used();
        selector
            .close(
                0,
                |argument, _type_work| {
                    discard_type_iteratively(argument);
                    Ok(Type::Int)
                },
                &mut constraints,
                &mut type_work,
            )
            .expect("selected closure");
        let exact_constraint_work = constraints.used() - close_constraint_start;
        let exact_type_work = type_work.used();

        let (checked_argument, selection) = slot.filled().expect("filled exact slot");
        assert_eq!(checked_argument, &Type::Int);
        assert_eq!(selection.argument(), &Type::Int);
        assert!(matches!(
            selection.node(selection.root()),
            Some(EvidenceNode::Implementation { implementation, .. })
                if implementation == concrete
        ));

        let short_slot = EvidenceSlot::empty();
        selector
            .push_obligation(
                interface,
                Type::Inference(crate::types::InferenceVariableId::new(1)),
                short_slot.handle(),
                span,
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the one-short fixture should retain its obligation");
        assert_eq!(
            selector
                .close(
                    0,
                    |argument, _type_work| {
                        discard_type_iteratively(argument);
                        Ok(Type::Int)
                    },
                    &mut InterfaceConstraintBudget::default(),
                    &mut TypeWorkBudget::with_limit(exact_type_work - 1),
                )
                .expect_err("one type-work unit below checked-goal retention must fail")
                .failure(),
            SelectionFailure::TypeResource,
        );
        assert!(short_slot.selection().is_none());

        let constraint_short_slot = EvidenceSlot::empty();
        selector
            .push_obligation(
                interface,
                Type::Inference(crate::types::InferenceVariableId::new(3)),
                constraint_short_slot.handle(),
                span,
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the constraint-short fixture should retain its obligation");
        assert_eq!(
            selector
                .close(
                    0,
                    |argument, _type_work| {
                        discard_type_iteratively(argument);
                        Ok(Type::Int)
                    },
                    &mut InterfaceConstraintBudget::with_limit(exact_constraint_work - 1),
                    &mut TypeWorkBudget::with_limit(exact_type_work),
                )
                .expect_err("one constraint unit below task/result retention must fail")
                .failure(),
            SelectionFailure::ConstraintResource,
        );
        assert!(constraint_short_slot.selection().is_none());

        let exact_slot = EvidenceSlot::empty();
        selector
            .push_obligation(
                interface,
                Type::Inference(crate::types::InferenceVariableId::new(2)),
                exact_slot.handle(),
                span,
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the exact fixture should retain its obligation");
        let mut exact_constraints = InterfaceConstraintBudget::with_limit(exact_constraint_work);
        let mut exact = TypeWorkBudget::with_limit(exact_type_work);
        selector
            .close(
                0,
                |argument, _type_work| {
                    discard_type_iteratively(argument);
                    Ok(Type::Int)
                },
                &mut exact_constraints,
                &mut exact,
            )
            .expect("the exact checked-goal retention budget should fill its slot");
        assert_eq!(exact.used(), exact_type_work);
        assert_eq!(exact_constraints.used(), exact_constraint_work);
        assert!(matches!(
            exact_slot.filled(),
            Some((Type::Int, selected)) if selected.argument() == &Type::Int
        ));
    }

    #[test]
    fn deep_ground_prerequisite_chain_selects_and_drops_on_a_small_stack() {
        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(|| {
                const DEPTH: usize = 1_000;
                let module = ModuleId::new(9);
                let mut selector = EvidenceSelector::new();
                for index in 0..DEPTH {
                    let declaration = u32::try_from(index).expect("interface index");
                    let interface = InterfaceId::new(module, declaration);
                    let method = MethodId::new(interface, 0);
                    let implementation_id = ImplId::new(module, declaration);
                    selector.add_interface_raw(
                        interface,
                        TypeVariableId::generated(declaration),
                        vec![(method, Type::Unit)],
                    );
                    let prerequisites = if index + 1 == DEPTH {
                        Vec::new()
                    } else {
                        let next = InterfaceId::new(module, declaration + 1);
                        vec![(
                            RequirementId::new(RequirementOwner::Impl(implementation_id), 0),
                            next,
                            Type::Int,
                        )]
                    };
                    selector.add_implementation_raw(implementation(
                        implementation_id,
                        interface,
                        Vec::new(),
                        Type::Int,
                        prerequisites,
                        vec![ImplMethodId::new(implementation_id, method)],
                    ));
                }
                let selection = selector
                    .select(
                        InterfaceId::new(module, 0),
                        &Type::Int,
                        &mut InterfaceConstraintBudget::default(),
                        &mut TypeWorkBudget::default(),
                    )
                    .expect("deep flat selection");
                assert_eq!(selection.node_count(), DEPTH);
            })
            .expect("small-stack selection thread")
            .join()
            .expect("selection and drop stay iterative");
    }

    fn deep_value_type(depth: usize) -> Type {
        let mut ty = Type::Unit;
        for _ in 0..depth {
            ty = Type::Function(Box::new(Type::Unit), Box::new(ty));
        }
        ty
    }

    #[test]
    fn owned_evidence_inputs_fail_without_recursive_drop_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("owned-evidence-input-failure".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let (interface, _, requirement) = ids();
                let source = SourceFile::new("owned-evidence.ash", "x")
                    .expect("the evidence fixture should fit");
                let span = source
                    .span(ByteRange::new(0, 1).expect("the range should be ordered"))
                    .expect("the range should belong to the fixture");
                let mut selector = EvidenceSelector::new();
                assert_eq!(
                    selector.push_abstract(
                        requirement,
                        interface,
                        deep_value_type(DEPTH),
                        &mut InterfaceConstraintBudget::with_limit(0),
                    ),
                    Err(SelectionFailure::ConstraintResource),
                );
                let slot = EvidenceSlot::empty();
                assert_eq!(
                    selector.push_owned_obligation(
                        interface,
                        deep_value_type(DEPTH),
                        SelectionSite::plain(slot.handle(), span),
                        &mut InterfaceConstraintBudget::with_limit(0),
                    ),
                    Err(SelectionFailure::ConstraintResource),
                );
            })
            .expect("the small-stack evidence thread should start")
            .join()
            .expect("owned evidence inputs must be dismantled iteratively on failure");
    }

    #[test]
    fn checked_argument_late_constraint_failure_drops_deep_type_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("checked-argument-late-failure".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let module = ModuleId::new(12);
                let interface = InterfaceId::new(module, 0);
                let method = MethodId::new(interface, 0);
                let parameter = TypeVariableId::resolved(module, 0);
                let implementation_id = ImplId::new(module, 0);
                let mut selector = EvidenceSelector::new();
                selector.add_interface_raw(interface, parameter, vec![(method, Type::Unit)]);
                selector.add_implementation_raw(implementation(
                    implementation_id,
                    interface,
                    vec![parameter],
                    Type::Variable(parameter),
                    Vec::new(),
                    vec![ImplMethodId::new(implementation_id, method)],
                ));

                let mut measured_constraints = InterfaceConstraintBudget::with_limit(usize::MAX);
                let mut measured_types = TypeWorkBudget::with_limit(usize::MAX);
                let (checked_argument, selection) = selector
                    .select_owned_for_test(
                        interface,
                        deep_value_type(DEPTH),
                        &mut Vec::new(),
                        &mut measured_constraints,
                        &mut measured_types,
                    )
                    .expect("the measured deep selection should succeed");
                discard_type_iteratively(checked_argument);
                drop(selection);

                assert_eq!(
                    selector.select_owned_for_test(
                        interface,
                        deep_value_type(DEPTH),
                        &mut Vec::new(),
                        &mut InterfaceConstraintBudget::with_limit(
                            measured_constraints.used() - 1,
                        ),
                        &mut TypeWorkBudget::with_limit(measured_types.used()),
                    ),
                    Err(SelectionFailure::ConstraintResource),
                );
            })
            .expect("the checked-argument failure thread should start")
            .join()
            .expect("late checked-argument failure must stay iterative");
    }

    #[test]
    fn duplicate_deep_replacement_is_dismantled_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("duplicate-evidence-replacement".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let parameter = TypeVariableId::new(0);
                let substitutions = [
                    EvidenceSubstitution::new(parameter, deep_value_type(DEPTH)),
                    EvidenceSubstitution::new(parameter, deep_value_type(DEPTH)),
                ];
                assert!(matches!(
                    replacement_map(&substitutions, &mut TypeWorkBudget::default()),
                    Err(SelectionFailure::InvalidState),
                ));
            })
            .expect("the duplicate-replacement thread should start")
            .join()
            .expect("duplicate replacement teardown must stay iterative");
    }

    #[test]
    fn replacement_map_charges_indexes_and_cloned_arguments_exactly_before_publication() {
        const INDEX_RECORDS: usize = 2;
        const ARGUMENT_NODES: usize = 1 + 3;
        const EXACT_TYPE_WORK: usize = INDEX_RECORDS + ARGUMENT_NODES;

        let module = ModuleId::new(92);
        let first = TypeVariableId::resolved(module, 0);
        let second = TypeVariableId::resolved(module, 1);
        let option = NominalTypeId::new(module, 0);
        let substitutions = [
            EvidenceSubstitution::new(first, Type::Int),
            EvidenceSubstitution::new(
                second,
                Type::Application(Box::new(Type::Nominal(option)), Box::new(Type::Int)),
            ),
        ];

        let mut index_short = TypeWorkBudget::with_limit(INDEX_RECORDS - 1);
        assert!(matches!(
            replacement_map(&substitutions, &mut index_short),
            Err(SelectionFailure::TypeResource)
        ));
        assert_eq!(
            index_short.used(),
            0,
            "the atomic index-record charge must fail before reserve or cloning"
        );

        assert!(
            matches!(
                replacement_map(
                    &substitutions,
                    &mut TypeWorkBudget::with_limit(EXACT_TYPE_WORK - 1),
                ),
                Err(SelectionFailure::TypeResource)
            ),
            "one missing retained Type cell must not publish a replacement map"
        );
        assert_eq!(substitutions[0].argument(), &Type::Int);
        assert!(matches!(
            substitutions[1].argument(),
            Type::Application(function, argument)
                if **function == Type::Nominal(option) && **argument == Type::Int
        ));

        let mut exact = TypeWorkBudget::with_limit(EXACT_TYPE_WORK);
        let replacements = replacement_map(&substitutions, &mut exact)
            .expect("the index records plus both cloned arguments should fit exactly");
        assert_eq!(replacements.as_map().get(&first), Some(&Type::Int));
        assert_eq!(
            replacements.as_map().get(&second),
            Some(&Type::Application(
                Box::new(Type::Nominal(option)),
                Box::new(Type::Int),
            ))
        );
        assert_eq!(exact.used(), EXACT_TYPE_WORK);
        assert_eq!(exact.charge(1), Err(()));
    }
}
#[cfg(test)]
mod replacement_owner_api_tests {
    #[test]
    fn recursive_type_replacements_do_not_bypass_the_owner_api() {
        let source: String = include_str!("evidence.rs")
            .chars()
            .filter(|character| !character.is_whitespace())
            .collect();
        let raw_field = ["replacements", ".values"].concat();
        assert!(!source.contains(&raw_field));
        let raw_insert = [".values", ".insert("].concat();
        let raw_reserve = [".values", ".try_reserve("].concat();
        assert_eq!(source.matches(&raw_insert).count(), 1);
        assert_eq!(source.matches(&raw_reserve).count(), 1);
        let broad_mutation = ["impl", "DerefMut", "for", "ReplacementMap"].concat();
        assert!(!source.contains(&broad_mutation));
    }
}
