//! Checked interface-evidence selection.

use std::{collections::HashMap, sync::Arc};

use crate::{
    interface::{
        CheckedImplementation, ConstrainedScheme, EvidenceSelection, EvidenceSelectionBuilder,
        EvidenceSlotHandle, EvidenceSubstitution, HeadMatchFailure, ImplId, ImplMethodId,
        InterfaceConstraintBudget, InterfaceId, InterfaceReason, MethodId, RequirementId,
        match_implementation_head,
    },
    resolved::{
        BinderId, CheckedGlobalScheme, CheckedInterfaceFact, ImportedGlobalScheme,
        ImportedImplementationFact, ResolvedImplementation,
    },
    source::Span,
    types::{
        NominalTypeId, Type, TypeVariableId, TypeWorkBudget, clone_type_with_budget,
        discard_type_iteratively, substitute_type_variables_with,
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
    import_span: Option<Span>,
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
    slot: EvidenceSlotHandle,
    span: Span,
    declaration_span: Option<Span>,
    import_span: Option<Span>,
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
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct SelectionMethod<'a> {
    interface: InterfaceId,
    interface_parameter: TypeVariableId,
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

    pub(crate) const fn value_type(self) -> &'a Type {
        self.value_type
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
        }
    }

    pub(crate) fn add_interface_fact(
        &mut self,
        fact: &CheckedInterfaceFact,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(), SelectionFailure> {
        self.add_interface_fact_parts(fact, constraint_work, type_work)
    }

    pub(crate) fn add_imported_interface_fact(
        &mut self,
        fact: &CheckedInterfaceFact,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(), SelectionFailure> {
        self.add_interface_fact_parts(fact, constraint_work, type_work)
    }

    fn add_interface_fact_parts(
        &mut self,
        fact: &CheckedInterfaceFact,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(), SelectionFailure> {
        constraint_work
            .charge(fact.methods.len().saturating_add(1))
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        if self.interface_indices.contains_key(&fact.id)
            || fact
                .methods
                .iter()
                .any(|method| self.method_indices.contains_key(&method.id))
        {
            return Err(SelectionFailure::InvalidState);
        }
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
            methods.push(MethodEntry {
                id: method.id,
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
            if self
                .method_indices
                .insert(method.id, (interface_index, method_index))
                .is_some()
            {
                return Err(SelectionFailure::InvalidState);
            }
        }
        if self
            .interface_indices
            .insert(fact.id, interface_index)
            .is_some()
        {
            return Err(SelectionFailure::InvalidState);
        }
        self.interfaces.push(InterfaceEntry {
            id: fact.id,
            parameter: fact.parameter.id,
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
        imported: &ImportedImplementationFact,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(), SelectionFailure> {
        let fact = &imported.fact;
        if self.implementation_indices.contains_key(&fact.id) {
            return Err(SelectionFailure::InvalidState);
        }
        constraint_work
            .charge(
                fact.head_parameters
                    .len()
                    .saturating_add(fact.prerequisites.len())
                    .saturating_add(fact.methods.len().saturating_mul(2))
                    .saturating_add(2),
            )
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        constraint_work
            .charge_type(&fact.argument)
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        let mut parameters = Vec::new();
        let mut prerequisites = Vec::new();
        let mut methods = Vec::new();
        let mut method_spans = Vec::new();
        parameters
            .try_reserve(fact.head_parameters.len())
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        prerequisites
            .try_reserve(fact.prerequisites.len())
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        methods
            .try_reserve(fact.methods.len())
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        method_spans
            .try_reserve(fact.methods.len())
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        parameters.extend(fact.head_parameters.iter().map(|parameter| parameter.id));
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
        let argument = clone_type_with_budget(&fact.argument, type_work)
            .map_err(|()| SelectionFailure::TypeResource)?;
        self.implementations
            .try_reserve(1)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        self.implementation_indices
            .try_reserve(1)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        self.implementation_candidates
            .try_reserve(1)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        let implementation_index = self.implementations.len();
        self.implementation_candidates
            .entry(fact.interface)
            .or_default()
            .try_reserve(1)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        if self
            .implementation_indices
            .insert(fact.id, implementation_index)
            .is_some()
        {
            return Err(SelectionFailure::InvalidState);
        }
        self.implementation_candidates
            .get_mut(&fact.interface)
            .ok_or(SelectionFailure::InvalidState)?
            .push(implementation_index);
        self.implementations.push(ImplementationEntry {
            id: fact.id,
            interface: fact.interface,
            parameters: parameters.into_boxed_slice(),
            argument,
            prerequisites: prerequisites.into_boxed_slice(),
            methods: methods.into_boxed_slice(),
            span: fact.span,
            method_spans,
            import_span: imported
                .authorization()
                .hops()
                .first()
                .map(|hop| hop.import_span),
        });
        Ok(())
    }

    pub(crate) fn add_local_implementation(
        &mut self,
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
        if self.implementation_indices.contains_key(&checked.id) {
            return Err(SelectionFailure::InvalidState);
        }
        constraint_work
            .charge_type(&resolved.argument.ty)
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        let mut parameters = Vec::new();
        let mut prerequisites = Vec::new();
        let mut methods = Vec::new();
        parameters
            .try_reserve(resolved.head_parameters.len())
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        prerequisites
            .try_reserve(resolved.prerequisites.len())
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        methods
            .try_reserve(checked.methods.len())
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        parameters.extend(
            resolved
                .head_parameters
                .iter()
                .map(|parameter| parameter.id),
        );
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
        let argument = clone_type_with_budget(&resolved.argument.ty, type_work)
            .map_err(|()| SelectionFailure::TypeResource)?;
        self.implementations
            .try_reserve(1)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        self.implementation_indices
            .try_reserve(1)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        self.implementation_candidates
            .try_reserve(1)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        let implementation_index = self.implementations.len();
        self.implementation_candidates
            .entry(checked.interface)
            .or_default()
            .try_reserve(1)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        if self
            .implementation_indices
            .insert(checked.id, implementation_index)
            .is_some()
        {
            return Err(SelectionFailure::InvalidState);
        }
        self.implementation_candidates
            .get_mut(&checked.interface)
            .ok_or(SelectionFailure::InvalidState)?
            .push(implementation_index);
        self.implementations.push(ImplementationEntry {
            id: checked.id,
            interface: checked.interface,
            parameters: parameters.into_boxed_slice(),
            argument,
            prerequisites: prerequisites.into_boxed_slice(),
            methods: methods.into_boxed_slice(),
            span: resolved.span,
            method_spans,
            import_span: None,
        });
        Ok(())
    }

    pub(crate) fn method(&self, id: MethodId) -> Option<SelectionMethod<'_>> {
        let (interface_index, method_index) = *self.method_indices.get(&id)?;
        let interface = self.interfaces.get(interface_index)?;
        let method = interface.methods.get(method_index)?;
        Some(SelectionMethod {
            interface: interface.id,
            interface_parameter: interface.parameter,
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
            argument,
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
        constraint_work
            .charge(1)
            .and_then(|()| constraint_work.charge_type(&argument))
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        self.pending
            .try_reserve(1)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        self.pending.push(PendingObligation {
            interface,
            argument,
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
        site: SelectionSite,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(), SelectionFailure> {
        constraint_work
            .charge(1)
            .and_then(|()| constraint_work.charge_type(argument))
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        let argument = clone_type_with_budget(argument, type_work)
            .map_err(|()| SelectionFailure::TypeResource)?;
        self.pending
            .try_reserve(1)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        self.pending.push(PendingObligation {
            interface,
            argument,
            slot: site.slot,
            span: site.span,
            declaration_span: site.declaration_span,
            import_span: site.import_span,
        });
        Ok(())
    }

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
        if marker > self.pending.len() {
            return Err(SelectionError {
                failure: SelectionFailure::InvalidState,
                span: None,
                declaration_span: None,
                import_span: None,
                causes: Vec::new(),
            });
        }
        constraint_work
            .charge(self.pending.len() - marker)
            .map_err(|()| SelectionError {
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
            obligation
                .slot
                .fill(checked_argument, selection)
                .map_err(|_| SelectionError {
                    failure: SelectionFailure::InvalidState,
                    span: Some(obligation.span),
                    declaration_span: obligation.declaration_span,
                    import_span: obligation.import_span,
                    causes: Vec::new(),
                })?;
        }
        Ok(())
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
        let mut causes = Vec::new();
        let (checked_argument, selection) =
            self.select_owned(interface, argument, &mut causes, constraint_work, type_work)?;
        discard_type_iteratively(checked_argument);
        Ok(selection)
    }

    fn select_owned(
        &self,
        interface: InterfaceId,
        argument: Type,
        causes: &mut Vec<SelectionCause>,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(Type, EvidenceSelection), SelectionFailure> {
        causes.clear();
        if matches!(&argument, Type::Inference(_)) {
            let interface_entry = self.interface_entry(interface)?;
            retain_selection_cause(
                causes,
                SelectionCauseKind::Interface,
                interface_entry.span,
                constraint_work,
            )?;
            discard_type_iteratively(argument);
            return Err(SelectionFailure::Reason(InterfaceReason::Ambiguous));
        }
        if matches!(&argument, Type::Forall(_, _)) {
            discard_type_iteratively(argument);
            return Err(SelectionFailure::InvalidState);
        }
        let mut builder = EvidenceSelectionBuilder::new();
        let mut checked_goal = Goal {
            interface,
            argument,
        };
        let work_argument = clone_type_with_budget(&checked_goal.argument, type_work)
            .map_err(|()| SelectionFailure::TypeResource)?;
        let mut work = SelectionWork::new(
            Goal {
                interface,
                argument: work_argument,
            },
            0,
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
                        let node = builder
                            .push_abstract(requirement, interface_methods, constraint_work)
                            .map_err(|()| SelectionFailure::ConstraintResource)?;
                        results
                            .try_reserve(1)
                            .map_err(|_| SelectionFailure::ConstraintResource)?;
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
                            let substitution = match_implementation_head(
                                implementation.parameters.iter().copied(),
                                &implementation.argument,
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
                            results
                                .try_reserve(1)
                                .map_err(|_| SelectionFailure::ConstraintResource)?;
                            results.push(node);
                            continue;
                        }
                    }

                    let key = goal_key(goal.interface, &goal.argument, constraint_work)?;
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
                        let substitution = match_implementation_head(
                            implementation.parameters.iter().copied(),
                            &implementation.argument,
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
                    if let Some(import_span) = implementation.import_span {
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
                    work.push(SelectionTask::Finish {
                        key,
                        candidate_index,
                        substitution,
                        result_start,
                    })?;
                    for prerequisite in implementation.prerequisites.iter().rev() {
                        let argument = substitute_type_variables_with(
                            &prerequisite.argument,
                            &replacements.values,
                            |cells| type_work.charge(cells),
                        )
                        .map_err(|()| SelectionFailure::TypeResource)?;
                        charge_prerequisite_goal(&argument, constraint_work)?;
                        work.push(SelectionTask::Select {
                            goal: Goal {
                                interface: prerequisite.interface,
                                argument,
                            },
                            cause_marker: prerequisite_cause_marker,
                        })?;
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
                    let prerequisites = &results[result_start..];
                    if prerequisites.len() != implementation.prerequisites.len() {
                        return Err(SelectionFailure::InvalidState);
                    }
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
        let checked_argument = std::mem::replace(&mut checked_goal.argument, Type::Unit);
        if constraint_work
            .charge(1)
            .and_then(|()| constraint_work.charge_type(&checked_argument))
            .is_err()
        {
            discard_type_iteratively(checked_argument);
            return Err(SelectionFailure::ConstraintResource);
        }
        let selection_argument = match clone_type_with_budget(&checked_argument, type_work) {
            Ok(argument) => argument,
            Err(()) => {
                discard_type_iteratively(checked_argument);
                return Err(SelectionFailure::TypeResource);
            }
        };
        let selection = match builder.finish(results[0], interface, selection_argument) {
            Ok(selection) => selection,
            Err(()) => {
                discard_type_iteratively(checked_argument);
                return Err(SelectionFailure::InvalidState);
            }
        };
        Ok((checked_argument, selection))
    }

    fn interface_entry(&self, interface: InterfaceId) -> Result<&InterfaceEntry, SelectionFailure> {
        self.interface_indices
            .get(&interface)
            .and_then(|index| self.interfaces.get(*index))
            .ok_or(SelectionFailure::InvalidState)
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
            methods: methods.into_boxed_slice(),
            method_ids,
            span,
        });
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

fn replacement_map(
    substitution: &[EvidenceSubstitution],
    type_work: &mut TypeWorkBudget,
) -> Result<ReplacementMap, SelectionFailure> {
    let mut values = HashMap::new();
    values
        .try_reserve(substitution.len())
        .map_err(|_| SelectionFailure::TypeResource)?;
    for binding in substitution {
        let argument = clone_type_with_budget(binding.argument(), type_work)
            .map_err(|()| SelectionFailure::TypeResource)?;
        if values.insert(binding.parameter(), argument).is_some() {
            return Err(SelectionFailure::InvalidState);
        }
    }
    Ok(ReplacementMap { values })
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
    fn new(goal: Goal, cause_marker: usize) -> Result<Self, SelectionFailure> {
        let mut tasks = Vec::new();
        tasks
            .try_reserve(1)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        tasks.push(SelectionTask::Select { goal, cause_marker });
        Ok(Self(tasks))
    }

    fn push(&mut self, task: SelectionTask) -> Result<(), SelectionFailure> {
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
    AppliedNominal(NominalTypeId, usize),
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
            Type::AppliedNominal(id, arguments) => {
                cells.push(GoalCell::AppliedNominal(*id, arguments.len()));
                constraint_work
                    .charge(arguments.len())
                    .map_err(|()| SelectionFailure::ConstraintResource)?;
                pending
                    .try_reserve(arguments.len())
                    .map_err(|_| SelectionFailure::ConstraintResource)?;
                pending.extend(arguments.iter().rev());
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
            (Type::AppliedNominal(left_id, left), Type::AppliedNominal(right_id, right))
                if left_id == right_id && left.len() == right.len() =>
            {
                constraint_work.charge(left.len())?;
                pending.try_reserve(left.len()).map_err(|_| ())?;
                pending.extend(left.iter().zip(right).rev());
            }
            (Type::Forall(left_parameters, left), Type::Forall(right_parameters, right)) => {
                if left_parameters.len() != right_parameters.len() {
                    return Ok(false);
                }
                constraint_work.charge(left_parameters.len().saturating_add(1))?;
                if left_parameters != right_parameters {
                    return Ok(false);
                }
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
        interface::{EvidenceNode, EvidenceSlot, RequirementOwner},
        module::ModuleId,
        resolved::BinderId,
        source::{ByteRange, SourceFile},
    };

    fn ids() -> (InterfaceId, MethodId, RequirementId) {
        let module = ModuleId::new(1);
        let interface = InterfaceId::new(module, 0);
        let method = MethodId::new(interface, 0);
        let requirement =
            RequirementId::new(RequirementOwner::Global(BinderId::resolved(module, 0)), 0);
        (interface, method, requirement)
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
            import_span: None,
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
            Type::AppliedNominal(option, vec![Type::Variable(parameter)].into_boxed_slice()),
            vec![(prerequisite, interface, Type::Variable(parameter))],
            vec![ImplMethodId::new(generic, method)],
        ));

        let goal = Type::AppliedNominal(option, vec![Type::Int].into_boxed_slice());
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
            Type::AppliedNominal(option, vec![Type::Variable(parameter)].into_boxed_slice()),
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
            Type::AppliedNominal(option, vec![Type::Variable(parameter)].into_boxed_slice());
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
        let (interface, method, _) = ids();
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
            selector.select_owned(
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
            baseline_work.used() + usize::try_from(REJECTED).expect("fixture width") * 7,
            "each rejected ground candidate costs one inspection and six head-match units",
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

        let failure = selector.select_owned(
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

        let reached_first = selector
            .close(
                0,
                |argument, _| Ok(argument),
                &mut InterfaceConstraintBudget::with_limit(WIDTH),
                &mut TypeWorkBudget::default(),
            )
            .expect_err("the exact transfer budget should reach the first obligation");
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
        let mut exact = TypeWorkBudget::with_limit(exact_type_work);
        selector
            .close(
                0,
                |argument, _type_work| {
                    discard_type_iteratively(argument);
                    Ok(Type::Int)
                },
                &mut InterfaceConstraintBudget::default(),
                &mut exact,
            )
            .expect("the exact checked-goal retention budget should fill its slot");
        assert_eq!(exact.used(), exact_type_work);
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
}
