mod lexical_sources;
use lexical_sources::{LinkedLexicalSource, OriginalLexicalContext};

use std::{
    collections::{HashMap, HashSet},
    error::Error,
    fmt,
    sync::Arc,
};

use crate::{
    core::dialect::{
        MethodEvidenceAdapter, MethodEvidenceCatalog, MethodEvidenceDomain,
        MethodEvidenceExpectation, MethodEvidenceExpectedRole, MethodEvidenceImplementationOwner,
        MethodEvidenceMethod, MethodEvidenceOccurrence, MethodEvidenceOwner,
    },
    interface::{
        CheckedRequirement, ConstrainedScheme, EvidenceNode, EvidenceNodeId, EvidenceSelection,
        EvidenceSubstitution, ImplId, ImplMethodId, InterfaceApplication,
        InterfaceConstraintBudget, InterfaceId, MethodId, RequirementId, RequirementOwner,
        same_kinded_argument_with_constraint_budget,
        same_type_with_constraint_budget as same_semantic_type_with_constraint_budget,
    },
    kind::{KindEnvironments, KindFailure, canonical_type_variable_kind},
    module::ModuleId,
    resolved::{
        AvailableImplementation, BinderId, CheckedGlobalScheme, CheckedImplementationFact,
        CheckedInterfaceFact, ImplementationAuthorization, PublicImplementationAuthorization,
        ResolvedBlock, ResolvedExpr, ResolvedExprKind, ResolvedLocalDeclaration, ResolvedModule,
        ResolvedModuleGroup, ResolvedModuleProgram, ResolvedOccurrence, ResolvedRegistry,
        ResolvedTermName, ResolvedTypeVariable,
    },
    source::{Origin, Span},
    types::{
        EffectRow, EffectRowVariable, IterativeArgumentOwner, IterativeTypeOwner, Kind,
        KindedArgument, NominalTypeId, Type, TypeVariableId, TypeWorkBudget,
        clone_kind_with_budget, clone_kinded_argument_with_budget, clone_type_with_budget,
        discard_kinded_argument_iteratively, discard_type_iteratively, same_kind_with_charge,
        substitute_type_and_row_variables_with, visit_owner_components_with_charge,
    },
};

#[cfg(test)]
use crate::resolved::ResolvedDefinitionKind;

/// Stable reason owned by pre-Core interface-evidence validation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EvidenceValidationReason {
    /// A linked checked identity is absent, duplicated, or owned by another declaration.
    UnknownIdentity,
    /// A selected implementation is not in the occurrence module's effective environment.
    UnavailableImplementation,
    /// An occurrence selection does not authenticate its checked interface obligation.
    InvalidEvidenceRoot,
    /// The persistent graph-wide interface and constraint budget was exhausted.
    ConstraintResourceExhausted,
    /// The linked kind-environment retention budget was exhausted.
    TypeResourceExhausted,
}

impl fmt::Display for EvidenceValidationReason {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::UnknownIdentity => "evidence.validation.unknown-identity",
            Self::UnavailableImplementation => "evidence.validation.unavailable-implementation",
            Self::InvalidEvidenceRoot => "evidence.validation.invalid-root",
            Self::ConstraintResourceExhausted => "internal.resource.constraint-work",
            Self::TypeResourceExhausted => "internal.resource.type-work",
        })
    }
}

/// Failure while authenticating linked checked evidence before any Core exists.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct EvidenceValidationFailure {
    reason: EvidenceValidationReason,
    primary: Span,
    kind_context: Option<crate::kind::KindFailureContext>,
}

impl EvidenceValidationFailure {
    fn with_kind_context(mut self, failure: &KindFailure) -> Self {
        self.kind_context = failure.internal_context();
        self
    }

    pub(crate) fn kind_context(self) -> Option<crate::kind::KindFailureContext> {
        self.kind_context
    }

    pub(crate) fn diagnostic_message(
        self,
    ) -> Option<(crate::message::Message<'static>, &'static str)> {
        use crate::message::Message;
        if let Some(cause) = self.kind_context {
            return Some((cause.message(), "validation_site"));
        }
        Some(match self.reason {
            EvidenceValidationReason::UnknownIdentity => {
                (Message::evidence_unknown_identity(), "evidence_use")
            }
            EvidenceValidationReason::InvalidEvidenceRoot => {
                (Message::evidence_invalid_root(), "evidence_use")
            }
            EvidenceValidationReason::UnavailableImplementation => (
                Message::evidence_unavailable_implementation(),
                "evidence_use",
            ),
            EvidenceValidationReason::ConstraintResourceExhausted => {
                (Message::compiler_constraint_resources(), "validation_site")
            }
            EvidenceValidationReason::TypeResourceExhausted => {
                (Message::compiler_type_resources(), "validation_site")
            }
        })
    }

    pub(crate) const fn diagnostic_resource(self) -> Option<&'static str> {
        match self.reason {
            EvidenceValidationReason::ConstraintResourceExhausted => Some("constraint-work"),
            EvidenceValidationReason::TypeResourceExhausted => Some("type-work"),
            _ => None,
        }
    }

    const fn new(reason: EvidenceValidationReason, primary: Span) -> Self {
        Self {
            reason,
            primary,
            kind_context: None,
        }
    }

    /// Returns the stable validation reason.
    #[must_use]
    pub const fn reason(self) -> EvidenceValidationReason {
        self.reason
    }

    /// Returns the first source span whose checked relationship failed authentication.
    #[must_use]
    pub const fn primary(self) -> Span {
        self.primary
    }
}

impl fmt::Display for EvidenceValidationFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{} at {:?}", self.reason, self.primary)
    }
}

impl Error for EvidenceValidationFailure {}

#[derive(Clone, Copy, Debug)]
struct FactLocation {
    group: usize,
    fact: usize,
}

#[derive(Clone, Copy, Debug)]
struct MethodLocation {
    interface: FactLocation,
    method: usize,
}

#[derive(Clone, Copy, Debug)]
struct SchemeLocation {
    group: usize,
    scheme: usize,
}

#[derive(Clone, Copy, Debug)]
struct ImplementationMethodLocation {
    implementation: FactLocation,
    method: usize,
}

#[derive(Clone, Copy, Debug)]
struct PublicImplementationLocation {
    group: usize,
    authorization: usize,
}

/// Owned identity locations into the checked facts retained by module groups.
#[derive(Debug)]
struct LinkedInterfaceRegistry {
    scoped_type_owners: std::cell::RefCell<HashMap<TypeVariableId, (LinkedBinderOwner, Span)>>,
    modules: HashMap<ModuleId, usize>,
    interfaces: HashMap<InterfaceId, FactLocation>,
    methods: HashMap<MethodId, MethodLocation>,
    implementations: HashMap<ImplId, FactLocation>,
    implementation_methods: HashMap<ImplMethodId, ImplementationMethodLocation>,
    public_implementations: HashMap<(ModuleId, ImplId), PublicImplementationLocation>,
    authenticated_public_implementations: HashSet<(ModuleId, ImplId)>,
    schemes: HashMap<BinderId, SchemeLocation>,
    binders: HashMap<BinderId, ()>,
}

impl LinkedInterfaceRegistry {
    #[cfg(test)]
    fn build(
        program: &ResolvedModuleProgram,
        budget: &mut InterfaceConstraintBudget,
    ) -> Result<Self, EvidenceValidationFailure> {
        let mut type_work = TypeWorkBudget::default();
        let mut kind_environments = build_linked_kind_environments(
            program.registry(),
            &mut type_work,
            program.result().span,
        )?;
        let registry = Self::build_with_kinds(
            program,
            &mut kind_environments,
            None,
            budget,
            &mut type_work,
        )?;
        Ok(registry)
    }

    fn build_with_kinds<'a>(
        program: &'a ResolvedModuleProgram,
        kind_environments: &mut KindEnvironments<'a>,
        mut binder_owners: Option<&mut HashMap<TypeVariableId, LinkedBinderOwner>>,
        budget: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<Self, EvidenceValidationFailure> {
        let mut registry = Self {
            scoped_type_owners: std::cell::RefCell::new(HashMap::new()),
            modules: HashMap::new(),
            interfaces: HashMap::new(),
            methods: HashMap::new(),
            implementations: HashMap::new(),
            implementation_methods: HashMap::new(),
            public_implementations: HashMap::new(),
            authenticated_public_implementations: HashSet::new(),
            schemes: HashMap::new(),
            binders: HashMap::new(),
        };

        for group_index in 0..program.groups().len() {
            let provisional_span = program
                .groups()
                .get(group_index)
                .map_or(program.result().span, ResolvedModuleGroup::span);
            charge(budget, 1, provisional_span)?;
            let group = program
                .groups()
                .get(group_index)
                .ok_or_else(|| unknown(provisional_span))?;
            let span = group.span();
            registry
                .modules
                .try_reserve(1)
                .map_err(|_| resource(span))?;
            if registry
                .modules
                .insert(group.module(), group_index)
                .is_some()
            {
                return Err(unknown(span));
            }
            for fact_index in 0..group.interface_facts().len() {
                charge(budget, 1, span)?;
                let fact = group
                    .interface_facts()
                    .get(fact_index)
                    .ok_or_else(|| unknown(span))?;
                charge(budget, 1, fact.span)?;
                registry
                    .interfaces
                    .try_reserve(1)
                    .map_err(|_| resource(fact.span))?;
                if fact.id.module() != group.module()
                    || usize::try_from(fact.id.declaration()) != Ok(fact_index)
                    || registry
                        .interfaces
                        .insert(
                            fact.id,
                            FactLocation {
                                group: group_index,
                                fact: fact_index,
                            },
                        )
                        .is_some()
                {
                    return Err(unknown(fact.span));
                }
                kind_environments
                    .insert_interface(fact.id, &fact.parameters, fact.span, type_work)
                    .map_err(|failure| map_kind_type_failure(failure, fact.span))?;
                for method_index in 0..fact.methods.len() {
                    charge(budget, 1, fact.span)?;
                    let method = fact
                        .methods
                        .get(method_index)
                        .ok_or_else(|| unknown(fact.span))?;
                    charge(budget, 1, method.span)?;
                    registry
                        .methods
                        .try_reserve(1)
                        .map_err(|_| resource(method.span))?;
                    if method.id.interface() != fact.id
                        || usize::try_from(method.id.declaration()) != Ok(method_index)
                        || registry
                            .methods
                            .insert(
                                method.id,
                                MethodLocation {
                                    interface: FactLocation {
                                        group: group_index,
                                        fact: fact_index,
                                    },
                                    method: method_index,
                                },
                            )
                            .is_some()
                    {
                        return Err(unknown(method.span));
                    }
                    if let Some(owners) = binder_owners.as_deref_mut() {
                        for parameter in method.authoritative_type_parameters() {
                            charge(budget, 1, parameter.origin.primary_span())?;
                            let canonical = program
                                .registry()
                                .type_variable(parameter.id)
                                .ok_or_else(|| unknown(method.span))?;
                            if !same_binders_charged(
                                std::slice::from_ref(canonical),
                                std::slice::from_ref(parameter),
                                budget,
                                method.span,
                            )? || owners
                                .insert(parameter.id, LinkedBinderOwner::Method(method.id))
                                .is_some()
                            {
                                return Err(unknown(method.span));
                            }
                        }
                    }
                }
            }
            for fact_index in 0..group.implementation_facts().len() {
                charge(budget, 1, span)?;
                let fact = group
                    .implementation_facts()
                    .get(fact_index)
                    .ok_or_else(|| unknown(span))?;
                charge(budget, 1, fact.span)?;
                registry
                    .implementations
                    .try_reserve(1)
                    .map_err(|_| resource(fact.span))?;
                if fact.id.module() != group.module()
                    || usize::try_from(fact.id.declaration()) != Ok(fact_index)
                    || registry
                        .implementations
                        .insert(
                            fact.id,
                            FactLocation {
                                group: group_index,
                                fact: fact_index,
                            },
                        )
                        .is_some()
                {
                    return Err(unknown(fact.span));
                }
                for method_index in 0..fact.methods.len() {
                    charge(budget, 1, fact.span)?;
                    let method = fact
                        .methods
                        .get(method_index)
                        .ok_or_else(|| unknown(fact.span))?;
                    charge(budget, 2, method.span)?;
                    registry
                        .implementation_methods
                        .try_reserve(1)
                        .map_err(|_| resource(method.span))?;
                    registry
                        .binders
                        .try_reserve(1)
                        .map_err(|_| resource(method.span))?;
                    if method.id.implementation() != fact.id
                        || method.id.method() != method.method
                        || method.binder.module() != Some(group.module())
                        || registry
                            .implementation_methods
                            .insert(
                                method.id,
                                ImplementationMethodLocation {
                                    implementation: FactLocation {
                                        group: group_index,
                                        fact: fact_index,
                                    },
                                    method: method_index,
                                },
                            )
                            .is_some()
                        || registry.binders.insert(method.binder, ()).is_some()
                    {
                        return Err(unknown(method.span));
                    }
                }
            }
            for scheme_index in 0..group.schemes().len() {
                charge(budget, 1, span)?;
                let scheme = group
                    .schemes()
                    .get(scheme_index)
                    .ok_or_else(|| unknown(span))?;
                let scheme_span = scheme.origin.primary_span();
                charge(budget, 2, scheme_span)?;
                registry
                    .schemes
                    .try_reserve(1)
                    .map_err(|_| resource(scheme_span))?;
                registry
                    .binders
                    .try_reserve(1)
                    .map_err(|_| resource(scheme_span))?;
                if scheme.binder.module() != Some(group.module())
                    || registry
                        .schemes
                        .insert(
                            scheme.binder,
                            SchemeLocation {
                                group: group_index,
                                scheme: scheme_index,
                            },
                        )
                        .is_some()
                    || registry.binders.insert(scheme.binder, ()).is_some()
                {
                    return Err(unknown(scheme_span));
                }
            }
            for authorization_index in 0..group.public_implementation_authorizations().len() {
                charge(budget, 1, span)?;
                let authorization = group
                    .public_implementation_authorizations()
                    .get(authorization_index)
                    .ok_or_else(|| unknown(span))?;
                charge(budget, 1, span)?;
                registry
                    .public_implementations
                    .try_reserve(1)
                    .map_err(|_| resource(span))?;
                if registry
                    .public_implementations
                    .insert(
                        (group.module(), authorization.id()),
                        PublicImplementationLocation {
                            group: group_index,
                            authorization: authorization_index,
                        },
                    )
                    .is_some()
                {
                    return Err(unknown(span));
                }
            }
        }
        registry.authenticate_public_implementations(program, budget)?;
        registry.authenticate_available_implementations(program, budget)?;
        Ok(registry)
    }

    fn public_implementation<'a>(
        &self,
        program: &'a ResolvedModuleProgram,
        publisher: ModuleId,
        id: ImplId,
    ) -> Option<&'a PublicImplementationAuthorization> {
        let location = self.public_implementations.get(&(publisher, id))?;
        let group = program.groups().get(location.group)?;
        if group.module() != publisher {
            return None;
        }
        group
            .public_implementation_authorizations()
            .get(location.authorization)
            .filter(|authorization| authorization.id() == id)
    }

    fn authenticate_public_implementations(
        &mut self,
        program: &ResolvedModuleProgram,
        budget: &mut InterfaceConstraintBudget,
    ) -> Result<(), EvidenceValidationFailure> {
        for group_index in 0..program.groups().len() {
            let group = program
                .groups()
                .get(group_index)
                .ok_or_else(|| unknown(program.result().span))?;
            for authorization_index in 0..group.public_implementation_authorizations().len() {
                charge(budget, 1, group.span())?;
                let authorization = group
                    .public_implementation_authorizations()
                    .get(authorization_index)
                    .ok_or_else(|| unknown(group.span()))?;
                let indexed = self
                    .public_implementations
                    .get(&(group.module(), authorization.id()))
                    .is_some_and(|location| {
                        location.group == group_index
                            && location.authorization == authorization_index
                    });
                if !indexed
                    || !self.authenticate_public_implementation(
                        program,
                        group_index,
                        group,
                        authorization,
                        budget,
                    )?
                {
                    return Err(unknown(group.span()));
                }
                charge(budget, 1, group.span())?;
                self.authenticated_public_implementations
                    .try_reserve(1)
                    .map_err(|_| resource(group.span()))?;
                if !self
                    .authenticated_public_implementations
                    .insert((group.module(), authorization.id()))
                {
                    return Err(unknown(group.span()));
                }
            }
        }
        Ok(())
    }

    fn authenticate_public_implementation(
        &self,
        program: &ResolvedModuleProgram,
        group_index: usize,
        group: &ResolvedModuleGroup,
        authorization: &PublicImplementationAuthorization,
        budget: &mut InterfaceConstraintBudget,
    ) -> Result<bool, EvidenceValidationFailure> {
        if authorization.authorization().is_local() {
            charge(budget, 1, group.span())?;
            let Some(location) = self.implementations.get(&authorization.id()).copied() else {
                return Ok(false);
            };
            charge(budget, 2, group.span())?;
            let Some(fact) = group.implementation_facts().get(location.fact) else {
                return Ok(false);
            };
            if location.group != group_index
                || authorization.id().module() != group.module()
                || fact.id != authorization.id()
            {
                return Ok(false);
            }
            return Ok(true);
        }
        self.authenticate_imported_authorization(
            program,
            group_index,
            group,
            authorization.id(),
            authorization.authorization(),
            budget,
        )
    }

    fn authenticate_available_implementations(
        &self,
        program: &ResolvedModuleProgram,
        budget: &mut InterfaceConstraintBudget,
    ) -> Result<(), EvidenceValidationFailure> {
        for group_index in 0..program.groups().len() {
            let group = program
                .groups()
                .get(group_index)
                .ok_or_else(|| unknown(program.result().span))?;
            for available_index in 0..group.available_implementations().len() {
                charge(budget, 1, group.span())?;
                let available = group
                    .available_implementations()
                    .get(available_index)
                    .ok_or_else(|| unknown(group.span()))?;
                if !self.authenticate_available_implementation(
                    program,
                    group_index,
                    group,
                    available,
                    budget,
                )? {
                    return Err(unknown(group.span()));
                }
            }
        }
        Ok(())
    }

    fn authenticate_available_implementation(
        &self,
        program: &ResolvedModuleProgram,
        group_index: usize,
        group: &ResolvedModuleGroup,
        available: &AvailableImplementation,
        budget: &mut InterfaceConstraintBudget,
    ) -> Result<bool, EvidenceValidationFailure> {
        if available.authorization().is_local() {
            charge(budget, 1, group.span())?;
            return Ok(self
                .implementations
                .get(&available.id())
                .is_some_and(|location| {
                    location.group == group_index && available.id().module() == group.module()
                }));
        }
        self.authenticate_imported_authorization(
            program,
            group_index,
            group,
            available.id(),
            available.authorization(),
            budget,
        )
    }

    fn authenticate_imported_authorization(
        &self,
        program: &ResolvedModuleProgram,
        group_index: usize,
        group: &ResolvedModuleGroup,
        implementation: ImplId,
        authorization: &ImplementationAuthorization,
        budget: &mut InterfaceConstraintBudget,
    ) -> Result<bool, EvidenceValidationFailure> {
        charge(budget, 1, group.span())?;
        let Some(first) = authorization.hops().first() else {
            return Ok(false);
        };
        charge(budget, 1, group.span())?;
        let Some(dependency_index) = self.modules.get(&first.to).copied() else {
            return Ok(false);
        };
        if first.from != group.module()
            || dependency_index >= group_index
            || !has_direct_dependency(group, first.to, first.import_span, budget, group.span())?
        {
            return Ok(false);
        }
        charge(budget, 2, group.span())?;
        if !self
            .authenticated_public_implementations
            .contains(&(first.to, implementation))
        {
            return Ok(false);
        }
        let Some(dependency_authorization) =
            self.public_implementation(program, first.to, implementation)
        else {
            return Ok(false);
        };
        authorization_suffix_matches(
            authorization,
            dependency_authorization.authorization(),
            budget,
            group.span(),
        )
    }

    fn interface<'a>(
        &self,
        program: &'a ResolvedModuleProgram,
        id: InterfaceId,
    ) -> Option<&'a CheckedInterfaceFact> {
        let location = self.interfaces.get(&id)?;
        program
            .groups()
            .get(location.group)?
            .interface_facts()
            .get(location.fact)
            .map(AsRef::as_ref)
    }

    fn method<'a>(
        &self,
        program: &'a ResolvedModuleProgram,
        id: MethodId,
    ) -> Option<&'a crate::resolved::CheckedInterfaceMethodFact> {
        let location = self.methods.get(&id)?;
        program
            .groups()
            .get(location.interface.group)?
            .interface_facts()
            .get(location.interface.fact)?
            .methods
            .get(location.method)
    }

    fn implementation<'a>(
        &self,
        program: &'a ResolvedModuleProgram,
        id: ImplId,
    ) -> Option<&'a CheckedImplementationFact> {
        let location = self.implementations.get(&id)?;
        program
            .groups()
            .get(location.group)?
            .implementation_facts()
            .get(location.fact)
    }

    fn scheme<'a>(
        &self,
        program: &'a ResolvedModuleProgram,
        id: BinderId,
    ) -> Option<&'a ConstrainedScheme> {
        let location = self.schemes.get(&id)?;
        Some(
            &program
                .groups()
                .get(location.group)?
                .schemes()
                .get(location.scheme)?
                .scheme,
        )
    }

    fn requirement<'a>(
        &self,
        program: &'a ResolvedModuleProgram,
        id: RequirementId,
    ) -> Option<&'a CheckedRequirement> {
        let declaration = usize::try_from(id.declaration()).ok()?;
        match id.owner() {
            RequirementOwner::Global(binder) => self
                .scheme(program, binder)?
                .requirements
                .get(declaration)
                .filter(|requirement| requirement.id == id),
            RequirementOwner::Impl(implementation) => self
                .implementation(program, implementation)?
                .prerequisites
                .get(declaration)
                .filter(|requirement| requirement.id == id),
            RequirementOwner::ResourceFamily(_) => None,
        }
    }

    fn implementation_method<'a>(
        &self,
        program: &'a ResolvedModuleProgram,
        id: ImplMethodId,
    ) -> Option<&'a crate::resolved::CheckedImplementationMethodFact> {
        let location = self.implementation_methods.get(&id)?;
        program
            .groups()
            .get(location.implementation.group)?
            .implementation_facts()
            .get(location.implementation.fact)?
            .methods
            .get(location.method)
    }
}

fn validate_linked_type_with_policy(
    ty: &Type,
    registry: &ResolvedRegistry,
    variables: &[TypeVariableId],
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<(), EvidenceValidationFailure> {
    match validate_type_with_application_policy(ty, registry, variables, budget, span) {
        Ok(()) => Ok(()),
        Err(failure)
            if failure.reason() == EvidenceValidationReason::ConstraintResourceExhausted =>
        {
            Err(failure)
        }
        Err(_) => Err(unknown(span)),
    }
}

#[allow(clippy::too_many_arguments)]
fn same_application_parts_charged(
    application: &InterfaceApplication,
    interface: InterfaceId,
    arguments: &[KindedArgument],
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<bool, EvidenceValidationFailure> {
    if application.interface() != interface || application.arguments().len() != arguments.len() {
        return Ok(false);
    }
    for (checked, source) in application.arguments().iter().zip(arguments) {
        if !same_argument_charged(checked, source, budget, span)? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn linked_selection_key_types<'a>(
    interface: &CheckedInterfaceFact,
    arguments: &'a [KindedArgument],
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<Vec<&'a KindedArgument>, EvidenceValidationFailure> {
    if arguments.len() != interface.parameters.len() {
        return Err(unknown(span));
    }
    let selected_count = interface
        .determination()
        .map_or(arguments.len(), |determination| {
            determination.positions().len()
        });
    let Some(determination) = interface.determination() else {
        charge(budget, selected_count, span)?;
        let mut selected = Vec::new();
        selected
            .try_reserve_exact(selected_count)
            .map_err(|_| resource(span))?;
        selected.extend(arguments);
        return Ok(selected);
    };

    let mut previous_position = None;
    for &position in determination.positions() {
        charge(budget, 1, span)?;
        if position >= arguments.len()
            || previous_position.is_some_and(|previous| previous >= position)
        {
            return Err(unknown(span));
        }
        previous_position = Some(position);
    }
    charge(budget, selected_count, span)?;
    let mut selected = Vec::new();
    selected
        .try_reserve_exact(selected_count)
        .map_err(|_| resource(span))?;
    for &position in determination.positions() {
        selected.push(arguments.get(position).ok_or_else(|| unknown(span))?);
    }
    Ok(selected)
}

fn build_linked_kind_environments<'a>(
    registry: &'a ResolvedRegistry,
    type_work: &mut TypeWorkBudget,
    span: Span,
) -> Result<KindEnvironments<'a>, EvidenceValidationFailure> {
    let mut environments = KindEnvironments::new_with_registry(registry);
    for nominal in registry
        .nominals()
        .iter()
        .chain(registry.lexical_nominals())
    {
        let parameters = registry
            .nominal_parameters(nominal.id)
            .ok_or_else(|| unknown(span))?;
        environments
            .insert_nominal(
                nominal.id,
                parameters,
                nominal.origin.primary_span(),
                type_work,
            )
            .map_err(|failure| map_kind_type_failure(failure, span))?;
    }
    let count = registry.abstract_nominal_kind_count();
    type_work.charge(count).map_err(|()| type_resource(span))?;
    let mut abstracts = Vec::new();
    abstracts
        .try_reserve_exact(count)
        .map_err(|_| type_resource(span))?;
    abstracts.extend(registry.abstract_nominal_kind_entries());
    abstracts.sort_unstable_by_key(|(identity, _, _)| *identity);
    for (identity, kind, origin) in abstracts {
        match kind {
            crate::resolved::NonMaterializedNominalKind::Ordinary(kind) => {
                environments.insert_frozen_nominal(identity, kind, origin, type_work)
            }
            crate::resolved::NonMaterializedNominalKind::RowBearingResource(resource_id) => {
                let owner = crate::resolved::OwnerId::Resource(*resource_id);
                let parameters = registry
                    .defining_owner_parameters(owner)
                    .ok_or_else(|| unknown(span))?;
                environments.insert_row_resource_family(
                    identity,
                    *resource_id,
                    parameters,
                    origin,
                    type_work,
                )
            }
        }
        .map_err(|failure| map_kind_type_failure(failure, span))?;
    }
    Ok(environments)
}

fn retain_constraint_variable(
    identity: TypeVariableId,
    output: &mut Vec<TypeVariableId>,
    budget: &mut impl FnMut(usize) -> Result<(), EvidenceValidationFailure>,
    span: Span,
) -> Result<(), EvidenceValidationFailure> {
    for known in output.iter() {
        budget(1)?;
        if *known == identity {
            return Ok(());
        }
    }
    budget(1)?;
    output.try_reserve(1).map_err(|_| resource(span))?;
    output.push(identity);
    Ok(())
}
fn collect_argument_constraint_variables(
    argument: &KindedArgument,
    output: &mut Vec<TypeVariableId>,
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<(), EvidenceValidationFailure> {
    let mut leaves = Vec::new();
    visit_owner_components_with_charge(
        std::iter::once(argument),
        &mut |cells| charge(budget, cells, span),
        |ty, _| {
            leaves.try_reserve(1).map_err(|_| resource(span))?;
            leaves.push(ty);
            Ok(())
        },
        |tail, work| {
            let EffectRowVariable::Rigid(id) = tail.variable() else {
                return Err(unknown(span));
            };
            retain_constraint_variable(id, output, work, span)
        },
    )?;
    for ty in leaves {
        collect_linked_constraint_variables(ty, output, budget, span)?;
    }
    Ok(())
}

fn collect_linked_constraint_variables(
    root: &Type,
    output: &mut Vec<TypeVariableId>,
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<(), EvidenceValidationFailure> {
    charge(budget, 1, span)?;
    let mut pending = Vec::new();
    pending.try_reserve(1).map_err(|_| resource(span))?;
    pending.push(root);
    while let Some(ty) = pending.pop() {
        charge(budget, 1, span)?;
        if let Some(function) = ty.function_view() {
            let effects = function.effects();
            if let Some(tail) = effects.and_then(|effects| effects.tail()) {
                let EffectRowVariable::Rigid(id) = tail.variable() else {
                    return Err(unknown(span));
                };
                retain_constraint_variable(
                    id,
                    output,
                    &mut |cells| charge(budget, cells, span),
                    span,
                )?;
            }
            let mut effect_argument_count = 0usize;
            if let Some(effects) = effects {
                for member in effects.known() {
                    charge(budget, 1, span)?;
                    effect_argument_count = effect_argument_count
                        .checked_add(member.arguments().len())
                        .ok_or_else(|| resource(span))?;
                }
            }
            let effect_arguments = effects
                .into_iter()
                .flat_map(|effects| {
                    effects
                        .known()
                        .iter()
                        .chain(effects.tail().into_iter().flat_map(|tail| tail.lacks()))
                })
                .flat_map(|instance| instance.arguments());
            let children = effect_argument_count
                .checked_add(2)
                .ok_or_else(|| resource(span))?;
            charge(budget, children, span)?;
            pending.try_reserve(children).map_err(|_| resource(span))?;
            visit_owner_components_with_charge(
                effect_arguments,
                &mut |cells| charge(budget, cells, span),
                |ty, _| {
                    pending.try_reserve(1).map_err(|_| resource(span))?;
                    pending.push(ty);
                    Ok(())
                },
                |tail, work| {
                    let EffectRowVariable::Rigid(id) = tail.variable() else {
                        return Err(unknown(span));
                    };
                    retain_constraint_variable(id, output, work, span)
                },
            )?;
            pending.push(function.value());
            pending.push(function.domain());
            continue;
        }
        match ty {
            Type::Variable(identity) => {
                let mut retained = false;
                for candidate in output.iter() {
                    charge(budget, 1, span)?;
                    if candidate == identity {
                        retained = true;
                        break;
                    }
                }
                if !retained {
                    charge(budget, 1, span)?;
                    output.try_reserve(1).map_err(|_| resource(span))?;
                    output.push(*identity);
                }
            }
            Type::ResourceApply(_, arguments) => {
                visit_owner_components_with_charge(
                    arguments.iter(),
                    &mut |cells| charge(budget, cells, span),
                    |ty, _| {
                        pending.try_reserve(1).map_err(|_| resource(span))?;
                        pending.push(ty);
                        Ok(())
                    },
                    |tail, work| {
                        let EffectRowVariable::Rigid(id) = tail.variable() else {
                            return Err(unknown(span));
                        };
                        retain_constraint_variable(id, output, work, span)
                    },
                )?;
            }
            Type::Tuple(elements) => {
                charge(budget, elements.len(), span)?;
                pending
                    .try_reserve(elements.len())
                    .map_err(|_| resource(span))?;
                pending.extend(elements.iter().rev());
            }
            Type::Application(function, argument) => {
                charge(budget, 2, span)?;
                pending.try_reserve(2).map_err(|_| resource(span))?;
                pending.push(argument);
                pending.push(function);
            }
            Type::Function(_, _) | Type::EffectfulFunction(_, _) => unreachable!(),
            Type::Bytes | Type::String | Type::Int | Type::Bool | Type::Unit | Type::Nominal(_) => {
            }
            Type::Inference(_) | Type::Forall(_, _) => return Err(unknown(span)),
        }
    }
    Ok(())
}

fn map_kind_type_failure(failure: KindFailure, span: Span) -> EvidenceValidationFailure {
    match failure {
        KindFailure::Resource(_) => type_resource(span),
        failure @ (KindFailure::Internal(_) | KindFailure::Source(_)) => {
            unknown(span).with_kind_context(&failure)
        }
    }
}

fn authenticate_selected_goal_kind(
    application: &InterfaceApplication,
    environments: &KindEnvironments<'_>,
    constraint_work: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<(), EvidenceValidationFailure> {
    environments
        .expect_body_free_interface_argument_with_ledger(
            application.interface(),
            application.arguments(),
            span,
            constraint_work,
        )
        .map_err(|failure| map_selected_kind_constraint_failure(failure, span))
}

fn authenticate_pending_goal_kind_from_prerequisite(
    constraint_work: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<(), EvidenceValidationFailure> {
    // Pending arguments are rebuilt here from a prerequisite authenticated by
    // the declaration pass and a substitution whose every binding was checked
    // against its canonical binder Kind. First-order substitution preserves
    // that judgment, so one edge unit records the proof without re-traversing
    // successively nested rebuilt types.
    charge(constraint_work, 1, span)
}

fn authenticate_selected_substitution_kinds<'a>(
    fact: &CheckedImplementationFact,
    substitution: &[EvidenceSubstitution],
    registry: &'a ResolvedRegistry,
    environments: &KindEnvironments<'a>,
    constraint_work: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<(), EvidenceValidationFailure> {
    if fact.head_parameters.len() != substitution.len() {
        return Err(invalid_root(span));
    }
    for (parameter, binding) in fact.head_parameters.iter().zip(substitution) {
        if binding.parameter() != parameter.id {
            return Err(invalid_root(span));
        }
        let expected = canonical_type_variable_kind(registry, parameter.id, span, constraint_work)
            .map_err(|failure| map_selected_kind_constraint_failure(failure, span))?;
        environments
            .expect_body_free_exact_kind_with_ledger(
                binding.argument(),
                expected,
                span,
                constraint_work,
            )
            .map_err(|failure| map_selected_kind_constraint_failure(failure, span))?;
    }
    Ok(())
}

fn map_selected_kind_type_failure(failure: KindFailure, span: Span) -> EvidenceValidationFailure {
    match failure {
        KindFailure::Resource(_) => type_resource(span),
        failure @ (KindFailure::Internal(_) | KindFailure::Source(_)) => {
            invalid_root(span).with_kind_context(&failure)
        }
    }
}

fn map_selected_kind_constraint_failure(
    failure: KindFailure,
    span: Span,
) -> EvidenceValidationFailure {
    match failure {
        KindFailure::Resource(_) => resource(span),
        failure @ (KindFailure::Internal(_) | KindFailure::Source(_)) => {
            invalid_root(span).with_kind_context(&failure)
        }
    }
}

struct OwnerReplacements {
    types: HashMap<TypeVariableId, Type>,
    rows: HashMap<TypeVariableId, EffectRow>,
}
impl OwnerReplacements {
    /// Inserts into the caller's already charged, fallibly reserved slot.
    /// Any displaced recursive payload is dismantled before returning.
    fn insert_discarding_previous(
        &mut self,
        parameter: TypeVariableId,
        argument: KindedArgument,
    ) -> bool {
        fn discard_replaced_row(row: EffectRow) {
            discard_kinded_argument_iteratively(KindedArgument::RowArg(row));
        }
        match argument {
            KindedArgument::TypeArg(ty) => {
                if let Some(previous) = self.types.insert(parameter, ty) {
                    discard_type_iteratively(previous);
                    true
                } else {
                    false
                }
            }
            KindedArgument::RowArg(row) => {
                if let Some(previous) = self.rows.insert(parameter, row) {
                    discard_replaced_row(previous);
                    true
                } else {
                    false
                }
            }
        }
    }
}
impl Drop for OwnerReplacements {
    fn drop(&mut self) {
        for (_, ty) in self.types.drain() {
            discard_type_iteratively(ty);
        }
        for (_, row) in self.rows.drain() {
            discard_kinded_argument_iteratively(KindedArgument::RowArg(row));
        }
    }
}
fn owner_replacements(
    parameters: &[ResolvedTypeVariable],
    arguments: &[KindedArgument],
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<OwnerReplacements, EvidenceValidationFailure> {
    if parameters.len() != arguments.len() {
        return Err(invalid_root(span));
    }
    charge(budget, parameters.len(), span)?;
    let type_count = arguments
        .iter()
        .filter(|argument| matches!(argument, KindedArgument::TypeArg(_)))
        .count();
    let row_count = arguments.len() - type_count;
    let mut result = OwnerReplacements {
        types: HashMap::new(),
        rows: HashMap::new(),
    };
    result
        .types
        .try_reserve(type_count)
        .map_err(|_| resource(span))?;
    result
        .rows
        .try_reserve(row_count)
        .map_err(|_| resource(span))?;
    for (parameter, argument) in parameters.iter().zip(arguments) {
        charge(budget, 1, span)?;
        if result.types.contains_key(&parameter.id) || result.rows.contains_key(&parameter.id) {
            return Err(invalid_root(span));
        }
        let copied = IterativeArgumentOwner::new(clone_kinded_argument_with_budget(
            argument,
            &mut |cells| charge(budget, cells, span),
        )?);
        match (&parameter.kind, copied.into_inner()) {
            (Kind::EffectRow, KindedArgument::RowArg(row)) => {
                if result.insert_discarding_previous(parameter.id, KindedArgument::RowArg(row)) {
                    return Err(invalid_root(span));
                }
            }
            (kind, KindedArgument::TypeArg(ty)) if *kind != Kind::EffectRow => {
                if result.insert_discarding_previous(parameter.id, KindedArgument::TypeArg(ty)) {
                    return Err(invalid_root(span));
                }
            }
            (_, other) => {
                discard_kinded_argument_iteratively(other);
                return Err(invalid_root(span));
            }
        }
    }
    Ok(result)
}

#[allow(clippy::too_many_arguments)]
fn same_type_after_method_instantiation(
    source: &Type,
    interface_parameters: &[ResolvedTypeVariable],
    interface_arguments: &[KindedArgument],
    method_parameters: &[ResolvedTypeVariable],
    method_arguments: &[Type],
    actual: &Type,
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<bool, EvidenceValidationFailure> {
    if method_parameters.len() != method_arguments.len() {
        return Ok(false);
    }
    let mut replacements =
        owner_replacements(interface_parameters, interface_arguments, budget, span)?;
    charge(budget, method_parameters.len(), span)?;
    replacements
        .types
        .try_reserve(method_parameters.len())
        .map_err(|_| resource(span))?;
    for (parameter, argument) in method_parameters.iter().zip(method_arguments) {
        if parameter.kind == Kind::EffectRow
            || replacements.rows.contains_key(&parameter.id)
            || replacements.types.contains_key(&parameter.id)
        {
            return Err(invalid_root(span));
        }
        let copied = clone_type_with_budget(argument, &mut |cells| charge(budget, cells, span))?;
        replacements.insert_discarding_previous(parameter.id, KindedArgument::TypeArg(copied));
    }
    let expected = IterativeTypeOwner::new(
        substitute_type_and_row_variables_with(
            source,
            &replacements.types,
            &replacements.rows,
            |cells| charge(budget, cells, span),
            || resource(span),
        )?
        .map_err(|_| invalid_root(span))?,
    );
    same_type_charged(&expected, actual, budget, span)
}

/// A checked module program whose retained interface evidence has been authenticated.
#[derive(Debug)]
struct MethodEvidenceAuthentication;

#[derive(Debug)]
pub struct ValidatedInterfaceProgram {
    source: ResolvedModuleProgram,

    _method_evidence: MethodEvidenceAuthentication,
}

impl ValidatedInterfaceProgram {
    /// Returns the combined nominal and constructor registry retained for Core lowering.
    #[must_use]
    pub const fn registry(&self) -> &Arc<ResolvedRegistry> {
        self.source.registry()
    }

    /// Returns dependency-ordered checked module groups.
    #[must_use]
    pub const fn groups(&self) -> &[ResolvedModuleGroup] {
        self.source.groups()
    }

    /// Returns the stable entry module identity.
    #[must_use]
    pub const fn entry(&self) -> ModuleId {
        self.source.entry()
    }

    /// Returns the generated entry expression retained for Core lowering.
    #[must_use]
    pub const fn result(&self) -> &ResolvedExpr {
        self.source.result()
    }
}

/// Checks new linked interface routes and the generated entry before Core assembly.
///
/// # Errors
///
/// Returns an internal validation failure for conflicting linked identities,
/// invalid implementation authorization routes, or invalid generated entry evidence.
pub fn validate_interface_evidence(
    program: ResolvedModuleProgram,
) -> Result<ValidatedInterfaceProgram, EvidenceValidationFailure> {
    validate_interface_evidence_with_budget(
        program,
        &mut InterfaceConstraintBudget::default(),
        &mut TypeWorkBudget::default(),
    )
}

pub(crate) fn validate_interface_evidence_with_budget(
    program: ResolvedModuleProgram,
    constraint_work: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
) -> Result<ValidatedInterfaceProgram, EvidenceValidationFailure> {
    let mut kind_environments =
        build_linked_kind_environments(program.registry(), type_work, program.result().span)?;
    let linked_interfaces = LinkedInterfaceRegistry::build_with_kinds(
        &program,
        &mut kind_environments,
        None,
        constraint_work,
        type_work,
    )?;
    retain_checked_scoped_owners(&program, &linked_interfaces, constraint_work)?;
    validate_linked_entry(
        &program,
        &linked_interfaces,
        &mut kind_environments,
        constraint_work,
        type_work,
    )?;
    Ok(ValidatedInterfaceProgram {
        source: program,

        _method_evidence: MethodEvidenceAuthentication,
    })
}

struct ModuleEvidenceInputs<'a> {
    module: &'a ResolvedModule,
    registry: &'a ResolvedRegistry,
    schemes: &'a [CheckedGlobalScheme],
    interfaces: &'a [crate::resolved::SharedCheckedInterfaceFact],
    implementations: &'a [CheckedImplementationFact],
    method_uses: &'a [crate::elaborate::CheckedMethodUse],
    global_uses: &'a [crate::elaborate::CheckedGlobalUse],
    lexical_sources: &'a [crate::elaborate::CheckedLexicalSource],
    publication: &'a crate::evidence::PendingEvidencePublication,
}

#[derive(Clone, Copy)]
struct MethodEvidenceInputs<'a>(&'a ModuleEvidenceInputs<'a>);

impl<'a> MethodEvidenceInputs<'a> {
    fn module(self) -> &'a ModuleEvidenceInputs<'a> {
        self.0
    }
    fn span(self) -> Span {
        self.0.module.span()
    }
    fn registry(self) -> &'a ResolvedRegistry {
        self.0.registry
    }
    fn interfaces(self) -> impl Iterator<Item = &'a CheckedInterfaceFact> {
        self.0
            .module
            .imported_facts()
            .interface_imports()
            .map(|imported| imported.fact.as_ref())
            .chain(self.0.interfaces.iter().map(AsRef::as_ref))
    }
    fn local_interfaces(self) -> impl Iterator<Item = &'a CheckedInterfaceFact> {
        self.0.interfaces.iter().map(AsRef::as_ref)
    }
    fn implementations(self) -> impl Iterator<Item = &'a CheckedImplementationFact> {
        self.0
            .module
            .imported_facts()
            .implementations()
            .map(|imported| &imported.fact)
            .chain(self.0.implementations.iter())
    }
    fn local_implementations(self) -> impl Iterator<Item = &'a CheckedImplementationFact> {
        self.0.implementations.iter()
    }
    fn globals(self) -> impl Iterator<Item = (BinderId, &'a ConstrainedScheme, &'a Origin)> {
        self.0
            .module
            .imported_facts()
            .globals()
            .map(|f| (f.binder, &f.scheme, &f.origin))
            .chain(
                self.0
                    .schemes
                    .iter()
                    .map(|f| (f.binder, &f.scheme, &f.origin)),
            )
    }
    fn local_globals(self) -> impl Iterator<Item = (BinderId, &'a ConstrainedScheme, &'a Origin)> {
        self.0
            .schemes
            .iter()
            .map(|f| (f.binder, &f.scheme, &f.origin))
    }
    fn owns(self, owner: MethodEvidenceOwner) -> bool {
        let module = self.0.module.module();
        match owner {
            MethodEvidenceOwner::Global(binder) => binder.module() == Some(module),
            MethodEvidenceOwner::Implementation(method) => {
                method.implementation().module() == module
            }
            MethodEvidenceOwner::ResourceFamily(resource) => resource.module() == module,
        }
    }
    fn implementation_method_count(
        self,
        work: &mut InterfaceConstraintBudget,
        span: Span,
    ) -> Result<usize, EvidenceValidationFailure> {
        let mut count = 0usize;
        for implementation in self.implementations() {
            charge(
                work,
                implementation
                    .methods
                    .len()
                    .checked_add(1)
                    .ok_or_else(|| resource(span))?,
                span,
            )?;
            count = count
                .checked_add(implementation.methods.len())
                .ok_or_else(|| resource(span))?;
        }
        Ok(count)
    }
    fn interface_count(
        self,
        work: &mut InterfaceConstraintBudget,
        span: Span,
    ) -> Result<usize, EvidenceValidationFailure> {
        let mut count = 0usize;
        for _ in self.interfaces() {
            charge(work, 1, span)?;
            count = count.checked_add(1).ok_or_else(|| resource(span))?;
        }
        Ok(count)
    }
    fn interface_search_width(
        self,
        work: &mut InterfaceConstraintBudget,
        span: Span,
    ) -> Result<usize, EvidenceValidationFailure> {
        let mut count = 0usize;
        for interface in self.interfaces() {
            charge(work, 1, span)?;
            count = count
                .checked_add(
                    interface
                        .methods
                        .len()
                        .checked_add(1)
                        .ok_or_else(|| resource(span))?,
                )
                .ok_or_else(|| resource(span))?;
        }
        Ok(count)
    }
}

fn clone_method_spelling(
    text: &str,
    work: &mut TypeWorkBudget,
    span: Span,
) -> Result<Box<str>, EvidenceValidationFailure> {
    work.charge(text.len()).map_err(|_| type_resource(span))?;
    let mut result = String::new();
    result
        .try_reserve_exact(text.len())
        .map_err(|_| type_resource(span))?;
    result.push_str(text);
    Ok(result.into_boxed_str())
}

fn copy_catalog_slice<T: Copy>(
    source: &[T],
    work: &mut TypeWorkBudget,
    span: Span,
) -> Result<Box<[T]>, EvidenceValidationFailure> {
    work.charge(source.len())
        .map_err(|()| type_resource(span))?;
    let mut retained = Vec::new();
    retained
        .try_reserve_exact(source.len())
        .map_err(|_| type_resource(span))?;
    retained.extend_from_slice(source);
    Ok(retained.into_boxed_slice())
}

fn copy_catalog_method(
    source: &MethodEvidenceMethod,
    work: &mut TypeWorkBudget,
    span: Span,
) -> Result<MethodEvidenceMethod, EvidenceValidationFailure> {
    Ok(MethodEvidenceMethod {
        id: source.id,
        spelling: clone_method_spelling(&source.spelling, work, span)?,
        interface_parameters: copy_catalog_slice(&source.interface_parameters, work, span)?,
        inherited_parameters: copy_catalog_slice(&source.inherited_parameters, work, span)?,
        parameters: crate::types::clone_kinded_type_parameters_with_budget(
            &source.parameters,
            work,
        )
        .map_err(|()| type_resource(span))?
        .into_boxed_slice(),
        value_type: clone_type_with_budget(&source.value_type, work)
            .map_err(|()| type_resource(span))?,
    })
}

fn copy_catalog_implementation_owner(
    source: &MethodEvidenceImplementationOwner,
    work: &mut TypeWorkBudget,
    span: Span,
) -> Result<MethodEvidenceImplementationOwner, EvidenceValidationFailure> {
    Ok(MethodEvidenceImplementationOwner {
        implementation: source.implementation,
        binder: source.binder,
        head_type_parameter_count: source.head_type_parameter_count,
        source_parameters: crate::types::clone_kinded_type_parameters_with_budget(
            &source.source_parameters,
            work,
        )
        .map_err(|()| type_resource(span))?
        .into_boxed_slice(),
        application: source
            .application
            .clone_with_budget(work)
            .map_err(|()| type_resource(span))?,
    })
}

fn copy_catalog_domain(
    source: &MethodEvidenceDomain,
    work: &mut TypeWorkBudget,
    span: Span,
) -> Result<MethodEvidenceDomain, EvidenceValidationFailure> {
    Ok(MethodEvidenceDomain {
        source_parameters: crate::types::clone_kinded_type_parameters_with_budget(
            &source.source_parameters,
            work,
        )
        .map_err(|()| type_resource(span))?
        .into_boxed_slice(),
        owner: source.owner,
        requirement: source.requirement,
        requirement_position: source.requirement_position,
        method: source.method,
        method_position: source.method_position,
        application: source
            .application
            .clone_with_budget(work)
            .map_err(|()| type_resource(span))?,
    })
}

fn evidence_owner_module(owner: MethodEvidenceOwner) -> Option<ModuleId> {
    match owner {
        MethodEvidenceOwner::Global(binder) => binder.module(),
        MethodEvidenceOwner::Implementation(method) => Some(method.implementation().module()),
        MethodEvidenceOwner::ResourceFamily(resource) => Some(resource.module()),
    }
}

#[allow(clippy::type_complexity)]
fn copy_dependency_catalog_declarations(
    inputs: MethodEvidenceInputs<'_>,
    constraint_work: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
) -> Result<
    (
        Vec<MethodEvidenceMethod>,
        Vec<MethodEvidenceImplementationOwner>,
        Vec<MethodEvidenceDomain>,
    ),
    EvidenceValidationFailure,
> {
    let mut methods = Vec::new();
    let mut owners = Vec::new();
    let mut domains = Vec::new();
    let module = inputs.module();
    for dependency in module.module.imported_lowerings() {
        let catalog = dependency
            .catalog()
            .ok_or_else(|| invalid_root(inputs.span()))?;
        let retained = catalog
            .methods()
            .len()
            .checked_add(catalog.implementation_owners().len())
            .and_then(|count| count.checked_add(catalog.domains().len()))
            .ok_or_else(|| resource(inputs.span()))?;
        charge(constraint_work, retained, inputs.span())?;
        methods
            .try_reserve(catalog.methods().len())
            .map_err(|_| resource(inputs.span()))?;
        owners
            .try_reserve(catalog.implementation_owners().len())
            .map_err(|_| resource(inputs.span()))?;
        domains
            .try_reserve(catalog.domains().len())
            .map_err(|_| resource(inputs.span()))?;
        for method in catalog.methods() {
            if method.id.interface().module() == dependency.module() {
                methods.push(copy_catalog_method(method, type_work, inputs.span())?);
            }
        }
        for owner in catalog.implementation_owners() {
            if owner.implementation.implementation().module() == dependency.module() {
                owners.push(copy_catalog_implementation_owner(
                    owner,
                    type_work,
                    inputs.span(),
                )?);
            }
        }
        for domain in catalog.domains() {
            if evidence_owner_module(domain.owner) == Some(dependency.module()) {
                domains.push(copy_catalog_domain(domain, type_work, inputs.span())?);
            }
        }
    }
    Ok((methods, owners, domains))
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn build_module_method_evidence_catalog(
    module: &ResolvedModule,
    registry: &ResolvedRegistry,
    schemes: &[CheckedGlobalScheme],
    interfaces: &[crate::resolved::SharedCheckedInterfaceFact],
    implementations: &[CheckedImplementationFact],
    method_uses: &[crate::elaborate::CheckedMethodUse],
    global_uses: &[crate::elaborate::CheckedGlobalUse],
    lexical_sources: &[crate::elaborate::CheckedLexicalSource],
    publication: &crate::evidence::PendingEvidencePublication,
    constraint_work: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
) -> Result<MethodEvidenceCatalog, EvidenceValidationFailure> {
    let inputs = ModuleEvidenceInputs {
        module,
        registry,
        schemes,
        interfaces,
        implementations,
        method_uses,
        global_uses,
        lexical_sources,
        publication,
    };
    build_method_evidence_catalog_from_inputs(
        MethodEvidenceInputs(&inputs),
        constraint_work,
        type_work,
    )
}

fn build_method_evidence_catalog_from_inputs(
    inputs: MethodEvidenceInputs<'_>,
    constraint_work: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
) -> Result<MethodEvidenceCatalog, EvidenceValidationFailure> {
    charge(constraint_work, 1, inputs.span())?;
    let (mut methods, mut implementation_owners, mut domains) =
        copy_dependency_catalog_declarations(inputs, constraint_work, type_work)?;
    let mut method_count = methods.len();
    for interface in inputs.local_interfaces() {
        charge(constraint_work, interface.methods.len(), inputs.span())?;
        for _ in &interface.methods {
            method_count = method_count
                .checked_add(1)
                .ok_or_else(|| resource(inputs.span()))?;
        }
    }
    charge(constraint_work, method_count, inputs.span())?;
    methods
        .try_reserve(method_count.saturating_sub(methods.len()))
        .map_err(|_| resource(inputs.span()))?;
    for interface in inputs.local_interfaces() {
        charge(constraint_work, interface.methods.len(), inputs.span())?;
        for method in &interface.methods {
            let mut parameters = Vec::new();
            type_work
                .charge(method.authoritative_type_parameters().len())
                .map_err(|()| type_resource(method.span))?;
            parameters
                .try_reserve(method.authoritative_type_parameters().len())
                .map_err(|_| type_resource(method.span))?;
            for parameter in method.authoritative_type_parameters() {
                parameters.push((
                    parameter.id,
                    clone_kind_with_budget(&parameter.kind, type_work)
                        .map_err(|()| type_resource(method.span))?,
                ));
            }
            type_work
                .charge(interface.parameters.len())
                .map_err(|()| type_resource(method.span))?;
            let mut interface_parameters = Vec::new();
            interface_parameters
                .try_reserve_exact(interface.parameters.len())
                .map_err(|_| type_resource(method.span))?;
            interface_parameters.extend(interface.parameters.iter().map(|parameter| parameter.id));
            method
                .authenticate_inherited_parameters(
                    crate::resolved::OwnerId::Interface(interface.id),
                    &interface.parameters,
                    type_work,
                )
                .map_err(|failure| match failure {
                    crate::resolved::ResolvedBuildFailure::TypeResource => {
                        type_resource(method.span)
                    }
                    _ => invalid_root(method.span),
                })?;
            type_work
                .charge(method.inherited_parameters.len())
                .map_err(|()| type_resource(method.span))?;
            let mut inherited_parameters = Vec::new();
            inherited_parameters
                .try_reserve_exact(method.inherited_parameters.len())
                .map_err(|_| type_resource(method.span))?;
            inherited_parameters.extend(method.inherited_parameters.iter().copied());
            methods.push(MethodEvidenceMethod {
                spelling: clone_method_spelling(&method.spelling, type_work, method.span)?,
                id: method.id,
                inherited_parameters: inherited_parameters.into_boxed_slice(),
                interface_parameters: interface_parameters.into_boxed_slice(),
                parameters: parameters.into_boxed_slice(),
                value_type: clone_type_with_budget(method.value_type(), type_work)
                    .map_err(|()| type_resource(method.span))?,
            });
        }
    }
    charge(
        constraint_work,
        methods.len().saturating_sub(1),
        inputs.span(),
    )?;
    if methods.len() != method_count {
        return Err(invalid_root(inputs.span()));
    }
    // Dependency order need not be identity order across module namespaces.
    // Keep the common already-canonical path, and charge every comparison when
    // canonicalizing a mixed builtin/source catalog before authentication.
    if methods.windows(2).any(|pair| pair[0].id >= pair[1].id) {
        for index in 1..methods.len() {
            let mut cursor = index;
            while cursor > 0 {
                charge(constraint_work, 1, inputs.span())?;
                if methods[cursor - 1].id <= methods[cursor].id {
                    break;
                }
                methods.swap(cursor - 1, cursor);
                cursor -= 1;
            }
        }
        charge(
            constraint_work,
            methods.len().saturating_sub(1),
            inputs.span(),
        )?;
        if methods.windows(2).any(|pair| pair[0].id >= pair[1].id) {
            return Err(invalid_root(inputs.span()));
        }
    }
    let mut implementation_owner_count = implementation_owners.len();
    for implementation in inputs.local_implementations() {
        for method in &implementation.methods {
            let search_work = method
                .scheme
                .requirements
                .len()
                .checked_add(1)
                .and_then(|passes| passes.checked_mul(methods.len()))
                .ok_or_else(|| resource(inputs.span()))?;
            charge(
                constraint_work,
                search_work
                    .checked_add(1)
                    .ok_or_else(|| resource(inputs.span()))?,
                inputs.span(),
            )?;
            if methods.iter().any(|canonical| {
                canonical.id == method.id.method() && method_is_polymorphic(canonical)
            }) || method.scheme.requirements.iter().any(|requirement| {
                interface_has_polymorphic_method(methods.as_slice(), requirement.interface())
            }) || local_representation_captures_method_parameter(
                inputs.registry(),
                method,
                constraint_work,
            )? {
                implementation_owner_count = implementation_owner_count
                    .checked_add(1)
                    .ok_or_else(|| resource(inputs.span()))?;
            }
        }
    }
    charge(constraint_work, implementation_owner_count, inputs.span())?;
    implementation_owners
        .try_reserve_exact(implementation_owner_count.saturating_sub(implementation_owners.len()))
        .map_err(|_| resource(inputs.span()))?;
    for implementation in inputs.local_implementations() {
        for method in &implementation.methods {
            let search_work = method
                .scheme
                .requirements
                .len()
                .checked_add(1)
                .and_then(|passes| passes.checked_mul(methods.len()))
                .ok_or_else(|| resource(inputs.span()))?;
            charge(
                constraint_work,
                search_work
                    .checked_add(1)
                    .ok_or_else(|| resource(inputs.span()))?,
                inputs.span(),
            )?;
            if !(methods.iter().any(|canonical| {
                canonical.id == method.id.method() && method_is_polymorphic(canonical)
            }) || method.scheme.requirements.iter().any(|requirement| {
                interface_has_polymorphic_method(methods.as_slice(), requirement.interface())
            }) || local_representation_captures_method_parameter(
                inputs.registry(),
                method,
                constraint_work,
            )?) {
                continue;
            }
            implementation_owners.push(core_implementation_owner(
                implementation.application(),
                method,
                type_work,
            )?);
        }
    }
    for index in 1..implementation_owners.len() {
        let mut cursor = index;
        while cursor > 0 {
            charge(constraint_work, 1, inputs.span())?;
            if implementation_owners[cursor - 1].implementation
                <= implementation_owners[cursor].implementation
            {
                break;
            }
            implementation_owners.swap(cursor - 1, cursor);
            cursor -= 1;
        }
    }
    charge(
        constraint_work,
        implementation_owners.len().saturating_sub(1),
        inputs.span(),
    )?;
    if implementation_owners.len() != implementation_owner_count
        || implementation_owners
            .windows(2)
            .any(|pair| pair[0].implementation >= pair[1].implementation)
    {
        return Err(invalid_root(inputs.span()));
    }
    for (binder, scheme, origin) in inputs.local_globals() {
        collect_method_evidence_domains(
            &methods,
            scheme,
            MethodEvidenceOwner::Global(binder),
            &mut domains,
            constraint_work,
            type_work,
            origin.primary_span(),
        )?;
    }
    for implementation in inputs.local_implementations() {
        for method in &implementation.methods {
            collect_method_evidence_domains(
                &methods,
                &method.scheme,
                MethodEvidenceOwner::Implementation(method.id),
                &mut domains,
                constraint_work,
                type_work,
                method.span,
            )?;
        }
    }
    let mut lexical_owners = Vec::new();
    let mut occurrences = collect_staged_module_occurrences(
        inputs.module(),
        &methods,
        &mut lexical_owners,
        constraint_work,
        type_work,
    )?;
    if !lexical_owners.is_empty() {
        charge(
            constraint_work,
            inputs.module().implementations.len(),
            inputs.span(),
        )?;
        for implementation in inputs.local_implementations() {
            charge(constraint_work, implementation.methods.len(), inputs.span())?;
            for method in &implementation.methods {
                charge(constraint_work, implementation_owners.len(), method.span)?;
                let Err(position) = implementation_owners
                    .binary_search_by_key(&method.id, |owner| owner.implementation)
                else {
                    continue;
                };
                if !lexical_header_captures_method_parameter(
                    &lexical_owners,
                    method,
                    constraint_work,
                )? {
                    continue;
                }
                let retention_work = implementation_owners
                    .len()
                    .checked_sub(position)
                    .and_then(|shifted| shifted.checked_add(1))
                    .ok_or_else(|| resource(method.span))?;
                charge(constraint_work, retention_work, method.span)?;
                implementation_owners
                    .try_reserve(1)
                    .map_err(|_| resource(method.span))?;
                implementation_owners.insert(
                    position,
                    core_implementation_owner(implementation.application(), method, type_work)?,
                );
            }
        }
    }
    // Slot identities are allocation addresses. Charge the complete bounded
    // insertion-sort window before scanning so allocator order cannot change
    // the defining transaction's work admission.
    let sorting_work = occurrences
        .len()
        .checked_mul(occurrences.len().saturating_sub(1))
        .map(|work| work / 2)
        .ok_or_else(|| resource(inputs.span()))?;
    charge(constraint_work, sorting_work, inputs.span())?;
    for index in 1..occurrences.len() {
        let mut cursor = index;
        while cursor > 0 {
            if occurrences[cursor - 1].slot <= occurrences[cursor].slot {
                break;
            }
            occurrences.swap(cursor - 1, cursor);
            cursor -= 1;
        }
    }
    charge(
        constraint_work,
        occurrences.len().saturating_sub(1),
        inputs.span(),
    )?;
    if occurrences
        .windows(2)
        .any(|pair| pair[0].slot == pair[1].slot)
    {
        return Err(invalid_root(inputs.span()));
    }
    let (adapters, expectations) = build_method_evidence_expectations(
        inputs,
        &methods,
        &implementation_owners,
        &lexical_owners,
        &domains,
        &occurrences,
        constraint_work,
        type_work,
        inputs.span(),
    )?;
    let concrete_sources = build_method_evidence_concrete_sources(
        inputs,
        &methods,
        &occurrences,
        &adapters,
        &expectations,
        constraint_work,
        type_work,
        inputs.span(),
    )?;
    charge(constraint_work, 1, inputs.span())?;
    let mut catalog = MethodEvidenceCatalog::new(
        methods,
        implementation_owners,
        domains,
        occurrences,
        adapters,
        concrete_sources,
        expectations,
    );
    catalog.set_lexical_owners(lexical_owners);
    Ok(catalog)
}

fn method_is_polymorphic(method: &MethodEvidenceMethod) -> bool {
    !method.parameters.is_empty()
}

fn interface_has_polymorphic_method(
    methods: &[MethodEvidenceMethod],
    interface: InterfaceId,
) -> bool {
    methods
        .iter()
        .any(|method| method.id.interface() == interface && method_is_polymorphic(method))
}

fn clone_evidence_substitution_arguments(
    substitution: &[EvidenceSubstitution],
    type_work: &mut TypeWorkBudget,
    span: Span,
) -> Result<TypeBuffer, EvidenceValidationFailure> {
    type_work
        .charge(substitution.len())
        .map_err(|()| type_resource(span))?;
    let mut arguments = TypeBuffer::new();
    arguments
        .try_reserve(substitution.len())
        .map_err(|_| type_resource(span))?;
    for binding in substitution {
        arguments.push(
            clone_type_with_budget(binding.argument(), type_work)
                .map_err(|()| type_resource(span))?,
        );
    }
    Ok(arguments)
}

#[allow(
    clippy::too_many_arguments,
    reason = "concrete adapter sources are derived from linked selection and checked method facts"
)]
fn build_method_evidence_concrete_sources(
    inputs: MethodEvidenceInputs<'_>,
    methods: &[MethodEvidenceMethod],
    occurrences: &[MethodEvidenceOccurrence],
    adapters: &[MethodEvidenceAdapter],
    expectations: &[MethodEvidenceExpectation],
    constraint_work: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
    span: Span,
) -> Result<Vec<crate::core::dialect::MethodEvidenceConcreteSource>, EvidenceValidationFailure> {
    let mut pending = Vec::new();
    charge(constraint_work, expectations.len(), span)?;
    let edge_count = expectations
        .iter()
        .filter(|expectation| {
            matches!(
                expectation.role,
                MethodEvidenceExpectedRole::AdapterEdge { .. }
            )
        })
        .count();
    let root_pass_work = expectations
        .len()
        .checked_add(edge_count)
        .ok_or_else(|| resource(span))?;
    charge(constraint_work, root_pass_work, span)?;
    pending
        .try_reserve(edge_count)
        .map_err(|_| resource(span))?;
    for expectation in expectations {
        let MethodEvidenceExpectedRole::AdapterEdge { adapter, ordinal } = expectation.role else {
            continue;
        };
        let edge = adapters
            .get(adapter)
            .and_then(|adapter| adapter.prerequisites.get(ordinal))
            .ok_or_else(|| invalid_root(span))?;
        if let crate::core::dialect::MethodEvidenceExpectedProducer::Monomorphic {
            selection_node,
            producer: crate::core::dialect::MethodEvidenceProducer::Adapter { implementation },
            ..
        } = edge.producer
        {
            pending.push((
                expectation.occurrence.ok_or_else(|| invalid_root(span))?,
                selection_node,
                implementation,
            ));
        }
    }

    let mut sources = Vec::new();
    while let Some((occurrence_slot, selection_node, implementation)) = pending.pop() {
        charge(
            constraint_work,
            occurrences
                .len()
                .checked_add(sources.len())
                .ok_or_else(|| resource(span))?,
            span,
        )?;
        if sources.iter().any(
            |source: &crate::core::dialect::MethodEvidenceConcreteSource| {
                source.occurrence == occurrence_slot
                    && source.selection_node == selection_node
                    && source.implementation == implementation
            },
        ) {
            continue;
        }
        let occurrence = occurrences
            .iter()
            .find(|occurrence| occurrence.slot == occurrence_slot)
            .ok_or_else(|| invalid_root(span))?;
        let EvidenceNode::Implementation {
            substitution,
            prerequisites,
            methods: selected_methods,
            ..
        } = occurrence
            .selection
            .node(selection_node)
            .ok_or_else(|| invalid_root(span))?
        else {
            return Err(invalid_root(span));
        };
        charge(
            constraint_work,
            selected_methods
                .len()
                .checked_add(methods.len())
                .ok_or_else(|| resource(span))?,
            span,
        )?;
        if !selected_methods.contains(&implementation)
            || methods
                .iter()
                .any(|method| method.id == implementation.method() && method_is_polymorphic(method))
        {
            return Err(invalid_root(span));
        }
        let method_count = inputs.implementation_method_count(constraint_work, span)?;
        charge(constraint_work, method_count, span)?;
        let checked = inputs
            .implementations()
            .flat_map(|implementation| implementation.methods.iter())
            .find(|method| method.id == implementation)
            .ok_or_else(|| invalid_root(span))?;
        if checked.head_type_parameter_count() != substitution.len()
            || checked.scheme.requirements.len() != prerequisites.len()
        {
            return Err(invalid_root(span));
        }
        charge(constraint_work, prerequisites.len(), span)?;
        let mut prerequisite_count = 0usize;
        for prerequisite in prerequisites {
            let methods = match occurrence
                .selection
                .node(*prerequisite)
                .ok_or_else(|| invalid_root(span))?
            {
                EvidenceNode::Abstract { methods, .. } | EvidenceNode::Lexical { methods, .. } => {
                    methods.len()
                }

                EvidenceNode::Implementation { methods, .. } => methods.len(),
            };
            prerequisite_count = prerequisite_count
                .checked_add(methods)
                .ok_or_else(|| resource(span))?;
        }
        charge(constraint_work, prerequisite_count, span)?;
        let retained_work = 5usize
            .checked_add(
                prerequisite_count
                    .checked_mul(2)
                    .ok_or_else(|| resource(span))?,
            )
            .ok_or_else(|| resource(span))?;
        charge(constraint_work, retained_work, span)?;
        sources.try_reserve(1).map_err(|_| resource(span))?;
        let head_arguments = clone_evidence_substitution_arguments(substitution, type_work, span)?;
        let mut retained_prerequisites = Vec::new();
        let construction_work = prerequisites
            .len()
            .checked_add(prerequisite_count)
            .ok_or_else(|| resource(span))?;
        charge(constraint_work, construction_work, span)?;
        charge(constraint_work, prerequisite_count, span)?;
        retained_prerequisites
            .try_reserve_exact(prerequisite_count)
            .map_err(|_| resource(span))?;
        for prerequisite in prerequisites {
            match occurrence
                .selection
                .node(*prerequisite)
                .ok_or_else(|| invalid_root(span))?
            {
                EvidenceNode::Lexical { methods, .. } => {
                    for method in methods {
                        retained_prerequisites.push(
                            crate::core::dialect::MethodEvidenceConcretePrerequisite {
                                selection_node: *prerequisite,
                                method: *method,
                                scope_position: None,
                            },
                        );
                    }
                }
                EvidenceNode::Abstract { methods, .. } => {
                    for method in methods {
                        let EvidenceNode::Abstract { requirement, .. } = occurrence
                            .selection
                            .node(*prerequisite)
                            .ok_or_else(|| invalid_root(span))?
                        else {
                            unreachable!()
                        };
                        retained_prerequisites.push(
                            crate::core::dialect::MethodEvidenceConcretePrerequisite {
                                selection_node: *prerequisite,
                                method: *method,
                                scope_position: Some(method_evidence_scope_position(
                                    inputs,
                                    occurrence,
                                    requirement,
                                    *method,
                                    constraint_work,
                                    span,
                                )?),
                            },
                        );
                    }
                }
                EvidenceNode::Implementation {
                    methods: selected_methods,
                    ..
                } => {
                    for method in selected_methods {
                        retained_prerequisites.push(
                            crate::core::dialect::MethodEvidenceConcretePrerequisite {
                                selection_node: *prerequisite,
                                method: method.method(),
                                scope_position: None,
                            },
                        );
                        charge(constraint_work, methods.len(), span)?;
                        if !methods
                            .iter()
                            .any(|row| row.id == method.method() && method_is_polymorphic(row))
                        {
                            charge(constraint_work, 1, span)?;
                            pending.try_reserve(1).map_err(|_| resource(span))?;
                            pending.push((occurrence_slot, *prerequisite, *method));
                        }
                    }
                }
            }
        }
        sources.push(crate::core::dialect::MethodEvidenceConcreteSource {
            occurrence: occurrence_slot,
            selection_node,
            implementation,
            binder: checked.binder,
            head_arguments: head_arguments.into_boxed_slice(),
            prerequisites: retained_prerequisites.into_boxed_slice(),
        });
    }
    Ok(sources)
}

#[allow(
    clippy::too_many_arguments,
    reason = "module evidence rows use distinct checked inputs"
)]
fn build_method_evidence_expectations(
    inputs: MethodEvidenceInputs<'_>,
    methods: &[MethodEvidenceMethod],
    implementation_owners: &[MethodEvidenceImplementationOwner],
    lexical_owners: &[crate::core::dialect::MethodEvidenceLexicalOwner],
    domains: &[MethodEvidenceDomain],
    occurrences: &[MethodEvidenceOccurrence],
    constraint_work: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
    span: Span,
) -> Result<(Vec<MethodEvidenceAdapter>, Vec<MethodEvidenceExpectation>), EvidenceValidationFailure>
{
    let mut expectations = Vec::new();
    let initial_expectations = implementation_owners
        .len()
        .checked_add(domains.len())
        .ok_or_else(|| resource(span))?;
    charge(constraint_work, initial_expectations, span)?;
    expectations
        .try_reserve(initial_expectations)
        .map_err(|_| resource(span))?;
    for (owner, row) in implementation_owners
        .iter()
        .enumerate()
        .filter(|(_, row)| inputs.owns(MethodEvidenceOwner::Implementation(row.implementation)))
    {
        expectations.push(MethodEvidenceExpectation {
            occurrence: None,
            method: row.implementation.method(),
            role: MethodEvidenceExpectedRole::ImplementationOwner { owner },
        });
    }
    let mut domain_expectations = HashMap::new();
    charge(constraint_work, domains.len(), span)?;
    domain_expectations
        .try_reserve(domains.len())
        .map_err(|_| resource(span))?;
    for (domain, row) in domains
        .iter()
        .enumerate()
        .filter(|(_, row)| inputs.owns(row.owner))
    {
        let expectation = expectations.len();
        expectations.push(MethodEvidenceExpectation {
            occurrence: None,
            method: row.method,
            role: MethodEvidenceExpectedRole::Domain { domain },
        });
        if domain_expectations.insert(domain, expectation).is_some() {
            return Err(invalid_root(span));
        }
    }

    let mut lexical_expectations = HashMap::new();
    for (owner, row) in lexical_owners.iter().enumerate() {
        charge(constraint_work, 2, span)?;
        expectations.try_reserve(1).map_err(|_| resource(span))?;
        lexical_expectations
            .try_reserve(1)
            .map_err(|_| resource(span))?;
        let expectation = expectations.len();
        expectations.push(MethodEvidenceExpectation {
            occurrence: None,
            method: row.method,
            role: MethodEvidenceExpectedRole::LexicalOwner { owner },
        });
        if lexical_expectations
            .insert((row.source, row.method), expectation)
            .is_some()
        {
            return Err(invalid_root(span));
        }
        charge(constraint_work, row.captures.len(), span)?;
        expectations
            .try_reserve(row.captures.len())
            .map_err(|_| resource(span))?;
        for ordinal in 0..row.captures.len() {
            expectations.push(MethodEvidenceExpectation {
                occurrence: None,
                method: row.method,
                role: MethodEvidenceExpectedRole::LexicalCaptureUse { owner, ordinal },
            });
        }
    }

    let mut adapters = Vec::new();
    let mut adapter_expectations = HashMap::new();
    let mut adapter_rows = HashMap::new();
    for occurrence in occurrences {
        let mut pending = Vec::new();
        charge(
            constraint_work,
            occurrence
                .selection
                .node_count()
                .checked_mul(2)
                .ok_or_else(|| resource(span))?,
            span,
        )?;
        pending
            .try_reserve(occurrence.selection.node_count())
            .map_err(|_| resource(span))?;
        pending.push(occurrence.selection.root());
        let mut visited = HashSet::new();
        visited
            .try_reserve(occurrence.selection.node_count())
            .map_err(|_| resource(span))?;
        while let Some(identity) = pending.pop() {
            charge(constraint_work, 1, span)?;
            if !visited.insert(identity) {
                continue;
            }
            let evidence = occurrence.selection.node(identity);
            let Some(EvidenceNode::Implementation {
                substitution,
                methods: selected_methods,
                ..
            }) = evidence
            else {
                continue;
            };
            let prerequisites = evidence
                .and_then(EvidenceNode::executable_prerequisites)
                .ok_or_else(|| invalid_root(span))?;
            charge(constraint_work, prerequisites.len(), span)?;
            pending
                .try_reserve(prerequisites.len())
                .map_err(|_| resource(span))?;
            pending.extend(prerequisites.iter().copied());
            charge(constraint_work, selected_methods.len(), span)?;
            for selected in selected_methods.iter().filter(|selected| {
                identity != occurrence.selection.root()
                    || occurrence
                        .checked_method
                        .is_none_or(|requested| requested == selected.method())
            }) {
                charge(constraint_work, methods.len(), span)?;
                let polymorphic = methods
                    .iter()
                    .any(|method| method.id == selected.method() && method_is_polymorphic(method));
                let producer_count = inputs.implementation_method_count(constraint_work, span)?;
                charge(constraint_work, producer_count, span)?;
                let producer = inputs
                    .implementations()
                    .flat_map(|implementation| implementation.methods.iter())
                    .find(|method| method.id == *selected)
                    .ok_or_else(|| invalid_root(span))?;
                let prerequisite_search = producer
                    .scheme
                    .requirements
                    .len()
                    .checked_mul(methods.len())
                    .ok_or_else(|| resource(span))?;
                charge(constraint_work, prerequisite_search, span)?;
                if !polymorphic
                    && !producer.scheme.requirements.iter().any(|requirement| {
                        interface_has_polymorphic_method(methods, requirement.interface())
                    })
                {
                    continue;
                }
                if producer.head_type_parameter_count() != substitution.len() {
                    return Err(invalid_root(span));
                }
                let head_arguments =
                    clone_evidence_substitution_arguments(substitution, type_work, span)?;
                let mut source_parameters = Vec::new();
                type_work
                    .charge(producer.scheme.type_parameters.len())
                    .map_err(|()| type_resource(span))?;
                source_parameters
                    .try_reserve_exact(producer.scheme.type_parameters.len())
                    .map_err(|_| type_resource(span))?;
                source_parameters.extend(
                    producer
                        .scheme
                        .type_parameters
                        .iter()
                        .map(|parameter| parameter.0),
                );
                // The adapter row retains both its row identity and the exact
                // selection-node identity that owns its head substitution.
                charge(constraint_work, 2, span)?;
                adapters.try_reserve(1).map_err(|_| resource(span))?;
                let adapter = adapters.len();
                adapters.push(MethodEvidenceAdapter {
                    selection_node: identity,
                    implementation: *selected,
                    binder: producer.binder,
                    source_parameters: source_parameters.into_boxed_slice(),
                    head_arguments: head_arguments.into_boxed_slice(),
                    prerequisites: Box::new([]),
                });
                charge(constraint_work, 2, span)?;
                adapter_rows.try_reserve(1).map_err(|_| resource(span))?;
                if adapter_rows
                    .insert((occurrence.slot, identity, *selected), adapter)
                    .is_some()
                {
                    return Err(invalid_root(span));
                }
                // Monomorphic parents have no abstraction to publish. Their
                // passive row authenticates the actual prerequisite edges.
                if !polymorphic {
                    continue;
                }
                charge(constraint_work, 1, span)?;
                expectations.try_reserve(1).map_err(|_| resource(span))?;
                let expectation = expectations.len();
                expectations.push(MethodEvidenceExpectation {
                    occurrence: Some(occurrence.slot),
                    method: selected.method(),
                    role: MethodEvidenceExpectedRole::Adapter { adapter },
                });
                // The lookup entry retains the adapter expectation relation
                // and its selection-node-specific key.
                charge(constraint_work, 2, span)?;
                adapter_expectations
                    .try_reserve(1)
                    .map_err(|_| resource(span))?;
                if adapter_expectations
                    .insert((occurrence.slot, identity, *selected), expectation)
                    .is_some()
                {
                    return Err(invalid_root(span));
                }
            }
        }
    }

    for occurrence in occurrences {
        let producer_method_width = match occurrence
            .selection
            .node(occurrence.selection.root())
            .ok_or_else(|| invalid_root(span))?
        {
            EvidenceNode::Abstract { methods, .. } | EvidenceNode::Lexical { methods, .. } => {
                methods.len()
            }

            EvidenceNode::Implementation { methods, .. } => methods.len(),
        };
        let lexical_node_count = if lexical_owners.is_empty() {
            0
        } else {
            occurrence.selection.node_count()
        };
        charge(constraint_work, lexical_node_count, span)?;
        for index in 0..lexical_node_count {
            #[cfg(test)]
            LEXICAL_PLAN_INSPECTIONS.with(|count| count.set(count.get() + 1));
            let selection_node = EvidenceNodeId::new(index);
            let Some(EvidenceNode::Lexical {
                source,
                methods: selected,
            }) = occurrence.selection.node(selection_node)
            else {
                continue;
            };
            for method in selected {
                if selection_node == occurrence.selection.root()
                    && occurrence
                        .checked_method
                        .is_some_and(|requested| requested != *method)
                {
                    continue;
                }
                charge(
                    constraint_work,
                    lexical_owners.len().saturating_add(1),
                    span,
                )?;
                let owner = lexical_owners
                    .iter()
                    .position(|owner| owner.source == source && owner.method == *method)
                    .ok_or_else(|| invalid_root(span))?;
                expectations.try_reserve(1).map_err(|_| resource(span))?;
                expectations.push(MethodEvidenceExpectation {
                    occurrence: Some(occurrence.slot),
                    method: *method,
                    role: MethodEvidenceExpectedRole::LexicalUse {
                        owner,
                        selection_node,
                    },
                });
            }
        }
        if let Some(method) = occurrence.checked_method.filter(|id| {
            methods
                .iter()
                .any(|method| method.id == *id && method_is_polymorphic(method))
        }) {
            charge(
                constraint_work,
                domains
                    .len()
                    .checked_add(adapter_expectations.len())
                    .and_then(|work| work.checked_add(producer_method_width))
                    .ok_or_else(|| resource(span))?,
                span,
            )?;
            let producer = method_evidence_producer_expectation(
                occurrence,
                occurrence.selection.root(),
                method,
                domains,
                &domain_expectations,
                &adapter_expectations,
                &lexical_expectations,
                span,
            )?;
            charge(constraint_work, 1, span)?;
            expectations.try_reserve(1).map_err(|_| resource(span))?;
            expectations.push(MethodEvidenceExpectation {
                occurrence: Some(occurrence.slot),
                method,
                role: MethodEvidenceExpectedRole::Instantiation { producer },
            });
        } else if occurrence.checked_method.is_none() {
            charge(constraint_work, methods.len(), span)?;
            for method in methods.iter().filter(|method| {
                method.id.interface() == occurrence.selection.interface()
                    && method_is_polymorphic(method)
            }) {
                charge(constraint_work, domains.len(), span)?;
                let domain = domains
                    .iter()
                    .position(|domain| {
                        Some(domain.owner) == occurrence.target_owner
                            && occurrence.target_requirement == Some(domain.requirement)
                            && domain.method == method.id
                    })
                    .ok_or_else(|| invalid_root(span))?;
                charge(
                    constraint_work,
                    domains
                        .len()
                        .checked_add(adapter_expectations.len())
                        .and_then(|count| count.checked_add(producer_method_width))
                        .and_then(|count| count.checked_add(1))
                        .ok_or_else(|| resource(span))?,
                    span,
                )?;
                expectations.try_reserve(1).map_err(|_| resource(span))?;
                expectations.push(MethodEvidenceExpectation {
                    occurrence: Some(occurrence.slot),
                    method: method.id,
                    role: MethodEvidenceExpectedRole::Application {
                        domain,
                        producer: method_evidence_producer_expectation(
                            occurrence,
                            occurrence.selection.root(),
                            method.id,
                            domains,
                            &domain_expectations,
                            &adapter_expectations,
                            &lexical_expectations,
                            span,
                        )?,
                    },
                });
            }
        }
        let mut pending = Vec::new();
        charge(
            constraint_work,
            occurrence
                .selection
                .node_count()
                .checked_mul(2)
                .ok_or_else(|| resource(span))?,
            span,
        )?;
        pending
            .try_reserve(occurrence.selection.node_count())
            .map_err(|_| resource(span))?;
        pending.push(occurrence.selection.root());
        let mut visited = HashSet::new();
        visited
            .try_reserve(occurrence.selection.node_count())
            .map_err(|_| resource(span))?;
        while let Some(identity) = pending.pop() {
            charge(constraint_work, 1, span)?;
            if !visited.insert(identity) {
                continue;
            }
            let node = occurrence
                .selection
                .node(identity)
                .ok_or_else(|| invalid_root(span))?;
            let EvidenceNode::Implementation {
                prerequisites,
                methods: selected_methods,
                ..
            } = node
            else {
                continue;
            };
            charge(constraint_work, prerequisites.len(), span)?;
            charge(constraint_work, selected_methods.len(), span)?;
            for selected in selected_methods.iter().filter(|selected| {
                identity != occurrence.selection.root()
                    || occurrence
                        .checked_method
                        .is_none_or(|requested| requested == selected.method())
            }) {
                let producer_count = inputs.implementation_method_count(constraint_work, span)?;
                charge(constraint_work, producer_count, span)?;
                let producer = inputs
                    .implementations()
                    .flat_map(|implementation| implementation.methods.iter())
                    .find(|method| method.id == *selected)
                    .ok_or_else(|| invalid_root(span))?;
                if producer.scheme.requirements.len() != prerequisites.len() {
                    return Err(invalid_root(span));
                }
                let adapter_row = adapter_rows
                    .get(&(occurrence.slot, identity, *selected))
                    .copied();
                if adapter_row.is_none() {
                    charge(constraint_work, prerequisites.len(), span)?;
                    pending
                        .try_reserve(prerequisites.len())
                        .map_err(|_| resource(span))?;
                    pending.extend(prerequisites.iter().copied());
                    continue;
                }
                charge(constraint_work, prerequisites.len(), span)?;
                let mut adapter_edge_count = 0usize;
                for prerequisite in prerequisites {
                    let child = occurrence
                        .selection
                        .node(*prerequisite)
                        .ok_or_else(|| invalid_root(span))?;
                    let methods = match child {
                        EvidenceNode::Abstract { methods, .. }
                        | EvidenceNode::Lexical { methods, .. } => methods.len(),

                        EvidenceNode::Implementation { methods, .. } => methods.len(),
                    };
                    adapter_edge_count = adapter_edge_count
                        .checked_add(methods)
                        .ok_or_else(|| resource(span))?;
                }
                charge(constraint_work, adapter_edge_count, span)?;
                let mut adapter_edges = Vec::new();
                adapter_edges
                    .try_reserve_exact(adapter_edge_count)
                    .map_err(|_| resource(span))?;
                for (prerequisite, requirement) in
                    prerequisites.iter().zip(&producer.scheme.requirements)
                {
                    let child = occurrence
                        .selection
                        .node(*prerequisite)
                        .ok_or_else(|| invalid_root(span))?;
                    macro_rules! retain_edge {
                        ($method:expr) => {{
                            let method = $method;
                            let producer_search_work = methods
                                .len()
                                .checked_add(domains.len())
                                .and_then(|count| count.checked_add(domain_expectations.len()))
                                .and_then(|count| count.checked_add(adapter_expectations.len()))
                                .and_then(|count| count.checked_add(expectations.len()))
                                .and_then(|count| {
                                    let child_methods = match child {

                                        EvidenceNode::Abstract { methods, .. } | EvidenceNode::Lexical { methods, .. }
                 => methods.len(),
                                        EvidenceNode::Implementation { methods, .. } => {
                                            methods.len()
                                        }
                                    };
                                    count.checked_add(child_methods)
                                })
                                .ok_or_else(|| resource(span))?;
                            charge(constraint_work, producer_search_work, span)?;
                            let producer = if methods
                                .iter()
                                .any(|row| row.id == method && method_is_polymorphic(row))
                            {
                                crate::core::dialect::MethodEvidenceExpectedProducer::Authenticated(
                                    method_evidence_producer_expectation(
                                        occurrence,
                                        *prerequisite,
                                        method,
                                        domains,
                                        &domain_expectations,
                                        &adapter_expectations,
                                        &lexical_expectations,
                                        span,
                                    )?,
                                )
                            } else {
                                let semantic_producer = method_evidence_semantic_producer(
                                    &occurrence.selection,
                                    *prerequisite,
                                    method,
                                    span,
                                )?;
                                let producer_scope_position = match semantic_producer {
                                    crate::core::dialect::MethodEvidenceProducer::Abstract {
                                        requirement,
                                    } => Some(method_evidence_scope_position(
                                        inputs,
                                        occurrence,
                                        requirement,
                                        method,
                                        constraint_work,
                                        span,
                                    )?),
                                    crate::core::dialect::MethodEvidenceProducer::Adapter {
                                        ..
                                    } | crate::core::dialect::MethodEvidenceProducer::Lexical { .. }
                                    => None,
                                };
                                crate::core::dialect::MethodEvidenceExpectedProducer::Monomorphic {
                                    selection_node: *prerequisite,
                                    producer_scope_position,
                                    producer: semantic_producer,
                                }
                            };
                            let retained_edge_work = 1usize
                                .checked_add(match producer {
                                    crate::core::dialect::MethodEvidenceExpectedProducer::Authenticated(_) => 0,
                                    crate::core::dialect::MethodEvidenceExpectedProducer::Monomorphic { .. } => 2,
                                })
                                .ok_or_else(|| resource(span))?;
                            charge(constraint_work, retained_edge_work, span)?;
                            adapter_edges.try_reserve(1).map_err(|_| resource(span))?;
                            let ordinal = adapter_edges.len();
                            let interface_search_work = inputs.interface_search_width(
                                constraint_work,
                                span,
                            )?;
                            charge(constraint_work, interface_search_work, span)?;
                            let interface = inputs
                                .interfaces()
                                .find(|interface| interface.id == method.interface())
                                .ok_or_else(|| invalid_root(span))?;
                            let canonical = interface
                                .methods
                                .iter()
                                .find(|candidate| candidate.id == method)
                                .ok_or_else(|| invalid_root(span))?;
                            let mut method_parameters = Vec::new();
                            type_work
                                .charge(canonical.authoritative_type_parameters().len())
                                .map_err(|()| type_resource(span))?;
                            method_parameters
                                .try_reserve_exact(canonical.authoritative_type_parameters().len())
                                .map_err(|_| type_resource(span))?;
                            for parameter in canonical.authoritative_type_parameters() {
                                method_parameters.push((
                                    parameter.id,
                                    clone_kind_with_budget(&parameter.kind, type_work)
                                        .map_err(|()| type_resource(span))?,
                                ));
                            }
                            adapter_edges.push(crate::core::dialect::MethodEvidenceAdapterEdge {
                                owner: MethodEvidenceOwner::Implementation(*selected),
                                requirement: requirement.id,
                                method,
                                application: requirement
                                    .application()
                                    .clone_with_budget(type_work)
                                    .map_err(|()| type_resource(span))?,
                                interface_parameters: {
                                    type_work
                                        .charge(interface.parameters.len())
                                        .map_err(|()| type_resource(span))?;
                                    let mut parameters = Vec::new();
                                    parameters
                                        .try_reserve_exact(interface.parameters.len())
                                        .map_err(|_| type_resource(span))?;
                                    parameters.extend(interface.parameters.iter().map(|parameter| parameter.id));
                                    parameters.into_boxed_slice()
                                },
                                method_parameters: method_parameters.into_boxed_slice(),
                                value_type: clone_type_with_budget(
                                    canonical.value_type(),
                                    type_work,
                                )
                                .map_err(|()| type_resource(span))?,
                                producer,
                            });
                            charge(constraint_work, 1, span)?;
                            expectations.try_reserve(1).map_err(|_| resource(span))?;
                            expectations.push(MethodEvidenceExpectation {
                                occurrence: Some(occurrence.slot),
                                method,
                                role: MethodEvidenceExpectedRole::AdapterEdge {
                                    adapter: adapter_row.ok_or_else(|| invalid_root(span))?,
                                    ordinal,
                                },
                            });
                        }};
                    }
                    match child {
                        EvidenceNode::Abstract { methods, .. }
                        | EvidenceNode::Lexical { methods, .. } => {
                            for method in methods {
                                retain_edge!(*method);
                            }
                        }
                        EvidenceNode::Implementation { methods, .. } => {
                            for method in methods {
                                retain_edge!(method.method());
                            }
                        }
                    }
                    charge(constraint_work, 1, span)?;
                    pending.try_reserve(1).map_err(|_| resource(span))?;
                    pending.push(*prerequisite);
                }
                if let Some(adapter) = adapter_row {
                    let row = adapters
                        .get_mut(adapter)
                        .ok_or_else(|| invalid_root(span))?;
                    if !row.prerequisites.is_empty() {
                        return Err(invalid_root(span));
                    }
                    row.prerequisites = adapter_edges.into_boxed_slice();
                }
            }
        }
    }
    Ok((adapters, expectations))
}

#[allow(
    clippy::too_many_arguments,
    reason = "producer identities use separate canonical domain, adapter, and lexical indexes"
)]
fn method_evidence_producer_expectation(
    occurrence: &MethodEvidenceOccurrence,
    node: EvidenceNodeId,
    method: MethodId,
    domains: &[MethodEvidenceDomain],
    domain_expectations: &HashMap<usize, usize>,
    adapter_expectations: &HashMap<(usize, EvidenceNodeId, ImplMethodId), usize>,
    lexical_expectations: &HashMap<(crate::interface::LexicalEvidenceId, MethodId), usize>,
    span: Span,
) -> Result<usize, EvidenceValidationFailure> {
    match occurrence
        .selection
        .node(node)
        .ok_or_else(|| invalid_root(span))?
    {
        // The registered witness method has no method-local polymorphism;
        // it cannot authorize an abstract producer instantiation anchor.
        EvidenceNode::Lexical { source, methods } if methods.contains(&method) => {
            lexical_expectations
                .get(&(source, method))
                .copied()
                .ok_or_else(|| invalid_root(span))
        }
        EvidenceNode::Abstract {
            requirement,
            methods,
        } if methods.contains(&method) => domains
            .iter()
            .position(|domain| {
                Some(domain.owner) == occurrence.scope
                    && domain.requirement == requirement
                    && domain.method == method
            })
            .and_then(|domain| domain_expectations.get(&domain).copied())
            .ok_or_else(|| invalid_root(span)),
        EvidenceNode::Implementation { methods, .. } => methods
            .iter()
            .find(|candidate| candidate.method() == method)
            .and_then(|implementation| {
                adapter_expectations
                    .get(&(occurrence.slot, node, *implementation))
                    .copied()
            })
            .ok_or_else(|| invalid_root(span)),
        EvidenceNode::Abstract { .. } | EvidenceNode::Lexical { .. } => Err(invalid_root(span)),
    }
}

fn method_evidence_semantic_producer(
    selection: &EvidenceSelection,
    node: EvidenceNodeId,
    method: MethodId,
    span: Span,
) -> Result<crate::core::dialect::MethodEvidenceProducer, EvidenceValidationFailure> {
    match selection.node(node).ok_or_else(|| invalid_root(span))? {
        EvidenceNode::Lexical { source, methods } if methods.contains(&method) => {
            Ok(crate::core::dialect::MethodEvidenceProducer::Lexical { source })
        }
        EvidenceNode::Abstract {
            requirement,
            methods,
        } if methods.contains(&method) => {
            Ok(crate::core::dialect::MethodEvidenceProducer::Abstract { requirement })
        }
        EvidenceNode::Implementation { methods, .. } => methods
            .iter()
            .find(|candidate| candidate.method() == method)
            .copied()
            .map(
                |implementation| crate::core::dialect::MethodEvidenceProducer::Adapter {
                    implementation,
                },
            )
            .ok_or_else(|| invalid_root(span)),
        EvidenceNode::Abstract { .. } | EvidenceNode::Lexical { .. } => Err(invalid_root(span)),
    }
}

fn method_evidence_scope_position(
    inputs: MethodEvidenceInputs<'_>,
    occurrence: &MethodEvidenceOccurrence,
    requirement: RequirementId,
    method: MethodId,
    constraint_work: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<usize, EvidenceValidationFailure> {
    let owner = occurrence.scope.ok_or_else(|| invalid_root(span))?;
    let candidate_count = match owner {
        MethodEvidenceOwner::Global(_) => {
            let mut count = 0usize;
            for _ in inputs.globals() {
                charge(constraint_work, 1, span)?;
                count = count.checked_add(1).ok_or_else(|| resource(span))?;
            }
            count
        }
        MethodEvidenceOwner::Implementation(_) => {
            inputs.implementation_method_count(constraint_work, span)?
        }
        MethodEvidenceOwner::ResourceFamily(_) => 0,
    };
    charge(constraint_work, candidate_count, span)?;
    let requirements = match owner {
        MethodEvidenceOwner::Global(binder) => inputs
            .globals()
            .find(|(id, _, _)| *id == binder)
            .map(|(_, scheme, _)| scheme.requirements.as_ref()),
        MethodEvidenceOwner::Implementation(implementation) => inputs
            .implementations()
            .flat_map(|implementation| implementation.methods.iter())
            .find(|candidate| candidate.id == implementation)
            .map(|method| method.scheme.requirements.as_ref()),
        MethodEvidenceOwner::ResourceFamily(_) => return Err(invalid_root(span)),
    }
    .ok_or_else(|| invalid_root(span))?;
    let requirement_position =
        usize::try_from(requirement.declaration()).map_err(|_| invalid_root(span))?;
    let requirements = requirements
        .get(..=requirement_position)
        .ok_or_else(|| invalid_root(span))?;
    charge(constraint_work, requirements.len(), span)?;
    let interface_count = inputs.interface_count(constraint_work, span)?;
    let interface_search_work = interface_count
        .checked_mul(requirements.len())
        .ok_or_else(|| resource(span))?;
    charge(
        constraint_work,
        interface_count
            .checked_add(interface_search_work)
            .ok_or_else(|| resource(span))?,
        span,
    )?;
    let mut position = 0usize;
    for (index, checked) in requirements.iter().enumerate() {
        if usize::try_from(checked.id.declaration()).ok() != Some(index) {
            return Err(invalid_root(span));
        }
        let interface = inputs
            .interfaces()
            .find(|interface| interface.id == checked.interface())
            .ok_or_else(|| invalid_root(span))?;
        if index == requirement_position {
            let method_position =
                usize::try_from(method.declaration()).map_err(|_| invalid_root(span))?;
            if checked.id != requirement
                || method.interface() != checked.interface()
                || interface
                    .methods
                    .get(method_position)
                    .is_none_or(|candidate| candidate.id != method)
            {
                return Err(invalid_root(span));
            }
            return position
                .checked_add(method_position)
                .ok_or_else(|| resource(span));
        }
        position = position
            .checked_add(interface.methods.len())
            .ok_or_else(|| resource(span))?;
    }
    Err(invalid_root(span))
}

fn collect_method_evidence_domains(
    methods: &[MethodEvidenceMethod],
    scheme: &ConstrainedScheme,
    owner: MethodEvidenceOwner,
    domains: &mut Vec<MethodEvidenceDomain>,
    constraint_work: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
    span: Span,
) -> Result<(), EvidenceValidationFailure> {
    for requirement in &scheme.requirements {
        charge(constraint_work, methods.len(), span)?;
        for method in methods.iter().filter(|method| {
            method.id.interface() == requirement.interface() && method_is_polymorphic(method)
        }) {
            charge(constraint_work, 1, span)?;
            domains.try_reserve(1).map_err(|_| resource(span))?;
            domains.push(MethodEvidenceDomain {
                source_parameters: crate::types::clone_kinded_type_parameters_with_budget(
                    &scheme.type_parameters,
                    type_work,
                )
                .map_err(|()| type_resource(span))?
                .into_boxed_slice(),
                owner,
                requirement: requirement.id,
                requirement_position: requirement.id.declaration(),
                method: method.id,
                method_position: method.id.declaration(),
                application: requirement
                    .application()
                    .clone_with_budget(type_work)
                    .map_err(|()| type_resource(span))?,
            });
        }
    }
    Ok(())
}

#[cfg(test)]
thread_local! {
    static LEXICAL_PLAN_INSPECTIONS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

fn selection_has_lexical(
    selection: &EvidenceSelection,
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<bool, EvidenceValidationFailure> {
    for index in 0..selection.node_count() {
        charge(budget, 1, span)?;
        #[cfg(test)]
        LEXICAL_PLAN_INSPECTIONS.with(|count| count.set(count.get() + 1));
        if matches!(
            selection.node(EvidenceNodeId::new(index)),
            Some(EvidenceNode::Lexical { .. })
        ) {
            return Ok(true);
        }
    }
    Ok(false)
}

fn staged_occurrence_failure(
    failure: crate::evidence::SelectionFailure,
    span: Span,
) -> EvidenceValidationFailure {
    match failure {
        crate::evidence::SelectionFailure::TypeResource => type_resource(span),
        crate::evidence::SelectionFailure::ConstraintResource => resource(span),
        _ => invalid_root(span),
    }
}

fn collect_staged_module_occurrences(
    module: &ModuleEvidenceInputs<'_>,
    methods: &[MethodEvidenceMethod],
    lexical_owners: &mut Vec<crate::core::dialect::MethodEvidenceLexicalOwner>,
    constraint_work: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
) -> Result<Vec<MethodEvidenceOccurrence>, EvidenceValidationFailure> {
    for retained in module.lexical_sources {
        let span = retained.span;
        let source = retained.slot.get().ok_or_else(|| invalid_root(span))?;
        if source.id.module() != module.module.module() {
            return Err(invalid_root(span));
        }
        charge(constraint_work, source.methods.len(), span)?;
        lexical_owners
            .try_reserve(source.methods.len())
            .map_err(|_| resource(span))?;
        for checked in &source.methods {
            charge(constraint_work, methods.len(), span)?;
            let canonical = methods
                .iter()
                .find(|method| method.id == checked.method)
                .ok_or_else(|| invalid_root(span))?;
            if checked.method.interface() != source.application.interface() {
                return Err(invalid_root(span));
            }
            let parameters: &[(TypeVariableId, Kind)] = if canonical.parameters.is_empty() {
                &[]
            } else if let Type::Forall(parameters, _) = &checked.scheme {
                if parameters.len() != canonical.parameters.len() {
                    return Err(invalid_root(span));
                }
                parameters
            } else {
                return Err(invalid_root(span));
            };
            charge(
                constraint_work,
                parameters
                    .len()
                    .checked_add(checked.captures.len())
                    .ok_or_else(|| resource(span))?,
                span,
            )?;
            let mut source_parameters = Vec::new();
            source_parameters
                .try_reserve_exact(parameters.len())
                .map_err(|_| resource(span))?;
            source_parameters.extend(parameters.iter().map(|(identity, _)| *identity));
            lexical_owners.push(crate::core::dialect::MethodEvidenceLexicalOwner {
                resource: source
                    .acquisition
                    .map(crate::core::dialect::MethodEvidenceResourceOwner::Builtin),
                source_parameters: source_parameters.into_boxed_slice(),
                source: source.id,
                method: checked.method,
                binder: checked.binder,
                application: source
                    .application
                    .clone_with_budget(type_work)
                    .map_err(|()| type_resource(span))?,
                captures: copy_catalog_slice(&checked.captures, type_work, span)?,
            });
        }
    }
    let mut occurrences = Vec::new();
    for use_ in module.method_uses {
        let span = use_.span;
        let staged = module
            .publication
            .occurrence(use_.slot.storage_id(), Some(use_.method), type_work)
            .map_err(|failure| staged_occurrence_failure(failure, span))?;
        charge(constraint_work, methods.len(), span)?;
        if !methods
            .iter()
            .any(|row| row.id == use_.method && method_is_polymorphic(row))
            && (lexical_owners.is_empty()
                || !selection_has_lexical(staged.selection, constraint_work, span)?)
        {
            continue;
        }
        let (scope, binder) = use_.scope.ok_or_else(|| invalid_root(span))?;
        retain_method_evidence_occurrence(
            &mut occurrences,
            use_.slot.storage_id(),
            Some(scope),
            Some(binder),
            None,
            None,
            Some(use_.method),
            staged.application,
            staged.method_arguments,
            Some(
                staged
                    .checked_value_type
                    .ok_or_else(|| invalid_root(span))?,
            ),
            staged.selection,
            constraint_work,
            type_work,
            span,
        )?;
    }
    for use_ in module.global_uses {
        let span = use_.span;
        let staged = module
            .publication
            .occurrence(use_.slot.storage_id(), None, type_work)
            .map_err(|failure| staged_occurrence_failure(failure, span))?;
        charge(constraint_work, methods.len(), span)?;
        if !interface_has_polymorphic_method(methods, staged.application.interface())
            && (lexical_owners.is_empty()
                || !selection_has_lexical(staged.selection, constraint_work, span)?)
        {
            continue;
        }
        let (scope, binder) = use_.scope.ok_or_else(|| invalid_root(span))?;
        retain_method_evidence_occurrence(
            &mut occurrences,
            use_.slot.storage_id(),
            Some(scope),
            Some(binder),
            Some(MethodEvidenceOwner::Global(use_.binder)),
            Some(use_.requirement),
            None,
            staged.application,
            &[],
            None,
            staged.selection,
            constraint_work,
            type_work,
            span,
        )?;
    }
    Ok(occurrences)
}

#[allow(clippy::too_many_arguments)]
fn retain_method_evidence_occurrence(
    occurrences: &mut Vec<MethodEvidenceOccurrence>,
    slot: usize,
    scope: Option<MethodEvidenceOwner>,
    scope_binder: Option<BinderId>,
    target_owner: Option<MethodEvidenceOwner>,
    target_requirement: Option<RequirementId>,
    checked_method: Option<MethodId>,
    checked_application: &InterfaceApplication,
    method_arguments: &[Type],
    checked_value_type: Option<&Type>,
    selection: &EvidenceSelection,
    constraint_work: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
    span: Span,
) -> Result<(), EvidenceValidationFailure> {
    charge(constraint_work, 2, span)?;
    occurrences.try_reserve(1).map_err(|_| resource(span))?;
    let mut retained_arguments = Vec::new();
    type_work
        .charge(method_arguments.len())
        .map_err(|()| type_resource(span))?;
    retained_arguments
        .try_reserve(method_arguments.len())
        .map_err(|_| type_resource(span))?;
    for argument in method_arguments {
        retained_arguments
            .push(clone_type_with_budget(argument, type_work).map_err(|()| type_resource(span))?);
    }
    occurrences.push(MethodEvidenceOccurrence {
        slot,
        scope,
        scope_binder,
        target_owner,
        target_requirement,
        checked_method,
        checked_application: checked_application
            .clone_with_budget(type_work)
            .map_err(|()| type_resource(span))?,
        method_arguments: retained_arguments.into_boxed_slice(),
        checked_value_type: checked_value_type
            .map(|ty| clone_type_with_budget(ty, type_work))
            .transpose()
            .map_err(|()| type_resource(span))?,
        selection: selection.clone(),
    });
    Ok(())
}

fn core_implementation_owner(
    application: &InterfaceApplication,
    method: &crate::resolved::CheckedImplementationMethodFact,
    type_work: &mut TypeWorkBudget,
) -> Result<MethodEvidenceImplementationOwner, EvidenceValidationFailure> {
    let mut source_parameters = Vec::new();
    type_work
        .charge(method.scheme.type_parameters.len())
        .map_err(|()| type_resource(method.span))?;
    source_parameters
        .try_reserve_exact(method.scheme.type_parameters.len())
        .map_err(|_| type_resource(method.span))?;
    for (parameter, kind) in &method.scheme.type_parameters {
        source_parameters.push((
            *parameter,
            clone_kind_with_budget(kind, type_work).map_err(|()| type_resource(method.span))?,
        ));
    }
    Ok(MethodEvidenceImplementationOwner {
        implementation: method.id,
        binder: method.binder,
        head_type_parameter_count: method.head_type_parameter_count(),
        source_parameters: source_parameters.into_boxed_slice(),
        application: application
            .clone_with_budget(type_work)
            .map_err(|()| type_resource(method.span))?,
    })
}

fn lexical_header_captures_method_parameter(
    owners: &[crate::core::dialect::MethodEvidenceLexicalOwner],
    method: &crate::resolved::CheckedImplementationMethodFact,
    budget: &mut InterfaceConstraintBudget,
) -> Result<bool, EvidenceValidationFailure> {
    if method.scheme.type_parameters.is_empty() {
        return Ok(false);
    }
    for owner in owners {
        charge(budget, 1, method.span)?;
        for argument in owner.application.arguments() {
            let mut variables = Vec::new();
            collect_argument_constraint_variables(argument, &mut variables, budget, method.span)?;
            charge(
                budget,
                method
                    .scheme
                    .type_parameters
                    .len()
                    .checked_mul(variables.len())
                    .ok_or_else(|| resource(method.span))?,
                method.span,
            )?;
            if method
                .scheme
                .type_parameters
                .iter()
                .any(|(parameter, _)| variables.contains(parameter))
            {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

fn local_representation_captures_method_parameter(
    registry: &ResolvedRegistry,
    method: &crate::resolved::CheckedImplementationMethodFact,
    budget: &mut InterfaceConstraintBudget,
) -> Result<bool, EvidenceValidationFailure> {
    if method.scheme.type_parameters.is_empty() {
        return Ok(false);
    }
    for nominal in registry.lexical_nominals() {
        charge(budget, 1, method.span)?;
        let span = nominal.origin.primary_span();
        if span.source() != method.span.source()
            || span.range().start() < method.span.range().start()
            || span.range().end() > method.span.range().end()
        {
            continue;
        }
        let representation = nominal
            .representation
            .as_ref()
            .ok_or_else(|| unknown(span))?;
        let mut variables = Vec::new();
        collect_linked_constraint_variables(representation, &mut variables, budget, span)?;
        charge(
            budget,
            method
                .scheme
                .type_parameters
                .len()
                .checked_mul(variables.len())
                .ok_or_else(|| resource(span))?,
            span,
        )?;
        if method
            .scheme
            .type_parameters
            .iter()
            .any(|(parameter, _)| variables.contains(parameter))
        {
            return Ok(true);
        }
    }
    Ok(false)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum LinkedBinderOwner {
    Region(BinderId),
    Store(BinderId),
    Network(BinderId),
    Method(MethodId),
}

fn retain_checked_scoped_owners(
    program: &ResolvedModuleProgram,
    registry: &LinkedInterfaceRegistry,
    budget: &mut InterfaceConstraintBudget,
) -> Result<(), EvidenceValidationFailure> {
    use crate::elaborate::CheckedScopedOwnerKind;

    for group in program.groups() {
        let fragment = group
            .typed_fragment()
            .ok_or_else(|| invalid_root(group.span()))?;
        let (_, _, _, owners) = fragment.evidence_inventory();
        charge(budget, owners.len(), group.span())?;
        let mut retained = registry.scoped_type_owners.borrow_mut();
        retained
            .try_reserve(owners.len())
            .map_err(|_| resource(group.span()))?;
        for owner in owners {
            if owner.identity.module() != Some(group.module())
                || owner.handle.module() != Some(group.module())
            {
                return Err(invalid_root(owner.span));
            }
            let kind = match owner.kind {
                CheckedScopedOwnerKind::Region => LinkedBinderOwner::Region(owner.handle),
                CheckedScopedOwnerKind::Network => LinkedBinderOwner::Network(owner.handle),
                CheckedScopedOwnerKind::Store => LinkedBinderOwner::Store(owner.handle),
            };
            match retained.entry(owner.identity) {
                std::collections::hash_map::Entry::Vacant(slot) => {
                    slot.insert((kind, owner.span));
                }
                std::collections::hash_map::Entry::Occupied(slot)
                    if *slot.get() == (kind, owner.span) => {}
                _ => return Err(invalid_root(owner.span)),
            }
        }
    }
    Ok(())
}

fn validate_linked_entry<'a>(
    program: &'a ResolvedModuleProgram,
    registry: &LinkedInterfaceRegistry,
    kind_environments: &mut KindEnvironments<'a>,
    budget: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
) -> Result<(), EvidenceValidationFailure> {
    let entry = registry
        .modules
        .get(&program.entry())
        .and_then(|index| program.groups().get(*index))
        .ok_or_else(|| unknown(program.result().span))?;
    validate_expression(
        program,
        registry,
        entry,
        EvidenceScope::NONE,
        program.result(),
        kind_environments,
        budget,
        type_work,
        false,
    )
}

#[allow(clippy::too_many_arguments)]
fn validate_expression<'a>(
    program: &'a ResolvedModuleProgram,
    registry: &LinkedInterfaceRegistry,
    group: &ResolvedModuleGroup,
    scope: EvidenceScope<'_>,
    root: &ResolvedExpr,
    kind_environments: &mut KindEnvironments<'a>,
    budget: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
    headers_only: bool,
) -> Result<(), EvidenceValidationFailure> {
    let mut pending = Vec::new();
    reserve_expressions(&mut pending, 1, budget, root.span)?;
    pending.push(root);
    validate_pending_expressions(
        program,
        registry,
        group,
        scope,
        &mut pending,
        None,
        kind_environments,
        budget,
        type_work,
        headers_only,
    )
}

#[allow(clippy::too_many_arguments)]
fn validate_pending_expressions<'a, 'body>(
    program: &'a ResolvedModuleProgram,
    registry: &LinkedInterfaceRegistry,
    group: &ResolvedModuleGroup,
    scope: EvidenceScope<'_>,
    pending: &mut Vec<&'body ResolvedExpr>,
    initial_block: Option<&'body ResolvedBlock>,
    kind_environments: &mut KindEnvironments<'a>,
    budget: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
    headers_only: bool,
) -> Result<(), EvidenceValidationFailure> {
    let mut sources = Vec::new();
    let mut method_scopes = Vec::new();
    let mut heads = Vec::new();
    let mut variables = Vec::new();
    let mut active_method_scope = None;
    let track_provider_equations = false;
    if let Some(block) = initial_block {
        schedule_lexical_block(
            pending,
            &mut heads,
            &mut sources,
            &mut method_scopes,
            (None, None),
            block,
            budget,
            track_provider_equations,
            OriginalLexicalContext {
                owner: scope.owner,
                local_head: None,
            },
            Some((
                program,
                registry,
                scope.variables,
                scope.owner,
                type_work,
                headers_only,
            )),
        )?;
    }
    while let Some(expression) = pending.pop() {
        let head = if sources.is_empty() && method_scopes.is_empty() {
            (None, None)
        } else {
            heads.pop().ok_or_else(|| invalid_root(expression.span))?
        };
        if head.1 != active_method_scope {
            variables.clear();
            let mut method_head = head.1;
            while let Some(index) = method_head {
                let (local, parent) = method_scopes
                    .get(index)
                    .ok_or_else(|| invalid_root(expression.span))?;
                charge(budget, usize::from(headers_only), expression.span)?;
                if let Some(identity) = match local {
                    LinkedLocalScope::Resource(resource) => Some(resource.identity.id),
                    LinkedLocalScope::Store(store) => Some(store.identity.id),
                    LinkedLocalScope::Network(network) => Some(network.identity.id),
                    LinkedLocalScope::Region(region) => Some(region.identity.id),

                    _ => None,
                } {
                    charge(budget, 1, expression.span)?;
                    variables
                        .try_reserve(1)
                        .map_err(|_| resource(expression.span))?;
                    variables.push(identity);
                }
                if let LinkedLocalScope::Method(method) = local {
                    charge(budget, method.contextual_parameters.len(), expression.span)?;
                    variables
                        .try_reserve(method.contextual_parameters.len())
                        .map_err(|_| resource(expression.span))?;
                    variables.extend(
                        method
                            .contextual_parameters
                            .iter()
                            .map(|parameter| parameter.id),
                    );
                }
                method_head = *parent;
            }
            if head.1.is_some() {
                charge(budget, scope.variables.len(), expression.span)?;
                variables
                    .try_reserve(scope.variables.len())
                    .map_err(|_| resource(expression.span))?;
                variables.extend_from_slice(scope.variables);
            }
            active_method_scope = head.1;
        }
        let active_variables = if head.1.is_some() {
            &variables
        } else {
            scope.variables
        };
        let scope = EvidenceScope {
            local_scopes: &method_scopes,
            lexical_sources: &sources,
            lexical_head: head.0,
            variables: active_variables,
            ..scope
        };
        charge(budget, 1, expression.span)?;
        match &expression.kind {
            ResolvedExprKind::Occurrence(occurrence) => {
                if !headers_only {
                    validate_occurrence(
                        program,
                        registry,
                        group,
                        scope,
                        occurrence,
                        kind_environments,
                        budget,
                        type_work,
                    )?;
                }
            }
            ResolvedExprKind::String(_)
            | ResolvedExprKind::Integer(_)
            | ResolvedExprKind::Boolean(_)
            | ResolvedExprKind::Unit
            | ResolvedExprKind::Constructor(_) => {}
            ResolvedExprKind::Tuple(elements) => {
                reserve_expressions(pending, elements.len(), budget, expression.span)?;
                pending.extend(elements.iter().rev());
            }
            ResolvedExprKind::Apply(application) => {
                reserve_expressions(pending, 2, budget, expression.span)?;
                pending.push(application.argument.as_ref());
                pending.push(application.function.as_ref());
            }
            ResolvedExprKind::Add(binary)
            | ResolvedExprKind::Multiply(binary)
            | ResolvedExprKind::Equal(binary) => {
                reserve_expressions(pending, 2, budget, expression.span)?;
                pending.push(binary.right.as_ref());
                pending.push(binary.left.as_ref());
            }
            ResolvedExprKind::Block(block) => {
                let original = OriginalLexicalContext {
                    owner: scope.owner,
                    local_head: head.1,
                };
                let header_scope = Some((
                    program,
                    registry,
                    active_variables,
                    original.owner,
                    &mut *type_work,
                    headers_only,
                ));
                schedule_lexical_block(
                    pending,
                    &mut heads,
                    &mut sources,
                    &mut method_scopes,
                    head,
                    block,
                    budget,
                    track_provider_equations,
                    original,
                    header_scope,
                )?;
            }
            ResolvedExprKind::Function(function) => {
                let original = OriginalLexicalContext {
                    owner: scope.owner,
                    local_head: head.1,
                };
                let header_scope = Some((
                    program,
                    registry,
                    active_variables,
                    original.owner,
                    &mut *type_work,
                    headers_only,
                ));
                schedule_lexical_block(
                    pending,
                    &mut heads,
                    &mut sources,
                    &mut method_scopes,
                    head,
                    &function.body,
                    budget,
                    track_provider_equations,
                    original,
                    header_scope,
                )?;
            }
            ResolvedExprKind::Match(matched) => {
                let additional = matched
                    .arms
                    .len()
                    .checked_add(1)
                    .ok_or_else(|| resource(expression.span))?;
                reserve_expressions(pending, additional, budget, expression.span)?;
                pending.extend(matched.arms.iter().rev().map(|arm| &arm.body));
                pending.push(matched.scrutinee.as_ref());
            }
            ResolvedExprKind::Region(region) => {
                let canonical = program
                    .registry()
                    .type_variable(region.identity.id)
                    .ok_or_else(|| invalid_root(expression.span))?;
                charge(
                    budget,
                    canonical.spelling.len().saturating_add(3),
                    expression.span,
                )?;
                if canonical.kind != Kind::Type
                    || canonical.spelling != region.identity.spelling
                    || canonical.origin.primary_span() != region.identity.origin.primary_span()
                    || region.identity.kind != Kind::Type
                    || region.identity.id.module() != region.handle.id.module()
                    || expression.span.cover(region.identity.origin.primary_span())
                        != Some(expression.span)
                    || expression.span.cover(region.handle.origin.primary_span())
                        != Some(expression.span)
                {
                    return Err(invalid_root(expression.span));
                }
                let mut owners = registry.scoped_type_owners.borrow_mut();
                owners
                    .try_reserve(1)
                    .map_err(|_| resource(expression.span))?;
                match owners.entry(region.identity.id) {
                    std::collections::hash_map::Entry::Vacant(slot) => {
                        slot.insert((LinkedBinderOwner::Region(region.handle.id), expression.span));
                    }
                    std::collections::hash_map::Entry::Occupied(slot)
                        if *slot.get()
                            == (LinkedBinderOwner::Region(region.handle.id), expression.span) => {}
                    _ => return Err(invalid_root(expression.span)),
                }
                drop(owners);
                reserve_expressions(pending, 2, budget, expression.span)?;
                resize_lexical_heads(&mut heads, pending.len(), head, budget, expression.span)?;
                method_scopes
                    .try_reserve(1)
                    .map_err(|_| resource(expression.span))?;
                let region_scope = Some(method_scopes.len());
                method_scopes.push((LinkedLocalScope::Region(region), head.1));
                pending.push(&region.body);
                if let Some(provider) = &region.provider {
                    pending.push(provider);
                }
                resize_lexical_heads(
                    &mut heads,
                    pending.len(),
                    (head.0, region_scope),
                    budget,
                    expression.span,
                )?;
            }
            ResolvedExprKind::RegionSelection(selection) => {
                reserve_expressions(pending, 2, budget, expression.span)?;
                pending.push(&selection.body);
                pending.push(&selection.region);
            }
            ResolvedExprKind::Resource(acquisition) => {
                let canonical = program
                    .registry()
                    .type_variable(acquisition.identity.id)
                    .ok_or_else(|| invalid_root(expression.span))?;
                charge(
                    budget,
                    canonical.spelling.len().saturating_add(2),
                    expression.span,
                )?;
                if !acquisition
                    .acquisition
                    .owns(acquisition, type_work)
                    .map_err(|()| resource(expression.span))?
                    || canonical.kind != Kind::Type
                    || canonical.spelling != acquisition.identity.spelling
                    || canonical.origin.primary_span() != acquisition.identity.origin.primary_span()
                    || acquisition.acquisition.span != expression.span
                {
                    return Err(invalid_root(expression.span));
                }
                reserve_expressions(pending, 2, budget, expression.span)?;
                resize_lexical_heads(&mut heads, pending.len(), head, budget, expression.span)?;
                charge(budget, 1, expression.span)?;
                method_scopes
                    .try_reserve(1)
                    .map_err(|_| resource(expression.span))?;
                let body_scope = Some(method_scopes.len());
                method_scopes.push((LinkedLocalScope::Resource(acquisition), head.1));
                pending.push(&acquisition.body);
                resize_lexical_heads(
                    &mut heads,
                    pending.len(),
                    (head.0, body_scope),
                    budget,
                    expression.span,
                )?;
                pending.push(&acquisition.initializer);
                resize_lexical_heads(&mut heads, pending.len(), head, budget, expression.span)?;
            }
            ResolvedExprKind::Network(network) => {
                let canonical = program
                    .registry()
                    .type_variable(network.identity.id)
                    .ok_or_else(|| invalid_root(expression.span))?;
                charge(
                    budget,
                    canonical.spelling.len().saturating_add(2),
                    expression.span,
                )?;
                if !network.acquisition.owns(network)
                    || canonical.kind != Kind::Type
                    || canonical.spelling != network.identity.spelling
                    || canonical.origin.primary_span() != network.identity.origin.primary_span()
                    || network.acquisition.span != expression.span
                {
                    return Err(invalid_root(expression.span));
                }
                let mut owners = registry.scoped_type_owners.borrow_mut();
                owners
                    .try_reserve(1)
                    .map_err(|_| resource(expression.span))?;
                match owners.entry(network.identity.id) {
                    std::collections::hash_map::Entry::Vacant(slot) => {
                        slot.insert((
                            LinkedBinderOwner::Network(network.handle.id),
                            expression.span,
                        ));
                    }
                    std::collections::hash_map::Entry::Occupied(slot)
                        if *slot.get()
                            == (
                                LinkedBinderOwner::Network(network.handle.id),
                                expression.span,
                            ) => {}
                    _ => return Err(invalid_root(expression.span)),
                }
                drop(owners);
                reserve_expressions(pending, 2, budget, expression.span)?;
                resize_lexical_heads(&mut heads, pending.len(), head, budget, expression.span)?;
                charge(budget, 1, expression.span)?;
                method_scopes
                    .try_reserve(1)
                    .map_err(|_| resource(expression.span))?;
                let body_scope = Some(method_scopes.len());
                method_scopes.push((LinkedLocalScope::Network(network), head.1));
                pending.push(&network.body);
                resize_lexical_heads(
                    &mut heads,
                    pending.len(),
                    (head.0, body_scope),
                    budget,
                    expression.span,
                )?;
                pending.push(&network.initializer);
                resize_lexical_heads(&mut heads, pending.len(), head, budget, expression.span)?;
            }
            ResolvedExprKind::Store(store) => {
                let canonical = program
                    .registry()
                    .type_variable(store.identity.id)
                    .ok_or_else(|| invalid_root(expression.span))?;
                charge(
                    budget,
                    canonical.spelling.len().saturating_add(2),
                    expression.span,
                )?;
                if !store.acquisition.owns(store)
                    || canonical.kind != Kind::Type
                    || canonical.spelling != store.identity.spelling
                    || canonical.origin.primary_span() != store.identity.origin.primary_span()
                    || store.acquisition.span != expression.span
                {
                    return Err(invalid_root(expression.span));
                }
                let mut owners = registry.scoped_type_owners.borrow_mut();
                owners
                    .try_reserve(1)
                    .map_err(|_| resource(expression.span))?;
                match owners.entry(store.identity.id) {
                    std::collections::hash_map::Entry::Vacant(slot) => {
                        slot.insert((LinkedBinderOwner::Store(store.handle.id), expression.span));
                    }
                    std::collections::hash_map::Entry::Occupied(slot)
                        if *slot.get()
                            == (LinkedBinderOwner::Store(store.handle.id), expression.span) => {}
                    _ => return Err(invalid_root(expression.span)),
                }
                drop(owners);
                reserve_expressions(pending, 2, budget, expression.span)?;
                resize_lexical_heads(&mut heads, pending.len(), head, budget, expression.span)?;
                charge(budget, 1, expression.span)?;
                method_scopes
                    .try_reserve(1)
                    .map_err(|_| resource(expression.span))?;
                let body_scope = Some(method_scopes.len());
                method_scopes.push((LinkedLocalScope::Store(store), head.1));
                pending.push(&store.body);
                resize_lexical_heads(
                    &mut heads,
                    pending.len(),
                    (head.0, body_scope),
                    budget,
                    expression.span,
                )?;
                pending.push(&store.initializer);
                resize_lexical_heads(&mut heads, pending.len(), head, budget, expression.span)?;
            }
            ResolvedExprKind::Cleanup(cleanup) => {
                reserve_expressions(pending, 2, budget, expression.span)?;
                resize_lexical_heads(&mut heads, pending.len(), head, budget, expression.span)?;
                pending.push(&cleanup.body);
                pending.push(&cleanup.action);
            }
            ResolvedExprKind::Perform(request) => pending.push(request.operand.as_ref()),
            ResolvedExprKind::Handle(handler) => {
                let additional = handler
                    .clauses
                    .len()
                    .saturating_add(1 + usize::from(handler.store.is_some()));
                reserve_expressions(pending, additional, budget, expression.span)?;
                pending.extend(handler.clauses.iter().rev().map(|clause| &clause.body));
                pending.push(handler.body.as_ref());
                if let Some(store) = &handler.store {
                    pending.push(store);
                }
            }
            ResolvedExprKind::Resume(resume) => pending.push(resume.value.as_ref()),
            ResolvedExprKind::Discard(_) | ResolvedExprKind::Retain(_) => {}
        }
        if !sources.is_empty() || !method_scopes.is_empty() {
            resize_lexical_heads(&mut heads, pending.len(), head, budget, expression.span)?;
        }
    }
    Ok(())
}

/// Authenticates one already-canonical method relation without searching or
/// reselecting. Linked registry construction has established that a MethodId's
/// declaration ordinal is the exact position in every method relation.
fn method_relation_slot_matches<T: PartialEq>(
    methods: &[T],
    method: MethodId,
    expected: &T,
) -> bool {
    usize::try_from(method.declaration())
        .ok()
        .and_then(|index| methods.get(index))
        == Some(expected)
}

#[allow(clippy::too_many_arguments)]
fn validate_occurrence<'a>(
    program: &'a ResolvedModuleProgram,
    registry: &LinkedInterfaceRegistry,
    group: &ResolvedModuleGroup,
    scope: EvidenceScope<'_>,
    occurrence: &ResolvedOccurrence,
    kind_environments: &mut KindEnvironments<'a>,
    budget: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
) -> Result<(), EvidenceValidationFailure> {
    let span = occurrence.origin.primary_span();
    charge(budget, 1, span)?;
    match occurrence.term {
        ResolvedTermName::Global(binder) => {
            let requirements = registry
                .scheme(program, binder)
                .map_or(&[][..], |scheme| scheme.requirements.as_ref());
            charge(budget, requirements.len(), span)?;
            if occurrence.evidence.len() != requirements.len() {
                return Err(invalid_root(span));
            }
            for (slot, _requirement) in occurrence.evidence.iter().zip(requirements) {
                let (checked_application, selection) =
                    slot.filled().ok_or_else(|| invalid_root(span))?;
                validate_checked_selection_in_scope(
                    program,
                    registry,
                    group,
                    selection,
                    checked_application,
                    scope,
                    kind_environments,
                    budget,
                    type_work,
                    span,
                )?;
            }
        }
        ResolvedTermName::Method(method) => {
            let occurrence_method = method;
            let method = registry
                .method(program, method)
                .ok_or_else(|| unknown(span))?;
            let [slot] = occurrence.evidence.as_ref() else {
                return Err(invalid_root(span));
            };
            let (
                checked_method,
                checked_application,
                method_arguments,
                checked_value_type,
                selection,
            ) = slot.filled_method().ok_or_else(|| invalid_root(span))?;
            if checked_method != occurrence_method {
                return Err(invalid_root(span));
            }
            validate_checked_selection_in_scope(
                program,
                registry,
                group,
                selection,
                checked_application,
                scope,
                kind_environments,
                budget,
                type_work,
                span,
            )?;
            let authentic_method_relation = match selection.node(selection.root()) {
                Some(
                    EvidenceNode::Abstract { methods, .. } | EvidenceNode::Lexical { methods, .. },
                ) => method_relation_slot_matches(methods, checked_method, &checked_method),
                Some(EvidenceNode::Implementation {
                    implementation,
                    methods,
                    ..
                }) => method_relation_slot_matches(
                    methods,
                    checked_method,
                    &ImplMethodId::new(implementation, checked_method),
                ),
                None => false,
            };
            if !authentic_method_relation {
                return Err(invalid_root(span));
            }
            if method_arguments.len() != method.authoritative_type_parameters().len() {
                return Err(invalid_root(span));
            }
            kind_environments
                .install_canonical_owner_ids(program.registry(), scope.variables, type_work, span)
                .map_err(|failure| map_selected_kind_type_failure(failure, span))?;
            for (parameter, argument) in method
                .authoritative_type_parameters()
                .iter()
                .zip(method_arguments)
            {
                validate_linked_type_with_policy(
                    argument,
                    program.registry(),
                    scope.variables,
                    budget,
                    span,
                )
                .map_err(|failure| {
                    if failure.reason() == EvidenceValidationReason::ConstraintResourceExhausted {
                        failure
                    } else {
                        invalid_root(span)
                    }
                })?;
                let expected =
                    canonical_type_variable_kind(program.registry(), parameter.id, span, budget)
                        .map_err(|failure| map_selected_kind_constraint_failure(failure, span))?;
                kind_environments
                    .expect_body_free_exact_kind_with_ledger(argument, expected, span, budget)
                    .map_err(|failure| map_selected_kind_constraint_failure(failure, span))?;
            }
            validate_linked_type_with_policy(
                checked_value_type,
                program.registry(),
                scope.variables,
                budget,
                span,
            )
            .map_err(|failure| {
                if failure.reason() == EvidenceValidationReason::ConstraintResourceExhausted {
                    failure
                } else {
                    invalid_root(span)
                }
            })?;
            kind_environments
                .expect_body_free_value_type_with_ledger(checked_value_type, span, budget)
                .map_err(|failure| map_selected_kind_constraint_failure(failure, span))?;
            if !same_type_after_method_instantiation(
                method.value_type(),
                &registry
                    .interface(program, method.id.interface())
                    .ok_or_else(|| unknown(span))?
                    .parameters,
                checked_application.arguments(),
                method.authoritative_type_parameters(),
                method_arguments,
                checked_value_type,
                budget,
                span,
            )? {
                return Err(invalid_root(span));
            }
        }
    }
    Ok(())
}

#[derive(Clone, Copy)]
struct EvidenceScope<'a> {
    local_scopes: &'a [(LinkedLocalScope<'a>, Option<usize>)],
    owner: Option<RequirementOwner>,
    variables: &'a [TypeVariableId],
    lexical_sources: &'a [(LinkedLexicalSource<'a>, Option<usize>)],
    lexical_head: Option<usize>,
}

impl EvidenceScope<'static> {
    const NONE: Self = Self {
        local_scopes: &[],
        owner: None,
        variables: &[],
        lexical_sources: &[],
        lexical_head: None,
    };
}

#[cfg(test)]
fn validate_selection(
    program: &ResolvedModuleProgram,
    registry: &LinkedInterfaceRegistry,
    group: &ResolvedModuleGroup,
    selection: &EvidenceSelection,
    expected_interface: InterfaceId,
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<(), EvidenceValidationFailure> {
    let expected_application = InterfaceApplication::new_kinded(
        expected_interface,
        selection.arguments().to_vec().into_boxed_slice(),
    );
    validate_selection_in_scope(
        program,
        registry,
        group,
        selection,
        &expected_application,
        EvidenceScope::NONE,
        budget,
        span,
    )
}

#[cfg(test)]
#[allow(clippy::too_many_arguments)]
fn validate_selection_in_scope(
    program: &ResolvedModuleProgram,
    registry: &LinkedInterfaceRegistry,
    group: &ResolvedModuleGroup,
    selection: &EvidenceSelection,
    expected_application: &InterfaceApplication,
    scope: EvidenceScope<'_>,
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<(), EvidenceValidationFailure> {
    let mut type_work = TypeWorkBudget::default();
    let mut kind_environments =
        build_linked_kind_environments(program.registry(), &mut type_work, span)?;
    for linked_group in program.groups() {
        for interface in linked_group.interface_facts() {
            kind_environments
                .insert_interface(
                    interface.id,
                    &interface.parameters,
                    interface.span,
                    &mut type_work,
                )
                .map_err(|failure| map_kind_type_failure(failure, span))?;
        }
    }
    if selection.interface() != expected_application.interface() {
        return Err(invalid_root(span));
    }
    validate_checked_selection_in_scope(
        program,
        registry,
        group,
        selection,
        expected_application,
        scope,
        &mut kind_environments,
        budget,
        &mut type_work,
        span,
    )
}

#[allow(clippy::too_many_arguments)]
fn validate_checked_selection_in_scope<'a>(
    program: &'a ResolvedModuleProgram,
    registry: &LinkedInterfaceRegistry,
    group: &ResolvedModuleGroup,
    selection: &EvidenceSelection,
    expected_application: &InterfaceApplication,
    scope: EvidenceScope<'_>,
    kind_environments: &mut KindEnvironments<'a>,
    budget: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
    span: Span,
) -> Result<(), EvidenceValidationFailure> {
    charge(budget, 2, span)?;
    for argument in expected_application.arguments() {
        validate_argument_with_policy(argument, program.registry(), scope.variables, budget, span)?;
    }
    if selection.interface() != expected_application.interface()
        || registry.interface(program, selection.interface()).is_none()
        || selection.node(selection.root()).is_none()
    {
        return Err(invalid_root(span));
    }
    if selection.arguments().len() != expected_application.arguments().len() {
        return Err(invalid_root(span));
    }
    for (selected, expected) in selection
        .arguments()
        .iter()
        .zip(expected_application.arguments())
    {
        if !same_argument_charged(selected, expected, budget, span)? {
            return Err(invalid_root(span));
        }
    }
    kind_environments
        .install_canonical_owner_ids(program.registry(), scope.variables, type_work, span)
        .map_err(|failure| map_selected_kind_type_failure(failure, span))?;
    authenticate_selected_goal_kind(expected_application, kind_environments, budget, span)?;
    charge(budget, selection.node_count(), span)?;
    let mut visited = HashSet::new();
    visited
        .try_reserve(selection.node_count())
        .map_err(|_| resource(span))?;
    let mut pending = PendingGoals::default();
    validate_evidence_node(
        program,
        registry,
        group,
        selection,
        selection.root(),
        expected_application,
        None,
        scope,
        kind_environments,
        &mut visited,
        &mut pending,
        budget,
        type_work,
        span,
    )?;
    while let Some(goal) = pending.pop() {
        authenticate_pending_goal_kind_from_prerequisite(budget, span)?;
        validate_evidence_node(
            program,
            registry,
            group,
            selection,
            goal.node,
            goal.application(),
            goal.mandated_requirement,
            scope,
            kind_environments,
            &mut visited,
            &mut pending,
            budget,
            type_work,
            span,
        )?;
    }
    if visited.len() == selection.node_count() {
        Ok(())
    } else {
        Err(invalid_root(span))
    }
}

#[allow(clippy::too_many_arguments)]
fn validate_evidence_node(
    program: &ResolvedModuleProgram,
    registry: &LinkedInterfaceRegistry,
    group: &ResolvedModuleGroup,
    selection: &EvidenceSelection,
    node: EvidenceNodeId,
    expected_application: &InterfaceApplication,
    mandated_requirement: Option<RequirementId>,
    scope: EvidenceScope<'_>,
    kind_environments: &KindEnvironments<'_>,
    visited: &mut HashSet<EvidenceNodeId>,
    pending: &mut PendingGoals,
    budget: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
    span: Span,
) -> Result<(), EvidenceValidationFailure> {
    charge(budget, 1, span)?;
    if !visited.insert(node) {
        return Err(invalid_root(span));
    }
    let interface = registry
        .interface(program, expected_application.interface())
        .ok_or_else(|| unknown(span))?;
    match selection.node(node).ok_or_else(|| invalid_root(span))? {
        EvidenceNode::Lexical { source, methods } => {
            if mandated_requirement.is_some() {
                return Err(invalid_root(span));
            }
            if first_identity_equal_abstract_requirement(
                program,
                registry,
                scope,
                expected_application,
                budget,
                span,
            )?
            .is_some()
            {
                return Err(invalid_root(span));
            }
            if let Some(RequirementOwner::Impl(current)) = scope.owner {
                charge(budget, 1, span)?;
                let current = registry
                    .implementation(program, current)
                    .ok_or_else(|| unknown(span))?;
                if same_application_parts_charged(
                    current.application(),
                    expected_application.interface(),
                    expected_application.arguments(),
                    budget,
                    span,
                )? {
                    return Err(invalid_root(span));
                }
            }
            let mut head = scope.lexical_head;
            let mut found = None;
            while let Some(index) = head {
                charge(budget, 1, span)?;
                let (candidate, parent) = scope
                    .lexical_sources
                    .get(index)
                    .ok_or_else(|| invalid_root(span))?;
                if candidate.id() == source {
                    found = Some(*candidate);
                    break;
                }
                head = *parent;
            }
            let source = found.ok_or_else(|| invalid_root(span))?;

            let LinkedLexicalSource::Declared(source, _) = source;
            charge(budget, methods.len(), span)?;
            if source.id.module() != group.module()
                || source.application.interface.id != expected_application.interface()
                || source.application.arguments.len() != expected_application.arguments().len()
                || !methods
                    .iter()
                    .copied()
                    .eq(interface.methods.iter().map(|method| method.id))
            {
                return Err(invalid_root(span));
            }
            if !found.ok_or_else(|| invalid_root(span))?.same_application(
                program,
                registry,
                expected_application,
                scope,
                budget,
                type_work,
                span,
            )? {
                return Err(invalid_root(span));
            }
            let mut supplied = HashSet::new();
            for method in &source.method_groups {
                let work = methods
                    .len()
                    .checked_add(1)
                    .and_then(|work| work.checked_add(method.equations.len()))
                    .ok_or_else(|| resource(span))?;
                charge(budget, work, span)?;
                supplied.try_reserve(1).map_err(|_| resource(span))?;
                let id = method.method.ok_or_else(|| invalid_root(span))?;
                if method.identity.is_some()
                    || !methods.contains(&id)
                    || !supplied.insert(id)
                    || method.binder.id.module() != Some(source.id.module())
                    || method
                        .equations
                        .iter()
                        .any(|equation| equation.name.binder != method.binder.id)
                {
                    return Err(invalid_root(span));
                }
            }
            if supplied.len() != methods.len() {
                return Err(invalid_root(span));
            }
        }
        EvidenceNode::Abstract {
            requirement,
            methods,
        } => {
            charge(budget, methods.len().saturating_add(1), span)?;
            if matches!(requirement.owner(), RequirementOwner::ResourceFamily(_)) {
                return Err(unknown(span));
            }
            let checked = registry
                .requirement(program, requirement)
                .ok_or_else(|| unknown(span))?;
            if scope.owner != Some(requirement.owner())
                || !same_application_parts_charged(
                    checked.application(),
                    expected_application.interface(),
                    expected_application.arguments(),
                    budget,
                    span,
                )?
                || !methods
                    .iter()
                    .copied()
                    .eq(interface.methods.iter().map(|method| method.id))
            {
                return Err(invalid_root(span));
            }
            if let Some(mandated) = mandated_requirement {
                if requirement != mandated {
                    return Err(invalid_root(span));
                }
            } else if first_identity_equal_abstract_requirement(
                program,
                registry,
                scope,
                expected_application,
                budget,
                span,
            )? != Some(requirement)
            {
                return Err(invalid_root(span));
            }
        }
        EvidenceNode::Implementation {
            implementation,
            substitution,
            prerequisites,
            methods,
        } => {
            if mandated_requirement.is_some() {
                return Err(invalid_root(span));
            }
            if first_identity_equal_abstract_requirement(
                program,
                registry,
                scope,
                expected_application,
                budget,
                span,
            )?
            .is_some()
            {
                return Err(invalid_root(span));
            }
            let current = match scope.owner {
                Some(RequirementOwner::Impl(current)) => {
                    charge(budget, 1, span)?;
                    Some(
                        registry
                            .implementation(program, current)
                            .ok_or_else(|| unknown(span))?,
                    )
                }
                Some(RequirementOwner::Global(_) | RequirementOwner::ResourceFamily(_)) | None => {
                    None
                }
            };
            let exact_current = match current {
                Some(current) if current.interface() == expected_application.interface() => {
                    same_application_parts_charged(
                        current.application(),
                        expected_application.interface(),
                        expected_application.arguments(),
                        budget,
                        span,
                    )?
                }
                Some(_) | None => false,
            };
            if exact_current {
                if current.is_none_or(|current| current.id != implementation) {
                    return Err(invalid_root(span));
                }
            } else if current.is_some_and(|current| current.id == implementation) {
                return Err(invalid_root(span));
            }
            if !exact_current
                && identity_equal_lexical_source(
                    program,
                    registry,
                    scope,
                    expected_application,
                    budget,
                    type_work,
                    span,
                )?
                .is_some()
            {
                return Err(invalid_root(span));
            }
            let fact = registry
                .implementation(program, implementation)
                .ok_or_else(|| unknown(span))?;
            charge(
                budget,
                substitution
                    .len()
                    .saturating_add(prerequisites.len())
                    .saturating_add(methods.len())
                    .saturating_add(1),
                span,
            )?;
            if fact.interface() != expected_application.interface() {
                return Err(invalid_root(span));
            }
            if !implementation_is_available(program, registry, group, implementation, budget, span)?
            {
                return Err(unavailable(span));
            }
            if methods.len() != fact.methods.len()
                || !methods
                    .iter()
                    .copied()
                    .eq(fact.methods.iter().map(|method| method.id))
                || methods
                    .iter()
                    .any(|method| registry.implementation_method(program, *method).is_none())
                || prerequisites.len() != fact.prerequisites.len()
            {
                return Err(invalid_root(span));
            }
            authenticate_selected_substitution_kinds(
                fact,
                substitution,
                program.registry(),
                kind_environments,
                budget,
                span,
            )?;
            if exact_current {
                if !current_identity_substitution_matches(
                    fact,
                    substitution,
                    scope.variables,
                    program.registry(),
                    budget,
                    span,
                )? {
                    return Err(invalid_root(span));
                }
            } else if !implementation_head_matches(
                fact,
                substitution,
                expected_application,
                program.registry(),
                scope.variables,
                budget,
                span,
            )? {
                return Err(invalid_root(span));
            }
            if exact_current {
                charge(budget, prerequisites.len(), span)?;
            }
            reserve_pending_goals(pending, prerequisites.len(), budget, span)?;
            for (prerequisite, requirement) in
                prerequisites.iter().copied().zip(&fact.prerequisites).rev()
            {
                if prerequisite.index() >= node.index() {
                    return Err(invalid_root(span));
                }
                let application = substitute_evidence_application(
                    requirement.application(),
                    substitution,
                    budget,
                    span,
                )?;
                let mandated_requirement = if exact_current {
                    Some(requirement.id)
                } else {
                    None
                };
                pending.push(PendingGoal::new(
                    prerequisite,
                    application,
                    mandated_requirement,
                ));
            }
        }
    }
    Ok(())
}

fn first_identity_equal_abstract_requirement(
    program: &ResolvedModuleProgram,
    registry: &LinkedInterfaceRegistry,
    scope: EvidenceScope<'_>,
    expected_application: &InterfaceApplication,
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<Option<RequirementId>, EvidenceValidationFailure> {
    let Some(owner) = scope.owner else {
        return Ok(None);
    };
    charge(budget, 1, span)?;
    let requirements = match owner {
        RequirementOwner::Global(binder) => registry
            .scheme(program, binder)
            .map(|scheme| scheme.requirements.as_ref()),
        RequirementOwner::Impl(implementation) => registry
            .implementation(program, implementation)
            .map(|fact| fact.prerequisites.as_ref()),
        RequirementOwner::ResourceFamily(_) => return Err(unknown(span)),
    }
    .ok_or_else(|| unknown(span))?;

    for index in 0..requirements.len() {
        charge(budget, 1, span)?;
        let requirement = requirements.get(index).ok_or_else(|| unknown(span))?;
        if same_application_parts_charged(
            requirement.application(),
            expected_application.interface(),
            expected_application.arguments(),
            budget,
            span,
        )? {
            return Ok(Some(requirement.id));
        }
    }
    Ok(None)
}

fn identity_equal_lexical_source(
    program: &ResolvedModuleProgram,
    registry: &LinkedInterfaceRegistry,
    scope: EvidenceScope<'_>,
    application: &InterfaceApplication,
    budget: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
    span: Span,
) -> Result<Option<crate::interface::LexicalEvidenceId>, EvidenceValidationFailure> {
    let mut head = scope.lexical_head;
    let mut found = None;
    while let Some(index) = head {
        charge(budget, 1, span)?;
        let (source, parent) = scope
            .lexical_sources
            .get(index)
            .ok_or_else(|| invalid_root(span))?;
        if source.same_application(
            program,
            registry,
            application,
            scope,
            budget,
            type_work,
            span,
        )? && found.replace(source.id()).is_some()
        {
            return Err(invalid_root(span));
        }
        head = *parent;
    }
    Ok(found)
}

fn current_identity_substitution_matches(
    fact: &CheckedImplementationFact,
    substitution: &[EvidenceSubstitution],
    scope_variables: &[TypeVariableId],
    registry: &ResolvedRegistry,
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<bool, EvidenceValidationFailure> {
    if fact.head_parameters.len() > scope_variables.len()
        || fact.head_parameters.len() != substitution.len()
    {
        return Ok(false);
    }
    for argument in fact.arguments() {
        validate_argument_with_policy(argument, registry, scope_variables, budget, span)?;
    }
    for ((parameter, scope_variable), binding) in fact
        .head_parameters
        .iter()
        .zip(scope_variables.iter().take(fact.head_parameters.len()))
        .zip(substitution)
    {
        charge(budget, 1, span)?;
        let identity_argument = Type::Variable(parameter.id);
        if *scope_variable != parameter.id
            || binding.parameter() != parameter.id
            || !same_type_charged(binding.argument(), &identity_argument, budget, span)?
        {
            return Ok(false);
        }
    }
    Ok(true)
}

struct PendingGoal {
    node: EvidenceNodeId,
    application: Option<InterfaceApplication>,
    mandated_requirement: Option<RequirementId>,
}

impl PendingGoal {
    const fn new(
        node: EvidenceNodeId,
        application: InterfaceApplication,
        mandated_requirement: Option<RequirementId>,
    ) -> Self {
        Self {
            node,
            application: Some(application),
            mandated_requirement,
        }
    }

    fn application(&self) -> &InterfaceApplication {
        self.application
            .as_ref()
            .expect("a pending evidence goal retains its application")
    }
}

impl Drop for PendingGoal {
    fn drop(&mut self) {
        drop(self.application.take());
    }
}

#[derive(Default)]
struct PendingGoals(Vec<PendingGoal>);

impl PendingGoals {
    fn try_reserve(&mut self, additional: usize) -> Result<(), std::collections::TryReserveError> {
        self.0.try_reserve(additional)
    }

    fn push(&mut self, goal: PendingGoal) {
        self.0.push(goal);
    }

    fn pop(&mut self) -> Option<PendingGoal> {
        self.0.pop()
    }
}

fn reserve_pending_goals(
    pending: &mut PendingGoals,
    additional: usize,
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<(), EvidenceValidationFailure> {
    charge(budget, additional, span)?;
    pending.try_reserve(additional).map_err(|_| resource(span))
}

fn implementation_head_matches(
    fact: &CheckedImplementationFact,
    substitution: &[EvidenceSubstitution],
    goal: &InterfaceApplication,
    registry: &ResolvedRegistry,
    goal_variables: &[TypeVariableId],
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<bool, EvidenceValidationFailure> {
    if fact.interface() != goal.interface() || fact.head_parameters.len() != substitution.len() {
        return Ok(false);
    }
    charge(budget, fact.head_parameters.len(), span)?;
    let mut head_variables = Vec::new();
    head_variables
        .try_reserve(fact.head_parameters.len())
        .map_err(|_| resource(span))?;
    head_variables.extend(fact.head_parameters.iter().map(|parameter| parameter.id));
    for argument in fact.arguments() {
        validate_argument_with_policy(argument, registry, &head_variables, budget, span)?;
    }
    for (parameter, binding) in fact.head_parameters.iter().zip(substitution) {
        charge(budget, 1, span)?;
        validate_type_with_application_policy(
            binding.argument(),
            registry,
            goal_variables,
            budget,
            span,
        )?;
        if binding.parameter() != parameter.id {
            return Ok(false);
        }
    }

    let instantiated =
        substitute_evidence_application(fact.application(), substitution, budget, span)?;
    same_application_parts_charged(
        &instantiated,
        goal.interface(),
        goal.arguments(),
        budget,
        span,
    )
}

fn validate_type_with_application_policy(
    root: &Type,
    registry: &ResolvedRegistry,
    variables: &[TypeVariableId],
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<(), EvidenceValidationFailure> {
    enum Task<'a> {
        Visit(&'a Type),
        Sequence(std::slice::Iter<'a, Type>),
    }

    let mut unique = HashSet::new();
    charge(budget, variables.len(), span)?;
    unique
        .try_reserve(variables.len())
        .map_err(|_| resource(span))?;
    for variable in variables {
        charge(budget, 1, span)?;
        if !unique.insert(*variable)
            || registry
                .type_variable(*variable)
                .is_none_or(|known| known.id != *variable)
        {
            return Err(invalid_root(span));
        }
    }

    let mut pending = Vec::new();
    charge(budget, 1, span)?;
    pending.try_reserve(1).map_err(|_| resource(span))?;
    pending.push(Task::Visit(root));
    while let Some(task) = pending.pop() {
        match task {
            Task::Visit(ty) => {
                charge(budget, 1, span)?;
                if let Some(function) = ty.function_view() {
                    let effects = function.effects();
                    if let Some(tail) = effects.and_then(|effects| effects.tail()) {
                        let EffectRowVariable::Rigid(id) = tail.variable() else {
                            return Err(invalid_root(span));
                        };
                        if !unique.contains(&id)
                            || registry
                                .type_variable(id)
                                .is_none_or(|parameter| parameter.kind != Kind::EffectRow)
                        {
                            return Err(invalid_root(span));
                        }
                    }
                    let mut effect_argument_count = 0usize;
                    if let Some(effects) = effects {
                        for member in effects.known() {
                            charge(budget, 1, span)?;
                            effect_argument_count = effect_argument_count
                                .checked_add(member.arguments().len())
                                .ok_or_else(|| resource(span))?;
                        }
                    }
                    let effect_arguments = effects
                        .into_iter()
                        .flat_map(|effects| {
                            effects
                                .known()
                                .iter()
                                .chain(effects.tail().into_iter().flat_map(|tail| tail.lacks()))
                        })
                        .flat_map(|instance| instance.arguments());
                    let children = effect_argument_count
                        .checked_add(2)
                        .ok_or_else(|| resource(span))?;
                    charge(budget, children, span)?;
                    pending.try_reserve(children).map_err(|_| resource(span))?;
                    visit_owner_components_with_charge(
                        effect_arguments,
                        &mut |cells| charge(budget, cells, span),
                        |ty, _| {
                            pending.try_reserve(1).map_err(|_| resource(span))?;
                            pending.push(Task::Visit(ty));
                            Ok(())
                        },
                        |tail, _| {
                            let EffectRowVariable::Rigid(id) = tail.variable() else {
                                return Err(invalid_root(span));
                            };
                            if !unique.contains(&id)
                                || registry
                                    .type_variable(id)
                                    .is_none_or(|parameter| parameter.kind != Kind::EffectRow)
                            {
                                return Err(invalid_root(span));
                            }
                            Ok(())
                        },
                    )?;
                    pending.push(Task::Visit(function.value()));
                    pending.push(Task::Visit(function.domain()));
                    continue;
                }
                match ty {
                    Type::Bytes | Type::String | Type::Int | Type::Bool | Type::Unit => {}
                    Type::Nominal(id) => {
                        if registry.nominal_kind(*id).is_none() {
                            return Err(invalid_root(span));
                        }
                    }
                    Type::Inference(_) | Type::Forall(_, _) => {
                        return Err(invalid_root(span));
                    }
                    Type::Variable(variable) if unique.contains(variable) => {}
                    Type::Variable(_) => return Err(invalid_root(span)),
                    Type::Application(function, argument) => {
                        charge(budget, 2, span)?;
                        pending.try_reserve(2).map_err(|_| resource(span))?;
                        pending.push(Task::Visit(argument));
                        pending.push(Task::Visit(function));
                    }
                    Type::ResourceApply(_, arguments) => {
                        visit_owner_components_with_charge(
                            arguments.iter(),
                            &mut |cells| charge(budget, cells, span),
                            |ty, _| {
                                pending.try_reserve(1).map_err(|_| resource(span))?;
                                pending.push(Task::Visit(ty));
                                Ok(())
                            },
                            |tail, _| {
                                let EffectRowVariable::Rigid(id) = tail.variable() else {
                                    return Err(invalid_root(span));
                                };
                                if !unique.contains(&id)
                                    || registry
                                        .type_variable(id)
                                        .is_none_or(|parameter| parameter.kind != Kind::EffectRow)
                                {
                                    return Err(invalid_root(span));
                                }
                                Ok(())
                            },
                        )?;
                    }
                    Type::Tuple(elements) if elements.len() >= 2 => {
                        charge(budget, 1, span)?;
                        pending.try_reserve(1).map_err(|_| resource(span))?;
                        pending.push(Task::Sequence(elements.iter()));
                    }
                    Type::Tuple(_) => return Err(invalid_root(span)),
                    Type::Function(_, _) | Type::EffectfulFunction(_, _) => unreachable!(),
                }
            }
            Task::Sequence(mut remaining) => {
                if let Some(next) = remaining.next() {
                    charge(budget, 2, span)?;
                    pending.try_reserve(2).map_err(|_| resource(span))?;
                    pending.push(Task::Sequence(remaining));
                    pending.push(Task::Visit(next));
                }
            }
        }
    }
    Ok(())
}

fn same_argument_charged(
    left: &KindedArgument,
    right: &KindedArgument,
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<bool, EvidenceValidationFailure> {
    same_kinded_argument_with_constraint_budget(left, right, budget).map_err(|()| resource(span))
}
fn validate_argument_with_policy(
    argument: &KindedArgument,
    registry: &ResolvedRegistry,
    variables: &[TypeVariableId],
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<(), EvidenceValidationFailure> {
    let mut leaves = Vec::new();
    visit_owner_components_with_charge(
        std::iter::once(argument),
        &mut |cells| charge(budget, cells, span),
        |ty, _| {
            leaves.try_reserve(1).map_err(|_| resource(span))?;
            leaves.push(ty);
            Ok(())
        },
        |tail, _| {
            let EffectRowVariable::Rigid(id) = tail.variable() else {
                return Err(invalid_root(span));
            };
            if !variables.contains(&id)
                || registry
                    .type_variable(id)
                    .is_none_or(|parameter| parameter.kind != Kind::EffectRow)
            {
                return Err(invalid_root(span));
            }
            Ok(())
        },
    )?;
    for ty in leaves {
        validate_type_with_application_policy(ty, registry, variables, budget, span)?;
    }
    Ok(())
}

fn same_type_charged(
    left: &Type,
    right: &Type,
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<bool, EvidenceValidationFailure> {
    same_semantic_type_with_constraint_budget(left, right, budget).map_err(|()| resource(span))
}

fn same_binders_charged(
    left: &[ResolvedTypeVariable],
    right: &[ResolvedTypeVariable],
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<bool, EvidenceValidationFailure> {
    if left.len() != right.len() {
        return Ok(false);
    }
    for (left, right) in left.iter().zip(right) {
        charge(budget, 1, span)?;
        if left.id != right.id
            || left.spelling != right.spelling
            || !same_origin_charged(&left.origin, &right.origin, budget, span)?
            || !same_kind_with_charge(&left.kind, &right.kind, || budget.charge(1))
                .map_err(|()| resource(span))?
        {
            return Ok(false);
        }
    }
    Ok(true)
}

fn same_origin_charged(
    mut left: &Origin,
    mut right: &Origin,
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<bool, EvidenceValidationFailure> {
    loop {
        charge(budget, 1, span)?;
        match (left, right) {
            (Origin::Source(left), Origin::Source(right)) => return Ok(left == right),
            (
                Origin::Generated {
                    cause: left_cause,
                    reason: left_reason,
                },
                Origin::Generated {
                    cause: right_cause,
                    reason: right_reason,
                },
            ) if left_reason == right_reason => {
                left = left_cause;
                right = right_cause;
            }
            (
                Origin::Related {
                    primary: left_primary,
                    related: left_related,
                },
                Origin::Related {
                    primary: right_primary,
                    related: right_related,
                },
            ) if left_related.len() == right_related.len() => {
                charge(budget, left_related.len(), span)?;
                if left_related != right_related {
                    return Ok(false);
                }
                left = left_primary;
                right = right_primary;
            }
            _ => return Ok(false),
        }
    }
}

struct TypeBuffer(Vec<Type>);

impl TypeBuffer {
    fn new() -> Self {
        Self(Vec::new())
    }

    #[cfg(test)]
    fn len(&self) -> usize {
        self.0.len()
    }

    fn try_reserve(&mut self, additional: usize) -> Result<(), std::collections::TryReserveError> {
        self.0.try_reserve(additional)
    }

    fn push(&mut self, ty: Type) {
        self.0.push(ty);
    }

    fn into_boxed_slice(mut self) -> Box<[Type]> {
        std::mem::take(&mut self.0).into_boxed_slice()
    }
}

impl Drop for TypeBuffer {
    fn drop(&mut self) {
        for ty in self.0.drain(..) {
            discard_type_iteratively(ty);
        }
    }
}

fn evidence_replacements(
    substitution: &[EvidenceSubstitution],
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<OwnerReplacements, EvidenceValidationFailure> {
    let mut result = OwnerReplacements {
        types: HashMap::new(),
        rows: HashMap::new(),
    };
    charge(budget, substitution.len(), span)?;
    result
        .types
        .try_reserve(substitution.len())
        .map_err(|_| resource(span))?;
    for binding in substitution {
        if result.types.contains_key(&binding.parameter()) {
            return Err(invalid_root(span));
        }
        let copied =
            clone_type_with_budget(binding.argument(), &mut |cells| charge(budget, cells, span))?;
        result.insert_discarding_previous(binding.parameter(), KindedArgument::TypeArg(copied));
    }
    Ok(result)
}
#[cfg(test)]
fn substitute_evidence_type(
    root: &Type,
    substitution: &[EvidenceSubstitution],
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<Type, EvidenceValidationFailure> {
    let replacements = evidence_replacements(substitution, budget, span)?;
    crate::types::substitute_type_and_row_variables_strict_source_with(
        root,
        &replacements.types,
        &replacements.rows,
        |cells| charge(budget, cells, span),
        || resource(span),
        || invalid_root(span),
    )?
    .map_err(|_| invalid_root(span))
}
fn substitute_evidence_application(
    application: &InterfaceApplication,
    substitution: &[EvidenceSubstitution],
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<InterfaceApplication, EvidenceValidationFailure> {
    let replacements = evidence_replacements(substitution, budget, span)?;
    charge(budget, application.arguments().len(), span)?;
    let mut arguments = Vec::new();
    arguments
        .try_reserve(application.arguments().len())
        .map_err(|_| resource(span))?;
    for argument in application.arguments() {
        let mapped = crate::types::substitute_kinded_argument_strict_source_with(
            argument,
            &replacements.types,
            &replacements.rows,
            |cells| charge(budget, cells, span),
            || resource(span),
            || invalid_root(span),
        )?
        .map_err(|_| invalid_root(span))?;
        arguments.push(IterativeArgumentOwner::new(mapped));
    }
    charge(budget, arguments.len(), span)?;
    let mut retained = Vec::new();
    retained
        .try_reserve(arguments.len())
        .map_err(|_| resource(span))?;
    retained.extend(
        arguments
            .into_iter()
            .map(IterativeArgumentOwner::into_inner),
    );
    Ok(InterfaceApplication::new_kinded(
        application.interface(),
        retained.into_boxed_slice(),
    ))
}

fn implementation_is_available(
    program: &ResolvedModuleProgram,
    registry: &LinkedInterfaceRegistry,
    group: &ResolvedModuleGroup,
    implementation: ImplId,
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<bool, EvidenceValidationFailure> {
    for index in 0..group.available_implementations().len() {
        charge(budget, 1, span)?;
        let available = group
            .available_implementations()
            .get(index)
            .ok_or_else(|| unknown(span))?;
        if available.id() == implementation {
            let group_index = registry
                .modules
                .get(&group.module())
                .copied()
                .ok_or_else(|| unknown(span))?;
            if registry.authenticate_available_implementation(
                program,
                group_index,
                group,
                available,
                budget,
            )? {
                return Ok(true);
            }
            return Err(unknown(group.span()));
        }
    }
    Ok(false)
}

fn authorization_suffix_matches(
    authorization: &ImplementationAuthorization,
    dependency: &ImplementationAuthorization,
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<bool, EvidenceValidationFailure> {
    let Some(suffix_length) = authorization.hops().len().checked_sub(1) else {
        return Ok(false);
    };
    charge(budget, 1, span)?;
    if suffix_length != dependency.hops().len() {
        return Ok(false);
    }
    for (actual, expected) in authorization.hops()[1..].iter().zip(dependency.hops()) {
        charge(budget, 1, span)?;
        if actual.from != expected.from
            || actual.to != expected.to
            || actual.import_span != expected.import_span
        {
            return Ok(false);
        }
    }
    Ok(true)
}

fn has_direct_dependency(
    group: &ResolvedModuleGroup,
    target: ModuleId,
    import_span: Span,
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<bool, EvidenceValidationFailure> {
    for index in 0..group.direct_dependencies().len() {
        charge(budget, 1, span)?;
        let route = group
            .direct_dependencies()
            .get(index)
            .ok_or_else(|| unknown(import_span))?;
        if route.target() == target && route.import_span() == import_span {
            return Ok(true);
        }
    }
    Ok(false)
}

enum LinkedLocalScope<'a> {
    Annotation(&'a crate::resolved::ResolvedType),
    Equation {
        source: &'a crate::resolved::ResolvedLexicalEvidence,
        method: &'a crate::resolved::ResolvedImplementationMethodGroup,
    },
    Method(&'a crate::resolved::ResolvedImplementationMethodGroup),
    Nominal(NominalTypeId),
    Resource(&'a crate::resolved::ResolvedResourceExpr),
    Store(&'a crate::resolved::ResolvedStoreExpr),
    Network(&'a crate::resolved::ResolvedNetworkExpr),
    Region(&'a crate::resolved::ResolvedRegionExpr),
}

// The same fixed-size pure shape excluded by ordinary scheme qualification.
// All other shapes retain only an original borrowed coordinate and are fully
// traversed, with charges, only when a row-bearing lexical owner needs facts.
fn may_have_source_row_context(ty: &Type) -> bool {
    let atomic = |ty: &Type| {
        matches!(
            ty,
            Type::Bytes
                | Type::String
                | Type::Int
                | Type::Bool
                | Type::Unit
                | Type::Nominal(_)
                | Type::Variable(_)
                | Type::Inference(_)
        )
    };
    !atomic(ty)
        && !matches!(ty, Type::Function(domain, codomain) if atomic(domain) && atomic(codomain))
}

#[allow(clippy::too_many_arguments)]
fn authenticate_lexical_header(
    program: &ResolvedModuleProgram,
    registry: &LinkedInterfaceRegistry,
    source: &crate::resolved::ResolvedLexicalEvidence,
    scope: EvidenceScope<'_>,
    locals: &[(LinkedLocalScope<'_>, Option<usize>)],
    local_head: Option<usize>,
    budget: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
) -> Result<(), EvidenceValidationFailure> {
    charge(budget, 1, source.span)?;
    let checked = source
        .checked
        .get()
        .ok_or_else(|| invalid_root(source.span))?;
    if checked.application.interface() != source.application.interface.id
        || checked.application.arguments().len() != source.application.arguments.len()
    {
        return Err(invalid_root(source.span));
    }
    let expected = lexical_sources::lexical_context_rows(
        program, registry, source, scope, locals, local_head, budget, type_work,
    )?;
    for (actual, original) in checked
        .application
        .arguments()
        .iter()
        .zip(&source.application.arguments)
    {
        let qualified = crate::types::qualify_kinded_argument_with_row_contexts_with_budget(
            &original.ty,
            expected.iter(),
            type_work,
        )
        .map_err(|()| type_resource(source.span))?
        .map_err(|_| invalid_root(source.span))?;
        let qualified = qualified.map(crate::types::IterativeArgumentOwner::new);
        if !same_argument_charged(
            actual,
            qualified.as_deref().unwrap_or(&original.ty),
            budget,
            source.span,
        )? {
            return Err(invalid_root(source.span));
        }
    }
    let interface = registry
        .interface(program, checked.application.interface())
        .ok_or_else(|| unknown(source.span))?;
    if interface.id.module().is_builtin_resource() && source.acquisition.is_none() {
        return Err(invalid_root(source.span));
    }
    let keys = linked_selection_key_types(
        interface,
        checked.application.arguments(),
        budget,
        source.span,
    )?;
    let mut nominals = HashSet::new();
    let mut has_local_key = false;
    if let Some(acquisition) = source.acquisition {
        if checked.acquisition != Some(acquisition)
            || !acquisition
                .supplies(source, type_work)
                .map_err(|()| resource(source.span))?
        {
            return Err(invalid_root(source.span));
        }
        let mut head = local_head;
        while let Some(index) = head {
            charge(budget, 1, source.span)?;
            let (entry, parent) = locals.get(index).ok_or_else(|| invalid_root(source.span))?;
            if let LinkedLocalScope::Resource(resource_scope) = entry {
                has_local_key = acquisition
                    .owns(resource_scope, type_work)
                    .map_err(|()| resource(source.span))?;
                break;
            }
            head = *parent;
        }
        if !has_local_key {
            return Err(invalid_root(source.span));
        }
    } else if checked.acquisition.is_some() {
        return Err(invalid_root(source.span));
    }
    for argument in checked.application.arguments() {
        validate_argument_with_policy(
            argument,
            program.registry(),
            scope.variables,
            budget,
            source.span,
        )?;
        nominals.clear();
        crate::resolved::collect_argument_nominal_identities(argument, &mut nominals, type_work)
            .map_err(|()| type_resource(source.span))?;
        charge(budget, keys.len(), source.span)?;
        let is_key = keys.iter().any(|key| std::ptr::eq(*key, argument));
        charge(budget, nominals.capacity(), source.span)?;
        for nominal in &nominals {
            if !nominal.is_lexical() {
                continue;
            }
            let mut head = local_head;
            let mut active = false;
            while let Some(index) = head {
                charge(budget, 1, source.span)?;
                let (entry, parent) = locals.get(index).ok_or_else(|| invalid_root(source.span))?;
                if matches!(entry, LinkedLocalScope::Nominal(owner) if owner == nominal) {
                    active = true;
                    break;
                }
                head = *parent;
            }
            if !active {
                return Err(invalid_root(source.span));
            }
            has_local_key |= is_key;
        }
    }
    if !has_local_key {
        return Err(invalid_root(source.span));
    }
    let mut head = scope.lexical_head;
    while let Some(index) = head {
        charge(budget, 1, source.span)?;
        let (earlier, parent) = scope
            .lexical_sources
            .get(index)
            .ok_or_else(|| invalid_root(source.span))?;
        let earlier = earlier.application(source.span)?;
        if earlier.interface() == interface.id {
            let earlier_keys =
                linked_selection_key_types(interface, earlier.arguments(), budget, source.span)?;
            let mut equal = true;
            for (key, earlier) in keys.iter().zip(earlier_keys) {
                if !same_argument_charged(key, earlier, budget, source.span)? {
                    equal = false;
                    break;
                }
            }
            if equal {
                return Err(invalid_root(source.span));
            }
        }
        head = *parent;
    }
    Ok(())
}

#[allow(clippy::too_many_arguments, clippy::type_complexity)]
fn schedule_lexical_block<'a>(
    pending: &mut Vec<&'a ResolvedExpr>,
    heads: &mut Vec<(Option<usize>, Option<usize>)>,
    sources: &mut Vec<(LinkedLexicalSource<'a>, Option<usize>)>,
    method_scopes: &mut Vec<(LinkedLocalScope<'a>, Option<usize>)>,
    mut head: (Option<usize>, Option<usize>),
    block: &'a ResolvedBlock,
    budget: &mut InterfaceConstraintBudget,
    track_provider_equations: bool,
    original: OriginalLexicalContext,
    mut header_scope: Option<(
        &ResolvedModuleProgram,
        &LinkedInterfaceRegistry,
        &[TypeVariableId],
        Option<RequirementOwner>,
        &mut TypeWorkBudget,
        bool,
    )>,
) -> Result<(), EvidenceValidationFailure> {
    let start = pending.len();
    let include_nominals = header_scope
        .as_ref()
        .is_some_and(|(_, _, _, _, _, headers_only)| *headers_only)
        || track_provider_equations;
    let (additional, has_lexical_scope) = block_schedule_shape_with_annotation_check(
        block,
        include_nominals,
        budget,
        |annotation, budget| {
            if let Some((program, registry, _, _, work, _)) = header_scope.as_mut() {
                validate_original_annotation_row_formation(
                    program, registry, annotation, original, budget, work,
                )?;
            }
            Ok(())
        },
    )?;
    if !has_lexical_scope {
        schedule_counted_block(pending, block, additional, budget)?;
        if !sources.is_empty() || !method_scopes.is_empty() {
            resize_lexical_heads(heads, pending.len(), head, budget, block.span)?;
        }
        return Ok(());
    }
    resize_lexical_heads(heads, pending.len(), head, budget, block.span)?;
    for declaration in &block.declarations {
        match declaration {
            ResolvedLocalDeclaration::Evidence(source) => {
                if let Some((program, registry, variables, owner, type_work, true)) =
                    header_scope.as_mut()
                {
                    authenticate_lexical_header(
                        program,
                        registry,
                        source,
                        EvidenceScope {
                            local_scopes: method_scopes,
                            lexical_sources: sources,
                            lexical_head: head.0,
                            variables,
                            owner: *owner,
                        },
                        method_scopes,
                        head.1,
                        budget,
                        type_work,
                    )?;
                }
                charge(budget, 2, source.span)?;
                sources.try_reserve(1).map_err(|_| resource(source.span))?;
                for method in &source.method_groups {
                    let mut method_head = head;
                    if !method.contextual_parameters.is_empty() {
                        charge(budget, 2, method.span)?;
                        method_scopes
                            .try_reserve(1)
                            .map_err(|_| resource(method.span))?;
                        method_head.1 = Some(method_scopes.len());
                        method_scopes.push((LinkedLocalScope::Method(method), head.1));
                    }
                    for equation in &method.equations {
                        // Each supplied method checks its own equation row,
                        // even when it has no contextual type parameters.
                        let equation_head = if track_provider_equations {
                            charge(budget, 2, equation.span)?;
                            method_scopes
                                .try_reserve(1)
                                .map_err(|_| resource(equation.span))?;
                            let index = method_scopes.len();
                            method_scopes.push((
                                LinkedLocalScope::Equation { source, method },
                                method_head.1,
                            ));
                            Some(index)
                        } else {
                            method_head.1
                        };
                        reserve_expressions(pending, 1, budget, equation.span)?;
                        resize_lexical_heads(
                            heads,
                            pending.len() + 1,
                            (method_head.0, equation_head),
                            budget,
                            equation.span,
                        )?;
                        pending.push(&equation.body);
                    }
                }
                let next = sources.len();
                sources.push((
                    LinkedLexicalSource::Declared(
                        source,
                        OriginalLexicalContext {
                            local_head: head.1,
                            ..original
                        },
                    ),
                    head.0,
                ));
                head.0 = Some(next);
            }
            ResolvedLocalDeclaration::Binding(binding) => {
                reserve_expressions(pending, 1, budget, binding.span)?;
                let binding_head = if let Some(annotation) = &binding.annotation
                    && may_have_source_row_context(&annotation.ty)
                {
                    charge(budget, 2, binding.span)?;
                    method_scopes
                        .try_reserve(1)
                        .map_err(|_| resource(binding.span))?;
                    let index = method_scopes.len();
                    method_scopes.push((LinkedLocalScope::Annotation(annotation), head.1));
                    (head.0, Some(index))
                } else {
                    head
                };
                resize_lexical_heads(heads, pending.len() + 1, binding_head, budget, binding.span)?;
                pending.push(&binding.initializer);
            }
            ResolvedLocalDeclaration::Recursive(group) => {
                reserve_expressions(pending, group.members.len(), budget, group.span)?;
                for member in &group.members {
                    if !may_have_source_row_context(&member.annotation.ty) {
                        resize_lexical_heads(heads, pending.len() + 1, head, budget, group.span)?;
                        pending.push(&member.initializer);
                        continue;
                    }
                    charge(budget, 2, group.span)?;
                    method_scopes
                        .try_reserve(1)
                        .map_err(|_| resource(group.span))?;
                    let index = method_scopes.len();
                    method_scopes.push((LinkedLocalScope::Annotation(&member.annotation), head.1));
                    resize_lexical_heads(
                        heads,
                        pending.len() + 1,
                        (head.0, Some(index)),
                        budget,
                        group.span,
                    )?;
                    pending.push(&member.initializer);
                }
            }
            ResolvedLocalDeclaration::Newtype(nominal) => {
                if header_scope.is_some() {
                    charge(budget, 2, block.span)?;
                    method_scopes
                        .try_reserve(1)
                        .map_err(|_| resource(block.span))?;
                    let index = method_scopes.len();
                    method_scopes.push((LinkedLocalScope::Nominal(*nominal), head.1));
                    head.1 = Some(index);
                }
            }
        }
    }
    reserve_expressions(pending, 1, budget, block.span)?;
    resize_lexical_heads(heads, pending.len() + 1, head, budget, block.span)?;
    pending.push(&block.result);
    pending[start..].reverse();
    heads[start..].reverse();
    Ok(())
}

fn resize_lexical_heads(
    heads: &mut Vec<(Option<usize>, Option<usize>)>,
    length: usize,
    head: (Option<usize>, Option<usize>),
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<(), EvidenceValidationFailure> {
    let additional = length.saturating_sub(heads.len());
    charge(
        budget,
        additional.saturating_mul(1 + usize::from(head.1.is_some())),
        span,
    )?;
    heads.try_reserve(additional).map_err(|_| resource(span))?;
    heads.resize(length, head);
    Ok(())
}

#[cfg(test)]
fn schedule_block<'a>(
    pending: &mut Vec<&'a ResolvedExpr>,
    block: &'a ResolvedBlock,
    budget: &mut InterfaceConstraintBudget,
) -> Result<(), EvidenceValidationFailure> {
    let (additional, _) = block_schedule_shape(block, false, budget)?;
    schedule_counted_block(pending, block, additional, budget)
}

fn validate_original_annotation_row_formation(
    program: &ResolvedModuleProgram,
    registry: &LinkedInterfaceRegistry,
    annotation: &crate::resolved::ResolvedType,
    original: OriginalLexicalContext,
    budget: &mut InterfaceConstraintBudget,
    work: &mut TypeWorkBudget,
) -> Result<(), EvidenceValidationFailure> {
    let span = annotation.span;
    let mut required = HashMap::new();
    crate::types::qualify_scheme_row_replacements_with_budget(
        &annotation.ty,
        &HashMap::new(),
        &mut required,
        true,
        work,
    )
    .map_err(|()| type_resource(span))?;
    if required.is_empty() {
        return Ok(());
    }
    charge(budget, 1, span)?;
    let scheme = match original.owner {
        Some(RequirementOwner::Global(binder)) => {
            &registry
                .scheme(program, binder)
                .ok_or_else(|| unknown(span))?
                .value_type
        }
        _ => return Err(invalid_root(span)),
    };
    let mut established = HashMap::new();
    crate::types::qualify_scheme_row_replacements_with_budget(
        scheme,
        &HashMap::new(),
        &mut established,
        true,
        work,
    )
    .map_err(|()| type_resource(span))?;
    if !crate::types::rigid_row_requirements_entailed_with_budget(
        &required,
        std::slice::from_ref(&established),
        work,
    )
    .map_err(|()| type_resource(span))?
    {
        return Err(invalid_root(span));
    }
    Ok(())
}

#[cfg(test)]
fn block_schedule_shape(
    block: &ResolvedBlock,
    include_nominals: bool,
    budget: &mut InterfaceConstraintBudget,
) -> Result<(usize, bool), EvidenceValidationFailure> {
    block_schedule_shape_with_annotation_check(block, include_nominals, budget, |_, _| Ok(()))
}

fn block_schedule_shape_with_annotation_check(
    block: &ResolvedBlock,
    include_nominals: bool,
    budget: &mut InterfaceConstraintBudget,
    mut annotation_check: impl FnMut(
        &crate::resolved::ResolvedType,
        &mut InterfaceConstraintBudget,
    ) -> Result<(), EvidenceValidationFailure>,
) -> Result<(usize, bool), EvidenceValidationFailure> {
    let mut additional = 1usize;
    let mut has_lexical_scope = false;
    for declaration in &block.declarations {
        charge(budget, 1, block.span)?;
        match declaration {
            ResolvedLocalDeclaration::Evidence(source) => {
                has_lexical_scope = true;
                charge(budget, source.method_groups.len(), source.span)?;
                for group in &source.method_groups {
                    additional = additional
                        .checked_add(group.equations.len())
                        .ok_or_else(|| resource(block.span))?;
                }
            }
            ResolvedLocalDeclaration::Binding(binding) => {
                if let Some(annotation) = &binding.annotation {
                    annotation_check(annotation, budget)?;
                }
                has_lexical_scope |= include_nominals
                    && binding
                        .annotation
                        .as_ref()
                        .is_some_and(|annotation| may_have_source_row_context(&annotation.ty));
                additional = additional
                    .checked_add(1)
                    .ok_or_else(|| resource(block.span))?;
            }
            ResolvedLocalDeclaration::Recursive(group) => {
                has_lexical_scope |= include_nominals
                    && group
                        .members
                        .iter()
                        .any(|member| may_have_source_row_context(&member.annotation.ty));
                for member in &group.members {
                    charge(budget, 1, block.span)?;
                    annotation_check(&member.annotation, budget)?;
                    additional = additional
                        .checked_add(1)
                        .ok_or_else(|| resource(block.span))?;
                }
            }
            ResolvedLocalDeclaration::Newtype(_) => has_lexical_scope |= include_nominals,
        }
    }
    Ok((additional, has_lexical_scope))
}

fn schedule_counted_block<'a>(
    pending: &mut Vec<&'a ResolvedExpr>,
    block: &'a ResolvedBlock,
    additional: usize,
    budget: &mut InterfaceConstraintBudget,
) -> Result<(), EvidenceValidationFailure> {
    reserve_expressions(pending, additional, budget, block.span)?;
    pending.push(block.result.as_ref());
    for declaration in block.declarations.iter().rev() {
        match declaration {
            ResolvedLocalDeclaration::Evidence(source) => {
                pending.extend(
                    source.method_groups.iter().rev().flat_map(|group| {
                        group.equations.iter().rev().map(|equation| &equation.body)
                    }),
                );
            }
            ResolvedLocalDeclaration::Binding(binding) => pending.push(&binding.initializer),
            ResolvedLocalDeclaration::Recursive(group) => {
                pending.extend(group.members.iter().rev().map(|member| &member.initializer));
            }
            ResolvedLocalDeclaration::Newtype(_) => {}
        }
    }
    Ok(())
}

fn reserve_expressions<T>(
    pending: &mut Vec<T>,
    additional: usize,
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<(), EvidenceValidationFailure> {
    charge(budget, additional, span)?;
    pending.try_reserve(additional).map_err(|_| resource(span))
}

fn charge(
    budget: &mut InterfaceConstraintBudget,
    work: usize,
    span: Span,
) -> Result<(), EvidenceValidationFailure> {
    budget.charge(work).map_err(|()| resource(span))
}

const fn unknown(span: Span) -> EvidenceValidationFailure {
    EvidenceValidationFailure::new(EvidenceValidationReason::UnknownIdentity, span)
}

const fn unavailable(span: Span) -> EvidenceValidationFailure {
    EvidenceValidationFailure::new(EvidenceValidationReason::UnavailableImplementation, span)
}

const fn invalid_root(span: Span) -> EvidenceValidationFailure {
    EvidenceValidationFailure::new(EvidenceValidationReason::InvalidEvidenceRoot, span)
}

const fn resource(span: Span) -> EvidenceValidationFailure {
    EvidenceValidationFailure::new(EvidenceValidationReason::ConstraintResourceExhausted, span)
}

const fn type_resource(span: Span) -> EvidenceValidationFailure {
    EvidenceValidationFailure::new(EvidenceValidationReason::TypeResourceExhausted, span)
}

#[cfg(test)]
mod tests {
    use std::{
        cell::Cell,
        fs,
        path::PathBuf,
        sync::atomic::{AtomicU64, Ordering},
        thread,
    };

    use super::*;
    fn test_type_argument(argument: &KindedArgument) -> &Type {
        let KindedArgument::TypeArg(ty) = argument else {
            panic!("fixture expects a Type argument");
        };
        ty
    }
    trait TestArgument {
        fn into_argument(self) -> KindedArgument;
    }
    impl TestArgument for Type {
        fn into_argument(self) -> KindedArgument {
            KindedArgument::TypeArg(self)
        }
    }
    impl TestArgument for KindedArgument {
        fn into_argument(self) -> KindedArgument {
            self
        }
    }
    fn test_application<T: TestArgument>(
        interface: InterfaceId,
        arguments: Box<[T]>,
    ) -> InterfaceApplication {
        InterfaceApplication::new_kinded(
            interface,
            arguments
                .into_vec()
                .into_iter()
                .map(TestArgument::into_argument)
                .collect::<Vec<_>>()
                .into_boxed_slice(),
        )
    }

    use crate::{
        elaborate::{
            check_module, link_modules, link_modules_with_budget, link_modules_with_budgets,
        },
        interface::{EvidenceSelectionBuilder, match_implementation_head_structurally},
        module::{ModuleGraph, ModuleRoots, load_module_graph},
        resolve::{DependencyExports, resolve_module},
        resolved::{
            CheckedModule, ImplementationRoute, ImplementationRouteHop, ResolvedTypeVariable,
            same_imported_constructor_fact_with_budget,
        },
        source::{ByteRange, SourceFile},
        types::{InferenceVariableId, Kind, NominalTypeId, Type, TypeVariableId, TypeWorkBudget},
    };

    static FIXTURE_IDS: AtomicU64 = AtomicU64::new(0);

    #[test]
    fn kind_causes_survive_all_evidence_adapters() {
        use crate::{
            message::{Catalogue, Locale},
            presentation::{compile_evidence_failure, write_human, write_json},
        };
        let declaration = SourceFile::new("declaration.ash", "binder").unwrap();
        let occurrence = SourceFile::new("occurrence.ash", "use").unwrap();
        let declaration_span = declaration.span(ByteRange::new(0, 6).unwrap()).unwrap();
        let occurrence_span = occurrence.span(ByteRange::new(0, 3).unwrap()).unwrap();
        type KindAdapter = fn(KindFailure, Span) -> EvidenceValidationFailure;
        let adapters: [(
            KindAdapter,
            EvidenceValidationReason,
            EvidenceValidationReason,
        ); 3] = [
            (
                map_kind_type_failure,
                EvidenceValidationReason::UnknownIdentity,
                EvidenceValidationReason::TypeResourceExhausted,
            ),
            (
                map_selected_kind_type_failure,
                EvidenceValidationReason::InvalidEvidenceRoot,
                EvidenceValidationReason::TypeResourceExhausted,
            ),
            (
                map_selected_kind_constraint_failure,
                EvidenceValidationReason::InvalidEvidenceRoot,
                EvidenceValidationReason::ConstraintResourceExhausted,
            ),
        ];
        for (adapt, reason, resource_reason) in adapters {
            for span in [declaration_span, occurrence_span] {
                let mut environments = KindEnvironments::new();
                let identity = TypeVariableId::new(0);
                let kind = Kind::Type;
                environments
                    .insert_declared(
                        identity,
                        &kind,
                        declaration_span,
                        &mut TypeWorkBudget::with_limit(1),
                    )
                    .unwrap();
                let error = environments
                    .insert_declared(
                        identity,
                        &kind,
                        declaration_span,
                        &mut TypeWorkBudget::with_limit(1),
                    )
                    .unwrap_err();
                let failure = adapt(error, span);
                assert_eq!(failure.reason(), reason);
                assert_eq!(failure.primary(), span);
                let view =
                    compile_evidence_failure(&failure, &[&declaration, &occurrence]).unwrap();
                for locale in [Locale::English, Locale::Bulgarian] {
                    let mut output = Vec::new();
                    write_human(&mut output, &view, &Catalogue::new(locale).unwrap()).unwrap();
                    if locale == Locale::English {
                        assert!(
                            String::from_utf8(output)
                                .unwrap()
                                .contains("duplicate type-variable identity")
                        );
                    }
                }
                let mut output = Vec::new();
                write_json(&mut output, &view).unwrap();
                let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
                assert_eq!(json["facts"][1]["name"], "kind_cause");
                assert_eq!(json["facts"][1]["value"], "duplicate-binder");
                assert_eq!(
                    json["labels"].as_array().unwrap().len(),
                    if span == declaration_span { 1 } else { 2 }
                );
                if span != declaration_span {
                    assert_eq!(json["labels"][1]["relationship"], "kind_failure_origin");
                    assert!(compile_evidence_failure(&failure, &[&occurrence]).is_err());
                }
                let error = KindEnvironments::new()
                    .insert_declared(
                        identity,
                        &kind,
                        declaration_span,
                        &mut TypeWorkBudget::with_limit(0),
                    )
                    .unwrap_err();
                assert_eq!(adapt(error, span).reason(), resource_reason);
            }
        }
    }

    #[test]
    fn evidence_failure_messages_preserve_resource_and_occurrence_context() {
        use crate::{
            message::{Catalogue, Locale},
            presentation::{compile_evidence_failure, write_human, write_json},
        };
        let source = SourceFile::new("evidence.ash", "use_value").unwrap();
        let span = source.span(ByteRange::new(0, 9).unwrap()).unwrap();
        for (error, resource_name, explanation) in [
            (
                resource(span),
                Some("constraint-work"),
                "The compiler ran out of resources for interface and constraint processing.",
            ),
            (
                type_resource(span),
                Some("type-work"),
                "The compiler ran out of resources for type checking and type construction.",
            ),
            (
                unavailable(span),
                None,
                "The compiler selected an implementation that is not available in the module containing this use.",
            ),
            (
                unknown(span),
                None,
                "The compiler could not match linked interface evidence to a unique declaration with the expected owner.",
            ),
            (
                invalid_root(span),
                None,
                "The compiler's selected evidence does not establish the interface requirement at this location.",
            ),
        ] {
            let view = compile_evidence_failure(&error, &[&source]).unwrap();
            for locale in [Locale::English, Locale::Bulgarian] {
                let mut output = Vec::new();
                write_human(&mut output, &view, &Catalogue::new(locale).unwrap()).unwrap();
                if locale == Locale::English {
                    let output = String::from_utf8(output).unwrap();
                    assert!(output.contains(explanation));
                    assert!(output.contains("use_value"));
                }
            }
            let mut output = Vec::new();
            write_json(&mut output, &view).unwrap();
            let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
            assert_eq!(json["reason"], error.reason().to_string());
            assert_eq!(json["responsibility"], "compiler");
            assert_eq!(json["facts"][0]["value"], "evidence-validation");
            if let Some(resource) = resource_name {
                assert_eq!(json["facts"][1]["value"], resource);
            }
            assert_eq!(
                json["labels"][0]["relationship"],
                if resource_name.is_some() {
                    "validation_site"
                } else {
                    "evidence_use"
                }
            );
            assert!(compile_evidence_failure(&error, &[]).is_err());
        }
    }

    fn deep_application_type(depth: usize) -> Type {
        let mut ty = Type::Int;
        for _ in 0..depth {
            ty = Type::Application(Box::new(ty), Box::new(Type::Unit));
        }
        ty
    }

    #[test]
    fn linked_catalog_head_clone_discards_a_deep_first_argument_when_the_second_is_one_short() {
        const DEPTH: usize = 16_384;
        const DEEP_ARGUMENT_CELLS: usize = 1 + 2 * DEPTH;
        // Two substitution-vector records precede the retained argument Types.
        const FIRST_ARGUMENT_PREFIX: usize = 2 + DEEP_ARGUMENT_CELLS;
        const EXACT_TYPE_WORK: usize = FIRST_ARGUMENT_PREFIX + 1;

        thread::Builder::new()
            .name("linked-catalog-partial-head-clone-owner".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("linked-head-clone.ash", "Pair")
                    .expect("the linked head fixture should fit");
                let span = source
                    .span(ByteRange::new(0, 4).expect("the fixture range is ordered"))
                    .expect("the fixture span should fit");
                let module = ModuleId::from(source.id());
                let substitution: Box<[EvidenceSubstitution]> = Box::new([
                    EvidenceSubstitution::new(
                        TypeVariableId::resolved(module, 0),
                        deep_application_type(DEPTH),
                    ),
                    EvidenceSubstitution::new(TypeVariableId::resolved(module, 1), Type::Bool),
                ]);

                let mut one_short = TypeWorkBudget::with_limit(FIRST_ARGUMENT_PREFIX);
                let failure = match clone_evidence_substitution_arguments(
                    &substitution,
                    &mut one_short,
                    span,
                ) {
                    Ok(cloned) => {
                        drop(cloned);
                        panic!("the second argument should be one Type cell short")
                    }
                    Err(failure) => failure,
                };
                assert_eq!(
                    failure.reason(),
                    EvidenceValidationReason::TypeResourceExhausted,
                );
                assert_eq!(one_short.used(), FIRST_ARGUMENT_PREFIX);

                let mut exact = TypeWorkBudget::with_limit(EXACT_TYPE_WORK);
                let cloned = clone_evidence_substitution_arguments(&substitution, &mut exact, span)
                    .expect("a fresh exact catalog clone should retain both arguments");
                assert_eq!(cloned.len(), 2);
                assert_eq!(exact.used(), EXACT_TYPE_WORK);
                drop(cloned);
            })
            .expect("the small-stack catalog worker should start")
            .join()
            .expect("partial and complete catalog clones must dismantle iteratively");
    }

    #[test]
    fn linked_application_substitution_discards_a_deep_first_argument_on_second_failure() {
        const DEPTH: usize = 16_384;
        // The common structural engine owns one initial task, one
        // Application record and Unit result per layer, then the Int root.
        const DEEP_SUBSTITUTION_WORK: usize = 2 + 2 * DEPTH;
        // Two application-vector records precede both argument substitutions.
        const FIRST_ARGUMENT_PREFIX: usize = 2 + DEEP_SUBSTITUTION_WORK;
        // The trailing Bool owns one initial task and one rebuilt atom.
        // Two final retained argument slots follow the trailing Bool.
        const EXACT_CONSTRAINT_WORK: usize = FIRST_ARGUMENT_PREFIX + 2 + 2;

        thread::Builder::new()
            .name("linked-application-partial-substitution-owner".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("linked-application-substitution.ash", "Pair")
                    .expect("the linked application fixture should fit");
                let span = source
                    .span(ByteRange::new(0, 4).expect("the fixture range is ordered"))
                    .expect("the fixture span should fit");
                let interface = InterfaceId::new(ModuleId::from(source.id()), 0);
                let application = test_application(
                    interface,
                    Box::new([deep_application_type(DEPTH), Type::Bool]),
                );

                let mut one_short = InterfaceConstraintBudget::with_limit(FIRST_ARGUMENT_PREFIX);
                assert_eq!(
                    substitute_evidence_application(&application, &[], &mut one_short, span)
                        .expect_err("the second argument should fail at its first work cell")
                        .reason(),
                    EvidenceValidationReason::ConstraintResourceExhausted,
                );
                assert_eq!(one_short.used(), FIRST_ARGUMENT_PREFIX);

                let mut exact = InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK);
                let substituted =
                    substitute_evidence_application(&application, &[], &mut exact, span)
                        .expect("a fresh exact substitution should retain both arguments");
                assert_eq!(substituted.arguments().len(), 2);
                assert_eq!(exact.used(), EXACT_CONSTRAINT_WORK);
                drop(substituted);
            })
            .expect("the small-stack substitution worker should start")
            .join()
            .expect("partial and complete substitutions must dismantle iteratively");
    }

    #[test]
    fn fixed_kind_binder_authentication_uses_the_constraint_budget() {
        // One binder record, one Source-Origin cell, and the Arrow with its two
        // Type leaves.
        const EXACT_WORK: usize = 5;
        let source = SourceFile::new("constraint-kind-comparison.ash", "F")
            .expect("the comparison fixture should fit");
        let span = source
            .span(ByteRange::new(0, 1).expect("the binder range should be ordered"))
            .expect("the binder range should belong to the fixture");
        let parameter = || ResolvedTypeVariable {
            id: TypeVariableId::resolved(ModuleId::new(0), 0),
            spelling: "F".to_owned(),
            kind: Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)),
            origin: Origin::Source(span),
        };
        let left = [parameter()];
        let right = [parameter()];

        let mut short = InterfaceConstraintBudget::with_limit(EXACT_WORK - 1);
        assert_eq!(
            same_binders_charged(&left, &right, &mut short, span)
                .map_err(|failure| failure.reason()),
            Err(EvidenceValidationReason::ConstraintResourceExhausted),
        );
        assert_eq!(short.used(), EXACT_WORK - 1);

        let mut exact = InterfaceConstraintBudget::with_limit(EXACT_WORK);
        assert_eq!(
            same_binders_charged(&left, &right, &mut exact, span),
            Ok(true),
        );
        assert_eq!(exact.used(), EXACT_WORK);

        let mismatched = [ResolvedTypeVariable {
            kind: Kind::Type,
            ..parameter()
        }];
        let mut mismatch = InterfaceConstraintBudget::with_limit(3);
        assert_eq!(
            same_binders_charged(&left, &mismatched, &mut mismatch, span),
            Ok(false),
        );
        assert_eq!(mismatch.used(), 3);
    }

    struct ValidationFixture(PathBuf);

    impl ValidationFixture {
        fn create(entry: &str) -> Self {
            loop {
                let id = FIXTURE_IDS.fetch_add(1, Ordering::Relaxed);
                let directory = std::env::temp_dir().join(format!(
                    "ash-evidence-validation-unit-{}-{id}",
                    std::process::id()
                ));
                match fs::create_dir(&directory) {
                    Ok(()) => {
                        let entry_path = directory.join("entry.ash");
                        fs::write(&entry_path, entry)
                            .expect("the validation entry should be writable");
                        return Self(entry_path);
                    }
                    Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                    Err(error) => panic!("the validation fixture should be creatable: {error}"),
                }
            }
        }

        fn write(&self, relative: &str, text: &str) {
            let path = self
                .0
                .parent()
                .expect("the fixture entry should have a parent")
                .join(relative);
            fs::write(path, text).expect("the validation dependency should be writable");
        }

        fn graph(&self) -> ModuleGraph {
            load_module_graph(&self.0, &ModuleRoots::empty())
                .expect("the validation graph should load")
        }
    }

    impl Drop for ValidationFixture {
        fn drop(&mut self) {
            if let Some(directory) = self.0.parent() {
                let _ = fs::remove_dir_all(directory);
            }
        }
    }

    fn check_graph(graph: &ModuleGraph) -> Vec<CheckedModule> {
        let mut checked = Vec::new();
        for module in graph.modules() {
            let dependencies = module
                .dependencies()
                .iter()
                .map(|edge| {
                    let dependency = checked
                        .iter()
                        .find(|checked: &&CheckedModule| checked.module() == edge.target())
                        .expect("dependency order should check the target first");
                    DependencyExports::new(edge, dependency.exports())
                        .expect("the direct edge should authenticate dependency exports")
                })
                .collect::<Vec<_>>();
            let resolved = resolve_module(module, &dependencies)
                .expect("the validation fixture should resolve");
            checked.push(check_module(resolved).expect("the validation fixture should check"));
        }
        checked
    }

    fn deep_constructor_lifecycle_checked_graph() -> (Vec<CheckedModule>, ModuleId) {
        // Keep a deep constructor through publication within the production
        // type-work limit and retain it on the worker's small stack.
        const DEPTH: usize = 16_384;
        const {
            assert!(13 * (2 * DEPTH) + 29 > crate::types::TYPE_WORK_LIMIT);
        }
        let fixture = ValidationFixture::create(concat!(
            "import dependency (Deep, Make)\n",
            "main : Unit -> Unit\nmain value = value\n",
        ));
        fixture.write("dependency.ash", "pub type Deep = Make(Unit)\n");
        let graph = fixture.graph();
        let defining = graph
            .modules()
            .iter()
            .find(|module| {
                std::path::Path::new(module.source().display_path()).file_name()
                    == Some("dependency.ash".as_ref())
            })
            .unwrap()
            .id();
        assert_ne!(defining, graph.entry());
        let mut checked = Vec::new();
        let mut constructor = None;
        let mut mutations = 0;

        for module in graph.modules() {
            let dependencies = module
                .dependencies()
                .iter()
                .map(|edge| {
                    let dependency = checked
                        .iter()
                        .find(|checked: &&CheckedModule| checked.module() == edge.target())
                        .expect("the deep constructor dependency should check first");
                    DependencyExports::new(edge, dependency.exports())
                        .expect("the deep constructor edge should match its summary")
                })
                .collect::<Vec<_>>();
            let mut resolved = resolve_module(module, &dependencies)
                .expect("the deep constructor lifecycle module should resolve");
            if module.id() == defining {
                let owner = resolved
                    .registry()
                    .nominals()
                    .iter()
                    .find(|nominal| nominal.id.module() == defining && nominal.spelling == "Deep")
                    .unwrap();
                let candidates = resolved
                    .registry()
                    .constructors()
                    .iter()
                    .filter(|constructor| {
                        constructor.owner == owner.id && constructor.spelling == "Make"
                    })
                    .collect::<Vec<_>>();
                let [candidate] = candidates.as_slice() else {
                    panic!("unique defining Deep.Make")
                };
                let id = candidate.id;
                assert!(
                    resolved
                        .imported_facts()
                        .effects()
                        .any(|effect| effect.id.module().is_builtin_region())
                );
                mutations += 1;
                let mut payload = Type::Unit;
                for _ in 0..DEPTH {
                    payload = Type::Function(Box::new(Type::Int), Box::new(payload));
                }
                assert!(resolved.replace_local_constructor_payload_for_test(id, payload));
                let mut retained = resolved
                    .registry()
                    .constructors()
                    .iter()
                    .find(|candidate| candidate.id == id)
                    .unwrap()
                    .payload
                    .as_ref()
                    .unwrap();
                for _ in 0..DEPTH {
                    let Type::Function(domain, result) = retained else {
                        panic!("pure constructor payload layer")
                    };
                    assert_eq!(domain.as_ref(), &Type::Int);
                    retained = result;
                }
                assert_eq!(retained, &Type::Unit);
                constructor = Some(id);
            } else if module.id() == graph.entry() {
                let id = constructor.expect("the defining constructor should precede the entry");
                let exported = checked
                    .iter()
                    .find(|checked: &&CheckedModule| checked.module() == defining)
                    .unwrap()
                    .exports()
                    .constructor("Make")
                    .expect("the checked dependency should publish Make's physical scheme");
                let imported = resolved
                    .imported_facts()
                    .constructor(id)
                    .expect("the targeted entry should retain Make's physical scheme");
                assert_eq!(imported.scheme.type_parameters.len(), 0);
                assert_eq!(imported.scheme.requirements.len(), 0);
                let mut type_work = TypeWorkBudget::with_limit(0);
                let mut constraint_work = InterfaceConstraintBudget::default();
                assert_eq!(
                    same_imported_constructor_fact_with_budget(
                        imported,
                        exported,
                        &mut type_work,
                        &mut constraint_work,
                    ),
                    Ok(true),
                );
                assert_eq!(type_work.used(), 0);
            }
            let mut type_work = TypeWorkBudget::default();
            checked.push(
                crate::elaborate::check_module_with_budget(
                    resolved,
                    &mut type_work,
                    &mut crate::pattern::UsefulnessBudget::default(),
                    &mut InterfaceConstraintBudget::default(),
                )
                .expect("checking should consume the imported physical scheme iteratively"),
            );
            if module.id() == defining {
                assert!(type_work.used() > 2 * DEPTH);
                assert!(type_work.used() < crate::types::TYPE_WORK_LIMIT);
            }
        }
        assert_eq!(mutations, 1);
        assert_eq!(checked.len(), 4);
        (checked, graph.entry())
    }

    #[test]
    fn deep_constructor_scheme_crosses_check_and_link_then_is_disposed_before_core() {
        // Four-module wrapper20, registry index44, three occupied map slots,
        // and group lookups2+3+4+5. The final lookup is charged atomically.
        const LINK_CONSTRAINT_WORK: usize = 20 + 44 + 3 + 2 + 3 + 4 + 5;
        const ONE_SHORT_PREFIX: usize = LINK_CONSTRAINT_WORK - 5;
        std::thread::Builder::new()
            .name("deep-constructor-check-link-lifecycle".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let (measured_modules, measured_entry) = deep_constructor_lifecycle_checked_graph();
                let mut measured = InterfaceConstraintBudget::with_limit(usize::MAX);
                let measured_program =
                    link_modules_with_budget(measured_modules, measured_entry, &mut measured)
                        .expect("the deep constructor registry should link");
                let exact_work = measured.used();
                assert_eq!(exact_work, LINK_CONSTRAINT_WORK);
                drop(
                    validate_interface_evidence(measured_program)
                        .expect("the minimal linked program should publish before Core"),
                );

                let (short_modules, short_entry) = deep_constructor_lifecycle_checked_graph();
                let mut one_short = InterfaceConstraintBudget::with_limit(exact_work - 1);
                assert!(matches!(
                    link_modules_with_budget(short_modules, short_entry, &mut one_short),
                    Err(crate::elaborate::TypeError::Internal(
                        crate::elaborate::ElaborationFailure::ConstraintResourceExhausted
                    )),
                ));
                assert_eq!(one_short.used(), ONE_SHORT_PREFIX);

                let (exact_modules, exact_entry) = deep_constructor_lifecycle_checked_graph();
                let mut exact = InterfaceConstraintBudget::with_limit(exact_work);
                let program = link_modules_with_budget(exact_modules, exact_entry, &mut exact)
                    .expect("the exact late-link boundary should publish the program");
                assert_eq!(exact.used(), exact_work);
                drop(
                    validate_interface_evidence(program)
                        .expect("the exact deep linked program should validate before Core"),
                );
            })
            .expect("the deep check/link lifecycle worker should spawn")
            .join()
            .expect("accepted and rejected deep lifecycle owners must tear down iteratively");
    }

    fn local_program() -> ResolvedModuleProgram {
        let fixture = ValidationFixture::create(concat!(
            "interface Equal<A> {\nequal : (A, A) -> Bool\n}\n\n",
            "impl Equal<Int> {\nequal (left, right) = left == right\n}\n\n",
            "main : Unit -> Bool\nmain () = equal((1, 1))\n",
        ));
        let graph = fixture.graph();
        link_modules(check_graph(&graph), graph.entry()).expect("the local fixture should link")
    }

    fn entry_group(program: &ResolvedModuleProgram) -> &crate::resolved::ResolvedModuleGroup {
        program
            .groups()
            .iter()
            .find(|group| group.module() == program.entry())
            .expect("the checked entry group")
    }

    fn entry_catalog(program: &ResolvedModuleProgram) -> &MethodEvidenceCatalog {
        entry_group(program)
            .local_lowering()
            .and_then(|lowering| lowering.catalog())
            .map(AsRef::as_ref)
            .expect("the checked entry retains its defining catalogue")
    }

    fn entry_program(source: &str) -> ResolvedModuleProgram {
        let fixture = ValidationFixture::create(source);
        let graph = fixture.graph();
        link_modules(check_graph(&graph), graph.entry()).expect("the entry fixture should link")
    }

    fn published_resource_program(implementation_only: bool) -> ResolvedModuleProgram {
        let (owner, entry) = if implementation_only {
            (
                "import @builtin.cell as Cell\npub interface Value<A> {\nvalue : A -> Int\n}\npub impl Value<Unit> {\nvalue ignored = resource cell<R> c = 42 {\nCell.read c\n}\n}\n",
                "import owner (value, impl Value)\nmain : Unit -> Int\nmain () = value ()\n",
            )
        } else {
            (
                "import @builtin.cell as Cell\npub readCell : Unit -> Int\nreadCell () = resource cell<R> c = 42 {\nCell.read c\n}\n",
                "import owner (readCell)\nmain : Unit -> Int\nmain () = readCell ()\n",
            )
        };
        let fixture = ValidationFixture::create(entry);
        fixture.write("owner.ash", owner);
        let graph = fixture.graph();
        let checked = check_graph(&graph);
        let defining = checked
            .iter()
            .find(|module| {
                module
                    .schemes()
                    .iter()
                    .any(|scheme| scheme.spelling == "readCell")
                    || !module.implementation_facts().is_empty()
            })
            .unwrap();
        assert_eq!(defining.schemes().len(), usize::from(!implementation_only));
        assert_eq!(
            defining.implementation_facts().len(),
            usize::from(implementation_only)
        );
        link_modules(checked, graph.entry()).unwrap()
    }

    #[test]
    fn published_resource_linked_owners_have_exact_atomic_validation_boundaries() {
        for implementation_only in [false, true] {
            let run = |constraint_limit, type_limit| {
                let mut constraints = InterfaceConstraintBudget::with_limit(constraint_limit);
                let mut types = TypeWorkBudget::with_limit(type_limit);
                let result = validate_interface_evidence_with_budget(
                    published_resource_program(implementation_only),
                    &mut constraints,
                    &mut types,
                );
                (result, constraints.used(), types.used())
            };
            let (measured, constraints, types) = run(usize::MAX, usize::MAX);
            let validated = measured.unwrap();
            let owners: Vec<_> = validated
                .groups()
                .iter()
                .filter_map(|group| {
                    group
                        .local_lowering()
                        .and_then(|lowering| lowering.catalog())
                })
                .flat_map(|catalog| catalog.lexical_owners())
                .filter_map(|owner| {
                    owner
                        .resource
                        .as_ref()
                        .and_then(crate::core::dialect::MethodEvidenceResourceOwner::builtin)
                        .map(|acquisition| (owner, acquisition))
                })
                .collect();
            assert_eq!(
                owners.len(),
                2,
                "one acquisition owns both generated methods"
            );
            assert_eq!(owners[0].1.identity, owners[1].1.identity);
            assert_eq!(owners[0].1.provider, owners[1].1.provider);
            assert_eq!(owners[0].0.method.declaration(), 0);
            assert_eq!(owners[1].0.method.declaration(), 1);
            // The defining catalogue retains the same acquisition identity
            // for both methods across linked composition.
            assert_eq!(
                run(constraints - 1, types).0.unwrap_err().reason(),
                EvidenceValidationReason::ConstraintResourceExhausted
            );
            assert_eq!(
                run(constraints, types - 1).0.unwrap_err().reason(),
                EvidenceValidationReason::TypeResourceExhausted
            );
            for _ in 0..2 {
                let (retry, used_constraints, used_types) = run(constraints, types);
                retry.unwrap();
                assert_eq!((used_constraints, used_types), (constraints, types));
            }
        }
    }

    #[test]
    fn defining_catalog_retains_mixed_namespace_methods() {
        let program = published_resource_program(true);
        let catalog = program
            .groups()
            .iter()
            .find(|group| !group.implementation_facts().is_empty())
            .and_then(|group| group.local_lowering())
            .and_then(|lowering| lowering.catalog())
            .expect("the defining module retains its catalogue");
        assert!(
            catalog
                .methods()
                .windows(2)
                .all(|pair| pair[0].id < pair[1].id)
        );
        assert_eq!(catalog.methods().len(), 3);
    }

    #[test]
    fn cell_linked_headers_authenticate_owner_and_preceding_body_scopes() {
        // No resource CheckedModule is constructed: only the normal builtin
        // group and an internally typed result feed this owning header pass.
        let program = crate::elaborate::cell_resource_linked_header_fixture_for_test();
        let registry =
            LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                .unwrap();
        let ResolvedExprKind::Resource(resource_scope) = &program.result().kind else {
            panic!("resource")
        };
        let run = |root: &ResolvedExpr, limit| {
            let mut types = TypeWorkBudget::default();
            let mut constraints = InterfaceConstraintBudget::with_limit(limit);
            let mut environments =
                build_linked_kind_environments(program.registry(), &mut types, root.span).unwrap();
            let result = validate_expression(
                &program,
                &registry,
                &program.groups()[0],
                EvidenceScope {
                    local_scopes: &[],
                    lexical_sources: &[],
                    lexical_head: None,
                    owner: None,
                    variables: &[],
                },
                root,
                &mut environments,
                &mut constraints,
                &mut types,
                true,
            );
            (result, constraints.used())
        };
        let (positive, work) = run(program.result(), usize::MAX);
        positive.expect("real resource body owns its generated provider and R");
        assert_eq!(
            run(program.result(), work - 1).0.unwrap_err().reason(),
            EvidenceValidationReason::ConstraintResourceExhausted
        );
        for _ in 0..2 {
            run(program.result(), work).0.expect("exact header retry");
        }
        run(&resource_scope.initializer, usize::MAX)
            .0
            .expect("initializer has preceding scope");
        assert!(
            run(&resource_scope.body, usize::MAX).0.is_err(),
            "detached provider body cannot mint authority"
        );
        for moved in [true, false] {
            let mut changed = program.result().clone();
            let ResolvedExprKind::Resource(changed_resource) = &mut changed.kind else {
                unreachable!()
            };
            if moved {
                crate::resolved::discard_resolved_expression_iteratively(std::mem::replace(
                    &mut *changed_resource.initializer,
                    (*changed_resource.body).clone(),
                ));
            } else {
                changed_resource.acquisition.provider =
                    crate::interface::LexicalEvidenceId::new(program.entry(), u32::MAX);
            }
            let result = run(&changed, usize::MAX).0;
            crate::resolved::discard_resolved_expression_iteratively(changed);
            assert!(
                result.is_err(),
                "moved initializer or detached owner must reject"
            );
        }
        let ResolvedExprKind::Block(body) = &resource_scope.body.kind else {
            panic!("provider wrapper")
        };
        let ResolvedLocalDeclaration::Evidence(source) = &body.declarations[0] else {
            panic!("provider")
        };
        for variables in [&[][..], &[resource_scope.identity.id][..]] {
            let result = authenticate_lexical_header(
                &program,
                &registry,
                source,
                EvidenceScope {
                    local_scopes: &[],
                    lexical_sources: &[],
                    lexical_head: None,
                    owner: None,
                    variables,
                },
                &[(LinkedLocalScope::Resource(resource_scope), None)],
                Some(0),
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            );
            assert_eq!(
                result.is_ok(),
                !variables.is_empty(),
                "owner does not implicitly add R to preceding scope"
            );
        }
    }

    fn unused_lexical_program() -> ResolvedModuleProgram {
        entry_program(concat!(
            "interface Choose<T> {\nchoose<A> : T -> A -> A\nkeep<B> : T -> B -> B\n}\n",
            "main : Unit -> Int\nmain () = {\nnewtype Token = Token(Unit)\n",
            "with Choose<Token> {\nchoose ignored value = value\nkeep ignored value = value\n}\n42\n}\n",
        ))
    }

    #[test]
    fn intact_lexical_method_groups_may_remain_in_either_source_order() {
        let program = entry_program(concat!(
            "interface Choose<T> {\nchoose<A> : T -> A -> A\nkeep<B> : T -> B -> B\n}\n",
            "main : Unit -> Int\nmain () = {\nnewtype Token = Token(Unit)\n",
            "with Choose<Token> {\nkeep ignored value = value\nchoose ignored value = value\n}\n42\n}\n",
        ));
        validate_interface_evidence(program)
            .expect("source group order does not change each group's canonical method slot");
    }

    fn first_lexical_source(
        program: &ResolvedModuleProgram,
    ) -> &crate::resolved::ResolvedLexicalEvidence {
        entry_group(program)
            .definitions()
            .iter()
            .find_map(|definition| {
                let ResolvedDefinitionKind::Equational(global) = definition.kind() else {
                    return None;
                };
                let ResolvedExprKind::Block(block) = &global.equations.first()?.body.kind else {
                    return None;
                };
                block
                    .declarations
                    .iter()
                    .find_map(|declaration| match declaration {
                        ResolvedLocalDeclaration::Evidence(source) => Some(source),
                        _ => None,
                    })
            })
            .expect("fixture lexical source")
    }

    fn lexical_resource_program() -> ResolvedModuleProgram {
        entry_program(concat!(
            "interface Read<A, B> where A -> B {\nread : A -> B\nagain : A -> B\n}\n",
            "interface Unused<C> {\nfirst : C -> C\nsecond : C -> C\nthird : C -> C\n}\n",
            "main : Unit -> Int\nmain () = {\nnewtype N = N(Int)\n",
            "with Read<N, Int> {\nread ignored = 42\nagain ignored = 42\n}\n42\n}\n",
        ))
    }

    #[test]
    fn lexical_node_method_and_equation_scans_have_exact_retry_boundaries() {
        let program = lexical_resource_program();
        let group = entry_group(&program);
        let source = first_lexical_source(&program);
        let application = &source.checked.get().expect("checked source").application;
        let methods = source
            .method_groups
            .iter()
            .map(|group| group.method.expect("method"))
            .collect::<Vec<_>>();
        let mut builder = EvidenceSelectionBuilder::new();
        let root = builder
            .push_lexical(
                source.id,
                &methods,
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("plan node");
        let selection = builder.finish(root, application.clone()).expect("plan");
        let sources = [(
            LinkedLexicalSource::Declared(source, OriginalLexicalContext::NONE),
            None,
        )];
        let scope = EvidenceScope {
            local_scopes: &[],
            owner: None,
            variables: &[],
            lexical_sources: &sources,
            lexical_head: Some(0),
        };
        let registry =
            LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                .expect("registry");
        // One visited node, one source link, four application comparison cells,
        // M=2 ordered method cells, then G=2 * (M membership + insert + E=1).
        const WORK: usize = 1 + 1 + 4 + 2 + 2 * (2 + 1 + 1);
        for limit in [WORK - 1, WORK, WORK] {
            let mut budget = InterfaceConstraintBudget::with_limit(limit);
            let result = validate_evidence_node(
                &program,
                &registry,
                group,
                &selection,
                root,
                application,
                None,
                scope,
                &KindEnvironments::new(),
                &mut HashSet::new(),
                &mut PendingGoals::default(),
                &mut budget,
                &mut TypeWorkBudget::default(),
                source.span,
            );
            if limit < WORK {
                assert_eq!(result, Err(resource(source.span)));
            } else {
                result.expect("the exact complete lexical node should authenticate");
                assert_eq!(budget.used(), WORK);
            }
        }
    }

    #[test]
    fn lexical_block_scheduling_charges_its_shape_scan_before_retention() {
        let program = lexical_resource_program();
        let ResolvedDefinitionKind::Equational(global) =
            entry_group(&program).definitions()[0].kind()
        else {
            panic!("global");
        };
        let ResolvedExprKind::Block(block) = &global.equations[0].body.kind else {
            panic!("block");
        };
        // Two declaration visits and two method-group counts, one source pair,
        // then two equation slots and the result, each with one scope-head cell.
        const WORK: usize = 2 + 2 + 2 + 3 * 2;
        for limit in [WORK - 1, WORK, WORK] {
            let mut budget = InterfaceConstraintBudget::with_limit(limit);
            let mut pending = Vec::new();
            let mut heads = Vec::new();
            let mut sources = Vec::new();
            let result = schedule_lexical_block(
                &mut pending,
                &mut heads,
                &mut sources,
                &mut Vec::new(),
                (None, None),
                block,
                &mut budget,
                false,
                OriginalLexicalContext::NONE,
                None,
            );
            if limit < WORK {
                assert_eq!(
                    result.expect_err("the shape scan must be charged").reason(),
                    EvidenceValidationReason::ConstraintResourceExhausted
                );
            } else {
                result.expect("the exact lexical block should schedule");
                assert_eq!(budget.used(), WORK);
                assert_eq!(sources.len(), 1);
                assert_eq!(pending.len(), 3);
                assert_eq!(heads, [(Some(0), None), (None, None), (None, None)]);
            }
        }
    }

    #[test]
    fn lexical_priority_is_authenticated_at_root_and_recursive_complete_goals() {
        let mut accepted_tampering = Vec::new();
        for same_dependent in [true, false] {
            let program = entry_program(&format!(
                concat!(
                    "type Wrap<A> = Wrap(A)\n",
                    "interface Read<A, B> where A -> B {{\nread : A -> B\n}}\n",
                    "interface Need<A> {{\nneed : A -> Int\n}}\n",
                    "impl<A> Read<Wrap<A>, Int> {{\nread ignored = 0\n}}\n",
                    "impl<A> Need<Wrap<Wrap<A>>> where Read<Wrap<A>, Int> {{\nneed (Wrap(value)) = read(value)\n}}\n",
                    "main : Unit -> Int\nmain () = {{\nnewtype Token = Token(Unit)\n",
                    "with Read<Wrap<Token>, {}> {{\nread ignored = {}\n}}\n42\n}}\n",
                ),
                if same_dependent { "Int" } else { "Bool" },
                if same_dependent { "42" } else { "false" }
            ));
            let group = entry_group(&program);
            let source = first_lexical_source(&program);
            let checked = source.checked.get().expect("checked source");
            let Type::Application(_, token) =
                test_type_argument(&checked.application.arguments()[0])
            else {
                panic!("Wrap<Token>");
            };
            let read = &group.implementation_facts()[0];
            let need = &group.implementation_facts()[1];
            let sources = [(
                LinkedLexicalSource::Declared(source, OriginalLexicalContext::NONE),
                None,
            )];
            let scope = EvidenceScope {
                local_scopes: &[],
                owner: None,
                variables: &[],
                lexical_sources: &sources,
                lexical_head: Some(0),
            };
            let registry =
                LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                    .expect("fixture registry");
            for nested in [false, true] {
                let mut builder = EvidenceSelectionBuilder::new();
                let child = builder
                    .push_implementation(
                        read.id,
                        single_substitution(read.head_parameters[0].id, token),
                        &[],
                        &[read.methods[0].id],
                        &mut InterfaceConstraintBudget::default(),
                    )
                    .expect("concrete child");
                let root = if nested {
                    builder
                        .push_implementation(
                            need.id,
                            single_substitution(need.head_parameters[0].id, token),
                            &[child],
                            &[need.methods[0].id],
                            &mut InterfaceConstraintBudget::default(),
                        )
                        .expect("outer prerequisite")
                } else {
                    child
                };
                let arguments = if nested {
                    vec![instantiate_single_parameter_head(need, token)]
                } else {
                    vec![
                        test_type_argument(&checked.application.arguments()[0]).clone(),
                        Type::Int,
                    ]
                };
                let application = test_application(
                    if nested {
                        need.interface()
                    } else {
                        read.interface()
                    },
                    arguments.into_boxed_slice(),
                );
                let selection = builder
                    .finish(root, application.clone())
                    .expect("well-formed plan");
                let result = validate_selection_in_scope(
                    &program,
                    &registry,
                    group,
                    &selection,
                    &application,
                    scope,
                    &mut InterfaceConstraintBudget::default(),
                    source.span,
                );
                if same_dependent {
                    if result.is_ok() {
                        accepted_tampering.push(nested);
                    }
                } else {
                    result.expect("complete-goal selection permits a different dependent argument; a pending root still conflicts earlier during improvement");
                }
            }
        }
        assert!(
            accepted_tampering.is_empty(),
            "accepted concrete shadowing (nested): {accepted_tampering:?}"
        );
    }

    #[test]
    fn lexical_nodes_cannot_replace_abstract_or_exact_current_evidence() {
        // These lower-level synthetic scopes isolate selection authentication.
        // A source-reachable declaration cannot introduce these enclosing rigid keys.
        let template = unused_lexical_program();
        for current in [false, true] {
            let program = abstract_priority_program();
            let group = entry_group(&program);
            let fact = &group.implementation_facts()[0];
            let global = &group.schemes()[0];
            let (application, owner, variables) = if current {
                (
                    fact.application(),
                    RequirementOwner::Impl(fact.id),
                    fact.head_parameters
                        .iter()
                        .map(|parameter| parameter.id)
                        .collect::<Vec<_>>(),
                )
            } else {
                (
                    global.scheme.requirements[0].application(),
                    RequirementOwner::Global(global.binder),
                    global
                        .scheme
                        .type_parameters
                        .iter()
                        .map(|parameter| parameter.0)
                        .collect::<Vec<_>>(),
                )
            };
            let interface = &group.interface_facts()[0];
            let mut source = first_lexical_source(&template).clone();
            source.id = crate::interface::LexicalEvidenceId::new(group.module(), 0);
            source.application.interface.id = application.interface();
            source.application.arguments = application
                .arguments()
                .iter()
                .map(|argument| {
                    let mut resolved = source.application.arguments[0].clone();
                    crate::types::discard_kinded_argument_iteratively(std::mem::replace(
                        &mut resolved.ty,
                        argument.clone(),
                    ));
                    resolved
                })
                .collect();
            source.method_groups = vec![source.method_groups[0].clone()].into_boxed_slice();
            let method = &mut source.method_groups[0];
            method.method = Some(interface.methods[0].id);
            method.binder.id = BinderId::resolved(group.module(), u32::MAX - 1);
            for equation in &mut method.equations {
                equation.name.binder = method.binder.id;
            }
            let sources = [(
                LinkedLexicalSource::Declared(&source, OriginalLexicalContext::NONE),
                None,
            )];
            let mut scope = EvidenceScope {
                local_scopes: &[],
                owner: None,
                variables: &variables,
                lexical_sources: &sources,
                lexical_head: Some(0),
            };
            let registry =
                LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                    .expect("fixture registry");
            let mut builder = EvidenceSelectionBuilder::new();
            let root = builder
                .push_lexical(
                    source.id,
                    &[interface.methods[0].id],
                    &mut InterfaceConstraintBudget::default(),
                )
                .expect("lexical node");
            let selection = builder
                .finish(root, application.clone())
                .expect("complete lexical plan");
            validate_selection_in_scope(
                &program,
                &registry,
                group,
                &selection,
                application,
                scope,
                &mut InterfaceConstraintBudget::default(),
                source.span,
            )
            .expect("the isolated lexical node has no higher authority");
            scope.owner = Some(owner);
            assert_eq!(
                validate_selection_in_scope(
                    &program,
                    &registry,
                    group,
                    &selection,
                    application,
                    scope,
                    &mut InterfaceConstraintBudget::default(),
                    source.span
                )
                .expect_err("higher authority cannot be replaced by a lexical node")
                .reason(),
                EvidenceValidationReason::InvalidEvidenceRoot
            );
            let higher = if current {
                let mut builder = EvidenceSelectionBuilder::new();
                let parameter = fact.head_parameters[0].id;
                let root = builder
                    .push_implementation(
                        fact.id,
                        single_substitution(parameter, &Type::Variable(parameter)),
                        &[],
                        &[fact.methods[0].id],
                        &mut InterfaceConstraintBudget::default(),
                    )
                    .expect("identity-current node");
                builder
                    .finish(root, application.clone())
                    .expect("identity-current plan")
            } else {
                abstract_selection_for_application(
                    global.scheme.requirements[0].id,
                    interface,
                    application.arguments().to_vec().into_boxed_slice(),
                )
            };
            validate_selection_in_scope(
                &program,
                &registry,
                group,
                &higher,
                application,
                scope,
                &mut InterfaceConstraintBudget::default(),
                source.span,
            )
            .expect(
                "the actual higher-priority producer remains valid with lexical evidence present",
            );
        }
    }

    #[test]
    fn lexical_selection_requires_the_complete_canonical_method_order() {
        let program = unused_lexical_program();
        let group = entry_group(&program);
        let source = first_lexical_source(&program);
        let application = &source.checked.get().expect("checked source").application;
        let methods = &group.interface_facts()[0].methods;
        let sources = [(
            LinkedLexicalSource::Declared(source, OriginalLexicalContext::NONE),
            None,
        )];
        let scope = EvidenceScope {
            local_scopes: &[],
            owner: None,
            variables: &[],
            lexical_sources: &sources,
            lexical_head: Some(0),
        };
        let registry =
            LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                .expect("fixture registry");
        for supplied in [
            vec![methods[0].id],
            vec![methods[1].id, methods[0].id],
            vec![methods[0].id, methods[0].id],
            vec![methods[0].id, methods[1].id, methods[1].id],
        ] {
            let mut builder = EvidenceSelectionBuilder::new();
            let root = builder
                .push_lexical(
                    source.id,
                    &supplied,
                    &mut InterfaceConstraintBudget::default(),
                )
                .expect("representable method list");
            let selection = builder
                .finish(root, application.clone())
                .expect("complete goal");
            assert_eq!(
                validate_selection_in_scope(
                    &program,
                    &registry,
                    group,
                    &selection,
                    application,
                    scope,
                    &mut InterfaceConstraintBudget::default(),
                    source.span
                )
                .expect_err("method slots are complete and interface-ordered")
                .reason(),
                EvidenceValidationReason::InvalidEvidenceRoot
            );
        }
    }

    #[test]
    fn lexical_header_parameter_detection_has_an_exact_retry_boundary() {
        let program = entry_program(concat!(
            "type Box<A> = Box(A)\ninterface Keep<A> {\nkeep : A -> A\n}\n",
            "interface Read<N, A> where N -> A {\nread : N -> Int\n}\n",
            "impl<A> Keep<Box<A>> {\nkeep value = {\nnewtype N = N(Unit)\n",
            "with Read<N, A> {\nread ignored = 0\n}\nvalue\n}\n}\n",
            "main : Unit -> Int\nmain () = 42\n",
        ));
        let catalog = entry_catalog(&program);
        let method = &entry_group(&program).implementation_facts()[0].methods[0];
        const EXACT: usize = 1 + (2 + 1) + (3 + 1) + 1;
        for limit in [EXACT - 1, EXACT, EXACT] {
            let mut budget = InterfaceConstraintBudget::with_limit(limit);
            let result = lexical_header_captures_method_parameter(
                catalog.lexical_owners(),
                method,
                &mut budget,
            );
            if limit < EXACT {
                assert_eq!(
                    result.expect_err("one-short dependency scan").reason(),
                    EvidenceValidationReason::ConstraintResourceExhausted
                );
            } else {
                assert!(result.expect("exact dependency scan"));
                assert_eq!(budget.used(), EXACT);
            }
        }
        let mut empty = InterfaceConstraintBudget::with_limit(0);
        assert!(!lexical_header_captures_method_parameter(&[], method, &mut empty).unwrap());
        assert_eq!(empty.used(), 0);
    }

    #[test]
    fn captured_method_parameter_detection_has_an_exact_retry_boundary() {
        let program = entry_program(concat!(
            "type Box<A> = Box(A)\n",
            "interface Keep<A> {\nkeep : A -> A\n}\n",
            "impl<A> Keep<Box<A>> {\nkeep value = {\nnewtype Local = Local(A)\nvalue\n}\n}\n",
            "main : Unit -> Int\nmain () = 42\n",
        ));
        let method = &entry_group(&program).implementation_facts()[0].methods[0];
        const EXACT: usize = 5;
        let mut short = InterfaceConstraintBudget::with_limit(EXACT - 1);
        assert_eq!(
            local_representation_captures_method_parameter(program.registry(), method, &mut short)
                .expect_err("the capture lookup must charge before completion")
                .reason(),
            EvidenceValidationReason::ConstraintResourceExhausted
        );
        for _ in 0..2 {
            let mut exact = InterfaceConstraintBudget::with_limit(EXACT);
            assert!(
                local_representation_captures_method_parameter(
                    program.registry(),
                    method,
                    &mut exact
                )
                .expect("the exact lookup should fit")
            );
            assert_eq!(exact.used(), EXACT);
        }
    }

    fn linked_determined_generic_decrease_program() -> ResolvedModuleProgram {
        entry_program(concat!(
            "type List<A> =\n",
            "Nil\n",
            "| Cons(A, List<A>)\n",
            "interface Relation<A, B> where A -> B {\n",
            "relate : A -> Int\n",
            "}\n",
            "impl<A> Relation<List<A>, A> where Relation<A, List<A>> {\n",
            "relate value = 0\n",
            "}\n",
            "main : Unit -> Unit\n",
            "main () = ()\n",
        ))
    }

    fn polymorphic_method_program() -> ResolvedModuleProgram {
        entry_program(concat!(
            "type Wrap<A> = Wrap(A)\n\n",
            "interface Use<I> {\n",
            "use<F : Type -> Type, A, B> : (F<A>, B, I) -> I\n",
            "}\n\n",
            "impl<H : Type -> Type> Use<H<Int>> {\n",
            "use (ignored, also_ignored, owner) = owner\n",
            "}\n\n",
            "relay<I, F : Type -> Type, A, B> : (F<A>, B, I) -> I where Use<I>\n",
            "relay pair = use(pair)\n\n",
            "main : Unit -> Wrap<Int>\n",
            "main () = use((Wrap(true), 42, Wrap(1)))\n",
        ))
    }

    fn concrete_monomorphic_source_program() -> ResolvedModuleProgram {
        entry_program(concat!(
            "type Wrap<A> = Wrap(A)\n\n",
            "interface Base<I> {\nbase : I -> I\n}\n\n",
            "interface Convert<I> {\nconvert<X> : (I, X) -> I\n}\n\n",
            "impl Base<Int> {\nbase value = value\n}\n\n",
            "impl<A> Convert<Wrap<A>> where Base<A> {\n",
            "convert (Wrap(value), ignored) = Wrap(base(value))\n",
            "}\n\n",
            "main : Unit -> Wrap<Int>\n",
            "main () = convert((Wrap(42), true))\n",
        ))
    }

    fn widened_abstract_method_source_program() -> ResolvedModuleProgram {
        entry_program(concat!(
            "interface Use<I> {\n",
            "first<X> : (I, X) -> I\n",
            "second<Y> : (I, Y) -> I\n",
            "}\n\n",
            "relay<I> : I -> I where Use<I>\n",
            "relay value = first((second((value, true)), 42))\n\n",
            "main : Unit -> Unit\n",
            "main value = value\n",
        ))
    }

    #[test]
    fn authenticates_polymorphic_method_occurrence_arguments_before_core() {
        validate_interface_evidence(polymorphic_method_program())
            .expect("canonical method schemes and occurrence arguments should authenticate");
    }

    #[test]
    fn defining_method_catalog_retains_checked_domains() {
        let program = polymorphic_method_program();
        let catalog = entry_catalog(&program);
        assert!(!catalog.expectations().is_empty());
        assert_eq!(
            catalog
                .domains()
                .iter()
                .map(|domain| domain.source_parameters.len())
                .sum::<usize>(),
            4
        );
        let mut retained_kinds = TypeWorkBudget::unbounded();
        for domain in catalog.domains() {
            for (_, kind) in &domain.source_parameters {
                crate::types::charge_kind_nodes(kind, &mut retained_kinds).unwrap();
            }
        }
        assert_eq!(retained_kinds.used(), 6);
    }

    #[test]
    fn lexical_owners_are_retained_in_the_defining_catalog() {
        let program = lexical_resource_program();
        assert_eq!(entry_catalog(&program).lexical_owners().len(), 2);
    }

    #[test]
    fn lexical_public_validation_rejects_one_short_without_a_partial_result() {
        let mut measured_constraints = InterfaceConstraintBudget::default();
        let mut measured_types = TypeWorkBudget::default();
        validate_interface_evidence_with_budget(
            lexical_resource_program(),
            &mut measured_constraints,
            &mut measured_types,
        )
        .expect("measure public validation");
        let constraints = measured_constraints.used();
        let types = measured_types.used();
        for (constraint_limit, type_limit, reason) in [
            (
                constraints - 1,
                types,
                EvidenceValidationReason::ConstraintResourceExhausted,
            ),
            (
                constraints,
                types - 1,
                EvidenceValidationReason::TypeResourceExhausted,
            ),
        ] {
            let result = validate_interface_evidence_with_budget(
                lexical_resource_program(),
                &mut InterfaceConstraintBudget::with_limit(constraint_limit),
                &mut TypeWorkBudget::with_limit(type_limit),
            );
            assert_eq!(
                result
                    .expect_err("a failed pass cannot publish a validated program")
                    .reason(),
                reason
            );
        }
        for _ in 0..2 {
            let mut exact_constraints = InterfaceConstraintBudget::with_limit(constraints);
            let mut exact_types = TypeWorkBudget::with_limit(types);
            validate_interface_evidence_with_budget(
                lexical_resource_program(),
                &mut exact_constraints,
                &mut exact_types,
            )
            .expect("a fresh exact pass should authenticate");
            assert_eq!(
                (exact_constraints.used(), exact_types.used()),
                (constraints, types)
            );
        }
    }

    #[test]
    fn lexical_plan_scan_charges_each_inspection_before_work_and_retries_exactly() {
        let program = generic_program();
        let selection = nested_generic_selection(&program, &Type::Int, Type::Int);
        let span = program.result().span;
        assert_eq!(selection.node_count(), 2);
        LEXICAL_PLAN_INSPECTIONS.with(|count| count.set(0));
        let mut short = InterfaceConstraintBudget::with_limit(1);
        assert_eq!(
            selection_has_lexical(&selection, &mut short, span)
                .expect_err("the second node must be charged before inspection")
                .reason(),
            EvidenceValidationReason::ConstraintResourceExhausted,
        );
        assert_eq!(LEXICAL_PLAN_INSPECTIONS.with(std::cell::Cell::get), 1);
        for _ in 0..2 {
            LEXICAL_PLAN_INSPECTIONS.with(|count| count.set(0));
            let mut exact = InterfaceConstraintBudget::with_limit(2);
            assert!(
                !selection_has_lexical(&selection, &mut exact, span)
                    .expect("both concrete nodes fit exactly")
            );
            assert_eq!(exact.used(), 2);
            assert_eq!(LEXICAL_PLAN_INSPECTIONS.with(std::cell::Cell::get), 2);
        }
    }

    #[test]
    fn defining_catalog_retains_widened_abstract_producers() {
        let program = widened_abstract_method_source_program();
        let catalog = entry_catalog(&program);
        assert_eq!(catalog.domains().len(), 2);
        assert!(catalog.adapters().is_empty());
        assert_eq!(
            catalog
                .expectations()
                .iter()
                .filter(|expectation| matches!(
                    expectation.role,
                    MethodEvidenceExpectedRole::Instantiation { .. }
                        | MethodEvidenceExpectedRole::Application { .. }
                ))
                .count(),
            2
        );
    }

    #[test]
    fn defining_catalog_retains_concrete_adapter_source() {
        let program = concrete_monomorphic_source_program();
        assert_eq!(entry_catalog(&program).concrete_sources().len(), 1);
    }

    #[test]
    fn final_method_relation_reads_one_declaration_ordinal_slot() {
        const WIDTH: usize = 32_768;

        #[derive(Clone)]
        struct CountedIdentity<'a> {
            value: MethodId,
            comparisons: &'a Cell<usize>,
        }

        impl PartialEq for CountedIdentity<'_> {
            fn eq(&self, other: &Self) -> bool {
                self.comparisons
                    .set(self.comparisons.get().saturating_add(1));
                self.value == other.value
            }
        }

        let interface = InterfaceId::new(ModuleId::new(71), 0);
        let comparisons = Cell::new(0);
        let methods = (0..WIDTH)
            .map(|ordinal| CountedIdentity {
                value: MethodId::new(interface, u32::try_from(ordinal).expect("test ordinal")),
                comparisons: &comparisons,
            })
            .collect::<Vec<_>>();
        let final_method =
            MethodId::new(interface, u32::try_from(WIDTH - 1).expect("final ordinal"));
        let expected = CountedIdentity {
            value: final_method,
            comparisons: &comparisons,
        };

        assert!(method_relation_slot_matches(
            &methods,
            final_method,
            &expected
        ));
        assert_eq!(
            comparisons.get(),
            1,
            "the final method must use one indexed comparison"
        );

        comparisons.set(0);
        let wrong = CountedIdentity {
            value: MethodId::new(interface, 0),
            comparisons: &comparisons,
        };
        assert!(!method_relation_slot_matches(
            &methods,
            final_method,
            &wrong
        ));
        assert_eq!(
            comparisons.get(),
            1,
            "a wrong final slot must not trigger a fallback scan"
        );

        comparisons.set(0);
        let out_of_range = MethodId::new(interface, u32::MAX);
        assert!(!method_relation_slot_matches(
            &methods,
            out_of_range,
            &expected
        ));
        assert_eq!(
            comparisons.get(),
            0,
            "an out-of-range ordinal must read no slot"
        );

        let actual_methods = methods
            .iter()
            .map(|method| method.value)
            .collect::<Vec<_>>();
        assert!(method_relation_slot_matches(
            &actual_methods,
            final_method,
            &final_method,
        ));
        let implementation = ImplId::new(interface.module(), 0);
        let implementation_methods = actual_methods
            .iter()
            .copied()
            .map(|method| ImplMethodId::new(implementation, method))
            .collect::<Vec<_>>();
        assert!(method_relation_slot_matches(
            &implementation_methods,
            final_method,
            &ImplMethodId::new(implementation, final_method),
        ));
    }

    fn reexport_groups(
        program: &ResolvedModuleProgram,
    ) -> (
        &crate::resolved::ResolvedModuleGroup,
        &crate::resolved::ResolvedModuleGroup,
        &crate::resolved::ResolvedModuleGroup,
    ) {
        let base = program
            .groups()
            .iter()
            .find(|group| {
                group
                    .interface_facts()
                    .iter()
                    .any(|fact| fact.spelling == "Equal")
            })
            .expect("Equal's defining group");
        let facade = program
            .groups()
            .iter()
            .filter(|group| group.module() != base.module() && group.module() != program.entry())
            .filter_map(|group| {
                group
                    .public_implementation_authorizations()
                    .iter()
                    .filter(|authorization| authorization.id().module() == base.module())
                    .map(|authorization| authorization.authorization().hops().len())
                    .max()
                    .map(|depth| (depth, group))
            })
            .max_by_key(|(depth, _)| *depth)
            .expect("the outer publishing facade")
            .1;
        (base, facade, entry_group(program))
    }

    fn reexport_program() -> ResolvedModuleProgram {
        let fixture = ValidationFixture::create(concat!(
            "pub import facade (Equal, equal, impl Equal)\n",
            "main : Unit -> Bool\nmain () = equal((1, 1))\n",
        ));
        fixture.write(
            "base.ash",
            concat!(
                "pub interface Equal<A> {\nequal : (A, A) -> Bool\n}\n\n",
                "pub impl Equal<Int> {\nequal (left, right) = left == right\n}\n",
            ),
        );
        fixture.write("facade.ash", "pub import base (Equal, equal, impl Equal)\n");
        let graph = fixture.graph();
        link_modules(check_graph(&graph), graph.entry())
            .expect("the transitive public fixture should link")
    }

    fn dual_reexport_program() -> ResolvedModuleProgram {
        let fixture = ValidationFixture::create(concat!(
            "import facade (Equal, equal, impl Equal)\n",
            "main : Unit -> ((Int, Int) -> Bool)\nmain () = equal\n",
        ));
        fixture.write(
            "base.ash",
            concat!(
                "pub interface Equal<A> {\nequal : (A, A) -> Bool\n}\n\n",
                "pub interface Keep<A> {\nkeep : A -> A\n}\n\n",
                "pub impl Equal<Int> {\nequal (left, right) = left == right\n}\n\n",
                "pub impl Keep<Int> {\nkeep value = value\n}\n",
            ),
        );
        fixture.write(
            "facade.ash",
            "pub import base (Equal, equal, Keep, keep, impl Equal, impl Keep)\n",
        );
        let graph = fixture.graph();
        link_modules(check_graph(&graph), graph.entry())
            .expect("the dual transitive fixture should link")
    }

    fn deep_reexport_program() -> ResolvedModuleProgram {
        let fixture = ValidationFixture::create(concat!(
            "pub import facade (Equal, equal, impl Equal)\n",
            "main : Unit -> Bool\nmain () = equal((1, 1))\n",
        ));
        fixture.write(
            "base.ash",
            concat!(
                "pub interface Equal<A> {\nequal : (A, A) -> Bool\n}\n\n",
                "pub impl Equal<Int> {\nequal (left, right) = left == right\n}\n",
            ),
        );
        fixture.write("inner.ash", "pub import base (Equal, equal, impl Equal)\n");
        fixture.write(
            "facade.ash",
            "pub import inner (Equal, equal, impl Equal)\n",
        );
        let graph = fixture.graph();
        link_modules(check_graph(&graph), graph.entry())
            .expect("the deep transitive fixture should link")
    }

    fn implementation_selection(
        implementation: ImplId,
        interface: InterfaceId,
        methods: &[ImplMethodId],
    ) -> EvidenceSelection {
        implementation_selection_for_argument(implementation, interface, methods, Type::Int)
    }

    fn finish_width_one(
        builder: EvidenceSelectionBuilder,
        root: EvidenceNodeId,
        interface: InterfaceId,
        argument: Type,
    ) -> Result<EvidenceSelection, ()> {
        builder.finish(root, test_application(interface, Box::new([argument])))
    }

    fn implementation_selection_for_argument(
        implementation: ImplId,
        interface: InterfaceId,
        methods: &[ImplMethodId],
        argument: Type,
    ) -> EvidenceSelection {
        let mut builder = EvidenceSelectionBuilder::new();
        let root = builder
            .push_implementation(
                implementation,
                Box::new([]),
                &[],
                methods,
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the tiny implementation node should fit");
        finish_width_one(builder, root, interface, argument)
            .expect("the implementation root should exist")
    }

    fn generic_program() -> ResolvedModuleProgram {
        entry_program(concat!(
            "type Wrap<A> = Wrap(A)\n\n",
            "interface Equal<A> {\nequal : (A, A) -> Bool\n}\n\n",
            "impl Equal<Int> {\nequal (left, right) = left == right\n}\n\n",
            "impl Equal<Wrap<A>> where Equal<A> {\n",
            "equal (Wrap(left), Wrap(right)) = equal((left, right))\n",
            "}\n\n",
            "main : Unit -> Bool\nmain () = equal((Wrap(1), Wrap(1)))\n",
        ))
    }

    fn higher_kinded_generic_program() -> ResolvedModuleProgram {
        entry_program(concat!(
            "type Wrapped<F : Type -> Type, A> = Wrapped(F<A>)\n\n",
            "interface Extract<A> {\nextract : A -> A\n}\n\n",
            "impl<F : Type -> Type, A> Extract<Wrapped<F, A>> {\n",
            "extract value = value\n",
            "}\n\n",
            "relay<G : Type -> Type> : G<Int> -> G<Int>\n",
            "relay value = value\n\n",
            "main : Unit -> Unit\nmain () = ()\n",
        ))
    }

    fn linked_registry_row_program() -> ResolvedModuleProgram {
        let fixture = ValidationFixture::create(concat!(
            "import dependency (pair)\n\n",
            "second<C, D> : (C, D) -> (C, D)\n",
            "second value = value\n\n",
            "main : Unit -> Unit\n",
            "main value = value\n",
        ));
        fixture.write(
            "dependency.ash",
            concat!(
                "pub pair<A, B> : (A, B) -> (A, B)\n",
                "pair value = value\n",
            ),
        );
        let graph = fixture.graph();
        link_modules(check_graph(&graph), graph.entry())
            .expect("the linked registry-row fixture should link")
    }

    #[test]
    fn linked_registry_rows_have_exact_constraint_work() {
        const GROUPS: usize = 4;
        const TYPE_VARIABLES: usize = 6;
        const GLOBAL_SCHEMES: usize = 9;
        const GLOBAL_ROWS: usize = 3;
        const GLOBAL_PARAMETERS: usize = 5;

        let program = linked_registry_row_program();
        assert_eq!(program.registry().nominals().len(), 5);
        assert_eq!(program.registry().constructors().len(), 5);
        assert!(
            program
                .registry()
                .constructors()
                .iter()
                .all(|constructor| constructor.payload.is_none())
        );
        assert!(
            program
                .registry()
                .type_variables()
                .all(|parameter| parameter.kind == Kind::Type)
        );
        let effects = program.registry().effects();
        let [effect] = effects else {
            panic!("only canonical DefaultAlloc")
        };
        assert!(effect.id.module().is_builtin_region());
        assert!(effect.parameters.is_empty());
        assert_eq!(effect.operations.len(), 2);
        let storage = program
            .registry()
            .nominals()
            .iter()
            .find(|nominal| nominal.spelling == "Storage")
            .unwrap();
        let [storage_owner] = program.registry().nominal_parameters(storage.id).unwrap() else {
            panic!("Storage owner")
        };
        let service_rows = program
            .registry()
            .global_parameter_rows()
            .iter()
            .filter(|row| {
                row.owner()
                    .module()
                    .is_some_and(ModuleId::is_builtin_region)
            })
            .collect::<Vec<_>>();
        let [service_row] = service_rows.as_slice() else {
            panic!("from_backing owner row")
        };
        let [service_parameter] = service_row.parameters() else {
            panic!("one global R")
        };
        assert_ne!(storage_owner.id, *service_parameter);
        let row_count = program.registry().global_parameter_rows().len();
        let parameter_count = program
            .registry()
            .global_parameter_rows()
            .iter()
            .map(|row| row.parameters().len())
            .sum::<usize>();
        assert_eq!(program.groups().len(), GROUPS);
        assert_eq!(program.registry().type_variable_count(), TYPE_VARIABLES);
        assert_eq!(
            program
                .groups()
                .iter()
                .map(|group| group.schemes().len())
                .sum::<usize>(),
            GLOBAL_SCHEMES,
        );
        assert_eq!(row_count, GLOBAL_ROWS);
        assert_eq!(parameter_count, GLOBAL_PARAMETERS);
        let mut measured_constraint_work = InterfaceConstraintBudget::default();
        let mut measured_type_work = TypeWorkBudget::default();
        validate_interface_evidence_with_budget(
            linked_registry_row_program(),
            &mut measured_constraint_work,
            &mut measured_type_work,
        )
        .expect("the complete linked program should validate with default budgets");
        let exact_constraint_work = measured_constraint_work.used();
        let exact_type_work = measured_type_work.used();

        let mut exact_constraint = InterfaceConstraintBudget::with_limit(exact_constraint_work);
        let mut exact_type = TypeWorkBudget::with_limit(exact_type_work);
        validate_interface_evidence_with_budget(
            linked_registry_row_program(),
            &mut exact_constraint,
            &mut exact_type,
        )
        .expect("a fresh fixture should publish its capability with both exact ledgers");
        assert_eq!(exact_constraint.used(), exact_constraint_work);
        assert_eq!(exact_type.used(), exact_type_work);
    }

    fn linked_higher_kinded_diamond_program() -> (ResolvedModuleProgram, ModuleId) {
        let fixture = ValidationFixture::create(concat!(
            "import left (relay as leftRelay, expose as leftExpose, Wrap as LeftWrap, ",
            "First as LeftFirst, Capsule as LeftCapsule, Observe as LeftObserve, ",
            "observe as leftObserve, impl Observe)\n",
            "import right (relay as rightRelay, expose as rightExpose, Wrap as RightWrap, ",
            "First as RightFirst, Capsule as RightCapsule, Observe as RightObserve, ",
            "observe as rightObserve, impl Observe)\n\n",
            "main : Unit -> Unit\nmain () = ()\n",
        ));
        fixture.write(
            "base.ash",
            concat!(
                "type Secret<F : Type -> Type> = Secret(F<Int>)\n\n",
                "pub expose<F : Type -> Type> : Secret<F> -> Secret<F>\n",
                "expose value = value\n\n",
                "pub type Wrap<F : Type -> Type, A> =\n",
                "First(F<A>)\n| Second(F<A>)\n\n",
                "pub opaque type Capsule<F : Type -> Type> = Seal(Unit)\n\n",
                "pub interface Observe<A> {\nobserve : A -> A\n}\n\n",
                "pub interface Witness<A> {\nwitness : A -> A\n}\n\n",
                "pub impl<F : Type -> Type, A> Observe<Wrap<F, A>> where Witness<A> {\n",
                "observe value = value\n}\n\n",
                "pub impl<F : Type -> Type> Observe<Capsule<F>> {\n",
                "observe value = value\n}\n\n",
                "pub relay<G : Type -> Type> : G<Int> -> G<Int>\n",
                "relay value = value\n",
            ),
        );
        let facade = concat!(
            "pub import base (relay, expose, Wrap, First, Capsule, Observe, observe, ",
            "impl Observe)\n",
        );
        fixture.write("left.ash", facade);
        fixture.write("right.ash", facade);
        let graph = fixture.graph();
        let program = link_modules(check_graph(&graph), graph.entry())
            .expect("the higher-kinded diamond fixture should link");
        let base = program
            .groups()
            .iter()
            .find(|group| {
                group
                    .schemes()
                    .iter()
                    .any(|scheme| scheme.spelling == "relay")
            })
            .map(ResolvedModuleGroup::module)
            .expect("the linked diamond should retain its defining base group");
        (program, base)
    }

    fn single_substitution(
        parameter: crate::types::TypeVariableId,
        argument: &Type,
    ) -> Box<[crate::interface::EvidenceSubstitution]> {
        match_implementation_head_structurally(
            [parameter].into_iter(),
            &Type::Variable(parameter),
            argument,
            &mut InterfaceConstraintBudget::default(),
            &mut TypeWorkBudget::default(),
        )
        .expect("the tiny synthetic substitution should be valid")
        .expect("one bindable parameter should match")
    }

    fn nested_generic_selection(
        program: &ResolvedModuleProgram,
        substitution_argument: &Type,
        root_argument: Type,
    ) -> EvidenceSelection {
        let group = entry_group(program);
        let ground = &group.implementation_facts()[0];
        let generic = &group.implementation_facts()[1];
        let parameter = generic.head_parameters[0].id;
        let mut builder = EvidenceSelectionBuilder::new();
        let child = builder
            .push_implementation(
                ground.id,
                Box::new([]),
                &[],
                &ground
                    .methods
                    .iter()
                    .map(|method| method.id)
                    .collect::<Vec<_>>(),
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the ground prerequisite should fit");
        let root = builder
            .push_implementation(
                generic.id,
                single_substitution(parameter, substitution_argument),
                &[child],
                &generic
                    .methods
                    .iter()
                    .map(|method| method.id)
                    .collect::<Vec<_>>(),
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the generic root should fit");
        finish_width_one(builder, root, generic.interface(), root_argument)
            .expect("the generic evidence root should exist")
    }

    fn abstract_program() -> ResolvedModuleProgram {
        entry_program(concat!(
            "interface Equal<A> {\nequal : (A, A) -> Bool\n}\n\n",
            "impl Equal<Int> {\nequal (left, right) = left == right\n}\n\n",
            "first : A -> Bool where Equal<A>\n",
            "first value = equal((value, value))\n\n",
            "second : A -> Bool where Equal<A>\n",
            "second value = equal((value, value))\n\n",
            "main : Unit -> Bool\nmain () = second(1)\n",
        ))
    }

    fn abstract_priority_program() -> ResolvedModuleProgram {
        entry_program(concat!(
            "type Wrap<A> = Wrap(A)\n",
            "type Nest<A> = Nest(A)\n\n",
            "interface Keep<A> {\nkeep : A -> A\n}\n\n",
            "impl Keep<Wrap<A>> {\nkeep value = value\n}\n\n",
            "impl Keep<Nest<Wrap<A>>> where Keep<Wrap<A>> {\n",
            "keep value = keep(value)\n",
            "}\n\n",
            "shadowed : Wrap<A> -> Wrap<A> where Keep<Wrap<A>>\n",
            "shadowed value = keep(value)\n\n",
            "main : Unit -> Unit\nmain () = ()\n",
        ))
    }

    fn current_authenticity_program() -> ResolvedModuleProgram {
        entry_program(concat!(
            "type Wrap<A> = Wrap(A)\n",
            "type Nest<A> = Nest(A)\n",
            "type Shell<A> = Shell(A)\n\n",
            "interface Keep<A> {\nkeep : A -> A\n}\n\n",
            "impl Keep<Wrap<A>> {\nkeep value = value\n}\n\n",
            "impl Keep<Nest<Wrap<A>>> where Keep<Wrap<A>> {\n",
            "keep value = keep(value)\n",
            "}\n\n",
            "impl Keep<Shell<A>> where Keep<A> {\n",
            "keep (Shell(value)) = Shell(keep(value))\n",
            "}\n\n",
            "main : Unit -> Unit\nmain () = ()\n",
        ))
    }

    fn distinct_abstract_prerequisites_program() -> ResolvedModuleProgram {
        entry_program(concat!(
            "type Wrap<A> = Wrap(A)\n\n",
            "interface Keep<A> {\nkeep : A -> A\n}\n\n",
            "interface Preserve<A> {\npreserve : A -> A\n}\n\n",
            "impl Keep<Wrap<A>> where Keep<A>, Preserve<A> {\n",
            "keep (Wrap(value)) = Wrap(keep(value))\n",
            "}\n\n",
            "main : Unit -> Unit\nmain () = ()\n",
        ))
    }

    fn exact_current_with_distinct_prerequisites_program() -> ResolvedModuleProgram {
        entry_program(concat!(
            "type Wrap<A> = Wrap(A)\n\n",
            "interface Keep<A> {\nkeep : A -> A\n}\n\n",
            "interface Preserve<A> {\npreserve : A -> A\n}\n\n",
            "impl Keep<Wrap<A>> where Keep<A>, Preserve<A> {\n",
            "keep value = keep(value)\n",
            "}\n\n",
            "main : Unit -> Unit\nmain () = ()\n",
        ))
    }

    fn instantiate_single_parameter_head(
        fact: &CheckedImplementationFact,
        argument: &Type,
    ) -> Type {
        let [parameter] = fact.head_parameters.as_ref() else {
            panic!("the fixture implementation should retain one head parameter");
        };
        substitute_evidence_type(
            test_type_argument(&fact.arguments()[0]),
            &single_substitution(parameter.id, argument),
            &mut InterfaceConstraintBudget::default(),
            fact.span,
        )
        .expect("the fixture head should instantiate within the default budget")
    }

    #[test]
    fn linked_evidence_walkers_accept_closed_effectful_arguments_and_reject_open_tails() {
        let program = entry_program("main : Unit -> Unit\nmain () = ()\n");
        let span = program.result().span;
        let parameter = TypeVariableId::new(0);
        let effect = crate::types::EffectId::new(ModuleId::new(77), 0);
        let closed = Type::function_computation(
            Type::Unit,
            crate::types::ComputationType::new(
                Type::Bool,
                crate::types::EffectRow::singleton(crate::types::EffectInstance::new(
                    effect,
                    Box::new([Type::Int]),
                )),
            ),
        );

        validate_type_with_application_policy(
            &closed,
            program.registry(),
            &[],
            &mut InterfaceConstraintBudget::default(),
            span,
        )
        .expect("closed effectful values are valid linked interface arguments");
        let closed_with_variable = Type::function_computation(
            Type::Unit,
            crate::types::ComputationType::new(
                Type::Bool,
                crate::types::EffectRow::singleton(crate::types::EffectInstance::new(
                    effect,
                    Box::new([Type::Variable(parameter)]),
                )),
            ),
        );
        let mut variables = Vec::new();
        collect_linked_constraint_variables(
            &closed_with_variable,
            &mut variables,
            &mut InterfaceConstraintBudget::default(),
            span,
        )
        .expect("closed row arguments contribute their ordinary variables");
        assert_eq!(variables, [parameter]);
        assert!(
            same_type_charged(
                &closed,
                &closed,
                &mut InterfaceConstraintBudget::default(),
                span,
            )
            .expect("closed effectful equality should authenticate")
        );
        let substituted = substitute_evidence_type(
            &closed_with_variable,
            &single_substitution(parameter, &Type::Int),
            &mut InterfaceConstraintBudget::default(),
            span,
        )
        .expect("evidence substitution should traverse closed row arguments");
        assert_eq!(
            substituted,
            Type::function_computation(
                Type::Unit,
                crate::types::ComputationType::new(
                    Type::Bool,
                    crate::types::EffectRow::singleton(crate::types::EffectInstance::new(
                        effect,
                        Box::new([Type::Int]),
                    )),
                ),
            )
        );

        let open = Type::function_computation(
            Type::Unit,
            crate::types::ComputationType::new(
                Type::Bool,
                crate::types::EffectRow::open(
                    crate::types::EffectRowVariable::rigid(parameter),
                    Box::new([]),
                ),
            ),
        );
        assert_eq!(
            validate_type_with_application_policy(
                &open,
                program.registry(),
                &[],
                &mut InterfaceConstraintBudget::default(),
                span,
            )
            .expect_err("an open row tail is invalid in a linked interface argument")
            .reason(),
            EvidenceValidationReason::InvalidEvidenceRoot
        );
    }

    #[test]
    fn nullary_closed_row_evidence_work_is_proportional_exact_and_retryable() {
        const NARROW: u32 = 1;
        const WIDE: u32 = 8;
        let program = entry_program("main : Unit -> Unit\nmain () = ()\n");
        let span = program.result().span;
        let closed = |width| {
            let members = (0..width)
                .map(|declaration| {
                    crate::types::EffectInstance::new(
                        crate::types::EffectId::new(ModuleId::new(77), declaration),
                        Box::new([]),
                    )
                })
                .collect::<Vec<_>>()
                .into_boxed_slice();
            Type::function_computation(
                Type::Unit,
                crate::types::ComputationType::new(
                    Type::Bool,
                    crate::types::EffectRow::closed(members),
                ),
            )
        };
        let exercise = |ty: &Type, budget: &mut InterfaceConstraintBudget| {
            validate_type_with_application_policy(ty, program.registry(), &[], budget, span)?;
            let mut variables = Vec::new();
            collect_linked_constraint_variables(ty, &mut variables, budget, span)?;
            if !same_type_charged(ty, ty, budget, span)? {
                return Err(invalid_root(span));
            }
            substitute_evidence_type(ty, &[], budget, span)?;
            Ok::<(), EvidenceValidationFailure>(())
        };

        let mut narrow_work = InterfaceConstraintBudget::default();
        exercise(&closed(NARROW), &mut narrow_work).expect("the narrow row should fit");
        let mut measured = InterfaceConstraintBudget::default();
        let wide = closed(WIDE);
        exercise(&wide, &mut measured).expect("the measured wide row should fit");
        let exact = measured.used();
        assert_eq!(
            exact - narrow_work.used(),
            9 * (WIDE - NARROW) as usize,
            "ordered nullary rows reuse canonical storage, preserving traversal and comparison work"
        );

        let mut one_short = InterfaceConstraintBudget::with_limit(exact - 1);
        assert_eq!(
            exercise(&wide, &mut one_short)
                .expect_err("one short must reject before returning evidence")
                .reason(),
            EvidenceValidationReason::ConstraintResourceExhausted
        );
        let mut retry = InterfaceConstraintBudget::with_limit(exact);
        exercise(&wide, &mut retry).expect("the exact ledger should retry successfully");
        assert_eq!(retry.used(), exact);

        let late_mismatch = closed(WIDE - 1);
        let Type::EffectfulFunction(domain, computation) = late_mismatch else {
            panic!("the fixture is effectful")
        };
        let mut members = computation.effects().known().to_vec();
        members.push(crate::types::EffectInstance::new(
            crate::types::EffectId::new(ModuleId::new(77), 99),
            Box::new([]),
        ));
        let late_mismatch = Type::function_computation(
            *domain,
            crate::types::ComputationType::new(
                computation.value().clone(),
                crate::types::EffectRow::closed(members.into_boxed_slice()),
            ),
        );
        let mismatch_work = WIDE as usize + 2;
        let mut mismatch_short = InterfaceConstraintBudget::with_limit(mismatch_work - 1);
        assert_eq!(
            same_type_charged(&wide, &late_mismatch, &mut mismatch_short, span)
                .expect_err("one short must fail before the late member comparison")
                .reason(),
            EvidenceValidationReason::ConstraintResourceExhausted
        );
        let mut mismatch_exact = InterfaceConstraintBudget::with_limit(mismatch_work);
        assert_eq!(
            same_type_charged(&wide, &late_mismatch, &mut mismatch_exact, span),
            Ok(false)
        );
        assert_eq!(mismatch_exact.used(), mismatch_work);
    }

    fn forged_fresh_current_node(
        builder: &mut EvidenceSelectionBuilder,
        leaf: &CheckedImplementationFact,
        current: &CheckedImplementationFact,
    ) -> EvidenceNodeId {
        let [leaf_parameter] = leaf.head_parameters.as_ref() else {
            panic!("the leaf implementation should retain one head parameter");
        };
        let [current_parameter] = current.head_parameters.as_ref() else {
            panic!("the current implementation should retain one head parameter");
        };
        let prerequisite = builder
            .push_implementation(
                leaf.id,
                single_substitution(leaf_parameter.id, &Type::Int),
                &[],
                &leaf
                    .methods
                    .iter()
                    .map(|method| method.id)
                    .collect::<Vec<_>>(),
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the concrete prerequisite node should fit");
        builder
            .push_implementation(
                current.id,
                single_substitution(current_parameter.id, &Type::Int),
                &[prerequisite],
                &current
                    .methods
                    .iter()
                    .map(|method| method.id)
                    .collect::<Vec<_>>(),
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the forged freshly instantiated current node should fit")
    }

    fn two_parameter_program() -> ResolvedModuleProgram {
        entry_program(concat!(
            "interface Keep<A> {\nkeep : A -> A\n}\n\n",
            "impl Keep<(A, B)> {\nkeep value = value\n}\n\n",
            "main : Unit -> (Int, Bool)\nmain () = keep((1, true))\n",
        ))
    }

    fn two_application_parameter_program() -> ResolvedModuleProgram {
        entry_program(concat!(
            "type Option<A> =\nNone\n| Some(A)\n\n",
            "interface Pair<A, B> {\npair : (A, B) -> (A, B)\n}\n\n",
            "impl Pair<Int, Bool> {\npair value = value\n}\n\n",
            "main : Unit -> (Int, Bool)\nmain () = pair((1, true))\n",
        ))
    }

    fn implementation_selection_for_application(
        fact: &CheckedImplementationFact,
        arguments: Box<[crate::types::KindedArgument]>,
    ) -> EvidenceSelection {
        let mut builder = EvidenceSelectionBuilder::new();
        let root = builder
            .push_implementation(
                fact.id,
                Box::new([]),
                &[],
                &fact
                    .methods
                    .iter()
                    .map(|method| method.id)
                    .collect::<Vec<_>>(),
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the concrete node should fit");
        builder
            .finish(
                root,
                InterfaceApplication::new_kinded(fact.interface(), arguments),
            )
            .expect("a forged application root should remain representable")
    }

    fn abstract_selection_for_application(
        requirement: RequirementId,
        interface: &CheckedInterfaceFact,
        arguments: Box<[crate::types::KindedArgument]>,
    ) -> EvidenceSelection {
        let mut builder = EvidenceSelectionBuilder::new();
        let root = builder
            .push_abstract(
                requirement,
                &interface
                    .methods
                    .iter()
                    .map(|method| method.id)
                    .collect::<Vec<_>>(),
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the abstract node should fit");
        builder
            .finish(
                root,
                InterfaceApplication::new_kinded(interface.id, arguments),
            )
            .expect("a forged abstract application should remain representable")
    }

    fn two_prerequisite_program() -> ResolvedModuleProgram {
        entry_program(concat!(
            "type Wrap<A> = Wrap(A)\n\n",
            "interface Left<A> {\nleft : A -> A\n}\n\n",
            "interface Right<A> {\nright : A -> A\n}\n\n",
            "interface Both<A> {\nboth : A -> A\n}\n\n",
            "impl Left<Int> {\nleft value = value\n}\n\n",
            "impl Right<Int> {\nright value = value\n}\n\n",
            "impl Both<Wrap<A>> where Left<A>, Right<A> {\n",
            "both (Wrap(value)) = Wrap(right(left(value)))\n",
            "}\n\n",
            "main : Unit -> Wrap<Int>\nmain () = both(Wrap(1))\n",
        ))
    }

    fn abstract_selection(
        requirement: RequirementId,
        interface: &CheckedInterfaceFact,
        argument: Type,
    ) -> EvidenceSelection {
        let mut builder = EvidenceSelectionBuilder::new();
        let methods = interface
            .methods
            .iter()
            .map(|method| method.id)
            .collect::<Vec<_>>();
        let root = builder
            .push_abstract(
                requirement,
                &methods,
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the abstract node should fit");
        finish_width_one(builder, root, interface.id, argument)
            .expect("the abstract root should exist")
    }

    #[test]
    fn validated_interface_capability_has_exact_resolved_program_payload() {
        let ValidatedInterfaceProgram {
            source,
            _method_evidence: _,
        } = validate_interface_evidence(local_program())
            .expect("the local fixture should validate");
        let source: ResolvedModuleProgram = source;

        drop(source);
    }

    #[test]
    fn validates_generic_prerequisites_and_lexical_abstract_evidence_before_core() {
        validate_interface_evidence(generic_program())
            .expect("generic prerequisite evidence should authenticate");
        validate_interface_evidence(abstract_program())
            .expect("abstract evidence should remain within its declaring globals");
    }

    #[test]
    fn rejects_selected_goal_that_does_not_match_the_recorded_impl_head() {
        let program = local_program();
        let group = entry_group(&program);
        let fact = &group.implementation_facts()[0];
        let selection = implementation_selection(
            fact.id,
            fact.interface(),
            &fact
                .methods
                .iter()
                .map(|method| method.id)
                .collect::<Vec<_>>(),
        );
        let mut builder = EvidenceSelectionBuilder::new();
        let root = builder
            .push_implementation(
                fact.id,
                Box::new([]),
                &[],
                &fact
                    .methods
                    .iter()
                    .map(|method| method.id)
                    .collect::<Vec<_>>(),
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the malformed goal fixture should fit");
        let wrong_goal = finish_width_one(builder, root, selection.interface(), Type::Bool)
            .expect("the malformed goal root should exist");
        let registry =
            LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                .expect("the valid linked registry should authenticate");

        let failure = validate_selection(
            &program,
            &registry,
            group,
            &wrong_goal,
            fact.interface(),
            &mut InterfaceConstraintBudget::default(),
            group.span(),
        )
        .expect_err("the selected goal must match the recorded implementation head");

        assert_eq!(
            failure.reason(),
            EvidenceValidationReason::InvalidEvidenceRoot
        );
    }

    #[test]
    fn rejects_missing_extra_and_reordered_checked_application_arguments() {
        let program = two_application_parameter_program();
        let group = entry_group(&program);
        let fact = &group.implementation_facts()[0];
        let registry =
            LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                .expect("the canonical linked registry should authenticate");

        for arguments in [
            Box::new([]),
            vec![
                crate::types::KindedArgument::TypeArg(Type::Int),
                crate::types::KindedArgument::TypeArg(Type::Bool),
                crate::types::KindedArgument::TypeArg(Type::Unit),
            ]
            .into_boxed_slice(),
            vec![
                crate::types::KindedArgument::TypeArg(Type::Bool),
                crate::types::KindedArgument::TypeArg(Type::Int),
            ]
            .into_boxed_slice(),
        ] {
            let forged = implementation_selection_for_application(fact, arguments);
            assert_eq!(
                validate_selection(
                    &program,
                    &registry,
                    group,
                    &forged,
                    fact.interface(),
                    &mut InterfaceConstraintBudget::default(),
                    fact.span,
                )
                .expect_err("checked application arity and order are authenticated")
                .reason(),
                EvidenceValidationReason::InvalidEvidenceRoot,
            );
        }
    }

    #[test]
    fn authenticates_an_honest_determined_linked_program_before_core() {
        let program = entry_program(concat!(
            "interface Relation<A, B> where A -> B {\n",
            "relate : A -> Int\n",
            "}\n\n",
            "impl Relation<Int, Bool> {\n",
            "relate value = 0\n",
            "}\n\n",
            "main : Unit -> Unit\n",
            "main () = ()\n",
        ));

        validate_interface_evidence(program)
            .expect("an honest determined relation must authenticate before Core");
    }

    #[test]
    fn linked_generic_prerequisite_decrease_uses_determined_selection_keys() {
        validate_interface_evidence(linked_determined_generic_decrease_program()).expect(
            "linked generic decrease must compare the determined key and retain the complete prerequisite only for groundness",
        );
    }

    #[test]
    fn linked_generic_prerequisite_selection_key_has_an_exact_public_retry_boundary() {
        let mut constraint_work = InterfaceConstraintBudget::default();
        let mut type_work = TypeWorkBudget::default();
        validate_interface_evidence_with_budget(
            linked_determined_generic_decrease_program(),
            &mut constraint_work,
            &mut type_work,
        )
        .expect("the measured generic decrease program should authenticate");
        let exact_constraint_work = constraint_work.used();
        let exact_type_work = type_work.used();
        assert!(exact_constraint_work > 0 && exact_type_work > 0);

        let mut constraint_short = InterfaceConstraintBudget::with_limit(exact_constraint_work - 1);
        let mut exact_type = TypeWorkBudget::with_limit(exact_type_work);
        let failure = validate_interface_evidence_with_budget(
            linked_determined_generic_decrease_program(),
            &mut constraint_short,
            &mut exact_type,
        )
        .expect_err("one missing constraint unit must reject before publication");
        assert_eq!(
            failure.reason(),
            EvidenceValidationReason::ConstraintResourceExhausted,
        );
        assert_eq!(constraint_short.used(), exact_constraint_work - 1);
        assert_eq!(exact_type.used(), exact_type_work);

        let mut exact_constraint = InterfaceConstraintBudget::with_limit(exact_constraint_work);
        let mut type_short = TypeWorkBudget::with_limit(exact_type_work - 1);
        let failure = validate_interface_evidence_with_budget(
            linked_determined_generic_decrease_program(),
            &mut exact_constraint,
            &mut type_short,
        )
        .expect_err("one missing type unit must reject before publication");
        assert_eq!(
            failure.reason(),
            EvidenceValidationReason::TypeResourceExhausted,
        );
        assert!(exact_constraint.used() <= exact_constraint_work);
        assert_eq!(type_short.used(), exact_type_work - 1);

        for _ in 0..2 {
            let mut exact_constraint = InterfaceConstraintBudget::with_limit(exact_constraint_work);
            let mut exact_type = TypeWorkBudget::with_limit(exact_type_work);
            validate_interface_evidence_with_budget(
                linked_determined_generic_decrease_program(),
                &mut exact_constraint,
                &mut exact_type,
            )
            .expect("the exact linked relationship boundary should remain retryable");
            assert_eq!(exact_constraint.used(), exact_constraint_work);
            assert_eq!(exact_type.used(), exact_type_work);
        }
    }

    #[test]
    fn linked_determination_is_retained_without_rechecking_and_retries_exactly() {
        fn program(determined: bool) -> ResolvedModuleProgram {
            let interface = if determined {
                "interface Relation<A, B, C> where (A, B) -> C {\n"
            } else {
                "interface Relation<A, B, C> {\n"
            };
            entry_program(&format!(
                "{interface}relation : (A, B, C) -> Unit\n}}\n\nmain : Unit -> Unit\nmain () = ()\n",
            ))
        }
        let measure = |determined| {
            let mut constraint_work = InterfaceConstraintBudget::default();
            let mut type_work = TypeWorkBudget::default();
            let validated = validate_interface_evidence_with_budget(
                program(determined),
                &mut constraint_work,
                &mut type_work,
            )
            .expect("the measured linked program should authenticate");
            let fact = validated
                .groups()
                .iter()
                .flat_map(|group| group.interface_facts())
                .find(|fact| fact.spelling == "Relation")
                .expect("the defining interface remains linked");
            assert_eq!(
                fact.determination().map(|key| key.positions()),
                determined.then_some([0, 1].as_slice())
            );
            (constraint_work.used(), type_work.used())
        };

        let ordinary = measure(false);
        let determined = measure(true);
        let (ordinary_constraint_work, ordinary_type_work) = ordinary;
        let (determined_constraint_work, exact_type_work) = determined;
        assert_eq!(ordinary_type_work, exact_type_work);
        assert_eq!(determined_constraint_work - ordinary_constraint_work, 0,);

        let mut short = InterfaceConstraintBudget::with_limit(determined_constraint_work - 1);
        let failure = validate_interface_evidence_with_budget(
            program(true),
            &mut short,
            &mut TypeWorkBudget::with_limit(exact_type_work),
        )
        .expect_err("one-short linked key work must not publish a capability");
        assert_eq!(
            failure.reason(),
            EvidenceValidationReason::ConstraintResourceExhausted,
        );
        assert_eq!(short.used(), determined_constraint_work - 1);

        for _ in 0..2 {
            let mut exact = InterfaceConstraintBudget::with_limit(determined_constraint_work);
            let mut exact_type = TypeWorkBudget::with_limit(exact_type_work);
            validate_interface_evidence_with_budget(program(true), &mut exact, &mut exact_type)
                .expect("the exact linked key boundary should remain retryable");
            assert_eq!(exact.used(), determined_constraint_work);
            assert_eq!(exact_type.used(), exact_type_work);
        }
    }

    #[test]
    fn rejects_kind_invalid_selected_goal_and_matching_higher_kinded_substitution() {
        let program = higher_kinded_generic_program();
        let group = entry_group(&program);
        let wrapped = program
            .registry()
            .nominals()
            .iter()
            .find(|nominal| nominal.id.module() == program.entry() && nominal.spelling == "Wrapped")
            .expect("the defining user Wrapped must remain canonical");
        let [fact] = group.implementation_facts() else {
            panic!("the fixture should retain exactly one generic implementation");
        };
        let malformed_goal =
            Type::apply_arguments(Type::Nominal(wrapped.id), [Type::Int, Type::Int]);
        let substitution = match_implementation_head_structurally(
            fact.head_parameters.iter().map(|parameter| parameter.id),
            test_type_argument(&fact.arguments()[0]),
            &malformed_goal,
            &mut InterfaceConstraintBudget::default(),
            &mut TypeWorkBudget::default(),
        )
        .expect("the malformed goal should remain structurally matchable")
        .expect("the forged substitution should reconstruct the malformed goal");
        let mut builder = EvidenceSelectionBuilder::new();
        let root = builder
            .push_implementation(
                fact.id,
                substitution,
                &[],
                &fact
                    .methods
                    .iter()
                    .map(|method| method.id)
                    .collect::<Vec<_>>(),
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the forged evidence node should fit");
        let selection = finish_width_one(builder, root, fact.interface(), malformed_goal)
            .expect("the forged root should remain structurally representable");
        let registry =
            LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                .expect("the canonical linked registry should authenticate");

        assert_eq!(
            validate_selection(
                &program,
                &registry,
                group,
                &selection,
                fact.interface(),
                &mut InterfaceConstraintBudget::default(),
                fact.span,
            )
            .expect_err("a selected goal must satisfy canonical K-Interface-Argument")
            .reason(),
            EvidenceValidationReason::InvalidEvidenceRoot,
        );
    }

    #[test]
    fn authenticates_one_reusable_higher_kinded_linked_diamond() {
        let (program, _) = linked_higher_kinded_diamond_program();
        validate_interface_evidence(program)
            .expect("the exact public, hidden, opaque, and implementation mirrors must link");
    }

    #[test]
    fn selected_substitution_authentication_has_exact_kind_limits() {
        // F -> G authenticates one canonical binder lookup, a function-kinded
        // variable synthesis (four cells), and a three-node Kind comparison.
        // A -> Int authenticates one lookup, two synthesis cells, and one
        // comparison cell: 8 + 4 = 12 constraint units. Installing lexical G
        // costs one canonical lookup plus one retained DELTA record.
        const SUBSTITUTION_CONSTRAINT_WORK: usize = 12;
        const LEXICAL_TYPE_WORK: usize = 2;
        let program = higher_kinded_generic_program();
        let group = entry_group(&program);
        let wrapped = program
            .registry()
            .nominals()
            .iter()
            .find(|nominal| nominal.id.module() == program.entry() && nominal.spelling == "Wrapped")
            .expect("the defining user Wrapped must remain canonical");
        let [fact] = group.implementation_facts() else {
            panic!("the fixture should retain exactly one generic implementation");
        };
        let relay = group
            .schemes()
            .iter()
            .find(|scheme| scheme.spelling == "relay")
            .expect("the fixture should retain relay's checked scheme");
        let [(rigid_function, _)] = relay.scheme.type_parameters.as_ref() else {
            panic!("relay should retain its one higher-kinded binder");
        };
        let goal = Type::apply_arguments(
            Type::Nominal(wrapped.id),
            [Type::Variable(*rigid_function), Type::Int],
        );
        let substitution = match_implementation_head_structurally(
            fact.head_parameters.iter().map(|parameter| parameter.id),
            test_type_argument(&fact.arguments()[0]),
            &goal,
            &mut InterfaceConstraintBudget::default(),
            &mut TypeWorkBudget::default(),
        )
        .expect("the rigid goal should remain structurally matchable")
        .expect("the valid substitution should be retained");
        let span = fact.span;

        let mut type_exact = TypeWorkBudget::with_limit(LEXICAL_TYPE_WORK);
        let mut environments = build_linked_kind_environments(
            program.registry(),
            &mut TypeWorkBudget::default(),
            span,
        )
        .expect("the nominal environment should fit outside the measured operation");
        environments
            .install_canonical_owner_ids(
                program.registry(),
                &[*rigid_function],
                &mut type_exact,
                span,
            )
            .expect("the exact lexical DELTA should fit");
        assert_eq!(type_exact.used(), LEXICAL_TYPE_WORK);

        let mut one_short = InterfaceConstraintBudget::with_limit(SUBSTITUTION_CONSTRAINT_WORK - 1);
        assert_eq!(
            authenticate_selected_substitution_kinds(
                fact,
                &substitution,
                program.registry(),
                &environments,
                &mut one_short,
                span,
            )
            .expect_err("one-short substitution Kind work must prevent publication")
            .reason(),
            EvidenceValidationReason::ConstraintResourceExhausted,
        );
        assert_eq!(one_short.used(), SUBSTITUTION_CONSTRAINT_WORK - 1);

        let mut exact = InterfaceConstraintBudget::with_limit(SUBSTITUTION_CONSTRAINT_WORK);
        authenticate_selected_substitution_kinds(
            fact,
            &substitution,
            program.registry(),
            &environments,
            &mut exact,
            span,
        )
        .expect("the exact substitution Kind budget should fit");
        assert_eq!(exact.used(), SUBSTITUTION_CONSTRAINT_WORK);

        let mut builder = EvidenceSelectionBuilder::new();
        let root = builder
            .push_implementation(
                fact.id,
                substitution,
                &[],
                &fact
                    .methods
                    .iter()
                    .map(|method| method.id)
                    .collect::<Vec<_>>(),
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the valid higher-kinded node should fit");
        let selection = finish_width_one(builder, root, fact.interface(), goal.clone())
            .expect("the valid higher-kinded selection should fit");
        let registry =
            LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                .expect("the canonical linked registry should authenticate");
        let mut selected_environments = build_linked_kind_environments(
            program.registry(),
            &mut TypeWorkBudget::default(),
            span,
        )
        .expect("the nominal environment should fit outside the measured operation");
        for interface in group.interface_facts() {
            selected_environments
                .insert_interface(
                    interface.id,
                    &interface.parameters,
                    interface.span,
                    &mut TypeWorkBudget::default(),
                )
                .expect("the interface environment should fit outside the measured operation");
        }
        let mut type_one_short = TypeWorkBudget::with_limit(LEXICAL_TYPE_WORK - 1);
        let application = test_application(fact.interface(), Box::new([goal.clone()]));
        assert_eq!(
            validate_checked_selection_in_scope(
                &program,
                &registry,
                group,
                &selection,
                &application,
                EvidenceScope {
                    local_scopes: &[],
                    lexical_sources: &[],
                    lexical_head: None,
                    owner: None,
                    variables: &[*rigid_function],
                },
                &mut selected_environments,
                &mut InterfaceConstraintBudget::default(),
                &mut type_one_short,
                span,
            )
            .expect_err("one-short lexical TypeWork must prevent selected evidence publication")
            .reason(),
            EvidenceValidationReason::TypeResourceExhausted,
        );
        assert_eq!(type_one_short.used(), LEXICAL_TYPE_WORK - 1);

        let malformed_goal =
            Type::apply_arguments(Type::Nominal(wrapped.id), [Type::Int, Type::Int]);
        let malformed = match_implementation_head_structurally(
            fact.head_parameters.iter().map(|parameter| parameter.id),
            test_type_argument(&fact.arguments()[0]),
            &malformed_goal,
            &mut InterfaceConstraintBudget::default(),
            &mut TypeWorkBudget::default(),
        )
        .expect("the malformed goal should remain structurally matchable")
        .expect("the malformed substitution should retain both parameters");
        assert_eq!(
            authenticate_selected_substitution_kinds(
                fact,
                &malformed,
                program.registry(),
                &environments,
                &mut InterfaceConstraintBudget::default(),
                span,
            )
            .expect_err("F -> Int violates F's canonical function kind")
            .reason(),
            EvidenceValidationReason::InvalidEvidenceRoot,
        );
    }

    #[test]
    fn rejects_wrong_generic_substitution_and_prerequisite_argument() {
        let program = generic_program();
        let group = entry_group(&program);
        let generic = &group.implementation_facts()[1];
        let owner = test_type_argument(&generic.arguments()[0])
            .outer_nominal()
            .expect("the generic fixture head should be a nominal application");
        let selection = nested_generic_selection(
            &program,
            &Type::Bool,
            Type::apply_arguments(Type::Nominal(owner), [Type::Int]),
        );
        let registry =
            LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                .expect("the valid linked registry should authenticate");

        let failure = validate_selection(
            &program,
            &registry,
            group,
            &selection,
            generic.interface(),
            &mut InterfaceConstraintBudget::default(),
            group.span(),
        )
        .expect_err("the recorded substitution and prerequisite argument must reconstruct exactly");

        assert_eq!(
            failure.reason(),
            EvidenceValidationReason::InvalidEvidenceRoot
        );
    }

    #[test]
    fn selected_root_and_prerequisite_kind_checks_have_exact_constraint_limit() {
        // Predecessor selection authentication costs 59 units. Canonical Kind
        // authentication adds nine for the Wrap<Int> root, four for A -> Int,
        // one positional root-application visit, and one for the
        // kind-preserving prerequisite edge: 59 + 9 + 4 + 1 + 1.
        const EXACT_WORK: usize = 74 + 15;
        let program = generic_program();
        let span = program.result().span;
        let mut proof_one_short = InterfaceConstraintBudget::with_limit(0);
        assert_eq!(
            authenticate_pending_goal_kind_from_prerequisite(&mut proof_one_short, span)
                .expect_err("one-short pending Kind proof work must prevent authentication")
                .reason(),
            EvidenceValidationReason::ConstraintResourceExhausted,
        );
        assert_eq!(proof_one_short.used(), 0);
        let mut proof_exact = InterfaceConstraintBudget::with_limit(1);
        authenticate_pending_goal_kind_from_prerequisite(&mut proof_exact, span)
            .expect("one unit should authenticate the kind-preserving pending edge");
        assert_eq!(proof_exact.used(), 1);

        let group = entry_group(&program);
        let generic = &group.implementation_facts()[1];
        let owner = test_type_argument(&generic.arguments()[0])
            .outer_nominal()
            .expect("the generic fixture head should be a nominal application");
        let selection = nested_generic_selection(
            &program,
            &Type::Int,
            Type::apply_arguments(Type::Nominal(owner), [Type::Int]),
        );
        let registry =
            LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                .expect("the valid linked registry should authenticate");
        let mut measured = InterfaceConstraintBudget::default();
        validate_selection(
            &program,
            &registry,
            group,
            &selection,
            generic.interface(),
            &mut measured,
            group.span(),
        )
        .expect("the selected goal should fit the measured budget");
        assert_eq!(measured.used(), EXACT_WORK);
        let mut one_short = InterfaceConstraintBudget::with_limit(EXACT_WORK - 1);
        assert_eq!(
            validate_selection(
                &program,
                &registry,
                group,
                &selection,
                generic.interface(),
                &mut one_short,
                group.span(),
            )
            .expect_err("one-short selected-goal work must prevent publication")
            .reason(),
            EvidenceValidationReason::ConstraintResourceExhausted,
        );
        assert_eq!(one_short.used(), EXACT_WORK - 1);

        let mut exact = InterfaceConstraintBudget::with_limit(EXACT_WORK);
        validate_selection(
            &program,
            &registry,
            group,
            &selection,
            generic.interface(),
            &mut exact,
            group.span(),
        )
        .expect("the exact selected-goal work should fit");
        assert_eq!(exact.used(), EXACT_WORK);
    }

    #[test]
    fn rejects_reordered_two_parameter_substitution() {
        let program = two_parameter_program();
        let group = entry_group(&program);
        let fact = &group.implementation_facts()[0];
        let [first, second] = fact.head_parameters.as_ref() else {
            panic!("the fixture should retain two head parameters");
        };
        let goal = Type::Tuple(vec![Type::Int, Type::Bool].into_boxed_slice());
        let reordered = match_implementation_head_structurally(
            [second.id, first.id].into_iter(),
            test_type_argument(&fact.arguments()[0]),
            &goal,
            &mut InterfaceConstraintBudget::default(),
            &mut TypeWorkBudget::default(),
        )
        .expect("the reversed parameter inventory remains structurally matchable")
        .expect("the tuple head should match the concrete goal");
        let mut builder = EvidenceSelectionBuilder::new();
        let root = builder
            .push_implementation(
                fact.id,
                reordered,
                &[],
                &fact
                    .methods
                    .iter()
                    .map(|method| method.id)
                    .collect::<Vec<_>>(),
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the reordered substitution should remain representable");
        let selection = finish_width_one(builder, root, fact.interface(), goal)
            .expect("the reordered root should exist");
        let registry =
            LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                .expect("the valid linked registry should authenticate");

        assert_eq!(
            validate_selection(
                &program,
                &registry,
                group,
                &selection,
                fact.interface(),
                &mut InterfaceConstraintBudget::default(),
                group.span(),
            )
            .expect_err("substitution order is the declared head-parameter order")
            .reason(),
            EvidenceValidationReason::InvalidEvidenceRoot,
        );
    }

    #[test]
    fn rejects_reordered_prerequisites_and_a_shared_prerequisite_child() {
        let program = two_prerequisite_program();
        let group = entry_group(&program);
        let left = &group.implementation_facts()[0];
        let right = &group.implementation_facts()[1];
        let generic = &group.implementation_facts()[2];
        let owner = test_type_argument(&generic.arguments()[0])
            .outer_nominal()
            .expect("the generic implementation should retain a nominal head");
        let parameter = generic.head_parameters[0].id;
        let registry =
            LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                .expect("the valid linked registry should authenticate");

        for shared in [false, true] {
            let mut builder = EvidenceSelectionBuilder::new();
            let left_node = builder
                .push_implementation(
                    left.id,
                    Box::new([]),
                    &[],
                    &left
                        .methods
                        .iter()
                        .map(|method| method.id)
                        .collect::<Vec<_>>(),
                    &mut InterfaceConstraintBudget::default(),
                )
                .expect("the left prerequisite should fit");
            let right_node = builder
                .push_implementation(
                    right.id,
                    Box::new([]),
                    &[],
                    &right
                        .methods
                        .iter()
                        .map(|method| method.id)
                        .collect::<Vec<_>>(),
                    &mut InterfaceConstraintBudget::default(),
                )
                .expect("the right prerequisite should fit");
            let prerequisites = if shared {
                [left_node, left_node]
            } else {
                [right_node, left_node]
            };
            let root = builder
                .push_implementation(
                    generic.id,
                    single_substitution(parameter, &Type::Int),
                    &prerequisites,
                    &generic
                        .methods
                        .iter()
                        .map(|method| method.id)
                        .collect::<Vec<_>>(),
                    &mut InterfaceConstraintBudget::default(),
                )
                .expect("the malformed prerequisite relation should remain representable");
            let selection = finish_width_one(
                builder,
                root,
                generic.interface(),
                Type::apply_arguments(Type::Nominal(owner), [Type::Int]),
            )
            .expect("the malformed prerequisite root should exist");

            assert_eq!(
                validate_selection(
                    &program,
                    &registry,
                    group,
                    &selection,
                    generic.interface(),
                    &mut InterfaceConstraintBudget::default(),
                    group.span(),
                )
                .expect_err("prerequisites form an ordered, unshared evidence tree")
                .reason(),
                EvidenceValidationReason::InvalidEvidenceRoot,
            );
        }
    }

    #[test]
    fn rejects_abstract_requirement_from_another_lexical_owner() {
        let program = abstract_program();
        let group = entry_group(&program);
        let first = &group.schemes()[0];
        let second = &group.schemes()[1];
        let selection = abstract_selection(
            first.scheme.requirements[0].id,
            &group.interface_facts()[0],
            Type::Variable(first.scheme.type_parameters[0].0),
        );
        let registry =
            LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                .expect("the valid linked registry should authenticate");
        let variables = [second.scheme.type_parameters[0].0];
        let scope = EvidenceScope {
            local_scopes: &[],
            lexical_sources: &[],
            lexical_head: None,
            owner: Some(RequirementOwner::Global(second.binder)),
            variables: &variables,
        };

        let failure = validate_selection_in_scope(
            &program,
            &registry,
            group,
            &selection,
            first.scheme.requirements[0].application(),
            scope,
            &mut InterfaceConstraintBudget::default(),
            group.span(),
        )
        .expect_err("abstract evidence cannot escape its declaring global");

        assert_eq!(
            failure.reason(),
            EvidenceValidationReason::InvalidEvidenceRoot
        );
    }

    #[test]
    fn rejects_abstract_requirement_with_a_different_goal_argument() {
        let program = abstract_program();
        let group = entry_group(&program);
        let first = &group.schemes()[0];
        let selection = abstract_selection(
            first.scheme.requirements[0].id,
            &group.interface_facts()[0],
            Type::Int,
        );
        let registry =
            LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                .expect("the valid linked registry should authenticate");
        let variables = [first.scheme.type_parameters[0].0];
        let scope = EvidenceScope {
            local_scopes: &[],
            lexical_sources: &[],
            lexical_head: None,
            owner: Some(RequirementOwner::Global(first.binder)),
            variables: &variables,
        };

        let failure = validate_selection_in_scope(
            &program,
            &registry,
            group,
            &selection,
            first.scheme.requirements[0].application(),
            scope,
            &mut InterfaceConstraintBudget::default(),
            group.span(),
        )
        .expect_err("abstract evidence must retain the exact declared requirement argument");

        assert_eq!(
            failure.reason(),
            EvidenceValidationReason::InvalidEvidenceRoot
        );
    }

    #[test]
    fn rejects_a_sibling_requirement_identity_for_an_exact_selected_application() {
        let program = distinct_abstract_prerequisites_program();
        let group = entry_group(&program);
        let implementation = &group.implementation_facts()[0];
        let [selected_requirement, sibling_requirement] = implementation.prerequisites.as_ref()
        else {
            panic!("the accepted implementation should retain both distinct prerequisites");
        };
        assert_ne!(selected_requirement.id, sibling_requirement.id);
        let [body] = group.implementations() else {
            panic!("the accepted implementation body should remain linked");
        };
        let [method] = body.method_groups() else {
            panic!("the accepted implementation should retain its method group");
        };
        let [equation] = method.equations.as_ref() else {
            panic!("the accepted implementation method should retain one equation");
        };
        let ResolvedExprKind::Apply(constructor_application) = &equation.body.kind else {
            panic!("the implementation method should rebuild Wrap");
        };
        let ResolvedExprKind::Apply(method_application) = &constructor_application.argument.kind
        else {
            panic!("the Wrap argument should call the interface method");
        };
        let ResolvedExprKind::Occurrence(occurrence) = &method_application.function.kind else {
            panic!("the nested call should retain its resolved method occurrence");
        };
        let [slot] = occurrence.evidence.as_ref() else {
            panic!("the constrained method occurrence should retain one evidence slot");
        };
        let selected = slot
            .selection()
            .expect("checking should fill the constrained method occurrence");
        assert!(matches!(
            selected.node(selected.root()),
            Some(EvidenceNode::Abstract { requirement, .. })
                if requirement == selected_requirement.id
        ));

        let selected_interface = group
            .interface_facts()
            .iter()
            .find(|interface| interface.id == selected_requirement.interface())
            .expect("the selected prerequisite interface should remain linked");
        let forged = abstract_selection(
            sibling_requirement.id,
            selected_interface,
            test_type_argument(&selected_requirement.arguments()[0]).clone(),
        );
        assert_eq!(forged.interface(), selected_requirement.interface());
        assert_eq!(forged.arguments(), selected_requirement.arguments());
        let Some(EvidenceNode::Abstract {
            requirement: forged_requirement,
            methods: forged_methods,
        }) = forged.node(forged.root())
        else {
            panic!("the forged selection should retain one abstract root");
        };
        assert_eq!(forged_requirement, sibling_requirement.id);
        assert!(
            forged_methods
                .iter()
                .copied()
                .eq(selected_interface.methods.iter().map(|method| method.id))
        );
        let registry =
            LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                .expect("the valid linked registry should authenticate");
        let scope_variables = implementation
            .head_parameters
            .iter()
            .map(|parameter| parameter.id)
            .collect::<Vec<_>>();
        let scope = EvidenceScope {
            local_scopes: &[],
            lexical_sources: &[],
            lexical_head: None,
            owner: Some(RequirementOwner::Impl(implementation.id)),
            variables: &scope_variables,
        };

        assert_eq!(
            validate_selection_in_scope(
                &program,
                &registry,
                group,
                &forged,
                selected_requirement.application(),
                scope,
                &mut InterfaceConstraintBudget::default(),
                selected_requirement.span,
            )
            .expect_err("a sibling RequirementId cannot satisfy the exact selected relationship")
            .reason(),
            EvidenceValidationReason::InvalidEvidenceRoot,
        );
    }

    #[test]
    fn accepts_exact_current_implementation_when_no_abstract_requirement_matches_its_head() {
        validate_interface_evidence(abstract_priority_program())
            .expect("exact current evidence should retain its abstract prerequisite");
    }

    #[test]
    fn accepts_exact_current_implementation_with_multiple_distinct_prerequisites() {
        validate_interface_evidence(exact_current_with_distinct_prerequisites_program())
            .expect("exact current evidence should carry every distinct prerequisite relationship");
    }

    #[test]
    fn rejects_freshly_instantiated_current_implementation_at_the_selection_root() {
        let program = current_authenticity_program();
        let group = entry_group(&program);
        let leaf = &group.implementation_facts()[0];
        let current = &group.implementation_facts()[1];
        let mut builder = EvidenceSelectionBuilder::new();
        let root = forged_fresh_current_node(&mut builder, leaf, current);
        let forged = finish_width_one(
            builder,
            root,
            current.interface(),
            instantiate_single_parameter_head(current, &Type::Int),
        )
        .expect("the forged direct selection should remain structurally valid");
        let registry =
            LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                .expect("the valid linked registry should authenticate");
        let scope = EvidenceScope {
            local_scopes: &[],
            lexical_sources: &[],
            lexical_head: None,
            owner: Some(RequirementOwner::Impl(current.id)),
            variables: &current
                .head_parameters
                .iter()
                .map(|parameter| parameter.id)
                .collect::<Vec<_>>(),
        };

        assert_eq!(
            validate_selection_in_scope(
                &program,
                &registry,
                group,
                &forged,
                current.application(),
                scope,
                &mut InterfaceConstraintBudget::default(),
                current.span,
            )
            .expect_err("current evidence cannot freshly instantiate its rigid head")
            .reason(),
            EvidenceValidationReason::InvalidEvidenceRoot,
        );
    }

    #[test]
    fn rejects_freshly_instantiated_current_implementation_below_another_node() {
        let program = current_authenticity_program();
        let group = entry_group(&program);
        let leaf = &group.implementation_facts()[0];
        let current = &group.implementation_facts()[1];
        let enclosing = &group.implementation_facts()[2];
        let non_rigid_current_goal = instantiate_single_parameter_head(current, &Type::Int);
        let [enclosing_parameter] = enclosing.head_parameters.as_ref() else {
            panic!("the enclosing implementation should retain one head parameter");
        };
        let mut builder = EvidenceSelectionBuilder::new();
        let forged_current = forged_fresh_current_node(&mut builder, leaf, current);
        let root = builder
            .push_implementation(
                enclosing.id,
                single_substitution(enclosing_parameter.id, &non_rigid_current_goal),
                &[forged_current],
                &enclosing
                    .methods
                    .iter()
                    .map(|method| method.id)
                    .collect::<Vec<_>>(),
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the enclosing implementation node should fit");
        let forged = finish_width_one(
            builder,
            root,
            enclosing.interface(),
            instantiate_single_parameter_head(enclosing, &non_rigid_current_goal),
        )
        .expect("the forged nested selection should remain structurally valid");
        let registry =
            LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                .expect("the valid linked registry should authenticate");
        let scope_variables = current
            .head_parameters
            .iter()
            .map(|parameter| parameter.id)
            .collect::<Vec<_>>();
        let scope = EvidenceScope {
            local_scopes: &[],
            lexical_sources: &[],
            lexical_head: None,
            owner: Some(RequirementOwner::Impl(current.id)),
            variables: &scope_variables,
        };

        assert_eq!(
            validate_selection_in_scope(
                &program,
                &registry,
                group,
                &forged,
                enclosing.application(),
                scope,
                &mut InterfaceConstraintBudget::default(),
                enclosing.span,
            )
            .expect_err("nested current evidence cannot freshly instantiate its rigid head")
            .reason(),
            EvidenceValidationReason::InvalidEvidenceRoot,
        );
    }

    #[test]
    fn rejects_concrete_evidence_when_lexical_abstract_requirement_matches_a_goal() {
        let program = abstract_priority_program();
        let group = entry_group(&program);
        let wrapped = &group.implementation_facts()[0];
        let outer = &group.implementation_facts()[1];
        let shadowed = &group.schemes()[0];
        let [requirement] = shadowed.scheme.requirements.as_ref() else {
            panic!("the constrained global should retain one abstract requirement");
        };
        let [scope_parameter] = shadowed.scheme.type_parameters.as_ref() else {
            panic!("the constrained global should retain one type parameter");
        };
        let variables = [scope_parameter.0];
        let scope = EvidenceScope {
            local_scopes: &[],
            lexical_sources: &[],
            lexical_head: None,
            owner: Some(RequirementOwner::Global(shadowed.binder)),
            variables: &variables,
        };
        let registry =
            LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                .expect("the valid linked registry should authenticate");

        let mut direct_builder = EvidenceSelectionBuilder::new();
        let direct_root = direct_builder
            .push_implementation(
                wrapped.id,
                single_substitution(
                    wrapped.head_parameters[0].id,
                    &Type::Variable(scope_parameter.0),
                ),
                &[],
                &wrapped
                    .methods
                    .iter()
                    .map(|method| method.id)
                    .collect::<Vec<_>>(),
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the forged direct implementation node should fit");
        let direct = finish_width_one(
            direct_builder,
            direct_root,
            requirement.interface(),
            test_type_argument(&requirement.arguments()[0]).clone(),
        )
        .expect("the forged direct selection should remain structurally valid");

        let mut nested_builder = EvidenceSelectionBuilder::new();
        let nested_child = nested_builder
            .push_implementation(
                wrapped.id,
                single_substitution(
                    wrapped.head_parameters[0].id,
                    &Type::Variable(scope_parameter.0),
                ),
                &[],
                &wrapped
                    .methods
                    .iter()
                    .map(|method| method.id)
                    .collect::<Vec<_>>(),
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the forged prerequisite implementation node should fit");
        let nested_root = nested_builder
            .push_implementation(
                outer.id,
                single_substitution(
                    outer.head_parameters[0].id,
                    &Type::Variable(scope_parameter.0),
                ),
                &[nested_child],
                &outer
                    .methods
                    .iter()
                    .map(|method| method.id)
                    .collect::<Vec<_>>(),
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the enclosing implementation node should fit");
        let outer_nominal = test_type_argument(&outer.arguments()[0])
            .outer_nominal()
            .expect("the enclosing implementation should retain a nominal head");
        let nested = finish_width_one(
            nested_builder,
            nested_root,
            outer.interface(),
            Type::apply_arguments(
                Type::Nominal(outer_nominal),
                [test_type_argument(&requirement.arguments()[0]).clone()],
            ),
        )
        .expect("the forged nested selection should remain structurally valid");

        let [implementation_requirement] = outer.prerequisites.as_ref() else {
            panic!("the generic implementation should retain one abstract prerequisite");
        };
        let [implementation_parameter] = outer.head_parameters.as_ref() else {
            panic!("the generic implementation should retain one rigid parameter");
        };
        let implementation_scope = EvidenceScope {
            local_scopes: &[],
            lexical_sources: &[],
            lexical_head: None,
            owner: Some(RequirementOwner::Impl(outer.id)),
            variables: std::slice::from_ref(&implementation_parameter.id),
        };
        let mut implementation_builder = EvidenceSelectionBuilder::new();
        let implementation_root = implementation_builder
            .push_implementation(
                wrapped.id,
                single_substitution(
                    wrapped.head_parameters[0].id,
                    &Type::Variable(implementation_parameter.id),
                ),
                &[],
                &wrapped
                    .methods
                    .iter()
                    .map(|method| method.id)
                    .collect::<Vec<_>>(),
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the forged implementation-scope node should fit");
        let implementation_selection = finish_width_one(
            implementation_builder,
            implementation_root,
            implementation_requirement.interface(),
            test_type_argument(&implementation_requirement.arguments()[0]).clone(),
        )
        .expect("the forged implementation-scope selection should remain structurally valid");

        let direct_result = validate_selection_in_scope(
            &program,
            &registry,
            group,
            &direct,
            requirement.application(),
            scope,
            &mut InterfaceConstraintBudget::default(),
            requirement.span,
        );
        let nested_result = validate_selection_in_scope(
            &program,
            &registry,
            group,
            &nested,
            outer.application(),
            scope,
            &mut InterfaceConstraintBudget::default(),
            requirement.span,
        );
        let implementation_result = validate_selection_in_scope(
            &program,
            &registry,
            group,
            &implementation_selection,
            implementation_requirement.application(),
            implementation_scope,
            &mut InterfaceConstraintBudget::default(),
            implementation_requirement.span,
        );

        assert_eq!(
            [direct_result, nested_result, implementation_result]
                .map(|result| result.err().map(EvidenceValidationFailure::reason)),
            [
                Some(EvidenceValidationReason::InvalidEvidenceRoot),
                Some(EvidenceValidationReason::InvalidEvidenceRoot),
                Some(EvidenceValidationReason::InvalidEvidenceRoot),
            ],
            "each current owner rejects concrete evidence shadowed at any tree depth",
        );
    }

    #[test]
    fn identity_equal_abstract_priority_scan_has_an_exact_constraint_limit() {
        let program = abstract_priority_program();
        let group = entry_group(&program);
        let shadowed = &group.schemes()[0];
        let [requirement] = shadowed.scheme.requirements.as_ref() else {
            panic!("the constrained global should retain one abstract requirement");
        };
        let variables = [shadowed.scheme.type_parameters[0].0];
        let scope = EvidenceScope {
            local_scopes: &[],
            lexical_sources: &[],
            lexical_head: None,
            owner: Some(RequirementOwner::Global(shadowed.binder)),
            variables: &variables,
        };
        let registry =
            LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                .expect("the valid linked registry should authenticate");
        let mut measured = InterfaceConstraintBudget::default();
        assert_eq!(
            first_identity_equal_abstract_requirement(
                &program,
                &registry,
                scope,
                requirement.application(),
                &mut measured,
                requirement.span,
            )
            .expect("the exact requirement scan should fit the default budget"),
            Some(requirement.id),
        );
        let exact = measured.used();
        assert_eq!(
            exact, 8,
            "owner lookup, requirement visit, and both Wrap<A> application children are charged"
        );

        assert_eq!(
            first_identity_equal_abstract_requirement(
                &program,
                &registry,
                scope,
                requirement.application(),
                &mut InterfaceConstraintBudget::with_limit(exact - 1),
                requirement.span,
            )
            .expect_err("one unit below the exact abstract-priority scan must fail")
            .reason(),
            EvidenceValidationReason::ConstraintResourceExhausted,
        );
        assert_eq!(
            first_identity_equal_abstract_requirement(
                &program,
                &registry,
                scope,
                requirement.application(),
                &mut InterfaceConstraintBudget::with_limit(exact),
                requirement.span,
            )
            .expect("the exact abstract-priority scan budget should fit"),
            Some(requirement.id),
        );
    }

    #[test]
    fn exact_current_implementation_authentication_has_an_exact_constraint_limit() {
        // Predecessor exact-current authentication costs 87 units. Canonical
        // Kind authentication adds 15 for the Nest<Wrap<A>> root, four for the
        // retained A -> A substitution, and one for the kind-preserving pending
        // prerequisite edge, plus one complete root-application positional
        // authentication visit.
        const EXACT_WORK: usize = 87 + 15 + 4 + 1 + 1 + 2;
        let program = current_authenticity_program();
        let group = entry_group(&program);
        let current = &group.implementation_facts()[1];
        let [parameter] = current.head_parameters.as_ref() else {
            panic!("the current implementation should retain one rigid parameter");
        };
        let [requirement] = current.prerequisites.as_ref() else {
            panic!("the current implementation should retain one abstract prerequisite");
        };
        let interface = group
            .interface_facts()
            .iter()
            .find(|interface| interface.id == requirement.interface())
            .expect("the prerequisite interface should remain linked");
        let mut builder = EvidenceSelectionBuilder::new();
        let prerequisite = builder
            .push_abstract(
                requirement.id,
                &interface
                    .methods
                    .iter()
                    .map(|method| method.id)
                    .collect::<Vec<_>>(),
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the current abstract prerequisite should fit");
        let root = builder
            .push_implementation(
                current.id,
                single_substitution(parameter.id, &Type::Variable(parameter.id)),
                &[prerequisite],
                &current
                    .methods
                    .iter()
                    .map(|method| method.id)
                    .collect::<Vec<_>>(),
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the exact current implementation node should fit");
        let selection = finish_width_one(
            builder,
            root,
            current.interface(),
            test_type_argument(&current.arguments()[0]).clone(),
        )
        .expect("the exact current selection should remain structurally valid");
        let registry =
            LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                .expect("the valid linked registry should authenticate");
        let scope_variables = current
            .head_parameters
            .iter()
            .map(|parameter| parameter.id)
            .collect::<Vec<_>>();
        let scope = EvidenceScope {
            local_scopes: &[],
            lexical_sources: &[],
            lexical_head: None,
            owner: Some(RequirementOwner::Impl(current.id)),
            variables: &scope_variables,
        };
        let mut measured = InterfaceConstraintBudget::default();
        validate_selection_in_scope(
            &program,
            &registry,
            group,
            &selection,
            current.application(),
            scope,
            &mut measured,
            current.span,
        )
        .expect("exact current authentication should fit the default budget");
        let exact = measured.used();
        assert_eq!(
            exact, EXACT_WORK,
            "exact-current relationships and every retained Kind judgment are charged"
        );

        assert_eq!(
            validate_selection_in_scope(
                &program,
                &registry,
                group,
                &selection,
                current.application(),
                scope,
                &mut InterfaceConstraintBudget::with_limit(exact - 1),
                current.span,
            )
            .expect_err("one unit below exact current authentication must fail")
            .reason(),
            EvidenceValidationReason::ConstraintResourceExhausted,
        );
        validate_selection_in_scope(
            &program,
            &registry,
            group,
            &selection,
            current.application(),
            scope,
            &mut InterfaceConstraintBudget::with_limit(exact),
            current.span,
        )
        .expect("the exact current-authentication budget should fit");
    }

    #[test]
    fn rejects_inference_forall_and_out_of_scope_type_escape_in_selected_goals() {
        let program = local_program();
        let group = entry_group(&program);
        let fact = &group.implementation_facts()[0];
        let methods = fact
            .methods
            .iter()
            .map(|method| method.id)
            .collect::<Vec<_>>();
        let registry =
            LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                .expect("the valid linked registry should authenticate");
        let malformed = [
            Type::Inference(InferenceVariableId::new(0)),
            Type::Forall(Box::new([]), Box::new(Type::Int)),
            Type::Variable(TypeVariableId::generated(99)),
        ];

        for argument in malformed {
            let mut builder = EvidenceSelectionBuilder::new();
            let root = builder
                .push_implementation(
                    fact.id,
                    Box::new([]),
                    &[],
                    &methods,
                    &mut InterfaceConstraintBudget::default(),
                )
                .expect("the malformed type fixture should fit");
            let selection = finish_width_one(builder, root, fact.interface(), argument)
                .expect("the malformed root should remain representable before validation");
            let failure = validate_selection(
                &program,
                &registry,
                group,
                &selection,
                fact.interface(),
                &mut InterfaceConstraintBudget::default(),
                group.span(),
            )
            .expect_err("unchecked type state cannot escape into evidence lowering");
            assert_eq!(
                failure.reason(),
                EvidenceValidationReason::InvalidEvidenceRoot
            );
        }
    }

    #[test]
    fn rejects_unknown_nominal_identity_and_wrong_nominal_arity_in_selected_goals() {
        let program = generic_program();
        let group = entry_group(&program);
        let ground = &group.implementation_facts()[0];
        let generic = &group.implementation_facts()[1];
        let owner = test_type_argument(&generic.arguments()[0])
            .outer_nominal()
            .expect("the generic fixture should retain its nominal head");
        let methods = ground
            .methods
            .iter()
            .map(|method| method.id)
            .collect::<Vec<_>>();
        let malformed = [
            Type::Nominal(NominalTypeId::new(group.module(), 99)),
            Type::Nominal(owner),
            Type::apply_arguments(Type::Nominal(owner), [Type::Int, Type::Bool]),
        ];
        let registry =
            LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                .expect("the valid linked registry should authenticate");

        for argument in malformed {
            let selection = implementation_selection(ground.id, ground.interface(), &methods);
            let mut builder = EvidenceSelectionBuilder::new();
            let root = builder
                .push_implementation(
                    ground.id,
                    Box::new([]),
                    &[],
                    &methods,
                    &mut InterfaceConstraintBudget::default(),
                )
                .expect("the malformed nominal fixture should fit");
            let malformed = finish_width_one(builder, root, selection.interface(), argument)
                .expect("the malformed nominal root should remain representable");
            assert_eq!(
                validate_selection(
                    &program,
                    &registry,
                    group,
                    &malformed,
                    ground.interface(),
                    &mut InterfaceConstraintBudget::default(),
                    group.span(),
                )
                .expect_err("nominal identity and saturation must authenticate")
                .reason(),
                EvidenceValidationReason::InvalidEvidenceRoot,
            );
        }
    }

    #[test]
    fn rejects_unreachable_nodes_in_a_flat_evidence_plan() {
        let program = local_program();
        let group = entry_group(&program);
        let fact = &group.implementation_facts()[0];
        let methods = fact
            .methods
            .iter()
            .map(|method| method.id)
            .collect::<Vec<_>>();
        let mut builder = EvidenceSelectionBuilder::new();
        builder
            .push_implementation(
                fact.id,
                Box::new([]),
                &[],
                &methods,
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the unreachable node should remain representable");
        let root = builder
            .push_implementation(
                fact.id,
                Box::new([]),
                &[],
                &methods,
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the root node should fit");
        let selection = finish_width_one(builder, root, fact.interface(), Type::Int)
            .expect("the root should exist");
        let registry =
            LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                .expect("the valid linked registry should authenticate");

        assert_eq!(
            validate_selection(
                &program,
                &registry,
                group,
                &selection,
                fact.interface(),
                &mut InterfaceConstraintBudget::default(),
                group.span(),
            )
            .expect_err("every retained evidence node must be reachable exactly once")
            .reason(),
            EvidenceValidationReason::InvalidEvidenceRoot,
        );
    }

    #[test]
    fn rejects_unknown_selected_impl_identity_before_core() {
        let program = local_program();
        let group = entry_group(&program);
        let fact = &group.implementation_facts()[0];
        let unknown_implementation = ImplId::new(group.module(), 99);
        let selection = implementation_selection(unknown_implementation, fact.interface(), &[]);
        let registry =
            LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                .expect("the valid linked registry should authenticate");

        let failure = validate_selection(
            &program,
            &registry,
            group,
            &selection,
            fact.interface(),
            &mut InterfaceConstraintBudget::default(),
            group.span(),
        )
        .expect_err("the unknown implementation identity should fail before Core");

        assert_eq!(failure.reason(), EvidenceValidationReason::UnknownIdentity);
    }

    #[test]
    fn rejects_hidden_implementation_method_binder_reused_by_a_global() {
        let mut program = local_program();
        let group = entry_group(&program);
        let module = group.module();
        let global = group.schemes()[0].binder;
        assert!(program.replace_first_implementation_method_binder_for_test(module, global));

        let failure = validate_interface_evidence(program)
            .expect_err("a hidden implementation method cannot reuse a global binder identity");

        assert_eq!(failure.reason(), EvidenceValidationReason::UnknownIdentity);
    }

    #[test]
    fn rejects_interface_identity_with_a_non_source_declaration_ordinal() {
        let mut program = local_program();
        let module = entry_group(&program).module();
        assert!(
            program.replace_first_interface_fact_id_for_test(module, InterfaceId::new(module, 99),)
        );

        let failure = validate_interface_evidence(program)
            .expect_err("an interface fact must use its category-local source ordinal");

        assert_eq!(failure.reason(), EvidenceValidationReason::UnknownIdentity);
    }

    #[test]
    fn rejects_method_identity_with_a_non_source_declaration_ordinal() {
        let mut program = local_program();
        let group = entry_group(&program);
        let module = group.module();
        let interface = group.interface_facts()[0].id;
        assert!(
            program
                .replace_first_interface_method_id_for_test(module, MethodId::new(interface, 99),)
        );

        let failure = validate_interface_evidence(program)
            .expect_err("a method fact must use its interface-local source ordinal");

        assert_eq!(failure.reason(), EvidenceValidationReason::UnknownIdentity);
    }

    #[test]
    fn rejects_implementation_identity_with_a_non_source_declaration_ordinal() {
        let mut program = local_program();
        let module = entry_group(&program).module();
        assert!(
            program.replace_first_implementation_fact_id_for_test(module, ImplId::new(module, 99),)
        );

        let failure = validate_interface_evidence(program)
            .expect_err("an implementation fact must use its category-local source ordinal");

        assert_eq!(failure.reason(), EvidenceValidationReason::UnknownIdentity);
    }

    #[test]
    fn rejects_two_hidden_implementation_methods_reusing_one_binder() {
        let mut program = entry_program(concat!(
            "interface Transform<A> {\n",
            "first : A -> A\n",
            "second : A -> A\n",
            "}\n\n",
            "impl Transform<Int> {\n",
            "first value = value\n",
            "second value = value\n",
            "}\n\n",
            "main : Unit -> Int\nmain () = first 1\n",
        ));
        let module = entry_group(&program).module();
        assert!(program.reuse_first_implementation_method_binder_for_test(module));

        let failure = validate_interface_evidence(program)
            .expect_err("distinct hidden implementation methods require distinct binders");

        assert_eq!(failure.reason(), EvidenceValidationReason::UnknownIdentity);
    }

    #[test]
    fn rejects_missing_and_reordered_same_typed_implementation_method_slots() {
        let program = entry_program(concat!(
            "interface Transform<A> {\n",
            "first : A -> A\n",
            "second : A -> A\n",
            "}\n\n",
            "impl Transform<Int> {\n",
            "first value = value + 1\n",
            "second value = value * 2\n",
            "}\n\n",
            "main : Unit -> Int\nmain () = first 1\n",
        ));
        let group = entry_group(&program);
        let fact = &group.implementation_facts()[0];
        let [first, second] = fact.methods.as_ref() else {
            panic!("the implementation should retain two same-typed method slots");
        };
        let registry =
            LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                .expect("the valid linked registry should authenticate");

        for methods in [vec![first.id], vec![second.id, first.id]] {
            let mut builder = EvidenceSelectionBuilder::new();
            let root = builder
                .push_implementation(
                    fact.id,
                    Box::new([]),
                    &[],
                    &methods,
                    &mut InterfaceConstraintBudget::default(),
                )
                .expect("the malformed slot sequence should remain representable");
            let selection = finish_width_one(builder, root, fact.interface(), Type::Int)
                .expect("the malformed root should remain representable before validation");

            assert_eq!(
                validate_selection(
                    &program,
                    &registry,
                    group,
                    &selection,
                    fact.interface(),
                    &mut InterfaceConstraintBudget::default(),
                    group.span(),
                )
                .expect_err("same-typed implementation method slots remain complete and ordered")
                .reason(),
                EvidenceValidationReason::InvalidEvidenceRoot,
            );
        }
    }

    #[test]
    fn rejects_selected_impl_unavailable_in_occurrence_module() {
        let fixture = ValidationFixture::create(concat!(
            "import middle as Middle\n",
            "main : Unit -> Unit\nmain () = Middle.unit(())\n",
        ));
        fixture.write(
            "middle.ash",
            concat!(
                "import leaf as Leaf\n",
                "pub unit : Unit -> Unit\nunit value = value\n",
            ),
        );
        fixture.write(
            "leaf.ash",
            concat!(
                "pub interface Equal<A> {\nequal : (A, A) -> Bool\n}\n\n",
                "pub impl Equal<Int> {\nequal (left, right) = left == right\n}\n",
            ),
        );
        let graph = fixture.graph();
        let program = link_modules(check_graph(&graph), graph.entry())
            .expect("the transitive fixture should link");
        let entry = program
            .groups()
            .iter()
            .find(|group| group.module() == graph.entry())
            .expect("the linked graph should retain its entry group");
        let fact = program
            .groups()
            .iter()
            .flat_map(ResolvedModuleGroup::implementation_facts)
            .next()
            .expect("the leaf implementation should be linked");
        let methods = fact
            .methods
            .iter()
            .map(|method| method.id)
            .collect::<Vec<_>>();
        let selection = implementation_selection(fact.id, fact.interface(), &methods);
        let registry =
            LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                .expect("the valid linked registry should authenticate");

        let failure = validate_selection(
            &program,
            &registry,
            entry,
            &selection,
            fact.interface(),
            &mut InterfaceConstraintBudget::default(),
            entry.span(),
        )
        .expect_err(
            "an implementation without an explicit selector should be unavailable in the entry module",
        );

        assert_eq!(
            failure.reason(),
            EvidenceValidationReason::UnavailableImplementation
        );
        let sources = graph
            .modules()
            .iter()
            .map(|module| module.source())
            .collect::<Vec<_>>();
        let diagnostic = crate::presentation::compile_evidence_failure(&failure, &sources).unwrap();
        for locale in [
            crate::message::Locale::English,
            crate::message::Locale::Bulgarian,
        ] {
            crate::presentation::write_human(
                &mut Vec::new(),
                &diagnostic,
                &crate::message::Catalogue::new(locale).unwrap(),
            )
            .unwrap();
        }
    }

    #[test]
    fn rejects_imported_implementation_route_without_its_exact_direct_edge() {
        let fixture = ValidationFixture::create(concat!(
            "import dependency as Dependency\n",
            "import dependency (impl Equal)\n",
            "main : Unit -> Bool\nmain () = Dependency.equal((1, 1))\n",
        ));
        fixture.write(
            "dependency.ash",
            concat!(
                "pub interface Equal<A> {\nequal : (A, A) -> Bool\n}\n\n",
                "pub impl Equal<Int> {\nequal (left, right) = left == right\n}\n",
            ),
        );
        let graph = fixture.graph();
        let mut program = link_modules(check_graph(&graph), graph.entry())
            .expect("the direct-import fixture should link");
        let entry = program
            .groups()
            .iter()
            .find(|group| group.module() == graph.entry())
            .expect("the linked graph should retain its entry group");
        let implementation = entry.available_implementations()[0].id();
        let wrong_span = entry.span();
        assert!(program.replace_available_route_for_test(
            graph.entry(),
            implementation,
            ImplementationRoute::DirectImport {
                direct_dependency: implementation.module(),
                available_at: wrong_span,
            },
        ));

        let failure = validate_interface_evidence(program)
            .expect_err("a forged route without its exact authenticated edge must fail");

        assert_eq!(failure.reason(), EvidenceValidationReason::UnknownIdentity);
    }

    #[test]
    fn rejects_a_forged_reexport_authorization_hop() {
        let mut program = reexport_program();
        let (base, _facade, entry) = reexport_groups(&program);
        let base_module = base.module();
        let entry_module = entry.module();
        let entry_span = entry.span();
        let [available] = entry.available_implementations() else {
            panic!("the entry should retain one selected implementation");
        };
        let implementation = available.id();
        let import_span = available.authorization().hops()[0].import_span;

        assert!(program.replace_available_authorization_hops_for_test(
            entry_module,
            implementation,
            vec![ImplementationRouteHop {
                from: entry_module,
                to: base_module,
                import_span,
            }],
        ));
        let failure = validate_interface_evidence(program)
            .expect_err("availability cannot skip its immediate publishing dependency");
        assert_eq!(failure.reason(), EvidenceValidationReason::UnknownIdentity);
        assert_eq!(failure.primary(), entry_span);
    }

    #[test]
    fn rejects_a_forged_intermediate_public_authorization_suffix() {
        let mut program = deep_reexport_program();
        let (_base, facade, _entry) = reexport_groups(&program);
        let facade_module = facade.module();
        let facade_span = facade.span();
        let [published] = facade.public_implementation_authorizations() else {
            panic!("the facade should publish one implementation");
        };
        let implementation = published.id();
        let mut forged = published.authorization().hops().to_vec();
        assert_eq!(forged.len(), 2);
        forged[1].import_span = facade_span;

        assert!(program.replace_public_authorization_hops_for_test(
            facade_module,
            implementation,
            forged,
        ));
        let failure = validate_interface_evidence(program)
            .expect_err("an intermediate public suffix must match the authenticated dependency");
        assert_eq!(failure.reason(), EvidenceValidationReason::UnknownIdentity);
        assert_eq!(failure.primary(), facade_span);
    }

    #[test]
    fn rejects_an_unused_forged_public_authorization_before_occurrences() {
        let mut program = dual_reexport_program();
        let (base, facade, entry) = reexport_groups(&program);
        let unused_implementation = base.implementation_facts()[1].id;
        let selected_implementation = entry.available_implementations()[0].id();
        assert_ne!(unused_implementation, selected_implementation);
        let facade_module = facade.module();
        let facade_span = facade.span();
        let unused = facade
            .public_implementation_authorizations()
            .iter()
            .find(|authorization| authorization.id() == unused_implementation)
            .expect("the facade should publish the unused implementation");
        let mut forged = unused.authorization().hops().to_vec();
        forged[0].import_span = facade_span;

        assert!(program.replace_public_authorization_hops_for_test(
            facade_module,
            unused_implementation,
            forged,
        ));
        let failure = validate_interface_evidence(program)
            .expect_err("every public authorization must authenticate before occurrences");
        assert_eq!(failure.reason(), EvidenceValidationReason::UnknownIdentity);
        assert_eq!(failure.primary(), facade_span);
    }

    #[test]
    fn rejects_a_forged_public_authorization_hop_span() {
        let mut program = reexport_program();
        let (_base, _facade, entry) = reexport_groups(&program);
        let entry_module = entry.module();
        let entry_span = entry.span();
        let [published] = entry.public_implementation_authorizations() else {
            panic!("the entry should publish one implementation");
        };
        let implementation = published.id();
        let mut hops = published.authorization().hops().to_vec();
        hops[0].import_span = entry_span;

        assert!(program.replace_public_authorization_hops_for_test(
            entry_module,
            implementation,
            hops,
        ));
        let failure = validate_interface_evidence(program)
            .expect_err("a public route must retain the exact first-hop import span");
        assert_eq!(failure.reason(), EvidenceValidationReason::UnknownIdentity);
        assert_eq!(failure.primary(), entry_span);
    }

    #[test]
    fn rejects_a_public_authorization_with_a_forged_final_owner() {
        let mut program = reexport_program();
        let (_base, facade, entry) = reexport_groups(&program);
        let entry_module = entry.module();
        let entry_span = entry.span();
        let facade_module = facade.module();
        let [published] = entry.public_implementation_authorizations() else {
            panic!("the entry should publish one implementation");
        };
        let implementation = published.id();
        let mut hops = published.authorization().hops().to_vec();
        hops[1].to = facade_module;

        assert!(program.replace_public_authorization_hops_for_test(
            entry_module,
            implementation,
            hops,
        ));
        let failure = validate_interface_evidence(program)
            .expect_err("the complete public route must terminate at the defining owner");
        assert_eq!(failure.reason(), EvidenceValidationReason::UnknownIdentity);
        assert_eq!(failure.primary(), entry_span);
    }

    #[test]
    fn rejects_a_disconnected_public_authorization_route() {
        let mut program = reexport_program();
        let (_base, _facade, entry) = reexport_groups(&program);
        let entry_module = entry.module();
        let entry_span = entry.span();
        let [published] = entry.public_implementation_authorizations() else {
            panic!("the entry should publish one implementation");
        };
        let implementation = published.id();
        let mut hops = published.authorization().hops().to_vec();
        hops[1].from = entry_module;

        assert!(program.replace_public_authorization_hops_for_test(
            entry_module,
            implementation,
            hops,
        ));
        let failure = validate_interface_evidence(program)
            .expect_err("a public authorization route must remain connected");
        assert_eq!(failure.reason(), EvidenceValidationReason::UnknownIdentity);
        assert_eq!(failure.primary(), entry_span);
    }

    #[test]
    fn rejects_a_repeated_public_authorization_route() {
        let mut program = reexport_program();
        let (_base, _facade, entry) = reexport_groups(&program);
        let entry_module = entry.module();
        let entry_span = entry.span();
        let [published] = entry.public_implementation_authorizations() else {
            panic!("the entry should publish one implementation");
        };
        let implementation = published.id();
        let mut hops = published.authorization().hops().to_vec();
        hops[1].to = entry_module;

        assert!(program.replace_public_authorization_hops_for_test(
            entry_module,
            implementation,
            hops,
        ));
        let failure = validate_interface_evidence(program)
            .expect_err("a public authorization route cannot return to a later group");
        assert_eq!(failure.reason(), EvidenceValidationReason::UnknownIdentity);
        assert_eq!(failure.primary(), entry_span);
    }

    #[test]
    fn rejects_dependency_private_implementation_forged_into_importer_availability() {
        let fixture = ValidationFixture::create(concat!(
            "import dependency as Dependency\n",
            "import dependency (impl Equal)\n",
            "main : Unit -> Unit\nmain () = ()\n",
        ));
        fixture.write(
            "dependency.ash",
            concat!(
                "pub interface Equal<A> {\nequal : (A, A) -> Bool\n}\n\n",
                "impl Equal<Int> {\nequal (left, right) = left == right\n}\n\n",
                "pub impl Equal<Bool> {\nequal (left, right) = left\n}\n",
            ),
        );
        let graph = fixture.graph();
        let mut program = link_modules(check_graph(&graph), graph.entry())
            .expect("the direct-import fixture should link");
        let dependency = program
            .groups()
            .iter()
            .find(|group| {
                group
                    .implementations()
                    .iter()
                    .any(|implementation| !implementation.source().public)
            })
            .expect("the dependency group should remain linked");
        let private = dependency
            .implementations()
            .iter()
            .find(|implementation| !implementation.source().public)
            .expect("the dependency should retain its private implementation")
            .id();
        let entry = program
            .groups()
            .iter()
            .find(|group| group.module() == graph.entry())
            .expect("the entry group should remain linked");
        let [published] = entry.available_implementations() else {
            panic!("only the dependency's public implementation should be available");
        };

        assert!(program.replace_available_implementation_id_for_test(
            graph.entry(),
            published.id(),
            private,
        ));
        assert_eq!(
            validate_interface_evidence(program)
                .expect_err("a dependency-private implementation cannot acquire an import route")
                .reason(),
            EvidenceValidationReason::UnknownIdentity,
        );
    }

    #[test]
    fn linked_registry_entries_have_an_exact_constraint_limit() {
        let program = local_program();
        let mut measured = InterfaceConstraintBudget::default();
        drop(
            LinkedInterfaceRegistry::build(&program, &mut measured)
                .expect("the linked registry should fit the default budget"),
        );
        let limit = measured.used();
        // Complete registry construction includes canonical service facts and
        // full row-bearing schemes; this donor owns the whole build boundary.
        assert!(limit > 0);
        let group = entry_group(&program);
        let [interface] = group.interface_facts() else {
            panic!("original Equal")
        };
        assert_eq!(interface.parameters.len(), 1);
        assert_eq!(interface.parameters[0].spelling, "A");
        assert_eq!(interface.parameters[0].kind, Kind::Type);
        let [implementation] = group.implementation_facts() else {
            panic!("original Int implementation")
        };
        assert_eq!(implementation.interface(), interface.id);
        assert_eq!(
            implementation.arguments(),
            [KindedArgument::TypeArg(Type::Int)]
        );
        assert_eq!(
            LinkedInterfaceRegistry::build(
                &program,
                &mut InterfaceConstraintBudget::with_limit(limit - 1),
            )
            .expect_err("one unit below the measured registry work should fail")
            .reason(),
            EvidenceValidationReason::ConstraintResourceExhausted,
        );
        LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::with_limit(limit))
            .expect("the exact linked-registry budget should fit");
    }

    #[test]
    fn deep_authorization_suffix_comparison_has_an_exact_limit() {
        const HOPS: usize = 20_000;

        let program = local_program();
        let span = program.result().span;
        let dependency_hops = (0..HOPS)
            .map(|index| ImplementationRouteHop {
                from: ModuleId::new(
                    u32::try_from(index + 1).expect("the route fixture ordinal should fit"),
                ),
                to: ModuleId::new(
                    u32::try_from(index + 2).expect("the route fixture ordinal should fit"),
                ),
                import_span: span,
            })
            .collect::<Vec<_>>();
        let dependency = ImplementationAuthorization::from_hops(dependency_hops.clone());
        let mut authorization_hops = Vec::with_capacity(HOPS + 1);
        authorization_hops.push(ImplementationRouteHop {
            from: ModuleId::new(0),
            to: ModuleId::new(1),
            import_span: span,
        });
        authorization_hops.extend_from_slice(&dependency_hops);
        let authorization = ImplementationAuthorization::from_hops(authorization_hops);

        let mut measured = InterfaceConstraintBudget::default();
        assert!(
            authorization_suffix_matches(&authorization, &dependency, &mut measured, span)
                .expect("the matching deep suffix should fit the default budget")
        );
        assert_eq!(
            measured.used(),
            HOPS + 1,
            "one length check and every suffix hop comparison are charged"
        );

        assert_eq!(
            authorization_suffix_matches(
                &authorization,
                &dependency,
                &mut InterfaceConstraintBudget::with_limit(HOPS),
                span,
            )
            .expect_err("one unit below the exact suffix work must exhaust the budget")
            .reason(),
            EvidenceValidationReason::ConstraintResourceExhausted,
        );
        assert!(
            authorization_suffix_matches(
                &authorization,
                &dependency,
                &mut InterfaceConstraintBudget::with_limit(HOPS + 1),
                span,
            )
            .expect("the exact suffix comparison budget should fit")
        );

        let mut mismatched_hops = dependency_hops;
        mismatched_hops
            .last_mut()
            .expect("the deep suffix should contain a final hop")
            .to = ModuleId::new(u32::MAX);
        let mismatch = ImplementationAuthorization::from_hops(mismatched_hops);
        let mut exact_mismatch = InterfaceConstraintBudget::with_limit(HOPS + 1);
        assert!(
            !authorization_suffix_matches(&authorization, &mismatch, &mut exact_mismatch, span,)
                .expect("the exact mismatch comparison budget should fit")
        );
        assert_eq!(exact_mismatch.used(), HOPS + 1);
    }

    #[test]
    fn one_constraint_budget_continues_from_linking_through_validation() {
        let fixture = ValidationFixture::create(concat!(
            "interface Equal<A> {\nequal : (A, A) -> Bool\n}\n\n",
            "impl Equal<Int> {\nequal (left, right) = left == right\n}\n\n",
            "main : Unit -> Bool\nmain () = equal((1, 1))\n",
        ));
        let graph = fixture.graph();
        let mut measured = InterfaceConstraintBudget::default();
        let linked = link_modules_with_budget(check_graph(&graph), graph.entry(), &mut measured)
            .expect("the checked local graph should link");
        let link_used = measured.used();
        // Wrapper19, combined registry index39 and six occupied map slots,
        // followed by group-lowering lookups of two, three and four units.
        const LINK_PREFIX_WORK: usize = 19 + 39 + 6 + 2 + 3 + 4;
        // Registry indexes and actual entry composition add 35 and 7 units.
        const LINK_AND_VALIDATION_WORK: usize = LINK_PREFIX_WORK + 35 + 7;
        assert_eq!(graph.modules().len(), 3);
        assert_eq!(linked.groups().len(), 3);
        assert_eq!(linked.registry().nominals().len(), 5);
        assert_eq!(linked.registry().constructors().len(), 5);
        assert_eq!(linked.registry().type_variable_count(), 3);
        assert_eq!(link_used, LINK_PREFIX_WORK);
        drop(
            validate_interface_evidence_with_budget(
                linked,
                &mut measured,
                &mut TypeWorkBudget::default(),
            )
            .expect("the linked evidence should validate on the same budget"),
        );
        let total = measured.used();
        assert_eq!(total, LINK_AND_VALIDATION_WORK);

        let mut one_short = InterfaceConstraintBudget::with_limit(total - 1);
        let linked = link_modules_with_budget(check_graph(&graph), graph.entry(), &mut one_short)
            .expect("the full link prefix should fit below the total validation boundary");
        assert_eq!(one_short.used(), link_used);
        assert_eq!(
            validate_interface_evidence_with_budget(
                linked,
                &mut one_short,
                &mut TypeWorkBudget::default(),
            )
            .expect_err("one unit below the combined boundary must fail in validation")
            .reason(),
            EvidenceValidationReason::ConstraintResourceExhausted,
        );
        assert_eq!(one_short.used(), LINK_AND_VALIDATION_WORK - 1);

        let mut exact = InterfaceConstraintBudget::with_limit(total);
        let linked = link_modules_with_budget(check_graph(&graph), graph.entry(), &mut exact)
            .expect("the exact combined boundary should admit linking");
        drop(
            validate_interface_evidence_with_budget(
                linked,
                &mut exact,
                &mut TypeWorkBudget::default(),
            )
            .expect("the exact combined boundary should admit validation"),
        );
        assert_eq!(exact.used(), total);
    }

    #[test]
    fn link_exposes_exact_independent_combined_registry_ledgers() {
        // Wrapper19, registry index40, six map slots, and group lookups2+3+4.
        const CONSTRAINT_WORK: usize = 19 + 40 + 6 + 2 + 3 + 4;
        // Atomic retained storage62; DefaultAlloc owner5/signature2 and
        // Equal owner5/signature3 retain their already-checked records.
        const TYPE_RETENTION_WORK: usize = 62;
        const TYPE_WORK: usize = TYPE_RETENTION_WORK + 5 + 2 + 5 + 3;
        const REGISTRY_CONSTRAINT_PREFIX: usize = 19 + 40 + 6;
        let fixture = ValidationFixture::create(concat!(
            "interface Equal<A> {\nequal<B> : (A, B) -> Bool\n}\n\n",
            "impl Equal<Int> {\nequal (left, ignored) = left == left\n}\n\n",
            "main : Unit -> Bool\nmain () = equal((1, true))\n",
        ));
        let graph = fixture.graph();
        let mut constraint_short = InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK - 1);
        let mut retained_type = TypeWorkBudget::with_limit(TYPE_WORK);
        let constraint_failure = link_modules_with_budgets(
            check_graph(&graph),
            graph.entry(),
            &mut constraint_short,
            &mut retained_type,
        )
        .expect_err("one missing entry group lookup cell must reject linking");
        assert_eq!(
            constraint_failure,
            crate::elaborate::TypeError::Internal(
                crate::elaborate::ElaborationFailure::ConstraintResourceExhausted,
            ),
        );
        assert_eq!(constraint_short.used(), CONSTRAINT_WORK - 4);
        assert_eq!(retained_type.used(), TYPE_WORK);

        // Retained storage is one atomic 62-cell precharge.
        let mut atomic_constraint = InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK);
        let mut atomic_type = TypeWorkBudget::with_limit(TYPE_RETENTION_WORK - 1);
        assert_eq!(
            link_modules_with_budgets(
                check_graph(&graph),
                graph.entry(),
                &mut atomic_constraint,
                &mut atomic_type
            )
            .expect_err("one missing physical-retention cell rejects before storage"),
            crate::elaborate::TypeError::Internal(
                crate::elaborate::ElaborationFailure::TypeResourceExhausted
            )
        );
        assert_eq!(atomic_constraint.used(), REGISTRY_CONSTRAINT_PREFIX);
        assert_eq!(atomic_type.used(), 0);

        let mut constraint = InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK);
        let mut type_short = TypeWorkBudget::with_limit(TYPE_WORK - 1);
        let type_failure = link_modules_with_budgets(
            check_graph(&graph),
            graph.entry(),
            &mut constraint,
            &mut type_short,
        )
        .expect_err("one missing combined-registry retention cell must reject linking");
        assert_eq!(
            type_failure,
            crate::elaborate::TypeError::Internal(
                crate::elaborate::ElaborationFailure::TypeResourceExhausted,
            ),
        );
        assert_eq!(constraint.used(), REGISTRY_CONSTRAINT_PREFIX);
        assert_eq!(type_short.used(), TYPE_WORK - 1);

        for _ in 0..2 {
            let mut constraint = InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK);
            let mut type_work = TypeWorkBudget::with_limit(TYPE_WORK);
            let linked = link_modules_with_budgets(
                check_graph(&graph),
                graph.entry(),
                &mut constraint,
                &mut type_work,
            )
            .expect("the exact independent link budgets should fit reproducibly");
            assert_eq!(constraint.used(), CONSTRAINT_WORK);
            assert_eq!(type_work.used(), TYPE_WORK);
            let registry = linked.registry();
            assert_eq!(linked.groups().len(), 3);
            assert_eq!(registry.nominals().len(), 5);
            assert_eq!(registry.constructors().len(), 5);
            assert!(
                registry
                    .constructors()
                    .iter()
                    .all(|constructor| constructor.payload.is_none())
            );
            assert_eq!(registry.type_variable_count(), 4);
            assert!(
                registry
                    .type_variables()
                    .all(|parameter| parameter.kind == Kind::Type)
            );
            let effects = registry.effects();
            let [effect] = effects else {
                panic!("canonical DefaultAlloc only")
            };
            assert!(effect.id.module().is_builtin_region());
            assert!(effect.parameters.is_empty());
            assert_eq!(effect.operations.len(), 2);
            for operation in &effect.operations {
                assert!(
                    matches!(operation.annotation.ty, Type::Function(_, _)),
                    "operation outer arrows remain plain"
                );
                let mut cells = TypeWorkBudget::unbounded();
                crate::types::charge_type_cells(&operation.annotation.ty, &mut cells).unwrap();
                assert_eq!(cells.used(), 3);
            }
            let group = entry_group(&linked);
            let [interface] = group.interface_facts() else {
                panic!("Equal owner")
            };
            let [parameter] = interface.parameters.as_ref() else {
                panic!("Equal A")
            };
            assert_eq!(parameter.spelling, "A");
            let [method] = interface.methods.as_ref() else {
                panic!("original equal method")
            };
            let [method_parameter] = method.type_parameters() else {
                panic!("method B")
            };
            assert_eq!(method_parameter.spelling, "B");
            assert_ne!(parameter.id, method_parameter.id);
            assert!(group.public_implementation_authorizations().is_empty());
            drop(linked);
        }
    }

    #[test]
    fn evidence_node_validation_has_an_exact_constraint_limit() {
        // The predecessor node proof costs sixteen units; K-Interface-Argument
        // for the selected Int goal adds two synthesis cells and one Kind cell.
        const EXACT_WORK: usize = 16 + 3 + 8;
        let program = local_program();
        let group = entry_group(&program);
        let fact = &group.implementation_facts()[0];
        let methods = fact
            .methods
            .iter()
            .map(|method| method.id)
            .collect::<Vec<_>>();
        let selection = implementation_selection(fact.id, fact.interface(), &methods);
        let registry =
            LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                .expect("the valid linked registry should authenticate");
        let mut measured = InterfaceConstraintBudget::default();
        validate_selection(
            &program,
            &registry,
            group,
            &selection,
            fact.interface(),
            &mut measured,
            group.span(),
        )
        .expect("the valid selected node should authenticate");
        let limit = measured.used();
        assert_eq!(
            limit, EXACT_WORK,
            "root goal, Kind, node, exact head, method slot, and availability are charged"
        );

        assert_eq!(
            validate_selection(
                &program,
                &registry,
                group,
                &selection,
                fact.interface(),
                &mut InterfaceConstraintBudget::with_limit(limit - 1),
                group.span(),
            )
            .expect_err("one unit below the measured node work should fail")
            .reason(),
            EvidenceValidationReason::ConstraintResourceExhausted,
        );
        validate_selection(
            &program,
            &registry,
            group,
            &selection,
            fact.interface(),
            &mut InterfaceConstraintBudget::with_limit(limit),
            group.span(),
        )
        .expect("the exact node-validation budget should fit");
    }

    #[test]
    fn linked_selection_accepts_a_specific_closed_effectful_implementation_head() {
        let mut program = entry_program(concat!(
            "effect Probe<A> {\n",
            "    call : A -> Bool\n",
            "}\n\n",
            "interface Equal<A> {\n",
            "    equal : (A, A) -> Bool\n",
            "}\n\n",
            "impl Equal<Int> {\n",
            "    equal (left, right) = left == right\n",
            "}\n\n",
            "main : Unit -> Bool\n",
            "main () = equal((1, 1))\n",
        ));
        let module = entry_group(&program).module();
        let effect = program
            .registry()
            .effects()
            .iter()
            .find(|effect| effect.id.module() == program.entry() && effect.spelling == "Probe")
            .expect("Probe");
        assert_eq!(effect.spelling, "Probe");
        let effect_id = effect.id;
        let closed = Type::function_computation(
            Type::Unit,
            crate::types::ComputationType::new(
                Type::Bool,
                crate::types::EffectRow::singleton(crate::types::EffectInstance::new(
                    effect_id,
                    Box::new([Type::Int]),
                )),
            ),
        );
        let registry =
            LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                .expect(
                    "the linked registry should authenticate before the retained head mutation",
                );
        assert!(program.replace_first_implementation_argument_for_test(module, closed.clone()));
        let group = entry_group(&program);
        let fact = &group.implementation_facts()[0];
        let methods = fact
            .methods
            .iter()
            .map(|method| method.id)
            .collect::<Vec<_>>();
        let selection =
            implementation_selection_for_argument(fact.id, fact.interface(), &methods, closed);
        validate_selection(
            &program,
            &registry,
            group,
            &selection,
            fact.interface(),
            &mut InterfaceConstraintBudget::default(),
            group.span(),
        )
        .expect("the selected specific closed-effect head should match its linked goal");

        let missing_effect = crate::types::EffectId::new(effect_id.module(), u32::MAX);
        assert!(program.registry().effect(missing_effect).is_none());
        let malformed = Type::function_computation(
            Type::Unit,
            crate::types::ComputationType::new(
                Type::Bool,
                crate::types::EffectRow::singleton(crate::types::EffectInstance::new(
                    missing_effect,
                    Box::new([Type::Int]),
                )),
            ),
        );
        assert!(program.replace_first_implementation_argument_for_test(module, malformed.clone()));
        let group = entry_group(&program);
        let fact = &group.implementation_facts()[0];
        let selection =
            implementation_selection_for_argument(fact.id, fact.interface(), &methods, malformed);
        let failure = validate_selection(
            &program,
            &registry,
            group,
            &selection,
            fact.interface(),
            &mut InterfaceConstraintBudget::default(),
            group.span(),
        )
        .expect_err("a matching retained head and goal cannot authorize an absent effect");
        assert_eq!(
            failure.reason(),
            EvidenceValidationReason::InvalidEvidenceRoot
        );
        assert_eq!(
            failure
                .kind_context()
                .expect("the canonical kind cause must be retained")
                .name(),
            "missing-row-effect",
        );
    }

    #[test]
    fn local_availability_authentication_requires_exactly_two_units() {
        let program = local_program();
        let group = entry_group(&program);
        let implementation = group.implementation_facts()[0].id;
        assert_eq!(group.available_implementations().len(), 1);
        let registry =
            LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                .expect("the valid local inventory should authenticate");

        assert_eq!(
            implementation_is_available(
                &program,
                &registry,
                group,
                implementation,
                &mut InterfaceConstraintBudget::with_limit(1),
                group.span(),
            )
            .expect_err("the local inventory lookup must charge after the record visit")
            .reason(),
            EvidenceValidationReason::ConstraintResourceExhausted,
        );
        assert!(
            implementation_is_available(
                &program,
                &registry,
                group,
                implementation,
                &mut InterfaceConstraintBudget::with_limit(2),
                group.span(),
            )
            .expect("the wrapper and local inventory lookup should fit")
        );
    }

    #[test]
    fn one_direct_dependency_visit_requires_exactly_one_unit() {
        let fixture = ValidationFixture::create(concat!(
            "import dependency as Dependency\n",
            "import dependency (impl Equal)\n",
            "main : Unit -> Bool\nmain () = Dependency.equal((1, 1))\n",
        ));
        fixture.write(
            "dependency.ash",
            concat!(
                "pub interface Equal<A> {\nequal : (A, A) -> Bool\n}\n\n",
                "pub impl Equal<Int> {\nequal (left, right) = left == right\n}\n",
            ),
        );
        let graph = fixture.graph();
        let program = link_modules(check_graph(&graph), graph.entry())
            .expect("the direct dependency fixture should link");
        let entry = program
            .groups()
            .iter()
            .find(|group| group.module() == graph.entry())
            .expect("the entry group should remain linked");
        let defining = graph
            .modules()
            .iter()
            .find(|module| {
                std::path::Path::new(module.source().display_path()).file_name()
                    == Some("dependency.ash".as_ref())
            })
            .expect("the user dependency must remain loaded")
            .id();
        let (prefix, route) = entry
            .direct_dependencies()
            .iter()
            .enumerate()
            .find(|(_, route)| route.target() == defining)
            .expect("the user name import edge must remain present");
        assert_eq!(
            entry
                .direct_dependencies()
                .iter()
                .filter(|route| route.target() == defining)
                .count(),
            2
        );
        // Earlier compiler-service edges retain their own one-unit visits; the
        // selected user edge independently needs exactly one further unit.
        assert_eq!(
            has_direct_dependency(
                entry,
                route.target(),
                route.import_span(),
                &mut InterfaceConstraintBudget::with_limit(prefix),
                entry.span(),
            )
            .expect_err("the selected direct-edge visit must charge after the paid prefix")
            .reason(),
            EvidenceValidationReason::ConstraintResourceExhausted,
        );
        assert!(
            has_direct_dependency(
                entry,
                route.target(),
                route.import_span(),
                &mut InterfaceConstraintBudget::with_limit(prefix + 1),
                entry.span(),
            )
            .expect("one exact direct-edge unit should fit")
        );
    }

    #[test]
    fn block_expression_worklist_pops_initializers_then_result_in_source_order() {
        let program = entry_program(concat!(
            "main : Unit -> Int\n",
            "main () = {\n",
            "let first = 1\n",
            "let second = 2\n",
            "first\n",
            "}\n",
        ));
        let definition = &entry_group(&program).definitions()[0];
        let ResolvedDefinitionKind::Equational(global) = definition.kind() else {
            panic!("the fixture should retain an equational global");
        };
        let ResolvedExprKind::Block(block) = &global.equations[0].body.kind else {
            panic!("the fixture body should retain its source block");
        };
        let ResolvedLocalDeclaration::Binding(first) = &block.declarations[0] else {
            panic!("the first declaration should be an ordinary binding");
        };
        let ResolvedLocalDeclaration::Binding(second) = &block.declarations[1] else {
            panic!("the second declaration should be an ordinary binding");
        };
        let mut pending = Vec::new();
        schedule_block(
            &mut pending,
            block,
            &mut InterfaceConstraintBudget::default(),
        )
        .expect("the small block should schedule");

        assert_eq!(
            pending.pop().map(|expression| expression.span),
            Some(first.initializer.span)
        );
        assert_eq!(
            pending.pop().map(|expression| expression.span),
            Some(second.initializer.span)
        );
        assert_eq!(
            pending.pop().map(|expression| expression.span),
            Some(block.result.span)
        );
    }

    #[test]
    fn block_scheduling_charges_scans_and_expression_slots_at_exact_limits() {
        let program = entry_program(concat!(
            "main : Unit -> Int\n",
            "main () = {\n",
            "let first = 1\n",
            "let rec second : Unit -> Int = fn(ignored) {\n2\n}\n",
            "and third : Unit -> Int = fn(ignored) {\n3\n}\n",
            "first\n",
            "}\n",
        ));
        let definition = &entry_group(&program).definitions()[0];
        let ResolvedDefinitionKind::Equational(global) = definition.kind() else {
            panic!("the fixture should retain an equational global");
        };
        let ResolvedExprKind::Block(block) = &global.equations[0].body.kind else {
            panic!("the fixture body should retain its source block");
        };
        let mut measured = InterfaceConstraintBudget::default();
        schedule_block(&mut Vec::new(), block, &mut measured)
            .expect("the small block should schedule");
        let exact = measured.used();

        assert_eq!(
            exact, 8,
            "two declaration visits, two member visits, and four slots are charged"
        );
        assert_eq!(
            schedule_block(
                &mut Vec::new(),
                block,
                &mut InterfaceConstraintBudget::with_limit(exact - 1),
            )
            .expect_err("one unit below exact block work should fail")
            .reason(),
            EvidenceValidationReason::ConstraintResourceExhausted,
        );
        schedule_block(
            &mut Vec::new(),
            block,
            &mut InterfaceConstraintBudget::with_limit(exact),
        )
        .expect("the exact block budget should fit");
        schedule_block(
            &mut Vec::new(),
            block,
            &mut InterfaceConstraintBudget::with_limit(exact + 1),
        )
        .expect("one unit above exact block work should fit");

        let registry =
            LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                .expect("the source-free registry should build");
        for headers_only in [false, true] {
            // Unscoped scheduling retains its original8/0 preflight. Scoped
            // headers additionally retain heads(1+2+2+1) and two annotation
            // records(2each):18. Each complete zeroarg row annotation pays
            // root1+domain/value/row3+instance1: two annotations cost10 types.
            let constraint_work = if headers_only { 8 + 6 + 2 * 2 } else { 8 };
            let type_work = if headers_only { 2 * (1 + 3 + 1) } else { 0 };
            for limit in [constraint_work - 1, constraint_work, constraint_work] {
                let mut budget = InterfaceConstraintBudget::with_limit(limit);
                let mut types = TypeWorkBudget::with_limit(type_work);
                let mut pending = Vec::new();
                let mut heads = Vec::new();
                let mut sources = Vec::new();
                let mut scopes = Vec::new();
                let result = schedule_lexical_block(
                    &mut pending,
                    &mut heads,
                    &mut sources,
                    &mut scopes,
                    (None, None),
                    block,
                    &mut budget,
                    false,
                    OriginalLexicalContext::NONE,
                    headers_only.then_some((&program, &registry, &[], None, &mut types, true)),
                );
                if limit < constraint_work {
                    assert_eq!(
                        result
                            .expect_err("one-short source-free scheduling rejects")
                            .reason(),
                        EvidenceValidationReason::ConstraintResourceExhausted
                    );
                    if !headers_only {
                        assert!(pending.is_empty(), "unscoped preflight is atomic");
                    }
                } else {
                    result.expect("the exact scheduling owner fits");
                    assert_eq!(budget.used(), constraint_work);
                    assert_eq!(pending.len(), 4);
                    if headers_only {
                        assert_eq!(
                            heads,
                            [(None, None), (None, Some(1)), (None, Some(0)), (None, None)]
                        );
                        let ResolvedLocalDeclaration::Recursive(group) = &block.declarations[1]
                        else {
                            panic!("original recursive group")
                        };
                        assert_eq!(group.members.len(), 2);
                        for ((scope, parent), member) in scopes.iter().zip(&group.members) {
                            let LinkedLocalScope::Annotation(annotation) = scope else {
                                panic!("original annotation owner")
                            };
                            assert!(std::ptr::eq(*annotation, &member.annotation));
                            assert_eq!(*parent, None);
                            let row = annotation.ty.function_view().unwrap().effects().unwrap();
                            let [instance] = row.known() else {
                                panic!("canonical singleton DefaultAlloc")
                            };
                            assert!(instance.effect().module().is_builtin_region());
                            assert!(instance.arguments().is_empty());
                            assert!(row.tail().is_none());
                        }
                    }
                }
                if headers_only {
                    assert_eq!(scopes.len(), 2);
                } else {
                    assert!(heads.is_empty());
                    assert!(scopes.is_empty());
                }
                assert!(sources.is_empty());
                assert_eq!(types.used(), type_work);
            }
        }
    }

    #[test]
    fn recursive_evidence_validation_buffers_do_not_bypass_the_owner_api() {
        let source: String = include_str!("evidence_validation.rs")
            .chars()
            .filter(|character| !character.is_whitespace())
            .collect();
        for raw_field in [["pending", ".0"].concat(), ["rebuilt", ".0"].concat()] {
            assert!(!source.contains(&raw_field));
        }
        for owner in ["PendingGoals", "TypeBuffer"] {
            let broad_mutation = ["impl", "DerefMut", "for", owner].concat();
            assert!(!source.contains(&broad_mutation));
        }
    }

    #[test]
    fn evidence_substitution_preserves_caller_scope_and_rejects_unbound_source_authority() {
        let source = SourceFile::new("evidence-substitution-policy.ash", "x")
            .expect("the policy fixture should fit");
        let span = source
            .span(ByteRange::new(0, 1).expect("ordered fixture range"))
            .expect("the span should fit");
        let module = ModuleId::from(source.id());
        let implementation_parameter = TypeVariableId::resolved(module, 0);
        let caller_parameter = TypeVariableId::resolved(module, 1);
        let caller_row = TypeVariableId::resolved(module, 2);
        let caller_value = Type::function_computation(
            Type::Variable(caller_parameter),
            crate::types::ComputationType::new(
                Type::Int,
                EffectRow::open(EffectRowVariable::rigid(caller_row), Box::new([])),
            ),
        );
        let substitution: Box<[EvidenceSubstitution]> = Box::new([EvidenceSubstitution::new(
            implementation_parameter,
            caller_value.clone(),
        )]);
        let rebuilt = substitute_evidence_type(
            &Type::Variable(implementation_parameter),
            &substitution,
            &mut InterfaceConstraintBudget::default(),
            span,
        )
        .expect("replacement bodies keep their authenticated caller scope");
        assert_eq!(rebuilt, caller_value);

        for original in [
            Type::Variable(caller_parameter),
            Type::Inference(crate::types::InferenceVariableId::new(0)),
            Type::Forall(Box::new([]), Box::new(Type::Unit)),
            Type::function_computation(
                Type::Unit,
                crate::types::ComputationType::new(
                    Type::Int,
                    EffectRow::open(EffectRowVariable::rigid(caller_row), Box::new([])),
                ),
            ),
        ] {
            assert_eq!(
                substitute_evidence_type(
                    &original,
                    &substitution,
                    &mut InterfaceConstraintBudget::default(),
                    span,
                )
                .expect_err("original source authority must be completely substituted"),
                invalid_root(span),
            );
        }
    }

    #[test]
    fn late_missing_substitution_discards_deep_rebuilt_type_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("late-evidence-substitution-failure".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = crate::source::SourceFile::new("evidence-buffer.ash", "x")
                    .expect("the source fixture should fit");
                let span = source
                    .span(crate::source::ByteRange::new(0, 1).expect("ordered source range"))
                    .expect("the span should belong to the fixture");
                let mut deep = Type::Int;
                for _ in 0..DEPTH {
                    deep = Type::Application(Box::new(deep), Box::new(Type::Unit));
                }
                let root = crate::types::IterativeTypeOwner::new(Type::Tuple(
                    vec![deep, Type::Variable(TypeVariableId::new(0))].into_boxed_slice(),
                ));
                let failure = match substitute_evidence_type(
                    &root,
                    &[],
                    &mut InterfaceConstraintBudget::default(),
                    span,
                ) {
                    Err(failure) => failure,
                    Ok(unexpected) => {
                        drop(crate::types::IterativeTypeOwner::new(unexpected));
                        panic!("the final variable must have a substitution");
                    }
                };
                assert_eq!(failure, invalid_root(span));
            })
            .expect("the small-stack evidence-validation thread should start")
            .join()
            .expect("late rebuilt-type teardown must stay iterative");
    }
}
