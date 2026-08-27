//! Authentication of linked checked interface evidence before Core synthesis.

use std::{
    collections::{HashMap, HashSet},
    error::Error,
    fmt,
    sync::Arc,
};

use crate::{
    interface::{
        CheckedRequirement, ConstrainedScheme, EvidenceNode, EvidenceNodeId, EvidenceSelection,
        EvidenceSubstitution, ImplId, ImplMethodId, InterfaceConstraintBudget, InterfaceId,
        MethodId, RequirementId, RequirementOwner, implementation_prerequisite_terminates,
    },
    kind::{KindEnvironments, KindFailure, canonical_type_variable_kind},
    module::ModuleId,
    resolved::{
        AvailableImplementation, BinderId, CheckedImplementationFact, CheckedInterfaceFact,
        ImplementationAuthorization, PublicImplementationAuthorization, ResolvedBlock,
        ResolvedDeclarationIndex, ResolvedDefinitionKind, ResolvedExpr, ResolvedExprKind,
        ResolvedLocalDeclaration, ResolvedModuleGroup, ResolvedModuleProgram, ResolvedOccurrence,
        ResolvedRegistry, ResolvedTermName, ResolvedTypeVariable,
    },
    source::{Origin, Span},
    types::{
        ConstructorId, IterativeTypeOwner, Kind, NominalTypeId, Type, TypeVariableId,
        TypeWorkBudget, discard_type_iteratively, same_kind_with_charge,
    },
};

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
}

impl EvidenceValidationFailure {
    const fn new(reason: EvidenceValidationReason, primary: Span) -> Self {
        Self { reason, primary }
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
        Self::build_with_kinds(program, &mut kind_environments, budget, &mut type_work)
    }

    fn build_with_kinds<'a>(
        program: &'a ResolvedModuleProgram,
        kind_environments: &mut KindEnvironments<'a>,
        budget: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<Self, EvidenceValidationFailure> {
        let mut registry = Self {
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
        registry.validate_references(program, kind_environments, budget, type_work)?;
        registry.authenticate_public_implementations(program, budget)?;
        registry.authenticate_available_implementations(program, budget)?;
        Ok(registry)
    }

    fn validate_references<'a>(
        &self,
        program: &'a ResolvedModuleProgram,
        kind_environments: &mut KindEnvironments<'a>,
        budget: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(), EvidenceValidationFailure> {
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
            validate_group_consistency(program, self, group, kind_environments, budget, type_work)?;
            for fact_index in 0..group.interface_facts().len() {
                charge(budget, 1, group.span())?;
                let fact = group
                    .interface_facts()
                    .get(fact_index)
                    .ok_or_else(|| unknown(group.span()))?;
                for method_index in 0..fact.methods.len() {
                    charge(budget, 1, fact.span)?;
                    let method = fact
                        .methods
                        .get(method_index)
                        .ok_or_else(|| unknown(fact.span))?;
                    if self.method(program, method.id).is_none() {
                        return Err(unknown(method.span));
                    }
                }
            }
            for scheme_index in 0..group.schemes().len() {
                charge(budget, 1, group.span())?;
                let scheme = group
                    .schemes()
                    .get(scheme_index)
                    .ok_or_else(|| unknown(group.span()))?;
                let variables = copy_kinded_parameter_ids(
                    &scheme.scheme.type_parameters,
                    budget,
                    scheme.origin.primary_span(),
                )?;
                validate_requirements(
                    &scheme.scheme,
                    RequirementOwner::Global(scheme.binder),
                    &variables,
                    self,
                    program,
                    budget,
                    scheme.origin.primary_span(),
                )?;
            }
            for fact_index in 0..group.implementation_facts().len() {
                charge(budget, 1, group.span())?;
                let fact = group
                    .implementation_facts()
                    .get(fact_index)
                    .ok_or_else(|| unknown(group.span()))?;
                if self.interface(program, fact.interface).is_none() {
                    return Err(unknown(fact.span));
                }
                let mut head_variables = Vec::new();
                charge(budget, fact.head_parameters.len(), fact.span)?;
                head_variables
                    .try_reserve(fact.head_parameters.len())
                    .map_err(|_| resource(fact.span))?;
                head_variables.extend(fact.head_parameters.iter().map(|parameter| parameter.id));
                validate_linked_type_with_policy(
                    &fact.argument,
                    program.registry(),
                    &head_variables,
                    budget,
                    fact.span,
                )?;
                for ordinal in 0..fact.prerequisites.len() {
                    charge(budget, 1, fact.span)?;
                    let prerequisite = fact
                        .prerequisites
                        .get(ordinal)
                        .ok_or_else(|| unknown(fact.span))?;
                    validate_requirement(
                        prerequisite,
                        RequirementOwner::Impl(fact.id),
                        ordinal,
                        &head_variables,
                        self,
                        program,
                        budget,
                    )?;
                    if !implementation_prerequisite_terminates(
                        &prerequisite.argument,
                        &fact.argument,
                        budget,
                    )
                    .map_err(|()| resource(prerequisite.span))?
                    {
                        return Err(unknown(prerequisite.span));
                    }
                }
                let interface = self
                    .interface(program, fact.interface)
                    .ok_or_else(|| unknown(fact.span))?;
                if fact.methods.len() != interface.methods.len() {
                    return Err(unknown(fact.span));
                }
                for method_index in 0..fact.methods.len() {
                    charge(budget, 1, fact.span)?;
                    let method = fact
                        .methods
                        .get(method_index)
                        .ok_or_else(|| unknown(fact.span))?;
                    let interface_method = interface
                        .methods
                        .get(method_index)
                        .ok_or_else(|| unknown(fact.span))?;
                    if method.method != interface_method.id
                        || method.id != ImplMethodId::new(fact.id, interface_method.id)
                    {
                        return Err(unknown(method.span));
                    }
                }
            }
        }
        Ok(())
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
            let Some(body) = group.implementations().get(location.fact) else {
                return Ok(false);
            };
            if location.group != group_index
                || authorization.id().module() != group.module()
                || fact.id != authorization.id()
                || body.id() != authorization.id()
                || !body.source().public
            {
                return Ok(false);
            }
            for method in &fact.methods {
                charge(budget, 1, group.span())?;
                if method.id.implementation() != fact.id
                    || method.binder.module() != Some(group.module())
                {
                    return Ok(false);
                }
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

    fn source_method<'a>(
        &self,
        program: &'a ResolvedModuleProgram,
        id: MethodId,
    ) -> Option<&'a crate::resolved::ResolvedInterfaceMethod> {
        let location = self.methods.get(&id)?;
        program
            .groups()
            .get(location.interface.group)?
            .interfaces()
            .get(location.interface.fact)?
            .methods
            .get(location.method)
            .filter(|method| method.id == id)
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

fn validate_group_consistency<'a>(
    program: &'a ResolvedModuleProgram,
    registry: &LinkedInterfaceRegistry,
    group: &'a ResolvedModuleGroup,
    kind_environments: &mut KindEnvironments<'a>,
    budget: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
) -> Result<(), EvidenceValidationFailure> {
    let span = group.span();
    charge(budget, 1, span)?;
    if group.interfaces().len() != group.interface_facts().len()
        || group.interfaces().len() != group.checked_interfaces().len()
        || group.definitions().len() != group.schemes().len()
        || group.implementations().len() != group.implementation_facts().len()
        || group.implementations().len() != group.checked_implementations().len()
    {
        return Err(unknown(span));
    }

    for index in 0..group.interface_facts().len() {
        charge(budget, 1, span)?;
        let source = group.interfaces().get(index).ok_or_else(|| unknown(span))?;
        let token = group
            .checked_interfaces()
            .get(index)
            .ok_or_else(|| unknown(span))?;
        let fact = group
            .interface_facts()
            .get(index)
            .ok_or_else(|| unknown(span))?;
        if token.source_index != index
            || token.id != source.id
            || fact.id != source.id
            || fact.spelling != source.spelling
        {
            return Err(unknown(source.span));
        }
        if !same_binders_charged(
            std::slice::from_ref(&fact.parameter),
            std::slice::from_ref(&source.parameter),
            budget,
            source.span,
        )? {
            return Err(unknown(source.span));
        }
        if !same_origin_charged(&fact.origin, &source.origin, budget, source.span)?
            || fact.span != source.span
            || fact.methods.len() != source.methods.len()
        {
            return Err(unknown(source.span));
        }
        let canonical_parameter = program
            .registry()
            .type_variable(fact.parameter.id)
            .ok_or_else(|| unknown(source.span))?;
        kind_environments
            .insert_interface(
                fact.id,
                &canonical_parameter.kind,
                canonical_parameter.origin.primary_span(),
                type_work,
            )
            .map_err(|failure| map_kind_type_failure(failure, source.span))?;
        for method_index in 0..fact.methods.len() {
            charge(budget, 1, fact.span)?;
            let source_method = source
                .methods
                .get(method_index)
                .ok_or_else(|| unknown(fact.span))?;
            let method = fact
                .methods
                .get(method_index)
                .ok_or_else(|| unknown(fact.span))?;
            if !source_method.type_parameters.is_empty() {
                return Err(unknown(method.span));
            }
            if method.id != source_method.id
                || method.spelling != source_method.spelling
                || !same_origin_charged(&method.origin, &source_method.origin, budget, method.span)?
                || method.span != source_method.span
                || !same_type_charged(
                    &method.value_type,
                    &source_method.annotation.ty,
                    budget,
                    method.span,
                )?
            {
                return Err(unknown(method.span));
            }
            validate_linked_value_structure(
                &method.value_type,
                program.registry(),
                std::slice::from_ref(&fact.parameter.id),
                budget,
                method.span,
            )?;
        }
    }

    for index in 0..group.schemes().len() {
        charge(budget, 1, span)?;
        let definition = group
            .definitions()
            .get(index)
            .ok_or_else(|| unknown(span))?;
        let checked = group.schemes().get(index).ok_or_else(|| unknown(span))?;
        validate_global_scheme(
            program,
            definition,
            checked,
            kind_environments,
            budget,
            type_work,
        )?;
    }

    for index in 0..group.implementation_facts().len() {
        charge(budget, 1, span)?;
        let body = group
            .implementations()
            .get(index)
            .ok_or_else(|| unknown(span))?;
        let token = group
            .checked_implementations()
            .get(index)
            .ok_or_else(|| unknown(span))?;
        let fact = group
            .implementation_facts()
            .get(index)
            .ok_or_else(|| unknown(span))?;
        validate_implementation_consistency(
            program,
            registry,
            body,
            token,
            fact,
            kind_environments,
            budget,
            type_work,
        )?;
    }
    Ok(())
}

fn validate_global_scheme<'a>(
    program: &'a ResolvedModuleProgram,
    definition: &crate::resolved::CheckedDefinition,
    checked: &crate::resolved::CheckedGlobalScheme,
    kind_environments: &mut KindEnvironments<'a>,
    budget: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
) -> Result<(), EvidenceValidationFailure> {
    let span = definition.span();
    let (name, parameters, requirements) = match definition.kind() {
        ResolvedDefinitionKind::Equational(global) => (
            &global.interface.name,
            global.interface.type_parameters.as_ref(),
            global.interface.requirements.as_ref(),
        ),
        ResolvedDefinitionKind::InlineOperational(global) => (
            &global.header.name,
            global.header.type_parameters.as_ref(),
            global.header.requirements.as_ref(),
        ),
    };
    charge(
        budget,
        parameters
            .len()
            .saturating_add(requirements.len())
            .saturating_add(1),
        span,
    )?;
    for parameter in parameters {
        let canonical = program
            .registry()
            .type_variable(parameter.id)
            .ok_or_else(|| unknown(span))?;
        if canonical.id != parameter.id
            || canonical.spelling != parameter.spelling
            || !same_origin_charged(&canonical.origin, &parameter.origin, budget, span)?
        {
            return Err(unknown(span));
        }
    }
    let checked_parameters =
        copy_kinded_parameter_ids(&checked.scheme.type_parameters, budget, span)?;
    for requirement in &checked.scheme.requirements {
        authenticate_linked_interface_argument_kind(
            &requirement.argument,
            requirement.interface,
            program.registry(),
            &checked_parameters,
            None,
            kind_environments,
            budget,
            type_work,
            requirement.span,
        )?;
    }
    if checked.binder != name.id
        || checked.spelling != name.spelling
        || !same_origin_charged(&checked.origin, &name.origin, budget, span)?
        || !checked
            .scheme
            .type_parameters
            .iter()
            .map(|(parameter, _)| *parameter)
            .eq(parameters.iter().map(|parameter| parameter.id))
        || !requirements_match(
            &checked.scheme.requirements,
            requirements,
            &checked_parameters,
            program,
            budget,
            span,
        )?
    {
        return Err(unknown(span));
    }
    let value_matches = match definition.kind() {
        ResolvedDefinitionKind::Equational(_) => true,
        ResolvedDefinitionKind::InlineOperational(global) => {
            validate_linked_value_structure(
                &checked.scheme.value_type,
                program.registry(),
                &checked_parameters,
                budget,
                span,
            )?;
            let Type::Function(domain, codomain) = &checked.scheme.value_type else {
                return Err(unknown(span));
            };
            let domain_matches = match global.header.parameters.as_slice() {
                [parameter] => {
                    same_type_charged(domain, &parameter.annotation.ty, budget, parameter.span)?
                }
                parameters if parameters.len() >= 2 => {
                    let Type::Tuple(elements) = domain.as_ref() else {
                        return Err(unknown(span));
                    };
                    if elements.len() != parameters.len() {
                        false
                    } else {
                        let mut matches = true;
                        for (element, parameter) in elements.iter().zip(parameters) {
                            if !same_type_charged(
                                element,
                                &parameter.annotation.ty,
                                budget,
                                parameter.span,
                            )? {
                                matches = false;
                                break;
                            }
                        }
                        matches
                    }
                }
                _ => false,
            };
            domain_matches
                && same_type_charged(
                    codomain,
                    &global.header.result_type.ty,
                    budget,
                    global.header.result_type.span,
                )?
        }
    };
    if value_matches {
        Ok(())
    } else {
        Err(unknown(span))
    }
}

fn requirements_match(
    checked: &[CheckedRequirement],
    source: &[crate::resolved::ResolvedRequirement],
    variables: &[TypeVariableId],
    program: &ResolvedModuleProgram,
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<bool, EvidenceValidationFailure> {
    if checked.len() != source.len() {
        return Ok(false);
    }
    for (checked, source) in checked.iter().zip(source) {
        charge(budget, 1, span)?;
        validate_linked_type_with_policy(
            &checked.argument,
            program.registry(),
            variables,
            budget,
            checked.span,
        )?;
        if checked.id != source.id
            || checked.interface != source.interface.id
            || !same_origin_charged(
                &checked.origin,
                &Origin::Source(source.span),
                budget,
                source.span,
            )?
            || checked.span != source.span
            || !same_type_charged(&checked.argument, &source.argument.ty, budget, source.span)?
        {
            return Ok(false);
        }
    }
    Ok(true)
}

#[allow(clippy::too_many_arguments)]
fn validate_implementation_consistency<'a>(
    program: &'a ResolvedModuleProgram,
    registry: &LinkedInterfaceRegistry,
    body: &'a crate::resolved::CheckedImplementationBody,
    token: &crate::interface::CheckedImplementation,
    fact: &'a CheckedImplementationFact,
    kind_environments: &mut KindEnvironments<'a>,
    budget: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
) -> Result<(), EvidenceValidationFailure> {
    let source = body.source();
    let span = source.span;
    charge(
        budget,
        fact.head_parameters
            .len()
            .saturating_add(fact.prerequisites.len())
            .saturating_add(fact.methods.len())
            .saturating_add(1),
        span,
    )?;
    if token.source_index != usize::try_from(source.id.declaration()).unwrap_or(usize::MAX)
        || token.id != source.id
        || token.interface != source.interface.id
        || body.id() != source.id
        || fact.id != source.id
        || fact.interface != source.interface.id
    {
        return Err(unknown(span));
    }
    if !same_binder_metadata_charged(&fact.head_parameters, &source.head_parameters, budget, span)?
    {
        return Err(unknown(span));
    }
    for parameter in &fact.head_parameters {
        let canonical = program
            .registry()
            .type_variable(parameter.id)
            .ok_or_else(|| unknown(span))?;
        if !same_binder_metadata_charged(
            std::slice::from_ref(canonical),
            std::slice::from_ref(parameter),
            budget,
            span,
        )? {
            return Err(unknown(span));
        }
    }
    if !same_origin_charged(
        &fact.origin,
        &Origin::Source(source.span),
        budget,
        source.span,
    )? || fact.span != source.span
        || fact.methods.len() != token.methods.len()
        || fact.methods.len()
            != registry
                .interface(program, fact.interface)
                .ok_or_else(|| unknown(span))?
                .methods
                .len()
    {
        return Err(unknown(span));
    }
    let mut variables = Vec::new();
    variables
        .try_reserve(fact.head_parameters.len())
        .map_err(|_| resource(span))?;
    variables.extend(fact.head_parameters.iter().map(|parameter| parameter.id));
    validate_linked_interface_argument(
        &fact.argument,
        fact.interface,
        program.registry(),
        &variables,
        &fact.head_parameters,
        &source.head_parameters,
        kind_environments,
        budget,
        type_work,
        span,
    )?;
    for prerequisite in &fact.prerequisites {
        authenticate_linked_interface_argument_kind(
            &prerequisite.argument,
            prerequisite.interface,
            program.registry(),
            &variables,
            None,
            kind_environments,
            budget,
            type_work,
            prerequisite.span,
        )?;
    }
    if !same_type_charged(&fact.argument, &source.argument.ty, budget, span)?
        || !requirements_match(
            &fact.prerequisites,
            &source.prerequisites,
            &variables,
            program,
            budget,
            span,
        )?
    {
        return Err(unknown(span));
    }

    let interface = registry
        .interface(program, fact.interface)
        .ok_or_else(|| unknown(span))?;
    for method_index in 0..fact.methods.len() {
        charge(budget, 1, span)?;
        let method = fact
            .methods
            .get(method_index)
            .ok_or_else(|| unknown(span))?;
        let checked = token
            .methods
            .get(method_index)
            .ok_or_else(|| unknown(span))?;
        let interface_method = interface
            .methods
            .get(method_index)
            .ok_or_else(|| unknown(span))?;
        let source_interface_method = registry
            .source_method(program, interface_method.id)
            .ok_or_else(|| unknown(span))?;
        let group = source
            .method_groups
            .get(checked.source_group)
            .ok_or_else(|| unknown(span))?;
        if !same_parameter_pairs_to_records_charged(
            &method.scheme.type_parameters,
            &fact.head_parameters,
            budget,
            method.span,
        )? {
            return Err(unknown(method.span));
        }
        if method.id != checked.id
            || method.method != checked.method
            || method.binder != checked.binder
            || checked.method != interface_method.id
            || group.method != Some(method.method)
            || group.identity != Some(method.id)
            || group.binder.id != method.binder
            || method.span != group.span
            || !method
                .scheme
                .type_parameters
                .iter()
                .map(|(parameter, _)| *parameter)
                .eq(variables.iter().copied())
            || !requirements_match(
                &method.scheme.requirements,
                &source.prerequisites,
                &variables,
                program,
                budget,
                method.span,
            )?
            || !implementation_method_origin_matches(
                &method.origin,
                source,
                group,
                interface_method.span,
                source_interface_method.annotation.span,
            )
            || !same_type_after_single_substitution(
                &interface_method.value_type,
                interface.parameter.id,
                &fact.argument,
                &method.scheme.value_type,
                budget,
                method.span,
            )?
        {
            return Err(unknown(method.span));
        }
        validate_linked_value_structure(
            &method.scheme.value_type,
            program.registry(),
            &variables,
            budget,
            method.span,
        )?;
    }
    Ok(())
}

fn implementation_method_origin_matches(
    origin: &Origin,
    implementation: &crate::resolved::ResolvedImplementation,
    group: &crate::resolved::ResolvedImplementationMethodGroup,
    method_span: Span,
    annotation_span: Span,
) -> bool {
    let first = group.equations.first();
    let Origin::Related { primary, related } = origin else {
        return false;
    };
    let primary_span = first.map_or(group.span, |equation| equation.span);
    let expected_prefix = [
        implementation.span,
        group.span,
        method_span,
        annotation_span,
    ];
    matches!(primary.as_ref(), Origin::Source(span) if *span == primary_span)
        && related.len() == expected_prefix.len() + usize::from(first.is_some())
        && related.starts_with(&expected_prefix)
        && first.is_none_or(|equation| related.last() == Some(&equation.body.span))
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
fn validate_linked_interface_argument<'a>(
    ty: &Type,
    interface: InterfaceId,
    registry: &'a ResolvedRegistry,
    variables: &[TypeVariableId],
    parameter_records: &'a [ResolvedTypeVariable],
    source_parameter_records: &'a [ResolvedTypeVariable],
    environments: &mut KindEnvironments<'a>,
    constraint_work: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
    span: Span,
) -> Result<(), EvidenceValidationFailure> {
    validate_linked_type_with_policy(ty, registry, variables, constraint_work, span)?;
    authenticate_linked_interface_argument_kind(
        ty,
        interface,
        registry,
        variables,
        Some((parameter_records, source_parameter_records)),
        environments,
        constraint_work,
        type_work,
        span,
    )
}

#[allow(clippy::too_many_arguments)]
fn authenticate_linked_interface_argument_kind<'a>(
    ty: &Type,
    interface: InterfaceId,
    registry: &'a ResolvedRegistry,
    variables: &[TypeVariableId],
    parameter_records: Option<(&'a [ResolvedTypeVariable], &'a [ResolvedTypeVariable])>,
    environments: &mut KindEnvironments<'a>,
    constraint_work: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
    span: Span,
) -> Result<(), EvidenceValidationFailure> {
    if let Some((parameters, source_parameters)) = parameter_records {
        if !parameters
            .iter()
            .map(|parameter| parameter.id)
            .eq(variables.iter().copied())
        {
            return Err(unknown(span));
        }
        environments
            .install_canonical_owner_records_with_source(
                registry,
                parameters,
                source_parameters,
                type_work,
                span,
            )
            .map_err(|failure| map_kind_type_failure(failure, span))?;
    } else {
        environments
            .install_canonical_owner_ids(registry, variables, type_work, span)
            .map_err(|failure| map_kind_type_failure(failure, span))?;
    }
    let result = if parameter_records.is_some() {
        environments.expect_body_free_exact_owner_interface_argument_with_ledger(
            interface,
            ty,
            span,
            constraint_work,
        )
    } else {
        environments.expect_body_free_interface_argument_with_ledger(
            interface,
            ty,
            span,
            constraint_work,
        )
    };
    result.map_err(|failure| map_kind_constraint_failure(failure, span))
}

fn validate_linked_value_structure(
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

fn build_linked_kind_environments<'a>(
    registry: &'a ResolvedRegistry,
    type_work: &mut TypeWorkBudget,
    span: Span,
) -> Result<KindEnvironments<'a>, EvidenceValidationFailure> {
    let mut environments = KindEnvironments::new();
    for nominal in registry.nominals() {
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
    Ok(environments)
}

fn validate_linked_value_type<'a>(
    ty: &Type,
    registry: &'a ResolvedRegistry,
    variables: &[TypeVariableId],
    environments: &mut KindEnvironments<'a>,
    constraint_work: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
    span: Span,
) -> Result<(), EvidenceValidationFailure> {
    environments
        .install_canonical_owner_ids(registry, variables, type_work, span)
        .map_err(|failure| map_kind_type_failure(failure, span))?;
    environments
        .expect_body_free_value_type_with_ledger(ty, span, constraint_work)
        .map_err(|failure| map_kind_constraint_failure(failure, span))
}

#[allow(clippy::too_many_arguments)]
fn validate_linked_paired_value_type_with_kind_mirrors<'a>(
    checked: &Type,
    source: &Type,
    registry: &'a ResolvedRegistry,
    parameters: &'a [(TypeVariableId, Kind)],
    source_parameters: &'a [ResolvedTypeVariable],
    environments: &mut KindEnvironments<'a>,
    constraint_work: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
    span: Span,
) -> Result<(), EvidenceValidationFailure> {
    environments
        .install_canonical_owner_pairs_with_source(
            registry,
            parameters,
            source_parameters,
            type_work,
            span,
        )
        .map_err(|failure| map_kind_type_failure(failure, span))?;
    environments
        .expect_body_free_paired_value_type_with_ledger(checked, source, span, constraint_work)
        .map_err(|failure| map_kind_constraint_failure(failure, span))
}

fn validate_linked_value_schemes<'a>(
    program: &'a ResolvedModuleProgram,
    environments: &mut KindEnvironments<'a>,
    constraint_work: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
) -> Result<(), EvidenceValidationFailure> {
    for group_index in 0..program.groups().len() {
        let group_span = program
            .groups()
            .get(group_index)
            .map_or(program.result().span, ResolvedModuleGroup::span);
        charge(constraint_work, 1, group_span)?;
        let group = program
            .groups()
            .get(group_index)
            .ok_or_else(|| unknown(group_span))?;

        for fact_index in 0..group.interface_facts().len() {
            charge(constraint_work, 1, group_span)?;
            let fact = group
                .interface_facts()
                .get(fact_index)
                .ok_or_else(|| unknown(group_span))?;
            let variables = [fact.parameter.id];
            for method_index in 0..fact.methods.len() {
                charge(constraint_work, 1, fact.span)?;
                let method = fact
                    .methods
                    .get(method_index)
                    .ok_or_else(|| unknown(fact.span))?;
                environments
                    .install_canonical_owner_ids(
                        program.registry(),
                        &variables,
                        type_work,
                        method.span,
                    )
                    .map_err(|failure| map_kind_type_failure(failure, method.span))?;
                environments
                    .expect_body_free_interface_method_with_ledger(
                        method.value_type(),
                        fact.parameter.id,
                        method.span,
                        constraint_work,
                    )
                    .map_err(|failure| map_kind_constraint_failure(failure, method.span))?;
            }
        }

        for scheme_index in 0..group.schemes().len() {
            charge(constraint_work, 1, group_span)?;
            let scheme = group
                .schemes()
                .get(scheme_index)
                .ok_or_else(|| unknown(group_span))?;
            let definition = group
                .definitions()
                .get(scheme_index)
                .ok_or_else(|| unknown(group_span))?;
            let span = scheme.origin.primary_span();
            match definition.kind() {
                ResolvedDefinitionKind::Equational(global) => {
                    validate_linked_paired_value_type_with_kind_mirrors(
                        &scheme.scheme.value_type,
                        &global.interface.annotation.ty,
                        program.registry(),
                        &scheme.scheme.type_parameters,
                        &global.interface.type_parameters,
                        environments,
                        constraint_work,
                        type_work,
                        span,
                    )?;
                }
                ResolvedDefinitionKind::InlineOperational(global) => {
                    environments
                        .install_canonical_owner_pairs_with_source(
                            program.registry(),
                            &scheme.scheme.type_parameters,
                            &global.header.type_parameters,
                            type_work,
                            span,
                        )
                        .map_err(|failure| map_kind_type_failure(failure, span))?;
                    environments
                        .expect_body_free_exact_owner_value_type_with_ledger(
                            &scheme.scheme.value_type,
                            span,
                            constraint_work,
                        )
                        .map_err(|failure| map_kind_constraint_failure(failure, span))?;
                }
            }
        }

        for fact_index in 0..group.implementation_facts().len() {
            charge(constraint_work, 1, group_span)?;
            let fact = group
                .implementation_facts()
                .get(fact_index)
                .ok_or_else(|| unknown(group_span))?;
            for method_index in 0..fact.methods.len() {
                charge(constraint_work, 1, fact.span)?;
                let method = fact
                    .methods
                    .get(method_index)
                    .ok_or_else(|| unknown(fact.span))?;
                let variables = copy_kinded_parameter_ids(
                    &method.scheme.type_parameters,
                    constraint_work,
                    method.span,
                )?;
                validate_linked_value_type(
                    &method.scheme.value_type,
                    program.registry(),
                    &variables,
                    environments,
                    constraint_work,
                    type_work,
                    method.span,
                )?;
            }
        }
    }
    Ok(())
}

fn map_kind_type_failure(failure: KindFailure, span: Span) -> EvidenceValidationFailure {
    match failure {
        KindFailure::Resource(_) => type_resource(span),
        KindFailure::Internal(_) | KindFailure::Source(_) => unknown(span),
    }
}

fn map_kind_constraint_failure(failure: KindFailure, span: Span) -> EvidenceValidationFailure {
    match failure {
        KindFailure::Resource(_) => resource(span),
        KindFailure::Internal(_) | KindFailure::Source(_) => unknown(span),
    }
}

fn authenticate_selected_goal_kind(
    interface: InterfaceId,
    argument: &Type,
    environments: &KindEnvironments<'_>,
    constraint_work: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<(), EvidenceValidationFailure> {
    environments
        .expect_body_free_interface_argument_with_ledger(interface, argument, span, constraint_work)
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
        KindFailure::Internal(_) | KindFailure::Source(_) => invalid_root(span),
    }
}

fn map_selected_kind_constraint_failure(
    failure: KindFailure,
    span: Span,
) -> EvidenceValidationFailure {
    match failure {
        KindFailure::Resource(_) => resource(span),
        KindFailure::Internal(_) | KindFailure::Source(_) => invalid_root(span),
    }
}

fn copy_kinded_parameter_ids(
    parameters: &[(TypeVariableId, Kind)],
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<Vec<TypeVariableId>, EvidenceValidationFailure> {
    charge(budget, parameters.len(), span)?;
    let mut ids = Vec::new();
    ids.try_reserve(parameters.len())
        .map_err(|_| resource(span))?;
    ids.extend(parameters.iter().map(|(parameter, _)| *parameter));
    Ok(ids)
}

fn same_type_after_single_substitution(
    source: &Type,
    parameter: TypeVariableId,
    argument: &Type,
    actual: &Type,
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<bool, EvidenceValidationFailure> {
    let mut pending = Vec::new();
    reserve_type_pairs(&mut pending, 1, budget, span)?;
    pending.push((source, actual));
    while let Some((source, actual)) = pending.pop() {
        charge(budget, 1, span)?;
        if matches!(source, Type::Variable(candidate) if *candidate == parameter) {
            if !same_type_charged(argument, actual, budget, span)? {
                return Ok(false);
            }
            continue;
        }
        match (source, actual) {
            (Type::Int, Type::Int) | (Type::Bool, Type::Bool) | (Type::Unit, Type::Unit) => {}
            (Type::Nominal(left), Type::Nominal(right)) if left == right => {}
            (Type::Variable(left), Type::Variable(right)) if left == right => {}
            (
                Type::Application(left_function, left_argument),
                Type::Application(right_function, right_argument),
            ) => {
                reserve_type_pairs(&mut pending, 2, budget, span)?;
                pending.push((left_argument, right_argument));
                pending.push((left_function, right_function));
            }
            (Type::Tuple(left), Type::Tuple(right)) if left.len() == right.len() => {
                reserve_type_pairs(&mut pending, left.len(), budget, span)?;
                pending.extend(left.iter().zip(right).rev());
            }
            (
                Type::Function(left_domain, left_codomain),
                Type::Function(right_domain, right_codomain),
            ) => {
                reserve_type_pairs(&mut pending, 2, budget, span)?;
                pending.push((left_codomain, right_codomain));
                pending.push((left_domain, right_domain));
            }
            _ => return Ok(false),
        }
    }
    Ok(true)
}

/// A checked module program whose retained interface evidence has been authenticated.
#[derive(Debug)]
pub struct ValidatedInterfaceProgram {
    source: ResolvedModuleProgram,
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

/// Authenticates linked checked interface evidence before Core synthesis.
///
/// # Errors
///
/// Returns an internal validation failure when a retained checked identity,
/// implementation authorization route, or occurrence evidence root is malformed.
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
    authenticate_linked_registry_facts(&program, constraint_work)?;
    let mut kind_environments =
        build_linked_kind_environments(program.registry(), type_work, program.result().span)?;
    authenticate_linked_constructor_payloads(
        &program,
        &mut kind_environments,
        constraint_work,
        type_work,
    )?;
    let linked_interfaces = LinkedInterfaceRegistry::build_with_kinds(
        &program,
        &mut kind_environments,
        constraint_work,
        type_work,
    )?;
    validate_linked_value_schemes(&program, &mut kind_environments, constraint_work, type_work)?;
    validate_occurrences(
        &program,
        &linked_interfaces,
        &mut kind_environments,
        constraint_work,
        type_work,
    )?;
    drop(kind_environments);
    Ok(ValidatedInterfaceProgram { source: program })
}

fn authenticate_linked_constructor_payloads<'a>(
    program: &'a ResolvedModuleProgram,
    environments: &mut KindEnvironments<'a>,
    constraint_work: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
) -> Result<(), EvidenceValidationFailure> {
    let registry = program.registry();
    for nominal in registry.nominals() {
        let span = nominal.origin.primary_span();
        charge(constraint_work, 1, span)?;
        let parameters = registry
            .nominal_parameters(nominal.id)
            .ok_or_else(|| unknown(span))?;
        charge(constraint_work, parameters.len(), span)?;
        let mut variables = Vec::new();
        variables
            .try_reserve(parameters.len())
            .map_err(|_| resource(span))?;
        variables.extend(parameters.iter().map(|parameter| parameter.id));
        for identity in &nominal.constructors {
            charge(constraint_work, 1, span)?;
            let constructor = registry
                .constructor(*identity)
                .ok_or_else(|| unknown(span))?;
            let Some(payload) = constructor.payload.as_ref() else {
                continue;
            };
            let payload_span = constructor.origin.primary_span();
            validate_linked_value_structure(
                payload,
                registry,
                &variables,
                constraint_work,
                payload_span,
            )?;
            validate_linked_value_type(
                payload,
                registry,
                &variables,
                environments,
                constraint_work,
                type_work,
                payload_span,
            )?;
        }
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum LinkedBinderOwner {
    Nominal(NominalTypeId),
    Interface(InterfaceId),
    Global(BinderId),
    Implementation(ImplId),
}

fn reserve_linked_registry_authentication_indexes(
    group_count: usize,
    owner_count: usize,
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<
    (
        HashSet<ModuleId>,
        HashMap<TypeVariableId, LinkedBinderOwner>,
    ),
    EvidenceValidationFailure,
> {
    let index_work = group_count
        .checked_add(owner_count)
        .ok_or_else(|| resource(span))?;
    charge(budget, index_work, span)?;
    let mut modules = HashSet::new();
    modules
        .try_reserve(group_count)
        .map_err(|_| resource(span))?;
    let mut owners = HashMap::new();
    owners
        .try_reserve(owner_count)
        .map_err(|_| resource(span))?;
    Ok((modules, owners))
}

fn authenticate_linked_registry_facts(
    program: &ResolvedModuleProgram,
    budget: &mut InterfaceConstraintBudget,
) -> Result<(), EvidenceValidationFailure> {
    let span = program.result().span;
    charge(budget, 1, span)?;
    let registry = program.registry();
    let (mut modules, mut owners) = reserve_linked_registry_authentication_indexes(
        program.groups().len(),
        registry.type_variable_count(),
        budget,
        span,
    )?;
    for group in program.groups() {
        charge(budget, 1, group.span())?;
        if !modules.insert(group.module()) {
            return Err(unknown(group.span()));
        }
    }
    let mut constructor_count = 0_usize;

    for nominal in registry.nominals() {
        charge(budget, 1, span)?;
        if !modules.contains(&nominal.id.module())
            || registry
                .nominal(nominal.id)
                .is_none_or(|found| found.id != nominal.id || found.spelling != nominal.spelling)
            || nominal.constructors.is_empty()
        {
            return Err(unknown(nominal.origin.primary_span()));
        }
        let parameters = registry
            .nominal_parameters(nominal.id)
            .ok_or_else(|| unknown(nominal.origin.primary_span()))?;
        for parameter in parameters {
            let canonical = registry
                .type_variable(parameter.id)
                .ok_or_else(|| unknown(parameter.origin.primary_span()))?;
            if !same_binders_charged(
                std::slice::from_ref(canonical),
                std::slice::from_ref(parameter),
                budget,
                parameter.origin.primary_span(),
            )? || owners
                .insert(parameter.id, LinkedBinderOwner::Nominal(nominal.id))
                .is_some()
            {
                return Err(unknown(parameter.origin.primary_span()));
            }
        }
        constructor_count = constructor_count
            .checked_add(nominal.constructors.len())
            .ok_or_else(|| resource(nominal.origin.primary_span()))?;
        for (ordinal, identity) in nominal.constructors.iter().copied().enumerate() {
            charge(budget, 1, nominal.origin.primary_span())?;
            let ordinal =
                u32::try_from(ordinal).map_err(|_| unknown(nominal.origin.primary_span()))?;
            let expected = ConstructorId::new(nominal.id, ordinal);
            let constructor = registry
                .constructor(identity)
                .ok_or_else(|| unknown(nominal.origin.primary_span()))?;
            if identity != expected || constructor.id != identity || constructor.owner != nominal.id
            {
                return Err(unknown(constructor.origin.primary_span()));
            }
        }
    }
    if constructor_count != registry.constructors().len() {
        return Err(unknown(span));
    }

    for group in program.groups() {
        for interface in group.interface_facts() {
            charge(budget, 1, interface.span)?;
            let owner = LinkedBinderOwner::Interface(interface.id);
            let canonical = registry
                .type_variable(interface.parameter.id)
                .ok_or_else(|| unknown(interface.span))?;
            if !same_binders_charged(
                std::slice::from_ref(canonical),
                std::slice::from_ref(&interface.parameter),
                budget,
                interface.span,
            )? || owners.insert(interface.parameter.id, owner).is_some()
            {
                return Err(unknown(interface.span));
            }
        }
        for scheme in group.schemes() {
            charge(budget, 1, scheme.origin.primary_span())?;
            for (identity, _) in &scheme.scheme.type_parameters {
                charge(budget, 1, scheme.origin.primary_span())?;
                let owner = LinkedBinderOwner::Global(scheme.binder);
                if registry.type_variable(*identity).is_none()
                    || owners.insert(*identity, owner).is_some()
                {
                    return Err(unknown(scheme.origin.primary_span()));
                }
            }
        }
        for implementation in group.implementation_facts() {
            charge(budget, 1, implementation.span)?;
            for parameter in &implementation.head_parameters {
                charge(budget, 1, parameter.origin.primary_span())?;
                let owner = LinkedBinderOwner::Implementation(implementation.id);
                if registry.type_variable(parameter.id).is_none()
                    || owners.insert(parameter.id, owner).is_some()
                {
                    return Err(unknown(parameter.origin.primary_span()));
                }
            }
        }
    }
    charge(budget, 1, span)?;
    if owners.len() != registry.type_variable_count() {
        return Err(unknown(span));
    }
    // Preserve canonical-fact precedence, then authenticate the ordered row
    // carrier before the validated capability can be constructed.
    authenticate_linked_global_parameter_rows(program, budget)?;
    Ok(())
}

fn authenticate_linked_global_parameter_rows(
    program: &ResolvedModuleProgram,
    budget: &mut InterfaceConstraintBudget,
) -> Result<(), EvidenceValidationFailure> {
    let registry = program.registry();
    let rows = registry.global_parameter_rows();
    let mut row_position = 0usize;
    for group in program.groups() {
        for scheme in group.schemes() {
            let parameters = &scheme.scheme.type_parameters;
            if parameters.is_empty() {
                continue;
            }
            let span = scheme.origin.primary_span();
            charge(budget, 1, span)?;
            let row = rows.get(row_position).ok_or_else(|| unknown(span))?;
            let indexed = registry
                .global_parameter_row(scheme.binder)
                .ok_or_else(|| unknown(span))?;
            if row.owner() != scheme.binder
                || !std::ptr::eq(row, indexed)
                || row.parameters().len() != parameters.len()
            {
                return Err(unknown(span));
            }
            for (retained, (expected, _)) in row.parameters().iter().zip(parameters) {
                charge(budget, 1, span)?;
                if retained != expected || registry.type_variable(*retained).is_none() {
                    return Err(unknown(span));
                }
            }
            row_position = row_position.checked_add(1).ok_or_else(|| resource(span))?;
        }
    }
    if row_position != rows.len() {
        return Err(unknown(program.result().span));
    }
    Ok(())
}

fn validate_occurrences<'a>(
    program: &'a ResolvedModuleProgram,
    registry: &LinkedInterfaceRegistry,
    kind_environments: &mut KindEnvironments<'a>,
    budget: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
) -> Result<(), EvidenceValidationFailure> {
    for group_index in 0..program.groups().len() {
        let group_span = program
            .groups()
            .get(group_index)
            .map_or(program.result().span, ResolvedModuleGroup::span);
        charge(budget, 1, group_span)?;
        let group = program
            .groups()
            .get(group_index)
            .ok_or_else(|| unknown(group_span))?;
        let mut next_definition = 0usize;
        let mut next_implementation = 0usize;
        let mut next_interface = 0usize;
        for declaration_index in 0..group.declaration_order().len() {
            charge(budget, 1, group.span())?;
            let declaration = group
                .declaration_order()
                .get(declaration_index)
                .ok_or_else(|| unknown(group.span()))?;
            match *declaration {
                ResolvedDeclarationIndex::Global(definition_index)
                    if definition_index == next_definition =>
                {
                    let definition = group
                        .definitions()
                        .get(definition_index)
                        .ok_or_else(|| unknown(group.span()))?;
                    validate_definition(
                        program,
                        registry,
                        group,
                        definition,
                        kind_environments,
                        budget,
                        type_work,
                    )?;
                    next_definition = next_definition
                        .checked_add(1)
                        .ok_or_else(|| resource(group.span()))?;
                }
                ResolvedDeclarationIndex::Implementation(implementation_index)
                    if implementation_index == next_implementation =>
                {
                    let implementation = group
                        .implementations()
                        .get(implementation_index)
                        .ok_or_else(|| unknown(group.span()))?;
                    validate_implementation(
                        program,
                        registry,
                        group,
                        implementation,
                        kind_environments,
                        budget,
                        type_work,
                    )?;
                    next_implementation = next_implementation
                        .checked_add(1)
                        .ok_or_else(|| resource(group.span()))?;
                }
                ResolvedDeclarationIndex::Interface(interface_index)
                    if interface_index == next_interface =>
                {
                    next_interface = next_interface
                        .checked_add(1)
                        .ok_or_else(|| resource(group.span()))?;
                }
                ResolvedDeclarationIndex::Type(_) => {}
                ResolvedDeclarationIndex::Global(_)
                | ResolvedDeclarationIndex::Implementation(_)
                | ResolvedDeclarationIndex::Interface(_) => return Err(unknown(group.span())),
            }
        }
        if next_definition != group.definitions().len()
            || next_implementation != group.implementations().len()
            || next_interface != group.interfaces().len()
        {
            return Err(unknown(group.span()));
        }
    }
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
    )
}

fn validate_definition<'a>(
    program: &'a ResolvedModuleProgram,
    registry: &LinkedInterfaceRegistry,
    group: &ResolvedModuleGroup,
    definition: &crate::resolved::CheckedDefinition,
    kind_environments: &mut KindEnvironments<'a>,
    budget: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
) -> Result<(), EvidenceValidationFailure> {
    let binder = match definition.kind() {
        ResolvedDefinitionKind::Equational(global) => global.interface.name.id,
        ResolvedDefinitionKind::InlineOperational(global) => global.header.name.id,
    };
    let scheme = registry
        .scheme(program, binder)
        .ok_or_else(|| unknown(definition.span()))?;
    let variables = copy_kinded_parameter_ids(&scheme.type_parameters, budget, definition.span())?;
    let scope = EvidenceScope {
        owner: Some(RequirementOwner::Global(binder)),
        variables: &variables,
    };
    match definition.kind() {
        ResolvedDefinitionKind::Equational(global) => {
            for equation_index in 0..global.equations.len() {
                charge(budget, 1, definition.span())?;
                let equation = global
                    .equations
                    .get(equation_index)
                    .ok_or_else(|| unknown(definition.span()))?;
                validate_expression(
                    program,
                    registry,
                    group,
                    scope,
                    &equation.body,
                    kind_environments,
                    budget,
                    type_work,
                )?;
            }
        }
        ResolvedDefinitionKind::InlineOperational(global) => {
            let mut pending = Vec::new();
            schedule_block(&mut pending, &global.body, budget)?;
            validate_pending_expressions(
                program,
                registry,
                group,
                scope,
                &mut pending,
                kind_environments,
                budget,
                type_work,
            )?;
        }
    }
    Ok(())
}

fn validate_implementation<'a>(
    program: &'a ResolvedModuleProgram,
    registry: &LinkedInterfaceRegistry,
    group: &ResolvedModuleGroup,
    implementation: &crate::resolved::CheckedImplementationBody,
    kind_environments: &mut KindEnvironments<'a>,
    budget: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
) -> Result<(), EvidenceValidationFailure> {
    let fact = registry
        .implementation(program, implementation.id())
        .ok_or_else(|| unknown(implementation.span()))?;
    charge(budget, fact.head_parameters.len(), implementation.span())?;
    let mut parameters = Vec::new();
    parameters
        .try_reserve(fact.head_parameters.len())
        .map_err(|_| resource(implementation.span()))?;
    parameters.extend(fact.head_parameters.iter().map(|parameter| parameter.id));
    let scope = EvidenceScope {
        owner: Some(RequirementOwner::Impl(implementation.id())),
        variables: &parameters,
    };
    for method_index in 0..implementation.method_groups().len() {
        charge(budget, 1, implementation.span())?;
        let method = implementation
            .method_groups()
            .get(method_index)
            .ok_or_else(|| unknown(implementation.span()))?;
        for equation_index in 0..method.equations.len() {
            charge(budget, 1, method.span)?;
            let equation = method
                .equations
                .get(equation_index)
                .ok_or_else(|| unknown(method.span))?;
            validate_expression(
                program,
                registry,
                group,
                scope,
                &equation.body,
                kind_environments,
                budget,
                type_work,
            )?;
        }
    }
    Ok(())
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
        kind_environments,
        budget,
        type_work,
    )
}

#[allow(clippy::too_many_arguments)]
fn validate_pending_expressions<'a>(
    program: &'a ResolvedModuleProgram,
    registry: &LinkedInterfaceRegistry,
    group: &ResolvedModuleGroup,
    scope: EvidenceScope<'_>,
    pending: &mut Vec<&ResolvedExpr>,
    kind_environments: &mut KindEnvironments<'a>,
    budget: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
) -> Result<(), EvidenceValidationFailure> {
    while let Some(expression) = pending.pop() {
        charge(budget, 1, expression.span)?;
        match &expression.kind {
            ResolvedExprKind::Occurrence(occurrence) => {
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
            ResolvedExprKind::Integer(_)
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
            ResolvedExprKind::Block(block) => schedule_block(pending, block, budget)?,
            ResolvedExprKind::Function(function) => {
                schedule_block(pending, &function.body, budget)?;
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
        }
    }
    Ok(())
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
            for (slot, requirement) in occurrence.evidence.iter().zip(requirements) {
                let (checked_argument, selection) =
                    slot.filled().ok_or_else(|| invalid_root(span))?;
                validate_checked_selection_in_scope(
                    program,
                    registry,
                    group,
                    selection,
                    requirement.interface,
                    checked_argument,
                    scope,
                    kind_environments,
                    budget,
                    type_work,
                    span,
                )?;
            }
        }
        ResolvedTermName::Method(method) => {
            let method = registry
                .method(program, method)
                .ok_or_else(|| unknown(span))?;
            let [slot] = occurrence.evidence.as_ref() else {
                return Err(invalid_root(span));
            };
            let (checked_argument, selection) = slot.filled().ok_or_else(|| invalid_root(span))?;
            validate_checked_selection_in_scope(
                program,
                registry,
                group,
                selection,
                method.id.interface(),
                checked_argument,
                scope,
                kind_environments,
                budget,
                type_work,
                span,
            )?;
        }
    }
    Ok(())
}

#[derive(Clone, Copy)]
struct EvidenceScope<'a> {
    owner: Option<RequirementOwner>,
    variables: &'a [TypeVariableId],
}

impl EvidenceScope<'static> {
    const NONE: Self = Self {
        owner: None,
        variables: &[],
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
    validate_selection_in_scope(
        program,
        registry,
        group,
        selection,
        expected_interface,
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
    expected_interface: InterfaceId,
    scope: EvidenceScope<'_>,
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<(), EvidenceValidationFailure> {
    let mut type_work = TypeWorkBudget::default();
    let mut kind_environments =
        build_linked_kind_environments(program.registry(), &mut type_work, span)?;
    for linked_group in program.groups() {
        for interface in linked_group.interface_facts() {
            let parameter = program
                .registry()
                .type_variable(interface.parameter.id)
                .ok_or_else(|| unknown(span))?;
            kind_environments
                .insert_interface(
                    interface.id,
                    &parameter.kind,
                    parameter.origin.primary_span(),
                    &mut type_work,
                )
                .map_err(|failure| map_kind_type_failure(failure, span))?;
        }
    }
    validate_checked_selection_in_scope(
        program,
        registry,
        group,
        selection,
        expected_interface,
        selection.argument(),
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
    expected_interface: InterfaceId,
    expected_argument: &Type,
    scope: EvidenceScope<'_>,
    kind_environments: &mut KindEnvironments<'a>,
    budget: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
    span: Span,
) -> Result<(), EvidenceValidationFailure> {
    charge(budget, 2, span)?;
    validate_type_with_application_policy(
        expected_argument,
        program.registry(),
        scope.variables,
        budget,
        span,
    )?;
    if selection.interface() != expected_interface
        || registry.interface(program, selection.interface()).is_none()
        || selection.node(selection.root()).is_none()
    {
        return Err(invalid_root(span));
    }
    if !same_type_charged(selection.argument(), expected_argument, budget, span)? {
        return Err(invalid_root(span));
    }
    kind_environments
        .install_canonical_owner_ids(program.registry(), scope.variables, type_work, span)
        .map_err(|failure| map_selected_kind_type_failure(failure, span))?;
    authenticate_selected_goal_kind(
        expected_interface,
        expected_argument,
        kind_environments,
        budget,
        span,
    )?;
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
        expected_interface,
        expected_argument,
        None,
        scope,
        kind_environments,
        &mut visited,
        &mut pending,
        budget,
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
            goal.interface,
            goal.argument(),
            goal.mandated_requirement,
            scope,
            kind_environments,
            &mut visited,
            &mut pending,
            budget,
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
    expected_interface: InterfaceId,
    expected_argument: &Type,
    mandated_requirement: Option<RequirementId>,
    scope: EvidenceScope<'_>,
    kind_environments: &KindEnvironments<'_>,
    visited: &mut HashSet<EvidenceNodeId>,
    pending: &mut PendingGoals,
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<(), EvidenceValidationFailure> {
    charge(budget, 1, span)?;
    if !visited.insert(node) {
        return Err(invalid_root(span));
    }
    let interface = registry
        .interface(program, expected_interface)
        .ok_or_else(|| unknown(span))?;
    match selection.node(node).ok_or_else(|| invalid_root(span))? {
        EvidenceNode::Abstract {
            requirement,
            methods,
        } => {
            charge(budget, methods.len().saturating_add(1), span)?;
            let checked = registry
                .requirement(program, requirement)
                .ok_or_else(|| unknown(span))?;
            if scope.owner != Some(requirement.owner())
                || checked.interface != expected_interface
                || !same_type_charged(&checked.argument, expected_argument, budget, span)?
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
                expected_interface,
                expected_argument,
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
                expected_interface,
                expected_argument,
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
                Some(RequirementOwner::Global(_)) | None => None,
            };
            let exact_current = match current {
                Some(current) if current.interface == expected_interface => {
                    same_type_charged(&current.argument, expected_argument, budget, span)?
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
            if fact.interface != expected_interface {
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
                expected_argument,
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
                let argument =
                    substitute_evidence_type(&requirement.argument, substitution, budget, span)?;
                let mandated_requirement = if exact_current {
                    Some(requirement.id)
                } else {
                    None
                };
                pending.push(PendingGoal::new(
                    prerequisite,
                    requirement.interface,
                    argument,
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
    expected_interface: InterfaceId,
    expected_argument: &Type,
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
    }
    .ok_or_else(|| unknown(span))?;

    for index in 0..requirements.len() {
        charge(budget, 1, span)?;
        let requirement = requirements.get(index).ok_or_else(|| unknown(span))?;
        if requirement.interface == expected_interface
            && same_type_charged(&requirement.argument, expected_argument, budget, span)?
        {
            return Ok(Some(requirement.id));
        }
    }
    Ok(None)
}

fn current_identity_substitution_matches(
    fact: &CheckedImplementationFact,
    substitution: &[EvidenceSubstitution],
    scope_variables: &[TypeVariableId],
    registry: &ResolvedRegistry,
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<bool, EvidenceValidationFailure> {
    if fact.head_parameters.len() != scope_variables.len()
        || fact.head_parameters.len() != substitution.len()
    {
        return Ok(false);
    }
    validate_type_with_application_policy(&fact.argument, registry, scope_variables, budget, span)?;
    for ((parameter, scope_variable), binding) in fact
        .head_parameters
        .iter()
        .zip(scope_variables)
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
    interface: InterfaceId,
    argument: Option<Type>,
    mandated_requirement: Option<RequirementId>,
}

impl PendingGoal {
    const fn new(
        node: EvidenceNodeId,
        interface: InterfaceId,
        argument: Type,
        mandated_requirement: Option<RequirementId>,
    ) -> Self {
        Self {
            node,
            interface,
            argument: Some(argument),
            mandated_requirement,
        }
    }

    fn argument(&self) -> &Type {
        self.argument
            .as_ref()
            .expect("a pending evidence goal retains its argument")
    }
}

impl Drop for PendingGoal {
    fn drop(&mut self) {
        if let Some(argument) = self.argument.take() {
            discard_type_iteratively(argument);
        }
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
    goal: &Type,
    registry: &ResolvedRegistry,
    goal_variables: &[TypeVariableId],
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<bool, EvidenceValidationFailure> {
    if fact.head_parameters.len() != substitution.len() {
        return Ok(false);
    }
    charge(budget, fact.head_parameters.len(), span)?;
    let mut head_variables = Vec::new();
    head_variables
        .try_reserve(fact.head_parameters.len())
        .map_err(|_| resource(span))?;
    head_variables.extend(fact.head_parameters.iter().map(|parameter| parameter.id));
    validate_type_with_application_policy(&fact.argument, registry, &head_variables, budget, span)?;
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

    let mut pending = Vec::new();
    reserve_type_pairs(&mut pending, 1, budget, span)?;
    pending.push((&fact.argument, goal));
    while let Some((candidate, goal)) = pending.pop() {
        charge(budget, 1, span)?;
        if let Type::Variable(variable) = candidate {
            let Some(binding) = find_evidence_binding(substitution, *variable, budget, span)?
            else {
                return Ok(false);
            };
            if !same_type_charged(binding.argument(), goal, budget, span)? {
                return Ok(false);
            }
            continue;
        }
        match (candidate, goal) {
            (Type::Int, Type::Int) | (Type::Bool, Type::Bool) | (Type::Unit, Type::Unit) => {}
            (Type::Nominal(left), Type::Nominal(right)) if left == right => {}
            (
                Type::Application(left_function, left_argument),
                Type::Application(right_function, right_argument),
            ) => {
                reserve_type_pairs(&mut pending, 2, budget, span)?;
                pending.push((left_argument, right_argument));
                pending.push((left_function, right_function));
            }
            (Type::Tuple(left), Type::Tuple(right)) if left.len() == right.len() => {
                reserve_type_pairs(&mut pending, left.len(), budget, span)?;
                pending.extend(left.iter().zip(right).rev());
            }
            (
                Type::Function(left_domain, left_codomain),
                Type::Function(right_domain, right_codomain),
            ) => {
                reserve_type_pairs(&mut pending, 2, budget, span)?;
                pending.push((left_codomain, right_codomain));
                pending.push((left_domain, right_domain));
            }
            _ => return Ok(false),
        }
    }
    Ok(true)
}

fn find_evidence_binding<'a>(
    substitution: &'a [EvidenceSubstitution],
    variable: TypeVariableId,
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<Option<&'a EvidenceSubstitution>, EvidenceValidationFailure> {
    for binding in substitution {
        charge(budget, 1, span)?;
        if binding.parameter() == variable {
            return Ok(Some(binding));
        }
    }
    Ok(None)
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
                match ty {
                    Type::Int | Type::Bool | Type::Unit => {}
                    Type::Nominal(id) => {
                        if registry.nominal_parameters(*id).is_none() {
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
                    Type::Tuple(elements) if elements.len() >= 2 => {
                        charge(budget, 1, span)?;
                        pending.try_reserve(1).map_err(|_| resource(span))?;
                        pending.push(Task::Sequence(elements.iter()));
                    }
                    Type::Tuple(_) => return Err(invalid_root(span)),
                    Type::Function(domain, codomain) => {
                        charge(budget, 2, span)?;
                        pending.try_reserve(2).map_err(|_| resource(span))?;
                        pending.push(Task::Visit(codomain));
                        pending.push(Task::Visit(domain));
                    }
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

fn same_type_charged(
    left: &Type,
    right: &Type,
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<bool, EvidenceValidationFailure> {
    let mut pending = Vec::new();
    reserve_type_pairs(&mut pending, 1, budget, span)?;
    pending.push((left, right));
    while let Some((left, right)) = pending.pop() {
        charge(budget, 1, span)?;
        match (left, right) {
            (Type::Int, Type::Int) | (Type::Bool, Type::Bool) | (Type::Unit, Type::Unit) => {}
            (Type::Nominal(left), Type::Nominal(right)) if left == right => {}
            (Type::Variable(left), Type::Variable(right)) if left == right => {}
            (
                Type::Application(left_function, left_argument),
                Type::Application(right_function, right_argument),
            ) => {
                reserve_type_pairs(&mut pending, 2, budget, span)?;
                pending.push((left_argument, right_argument));
                pending.push((left_function, right_function));
            }
            (Type::Tuple(left), Type::Tuple(right)) if left.len() == right.len() => {
                reserve_type_pairs(&mut pending, left.len(), budget, span)?;
                pending.extend(left.iter().zip(right).rev());
            }
            (
                Type::Function(left_domain, left_codomain),
                Type::Function(right_domain, right_codomain),
            ) => {
                reserve_type_pairs(&mut pending, 2, budget, span)?;
                pending.push((left_codomain, right_codomain));
                pending.push((left_domain, right_domain));
            }
            _ => return Ok(false),
        }
    }
    Ok(true)
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

fn same_binder_metadata_charged(
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
        {
            return Ok(false);
        }
    }
    Ok(true)
}

fn same_parameter_pairs_to_records_charged(
    pairs: &[(TypeVariableId, Kind)],
    records: &[ResolvedTypeVariable],
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<bool, EvidenceValidationFailure> {
    if pairs.len() != records.len() {
        return Ok(false);
    }
    for ((identity, kind), record) in pairs.iter().zip(records) {
        charge(budget, 1, span)?;
        if *identity != record.id
            || !same_kind_with_charge(kind, &record.kind, || budget.charge(1))
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

fn reserve_type_pairs<'a>(
    pending: &mut Vec<(&'a Type, &'a Type)>,
    additional: usize,
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<(), EvidenceValidationFailure> {
    charge(budget, additional, span)?;
    pending.try_reserve(additional).map_err(|_| resource(span))
}

struct TypeBuffer(Vec<Type>);

impl TypeBuffer {
    fn new() -> Self {
        Self(Vec::new())
    }

    fn len(&self) -> usize {
        self.0.len()
    }

    fn try_reserve(&mut self, additional: usize) -> Result<(), std::collections::TryReserveError> {
        self.0.try_reserve(additional)
    }

    fn push(&mut self, ty: Type) {
        self.0.push(ty);
    }

    fn pop_owned(&mut self) -> Option<IterativeTypeOwner> {
        self.0.pop().map(IterativeTypeOwner::new)
    }

    fn split_off(&mut self, at: usize) -> Self {
        Self(self.0.split_off(at))
    }

    fn into_boxed_slice(mut self) -> Box<[Type]> {
        std::mem::take(&mut self.0).into_boxed_slice()
    }

    fn into_one(mut self) -> Option<Type> {
        (self.0.len() == 1).then(|| self.0.pop().expect("a singleton buffer has one type"))
    }
}

impl Drop for TypeBuffer {
    fn drop(&mut self) {
        for ty in self.0.drain(..) {
            discard_type_iteratively(ty);
        }
    }
}

fn substitute_evidence_type(
    root: &Type,
    substitution: &[EvidenceSubstitution],
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<Type, EvidenceValidationFailure> {
    enum Task<'a> {
        Visit(&'a Type, bool),
        Sequence(std::slice::Iter<'a, Type>, bool),
        FinishTuple(usize),
        FinishApplication,
        FinishFunction,
    }

    let mut work = Vec::new();
    charge(budget, 1, span)?;
    work.try_reserve(1).map_err(|_| resource(span))?;
    work.push(Task::Visit(root, true));
    let mut rebuilt = TypeBuffer::new();
    while let Some(task) = work.pop() {
        match task {
            Task::Visit(Type::Variable(variable), true) => {
                let binding = find_evidence_binding(substitution, *variable, budget, span)?
                    .ok_or_else(|| invalid_root(span))?;
                charge(budget, 1, span)?;
                work.try_reserve(1).map_err(|_| resource(span))?;
                work.push(Task::Visit(binding.argument(), false));
            }
            Task::Visit(Type::Int, _) => {
                charge_and_push_type(&mut rebuilt, Type::Int, budget, span)?
            }
            Task::Visit(Type::Bool, _) => {
                charge_and_push_type(&mut rebuilt, Type::Bool, budget, span)?
            }
            Task::Visit(Type::Unit, _) => {
                charge_and_push_type(&mut rebuilt, Type::Unit, budget, span)?
            }
            Task::Visit(Type::Nominal(id), _) => {
                charge_and_push_type(&mut rebuilt, Type::Nominal(*id), budget, span)?
            }
            Task::Visit(Type::Variable(id), _) => {
                charge_and_push_type(&mut rebuilt, Type::Variable(*id), budget, span)?
            }
            Task::Visit(Type::Inference(_), _) | Task::Visit(Type::Forall(_, _), _) => {
                return Err(invalid_root(span));
            }
            Task::Visit(Type::Tuple(elements), substitute) => {
                charge(budget, 2, span)?;
                work.try_reserve(2).map_err(|_| resource(span))?;
                work.push(Task::FinishTuple(elements.len()));
                work.push(Task::Sequence(elements.iter(), substitute));
            }
            Task::Visit(Type::Application(function, argument), substitute) => {
                charge(budget, 3, span)?;
                work.try_reserve(3).map_err(|_| resource(span))?;
                work.push(Task::FinishApplication);
                work.push(Task::Visit(argument, substitute));
                work.push(Task::Visit(function, substitute));
            }
            Task::Visit(Type::Function(domain, codomain), substitute) => {
                charge(budget, 3, span)?;
                work.try_reserve(3).map_err(|_| resource(span))?;
                work.push(Task::FinishFunction);
                work.push(Task::Visit(codomain, substitute));
                work.push(Task::Visit(domain, substitute));
            }
            Task::Sequence(mut remaining, substitute) => {
                if let Some(next) = remaining.next() {
                    charge(budget, 2, span)?;
                    work.try_reserve(2).map_err(|_| resource(span))?;
                    work.push(Task::Sequence(remaining, substitute));
                    work.push(Task::Visit(next, substitute));
                }
            }
            Task::FinishTuple(count) => {
                if count > rebuilt.len() {
                    return Err(invalid_root(span));
                }
                reserve_rebuilt_type(&mut rebuilt, budget, span)?;
                let values = rebuilt.split_off(rebuilt.len() - count);
                rebuilt.push(Type::Tuple(values.into_boxed_slice()));
            }
            Task::FinishApplication => {
                if rebuilt.len() < 2 {
                    return Err(invalid_root(span));
                }
                reserve_rebuilt_type(&mut rebuilt, budget, span)?;
                let argument = rebuilt.pop_owned().ok_or_else(|| invalid_root(span))?;
                let function = rebuilt.pop_owned().ok_or_else(|| invalid_root(span))?;
                rebuilt.push(Type::Application(
                    Box::new(function.into_inner()),
                    Box::new(argument.into_inner()),
                ));
            }
            Task::FinishFunction => {
                if rebuilt.len() < 2 {
                    return Err(invalid_root(span));
                }
                reserve_rebuilt_type(&mut rebuilt, budget, span)?;
                let codomain = rebuilt.pop_owned().ok_or_else(|| invalid_root(span))?;
                let domain = rebuilt.pop_owned().ok_or_else(|| invalid_root(span))?;
                rebuilt.push(Type::Function(
                    Box::new(domain.into_inner()),
                    Box::new(codomain.into_inner()),
                ));
            }
        }
    }
    if rebuilt.len() != 1 {
        return Err(invalid_root(span));
    }
    Ok(rebuilt.into_one().expect("one reconstructed evidence type"))
}

fn charge_and_push_type(
    rebuilt: &mut TypeBuffer,
    ty: Type,
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<(), EvidenceValidationFailure> {
    charge(budget, 1, span)?;
    rebuilt.try_reserve(1).map_err(|_| resource(span))?;
    rebuilt.push(ty);
    Ok(())
}

fn reserve_rebuilt_type(
    rebuilt: &mut TypeBuffer,
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<(), EvidenceValidationFailure> {
    charge(budget, 1, span)?;
    rebuilt.try_reserve(1).map_err(|_| resource(span))
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

fn validate_requirements(
    scheme: &ConstrainedScheme,
    owner: RequirementOwner,
    variables: &[TypeVariableId],
    registry: &LinkedInterfaceRegistry,
    program: &ResolvedModuleProgram,
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<(), EvidenceValidationFailure> {
    for (ordinal, requirement) in scheme.requirements.iter().enumerate() {
        validate_requirement(
            requirement,
            owner,
            ordinal,
            variables,
            registry,
            program,
            budget,
        )?;
    }
    charge(budget, 0, span)
}

fn validate_requirement(
    requirement: &CheckedRequirement,
    owner: RequirementOwner,
    ordinal: usize,
    variables: &[TypeVariableId],
    registry: &LinkedInterfaceRegistry,
    program: &ResolvedModuleProgram,
    budget: &mut InterfaceConstraintBudget,
) -> Result<(), EvidenceValidationFailure> {
    charge(budget, 1, requirement.span)?;
    validate_linked_type_with_policy(
        &requirement.argument,
        program.registry(),
        variables,
        budget,
        requirement.span,
    )?;
    if requirement.id.owner() != owner
        || usize::try_from(requirement.id.declaration()) != Ok(ordinal)
        || registry.interface(program, requirement.interface).is_none()
    {
        return Err(unknown(requirement.span));
    }
    Ok(())
}

fn schedule_block<'a>(
    pending: &mut Vec<&'a ResolvedExpr>,
    block: &'a ResolvedBlock,
    budget: &mut InterfaceConstraintBudget,
) -> Result<(), EvidenceValidationFailure> {
    let mut additional = 1usize;
    for declaration in &block.declarations {
        charge(budget, 1, block.span)?;
        match declaration {
            ResolvedLocalDeclaration::Binding(_) => {
                additional = additional
                    .checked_add(1)
                    .ok_or_else(|| resource(block.span))?;
            }
            ResolvedLocalDeclaration::Recursive(group) => {
                for _ in &group.members {
                    charge(budget, 1, block.span)?;
                    additional = additional
                        .checked_add(1)
                        .ok_or_else(|| resource(block.span))?;
                }
            }
        }
    }
    reserve_expressions(pending, additional, budget, block.span)?;
    pending.push(block.result.as_ref());
    for declaration in block.declarations.iter().rev() {
        match declaration {
            ResolvedLocalDeclaration::Binding(binding) => pending.push(&binding.initializer),
            ResolvedLocalDeclaration::Recursive(group) => {
                pending.extend(group.members.iter().rev().map(|member| &member.initializer));
            }
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
        fs,
        path::PathBuf,
        sync::atomic::{AtomicU64, Ordering},
        thread,
    };

    use super::*;
    use crate::{
        elaborate::{
            check_module, link_modules, link_modules_with_budget, link_modules_with_budgets,
        },
        interface::{EvidenceSelectionBuilder, match_implementation_head_structurally},
        module::{ModuleGraph, ModuleRoots, load_module_graph},
        resolve::{DependencyExports, resolve_module},
        resolved::{
            CheckedModule, ImplementationRoute, ImplementationRouteHop,
            LinkedCarrierMutationForTest, LinkedGlobalParameterRowMutationForTest,
            ResolvedTypeVariable, same_imported_constructor_fact_with_budget,
        },
        source::{ByteRange, SourceFile},
        types::{InferenceVariableId, Kind, NominalTypeId, Type, TypeVariableId, TypeWorkBudget},
    };

    static FIXTURE_IDS: AtomicU64 = AtomicU64::new(0);

    fn validate_direct_linked_value_type(
        program: &ResolvedModuleProgram,
        ty: &Type,
        variables: &[TypeVariableId],
    ) -> Result<(), EvidenceValidationFailure> {
        let span = program.result().span;
        let mut type_work = TypeWorkBudget::default();
        let mut environments =
            build_linked_kind_environments(program.registry(), &mut type_work, span)?;
        validate_linked_value_type(
            ty,
            program.registry(),
            variables,
            &mut environments,
            &mut InterfaceConstraintBudget::default(),
            &mut type_work,
            span,
        )
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

    #[test]
    fn declaration_head_and_prerequisite_kind_authentication_has_exact_dual_limits() {
        // The head Wrap<A> consumes nine constraint units and the prerequisite
        // A consumes three. Each occurrence installs one canonical binder
        // lookup plus one retained DELTA record: 9 + 3 and 2 + 2.
        const CONSTRAINT_WORK: usize = 12;
        const TYPE_WORK: usize = 4;
        let program = generic_program();
        let group = &program.groups()[0];
        let fact = &group.implementation_facts()[1];
        let interface = &group.interface_facts()[0];
        let variables = fact
            .head_parameters
            .iter()
            .map(|parameter| parameter.id)
            .collect::<Vec<_>>();
        let interface_parameter = program
            .registry()
            .type_variable(interface.parameter.id)
            .expect("the interface parameter should be canonical");
        let prerequisite = &fact.prerequisites[0];
        let authenticate = |constraint_limit, type_limit| {
            let mut environments = build_linked_kind_environments(
                program.registry(),
                &mut TypeWorkBudget::default(),
                fact.span,
            )
            .expect("the nominal environment should fit outside the measured operation");
            environments
                .insert_interface(
                    interface.id,
                    &interface_parameter.kind,
                    interface_parameter.origin.primary_span(),
                    &mut TypeWorkBudget::default(),
                )
                .expect("the interface environment should fit outside the measured operation");
            let mut constraint_work = InterfaceConstraintBudget::with_limit(constraint_limit);
            let mut type_work = TypeWorkBudget::with_limit(type_limit);
            let result = (|| {
                authenticate_linked_interface_argument_kind(
                    &fact.argument,
                    fact.interface,
                    program.registry(),
                    &variables,
                    None,
                    &mut environments,
                    &mut constraint_work,
                    &mut type_work,
                    fact.span,
                )?;
                authenticate_linked_interface_argument_kind(
                    &prerequisite.argument,
                    prerequisite.interface,
                    program.registry(),
                    &variables,
                    None,
                    &mut environments,
                    &mut constraint_work,
                    &mut type_work,
                    prerequisite.span,
                )
            })();
            (result, constraint_work.used(), type_work.used())
        };

        let (failure, constraint_used, type_used) = authenticate(CONSTRAINT_WORK - 1, TYPE_WORK);
        assert_eq!(
            failure
                .expect_err("one-short constraint work must prevent authentication")
                .reason(),
            EvidenceValidationReason::ConstraintResourceExhausted,
        );
        assert_eq!(constraint_used, CONSTRAINT_WORK - 1);
        assert_eq!(type_used, TYPE_WORK);

        let (failure, constraint_used, type_used) = authenticate(CONSTRAINT_WORK, TYPE_WORK - 1);
        assert_eq!(
            failure
                .expect_err("one-short TypeWork must prevent authentication")
                .reason(),
            EvidenceValidationReason::TypeResourceExhausted,
        );
        assert_eq!(constraint_used, 9);
        assert_eq!(type_used, TYPE_WORK - 1);

        let (result, constraint_used, type_used) = authenticate(CONSTRAINT_WORK, TYPE_WORK);
        result.expect("the exact declaration Kind budgets should fit");
        assert_eq!(constraint_used, CONSTRAINT_WORK);
        assert_eq!(type_used, TYPE_WORK);
    }

    #[test]
    fn linked_value_type_accepts_higher_kinded_variable_application() {
        let program = entry_program(concat!(
            "keep<F : Type -> Type, A> : F<A> -> F<A>\n",
            "keep value = value\n\n",
            "main : Unit -> Unit\n",
            "main () = ()\n",
        ));
        let scheme = &program.groups()[0].schemes()[0].scheme;
        let variables = scheme
            .type_parameters
            .iter()
            .map(|(identity, _)| *identity)
            .collect::<Vec<_>>();

        validate_direct_linked_value_type(&program, &scheme.value_type, &variables)
            .expect("a function-kinded binder may be applied inside a linked value type");
    }

    #[test]
    fn linked_value_type_accepts_partial_nominal_constructor_argument() {
        let program = entry_program(concat!(
            "type Pair<A, B> = Pair(A, B)\n",
            "type Higher<F : Type -> Type> = Higher(F<Int>)\n\n",
            "main : Unit -> Unit\n",
            "main () = ()\n",
        ));
        let [pair, higher] = program.registry().nominals() else {
            panic!("the fixture should retain Pair and Higher in source order");
        };
        let partial_pair = Type::Application(Box::new(Type::Nominal(pair.id)), Box::new(Type::Int));
        let value_type =
            Type::Application(Box::new(Type::Nominal(higher.id)), Box::new(partial_pair));

        validate_direct_linked_value_type(&program, &value_type, &[])
            .expect("a partial constructor may satisfy a higher-kinded nominal parameter");
    }

    #[test]
    fn linked_value_type_rejects_wrong_higher_kinded_application_domain() {
        let program = entry_program(concat!(
            "type Option<A> =\nNone\n| Some(A)\n\n",
            "keep<F : Type -> Type> : F<Int> -> F<Int>\n",
            "keep value = value\n\n",
            "main : Unit -> Unit\n",
            "main () = ()\n",
        ));
        let scheme = &program.groups()[0].schemes()[0].scheme;
        let function = scheme.type_parameters[0].0;
        let option = program.registry().nominals()[0].id;
        let wrong = Type::Application(
            Box::new(Type::Variable(function)),
            Box::new(Type::Nominal(option)),
        );

        assert_eq!(
            validate_direct_linked_value_type(&program, &wrong, &[function],)
                .expect_err("F expects a Type argument, not a Type constructor")
                .reason(),
            EvidenceValidationReason::UnknownIdentity,
        );
    }

    #[test]
    fn linked_value_type_rejects_application_of_type_kinded_variable() {
        let program = entry_program(concat!(
            "identity<A> : A -> A\n",
            "identity value = value\n\n",
            "main : Unit -> Unit\n",
            "main () = ()\n",
        ));
        let parameter = program.groups()[0].schemes()[0].scheme.type_parameters[0].0;
        let wrong = Type::Application(Box::new(Type::Variable(parameter)), Box::new(Type::Int));

        assert_eq!(
            validate_direct_linked_value_type(&program, &wrong, &[parameter],)
                .expect_err("a Type-kinded binder is not applicable")
                .reason(),
            EvidenceValidationReason::UnknownIdentity,
        );
    }

    #[test]
    fn linked_value_structure_owns_scope_inference_and_scheme_exclusions() {
        let program = entry_program(concat!(
            "identity<A> : A -> A\n",
            "identity value = value\n\n",
            "main : Unit -> Unit\n",
            "main () = ()\n",
        ));
        let parameter = program.groups()[0].schemes()[0].scheme.type_parameters[0].0;
        let cases = [
            Type::Variable(parameter),
            Type::Inference(InferenceVariableId::new(0)),
            Type::Forall(
                vec![(parameter, Kind::Type)].into_boxed_slice(),
                Box::new(Type::Variable(parameter)),
            ),
        ];

        for ty in &cases {
            let mut constraint_work = InterfaceConstraintBudget::default();
            assert_eq!(
                validate_linked_value_structure(
                    ty,
                    program.registry(),
                    &[],
                    &mut constraint_work,
                    program.result().span,
                )
                .expect_err("linked monotypes reject missing scope, inference, and nested schemes")
                .reason(),
                EvidenceValidationReason::UnknownIdentity,
            );
        }
    }

    #[test]
    fn linked_value_kind_validation_has_exact_dual_limits() {
        // Predecessor linked-fact authentication owns exactly 18 structural
        // cells. The later pass therefore charges only eighteen synthesis and
        // comparison cells plus one root-Type comparison = 20. Type work is
        // two owner binders * (1 canonical lookup + 1 retained DELTA record) = 4.
        const STRUCTURAL_WORK: usize = 18;
        const CONSTRAINT_WORK: usize = 20;
        const TYPE_WORK: usize = 4;
        let program = entry_program(concat!(
            "keep<F : Type -> Type, A> : F<A> -> F<A>\n",
            "keep value = value\n\n",
            "main : Unit -> Unit\n",
            "main () = ()\n",
        ));
        let scheme = &program.groups()[0].schemes()[0].scheme;
        let variables = scheme
            .type_parameters
            .iter()
            .map(|(identity, _)| *identity)
            .collect::<Vec<_>>();
        let span = program.groups()[0].span();

        let mut structural_short = InterfaceConstraintBudget::with_limit(STRUCTURAL_WORK - 1);
        assert_eq!(
            validate_linked_value_structure(
                &scheme.value_type,
                program.registry(),
                &variables,
                &mut structural_short,
                span,
            )
            .expect_err("one-short predecessor structural work should fail")
            .reason(),
            EvidenceValidationReason::ConstraintResourceExhausted,
        );
        assert_eq!(structural_short.used(), STRUCTURAL_WORK - 1);

        let mut structural_exact = InterfaceConstraintBudget::with_limit(STRUCTURAL_WORK);
        validate_linked_value_structure(
            &scheme.value_type,
            program.registry(),
            &variables,
            &mut structural_exact,
            span,
        )
        .expect("the exact predecessor structural boundary should fit");
        assert_eq!(structural_exact.used(), STRUCTURAL_WORK);

        let mut constraint_short = InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK - 1);
        let mut type_exact = TypeWorkBudget::with_limit(TYPE_WORK);
        let mut environments =
            build_linked_kind_environments(program.registry(), &mut type_exact, span)
                .expect("the empty XI should fit");
        assert_eq!(
            validate_linked_value_type(
                &scheme.value_type,
                program.registry(),
                &variables,
                &mut environments,
                &mut constraint_short,
                &mut type_exact,
                span,
            )
            .expect_err("one-short constraint work should fail atomically")
            .reason(),
            EvidenceValidationReason::ConstraintResourceExhausted,
        );
        assert_eq!(constraint_short.used(), CONSTRAINT_WORK - 1);
        assert_eq!(type_exact.used(), TYPE_WORK);

        let mut constraint_for_type_short = InterfaceConstraintBudget::default();
        let mut type_short = TypeWorkBudget::with_limit(TYPE_WORK - 1);
        let mut environments =
            build_linked_kind_environments(program.registry(), &mut type_short, span)
                .expect("the empty XI should fit");
        assert_eq!(
            validate_linked_value_type(
                &scheme.value_type,
                program.registry(),
                &variables,
                &mut environments,
                &mut constraint_for_type_short,
                &mut type_short,
                span,
            )
            .expect_err("one-short DELTA retention should fail atomically")
            .reason(),
            EvidenceValidationReason::TypeResourceExhausted,
        );
        assert_eq!(type_short.used(), TYPE_WORK - 1);

        let mut constraint_exact = InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK);
        let mut type_exact = TypeWorkBudget::with_limit(TYPE_WORK);
        let mut environments =
            build_linked_kind_environments(program.registry(), &mut type_exact, span)
                .expect("the empty XI should fit");
        validate_linked_value_type(
            &scheme.value_type,
            program.registry(),
            &variables,
            &mut environments,
            &mut constraint_exact,
            &mut type_exact,
            span,
        )
        .expect("the higher-kinded value type should validate");
        assert_eq!(constraint_exact.used(), CONSTRAINT_WORK);
        assert_eq!(type_exact.used(), TYPE_WORK);
        assert_eq!(
            scheme.type_parameters.len(),
            2,
            "failed attempts do not mutate the scheme"
        );
    }

    #[test]
    fn linked_nominal_kinds_are_retained_once_for_all_value_schemes() {
        // XI is retained once for the graph. For each nominal, the exact type
        // work is one environment record, one Type result, and for every
        // parameter its Kind nodes plus one Arrow node:
        //
        //   Σ_nominal [2 + Σ_parameter (|K| + 1)]
        //
        // Option<A> therefore costs 2 + (1 + 1) = 4 and
        // Higher<F : Type -> Type> costs 2 + (3 + 1) = 6, for 10 total.
        // Validating two schemes that share both constructors must not rebuild
        // XI or spend further type work.
        const XI_WORK: usize = 10;
        let program = entry_program(concat!(
            "type Option<A> =\nNone\n| Some(A)\n\n",
            "type Higher<F : Type -> Type> = Higher(F<Int>)\n\n",
            "first : Higher<Option> -> Higher<Option>\n",
            "first value = value\n\n",
            "second : Higher<Option> -> Higher<Option>\n",
            "second value = value\n\n",
            "main : Unit -> Unit\n",
            "main () = ()\n",
        ));
        let span = program.result().span;

        let mut short = TypeWorkBudget::with_limit(XI_WORK - 1);
        let Err(failure) = build_linked_kind_environments(program.registry(), &mut short, span)
        else {
            panic!("one-short XI retention must fail before publication");
        };
        assert_eq!(
            failure.reason(),
            EvidenceValidationReason::TypeResourceExhausted,
        );
        assert_eq!(short.used(), XI_WORK - 1);

        let mut exact = TypeWorkBudget::with_limit(XI_WORK);
        let mut environments = build_linked_kind_environments(program.registry(), &mut exact, span)
            .expect("the exact XI retention budget should succeed");
        assert_eq!(exact.used(), XI_WORK);
        validate_linked_value_schemes(
            &program,
            &mut environments,
            &mut InterfaceConstraintBudget::default(),
            &mut exact,
        )
        .expect("both schemes may reuse the graph-lifetime nominal environment");
        assert_eq!(
            exact.used(),
            XI_WORK,
            "linked value schemes must not rebuild the nominal environment",
        );
        assert!(program.groups()[0].schemes().len() >= 2);
    }

    #[test]
    fn deep_linked_value_kinding_is_exact_and_stack_safe() {
        const DEPTH: usize = 32_768;
        // Predecessor linked-fact authentication owns structural admission.
        // Total Kind authentication is 6D + 3: one reusable current-state
        // slot, one continuation plus one visited Application per layer,
        // 2D + 1 for the deep variable Kind lookup, one primitive visit and
        // one domain comparison per layer, and one root-Type comparison.
        // Leaving one argument unapplied removes four synthesis cells.
        const VALID_WORK: usize = 6 * DEPTH + 3;
        const RESIDUAL_WORK: usize = 6 * DEPTH - 1;
        const TYPE_WORK: usize = 2;

        thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                fn fixture(applications: usize) -> (ResolvedRegistry, Type, TypeVariableId, Span) {
                    let source = SourceFile::new("deep-linked-kind.ash", "F")
                        .expect("the deep fixture source should fit");
                    let span = source
                        .span(ByteRange::new(0, 1).expect("the binder range should be ordered"))
                        .expect("the binder range should belong to the fixture");
                    let identity = TypeVariableId::resolved(ModuleId::new(0), 0);
                    let mut kind = Kind::Type;
                    for _ in 0..DEPTH {
                        kind = Kind::Arrow(Box::new(Kind::Type), Box::new(kind));
                    }
                    let registry = ResolvedRegistry::new(Vec::new(), Vec::new())
                        .with_additional_type_variables([ResolvedTypeVariable {
                            id: identity,
                            spelling: "F".to_owned(),
                            kind,
                            origin: Origin::Source(span),
                        }]);
                    let mut ty = Type::Variable(identity);
                    for _ in 0..applications {
                        ty = Type::Application(Box::new(ty), Box::new(Type::Int));
                    }
                    (registry, ty, identity, span)
                }

                let (registry, valid, identity, span) = fixture(DEPTH);
                let valid = IterativeTypeOwner::new(valid);
                let mut type_work = TypeWorkBudget::with_limit(TYPE_WORK);
                let mut environments =
                    build_linked_kind_environments(&registry, &mut type_work, span)
                        .expect("the empty XI should fit");
                let mut default = InterfaceConstraintBudget::default();
                validate_linked_value_type(
                    &valid,
                    &registry,
                    &[identity],
                    &mut environments,
                    &mut default,
                    &mut type_work,
                    span,
                )
                .expect("the admitted deep linked value must fit the production budget");
                assert_eq!(default.used(), VALID_WORK);

                drop(environments);
                let mut type_work = TypeWorkBudget::with_limit(TYPE_WORK);
                let mut environments =
                    build_linked_kind_environments(&registry, &mut type_work, span)
                        .expect("the empty XI should fit");
                let mut one_short = InterfaceConstraintBudget::with_limit(VALID_WORK - 1);
                assert_eq!(
                    validate_linked_value_type(
                        &valid,
                        &registry,
                        &[identity],
                        &mut environments,
                        &mut one_short,
                        &mut type_work,
                        span,
                    )
                    .expect_err("one-short work must reject at the late root comparison")
                    .reason(),
                    EvidenceValidationReason::ConstraintResourceExhausted,
                );
                assert_eq!(one_short.used(), VALID_WORK - 1);
                assert!(registry.type_variable(identity).is_some());

                drop(environments);
                let mut type_work = TypeWorkBudget::with_limit(TYPE_WORK);
                let mut environments =
                    build_linked_kind_environments(&registry, &mut type_work, span)
                        .expect("the empty XI should fit");
                let mut exact = InterfaceConstraintBudget::with_limit(VALID_WORK);
                validate_linked_value_type(
                    &valid,
                    &registry,
                    &[identity],
                    &mut environments,
                    &mut exact,
                    &mut type_work,
                    span,
                )
                .expect("the exact deep linked value boundary should succeed");
                assert_eq!(exact.used(), VALID_WORK);

                let (registry, residual, identity, span) = fixture(DEPTH - 1);
                let residual = IterativeTypeOwner::new(residual);
                let mut type_work = TypeWorkBudget::with_limit(TYPE_WORK);
                let mut environments =
                    build_linked_kind_environments(&registry, &mut type_work, span)
                        .expect("the empty XI should fit");
                let mut exact_rejection = InterfaceConstraintBudget::with_limit(RESIDUAL_WORK);
                assert_eq!(
                    validate_linked_value_type(
                        &residual,
                        &registry,
                        &[identity],
                        &mut environments,
                        &mut exact_rejection,
                        &mut type_work,
                        span,
                    )
                    .expect_err("a residual constructor Kind is not a linked value type")
                    .reason(),
                    EvidenceValidationReason::UnknownIdentity,
                );
                assert_eq!(exact_rejection.used(), RESIDUAL_WORK);
                assert!(registry.type_variable(identity).is_some());
            })
            .expect("the small-stack kinding worker should spawn")
            .join()
            .expect("deep linked kinding and teardown should remain iterative");
    }

    #[test]
    fn deep_public_linked_value_kinding_fits_the_default_budget_on_a_small_stack() {
        const DEPTH: usize = 32_768;
        // Checked/source type equality is fused into synthesis. The canonical
        // lookup separately charges both checked and source Kind pairs, while
        // each scheduled codomain owns one continuation cell. Iterative
        // source-binder provenance owns its retained Origin cell. One retained
        // coverage-set cell proves the owner binder was visited; the module
        // and binder-owner authentication indexes add two fixed cells. Linked
        // registry-row authentication visits the identity row and parameter.
        const ROW_WORK: usize = 2;
        const EXACT_WORK: usize = 9 * DEPTH + 63 + ROW_WORK;
        // TypeWork retains only the two canonical environment records.
        const EXACT_TYPE_WORK: usize = 2;

        thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                fn deep_kind() -> Kind {
                    let mut kind = Kind::Type;
                    for _ in 0..DEPTH {
                        kind = Kind::Arrow(Box::new(Kind::Type), Box::new(kind));
                    }
                    kind
                }

                fn deep_value_type(parameter: TypeVariableId) -> Type {
                    let mut ty = Type::Variable(parameter);
                    for _ in 0..DEPTH {
                        ty = Type::Application(Box::new(ty), Box::new(Type::Int));
                    }
                    ty
                }

                fn fixture() -> ResolvedModuleProgram {
                    let mut program = entry_program(concat!(
                        "identity<A> : A -> A\n",
                        "identity value = value\n\n",
                        "main : Unit -> Unit\n",
                        "main () = ()\n",
                    ));
                    let module = program.groups()[0].module();
                    let parameter = program.groups()[0].schemes()[0].scheme.type_parameters[0].0;
                    let canonical = program
                        .registry()
                        .type_variable(parameter)
                        .expect("the source binder should be canonical");
                    let canonical_parameter = ResolvedTypeVariable {
                        id: parameter,
                        spelling: canonical.spelling.clone(),
                        kind: deep_kind(),
                        origin: canonical.origin.clone(),
                    };
                    assert!(program.replace_first_global_kind_boundary_for_test(
                        module,
                        (canonical_parameter, deep_kind(), deep_kind()),
                        (deep_value_type(parameter), deep_value_type(parameter)),
                    ));
                    program
                }

                let mut one_short = InterfaceConstraintBudget::with_limit(EXACT_WORK - 1);
                let failure = validate_interface_evidence_with_budget(
                    fixture(),
                    &mut one_short,
                    &mut TypeWorkBudget::default(),
                )
                .expect_err("one-short public work must not publish a validated program");
                assert_eq!(
                    failure.reason(),
                    EvidenceValidationReason::ConstraintResourceExhausted,
                );
                assert_eq!(one_short.used(), EXACT_WORK - 1);

                let mut type_one_short = TypeWorkBudget::with_limit(EXACT_TYPE_WORK - 1);
                let failure = validate_interface_evidence_with_budget(
                    fixture(),
                    &mut InterfaceConstraintBudget::with_limit(EXACT_WORK),
                    &mut type_one_short,
                )
                .expect_err("one-short linked Kind-mirror work must prevent publication");
                assert_eq!(
                    failure.reason(),
                    EvidenceValidationReason::TypeResourceExhausted,
                );
                assert_eq!(type_one_short.used(), EXACT_TYPE_WORK - 1);

                let mut exact = InterfaceConstraintBudget::with_limit(EXACT_WORK);
                let mut type_work = TypeWorkBudget::with_limit(EXACT_TYPE_WORK);
                validate_interface_evidence_with_budget(fixture(), &mut exact, &mut type_work)
                    .expect("the exact public linked Kind budget should validate");
                assert_eq!(exact.used(), EXACT_WORK);
                assert_eq!(type_work.used(), EXACT_TYPE_WORK);

                validate_interface_evidence(fixture())
                    .expect("the admitted deep linked program must fit the production budget");
            })
            .expect("the public linked-kinding worker should spawn")
            .join()
            .expect("public linked kinding and teardown should remain iterative");
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
        const DEPTH: usize = 32_768;
        let fixture = ValidationFixture::create(concat!(
            "import dependency (Deep, Make)\n",
            "main : Unit -> Unit\nmain value = value\n",
        ));
        fixture.write("dependency.ash", "pub type Deep = Make(Unit)\n");
        let graph = fixture.graph();
        let mut checked = Vec::new();
        let mut constructor = None;

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
            if module.id() != graph.entry() {
                let id = resolved.registry().constructors()[0].id;
                let mut payload = Type::Unit;
                for _ in 0..DEPTH {
                    payload = Type::Function(Box::new(Type::Int), Box::new(payload));
                }
                assert!(resolved.replace_local_constructor_payload_for_test(id, payload));
                constructor = Some(id);
            } else {
                let id = constructor.expect("the defining constructor should precede the entry");
                let exported = checked[0]
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
            checked.push(
                check_module(resolved)
                    .expect("checking should consume the imported physical scheme iteratively"),
            );
        }
        (checked, graph.entry())
    }

    #[test]
    fn deep_constructor_scheme_crosses_check_and_link_then_is_disposed_before_core() {
        // Seven graph/link cells precede the combined registry's twelve fixed
        // module/nominal/family/constructor/global inventory cells.
        const LINK_CONSTRAINT_WORK: usize = 7 + 12;
        const ONE_SHORT_PREFIX: usize = 7;
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
                link_modules_with_budget(short_modules, short_entry, &mut one_short)
                    .expect_err("one missing late-link cell must reject before publication");
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

    fn entry_program(source: &str) -> ResolvedModuleProgram {
        let fixture = ValidationFixture::create(source);
        let graph = fixture.graph();
        link_modules(check_graph(&graph), graph.entry()).expect("the entry fixture should link")
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
        builder
            .finish(root, interface, argument)
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

    fn multi_module_all_binder_owner_program() -> ResolvedModuleProgram {
        let fixture = ValidationFixture::create(concat!(
            "import dependency (relay)\n",
            "main : Unit -> Unit\nmain () = ()\n",
        ));
        fixture.write(
            "dependency.ash",
            concat!(
                "pub type Wrapped<F : Type -> Type, A> = Wrapped(F<A>)\n\n",
                "pub interface Extract<A> {\nextract : A -> A\n}\n\n",
                "pub impl<F : Type -> Type, A> Extract<Wrapped<F, A>> {\n",
                "extract value = value\n",
                "}\n\n",
                "pub relay<G : Type -> Type> : G<Int> -> G<Int>\n",
                "relay value = value\n",
            ),
        );
        let graph = fixture.graph();
        link_modules(check_graph(&graph), graph.entry())
            .expect("the all-binder-owner fixture should link")
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
    fn linked_registry_rejects_every_resolved_global_parameter_row_mutation_before_core() {
        let mutations = [
            LinkedGlobalParameterRowMutationForTest::Owner,
            LinkedGlobalParameterRowMutationForTest::ParameterIdentity,
            LinkedGlobalParameterRowMutationForTest::ParameterOrder,
            LinkedGlobalParameterRowMutationForTest::RowOrder,
            LinkedGlobalParameterRowMutationForTest::OwnerPosition,
            LinkedGlobalParameterRowMutationForTest::MissingRow,
            LinkedGlobalParameterRowMutationForTest::ExtraRow,
            LinkedGlobalParameterRowMutationForTest::DuplicateOwner,
        ];
        for mutation in mutations {
            let mut program = linked_registry_row_program();
            let [first_row, second_row] = program.registry().global_parameter_rows() else {
                panic!("the linked fixture must retain exactly two global rows");
            };
            let original_owners = [first_row.owner(), second_row.owner()];
            let original_parameters = [
                first_row.parameters().to_vec(),
                second_row.parameters().to_vec(),
            ];
            let empty_owner = program
                .groups()
                .iter()
                .flat_map(|group| group.schemes())
                .find(|scheme| scheme.scheme.type_parameters.is_empty())
                .map(|scheme| scheme.binder)
                .expect("the linked fixture must retain an empty-scheme owner");
            let scheme_spans = program
                .groups()
                .iter()
                .flat_map(|group| group.schemes())
                .filter(|scheme| !scheme.scheme.type_parameters.is_empty())
                .map(|scheme| scheme.origin.primary_span())
                .collect::<Vec<_>>();
            let [first_span, second_span] = scheme_spans.as_slice() else {
                panic!("the linked fixture must retain exactly two non-empty schemes");
            };
            let result_span = program.result().span;
            let expected_primary = match mutation {
                LinkedGlobalParameterRowMutationForTest::Owner
                | LinkedGlobalParameterRowMutationForTest::ParameterIdentity
                | LinkedGlobalParameterRowMutationForTest::ParameterOrder
                | LinkedGlobalParameterRowMutationForTest::RowOrder
                | LinkedGlobalParameterRowMutationForTest::OwnerPosition => *first_span,
                LinkedGlobalParameterRowMutationForTest::MissingRow
                | LinkedGlobalParameterRowMutationForTest::DuplicateOwner => *second_span,
                LinkedGlobalParameterRowMutationForTest::ExtraRow => result_span,
            };
            assert!(
                program.corrupt_linked_global_parameter_rows_for_test(mutation),
                "the linked fixture must support {mutation:?}",
            );
            match mutation {
                LinkedGlobalParameterRowMutationForTest::Owner => {
                    let rows = program.registry().global_parameter_rows();
                    assert_eq!(rows.len(), 2);
                    assert_eq!(rows[0].owner(), empty_owner);
                    assert_eq!(rows[0].parameters(), original_parameters[0].as_slice());
                    assert!(
                        program
                            .registry()
                            .global_parameter_row(original_owners[0])
                            .is_none()
                    );
                    assert!(std::ptr::eq(
                        program
                            .registry()
                            .global_parameter_row(empty_owner)
                            .expect("the replacement owner index must remain coherent"),
                        &rows[0],
                    ));
                }
                LinkedGlobalParameterRowMutationForTest::RowOrder => {
                    let rows = program.registry().global_parameter_rows();
                    assert_eq!(rows.len(), 2);
                    assert_eq!(rows[0].owner(), original_owners[1]);
                    assert_eq!(rows[1].owner(), original_owners[0]);
                    assert_eq!(rows[0].parameters(), original_parameters[1].as_slice());
                    assert_eq!(rows[1].parameters(), original_parameters[0].as_slice());
                    assert!(std::ptr::eq(
                        program
                            .registry()
                            .global_parameter_row(original_owners[1])
                            .expect("the moved second owner index must remain coherent"),
                        &rows[0],
                    ));
                    assert!(std::ptr::eq(
                        program
                            .registry()
                            .global_parameter_row(original_owners[0])
                            .expect("the moved first owner index must remain coherent"),
                        &rows[1],
                    ));
                }
                LinkedGlobalParameterRowMutationForTest::DuplicateOwner => {
                    let rows = program.registry().global_parameter_rows();
                    assert_eq!(rows.len(), 2);
                    assert_eq!(rows[0].owner(), original_owners[0]);
                    assert_eq!(rows[1].owner(), original_owners[0]);
                    assert_eq!(rows[0].parameters(), original_parameters[0].as_slice());
                    assert_eq!(rows[1].parameters(), original_parameters[1].as_slice());
                    assert!(std::ptr::eq(
                        program
                            .registry()
                            .global_parameter_row(original_owners[0])
                            .expect("the first duplicate owner position must remain authoritative"),
                        &rows[0],
                    ));
                    assert!(
                        program
                            .registry()
                            .global_parameter_row(original_owners[1])
                            .is_none()
                    );
                }
                LinkedGlobalParameterRowMutationForTest::ParameterIdentity => {
                    let rows = program.registry().global_parameter_rows();
                    assert_eq!(rows.len(), 2);
                    assert_eq!([rows[0].owner(), rows[1].owner()], original_owners,);
                    let replacement = rows[0].parameters()[0];
                    assert_ne!(replacement, original_parameters[0][0]);
                    assert!(original_parameters[1].contains(&replacement));
                    assert_eq!(
                        program
                            .registry()
                            .type_variable(replacement)
                            .expect("the replacement identity must remain canonical")
                            .kind,
                        program
                            .registry()
                            .type_variable(original_parameters[0][0])
                            .expect("the replaced identity must remain canonical")
                            .kind,
                    );
                    assert_eq!(&rows[0].parameters()[1..], &original_parameters[0][1..],);
                    assert_eq!(rows[1].parameters(), original_parameters[1].as_slice());
                    assert!(std::ptr::eq(
                        program
                            .registry()
                            .global_parameter_row(original_owners[0])
                            .expect("the first owner index must remain coherent"),
                        &rows[0],
                    ));
                    assert!(std::ptr::eq(
                        program
                            .registry()
                            .global_parameter_row(original_owners[1])
                            .expect("the second owner index must remain coherent"),
                        &rows[1],
                    ));
                }
                LinkedGlobalParameterRowMutationForTest::ParameterOrder => {
                    let rows = program.registry().global_parameter_rows();
                    assert_eq!(rows.len(), 2);
                    assert_eq!([rows[0].owner(), rows[1].owner()], original_owners,);
                    assert_eq!(
                        rows[0].parameters(),
                        [original_parameters[0][1], original_parameters[0][0]],
                    );
                    assert_eq!(rows[1].parameters(), original_parameters[1].as_slice());
                    assert!(std::ptr::eq(
                        program
                            .registry()
                            .global_parameter_row(original_owners[0])
                            .expect("the first owner index must remain coherent"),
                        &rows[0],
                    ));
                    assert!(std::ptr::eq(
                        program
                            .registry()
                            .global_parameter_row(original_owners[1])
                            .expect("the second owner index must remain coherent"),
                        &rows[1],
                    ));
                }
                LinkedGlobalParameterRowMutationForTest::OwnerPosition => {
                    let rows = program.registry().global_parameter_rows();
                    assert_eq!(rows.len(), 2);
                    assert_eq!([rows[0].owner(), rows[1].owner()], original_owners,);
                    assert_eq!(rows[0].parameters(), original_parameters[0].as_slice());
                    assert_eq!(rows[1].parameters(), original_parameters[1].as_slice());
                    assert!(
                        program
                            .registry()
                            .global_parameter_row(original_owners[0])
                            .is_none()
                    );
                    assert!(
                        program
                            .registry()
                            .global_parameter_row(original_owners[1])
                            .is_none()
                    );
                }
                LinkedGlobalParameterRowMutationForTest::MissingRow => {
                    let rows = program.registry().global_parameter_rows();
                    assert_eq!(rows.len(), 1);
                    assert_eq!(rows[0].owner(), original_owners[0]);
                    assert_eq!(rows[0].parameters(), original_parameters[0].as_slice());
                    assert!(std::ptr::eq(
                        program
                            .registry()
                            .global_parameter_row(original_owners[0])
                            .expect("the retained owner index must remain coherent"),
                        &rows[0],
                    ));
                    assert!(
                        program
                            .registry()
                            .global_parameter_row(original_owners[1])
                            .is_none()
                    );
                }
                LinkedGlobalParameterRowMutationForTest::ExtraRow => {
                    let rows = program.registry().global_parameter_rows();
                    assert_eq!(rows.len(), 3);
                    assert_eq!([rows[0].owner(), rows[1].owner()], original_owners,);
                    assert_eq!(rows[0].parameters(), original_parameters[0].as_slice());
                    assert_eq!(rows[1].parameters(), original_parameters[1].as_slice());
                    assert_eq!(rows[2].owner(), empty_owner);
                    assert_eq!(rows[2].parameters(), [original_parameters[0][0]]);
                    assert!(std::ptr::eq(
                        program
                            .registry()
                            .global_parameter_row(original_owners[0])
                            .expect("the first owner index must remain coherent"),
                        &rows[0],
                    ));
                    assert!(std::ptr::eq(
                        program
                            .registry()
                            .global_parameter_row(original_owners[1])
                            .expect("the second owner index must remain coherent"),
                        &rows[1],
                    ));
                    assert!(std::ptr::eq(
                        program
                            .registry()
                            .global_parameter_row(empty_owner)
                            .expect("the surplus owner index must remain coherent"),
                        &rows[2],
                    ));
                }
            }
            let failure = validate_interface_evidence(program)
                .expect_err("every independent row mutation must fail before Core");
            assert_eq!(
                failure.reason(),
                EvidenceValidationReason::UnknownIdentity,
                "{mutation:?}",
            );
            assert_eq!(failure.primary(), expected_primary, "{mutation:?}");
        }
    }

    #[test]
    fn linked_registry_rows_have_exact_constraint_work_and_no_type_work() {
        let program = linked_registry_row_program();
        let row_count = program.registry().global_parameter_rows().len();
        let parameter_count = program
            .registry()
            .global_parameter_rows()
            .iter()
            .map(|row| row.parameters().len())
            .sum::<usize>();
        let exact_row_work = row_count + parameter_count;
        assert!(row_count > 1);
        assert!(parameter_count > row_count);

        let mut row_short = InterfaceConstraintBudget::with_limit(exact_row_work - 1);
        assert_eq!(
            authenticate_linked_global_parameter_rows(&program, &mut row_short)
                .expect_err("one-short row authentication must fail")
                .reason(),
            EvidenceValidationReason::ConstraintResourceExhausted,
        );
        assert_eq!(row_short.used(), exact_row_work - 1);

        let retry = linked_registry_row_program();
        let mut row_exact = InterfaceConstraintBudget::with_limit(exact_row_work);
        authenticate_linked_global_parameter_rows(&retry, &mut row_exact)
            .expect("a fresh exact-budget fixture must authenticate its rows");
        assert_eq!(row_exact.used(), exact_row_work);

        let mut authentication_measured = InterfaceConstraintBudget::default();
        authenticate_linked_registry_facts(&retry, &mut authentication_measured)
            .expect("the complete linked registry should authenticate");
        let exact_authentication_work = authentication_measured.used();
        let mut authentication_short =
            InterfaceConstraintBudget::with_limit(exact_authentication_work - 1);
        let mut untouched_type_work = TypeWorkBudget::with_limit(0);
        let rejected = validate_interface_evidence_with_budget(
            linked_registry_row_program(),
            &mut authentication_short,
            &mut untouched_type_work,
        );
        assert_eq!(
            rejected
                .expect_err("one-short registry authentication cannot publish a capability")
                .reason(),
            EvidenceValidationReason::ConstraintResourceExhausted,
        );
        assert_eq!(authentication_short.used(), exact_authentication_work - 1);
        assert_eq!(untouched_type_work.used(), 0);

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

    #[test]
    fn linked_registry_canonical_malformation_precedes_a_later_row_mismatch() {
        let (mut both, base) = linked_higher_kinded_diamond_program();
        let canonical_span = both
            .registry()
            .nominals()
            .first()
            .and_then(|nominal| both.registry().nominal_parameters(nominal.id))
            .and_then(|parameters| parameters.first())
            .map(|parameter| parameter.origin.primary_span())
            .expect("the fixture should retain a canonical nominal parameter");
        let row_span = both
            .groups()
            .iter()
            .flat_map(|group| group.schemes())
            .find(|scheme| !scheme.scheme.type_parameters.is_empty())
            .map(|scheme| scheme.origin.primary_span())
            .expect("the fixture should retain a non-empty checked global scheme");
        assert_ne!(canonical_span, row_span);
        assert!(both.corrupt_linked_carrier_for_test(
            base,
            LinkedCarrierMutationForTest::NominalParameterKind(0),
        ));
        assert!(both.corrupt_linked_global_parameter_rows_for_test(
            LinkedGlobalParameterRowMutationForTest::Owner,
        ));
        let found = validate_interface_evidence(both)
            .expect_err("the earlier canonical failure must preempt row authentication");

        assert_eq!(found.reason(), EvidenceValidationReason::UnknownIdentity);
        assert_eq!(found.primary(), canonical_span);
        assert_ne!(found.primary(), row_span);
    }

    #[test]
    fn linked_registry_indexes_precharge_exactly_before_reserve_and_retry() {
        const WIDTH: usize = 32_768;
        std::thread::Builder::new()
            .name("wide-linked-registry-index-reservation".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("linked-registry-indexes.ash", "index")
                    .expect("the index source should fit");
                let span = source
                    .span(ByteRange::new(0, 5).expect("the index range should be ordered"))
                    .expect("the index span should fit");
                let mut short = InterfaceConstraintBudget::with_limit(2 * WIDTH - 1);
                assert!(
                    reserve_linked_registry_authentication_indexes(WIDTH, WIDTH, &mut short, span,)
                        .is_err()
                );
                assert_eq!(short.used(), 0, "the aggregate index charge is atomic");

                for _ in 0..2 {
                    let mut exact = InterfaceConstraintBudget::with_limit(2 * WIDTH);
                    let (modules, owners) = reserve_linked_registry_authentication_indexes(
                        WIDTH, WIDTH, &mut exact, span,
                    )
                    .expect("the exact module and owner index capacities should fit");
                    assert_eq!(exact.used(), 2 * WIDTH);
                    assert!(modules.is_empty());
                    assert!(owners.is_empty());
                }
            })
            .expect("the wide linked-registry index worker should start")
            .join()
            .expect("wide linked-registry index success and rejection must fit 256 KiB");

        let program = multi_module_all_binder_owner_program();
        assert!(program.groups().len() > 1);
        assert!(program.registry().nominals().iter().any(|nominal| {
            program
                .registry()
                .nominal_parameters(nominal.id)
                .is_some_and(|parameters| !parameters.is_empty())
        }));
        assert!(
            program
                .groups()
                .iter()
                .any(|group| !group.interface_facts().is_empty())
        );
        assert!(program.groups().iter().any(|group| {
            group
                .schemes()
                .iter()
                .any(|scheme| !scheme.scheme.type_parameters.is_empty())
        }));
        assert!(program.groups().iter().any(|group| {
            group
                .implementation_facts()
                .iter()
                .any(|fact| !fact.head_parameters.is_empty())
        }));

        let index_boundary = 1 + program.groups().len() + program.registry().type_variable_count();
        let mut index_short = InterfaceConstraintBudget::with_limit(index_boundary - 1);
        assert!(authenticate_linked_registry_facts(&program, &mut index_short).is_err());
        assert_eq!(
            index_short.used(),
            1,
            "root authentication precedes the atomic index-storage charge",
        );

        let mut measured = InterfaceConstraintBudget::default();
        authenticate_linked_registry_facts(&program, &mut measured)
            .expect("the all-owner linked registry should authenticate");
        let exact_work = measured.used();
        assert!(exact_work > index_boundary);
        let mut one_short = InterfaceConstraintBudget::with_limit(exact_work - 1);
        assert!(authenticate_linked_registry_facts(&program, &mut one_short).is_err());
        for _ in 0..2 {
            let mut exact = InterfaceConstraintBudget::with_limit(exact_work);
            authenticate_linked_registry_facts(&program, &mut exact)
                .expect("the immutable all-owner registry should remain reusable");
            assert_eq!(exact.used(), exact_work);
        }
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
        let group = &program.groups()[0];
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
        builder
            .finish(root, generic.interface, root_argument)
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

    fn repeated_abstract_priority_program() -> ResolvedModuleProgram {
        entry_program(concat!(
            "type Wrap<A> = Wrap(A)\n\n",
            "interface Keep<A> {\nkeep : A -> A\n}\n\n",
            "impl Keep<Wrap<A>> where Keep<A>, Keep<A> {\n",
            "keep (Wrap(value)) = Wrap(keep(value))\n",
            "}\n\n",
            "main : Unit -> Unit\nmain () = ()\n",
        ))
    }

    fn repeated_exact_current_prerequisites_program() -> ResolvedModuleProgram {
        entry_program(concat!(
            "type Wrap<A> = Wrap(A)\n\n",
            "interface Keep<A> {\nkeep : A -> A\n}\n\n",
            "impl Keep<Wrap<A>> where Keep<A>, Keep<A> {\n",
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
            &fact.argument,
            &single_substitution(parameter.id, argument),
            &mut InterfaceConstraintBudget::default(),
            fact.span,
        )
        .expect("the fixture head should instantiate within the default budget")
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
        builder
            .finish(root, interface.id, argument)
            .expect("the abstract root should exist")
    }

    #[test]
    fn validated_interface_capability_has_exact_resolved_program_payload() {
        let ValidatedInterfaceProgram { source } = validate_interface_evidence(local_program())
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
        let group = &program.groups()[0];
        let fact = &group.implementation_facts()[0];
        let selection = implementation_selection(
            fact.id,
            fact.interface,
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
        let wrong_goal = builder
            .finish(root, selection.interface(), Type::Bool)
            .expect("the malformed goal root should exist");
        let registry =
            LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                .expect("the valid linked registry should authenticate");

        let failure = validate_selection(
            &program,
            &registry,
            group,
            &wrong_goal,
            fact.interface,
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
    fn rejects_kind_invalid_selected_goal_and_matching_higher_kinded_substitution() {
        let program = higher_kinded_generic_program();
        let group = &program.groups()[0];
        let [wrapped] = program.registry().nominals() else {
            panic!("the fixture should retain exactly one nominal constructor");
        };
        let [fact] = group.implementation_facts() else {
            panic!("the fixture should retain exactly one generic implementation");
        };
        let malformed_goal =
            Type::apply_arguments(Type::Nominal(wrapped.id), [Type::Int, Type::Int]);
        let substitution = match_implementation_head_structurally(
            fact.head_parameters.iter().map(|parameter| parameter.id),
            &fact.argument,
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
        let selection = builder
            .finish(root, fact.interface, malformed_goal)
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
                fact.interface,
                &mut InterfaceConstraintBudget::default(),
                fact.span,
            )
            .expect_err("a selected goal must satisfy canonical K-Interface-Argument")
            .reason(),
            EvidenceValidationReason::InvalidEvidenceRoot,
        );
    }

    #[test]
    fn rejects_checked_global_parameter_kind_mirror_before_core() {
        let mut program = higher_kinded_generic_program();
        let module = program.groups()[0].module();
        assert!(program.replace_first_checked_global_parameter_kind_for_test(module, Kind::Type,));

        let failure = validate_interface_evidence(program)
            .expect_err("a checked scheme Kind mirror must match the combined registry");

        assert_eq!(failure.reason(), EvidenceValidationReason::UnknownIdentity);
    }

    #[test]
    fn authenticates_one_reusable_higher_kinded_linked_diamond() {
        let (program, _) = linked_higher_kinded_diamond_program();
        validate_interface_evidence(program)
            .expect("the exact public, hidden, opaque, and implementation mirrors must link");
    }

    #[test]
    fn rejects_every_task8_kinded_linked_diamond_carrier_before_core() {
        let mutations = [
            LinkedCarrierMutationForTest::NominalParameterKind(0),
            LinkedCarrierMutationForTest::NominalParameterKind(1),
            LinkedCarrierMutationForTest::ConstructorIdentity,
            LinkedCarrierMutationForTest::ConstructorOrdinal,
            LinkedCarrierMutationForTest::DefiningModule,
            LinkedCarrierMutationForTest::GlobalRegistryKind,
            LinkedCarrierMutationForTest::GlobalSourceParameterIdentity,
            LinkedCarrierMutationForTest::GlobalSourceParameterSpelling,
            LinkedCarrierMutationForTest::GlobalSourceParameterOrigin,
            LinkedCarrierMutationForTest::GlobalSourceNameIdentity,
            LinkedCarrierMutationForTest::GlobalSourceNameSpelling,
            LinkedCarrierMutationForTest::GlobalSourceNameOrigin,
            LinkedCarrierMutationForTest::GlobalSourceKind,
            LinkedCarrierMutationForTest::GlobalCheckedKind,
            LinkedCarrierMutationForTest::GlobalSourceType,
            LinkedCarrierMutationForTest::InterfaceTokenIdentity,
            LinkedCarrierMutationForTest::InterfaceTokenSourceIndex,
            LinkedCarrierMutationForTest::InterfaceSourceParameterIdentity,
            LinkedCarrierMutationForTest::InterfaceSourceParameterSpelling,
            LinkedCarrierMutationForTest::InterfaceSourceMethodIdentity,
            LinkedCarrierMutationForTest::InterfaceSourceMethodSpelling,
            LinkedCarrierMutationForTest::InterfaceSourceMethodSpan,
            LinkedCarrierMutationForTest::InterfaceSourceMethodLocalBinder,
            LinkedCarrierMutationForTest::InterfaceRegistryKind,
            LinkedCarrierMutationForTest::InterfaceFactParameterIdentity,
            LinkedCarrierMutationForTest::InterfaceFactParameterSpelling,
            LinkedCarrierMutationForTest::InterfaceFactParameterKind,
            LinkedCarrierMutationForTest::InterfaceHiddenFactParameterKind,
            LinkedCarrierMutationForTest::InterfaceFactParameterOrigin,
            LinkedCarrierMutationForTest::InterfaceMethodType,
            LinkedCarrierMutationForTest::InterfaceMethodOrigin,
            LinkedCarrierMutationForTest::ImplementationRegistryKind,
            LinkedCarrierMutationForTest::ImplementationSourceParameterIdentity,
            LinkedCarrierMutationForTest::ImplementationSourceParameterSpelling,
            LinkedCarrierMutationForTest::ImplementationSourceParameterOrigin,
            LinkedCarrierMutationForTest::ImplementationSourceKind,
            LinkedCarrierMutationForTest::ImplementationFactKind,
            LinkedCarrierMutationForTest::ImplementationOpaqueFactKind,
            LinkedCarrierMutationForTest::ImplementationTokenIdentity,
            LinkedCarrierMutationForTest::ImplementationTokenInterface,
            LinkedCarrierMutationForTest::ImplementationTokenSourceIndex,
            LinkedCarrierMutationForTest::ImplementationTokenMethod,
            LinkedCarrierMutationForTest::ImplementationPrerequisite,
            LinkedCarrierMutationForTest::ImplementationMethodRequirement,
            LinkedCarrierMutationForTest::ImplementationMethodIdentity,
            LinkedCarrierMutationForTest::ImplementationMethodBinder,
        ];
        for mutation in mutations {
            let (mut program, base) = linked_higher_kinded_diamond_program();
            assert!(
                program.corrupt_linked_carrier_for_test(base, mutation),
                "the linked diamond must retain {mutation:?}",
            );
            assert_eq!(
                validate_interface_evidence(program)
                    .expect_err("every independent linked carrier must authenticate before Core")
                    .reason(),
                EvidenceValidationReason::UnknownIdentity,
                "{mutation:?}",
            );
        }
    }

    #[test]
    fn rejects_implementation_method_parameter_kind_mirror_before_core() {
        let mut program = higher_kinded_generic_program();
        let module = program.groups()[0].module();
        assert!(
            program
                .replace_first_implementation_method_parameter_kind_for_test(module, Kind::Type,)
        );

        let failure = validate_interface_evidence(program)
            .expect_err("an implementation method Kind mirror must match its registry binder");

        assert_eq!(failure.reason(), EvidenceValidationReason::UnknownIdentity);
    }

    #[test]
    fn rejects_every_surviving_linked_nominal_and_constructor_mirror_before_core() {
        enum Mutation {
            NominalParameter,
            Family,
            Payload,
            DefiningOwner,
        }

        for mutation in [
            Mutation::NominalParameter,
            Mutation::Family,
            Mutation::Payload,
            Mutation::DefiningOwner,
        ] {
            let mut program = match mutation {
                Mutation::Family => entry_program(concat!(
                    "type Choice<A> =\n",
                    "First(A)\n",
                    "| Second(A)\n\n",
                    "main : Unit -> Unit\n",
                    "main () = ()\n",
                )),
                _ => higher_kinded_generic_program(),
            };
            let changed = match mutation {
                Mutation::NominalParameter => {
                    program.replace_first_linked_nominal_parameter_kind_for_test(Kind::Type)
                }
                Mutation::Family => program.truncate_first_linked_constructor_family_for_test(),
                Mutation::Payload => {
                    let owner = program.registry().nominals()[0].id;
                    program.replace_first_linked_constructor_payload_for_test(Type::Nominal(owner))
                }
                Mutation::DefiningOwner => {
                    program.detach_first_linked_constructor_from_owner_for_test()
                }
            };
            assert!(
                changed,
                "the selected linked mutation must reach its carrier"
            );

            let failure = validate_interface_evidence(program)
                .expect_err("every surviving linked registry mirror must authenticate");
            assert_eq!(failure.reason(), EvidenceValidationReason::UnknownIdentity);
        }
    }

    #[test]
    fn rejects_unused_inline_and_implementation_registry_binder_mirrors_before_core() {
        let mut inline = entry_program(concat!(
            "fn operational<F : Type -> Type>(value : F<Int>) -> F<Int> {\n",
            "value\n",
            "}\n\n",
            "main : Unit -> Unit\n",
            "main () = ()\n",
        ));
        let module = inline.groups()[0].module();
        assert!(inline.erase_first_inline_global_binder_occurrence_for_test(module));
        assert_eq!(
            validate_interface_evidence(inline)
                .expect_err("an inline checked/source pair cannot retain an unused binder")
                .reason(),
            EvidenceValidationReason::UnknownIdentity,
        );

        let mut implementation = higher_kinded_generic_program();
        assert!(implementation.corrupt_first_linked_implementation_parameter_spelling_for_test());
        assert_eq!(
            validate_interface_evidence(implementation)
                .expect_err("an implementation binder record must match registry metadata")
                .reason(),
            EvidenceValidationReason::UnknownIdentity,
        );
    }

    #[test]
    fn rejects_correlated_interface_method_shape_tampering_before_core() {
        for replacement in [
            None,
            Some(Type::Function(Box::new(Type::Int), Box::new(Type::Int))),
        ] {
            let mut program = entry_program(concat!(
                "interface View<A> {\n",
                "view : A -> A\n",
                "}\n\n",
                "main : Unit -> Unit\n",
                "main () = ()\n",
            ));
            let group = &program.groups()[0];
            let module = group.module();
            let parameter = group.interface_facts()[0].parameter.id;
            let replacement = replacement.unwrap_or(Type::Variable(parameter));
            assert!(
                program.replace_first_interface_method_type_pair_for_test(module, replacement,)
            );

            assert_eq!(
                validate_interface_evidence(program)
                    .expect_err("a linked interface method must retain its exact shape")
                    .reason(),
                EvidenceValidationReason::UnknownIdentity,
            );
        }
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
        let group = &program.groups()[0];
        let [wrapped] = program.registry().nominals() else {
            panic!("the fixture should retain exactly one nominal constructor");
        };
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
            &fact.argument,
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
        let selection = builder
            .finish(root, fact.interface, goal.clone())
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
            let parameter = program
                .registry()
                .type_variable(interface.parameter.id)
                .expect("the interface parameter should be canonical");
            selected_environments
                .insert_interface(
                    interface.id,
                    &parameter.kind,
                    parameter.origin.primary_span(),
                    &mut TypeWorkBudget::default(),
                )
                .expect("the interface environment should fit outside the measured operation");
        }
        let mut type_one_short = TypeWorkBudget::with_limit(LEXICAL_TYPE_WORK - 1);
        assert_eq!(
            validate_checked_selection_in_scope(
                &program,
                &registry,
                group,
                &selection,
                fact.interface,
                &goal,
                EvidenceScope {
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
            &fact.argument,
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
        let group = &program.groups()[0];
        let generic = &group.implementation_facts()[1];
        let owner = generic
            .argument
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
            generic.interface,
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
        // and one for the kind-preserving prerequisite edge: 59 + 9 + 4 + 1.
        const EXACT_WORK: usize = 73;
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

        let group = &program.groups()[0];
        let generic = &group.implementation_facts()[1];
        let owner = generic
            .argument
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
            generic.interface,
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
                generic.interface,
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
            generic.interface,
            &mut exact,
            group.span(),
        )
        .expect("the exact selected-goal work should fit");
        assert_eq!(exact.used(), EXACT_WORK);
    }

    #[test]
    fn rejects_reordered_two_parameter_substitution() {
        let program = two_parameter_program();
        let group = &program.groups()[0];
        let fact = &group.implementation_facts()[0];
        let [first, second] = fact.head_parameters.as_ref() else {
            panic!("the fixture should retain two head parameters");
        };
        let goal = Type::Tuple(vec![Type::Int, Type::Bool].into_boxed_slice());
        let reordered = match_implementation_head_structurally(
            [second.id, first.id].into_iter(),
            &fact.argument,
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
        let selection = builder
            .finish(root, fact.interface, goal)
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
                fact.interface,
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
        let group = &program.groups()[0];
        let left = &group.implementation_facts()[0];
        let right = &group.implementation_facts()[1];
        let generic = &group.implementation_facts()[2];
        let owner = generic
            .argument
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
            let selection = builder
                .finish(
                    root,
                    generic.interface,
                    Type::apply_arguments(Type::Nominal(owner), [Type::Int]),
                )
                .expect("the malformed prerequisite root should exist");

            assert_eq!(
                validate_selection(
                    &program,
                    &registry,
                    group,
                    &selection,
                    generic.interface,
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
        let group = &program.groups()[0];
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
            owner: Some(RequirementOwner::Global(second.binder)),
            variables: &variables,
        };

        let failure = validate_selection_in_scope(
            &program,
            &registry,
            group,
            &selection,
            first.scheme.requirements[0].interface,
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
        let group = &program.groups()[0];
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
            owner: Some(RequirementOwner::Global(first.binder)),
            variables: &variables,
        };

        let failure = validate_selection_in_scope(
            &program,
            &registry,
            group,
            &selection,
            first.scheme.requirements[0].interface,
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
    fn rejects_later_identity_equal_abstract_requirement_selected_out_of_source_order() {
        let program = repeated_abstract_priority_program();
        let group = &program.groups()[0];
        let implementation = &group.implementation_facts()[0];
        let [first, later] = implementation.prerequisites.as_ref() else {
            panic!("the accepted implementation should retain both repeated prerequisites");
        };
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
            Some(EvidenceNode::Abstract { requirement, .. }) if requirement == first.id
        ));

        let interface = &group.interface_facts()[0];
        let forged = abstract_selection(later.id, interface, later.argument.clone());
        let registry =
            LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                .expect("the valid linked registry should authenticate");
        let scope_variables = implementation
            .head_parameters
            .iter()
            .map(|parameter| parameter.id)
            .collect::<Vec<_>>();
        let scope = EvidenceScope {
            owner: Some(RequirementOwner::Impl(implementation.id)),
            variables: &scope_variables,
        };

        assert_eq!(
            validate_selection_in_scope(
                &program,
                &registry,
                group,
                &forged,
                later.interface,
                scope,
                &mut InterfaceConstraintBudget::default(),
                later.span,
            )
            .expect_err("only the first identity-equal abstract requirement is authentic")
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
    fn accepts_exact_current_implementation_with_repeated_identity_equal_prerequisites() {
        validate_interface_evidence(repeated_exact_current_prerequisites_program())
            .expect("exact current evidence should retain every repeated prerequisite by identity");
    }

    #[test]
    fn rejects_freshly_instantiated_current_implementation_at_the_selection_root() {
        let program = current_authenticity_program();
        let group = &program.groups()[0];
        let leaf = &group.implementation_facts()[0];
        let current = &group.implementation_facts()[1];
        let mut builder = EvidenceSelectionBuilder::new();
        let root = forged_fresh_current_node(&mut builder, leaf, current);
        let forged = builder
            .finish(
                root,
                current.interface,
                instantiate_single_parameter_head(current, &Type::Int),
            )
            .expect("the forged direct selection should remain structurally valid");
        let registry =
            LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                .expect("the valid linked registry should authenticate");
        let scope = EvidenceScope {
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
                current.interface,
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
        let group = &program.groups()[0];
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
        let forged = builder
            .finish(
                root,
                enclosing.interface,
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
            owner: Some(RequirementOwner::Impl(current.id)),
            variables: &scope_variables,
        };

        assert_eq!(
            validate_selection_in_scope(
                &program,
                &registry,
                group,
                &forged,
                enclosing.interface,
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
        let group = &program.groups()[0];
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
        let direct = direct_builder
            .finish(
                direct_root,
                requirement.interface,
                requirement.argument.clone(),
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
        let outer_nominal = outer
            .argument
            .outer_nominal()
            .expect("the enclosing implementation should retain a nominal head");
        let nested = nested_builder
            .finish(
                nested_root,
                outer.interface,
                Type::apply_arguments(Type::Nominal(outer_nominal), [requirement.argument.clone()]),
            )
            .expect("the forged nested selection should remain structurally valid");

        let [implementation_requirement] = outer.prerequisites.as_ref() else {
            panic!("the generic implementation should retain one abstract prerequisite");
        };
        let [implementation_parameter] = outer.head_parameters.as_ref() else {
            panic!("the generic implementation should retain one rigid parameter");
        };
        let implementation_scope = EvidenceScope {
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
        let implementation_selection = implementation_builder
            .finish(
                implementation_root,
                implementation_requirement.interface,
                implementation_requirement.argument.clone(),
            )
            .expect("the forged implementation-scope selection should remain structurally valid");

        let direct_result = validate_selection_in_scope(
            &program,
            &registry,
            group,
            &direct,
            requirement.interface,
            scope,
            &mut InterfaceConstraintBudget::default(),
            requirement.span,
        );
        let nested_result = validate_selection_in_scope(
            &program,
            &registry,
            group,
            &nested,
            outer.interface,
            scope,
            &mut InterfaceConstraintBudget::default(),
            requirement.span,
        );
        let implementation_result = validate_selection_in_scope(
            &program,
            &registry,
            group,
            &implementation_selection,
            implementation_requirement.interface,
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
        let group = &program.groups()[0];
        let shadowed = &group.schemes()[0];
        let [requirement] = shadowed.scheme.requirements.as_ref() else {
            panic!("the constrained global should retain one abstract requirement");
        };
        let variables = [shadowed.scheme.type_parameters[0].0];
        let scope = EvidenceScope {
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
                requirement.interface,
                &requirement.argument,
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
                requirement.interface,
                &requirement.argument,
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
                requirement.interface,
                &requirement.argument,
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
        // prerequisite edge.
        const EXACT_WORK: usize = 87 + 15 + 4 + 1;
        let program = current_authenticity_program();
        let group = &program.groups()[0];
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
            .find(|interface| interface.id == requirement.interface)
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
        let selection = builder
            .finish(root, current.interface, current.argument.clone())
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
            owner: Some(RequirementOwner::Impl(current.id)),
            variables: &scope_variables,
        };
        let mut measured = InterfaceConstraintBudget::default();
        validate_selection_in_scope(
            &program,
            &registry,
            group,
            &selection,
            current.interface,
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
                current.interface,
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
            current.interface,
            scope,
            &mut InterfaceConstraintBudget::with_limit(exact),
            current.span,
        )
        .expect("the exact current-authentication budget should fit");
    }

    #[test]
    fn rejects_inference_forall_and_out_of_scope_type_escape_in_selected_goals() {
        let program = local_program();
        let group = &program.groups()[0];
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
            let selection = builder
                .finish(root, fact.interface, argument)
                .expect("the malformed root should remain representable before validation");
            let failure = validate_selection(
                &program,
                &registry,
                group,
                &selection,
                fact.interface,
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
        let group = &program.groups()[0];
        let ground = &group.implementation_facts()[0];
        let generic = &group.implementation_facts()[1];
        let owner = generic
            .argument
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
            let selection = implementation_selection(ground.id, ground.interface, &methods);
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
            let malformed = builder
                .finish(root, selection.interface(), argument)
                .expect("the malformed nominal root should remain representable");
            assert_eq!(
                validate_selection(
                    &program,
                    &registry,
                    group,
                    &malformed,
                    ground.interface,
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
        let group = &program.groups()[0];
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
        let selection = builder
            .finish(root, fact.interface, Type::Int)
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
                fact.interface,
                &mut InterfaceConstraintBudget::default(),
                group.span(),
            )
            .expect_err("every retained evidence node must be reachable exactly once")
            .reason(),
            EvidenceValidationReason::InvalidEvidenceRoot,
        );
    }

    #[test]
    fn rejects_linked_implementation_type_scheme_and_provenance_corruption() {
        let cases = [0, 1, 2];
        for case in cases {
            let mut program = local_program();
            let group = &program.groups()[0];
            let module = group.module();
            let span = group.span();
            let changed = match case {
                0 => program.replace_first_implementation_argument_for_test(
                    module,
                    Type::Inference(InferenceVariableId::new(7)),
                ),
                1 => program.replace_first_implementation_method_type_for_test(
                    module,
                    Type::Function(Box::new(Type::Int), Box::new(Type::Int)),
                ),
                2 => program.replace_first_implementation_method_origin_for_test(
                    module,
                    Origin::Source(span),
                ),
                _ => unreachable!(),
            };
            assert!(changed);

            assert_eq!(
                validate_interface_evidence(program)
                    .expect_err("linked checked facts must agree with source bodies and provenance")
                    .reason(),
                EvidenceValidationReason::UnknownIdentity,
            );
        }
    }

    #[test]
    fn rejects_unknown_selected_impl_identity_before_core() {
        let program = local_program();
        let group = &program.groups()[0];
        let fact = &group.implementation_facts()[0];
        let unknown_implementation = ImplId::new(group.module(), 99);
        let selection = implementation_selection(unknown_implementation, fact.interface, &[]);
        let registry =
            LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                .expect("the valid linked registry should authenticate");

        let failure = validate_selection(
            &program,
            &registry,
            group,
            &selection,
            fact.interface,
            &mut InterfaceConstraintBudget::default(),
            group.span(),
        )
        .expect_err("the unknown implementation identity should fail before Core");

        assert_eq!(failure.reason(), EvidenceValidationReason::UnknownIdentity);
    }

    #[test]
    fn rejects_hidden_implementation_method_binder_reused_by_a_global() {
        let mut program = local_program();
        let group = &program.groups()[0];
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
        let module = program.groups()[0].module();
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
        let group = &program.groups()[0];
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
        let module = program.groups()[0].module();
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
        let module = program.groups()[0].module();
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
        let group = &program.groups()[0];
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
            let selection = builder
                .finish(root, fact.interface, Type::Int)
                .expect("the malformed root should remain representable before validation");

            assert_eq!(
                validate_selection(
                    &program,
                    &registry,
                    group,
                    &selection,
                    fact.interface,
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
        let selection = implementation_selection(fact.id, fact.interface, &methods);
        let registry =
            LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                .expect("the valid linked registry should authenticate");

        let failure = validate_selection(
            &program,
            &registry,
            entry,
            &selection,
            fact.interface,
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
    }

    #[test]
    fn rejects_a_selection_for_a_different_checked_occurrence_argument() {
        let mut program = entry_program(concat!(
            "interface Keep<A> {\nkeep : A -> A\n}\n\n",
            "impl Keep<Int> {\nkeep value = value\n}\n\n",
            "impl Keep<Bool> {\nkeep value = value\n}\n\n",
            "main : Unit -> (Int -> Int)\nmain () = keep\n",
        ));
        let group = &program.groups()[0];
        let module = group.module();
        let bool_implementation = group
            .implementation_facts()
            .iter()
            .find(|implementation| implementation.argument == Type::Bool)
            .expect("the fixture should retain its Bool implementation");
        let methods = bool_implementation
            .methods
            .iter()
            .map(|method| method.id)
            .collect::<Vec<_>>();
        let forged = implementation_selection_for_argument(
            bool_implementation.id,
            bool_implementation.interface,
            &methods,
            Type::Bool,
        );

        assert!(program.replace_direct_equation_body_selection_for_test(module, forged));

        assert_eq!(
            validate_interface_evidence(program)
                .expect_err("evidence must retain the checked occurrence argument")
                .reason(),
            EvidenceValidationReason::InvalidEvidenceRoot,
        );
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
        let [base, _facade, entry] = program.groups() else {
            panic!("the re-export fixture should retain three groups");
        };
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
        let [_base, _inner, facade, _entry] = program.groups() else {
            panic!("the deep re-export fixture should retain four groups");
        };
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
        let [base, facade, entry] = program.groups() else {
            panic!("the dual re-export fixture should retain three groups");
        };
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
        let [_base, _facade, entry] = program.groups() else {
            panic!("the re-export fixture should retain three groups");
        };
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
        let [_base, facade, entry] = program.groups() else {
            panic!("the re-export fixture should retain three groups");
        };
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
        let [_base, _facade, entry] = program.groups() else {
            panic!("the re-export fixture should retain three groups");
        };
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
        let [_base, _facade, entry] = program.groups() else {
            panic!("the re-export fixture should retain three groups");
        };
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
    fn changed_available_identity_is_reported_as_occurrence_unavailability() {
        let mut program = dual_reexport_program();
        let [base, _facade, entry] = program.groups() else {
            panic!("the re-export fixture should retain three groups");
        };
        let entry_module = entry.module();
        let [equal] = entry.available_implementations() else {
            panic!("the entry should retain only its explicitly selected implementation");
        };
        let keep = &base.implementation_facts()[1];
        assert!(program.replace_available_implementation_id_for_test(
            entry_module,
            equal.id(),
            keep.id,
        ));

        assert_eq!(
            validate_interface_evidence(program)
                .expect_err("the validator must not reselect after effective availability changes")
                .reason(),
            EvidenceValidationReason::UnavailableImplementation,
        );
    }

    #[test]
    fn changed_selected_identity_is_reported_as_an_invalid_evidence_root() {
        let mut program = dual_reexport_program();
        let [base, _facade, entry] = program.groups() else {
            panic!("the re-export fixture should retain three groups");
        };
        let entry_module = entry.module();
        let keep = &base.implementation_facts()[1];
        let forged = implementation_selection(
            keep.id,
            keep.interface,
            &keep
                .methods
                .iter()
                .map(|method| method.id)
                .collect::<Vec<_>>(),
        );
        assert!(program.replace_direct_equation_body_selection_for_test(entry_module, forged));

        assert_eq!(
            validate_interface_evidence(program)
                .expect_err("an occurrence cannot change to a different selected interface")
                .reason(),
            EvidenceValidationReason::InvalidEvidenceRoot,
        );
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
            .find(|group| group.module() != graph.entry())
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
    fn rejects_coherently_forged_expanding_generic_prerequisite() {
        let mut program = entry_program(concat!(
            "type Wrap<A> = Wrap(A)\n\n",
            "interface Equal<A> {\nequal : (A, A) -> Bool\n}\n\n",
            "impl Equal<Int> {\nequal (left, right) = left == right\n}\n\n",
            "impl Equal<Wrap<A>> where Equal<A> {\n",
            "equal (Wrap(left), Wrap(right)) = equal((left, right))\n",
            "}\n\n",
            "main : Unit -> Unit\nmain () = ()\n",
        ));
        let generic = &program.groups()[0].implementation_facts()[1];
        let implementation = generic.id;
        assert!(program.replace_implementation_prerequisite_with_head_for_test(implementation, 0,));

        assert_eq!(
            validate_interface_evidence(program)
                .expect_err("a generic prerequisite must remain a strict head subterm")
                .reason(),
            EvidenceValidationReason::UnknownIdentity,
        );
    }

    #[test]
    fn linked_registry_entries_have_an_exact_constraint_limit() {
        // The complete canonical interface-carrier mirror is authenticated by
        // linked-registry ingress before this private registry build begins.
        // The build therefore owns three fewer duplicate comparison cells.
        const PREDECESSOR_RELATION_WORK: usize = 94;
        // The one retained implementation head is additionally authenticated
        // against canonical IOTA: two total-synthesis cells for `Int` and
        // one `Type`/`Type` Kind comparison cell.
        const IMPLEMENTATION_HEAD_KIND_WORK: usize = 3;
        // The retained `(A, A) -> Bool` interface method authenticates its
        // free-variable closure and outer Function shape in the same Kind/type
        // walk that validates the linked value, so it has no standalone
        // constraint traversal. Charging retained provenance and binder
        // mirrors still has a net additional one-cell carrier cost here.
        // Six newly iterative Source-Origin cells displace five cells from the
        // removed standalone checked/source value-type equality walk.
        const FUSED_CARRIER_NET_WORK: usize = 6 - 5;
        let program = local_program();
        let mut measured = InterfaceConstraintBudget::default();
        drop(
            LinkedInterfaceRegistry::build(&program, &mut measured)
                .expect("the linked registry should fit the default budget"),
        );
        let limit = measured.used();
        assert_eq!(
            limit,
            PREDECESSOR_RELATION_WORK + IMPLEMENTATION_HEAD_KIND_WORK + FUSED_CARRIER_NET_WORK,
            "every retained registry relationship, binder record, total-synthesis cell, and Kind pair is charged"
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
        // The graph/link prefix costs seven cells. Combined-registry
        // authentication adds five fixed structural inventory cells and one
        // binder-index cell. The three-cell interface mirror belongs to the
        // consuming linked-evidence boundary.
        assert_eq!(link_used, 7 + 6, "every linked retained entry is charged");
        drop(
            validate_interface_evidence_with_budget(
                linked,
                &mut measured,
                &mut TypeWorkBudget::default(),
            )
            .expect("the linked evidence should validate on the same budget"),
        );
        let total = measured.used();
        assert!(total > link_used);

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
        // The ordinary link prefix is seven cells. The one-interface local
        // registry contributes five fixed module/interface/global/
        // implementation inventory cells and one binder-index cell. The
        // consuming linked-evidence boundary owns the full interface mirror.
        // TypeWork owns only the retained record and its Type Kind plus the
        // canonical-variable staging cell.
        const CONSTRAINT_WORK: usize = 7 + 6;
        const TYPE_WORK: usize = 3;
        let fixture = ValidationFixture::create(concat!(
            "interface Equal<A> {\nequal : (A, A) -> Bool\n}\n\n",
            "impl Equal<Int> {\nequal (left, right) = left == right\n}\n\n",
            "main : Unit -> Bool\nmain () = equal((1, 1))\n",
        ));
        let graph = fixture.graph();

        let mut constraint_short = InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK - 1);
        let mut untouched_type = TypeWorkBudget::with_limit(TYPE_WORK);
        let constraint_failure = link_modules_with_budgets(
            check_graph(&graph),
            graph.entry(),
            &mut constraint_short,
            &mut untouched_type,
        )
        .expect_err("one missing combined-registry owner-index cell must reject linking");
        assert_eq!(
            constraint_failure,
            crate::elaborate::TypeError::Internal(
                crate::elaborate::ElaborationFailure::ConstraintResourceExhausted,
            ),
        );
        assert_eq!(constraint_short.used(), CONSTRAINT_WORK - 1);
        assert_eq!(untouched_type.used(), 0);

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
        assert_eq!(constraint.used(), CONSTRAINT_WORK);
        assert_eq!(type_short.used(), 0);

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
            drop(linked);
        }
    }

    #[test]
    fn evidence_node_validation_has_an_exact_constraint_limit() {
        // The predecessor node proof costs sixteen units; K-Interface-Argument
        // for the selected Int goal adds two synthesis cells and one Kind cell.
        const EXACT_WORK: usize = 16 + 3;
        let program = local_program();
        let group = &program.groups()[0];
        let fact = &group.implementation_facts()[0];
        let methods = fact
            .methods
            .iter()
            .map(|method| method.id)
            .collect::<Vec<_>>();
        let selection = implementation_selection(fact.id, fact.interface, &methods);
        let registry =
            LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                .expect("the valid linked registry should authenticate");
        let mut measured = InterfaceConstraintBudget::default();
        validate_selection(
            &program,
            &registry,
            group,
            &selection,
            fact.interface,
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
                fact.interface,
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
            fact.interface,
            &mut InterfaceConstraintBudget::with_limit(limit),
            group.span(),
        )
        .expect("the exact node-validation budget should fit");
    }

    #[test]
    fn local_availability_authentication_requires_exactly_two_units() {
        let program = local_program();
        let group = &program.groups()[0];
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
        let [route, _selector_route] = entry.direct_dependencies() else {
            panic!("the entry should retain its name and implementation edges");
        };

        assert_eq!(
            has_direct_dependency(
                entry,
                route.target(),
                route.import_span(),
                &mut InterfaceConstraintBudget::with_limit(0),
                entry.span(),
            )
            .expect_err("the first direct-edge visit must charge before inspection")
            .reason(),
            EvidenceValidationReason::ConstraintResourceExhausted,
        );
        assert!(
            has_direct_dependency(
                entry,
                route.target(),
                route.import_span(),
                &mut InterfaceConstraintBudget::with_limit(1),
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
        let definition = &program.groups()[0].definitions()[0];
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
        let definition = &program.groups()[0].definitions()[0];
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
                assert_eq!(
                    substitute_evidence_type(
                        &root,
                        &[],
                        &mut InterfaceConstraintBudget::default(),
                        span,
                    )
                    .expect_err("the final variable has no substitution"),
                    invalid_root(span),
                );
            })
            .expect("the small-stack evidence-validation thread should start")
            .join()
            .expect("late rebuilt-type teardown must stay iterative");
    }
}
