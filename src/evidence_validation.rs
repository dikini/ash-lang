//! Authentication of linked checked interface evidence before Core synthesis.

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
        same_type_with_constraint_budget as same_semantic_type_with_constraint_budget,
    },
    kind::{
        BodyFreeInterfaceMethodSeed, KindEnvironments, KindFailure, canonical_type_variable_kind,
    },
    module::ModuleId,
    resolved::{
        AvailableImplementation, BinderId, CheckedImplementationFact, CheckedInterfaceFact,
        ImplementationAuthorization, PublicImplementationAuthorization, ResolvedBlock,
        ResolvedDeclarationIndex, ResolvedDefinitionKind, ResolvedExpr, ResolvedExprKind,
        ResolvedInterfaceApplication, ResolvedLocalDeclaration, ResolvedModuleGroup,
        ResolvedModuleProgram, ResolvedOccurrence, ResolvedRegistry, ResolvedTermName,
        ResolvedTypeVariable, resolved_determination_positions_match,
    },
    source::{Origin, Span},
    types::{
        ConstructorId, IterativeTypeOwner, Kind, NominalTypeId, Type, TypeVariableId,
        TypeWorkBudget, clone_kind_with_budget, clone_type_with_budget, discard_type_iteratively,
        same_kind_with_charge,
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
        Self::build_with_kinds(
            program,
            &mut kind_environments,
            None,
            budget,
            &mut type_work,
        )
    }

    fn build_with_kinds<'a>(
        program: &'a ResolvedModuleProgram,
        kind_environments: &mut KindEnvironments<'a>,
        mut binder_owners: Option<&mut HashMap<TypeVariableId, LinkedBinderOwner>>,
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
        // Every declaration key is authenticated before any global or
        // implementation relationship reads determinant positions. This pass
        // is independent of dependency and group order because registry
        // indexing for every group has already completed.
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
            validate_group_interface_consistency(
                program,
                group,
                kind_environments,
                budget,
                type_work,
            )?;
        }

        for group_index in 0..program.groups().len() {
            let group = program
                .groups()
                .get(group_index)
                .ok_or_else(|| unknown(program.result().span))?;
            validate_group_remaining_consistency(
                program,
                self,
                group,
                kind_environments,
                budget,
                type_work,
            )?;
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
                if self.interface(program, fact.interface()).is_none() {
                    return Err(unknown(fact.span));
                }
                let mut head_variables = Vec::new();
                charge(budget, fact.head_parameters.len(), fact.span)?;
                head_variables
                    .try_reserve(fact.head_parameters.len())
                    .map_err(|_| resource(fact.span))?;
                head_variables.extend(fact.head_parameters.iter().map(|parameter| parameter.id));
                for argument in fact.arguments() {
                    validate_linked_type_with_policy(
                        argument,
                        program.registry(),
                        &head_variables,
                        budget,
                        fact.span,
                    )?;
                }
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
                }
                let interface = self
                    .interface(program, fact.interface())
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

fn validate_group_interface_consistency<'a>(
    program: &'a ResolvedModuleProgram,
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
        if !resolved_determination_positions_match(
            &source.parameters,
            source.determination.as_ref(),
            &[
                token.determination().map(|key| key.positions()),
                fact.determination().map(|key| key.positions()),
            ],
            |work| budget.charge(work),
        )
        .map_err(|()| resource(source.span))?
        {
            return Err(unknown(source.span));
        }
        if !same_binders_charged(&fact.parameters, &source.parameters, budget, source.span)? {
            return Err(unknown(source.span));
        }
        if !same_origin_charged(&fact.origin, &source.origin, budget, source.span)?
            || fact.span != source.span
            || fact.methods.len() != source.methods.len()
        {
            return Err(unknown(source.span));
        }
        kind_environments
            .insert_interface(fact.id, &fact.parameters, fact.span, type_work)
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
            if method.id != source_method.id
                || method.spelling != source_method.spelling
                || !same_binders_charged(
                    method.authoritative_type_parameters(),
                    &source_method.type_parameters,
                    budget,
                    method.span,
                )?
                || !same_binders_charged(
                    method.authoritative_type_parameters(),
                    method.type_parameters(),
                    budget,
                    method.span,
                )?
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
            for parameter in method.authoritative_type_parameters() {
                let canonical = program
                    .registry()
                    .type_variable(parameter.id)
                    .ok_or_else(|| unknown(method.span))?;
                if !same_binders_charged(
                    std::slice::from_ref(canonical),
                    std::slice::from_ref(parameter),
                    budget,
                    method.span,
                )? {
                    return Err(unknown(method.span));
                }
            }
            if let ([parameter], []) = (
                fact.parameters.as_ref(),
                method.authoritative_type_parameters(),
            ) {
                validate_linked_value_structure(
                    &method.value_type,
                    program.registry(),
                    std::slice::from_ref(&parameter.id),
                    budget,
                    method.span,
                )?;
            } else {
                let variable_count = fact
                    .parameters
                    .len()
                    .checked_add(method.authoritative_type_parameters().len())
                    .ok_or_else(|| resource(method.span))?;
                charge(budget, variable_count, method.span)?;
                let mut variables = Vec::new();
                variables
                    .try_reserve_exact(variable_count)
                    .map_err(|_| resource(method.span))?;
                variables.extend(fact.parameters.iter().map(|parameter| parameter.id));
                variables.extend(
                    method
                        .authoritative_type_parameters()
                        .iter()
                        .map(|parameter| parameter.id),
                );
                validate_linked_value_structure(
                    &method.value_type,
                    program.registry(),
                    &variables,
                    budget,
                    method.span,
                )?;
            }
        }
    }

    Ok(())
}

fn validate_group_remaining_consistency<'a>(
    program: &'a ResolvedModuleProgram,
    registry: &LinkedInterfaceRegistry,
    group: &'a ResolvedModuleGroup,
    kind_environments: &mut KindEnvironments<'a>,
    budget: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
) -> Result<(), EvidenceValidationFailure> {
    let span = group.span();
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
        authenticate_linked_interface_application_kind(
            requirement.application(),
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
        for argument in checked.arguments() {
            validate_linked_type_with_policy(
                argument,
                program.registry(),
                variables,
                budget,
                checked.span,
            )?;
        }
        if checked.id != source.id
            || !same_source_application_charged(
                checked.application(),
                &source.application,
                budget,
                source.application.span,
            )?
            || !same_origin_charged(
                &checked.origin,
                &Origin::Source(source.application.span),
                budget,
                source.application.span,
            )?
            || checked.span != source.application.span
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
        || token.interface() != source.head.interface.id
        || body.id() != source.id
        || fact.id != source.id
        || fact.interface() != source.head.interface.id
        || !same_application_parts_charged(
            token.application(),
            fact.interface(),
            fact.arguments(),
            budget,
            span,
        )?
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
                .interface(program, fact.interface())
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
    validate_linked_interface_application(
        fact.application(),
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
        authenticate_linked_interface_application_kind(
            prerequisite.application(),
            program.registry(),
            &variables,
            None,
            kind_environments,
            budget,
            type_work,
            prerequisite.span,
        )?;
    }
    if !same_source_application_charged(fact.application(), &source.head, budget, span)?
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
        .interface(program, fact.interface())
        .ok_or_else(|| unknown(span))?;
    let head_key = if fact.prerequisites.is_empty() {
        Vec::new()
    } else {
        linked_selection_key_types(interface, fact.arguments(), budget, span)?
    };
    for prerequisite in &fact.prerequisites {
        let complete_prerequisite =
            linked_type_references(prerequisite.arguments(), budget, prerequisite.span)?;
        let prerequisite_interface = registry
            .interface(program, prerequisite.interface())
            .ok_or_else(|| unknown(prerequisite.span))?;
        let prerequisite_key = linked_selection_key_types(
            prerequisite_interface,
            prerequisite.arguments(),
            budget,
            prerequisite.span,
        )?;
        if !crate::interface::implementation_prerequisite_selection_key_terminates(
            &complete_prerequisite,
            &prerequisite_key,
            &head_key,
            budget,
        )
        .map_err(|()| resource(prerequisite.span))?
        {
            return Err(unknown(prerequisite.span));
        }
    }
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
        if method.head_type_parameter_count() != fact.head_parameters.len()
            || !same_parameter_pairs_to_two_record_slices_charged(
                &method.scheme.type_parameters,
                &fact.head_parameters,
                interface_method.authoritative_type_parameters(),
                budget,
                method.span,
            )?
        {
            return Err(unknown(method.span));
        }
        let method_variable_count = variables
            .len()
            .checked_add(interface_method.authoritative_type_parameters().len())
            .ok_or_else(|| resource(method.span))?;
        charge(budget, method_variable_count, method.span)?;
        let mut method_variables = Vec::new();
        method_variables
            .try_reserve_exact(method_variable_count)
            .map_err(|_| resource(method.span))?;
        method_variables.extend_from_slice(&variables);
        method_variables.extend(
            interface_method
                .authoritative_type_parameters()
                .iter()
                .map(|parameter| parameter.id),
        );
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
                .eq(method_variables.iter().copied())
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
            || !same_type_after_interface_substitution(
                &interface_method.value_type,
                &interface.parameters,
                fact.arguments(),
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
            &method_variables,
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
fn same_application_parts_charged(
    application: &InterfaceApplication,
    interface: InterfaceId,
    arguments: &[Type],
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<bool, EvidenceValidationFailure> {
    if application.interface() != interface || application.arguments().len() != arguments.len() {
        return Ok(false);
    }
    for (checked, source) in application.arguments().iter().zip(arguments) {
        if !same_type_charged(checked, source, budget, span)? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn linked_type_references<'a>(
    types: &'a [Type],
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<Vec<&'a Type>, EvidenceValidationFailure> {
    charge(budget, types.len(), span)?;
    let mut references = Vec::new();
    references
        .try_reserve_exact(types.len())
        .map_err(|_| resource(span))?;
    references.extend(types);
    Ok(references)
}

fn linked_selection_key_types<'a>(
    interface: &CheckedInterfaceFact,
    arguments: &'a [Type],
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<Vec<&'a Type>, EvidenceValidationFailure> {
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

fn same_source_application_charged(
    application: &InterfaceApplication,
    source: &ResolvedInterfaceApplication,
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<bool, EvidenceValidationFailure> {
    if application.interface() != source.interface.id
        || application.arguments().len() != source.arguments.len()
    {
        return Ok(false);
    }
    for (checked, source) in application.arguments().iter().zip(&source.arguments) {
        if !same_type_charged(checked, &source.ty, budget, span)? {
            return Ok(false);
        }
    }
    Ok(true)
}

#[allow(clippy::too_many_arguments)]
fn validate_linked_interface_application<'a>(
    application: &InterfaceApplication,
    registry: &'a ResolvedRegistry,
    variables: &[TypeVariableId],
    parameter_records: &'a [ResolvedTypeVariable],
    source_parameter_records: &'a [ResolvedTypeVariable],
    environments: &mut KindEnvironments<'a>,
    constraint_work: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
    span: Span,
) -> Result<(), EvidenceValidationFailure> {
    for argument in application.arguments() {
        validate_linked_type_with_policy(argument, registry, variables, constraint_work, span)?;
    }
    authenticate_linked_interface_application_kind(
        application,
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
fn authenticate_linked_interface_application_kind<'a>(
    application: &InterfaceApplication,
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
            application.interface(),
            application.arguments(),
            span,
            constraint_work,
        )
    } else {
        environments.expect_body_free_interface_argument_with_ledger(
            application.interface(),
            application.arguments(),
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
    allowed_unused: Option<&[TypeVariableId]>,
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
    if let Some(allowed_unused) = allowed_unused {
        environments
            .expect_body_free_paired_global_value_type_with_ledger(
                checked,
                source,
                allowed_unused,
                span,
                constraint_work,
            )
            .map_err(|failure| map_kind_constraint_failure(failure, span))
    } else {
        environments
            .expect_body_free_paired_value_type_with_ledger(checked, source, span, constraint_work)
            .map_err(|failure| map_kind_constraint_failure(failure, span))
    }
}

fn validate_linked_value_schemes<'a>(
    program: &'a ResolvedModuleProgram,
    registry: &LinkedInterfaceRegistry,
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

        // The late body-free method pass owns this fact visit. Registry
        // indexing and consistency already established each immutable method
        // location, so the defensive lookup is fused into the charged method
        // visit below instead of repeating a separate registry traversal.
        for fact_index in 0..group.interface_facts().len() {
            charge(constraint_work, 1, group_span)?;
            let fact = group
                .interface_facts()
                .get(fact_index)
                .ok_or_else(|| unknown(group_span))?;
            let determinant_parameters = fact
                .determination()
                .map(|determination| {
                    charge(constraint_work, determination.positions().len(), fact.span)?;
                    let mut parameters = Vec::new();
                    parameters
                        .try_reserve_exact(determination.positions().len())
                        .map_err(|_| resource(fact.span))?;
                    for &position in determination.positions() {
                        parameters.push(
                            fact.parameters
                                .get(position)
                                .ok_or_else(|| unknown(fact.span))?
                                .id,
                        );
                    }
                    Ok::<_, EvidenceValidationFailure>(parameters)
                })
                .transpose()?;
            let method_seed = determinant_parameters.as_deref().map_or(
                BodyFreeInterfaceMethodSeed::AllInterfaceParameters,
                BodyFreeInterfaceMethodSeed::Determined,
            );
            for method_index in 0..fact.methods.len() {
                charge(constraint_work, 1, fact.span)?;
                let method = fact
                    .methods
                    .get(method_index)
                    .ok_or_else(|| unknown(fact.span))?;
                if registry.method(program, method.id).is_none() {
                    return Err(unknown(method.span));
                }
                let variable_count = fact
                    .parameters
                    .len()
                    .checked_add(method.authoritative_type_parameters().len())
                    .ok_or_else(|| resource(method.span))?;
                charge(constraint_work, variable_count, method.span)?;
                let mut variables = Vec::new();
                variables
                    .try_reserve_exact(variable_count)
                    .map_err(|_| resource(method.span))?;
                variables.extend(fact.parameters.iter().map(|parameter| parameter.id));
                variables.extend(
                    method
                        .authoritative_type_parameters()
                        .iter()
                        .map(|parameter| parameter.id),
                );
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
                        &variables[..fact.parameters.len()],
                        method_seed,
                        &variables[fact.parameters.len()..],
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
            let allowed_unused = authenticated_global_dependent_only_binders(
                program,
                registry,
                &scheme.scheme,
                constraint_work,
                span,
            )?;
            match definition.kind() {
                ResolvedDefinitionKind::Equational(global) => {
                    validate_linked_paired_value_type_with_kind_mirrors(
                        &scheme.scheme.value_type,
                        &global.interface.annotation.ty,
                        program.registry(),
                        &scheme.scheme.type_parameters,
                        &global.interface.type_parameters,
                        allowed_unused.as_deref(),
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
                    if let Some(allowed_unused) = allowed_unused.as_deref() {
                        environments
                            .expect_body_free_exact_global_value_type_with_ledger(
                                &scheme.scheme.value_type,
                                allowed_unused,
                                span,
                                constraint_work,
                            )
                            .map_err(|failure| map_kind_constraint_failure(failure, span))?;
                    } else {
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

fn authenticated_global_dependent_only_binders(
    program: &ResolvedModuleProgram,
    registry: &LinkedInterfaceRegistry,
    scheme: &ConstrainedScheme,
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<Option<Vec<TypeVariableId>>, EvidenceValidationFailure> {
    let mut required = Vec::new();
    let mut dependent = Vec::new();
    let mut has_determination = false;
    for requirement in &scheme.requirements {
        charge(budget, 1, requirement.span)?;
        let interface = registry
            .interface(program, requirement.interface())
            .ok_or_else(|| unknown(requirement.span))?;
        if requirement.arguments().len() != interface.parameters.len() {
            return Err(unknown(requirement.span));
        }
        let Some(determination) = interface.determination() else {
            for argument in requirement.arguments() {
                collect_linked_constraint_variables(argument, &mut required, budget, span)?;
            }
            continue;
        };
        has_determination = true;
        let mut previous = None;
        for &position in determination.positions() {
            charge(budget, 1, requirement.span)?;
            if position >= requirement.arguments().len()
                || previous.is_some_and(|previous| previous >= position)
            {
                return Err(unknown(requirement.span));
            }
            previous = Some(position);
        }
        let mut next_key = determination.positions().iter().copied().peekable();
        for (position, argument) in requirement.arguments().iter().enumerate() {
            charge(budget, 1, requirement.span)?;
            if next_key.peek() == Some(&position) {
                next_key.next();
                collect_linked_constraint_variables(argument, &mut required, budget, span)?;
            } else {
                collect_linked_constraint_variables(argument, &mut dependent, budget, span)?;
            }
        }
        if next_key.next().is_some() {
            return Err(unknown(requirement.span));
        }
    }
    if !has_determination {
        return Ok(None);
    }

    let mut allowed = Vec::new();
    for identity in dependent {
        let mut is_required = false;
        for candidate in &required {
            charge(budget, 1, span)?;
            if *candidate == identity {
                is_required = true;
                break;
            }
        }
        if is_required {
            continue;
        }
        let mut declared = false;
        for (parameter, _) in &scheme.type_parameters {
            charge(budget, 1, span)?;
            if *parameter == identity {
                declared = true;
                break;
            }
        }
        if !declared {
            return Err(unknown(span));
        }
        charge(budget, 1, span)?;
        allowed.try_reserve(1).map_err(|_| resource(span))?;
        allowed.push(identity);
    }
    Ok(Some(allowed))
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
            if effects.is_some_and(|effects| effects.tail().is_some()) {
                return Err(unknown(span));
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
                .flat_map(|effects| effects.known())
                .flat_map(|instance| instance.arguments());
            let children = effect_argument_count
                .checked_add(2)
                .ok_or_else(|| resource(span))?;
            charge(budget, children, span)?;
            pending.try_reserve(children).map_err(|_| resource(span))?;
            pending.extend(effect_arguments.rev());
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
            Type::Int | Type::Bool | Type::Unit | Type::Nominal(_) => {}
            Type::Inference(_) | Type::Forall(_, _) => return Err(unknown(span)),
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

fn same_type_after_interface_substitution(
    source: &Type,
    parameters: &[ResolvedTypeVariable],
    arguments: &[Type],
    actual: &Type,
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<bool, EvidenceValidationFailure> {
    if parameters.len() != arguments.len() {
        return Ok(false);
    }
    let mut pending = Vec::new();
    reserve_type_pairs(&mut pending, 1, budget, span)?;
    pending.push((source, actual));
    while let Some((source, actual)) = pending.pop() {
        charge(budget, 1, span)?;
        if let Type::Variable(candidate) = source {
            let mut replacement = None;
            for (parameter, argument) in parameters.iter().zip(arguments) {
                charge(budget, 1, span)?;
                if *candidate == parameter.id {
                    replacement = Some(argument);
                    break;
                }
            }
            if let Some(replacement) = replacement {
                if !same_type_charged(replacement, actual, budget, span)? {
                    return Ok(false);
                }
                continue;
            }
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
            (Type::EffectfulFunction(_, _), Type::EffectfulFunction(_, _)) => {
                charge(budget, parameters.len(), span)?;
                let mut replacements = HashMap::new();
                replacements
                    .try_reserve(parameters.len())
                    .map_err(|_| resource(span))?;
                let mut retained = TypeBuffer::new();
                for argument in arguments {
                    reserve_rebuilt_type(&mut retained, budget, span)?;
                    let argument =
                        clone_type_with_budget(argument, &mut |cells| charge(budget, cells, span))?;
                    retained.push(argument);
                }
                for (parameter, argument) in parameters.iter().zip(retained.0.drain(..)) {
                    replacements.insert(parameter.id, argument);
                }
                // Preserve method-local variables that this interface substitution
                // does not bind; all effect arguments still participate in equality.
                let expected = crate::types::substitute_type_variables_with(
                    source,
                    &replacements,
                    |cells| charge(budget, cells, span),
                    || resource(span),
                );
                for (_, ty) in replacements {
                    discard_type_iteratively(ty);
                }
                let expected = IterativeTypeOwner::new(expected?);
                if !same_type_charged(&expected, actual, budget, span)? {
                    return Ok(false);
                }
            }
            _ => return Ok(false),
        }
    }
    Ok(true)
}

#[allow(clippy::too_many_arguments)]
fn same_type_after_method_instantiation(
    source: &Type,
    interface_parameters: &[ResolvedTypeVariable],
    interface_arguments: &[Type],
    method_parameters: &[ResolvedTypeVariable],
    method_arguments: &[Type],
    actual: &Type,
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<bool, EvidenceValidationFailure> {
    if interface_parameters.len() != interface_arguments.len()
        || method_parameters.len() != method_arguments.len()
    {
        return Ok(false);
    }
    let mut pending = Vec::new();
    reserve_type_pairs(&mut pending, 1, budget, span)?;
    pending.push((source, actual));
    while let Some((source, actual)) = pending.pop() {
        charge(budget, 1, span)?;
        if let Type::Variable(candidate) = source {
            let mut replacement = None;
            for (parameter, argument) in interface_parameters.iter().zip(interface_arguments) {
                charge(budget, 1, span)?;
                if parameter.id == *candidate {
                    replacement = Some(argument);
                    break;
                }
            }
            if let Some(replacement) = replacement {
                if !same_type_charged(replacement, actual, budget, span)? {
                    return Ok(false);
                }
                continue;
            }
            for (index, parameter) in method_parameters.iter().enumerate() {
                charge(budget, 1, span)?;
                if parameter.id == *candidate {
                    replacement = method_arguments.get(index);
                    break;
                }
            }
            if let Some(replacement) = replacement {
                if !same_type_charged(replacement, actual, budget, span)? {
                    return Ok(false);
                }
                continue;
            }
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
            (Type::EffectfulFunction(_, _), Type::EffectfulFunction(_, _)) => {
                let count = interface_parameters
                    .len()
                    .checked_add(method_parameters.len())
                    .ok_or_else(|| resource(span))?;
                charge(budget, count, span)?;
                let mut substitution = Vec::new();
                substitution
                    .try_reserve(count)
                    .map_err(|_| resource(span))?;
                for (parameter, argument) in interface_parameters
                    .iter()
                    .zip(interface_arguments)
                    .chain(method_parameters.iter().zip(method_arguments))
                {
                    substitution.push(EvidenceSubstitution::new(
                        parameter.id,
                        clone_type_with_budget(argument, &mut |cells| charge(budget, cells, span))?,
                    ));
                }
                let expected = IterativeTypeOwner::new(substitute_evidence_type(
                    source,
                    &substitution,
                    budget,
                    span,
                )?);
                if !same_type_charged(&expected, actual, budget, span)? {
                    return Ok(false);
                }
            }
            _ => return Ok(false),
        }
    }
    Ok(true)
}

/// A checked module program whose retained interface evidence has been authenticated.
#[derive(Debug)]
struct MethodEvidenceAuthentication;

#[derive(Debug)]
pub struct ValidatedInterfaceProgram {
    source: ResolvedModuleProgram,
    method_evidence: Arc<MethodEvidenceCatalog>,
    _method_evidence: MethodEvidenceAuthentication,
}

impl ValidatedInterfaceProgram {
    /// Returns the combined nominal and constructor registry retained for Core lowering.
    #[must_use]
    pub const fn registry(&self) -> &Arc<ResolvedRegistry> {
        self.source.registry()
    }

    pub(crate) const fn method_evidence(&self) -> &Arc<MethodEvidenceCatalog> {
        &self.method_evidence
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
    let mut binder_owners = authenticate_linked_registry_facts(&program, constraint_work)?;
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
        Some(&mut binder_owners),
        constraint_work,
        type_work,
    )?;
    let has_contextual_parameters = binder_owners.len() != program.registry().type_variable_count();
    if !has_contextual_parameters {
        finalize_linked_registry_authentication(&program, &binder_owners, constraint_work)?;
    }
    validate_linked_value_schemes(
        &program,
        &linked_interfaces,
        &mut kind_environments,
        constraint_work,
        type_work,
    )?;
    validate_occurrences(
        &program,
        &linked_interfaces,
        &mut kind_environments,
        constraint_work,
        type_work,
        false,
    )?;
    let method_evidence = build_core_method_evidence_catalog(&program, constraint_work, type_work)?;
    validate_lexical_headers(
        &program,
        &linked_interfaces,
        &method_evidence,
        &mut kind_environments,
        constraint_work,
        type_work,
    )?;
    drop(kind_environments);
    if has_contextual_parameters {
        for owner in method_evidence.lexical_owners() {
            if let Some(acquisition) = owner.acquisition
                && owner.method.declaration() == 0
            {
                charge(constraint_work, 1, acquisition.span)?;
                let canonical = program
                    .registry()
                    .type_variable(acquisition.identity)
                    .ok_or_else(|| unknown(acquisition.span))?;
                binder_owners
                    .try_reserve(1)
                    .map_err(|_| resource(acquisition.span))?;
                if canonical.kind != Kind::Type
                    || acquisition.identity.module() != Some(acquisition.provider.module())
                    || binder_owners
                        .insert(
                            acquisition.identity,
                            LinkedBinderOwner::Resource(acquisition.provider),
                        )
                        .is_some()
                {
                    return Err(unknown(acquisition.span));
                }
            }
            let method = method_evidence
                .method(owner.method)
                .ok_or_else(|| unknown(program.result().span))?;
            if owner.source_parameters.len() != method.parameters.len() {
                return Err(unknown(program.result().span));
            }
            charge(
                constraint_work,
                owner.source_parameters.len(),
                program.result().span,
            )?;
            binder_owners
                .try_reserve(owner.source_parameters.len())
                .map_err(|_| resource(program.result().span))?;
            for (parameter, (_, kind)) in owner.source_parameters.iter().zip(&method.parameters) {
                charge(constraint_work, 1, program.result().span)?;
                let canonical = program
                    .registry()
                    .type_variable(*parameter)
                    .ok_or_else(|| unknown(program.result().span))?;
                if parameter.module() != Some(owner.source.module())
                    || !same_kind_with_charge(&canonical.kind, kind, || constraint_work.charge(1))
                        .map_err(|()| resource(program.result().span))?
                    || binder_owners
                        .insert(
                            *parameter,
                            LinkedBinderOwner::LexicalMethod(owner.source, owner.method),
                        )
                        .is_some()
                {
                    return Err(unknown(program.result().span));
                }
            }
        }
        finalize_linked_registry_authentication(&program, &binder_owners, constraint_work)?;
    }
    charge(constraint_work, 1, program.result().span)?;
    Ok(ValidatedInterfaceProgram {
        source: program,
        method_evidence: Arc::new(method_evidence),
        _method_evidence: MethodEvidenceAuthentication,
    })
}

fn build_core_method_evidence_catalog(
    program: &ResolvedModuleProgram,
    constraint_work: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
) -> Result<MethodEvidenceCatalog, EvidenceValidationFailure> {
    charge(constraint_work, 1, program.result().span)?;
    let mut method_count = 0usize;
    for group in program.groups() {
        for interface in group.interface_facts() {
            charge(
                constraint_work,
                interface.methods.len(),
                program.result().span,
            )?;
            for _ in &interface.methods {
                method_count = method_count
                    .checked_add(1)
                    .ok_or_else(|| resource(program.result().span))?;
            }
        }
    }
    charge(constraint_work, method_count, program.result().span)?;
    let mut methods = Vec::new();
    methods
        .try_reserve(method_count)
        .map_err(|_| resource(program.result().span))?;
    for group in program.groups() {
        for interface in group.interface_facts() {
            charge(
                constraint_work,
                interface.methods.len(),
                program.result().span,
            )?;
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
                interface_parameters
                    .extend(interface.parameters.iter().map(|parameter| parameter.id));
                methods.push(MethodEvidenceMethod {
                    id: method.id,
                    interface_parameters: interface_parameters.into_boxed_slice(),
                    parameters: parameters.into_boxed_slice(),
                    value_type: clone_type_with_budget(method.value_type(), type_work)
                        .map_err(|()| type_resource(method.span))?,
                });
            }
        }
    }
    charge(
        constraint_work,
        methods.len().saturating_sub(1),
        program.result().span,
    )?;
    if methods.len() != method_count {
        return Err(invalid_root(program.result().span));
    }
    // Dependency order need not be identity order across module namespaces.
    // Keep the common already-canonical path, and charge every comparison when
    // canonicalizing a mixed builtin/source catalog before authentication.
    if methods.windows(2).any(|pair| pair[0].id >= pair[1].id) {
        for index in 1..methods.len() {
            let mut cursor = index;
            while cursor > 0 {
                charge(constraint_work, 1, program.result().span)?;
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
            program.result().span,
        )?;
        if methods.windows(2).any(|pair| pair[0].id >= pair[1].id) {
            return Err(invalid_root(program.result().span));
        }
    }
    let mut implementation_owner_count = 0usize;
    for group in program.groups() {
        for implementation in group.implementation_facts() {
            for method in &implementation.methods {
                let search_work = method
                    .scheme
                    .requirements
                    .len()
                    .checked_add(1)
                    .and_then(|passes| passes.checked_mul(methods.len()))
                    .ok_or_else(|| resource(program.result().span))?;
                charge(
                    constraint_work,
                    search_work
                        .checked_add(1)
                        .ok_or_else(|| resource(program.result().span))?,
                    program.result().span,
                )?;
                if methods.iter().any(|canonical| {
                    canonical.id == method.id.method() && method_is_polymorphic(canonical)
                }) || method.scheme.requirements.iter().any(|requirement| {
                    interface_has_polymorphic_method(methods.as_slice(), requirement.interface())
                }) || local_representation_captures_method_parameter(
                    program.registry(),
                    method,
                    constraint_work,
                )? {
                    implementation_owner_count = implementation_owner_count
                        .checked_add(1)
                        .ok_or_else(|| resource(program.result().span))?;
                }
            }
        }
    }
    charge(
        constraint_work,
        implementation_owner_count,
        program.result().span,
    )?;
    let mut implementation_owners = Vec::new();
    implementation_owners
        .try_reserve_exact(implementation_owner_count)
        .map_err(|_| resource(program.result().span))?;
    for group in program.groups() {
        for implementation in group.implementation_facts() {
            for method in &implementation.methods {
                let search_work = method
                    .scheme
                    .requirements
                    .len()
                    .checked_add(1)
                    .and_then(|passes| passes.checked_mul(methods.len()))
                    .ok_or_else(|| resource(program.result().span))?;
                charge(
                    constraint_work,
                    search_work
                        .checked_add(1)
                        .ok_or_else(|| resource(program.result().span))?,
                    program.result().span,
                )?;
                if !(methods.iter().any(|canonical| {
                    canonical.id == method.id.method() && method_is_polymorphic(canonical)
                }) || method.scheme.requirements.iter().any(|requirement| {
                    interface_has_polymorphic_method(methods.as_slice(), requirement.interface())
                }) || local_representation_captures_method_parameter(
                    program.registry(),
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
    }
    for index in 1..implementation_owners.len() {
        let mut cursor = index;
        while cursor > 0 {
            charge(constraint_work, 1, program.result().span)?;
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
        program.result().span,
    )?;
    if implementation_owners.len() != implementation_owner_count
        || implementation_owners
            .windows(2)
            .any(|pair| pair[0].implementation >= pair[1].implementation)
    {
        return Err(invalid_root(program.result().span));
    }
    let mut domains = Vec::new();
    for group in program.groups() {
        for checked in group.schemes() {
            collect_method_evidence_domains(
                &methods,
                &checked.scheme,
                MethodEvidenceOwner::Global(checked.binder),
                &mut domains,
                constraint_work,
                type_work,
                checked.origin.primary_span(),
            )?;
        }
        for implementation in group.implementation_facts() {
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
    }
    let mut lexical_owners = Vec::new();
    let mut occurrences = collect_method_evidence_occurrences(
        program,
        &methods,
        &mut lexical_owners,
        constraint_work,
        type_work,
    )?;
    if !lexical_owners.is_empty() {
        charge(
            constraint_work,
            program.groups().len(),
            program.result().span,
        )?;
        for group in program.groups() {
            charge(
                constraint_work,
                group.implementation_facts().len(),
                program.result().span,
            )?;
            for implementation in group.implementation_facts() {
                charge(
                    constraint_work,
                    implementation.methods.len(),
                    program.result().span,
                )?;
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
    }
    for index in 1..occurrences.len() {
        let mut cursor = index;
        while cursor > 0 {
            charge(constraint_work, 1, program.result().span)?;
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
        program.result().span,
    )?;
    if occurrences
        .windows(2)
        .any(|pair| pair[0].slot == pair[1].slot)
    {
        return Err(invalid_root(program.result().span));
    }
    let (adapters, expectations) = build_method_evidence_expectations(
        program,
        &methods,
        &implementation_owners,
        &lexical_owners,
        &domains,
        &occurrences,
        constraint_work,
        type_work,
        program.result().span,
    )?;
    let concrete_sources = build_method_evidence_concrete_sources(
        program,
        &methods,
        &occurrences,
        &adapters,
        &expectations,
        constraint_work,
        type_work,
        program.result().span,
    )?;
    charge(constraint_work, 1, program.result().span)?;
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

fn checked_implementation_method_count(
    program: &ResolvedModuleProgram,
    constraint_work: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<usize, EvidenceValidationFailure> {
    charge(constraint_work, program.groups().len(), span)?;
    let implementation_count = program
        .groups()
        .iter()
        .map(|group| group.implementation_facts().len())
        .try_fold(0usize, usize::checked_add)
        .ok_or_else(|| resource(span))?;
    charge(constraint_work, implementation_count, span)?;
    program
        .groups()
        .iter()
        .flat_map(ResolvedModuleGroup::implementation_facts)
        .map(|implementation| implementation.methods.len())
        .try_fold(0usize, usize::checked_add)
        .ok_or_else(|| resource(span))
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

fn checked_global_scheme_count(
    program: &ResolvedModuleProgram,
    constraint_work: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<usize, EvidenceValidationFailure> {
    charge(constraint_work, program.groups().len(), span)?;
    program
        .groups()
        .iter()
        .map(|group| group.schemes().len())
        .try_fold(0usize, usize::checked_add)
        .ok_or_else(|| resource(span))
}

fn checked_interface_count(
    program: &ResolvedModuleProgram,
    constraint_work: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<usize, EvidenceValidationFailure> {
    charge(constraint_work, program.groups().len(), span)?;
    program
        .groups()
        .iter()
        .map(|group| group.interface_facts().len())
        .try_fold(0usize, usize::checked_add)
        .ok_or_else(|| resource(span))
}

fn checked_interface_method_search_width(
    program: &ResolvedModuleProgram,
    constraint_work: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<usize, EvidenceValidationFailure> {
    let interface_count = checked_interface_count(program, constraint_work, span)?;
    charge(constraint_work, interface_count, span)?;
    program
        .groups()
        .iter()
        .flat_map(ResolvedModuleGroup::interface_facts)
        .try_fold(interface_count, |count, interface| {
            count.checked_add(interface.methods.len())
        })
        .ok_or_else(|| resource(span))
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
    program: &ResolvedModuleProgram,
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
        let method_count = checked_implementation_method_count(program, constraint_work, span)?;
        charge(constraint_work, method_count, span)?;
        let checked = program
            .groups()
            .iter()
            .flat_map(ResolvedModuleGroup::implementation_facts)
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
                                    program,
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
    reason = "linked evidence rows are derived from independent authenticated inputs"
)]
fn build_method_evidence_expectations(
    program: &ResolvedModuleProgram,
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
    for (owner, row) in implementation_owners.iter().enumerate() {
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
    for (domain, row) in domains.iter().enumerate() {
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
            let Some(EvidenceNode::Implementation {
                substitution,
                prerequisites,
                methods: selected_methods,
                ..
            }) = occurrence.selection.node(identity)
            else {
                continue;
            };
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
                if !methods
                    .iter()
                    .any(|method| method.id == selected.method() && method_is_polymorphic(method))
                {
                    continue;
                }
                let producer_count =
                    checked_implementation_method_count(program, constraint_work, span)?;
                charge(constraint_work, producer_count, span)?;
                let producer = program
                    .groups()
                    .iter()
                    .flat_map(ResolvedModuleGroup::implementation_facts)
                    .flat_map(|implementation| implementation.methods.iter())
                    .find(|method| method.id == *selected)
                    .ok_or_else(|| invalid_root(span))?;
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
                let producer_count =
                    checked_implementation_method_count(program, constraint_work, span)?;
                charge(constraint_work, producer_count, span)?;
                let producer = program
                    .groups()
                    .iter()
                    .flat_map(ResolvedModuleGroup::implementation_facts)
                    .flat_map(|implementation| implementation.methods.iter())
                    .find(|method| method.id == *selected)
                    .ok_or_else(|| invalid_root(span))?;
                if producer.scheme.requirements.len() != prerequisites.len() {
                    return Err(invalid_root(span));
                }
                let adapter_expectation = adapter_expectations
                    .get(&(occurrence.slot, identity, *selected))
                    .copied();
                if adapter_expectation.is_none() {
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
                                .and_then(|count| {
                                    let child_methods = match child {
                                        EvidenceNode::Abstract { methods, .. } | EvidenceNode::Lexical { methods, .. } => methods.len(),
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
                                        program,
                                        occurrence,
                                        requirement,
                                        method,
                                        constraint_work,
                                        span,
                                    )?),
                                    crate::core::dialect::MethodEvidenceProducer::Adapter {
                                        ..
                                    } | crate::core::dialect::MethodEvidenceProducer::Lexical { .. } => None,
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
                            let interface_search_work = checked_interface_method_search_width(
                                program,
                                constraint_work,
                                span,
                            )?;
                            charge(constraint_work, interface_search_work, span)?;
                            let interface = program
                                .groups()
                                .iter()
                                .flat_map(ResolvedModuleGroup::interface_facts)
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
                                    adapter: adapter_expectation
                                        .and_then(|expectation| {
                                            match expectations.get(expectation)?.role {
                                                MethodEvidenceExpectedRole::Adapter { adapter } => {
                                                    Some(adapter)
                                                }
                                                _ => None,
                                            }
                                        })
                                        .ok_or_else(|| invalid_root(span))?,
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
                if let Some(expectation) = adapter_expectation {
                    let MethodEvidenceExpectedRole::Adapter { adapter } = expectations
                        .get(expectation)
                        .ok_or_else(|| invalid_root(span))?
                        .role
                    else {
                        return Err(invalid_root(span));
                    };
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
    program: &ResolvedModuleProgram,
    occurrence: &MethodEvidenceOccurrence,
    requirement: RequirementId,
    method: MethodId,
    constraint_work: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<usize, EvidenceValidationFailure> {
    let owner = occurrence.scope.ok_or_else(|| invalid_root(span))?;
    let candidate_count = match owner {
        MethodEvidenceOwner::Global(_) => {
            checked_global_scheme_count(program, constraint_work, span)?
        }
        MethodEvidenceOwner::Implementation(_) => {
            checked_implementation_method_count(program, constraint_work, span)?
        }
    };
    charge(constraint_work, candidate_count, span)?;
    let scheme = match owner {
        MethodEvidenceOwner::Global(binder) => program
            .groups()
            .iter()
            .flat_map(ResolvedModuleGroup::schemes)
            .find(|scheme| scheme.binder == binder)
            .map(|scheme| &scheme.scheme),
        MethodEvidenceOwner::Implementation(implementation) => program
            .groups()
            .iter()
            .flat_map(ResolvedModuleGroup::implementation_facts)
            .flat_map(|implementation| implementation.methods.iter())
            .find(|candidate| candidate.id == implementation)
            .map(|method| &method.scheme),
    }
    .ok_or_else(|| invalid_root(span))?;
    let requirement_position =
        usize::try_from(requirement.declaration()).map_err(|_| invalid_root(span))?;
    let requirements = scheme
        .requirements
        .get(..=requirement_position)
        .ok_or_else(|| invalid_root(span))?;
    charge(constraint_work, requirements.len(), span)?;
    let interface_count = checked_interface_count(program, constraint_work, span)?;
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
        let interface = program
            .groups()
            .iter()
            .flat_map(ResolvedModuleGroup::interface_facts)
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

fn retain_lexical_owners(
    source: &crate::resolved::ResolvedLexicalEvidence,
    methods: &[MethodEvidenceMethod],
    owners: &mut Vec<crate::core::dialect::MethodEvidenceLexicalOwner>,
    budget: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
) -> Result<(), EvidenceValidationFailure> {
    let checked = source
        .checked
        .get()
        .ok_or_else(|| invalid_root(source.span))?;
    if checked.acquisition != source.acquisition
        || checked.id != source.id
        || checked.application.interface() != source.application.interface.id
        || checked.application.arguments().len() != source.application.arguments.len()
        || checked.methods.len() != source.method_groups.len()
    {
        return Err(invalid_root(source.span));
    }
    for (checked, resolved) in checked
        .application
        .arguments()
        .iter()
        .zip(&source.application.arguments)
    {
        if !same_type_charged(checked, &resolved.ty, budget, source.span)? {
            return Err(invalid_root(source.span));
        }
    }
    charge(
        budget,
        owners.len().saturating_add(source.method_groups.len()),
        source.span,
    )?;
    if owners.iter().any(|owner| owner.source == source.id) {
        return Err(invalid_root(source.span));
    }
    owners
        .try_reserve(source.method_groups.len())
        .map_err(|_| resource(source.span))?;
    for group in &source.method_groups {
        let method = group.method.ok_or_else(|| invalid_root(group.span))?;
        if group.identity.is_some() || method.interface() != source.application.interface.id {
            return Err(invalid_root(group.span));
        }
        charge(budget, group.equations.len(), group.span)?;
        if group.equations.is_empty()
            || group
                .equations
                .iter()
                .any(|equation| equation.name.binder != group.binder.id)
        {
            return Err(invalid_root(group.span));
        }
        let checked_method = checked
            .methods
            .get(method.declaration() as usize)
            .ok_or_else(|| invalid_root(group.span))?;
        charge(budget, methods.len(), group.span)?;
        let canonical = methods
            .iter()
            .find(|row| row.id == method)
            .ok_or_else(|| invalid_root(group.span))?;
        if checked_method.method != method
            || checked_method.binder != group.binder.id
            || checked_method.captures
                != crate::resolved::lexical_method_captures(group, type_work)
                    .map_err(|()| type_resource(group.span))?
        {
            return Err(invalid_root(group.span));
        }
        let mut replacements = HashMap::new();
        let replacement_count = canonical
            .interface_parameters
            .len()
            .checked_add(canonical.parameters.len())
            .ok_or_else(|| resource(group.span))?;
        charge(budget, replacement_count, group.span)?;
        replacements
            .try_reserve(replacement_count)
            .map_err(|_| resource(group.span))?;
        let mut replacement_types = TypeBuffer::new();
        replacement_types
            .try_reserve(checked.application.arguments().len())
            .map_err(|_| resource(group.span))?;
        for argument in checked.application.arguments() {
            replacement_types.push(
                clone_type_with_budget(argument, type_work)
                    .map_err(|()| type_resource(group.span))?,
            );
        }
        if group.contextual_parameters.len() != canonical.parameters.len()
            || checked.application.arguments().len() != canonical.interface_parameters.len()
        {
            return Err(invalid_root(group.span));
        }
        for ((parameter, kind), contextual) in canonical
            .parameters
            .iter()
            .zip(&group.contextual_parameters)
        {
            if !same_kind_with_charge(kind, &contextual.kind, || budget.charge(1))
                .map_err(|()| resource(group.span))?
            {
                return Err(invalid_root(group.span));
            }
            replacements.insert(*parameter, Type::Variable(contextual.id));
        }
        // Keep deep arguments in their iterative owner until every fallible
        // contextual-parameter check and map reservation has succeeded.
        for parameter in canonical.interface_parameters.iter().rev() {
            let argument = replacement_types
                .pop_owned()
                .expect("the checked argument count matches the interface parameter count");
            replacements.insert(*parameter, argument.into_inner());
        }
        let method_type = crate::types::substitute_type_variables_with(
            &canonical.value_type,
            &replacements,
            |cells| charge(budget, cells, group.span),
            || resource(group.span),
        );
        for (_, ty) in replacements {
            discard_type_iteratively(ty);
        }
        let method_type = IterativeTypeOwner::new(method_type?);
        let actual_value_type = match (&checked_method.scheme, canonical.parameters.is_empty()) {
            (Type::Forall(parameters, body), false) => {
                if parameters.len() != group.contextual_parameters.len() {
                    return Err(invalid_root(group.span));
                }
                charge(budget, parameters.len(), group.span)?;
                for ((id, kind), contextual) in parameters.iter().zip(&group.contextual_parameters)
                {
                    if *id != contextual.id
                        || !same_kind_with_charge(kind, &contextual.kind, || budget.charge(1))
                            .map_err(|()| resource(group.span))?
                    {
                        return Err(invalid_root(group.span));
                    }
                }
                body.as_ref()
            }
            (ty, true) => ty,
            _ => return Err(invalid_root(group.span)),
        };
        if !same_type_charged(&method_type, actual_value_type, budget, group.span)? {
            return Err(invalid_root(group.span));
        }
        let application = checked
            .application
            .clone_with_budget(type_work)
            .map_err(|()| type_resource(group.span))?;
        charge(budget, checked_method.captures.len(), group.span)?;
        let mut captures = Vec::new();
        captures
            .try_reserve(checked_method.captures.len())
            .map_err(|_| resource(group.span))?;
        captures.extend_from_slice(&checked_method.captures);
        charge(budget, group.contextual_parameters.len(), group.span)?;
        let mut source_parameters = Vec::new();
        source_parameters
            .try_reserve(group.contextual_parameters.len())
            .map_err(|_| resource(group.span))?;
        source_parameters.extend(
            group
                .contextual_parameters
                .iter()
                .map(|parameter| parameter.id),
        );
        owners.push(crate::core::dialect::MethodEvidenceLexicalOwner {
            acquisition: source.acquisition,
            source_parameters: source_parameters.into_boxed_slice(),
            source: source.id,
            method,
            binder: group.binder.id,
            application,
            captures: captures.into_boxed_slice(),
        });
    }
    Ok(())
}

fn collect_method_evidence_occurrences(
    program: &ResolvedModuleProgram,
    methods: &[MethodEvidenceMethod],
    lexical_owners: &mut Vec<crate::core::dialect::MethodEvidenceLexicalOwner>,
    constraint_work: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
) -> Result<Vec<MethodEvidenceOccurrence>, EvidenceValidationFailure> {
    let mut occurrences = Vec::new();
    for group in program.groups() {
        for (definition, checked) in group.definitions().iter().zip(group.schemes()) {
            let owner = Some(MethodEvidenceOwner::Global(checked.binder));
            match definition.kind() {
                ResolvedDefinitionKind::Equational(global) => {
                    for equation in &global.equations {
                        collect_method_evidence_expression_occurrences(
                            program,
                            owner,
                            &equation.body,
                            methods,
                            &mut occurrences,
                            lexical_owners,
                            constraint_work,
                            type_work,
                        )?;
                    }
                }
                ResolvedDefinitionKind::InlineOperational(global) => {
                    for declaration in &global.body.declarations {
                        match declaration {
                            ResolvedLocalDeclaration::Binding(binding) => {
                                collect_method_evidence_expression_occurrences(
                                    program,
                                    owner,
                                    &binding.initializer,
                                    methods,
                                    &mut occurrences,
                                    lexical_owners,
                                    constraint_work,
                                    type_work,
                                )?;
                            }
                            ResolvedLocalDeclaration::Recursive(group) => {
                                for member in &group.members {
                                    collect_method_evidence_expression_occurrences(
                                        program,
                                        owner,
                                        &member.initializer,
                                        methods,
                                        &mut occurrences,
                                        lexical_owners,
                                        constraint_work,
                                        type_work,
                                    )?;
                                }
                            }
                            ResolvedLocalDeclaration::Evidence(source) => {
                                retain_lexical_owners(
                                    source,
                                    methods,
                                    lexical_owners,
                                    constraint_work,
                                    type_work,
                                )?;
                                for equation in source
                                    .method_groups
                                    .iter()
                                    .flat_map(|group| &group.equations)
                                {
                                    collect_method_evidence_expression_occurrences(
                                        program,
                                        owner,
                                        &equation.body,
                                        methods,
                                        &mut occurrences,
                                        lexical_owners,
                                        constraint_work,
                                        type_work,
                                    )?;
                                }
                            }
                            ResolvedLocalDeclaration::Newtype(_) => {}
                        }
                    }
                    collect_method_evidence_expression_occurrences(
                        program,
                        owner,
                        &global.body.result,
                        methods,
                        &mut occurrences,
                        lexical_owners,
                        constraint_work,
                        type_work,
                    )?;
                }
            }
        }
        for implementation in group.implementations() {
            for method in implementation.method_groups() {
                let owner = Some(MethodEvidenceOwner::Implementation(
                    method.identity.ok_or_else(|| invalid_root(method.span))?,
                ));
                for equation in &method.equations {
                    collect_method_evidence_expression_occurrences(
                        program,
                        owner,
                        &equation.body,
                        methods,
                        &mut occurrences,
                        lexical_owners,
                        constraint_work,
                        type_work,
                    )?;
                }
            }
        }
    }
    collect_method_evidence_expression_occurrences(
        program,
        None,
        program.result(),
        methods,
        &mut occurrences,
        lexical_owners,
        constraint_work,
        type_work,
    )?;
    Ok(occurrences)
}

#[allow(
    clippy::too_many_arguments,
    reason = "occurrence and lexical owner outputs retain independent constraint and type ledgers"
)]
fn collect_method_evidence_expression_occurrences(
    program: &ResolvedModuleProgram,
    scope: Option<MethodEvidenceOwner>,
    root: &ResolvedExpr,
    methods: &[MethodEvidenceMethod],
    occurrences: &mut Vec<MethodEvidenceOccurrence>,
    lexical_owners: &mut Vec<crate::core::dialect::MethodEvidenceLexicalOwner>,
    constraint_work: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
) -> Result<(), EvidenceValidationFailure> {
    let mut pending = Vec::new();
    charge(constraint_work, 1, root.span)?;
    pending.try_reserve(1).map_err(|_| resource(root.span))?;
    pending.push(root);
    while let Some(expression) = pending.pop() {
        charge(constraint_work, 1, expression.span)?;
        match &expression.kind {
            ResolvedExprKind::Occurrence(occurrence) => match occurrence.term {
                ResolvedTermName::Global(binder) => {
                    let mut scheme = None;
                    'groups: for group in program.groups() {
                        for checked in group.schemes() {
                            charge(constraint_work, 1, expression.span)?;
                            if checked.binder == binder {
                                scheme = Some(&checked.scheme);
                                break 'groups;
                            }
                        }
                    }
                    let Some(scheme) = scheme else {
                        if occurrence.evidence.is_empty() {
                            continue;
                        }
                        return Err(invalid_root(expression.span));
                    };
                    for (slot, requirement) in occurrence.evidence.iter().zip(&scheme.requirements)
                    {
                        charge(constraint_work, methods.len(), expression.span)?;
                        if !interface_has_polymorphic_method(methods, requirement.interface())
                            && (lexical_owners.is_empty()
                                || !slot
                                    .selection()
                                    .map(|selection| {
                                        selection_has_lexical(
                                            selection,
                                            constraint_work,
                                            expression.span,
                                        )
                                    })
                                    .transpose()?
                                    .unwrap_or(false))
                        {
                            continue;
                        }
                        let (checked_application, selection) =
                            slot.filled().ok_or_else(|| invalid_root(expression.span))?;
                        push_method_evidence_occurrence(
                            occurrences,
                            program,
                            slot.storage_id(),
                            scope,
                            Some(MethodEvidenceOwner::Global(binder)),
                            Some(requirement.id),
                            None,
                            checked_application,
                            &[],
                            None,
                            selection,
                            constraint_work,
                            type_work,
                            expression.span,
                        )?;
                    }
                }
                ResolvedTermName::Method(method) => {
                    charge(constraint_work, methods.len(), expression.span)?;
                    let [slot] = occurrence.evidence.as_ref() else {
                        return Err(invalid_root(expression.span));
                    };
                    if !methods
                        .iter()
                        .any(|row| row.id == method && method_is_polymorphic(row))
                        && (lexical_owners.is_empty()
                            || !slot
                                .selection()
                                .map(|selection| {
                                    selection_has_lexical(
                                        selection,
                                        constraint_work,
                                        expression.span,
                                    )
                                })
                                .transpose()?
                                .unwrap_or(false))
                    {
                        continue;
                    }
                    let (
                        checked_method,
                        checked_application,
                        method_arguments,
                        checked_value_type,
                        selection,
                    ) = slot
                        .filled_method()
                        .ok_or_else(|| invalid_root(expression.span))?;
                    push_method_evidence_occurrence(
                        occurrences,
                        program,
                        slot.storage_id(),
                        scope,
                        None,
                        None,
                        Some(checked_method),
                        checked_application,
                        method_arguments,
                        Some(checked_value_type),
                        selection,
                        constraint_work,
                        type_work,
                        expression.span,
                    )?;
                }
            },
            ResolvedExprKind::Integer(_)
            | ResolvedExprKind::Boolean(_)
            | ResolvedExprKind::Unit
            | ResolvedExprKind::Constructor(_) => {}
            ResolvedExprKind::Tuple(elements) => {
                charge(constraint_work, elements.len(), expression.span)?;
                pending
                    .try_reserve(elements.len())
                    .map_err(|_| resource(expression.span))?;
                pending.extend(elements.iter().rev());
            }
            ResolvedExprKind::Apply(application) => {
                charge(constraint_work, 2, expression.span)?;
                pending
                    .try_reserve(2)
                    .map_err(|_| resource(expression.span))?;
                pending.push(&application.argument);
                pending.push(&application.function);
            }
            ResolvedExprKind::Add(binary)
            | ResolvedExprKind::Multiply(binary)
            | ResolvedExprKind::Equal(binary) => {
                charge(constraint_work, 2, expression.span)?;
                pending
                    .try_reserve(2)
                    .map_err(|_| resource(expression.span))?;
                pending.push(&binary.right);
                pending.push(&binary.left);
            }
            ResolvedExprKind::Block(block) => {
                charge(constraint_work, 1, expression.span)?;
                pending
                    .try_reserve(1)
                    .map_err(|_| resource(expression.span))?;
                pending.push(&block.result);
                for declaration in block.declarations.iter().rev() {
                    match declaration {
                        ResolvedLocalDeclaration::Evidence(source) => {
                            retain_lexical_owners(
                                source,
                                methods,
                                lexical_owners,
                                constraint_work,
                                type_work,
                            )?;
                            for equation in source
                                .method_groups
                                .iter()
                                .rev()
                                .flat_map(|group| group.equations.iter().rev())
                            {
                                reserve_expressions(
                                    &mut pending,
                                    1,
                                    constraint_work,
                                    equation.span,
                                )?;
                                pending.push(&equation.body);
                            }
                        }
                        ResolvedLocalDeclaration::Binding(binding) => {
                            charge(constraint_work, 1, expression.span)?;
                            pending
                                .try_reserve(1)
                                .map_err(|_| resource(expression.span))?;
                            pending.push(&binding.initializer);
                        }
                        ResolvedLocalDeclaration::Recursive(group) => {
                            charge(constraint_work, group.members.len(), expression.span)?;
                            pending
                                .try_reserve(group.members.len())
                                .map_err(|_| resource(expression.span))?;
                            pending.extend(
                                group.members.iter().rev().map(|member| &member.initializer),
                            );
                        }
                        ResolvedLocalDeclaration::Newtype(_) => {}
                    }
                }
            }
            ResolvedExprKind::Function(function) => {
                charge(constraint_work, 1, expression.span)?;
                pending
                    .try_reserve(1)
                    .map_err(|_| resource(expression.span))?;
                pending.push(&function.body.result);
                for declaration in function.body.declarations.iter().rev() {
                    match declaration {
                        ResolvedLocalDeclaration::Evidence(source) => {
                            retain_lexical_owners(
                                source,
                                methods,
                                lexical_owners,
                                constraint_work,
                                type_work,
                            )?;
                            for equation in source
                                .method_groups
                                .iter()
                                .rev()
                                .flat_map(|group| group.equations.iter().rev())
                            {
                                reserve_expressions(
                                    &mut pending,
                                    1,
                                    constraint_work,
                                    equation.span,
                                )?;
                                pending.push(&equation.body);
                            }
                        }
                        ResolvedLocalDeclaration::Binding(binding) => {
                            charge(constraint_work, 1, expression.span)?;
                            pending
                                .try_reserve(1)
                                .map_err(|_| resource(expression.span))?;
                            pending.push(&binding.initializer);
                        }
                        ResolvedLocalDeclaration::Recursive(group) => {
                            charge(constraint_work, group.members.len(), expression.span)?;
                            pending
                                .try_reserve(group.members.len())
                                .map_err(|_| resource(expression.span))?;
                            pending.extend(
                                group.members.iter().rev().map(|member| &member.initializer),
                            );
                        }
                        ResolvedLocalDeclaration::Newtype(_) => {}
                    }
                }
            }
            ResolvedExprKind::Match(matched) => {
                let child_count = matched
                    .arms
                    .len()
                    .checked_add(1)
                    .ok_or_else(|| resource(expression.span))?;
                charge(constraint_work, child_count, expression.span)?;
                pending
                    .try_reserve(child_count)
                    .map_err(|_| resource(expression.span))?;
                pending.extend(matched.arms.iter().rev().map(|arm| &arm.body));
                pending.push(&matched.scrutinee);
            }
            ResolvedExprKind::Resource(acquisition) => {
                reserve_expressions(&mut pending, 2, constraint_work, expression.span)?;
                pending.push(&acquisition.body);
                pending.push(&acquisition.initializer);
            }
            ResolvedExprKind::Cleanup(cleanup) => {
                reserve_expressions(&mut pending, 2, constraint_work, expression.span)?;
                pending.push(&cleanup.body);
                pending.push(&cleanup.action);
            }
            ResolvedExprKind::Perform(request) => pending.push(&request.operand),
            ResolvedExprKind::Handle(handler) => {
                let child_count = handler.clauses.len().saturating_add(1);
                charge(constraint_work, child_count, expression.span)?;
                pending
                    .try_reserve(child_count)
                    .map_err(|_| resource(expression.span))?;
                pending.extend(handler.clauses.iter().rev().map(|clause| &clause.body));
                pending.push(&handler.body);
            }
            ResolvedExprKind::Resume(resume) => pending.push(&resume.value),
            ResolvedExprKind::Discard(_) => {}
        }
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn push_method_evidence_occurrence(
    occurrences: &mut Vec<MethodEvidenceOccurrence>,
    program: &ResolvedModuleProgram,
    slot: usize,
    scope: Option<MethodEvidenceOwner>,
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
    let scope_binder = match scope {
        Some(MethodEvidenceOwner::Global(binder)) => Some(binder),
        Some(MethodEvidenceOwner::Implementation(implementation)) => {
            let candidate_count =
                checked_implementation_method_count(program, constraint_work, span)?;
            charge(constraint_work, candidate_count, span)?;
            Some(
                program
                    .groups()
                    .iter()
                    .flat_map(ResolvedModuleGroup::implementation_facts)
                    .flat_map(|implementation| implementation.methods.iter())
                    .find(|candidate| candidate.id == implementation)
                    .ok_or_else(|| invalid_root(span))?
                    .binder,
            )
        }
        None => None,
    };
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
            collect_linked_constraint_variables(argument, &mut variables, budget, method.span)?;
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
    Resource(crate::interface::LexicalEvidenceId),
    LexicalMethod(crate::interface::LexicalEvidenceId, MethodId),
    Nominal(NominalTypeId),
    Effect(crate::types::EffectId),
    Interface(InterfaceId),
    Method(MethodId),
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
) -> Result<HashMap<TypeVariableId, LinkedBinderOwner>, EvidenceValidationFailure> {
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
        if let Some(api) = crate::resolved::ResourceApi::for_module(group.module()) {
            charge(
                budget,
                api.nominal_count() + api.constructor_count() + 2 * api.method_names().len(),
                group.span(),
            )?;
            if !api.registry(registry)
                || !matches!(group.interface_facts(), [interface] if api.interface(interface))
            {
                return Err(unknown(group.span()));
            }
        }
        if !modules.insert(group.module()) {
            return Err(unknown(group.span()));
        }
    }
    let mut constructor_count = 0_usize;

    for nominal in registry
        .nominals()
        .iter()
        .chain(registry.lexical_nominals())
    {
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
    if constructor_count != registry.constructors().len() + registry.lexical_constructors().len() {
        return Err(unknown(span));
    }

    for effect in registry.effects() {
        charge(budget, 1, effect.span)?;
        if !modules.contains(&effect.id.module())
            || registry.effect(effect.id) != Some(effect)
            || effect.operations.is_empty()
        {
            return Err(unknown(effect.span));
        }
        for parameter in &effect.parameters {
            charge(budget, 1, parameter.origin.primary_span())?;
            let canonical = registry
                .type_variable(parameter.id)
                .ok_or_else(|| unknown(parameter.origin.primary_span()))?;
            if !same_binders_charged(
                std::slice::from_ref(canonical),
                std::slice::from_ref(parameter),
                budget,
                parameter.origin.primary_span(),
            )? || owners
                .insert(parameter.id, LinkedBinderOwner::Effect(effect.id))
                .is_some()
            {
                return Err(unknown(parameter.origin.primary_span()));
            }
        }
        for (ordinal, operation) in effect.operations.iter().enumerate() {
            charge(budget, 1, operation.span)?;
            if operation.id.owner() != effect.id
                || usize::try_from(operation.id.operation()) != Ok(ordinal)
            {
                return Err(unknown(operation.span));
            }
        }
    }

    for group in program.groups() {
        for interface in group.interface_facts() {
            charge(budget, 1, interface.span)?;
            let owner = LinkedBinderOwner::Interface(interface.id);
            for parameter in &interface.parameters {
                charge(budget, 1, interface.span)?;
                let canonical = registry
                    .type_variable(parameter.id)
                    .ok_or_else(|| unknown(interface.span))?;
                if !same_binders_charged(
                    std::slice::from_ref(canonical),
                    std::slice::from_ref(parameter),
                    budget,
                    interface.span,
                )? || owners.insert(parameter.id, owner).is_some()
                {
                    return Err(unknown(interface.span));
                }
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
    Ok(owners)
}

fn finalize_linked_registry_authentication(
    program: &ResolvedModuleProgram,
    owners: &HashMap<TypeVariableId, LinkedBinderOwner>,
    budget: &mut InterfaceConstraintBudget,
) -> Result<(), EvidenceValidationFailure> {
    let span = program.result().span;
    charge(budget, 1, span)?;
    if owners.len() != program.registry().type_variable_count() {
        return Err(unknown(span));
    }
    authenticate_linked_global_parameter_rows(program, budget)
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
    if rows.len() != registry.global_parameter_position_count() {
        return Err(unknown(program.result().span));
    }
    Ok(())
}

fn validate_lexical_headers<'a>(
    program: &'a ResolvedModuleProgram,
    registry: &LinkedInterfaceRegistry,
    catalog: &MethodEvidenceCatalog,
    kind_environments: &mut KindEnvironments<'a>,
    budget: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
) -> Result<(), EvidenceValidationFailure> {
    if catalog.lexical_owners().is_empty() {
        return Ok(());
    }
    validate_occurrences(
        program,
        registry,
        kind_environments,
        budget,
        type_work,
        true,
    )
}

fn validate_occurrences<'a>(
    program: &'a ResolvedModuleProgram,
    registry: &LinkedInterfaceRegistry,
    kind_environments: &mut KindEnvironments<'a>,
    budget: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
    headers_only: bool,
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
                        headers_only,
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
                        headers_only,
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
                ResolvedDeclarationIndex::Effect(_) => {}
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
        headers_only,
    )
}

#[allow(clippy::too_many_arguments)]
fn validate_definition<'a>(
    program: &'a ResolvedModuleProgram,
    registry: &LinkedInterfaceRegistry,
    group: &ResolvedModuleGroup,
    definition: &crate::resolved::CheckedDefinition,
    kind_environments: &mut KindEnvironments<'a>,
    budget: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
    headers_only: bool,
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
        lexical_sources: &[],
        lexical_head: None,
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
                    headers_only,
                )?;
            }
        }
        ResolvedDefinitionKind::InlineOperational(global) => {
            let mut pending = Vec::new();
            validate_pending_expressions(
                program,
                registry,
                group,
                scope,
                &mut pending,
                Some(&global.body),
                kind_environments,
                budget,
                type_work,
                headers_only,
            )?;
        }
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn validate_implementation<'a>(
    program: &'a ResolvedModuleProgram,
    registry: &LinkedInterfaceRegistry,
    group: &ResolvedModuleGroup,
    implementation: &crate::resolved::CheckedImplementationBody,
    kind_environments: &mut KindEnvironments<'a>,
    budget: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
    headers_only: bool,
) -> Result<(), EvidenceValidationFailure> {
    let fact = registry
        .implementation(program, implementation.id())
        .ok_or_else(|| unknown(implementation.span()))?;
    for method_index in 0..implementation.method_groups().len() {
        charge(budget, 1, implementation.span())?;
        let method = implementation
            .method_groups()
            .get(method_index)
            .ok_or_else(|| unknown(implementation.span()))?;
        let checked_method = fact
            .methods
            .get(method_index)
            .ok_or_else(|| unknown(method.span))?;
        charge(
            budget,
            checked_method.scheme.type_parameters.len(),
            method.span,
        )?;
        let mut method_parameters = Vec::new();
        method_parameters
            .try_reserve_exact(checked_method.scheme.type_parameters.len())
            .map_err(|_| resource(method.span))?;
        method_parameters.extend(
            checked_method
                .scheme
                .type_parameters
                .iter()
                .map(|(identity, _)| *identity),
        );
        let scope = EvidenceScope {
            lexical_sources: &[],
            lexical_head: None,
            owner: Some(RequirementOwner::Impl(implementation.id())),
            variables: &method_parameters,
        };
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
                headers_only,
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
    if let Some(block) = initial_block {
        schedule_lexical_block(
            pending,
            &mut heads,
            &mut sources,
            &mut method_scopes,
            (None, None),
            block,
            budget,
            headers_only.then_some((program, registry, scope.variables, type_work)),
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
                if let LinkedLocalScope::Resource(resource_scope) = local {
                    charge(budget, 1, expression.span)?;
                    variables
                        .try_reserve(1)
                        .map_err(|_| resource(expression.span))?;
                    variables.push(resource_scope.identity.id);
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
            ResolvedExprKind::Block(block) => {
                schedule_lexical_block(
                    pending,
                    &mut heads,
                    &mut sources,
                    &mut method_scopes,
                    head,
                    block,
                    budget,
                    headers_only.then_some((program, registry, active_variables, type_work)),
                )?;
            }
            ResolvedExprKind::Function(function) => {
                schedule_lexical_block(
                    pending,
                    &mut heads,
                    &mut sources,
                    &mut method_scopes,
                    head,
                    &function.body,
                    budget,
                    headers_only.then_some((program, registry, active_variables, type_work)),
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
                if !acquisition.acquisition.owns(acquisition)
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
            ResolvedExprKind::Cleanup(cleanup) => {
                reserve_expressions(pending, 2, budget, expression.span)?;
                resize_lexical_heads(&mut heads, pending.len(), head, budget, expression.span)?;
                pending.push(&cleanup.body);
                pending.push(&cleanup.action);
            }
            ResolvedExprKind::Perform(request) => pending.push(request.operand.as_ref()),
            ResolvedExprKind::Handle(handler) => {
                let additional = handler.clauses.len().saturating_add(1);
                reserve_expressions(pending, additional, budget, expression.span)?;
                pending.extend(handler.clauses.iter().rev().map(|clause| &clause.body));
                pending.push(handler.body.as_ref());
            }
            ResolvedExprKind::Resume(resume) => pending.push(resume.value.as_ref()),
            ResolvedExprKind::Discard(_) => {}
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
    owner: Option<RequirementOwner>,
    variables: &'a [TypeVariableId],
    lexical_sources: &'a [(&'a crate::resolved::ResolvedLexicalEvidence, Option<usize>)],
    lexical_head: Option<usize>,
}

impl EvidenceScope<'static> {
    const NONE: Self = Self {
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
    let expected_application = InterfaceApplication::new(
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
        validate_type_with_application_policy(
            argument,
            program.registry(),
            scope.variables,
            budget,
            span,
        )?;
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
        if !same_type_charged(selected, expected, budget, span)? {
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
                if candidate.id == source {
                    found = Some(*candidate);
                    break;
                }
                head = *parent;
            }
            let source = found.ok_or_else(|| invalid_root(span))?;
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
            for (actual, expected) in source
                .application
                .arguments
                .iter()
                .zip(expected_application.arguments())
            {
                if !same_type_charged(&actual.ty, expected, budget, span)? {
                    return Err(invalid_root(span));
                }
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
                Some(RequirementOwner::Global(_)) | None => None,
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
                && identity_equal_lexical_source(scope, expected_application, budget, span)?
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
    scope: EvidenceScope<'_>,
    application: &InterfaceApplication,
    budget: &mut InterfaceConstraintBudget,
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
        if same_source_application_charged(application, &source.application, budget, span)?
            && found.replace(source.id).is_some()
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
        validate_type_with_application_policy(argument, registry, scope_variables, budget, span)?;
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
        validate_type_with_application_policy(argument, registry, &head_variables, budget, span)?;
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

    if fact.arguments().len() != goal.arguments().len() {
        return Ok(false);
    }
    let mut pending = Vec::new();
    reserve_type_pairs(&mut pending, fact.arguments().len(), budget, span)?;
    pending.extend(fact.arguments().iter().zip(goal.arguments()).rev());
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
        match (candidate.function_view(), goal.function_view()) {
            (Some(candidate_function), Some(goal_function)) => {
                let effect_argument_count =
                    match (candidate_function.effects(), goal_function.effects()) {
                        (None, None) => 0,
                        (Some(candidate_effects), Some(goal_effects))
                            if candidate_effects.tail().is_none()
                                && goal_effects.tail().is_none()
                                && candidate_effects.known().len()
                                    == goal_effects.known().len() =>
                        {
                            let mut arguments = 0usize;
                            for (candidate_instance, goal_instance) in
                                candidate_effects.known().iter().zip(goal_effects.known())
                            {
                                charge(budget, 1, span)?;
                                if candidate_instance.effect() != goal_instance.effect()
                                    || candidate_instance.arguments().len()
                                        != goal_instance.arguments().len()
                                {
                                    return Ok(false);
                                }
                                arguments = arguments
                                    .checked_add(candidate_instance.arguments().len())
                                    .ok_or_else(|| resource(span))?;
                            }
                            arguments
                        }
                        _ => return Ok(false),
                    };
                reserve_type_pairs(
                    &mut pending,
                    effect_argument_count.saturating_add(2),
                    budget,
                    span,
                )?;
                if let (Some(candidate_effects), Some(goal_effects)) =
                    (candidate_function.effects(), goal_function.effects())
                {
                    for (candidate_instance, goal_instance) in candidate_effects
                        .known()
                        .iter()
                        .zip(goal_effects.known())
                        .rev()
                    {
                        pending.extend(
                            candidate_instance
                                .arguments()
                                .iter()
                                .zip(goal_instance.arguments())
                                .rev(),
                        );
                    }
                }
                pending.push((candidate_function.value(), goal_function.value()));
                pending.push((candidate_function.domain(), goal_function.domain()));
                continue;
            }
            (Some(_), None) | (None, Some(_)) => return Ok(false),
            (None, None) => {}
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
            (Type::Function(_, _), Type::Function(_, _))
            | (Type::EffectfulFunction(_, _), Type::EffectfulFunction(_, _)) => unreachable!(),
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
                if let Some(function) = ty.function_view() {
                    let effects = function.effects();
                    if effects.is_some_and(|effects| effects.tail().is_some()) {
                        return Err(invalid_root(span));
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
                        .flat_map(|effects| effects.known())
                        .flat_map(|instance| instance.arguments());
                    let children = effect_argument_count
                        .checked_add(2)
                        .ok_or_else(|| resource(span))?;
                    charge(budget, children, span)?;
                    pending.try_reserve(children).map_err(|_| resource(span))?;
                    pending.extend(effect_arguments.rev().map(Task::Visit));
                    pending.push(Task::Visit(function.value()));
                    pending.push(Task::Visit(function.domain()));
                    continue;
                }
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

fn same_parameter_pairs_to_two_record_slices_charged(
    pairs: &[(TypeVariableId, Kind)],
    first: &[ResolvedTypeVariable],
    second: &[ResolvedTypeVariable],
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<bool, EvidenceValidationFailure> {
    let expected = first
        .len()
        .checked_add(second.len())
        .ok_or_else(|| resource(span))?;
    if pairs.len() != expected {
        return Ok(false);
    }
    for ((identity, kind), record) in pairs.iter().zip(first.iter().chain(second)) {
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
    struct RowShape {
        known: Box<[(crate::types::EffectId, usize)]>,
        argument_count: usize,
    }

    enum Task<'a> {
        Visit(&'a Type, bool),
        Sequence(std::slice::Iter<'a, Type>, bool),
        FinishTuple(usize),
        FinishApplication,
        FinishFunction,
        FinishEffectfulFunction(RowShape),
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
            Task::Visit(ty, substitute) if ty.function_view().is_some() => {
                let function = ty
                    .function_view()
                    .expect("the guarded evidence type has a semantic function view");
                let Some(effects) = function.effects() else {
                    charge(budget, 3, span)?;
                    work.try_reserve(3).map_err(|_| resource(span))?;
                    work.push(Task::FinishFunction);
                    work.push(Task::Visit(function.value(), substitute));
                    work.push(Task::Visit(function.domain(), substitute));
                    continue;
                };
                if effects.tail().is_some() {
                    return Err(invalid_root(span));
                }
                let mut known = Vec::new();
                let mut argument_count = 0usize;
                for instance in effects.known() {
                    charge(budget, 1, span)?;
                    argument_count = argument_count
                        .checked_add(instance.arguments().len())
                        .ok_or_else(|| resource(span))?;
                    known.try_reserve(1).map_err(|_| resource(span))?;
                    known.push((instance.effect(), instance.arguments().len()));
                }
                let known = known.into_boxed_slice();
                let tasks = argument_count
                    .checked_add(3)
                    .ok_or_else(|| resource(span))?;
                charge(budget, tasks, span)?;
                work.try_reserve(tasks).map_err(|_| resource(span))?;
                work.push(Task::FinishEffectfulFunction(RowShape {
                    known,
                    argument_count,
                }));
                for argument in effects
                    .known()
                    .iter()
                    .flat_map(|instance| instance.arguments())
                    .rev()
                {
                    work.push(Task::Visit(argument, substitute));
                }
                work.push(Task::Visit(function.value(), substitute));
                work.push(Task::Visit(function.domain(), substitute));
            }
            Task::Visit(Type::Function(_, _) | Type::EffectfulFunction(_, _), _) => {
                unreachable!("function variants have a semantic function view")
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
            Task::FinishEffectfulFunction(shape) => {
                if rebuilt.len() < shape.argument_count.saturating_add(2) {
                    return Err(invalid_root(span));
                }
                reserve_rebuilt_type(&mut rebuilt, budget, span)?;
                charge(budget, shape.argument_count, span)?;
                let mut arguments = TypeBuffer::new();
                arguments
                    .try_reserve(shape.argument_count)
                    .map_err(|_| resource(span))?;
                for _ in 0..shape.argument_count {
                    let argument = rebuilt.pop_owned().ok_or_else(|| invalid_root(span))?;
                    arguments.push(argument.into_inner());
                }
                let mut known = Vec::new();
                charge(budget, shape.known.len(), span)?;
                known
                    .try_reserve(shape.known.len())
                    .map_err(|_| resource(span))?;
                for (effect, count) in shape.known {
                    charge(budget, count, span)?;
                    let mut instance_arguments = TypeBuffer::new();
                    instance_arguments
                        .try_reserve(count)
                        .map_err(|_| resource(span))?;
                    for _ in 0..count {
                        let argument = arguments.pop_owned().ok_or_else(|| invalid_root(span))?;
                        instance_arguments.push(argument.into_inner());
                    }
                    known.push(crate::types::EffectInstance::new(
                        effect,
                        instance_arguments.into_boxed_slice(),
                    ));
                }
                if arguments.len() != 0 {
                    return Err(invalid_root(span));
                }
                let codomain = rebuilt.pop_owned().ok_or_else(|| invalid_root(span))?;
                let domain = rebuilt.pop_owned().ok_or_else(|| invalid_root(span))?;
                rebuilt.push(Type::function_computation(
                    domain.into_inner(),
                    crate::types::ComputationType::new(
                        codomain.into_inner(),
                        crate::types::EffectRow::closed(known.into_boxed_slice()),
                    ),
                ));
            }
        }
    }
    if rebuilt.len() != 1 {
        return Err(invalid_root(span));
    }
    Ok(rebuilt.into_one().expect("one reconstructed evidence type"))
}

fn substitute_evidence_application(
    application: &InterfaceApplication,
    substitution: &[EvidenceSubstitution],
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<InterfaceApplication, EvidenceValidationFailure> {
    charge(budget, application.arguments().len(), span)?;
    let mut arguments = TypeBuffer::new();
    arguments
        .try_reserve(application.arguments().len())
        .map_err(|_| resource(span))?;
    for argument in application.arguments() {
        arguments.push(substitute_evidence_type(
            argument,
            substitution,
            budget,
            span,
        )?);
    }
    Ok(InterfaceApplication::new(
        application.interface(),
        arguments.into_boxed_slice(),
    ))
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
    for argument in requirement.arguments() {
        validate_linked_type_with_policy(
            argument,
            program.registry(),
            variables,
            budget,
            requirement.span,
        )?;
    }
    if requirement.id.owner() != owner
        || usize::try_from(requirement.id.declaration()) != Ok(ordinal)
        || registry
            .interface(program, requirement.interface())
            .is_none()
    {
        return Err(unknown(requirement.span));
    }
    Ok(())
}

enum LinkedLocalScope<'a> {
    Method(&'a crate::resolved::ResolvedImplementationMethodGroup),
    Nominal(NominalTypeId),
    Resource(&'a crate::resolved::ResolvedResourceExpr),
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
        if checked.acquisition != Some(acquisition) || !acquisition.supplies(source) {
            return Err(invalid_root(source.span));
        }
        let mut head = local_head;
        while let Some(index) = head {
            charge(budget, 1, source.span)?;
            let (entry, parent) = locals.get(index).ok_or_else(|| invalid_root(source.span))?;
            if let LinkedLocalScope::Resource(resource_scope) = entry {
                has_local_key = acquisition.owns(resource_scope);
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
        validate_type_with_application_policy(
            argument,
            program.registry(),
            scope.variables,
            budget,
            source.span,
        )?;
        nominals.clear();
        crate::resolved::collect_nominal_identities(argument, &mut nominals, type_work)
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
        let earlier = earlier
            .checked
            .get()
            .ok_or_else(|| invalid_root(source.span))?;
        if earlier.application.interface() == interface.id {
            let earlier_keys = linked_selection_key_types(
                interface,
                earlier.application.arguments(),
                budget,
                source.span,
            )?;
            let mut equal = true;
            for (key, earlier) in keys.iter().zip(earlier_keys) {
                if !same_type_charged(key, earlier, budget, source.span)? {
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
    sources: &mut Vec<(&'a crate::resolved::ResolvedLexicalEvidence, Option<usize>)>,
    method_scopes: &mut Vec<(LinkedLocalScope<'a>, Option<usize>)>,
    mut head: (Option<usize>, Option<usize>),
    block: &'a ResolvedBlock,
    budget: &mut InterfaceConstraintBudget,
    mut header_scope: Option<(
        &ResolvedModuleProgram,
        &LinkedInterfaceRegistry,
        &[TypeVariableId],
        &mut TypeWorkBudget,
    )>,
) -> Result<(), EvidenceValidationFailure> {
    let start = pending.len();
    let (additional, has_lexical_scope) =
        block_schedule_shape(block, header_scope.is_some(), budget)?;
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
                if let Some((program, registry, variables, type_work)) = header_scope.as_mut() {
                    authenticate_lexical_header(
                        program,
                        registry,
                        source,
                        EvidenceScope {
                            lexical_sources: sources,
                            lexical_head: head.0,
                            variables,
                            owner: None,
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
                        reserve_expressions(pending, 1, budget, equation.span)?;
                        resize_lexical_heads(
                            heads,
                            pending.len() + 1,
                            method_head,
                            budget,
                            equation.span,
                        )?;
                        pending.push(&equation.body);
                    }
                }
                let next = sources.len();
                sources.push((source, head.0));
                head.0 = Some(next);
            }
            ResolvedLocalDeclaration::Binding(binding) => {
                reserve_expressions(pending, 1, budget, binding.span)?;
                resize_lexical_heads(heads, pending.len() + 1, head, budget, binding.span)?;
                pending.push(&binding.initializer);
            }
            ResolvedLocalDeclaration::Recursive(group) => {
                reserve_expressions(pending, group.members.len(), budget, group.span)?;
                resize_lexical_heads(
                    heads,
                    pending.len() + group.members.len(),
                    head,
                    budget,
                    group.span,
                )?;
                for member in &group.members {
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

fn block_schedule_shape(
    block: &ResolvedBlock,
    include_nominals: bool,
    budget: &mut InterfaceConstraintBudget,
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
    use crate::{
        elaborate::{
            check_module, link_modules, link_modules_with_budget, link_modules_with_budgets,
        },
        interface::{EvidenceSelectionBuilder, match_implementation_head_structurally},
        module::{ModuleGraph, ModuleRoots, load_module_graph},
        resolve::{DependencyExports, resolve_module},
        resolved::{
            CheckedModule, ImplementationRoute, ImplementationRouteHop,
            LinkedCarrierMutationForTest, LinkedDeterminationCarrierForTest,
            LinkedDeterminationMutationForTest, LinkedGlobalParameterRowMutationForTest,
            ResolvedTypeVariable, same_imported_constructor_fact_with_budget,
        },
        source::{ByteRange, SourceFile},
        types::{InferenceVariableId, Kind, NominalTypeId, Type, TypeVariableId, TypeWorkBudget},
    };

    static FIXTURE_IDS: AtomicU64 = AtomicU64::new(0);

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
        // Substitution owns one initial task, then five work cells per
        // Application layer and one each for the Int root and Unit leaves.
        const DEEP_SUBSTITUTION_WORK: usize = 2 + 5 * DEPTH;
        // Two application-vector records precede both argument substitutions.
        const FIRST_ARGUMENT_PREFIX: usize = 2 + DEEP_SUBSTITUTION_WORK;
        // The trailing Bool owns one initial task and one rebuilt atom.
        const EXACT_CONSTRAINT_WORK: usize = FIRST_ARGUMENT_PREFIX + 2;

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
                let application = InterfaceApplication::new(
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
                    &interface.parameters,
                    interface.span,
                    &mut TypeWorkBudget::default(),
                )
                .expect("the interface environment should fit outside the measured operation");
            let mut constraint_work = InterfaceConstraintBudget::with_limit(constraint_limit);
            let mut type_work = TypeWorkBudget::with_limit(type_limit);
            let result = (|| {
                authenticate_linked_interface_application_kind(
                    fact.application(),
                    program.registry(),
                    &variables,
                    None,
                    &mut environments,
                    &mut constraint_work,
                    &mut type_work,
                    fact.span,
                )?;
                authenticate_linked_interface_application_kind(
                    prerequisite.application(),
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
        let registry =
            LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                .expect("the linked fixture registry should authenticate");
        validate_linked_value_schemes(
            &program,
            &registry,
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
        const GENERATED_ORIGIN_DEPTH: usize = 16_384;
        // Checked/source type equality is fused into synthesis. The canonical
        // lookup separately charges both checked and source Kind pairs, while
        // each scheduled codomain owns one continuation cell. Iterative
        // source-binder provenance owns its retained Origin cell. One retained
        // coverage-set cell proves the owner binder was visited; the module
        // and binder-owner authentication indexes add two fixed cells. Linked
        // registry-row authentication visits the identity row and parameter.
        const DEEP_TYPE_AND_KIND_WORK: usize = 9 * DEPTH;
        // The final unit publishes the private method-evidence authentication
        // capability only after every occurrence has validated.
        const PREEXISTING_FIXED_WORK: usize = 63 + 1 + 16;
        // Replacing the predecessor Source-Origin comparison with generated
        // causes plus its Source leaf adds exactly one cell per cause. Keep
        // that independent deep payload within the production constraint cap.
        const GENERATED_ORIGIN_DELTA: usize = GENERATED_ORIGIN_DEPTH;
        const ROW_WORK: usize = 2;
        const EXACT_WORK: usize =
            DEEP_TYPE_AND_KIND_WORK + PREEXISTING_FIXED_WORK + GENERATED_ORIGIN_DELTA + ROW_WORK;
        // TypeWork owns one canonical binder lookup and one declaration-kind
        // environment record.
        const CANONICAL_BINDER_LOOKUP_WORK: usize = 1;
        const DECLARATION_ENVIRONMENT_RECORD_WORK: usize = 1;
        const EXACT_TYPE_WORK: usize =
            CANONICAL_BINDER_LOOKUP_WORK + DECLARATION_ENVIRONMENT_RECORD_WORK;

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

                fn deep_origin(span: Span) -> Origin {
                    let mut origin = Origin::Source(span);
                    for _ in 0..GENERATED_ORIGIN_DEPTH {
                        origin = Origin::Generated {
                            cause: Box::new(origin),
                            reason: crate::source::GeneratedReason::TypeChecking,
                        };
                    }
                    origin
                }

                fn generated_origin_depth(mut origin: &Origin) -> usize {
                    let mut depth = 0;
                    loop {
                        match origin {
                            Origin::Generated { cause, reason } => {
                                assert_eq!(*reason, crate::source::GeneratedReason::TypeChecking);
                                depth += 1;
                                origin = cause;
                            }
                            Origin::Source(_) => return depth,
                            Origin::Related { .. } => {
                                panic!("the deep fixture must use only generated causes")
                            }
                        }
                    }
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
                    let origin_span = canonical.origin.primary_span();
                    let canonical_parameter = ResolvedTypeVariable {
                        id: parameter,
                        spelling: canonical.spelling.clone(),
                        kind: deep_kind(),
                        origin: deep_origin(origin_span),
                    };
                    assert!(program.replace_first_global_kind_boundary_for_test(
                        module,
                        (
                            canonical_parameter,
                            deep_kind(),
                            deep_kind(),
                            deep_origin(origin_span),
                        ),
                        (deep_value_type(parameter), deep_value_type(parameter)),
                    ));
                    let [row] = program.registry().global_parameter_rows() else {
                        panic!("the deep fixture must retain exactly one global row");
                    };
                    assert_eq!(row.parameters(), [parameter]);
                    let canonical = program
                        .registry()
                        .type_variable(parameter)
                        .expect("the deep source binder must remain canonical");
                    assert_eq!(
                        generated_origin_depth(&canonical.origin),
                        GENERATED_ORIGIN_DEPTH,
                    );
                    let source_origin = match program.groups()[0].definitions()[0].kind() {
                        ResolvedDefinitionKind::Equational(global) => {
                            &global.interface.type_parameters[0].origin
                        }
                        ResolvedDefinitionKind::InlineOperational(_) => {
                            panic!("the deep fixture must remain equational")
                        }
                    };
                    assert_eq!(
                        generated_origin_depth(source_origin),
                        GENERATED_ORIGIN_DEPTH,
                    );
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
        // Checking and freezing cost 8D + 18 type cells; complete producer
        // authentication adds 5D + 11 for the nominal and constructor scheme.
        // Keep the whole publication within the production type-work limit
        // while retaining deep ownership on the worker's small stack.
        const DEPTH: usize = 16_384;
        const DEFINING_TYPE_WORK: usize = 13 * DEPTH + 29;
        const {
            assert!(DEFINING_TYPE_WORK < crate::types::TYPE_WORK_LIMIT);
            assert!(13 * (2 * DEPTH) + 29 > crate::types::TYPE_WORK_LIMIT);
        }
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
            if module.id() != graph.entry() {
                assert_eq!(type_work.used(), DEFINING_TYPE_WORK);
            }
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

    #[test]
    fn generic_implementation_validation_excludes_discarded_head_scope_buffer_work() {
        const EXACT_WORK_WITHOUT_UNUSED_HEAD_BUFFER: usize = 6;
        let program = entry_program(concat!(
            "type Wrap<A> = Wrap(A)\n\n",
            "interface Marker<I> {\nmarker : I -> I\n}\n\n",
            "impl<A> Marker<Wrap<A>> {\nmarker value = value\n}\n\n",
            "main : Unit -> Unit\n",
            "main () = ()\n",
        ));
        let group = &program.groups()[0];
        let implementation = &group.implementations()[0];
        assert_eq!(
            group.implementation_facts()[0].head_parameters.len(),
            1,
            "the fixture must expose the obsolete head-scope allocation",
        );
        assert_eq!(implementation.method_groups().len(), 1);
        let run = |limit| {
            let registry =
                LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                    .expect("the generic implementation registry should authenticate");
            let mut type_work = TypeWorkBudget::default();
            let mut environments =
                build_linked_kind_environments(program.registry(), &mut type_work, group.span())
                    .expect("the nominal environment should fit");
            let mut budget = InterfaceConstraintBudget::with_limit(limit);
            let result = validate_implementation(
                &program,
                &registry,
                group,
                implementation,
                &mut environments,
                &mut budget,
                &mut type_work,
                false,
            );
            (result, budget.used())
        };

        let (one_short, one_short_used) = run(EXACT_WORK_WITHOUT_UNUSED_HEAD_BUFFER - 1);
        assert_eq!(
            one_short
                .expect_err("one missing body-validation cell must reject")
                .reason(),
            EvidenceValidationReason::ConstraintResourceExhausted,
        );
        assert_eq!(one_short_used, EXACT_WORK_WITHOUT_UNUSED_HEAD_BUFFER - 1);
        for _ in 0..2 {
            let (exact, exact_used) = run(EXACT_WORK_WITHOUT_UNUSED_HEAD_BUFFER);
            exact.expect("the exact implementation-body validation budget should fit");
            assert_eq!(exact_used, EXACT_WORK_WITHOUT_UNUSED_HEAD_BUFFER);
        }
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
                .method_evidence()
                .lexical_owners()
                .iter()
                .filter_map(|owner| owner.acquisition.map(|acquisition| (owner, acquisition)))
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
            // Full validation rejects a duplicate owner insertion, so success
            // above also proves the shared R is registered only once.
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
            let mut surplus = published_resource_program(implementation_only);
            let module = surplus
                .groups()
                .iter()
                .find(|group| {
                    group
                        .schemes()
                        .iter()
                        .any(|scheme| scheme.spelling == "readCell")
                        || !group.implementation_facts().is_empty()
                })
                .unwrap()
                .module();
            assert!(surplus.add_surplus_registry_type_variable_for_test(module));
            assert_eq!(
                validate_interface_evidence(surplus).unwrap_err().reason(),
                EvidenceValidationReason::UnknownIdentity
            );
        }
        for detach in [false, true] {
            let mut program = published_resource_program(false);
            assert!(program.corrupt_first_direct_resource_owner_for_test(detach));
            assert!(
                validate_interface_evidence(program).is_err(),
                "detached={detach} must publish no capability"
            );
        }
    }

    #[test]
    fn native_buffer_linked_authority_rejects_independent_acquisition_forgeries() {
        use crate::resolved::LinkedResourceMutationForTest as Mutation;
        for mutation in [
            Mutation::Provider,
            Mutation::DetachedOwner,
            Mutation::Builtin,
            Mutation::MethodOrder,
            Mutation::MethodKind,
            Mutation::Handle,
            Mutation::Brand,
            Mutation::Origin,
            Mutation::Operation,
        ] {
            crate::eval::reset_native_buffer_counters_for_test();
            let fixture = ValidationFixture::create(
                "import @builtin.native_buffer as Buffer\nmain : Unit -> Buffer.Outcome<Int>\nmain () = resource native_buffer<R> b = 4 {\nBuffer.length b\n}\n",
            );
            let graph = fixture.graph();
            let mut program =
                crate::elaborate::link_modules(check_graph(&graph), graph.entry()).unwrap();
            assert!(program.corrupt_first_direct_resource_for_test(mutation));
            assert!(
                validate_interface_evidence(program).is_err(),
                "mutation={mutation:?}"
            );
            assert_eq!(
                crate::eval::native_buffer_counters_for_test(),
                [0; 6],
                "mutation={mutation:?}"
            );
        }
    }

    #[test]
    fn native_buffer_linked_registry_authenticates_ordinary_constructor_payloads() {
        for error_payload in [false, true] {
            crate::eval::reset_native_buffer_counters_for_test();
            let fixture = ValidationFixture::create(
                "import @builtin.native_buffer as Buffer\nmain : Unit -> Int\nmain () = 42\n",
            );
            let graph = fixture.graph();
            let mut program =
                crate::elaborate::link_modules(check_graph(&graph), graph.entry()).unwrap();
            program.corrupt_native_constructor_for_test(error_payload);
            assert!(validate_interface_evidence(program).is_err());
            assert_eq!(crate::eval::native_buffer_counters_for_test(), [0; 6]);
        }
    }

    #[test]
    fn native_buffer_linked_authority_has_exact_one_short_and_fresh_budgets() {
        let fixture = ValidationFixture::create(
            "import @builtin.native_buffer as Buffer\nmain : Unit -> Buffer.Outcome<Buffer.Outcome<Int>>\nmain () = resource native_buffer<R> b = 4 {\nBuffer.read (b, 0)\n}\n",
        );
        let graph = fixture.graph();
        let run = |constraint_limit, type_limit| {
            let program =
                crate::elaborate::link_modules(check_graph(&graph), graph.entry()).unwrap();
            let mut constraints = InterfaceConstraintBudget::with_limit(constraint_limit);
            let mut types = TypeWorkBudget::with_limit(type_limit);
            let result =
                validate_interface_evidence_with_budget(program, &mut constraints, &mut types);
            (result, constraints.used(), types.used())
        };
        let (result, constraints, types) = run(
            crate::interface::INTERFACE_CONSTRAINT_WORK_LIMIT,
            crate::types::TYPE_WORK_LIMIT,
        );
        result.unwrap();
        assert_eq!(
            run(constraints - 1, types).0.unwrap_err().reason(),
            EvidenceValidationReason::ConstraintResourceExhausted
        );
        assert_eq!(
            run(constraints, types - 1).0.unwrap_err().reason(),
            EvidenceValidationReason::TypeResourceExhausted
        );
        for _ in 0..2 {
            let (result, used_constraints, used_types) = run(constraints, types);
            result.unwrap();
            assert_eq!((used_constraints, used_types), (constraints, types));
        }
    }

    #[test]
    fn mixed_namespace_method_catalog_is_canonical_and_exactly_retryable() {
        let program = published_resource_program(true);
        let run = |constraint_limit, type_limit| {
            let mut constraints = InterfaceConstraintBudget::with_limit(constraint_limit);
            let mut types = TypeWorkBudget::with_limit(type_limit);
            let result = build_core_method_evidence_catalog(&program, &mut constraints, &mut types);
            (result, constraints.used(), types.used())
        };
        let (catalog, constraints, types) = run(usize::MAX, usize::MAX);
        let catalog = catalog.unwrap();
        assert!(
            catalog
                .methods()
                .windows(2)
                .all(|pair| pair[0].id < pair[1].id)
        );
        assert_eq!(catalog.methods().len(), 3);
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
        let mut duplicate = published_resource_program(true);
        let builtin = duplicate
            .groups()
            .iter()
            .find(|group| {
                group.implementation_facts().is_empty() && !group.interface_facts().is_empty()
            })
            .unwrap()
            .interface_facts()[0]
            .methods[0]
            .id;
        let source = duplicate
            .groups()
            .iter()
            .find(|group| !group.implementation_facts().is_empty())
            .unwrap()
            .module();
        assert!(duplicate.replace_first_interface_method_id_for_test(source, builtin));
        assert_eq!(
            build_core_method_evidence_catalog(
                &duplicate,
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            )
            .unwrap_err()
            .reason(),
            EvidenceValidationReason::InvalidEvidenceRoot
        );
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
    fn unused_lexical_sources_authenticate_all_retained_declaration_facts() {
        validate_interface_evidence(unused_lexical_program())
            .expect("an unused but checked lexical source should authenticate");
        let mut accepted = Vec::new();
        for mutation in [
            LinkedCarrierMutationForTest::LexicalSourceIdentity,
            LinkedCarrierMutationForTest::LexicalApplicationArgument,
            LinkedCarrierMutationForTest::LexicalMethodIdentity,
            LinkedCarrierMutationForTest::LexicalMethodBinder,
            LinkedCarrierMutationForTest::LexicalEquationBinder,
            LinkedCarrierMutationForTest::LexicalEmptyEquations,
            LinkedCarrierMutationForTest::LexicalContextualParameter,
            LinkedCarrierMutationForTest::LexicalBeforeNominal,
        ] {
            let mut program = unused_lexical_program();
            let module = program.groups()[0].module();
            assert!(program.corrupt_linked_carrier_for_test(module, mutation));
            if validate_interface_evidence(program).is_ok() {
                accepted.push(mutation);
            }
        }
        assert!(
            accepted.is_empty(),
            "accepted unused-source tampering: {accepted:?}"
        );
    }

    #[test]
    fn intact_lexical_method_groups_may_remain_in_either_source_order() {
        let mut program = unused_lexical_program();
        let module = program.groups()[0].module();
        assert!(program.corrupt_linked_carrier_for_test(
            module,
            LinkedCarrierMutationForTest::LexicalMethodOrder
        ));
        validate_interface_evidence(program)
            .expect("source group order does not change each group's canonical method slot");
    }

    #[test]
    fn unused_lexical_header_requires_its_dependent_nominal_to_be_active() {
        let mut program = entry_program(concat!(
            "interface R<A, B> where A -> B {\nread : A -> Int\n}\n",
            "main : Unit -> Int\nmain () = {\nnewtype N = N(Unit)\nnewtype M = M(Unit)\n",
            "with R<N, M> {\nread ignored = 42\n}\n42\n}\n",
        ));
        let module = program.groups()[0].module();
        assert!(program.corrupt_linked_carrier_for_test(
            module,
            LinkedCarrierMutationForTest::LexicalBeforeNominal
        ));
        assert!(
            validate_interface_evidence(program).is_err(),
            "an active key nominal does not authorize a later dependent nominal"
        );
    }

    fn first_lexical_source(
        program: &ResolvedModuleProgram,
    ) -> &crate::resolved::ResolvedLexicalEvidence {
        program.groups()[0]
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
        let group = &program.groups()[0];
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
        let sources = [(source, None)];
        let scope = EvidenceScope {
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
    fn lexical_owner_lookup_charges_unrelated_method_table_width() {
        let program = lexical_resource_program();
        let source = first_lexical_source(&program);
        let fact = &program.groups()[0].interface_facts()[0];
        let mut methods = fact
            .methods
            .iter()
            .map(|method| MethodEvidenceMethod {
                id: method.id,
                interface_parameters: fact
                    .parameters
                    .iter()
                    .map(|parameter| parameter.id)
                    .collect(),
                parameters: Box::new([]),
                value_type: method.value_type().clone(),
            })
            .collect::<Vec<_>>();
        let mut base = InterfaceConstraintBudget::default();
        retain_lexical_owners(
            source,
            &methods,
            &mut Vec::new(),
            &mut base,
            &mut TypeWorkBudget::default(),
        )
        .expect("base owners");
        let unrelated = &program.groups()[0].interface_facts()[1];
        for method in &unrelated.methods {
            methods.push(MethodEvidenceMethod {
                id: method.id,
                interface_parameters: unrelated
                    .parameters
                    .iter()
                    .map(|parameter| parameter.id)
                    .collect(),
                parameters: Box::new([]),
                value_type: method.value_type().clone(),
            });
        }
        let mut wide = InterfaceConstraintBudget::default();
        retain_lexical_owners(
            source,
            &methods,
            &mut Vec::new(),
            &mut wide,
            &mut TypeWorkBudget::default(),
        )
        .expect("wide owners");
        // Four application-comparison cells and two owner slots. Per group:
        // E=1 equation, T canonical rows, P=2 replacements, three substituted
        // Type nodes and six cells comparing N -> Int with its checked scheme.
        assert_eq!(base.used(), 4 + 2 + 2 * (1 + 2 + 2 + 3 + 6));
        assert_eq!(wide.used(), 4 + 2 + 2 * (1 + 5 + 2 + 3 + 6));
        assert_eq!(
            wide.used() - base.used(),
            source.method_groups.len() * 3,
            "each supplied method scans the complete canonical table"
        );
        let work = wide.used();
        for limit in [work - 1, work, work] {
            let mut budget = InterfaceConstraintBudget::with_limit(limit);
            let mut owners = Vec::new();
            let result = retain_lexical_owners(
                source,
                &methods,
                &mut owners,
                &mut budget,
                &mut TypeWorkBudget::default(),
            );
            if limit < work {
                assert_eq!(
                    result
                        .expect_err("one-short owner authentication must reject")
                        .reason(),
                    EvidenceValidationReason::ConstraintResourceExhausted
                );
            } else {
                result.expect("the exact owner table must authenticate");
                assert_eq!(owners.len(), 2);
                assert_eq!(budget.used(), work);
            }
        }
    }

    #[test]
    fn lexical_block_scheduling_charges_its_shape_scan_before_retention() {
        let program = lexical_resource_program();
        let ResolvedDefinitionKind::Equational(global) =
            program.groups()[0].definitions()[0].kind()
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
            let group = &program.groups()[0];
            let source = first_lexical_source(&program);
            let checked = source.checked.get().expect("checked source");
            let Type::Application(_, token) = &checked.application.arguments()[0] else {
                panic!("Wrap<Token>");
            };
            let read = &group.implementation_facts()[0];
            let need = &group.implementation_facts()[1];
            let sources = [(source, None)];
            let scope = EvidenceScope {
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
                    vec![checked.application.arguments()[0].clone(), Type::Int]
                };
                let application = InterfaceApplication::new(
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
            let group = &program.groups()[0];
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
                    discard_type_iteratively(std::mem::replace(&mut resolved.ty, argument.clone()));
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
            let sources = [(&source, None)];
            let mut scope = EvidenceScope {
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
        let group = &program.groups()[0];
        let source = first_lexical_source(&program);
        let application = &source.checked.get().expect("checked source").application;
        let methods = &group.interface_facts()[0].methods;
        let sources = [(source, None)];
        let scope = EvidenceScope {
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
        let catalog = build_core_method_evidence_catalog(
            &program,
            &mut InterfaceConstraintBudget::default(),
            &mut TypeWorkBudget::default(),
        )
        .expect("complete lexical catalog");
        let method = &program.groups()[0].implementation_facts()[0].methods[0];
        // Owner visit, nominal worklist and node, variable worklist/node/slot,
        // and one source-parameter comparison.
        const EXACT: usize = 1 + 2 + 3 + 1;
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
        let method = &program.groups()[0].implementation_facts()[0].methods[0];
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

    fn dependent_only_global_program() -> ResolvedModuleProgram {
        entry_program(concat!(
            "interface Measure<I, Item> where I -> Item {\n",
            "measure : I -> Int\n",
            "}\n\n",
            "size<I, Item> : I -> Int where Measure<I, Item>\n",
            "size value = 0\n\n",
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
    fn linked_method_evidence_catalog_has_exact_independent_ledgers() {
        let program = polymorphic_method_program();
        let mut measured_constraint = InterfaceConstraintBudget::default();
        let mut measured_type = TypeWorkBudget::default();
        let catalog = build_core_method_evidence_catalog(
            &program,
            &mut measured_constraint,
            &mut measured_type,
        )
        .expect("the measured linked method-evidence catalog should build");
        assert!(!catalog.expectations().is_empty());
        let constraint_work = measured_constraint.used();
        let type_work = measured_type.used();
        // The predecessor formula is 87. This fixture retains C=2 exact
        // occurrence-owner binders and A=1 adapter selection identity in both
        // the adapter row and its expectation lookup key. The bounded concrete
        // source pass counts and then reads E=4 expectations, reserves G=1
        // edge-root slot, and classifies M=1 selected source method. The
        // selected implementation lookup has J=1 candidate and therefore
        // charges one search slot. Its checked width derivations first admit
        // B=3 implementation/interface header reads, before traversing
        // those rows:
        // Its producer lookups additionally read P=2 selected-node method
        // cells. The five retained checked applications now each preserve their
        // complete ordered carrier rather than one scalar argument:
        // 87 + C + 2A + 2E + G + M + J + B + P = 107 constraint units;
        // type work rises by five carrier argument visits to 79.
        assert_eq!(constraint_work, 107);
        assert_eq!(type_work, 79);
        drop(catalog);

        let mut constraint_short = InterfaceConstraintBudget::with_limit(constraint_work - 1);
        let mut type_default = TypeWorkBudget::default();
        assert_eq!(
            build_core_method_evidence_catalog(&program, &mut constraint_short, &mut type_default,)
                .expect_err("one missing catalog relation unit must reject before publication")
                .reason(),
            EvidenceValidationReason::ConstraintResourceExhausted,
        );
        assert_eq!(constraint_short.used(), constraint_work - 1);

        let mut constraint_default = InterfaceConstraintBudget::default();
        let mut type_short = TypeWorkBudget::with_limit(type_work - 1);
        assert_eq!(
            build_core_method_evidence_catalog(&program, &mut constraint_default, &mut type_short,)
                .expect_err("one missing retained Type or Kind cell must reject publication")
                .reason(),
            EvidenceValidationReason::TypeResourceExhausted,
        );
        assert_eq!(type_short.used(), 75);

        for _ in 0..2 {
            let mut constraint_exact = InterfaceConstraintBudget::with_limit(constraint_work);
            let mut type_exact = TypeWorkBudget::with_limit(type_work);
            let retry = build_core_method_evidence_catalog(
                &program,
                &mut constraint_exact,
                &mut type_exact,
            )
            .expect("a fresh exact catalog stage should retry reproducibly");
            assert_eq!(constraint_exact.used(), constraint_work);
            assert_eq!(type_exact.used(), type_work);
            drop(retry);
        }
    }

    #[test]
    fn lexical_contextual_count_failure_discards_deep_replacements_on_a_small_stack() {
        thread::Builder::new()
            .name("lexical-contextual-replacement-drop".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let file = SourceFile::new("lexical-contextual-drop.ash", "Read").expect("fixture");
                let span = file
                    .span(ByteRange::new(0, 4).expect("range"))
                    .expect("span");
                let module = ModuleId::from(file.id());
                let interface = InterfaceId::new(module, 0);
                let method = MethodId::new(interface, 0);
                let binder = BinderId::resolved(module, 0);
                let id = crate::interface::LexicalEvidenceId::new(module, 0);
                let checked = crate::interface::LexicalEvidenceSlot::default();
                checked
                    .fill(crate::interface::CheckedLexicalEvidence {
                        acquisition: None,
                        id,
                        application: InterfaceApplication::new(
                            interface,
                            Box::new([deep_application_type(16_384)]),
                        ),
                        methods: Box::new([crate::interface::CheckedLexicalMethod {
                            method,
                            binder,
                            scheme: Type::Int,
                            captures: Box::new([]),
                        }]),
                    })
                    .expect("checked fixture");
                let mut source = crate::resolved::ResolvedLexicalEvidence {
                    acquisition: None,
                    checked,
                    id,
                    span,
                    application: ResolvedInterfaceApplication {
                        interface: crate::resolved::ResolvedInterfaceOccurrence {
                            id: interface,
                            spelling: "Read".to_owned(),
                            origin: Origin::Source(span),
                        },
                        arguments: Box::new([crate::resolved::ResolvedType {
                            ty: deep_application_type(16_384),
                            provenance: crate::resolved::ResolvedTypeProvenance::new(
                                vec![crate::resolved::ResolvedTypeProvenanceNode::Fact(span)],
                                0,
                            ),
                            origin: Origin::Source(span),
                            span,
                        }]),
                        span,
                    },
                    method_groups: Box::new([crate::resolved::ResolvedImplementationMethodGroup {
                        contextual_parameters: Box::new([]),
                        method: Some(method),
                        identity: None,
                        binder: crate::resolved::Binder {
                            id: binder,
                            spelling: "read".to_owned(),
                            origin: Origin::Source(span),
                        },
                        equations: Box::new([crate::resolved::ResolvedEquation {
                            name: crate::resolved::ResolvedEquationHead {
                                binder,
                                spelling: "read".to_owned(),
                                origin: Origin::Source(span),
                            },
                            patterns: Vec::new(),
                            body: ResolvedExpr {
                                kind: ResolvedExprKind::Unit,
                                span,
                            },
                            span,
                        }]),
                        span,
                    }]),
                };
                let methods = [MethodEvidenceMethod {
                    id: method,
                    interface_parameters: Box::new([TypeVariableId::resolved(module, 0)]),
                    parameters: Box::new([(TypeVariableId::resolved(module, 1), Kind::Type)]),
                    value_type: Type::Int,
                }];
                let mut type_work = TypeWorkBudget::default();
                assert_eq!(
                    retain_lexical_owners(
                        &source,
                        &methods,
                        &mut Vec::new(),
                        &mut InterfaceConstraintBudget::default(),
                        &mut type_work
                    )
                    .expect_err("the malformed contextual count must reject")
                    .reason(),
                    EvidenceValidationReason::InvalidEvidenceRoot
                );
                assert!(
                    type_work.used() > 16_384,
                    "the rejection must occur after retaining the deep replacement"
                );
                discard_type_iteratively(std::mem::replace(
                    &mut source.application.arguments[0].ty,
                    Type::Unit,
                ));
            })
            .expect("small-stack worker")
            .join()
            .expect("failure must dispose iteratively");
    }

    #[test]
    fn lexical_plan_scans_preserve_the_no_source_fast_path() {
        for program in [generic_program(), polymorphic_method_program()] {
            LEXICAL_PLAN_INSPECTIONS.with(|count| count.set(0));
            let catalog = build_core_method_evidence_catalog(
                &program,
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            )
            .expect("existing concrete plans should build without lexical scanning");
            assert!(catalog.lexical_owners().is_empty());
            assert_eq!(LEXICAL_PLAN_INSPECTIONS.with(std::cell::Cell::get), 0);
            let registry =
                LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                    .expect("registry");
            let mut constraints = InterfaceConstraintBudget::with_limit(0);
            let mut types = TypeWorkBudget::with_limit(0);
            validate_lexical_headers(
                &program,
                &registry,
                &catalog,
                &mut KindEnvironments::new(),
                &mut constraints,
                &mut types,
            )
            .expect("source-free programs skip header authentication");
            assert_eq!(constraints.used(), 0);
            assert_eq!(types.used(), 0);
        }
    }

    #[test]
    fn lexical_header_pass_has_exact_independent_retry_boundaries() {
        let program = lexical_resource_program();
        let registry =
            LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                .expect("registry");
        let catalog = build_core_method_evidence_catalog(
            &program,
            &mut InterfaceConstraintBudget::default(),
            &mut TypeWorkBudget::default(),
        )
        .expect("catalog");
        assert_eq!(catalog.lexical_owners().len(), 2);
        let run = |constraint_limit, type_limit| {
            let mut environments = build_linked_kind_environments(
                program.registry(),
                &mut TypeWorkBudget::default(),
                program.result().span,
            )
            .expect("kind environments");
            let mut constraints = InterfaceConstraintBudget::with_limit(constraint_limit);
            let mut types = TypeWorkBudget::with_limit(type_limit);
            let result = validate_lexical_headers(
                &program,
                &registry,
                &catalog,
                &mut environments,
                &mut constraints,
                &mut types,
            );
            (result, constraints.used(), types.used())
        };
        let (result, constraint_work, type_work) = run(usize::MAX, usize::MAX);
        result.expect("the complete header-only pass should authenticate");
        // Seven outer visits, then shape(4), nominal scope(2), header(16),
        // source(2), expression/scope slots(9), four body/scope visits and
        // six generated entry-expression units. N and Int use three type cells.
        assert_eq!(constraint_work, 7 + (4 + 2 + 16 + 2 + 9) + 4 + 6);
        assert_eq!(type_work, 3);
        assert_eq!(
            run(constraint_work - 1, type_work)
                .0
                .expect_err("one-short header constraint budget")
                .reason(),
            EvidenceValidationReason::ConstraintResourceExhausted
        );
        assert_eq!(
            run(constraint_work, type_work - 1)
                .0
                .expect_err("one-short header type budget")
                .reason(),
            EvidenceValidationReason::TypeResourceExhausted
        );
        for _ in 0..2 {
            let (result, constraints, types) = run(constraint_work, type_work);
            result.expect("fresh exact budgets retry header authentication");
            assert_eq!((constraints, types), (constraint_work, type_work));
        }
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
    fn widened_abstract_producer_lookup_has_an_exact_retry_boundary() {
        let program = widened_abstract_method_source_program();
        let mut measured_constraint = InterfaceConstraintBudget::default();
        let mut measured_type = TypeWorkBudget::default();
        let catalog = build_core_method_evidence_catalog(
            &program,
            &mut measured_constraint,
            &mut measured_type,
        )
        .expect("the widened abstract-only catalog should build");
        assert_eq!(catalog.domains().len(), 2);
        assert!(catalog.adapters().is_empty());
        let producer_lookups = catalog
            .expectations()
            .iter()
            .filter(|expectation| {
                matches!(
                    expectation.role,
                    MethodEvidenceExpectedRole::Instantiation { .. }
                        | MethodEvidenceExpectedRole::Application { .. }
                )
            })
            .count();
        assert_eq!(producer_lookups, 2);
        // The fixed abstract-only catalog costs 85 constraint units. Its two
        // producer lookups each read the exact W=2 selected-node method list;
        // D=2 domain scans were already charged and A=0:
        // 85 + L*W = 85 + 2*2 = 89.
        const CONSTRAINT_WORK: usize = 85 + 2 * 2;
        // Two complete abstract applications retain three additional Type
        // carrier cells each beyond their predecessor scalar form.
        const TYPE_WORK: usize = 38;
        assert_eq!(measured_constraint.used(), CONSTRAINT_WORK);
        assert_eq!(measured_type.used(), TYPE_WORK);
        drop(catalog);

        let mut constraint_short = InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK - 1);
        assert_eq!(
            build_core_method_evidence_catalog(
                &program,
                &mut constraint_short,
                &mut TypeWorkBudget::default(),
            )
            .expect_err("one missing selected-method scan unit rejects publication")
            .reason(),
            EvidenceValidationReason::ConstraintResourceExhausted,
        );
        let mut type_short = TypeWorkBudget::with_limit(TYPE_WORK - 1);
        assert_eq!(
            build_core_method_evidence_catalog(
                &program,
                &mut InterfaceConstraintBudget::default(),
                &mut type_short,
            )
            .expect_err("one missing abstract-only Type cell rejects publication")
            .reason(),
            EvidenceValidationReason::TypeResourceExhausted,
        );
        for _ in 0..2 {
            let mut constraint_exact = InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK);
            let mut type_exact = TypeWorkBudget::with_limit(TYPE_WORK);
            let retry = build_core_method_evidence_catalog(
                &program,
                &mut constraint_exact,
                &mut type_exact,
            )
            .expect("a fresh exact widened producer stage retries");
            assert_eq!(constraint_exact.used(), CONSTRAINT_WORK);
            assert_eq!(type_exact.used(), TYPE_WORK);
            drop(retry);
        }
    }

    #[test]
    fn concrete_adapter_source_catalog_has_an_exact_retry_boundary() {
        let program = concrete_monomorphic_source_program();
        let mut measured_constraint = InterfaceConstraintBudget::default();
        let mut measured_type = TypeWorkBudget::default();
        let catalog = build_core_method_evidence_catalog(
            &program,
            &mut measured_constraint,
            &mut measured_type,
        )
        .expect("the concrete source catalog should build");
        assert_eq!(catalog.concrete_sources().len(), 1);
        // The fixed linked adapter pipeline costs 122 constraint units after
        // separately charging every count/search pass over checked methods,
        // interface methods, owner candidates, and requirement interfaces,
        // including checked outer row reads before deriving widths. The
        // source pass adds 2E=8 expectation passes, G=1 root capacity, C=1
        // occurrence lookup, J=2 checked-method reads, M=1 selected-method
        // membership, P=1 polymorphic-method classification, and five retained
        // complete checked applications (four carrier cells each). This ground
        // source has H=0 cloned head Types.
        const CONSTRAINT_WORK: usize = 122 + 8 + 1 + 1 + 2 + 1 + 1 + 5 * 4;
        // Three retained complete application arguments add three Type carrier
        // cells each to this concrete adapter source.
        const TYPE_WORK: usize = 45;
        assert_eq!(measured_constraint.used(), CONSTRAINT_WORK);
        assert_eq!(measured_type.used(), TYPE_WORK);
        drop(catalog);

        let mut constraint_short = InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK - 1);
        assert_eq!(
            build_core_method_evidence_catalog(
                &program,
                &mut constraint_short,
                &mut TypeWorkBudget::default(),
            )
            .expect_err("one missing concrete-source catalog unit rejects")
            .reason(),
            EvidenceValidationReason::ConstraintResourceExhausted,
        );
        let mut type_short = TypeWorkBudget::with_limit(TYPE_WORK - 1);
        assert_eq!(
            build_core_method_evidence_catalog(
                &program,
                &mut InterfaceConstraintBudget::default(),
                &mut type_short,
            )
            .expect_err("one missing catalog Type cell rejects")
            .reason(),
            EvidenceValidationReason::TypeResourceExhausted,
        );
        for _ in 0..2 {
            let mut exact_constraint = InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK);
            let mut exact_type = TypeWorkBudget::with_limit(TYPE_WORK);
            let retry = build_core_method_evidence_catalog(
                &program,
                &mut exact_constraint,
                &mut exact_type,
            )
            .expect("a fresh exact concrete-source catalog retries");
            assert_eq!(exact_constraint.used(), CONSTRAINT_WORK);
            assert_eq!(exact_type.used(), TYPE_WORK);
            drop(retry);
        }
    }

    fn same_shaped_method_program() -> ResolvedModuleProgram {
        entry_program(concat!(
            "interface Choose<I> {\n",
            "first<A> : (I, A) -> I\n",
            "second<B> : (I, B) -> I\n",
            "}\n\n",
            "impl Choose<Bool> {\n",
            "first pair = true\n",
            "second pair = true\n",
            "}\n\n",
            "main : Unit -> Bool\n",
            "main () = first((true, false))\n",
        ))
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

    #[test]
    fn rejects_same_shaped_method_occurrence_identity_substitution() {
        let mut program = same_shaped_method_program();
        let group = &program.groups()[0];
        let module = group.module();
        let second = group.interface_facts()[0].methods[1].id;
        assert!(
            program.replace_nth_direct_method_occurrence_identity_for_test(module, 0, second),
            "the fixture should expose its first method occurrence",
        );

        assert_eq!(
            validate_interface_evidence(program)
                .expect_err("retained occurrence evidence must reject a same-shaped MethodId")
                .reason(),
            EvidenceValidationReason::InvalidEvidenceRoot,
        );
    }

    #[test]
    fn rejects_same_shaped_retained_method_identity_substitution() {
        let mut program = same_shaped_method_program();
        let group = &program.groups()[0];
        let module = group.module();
        let second = group.interface_facts()[0].methods[1].id;
        assert!(
            program.replace_nth_direct_method_evidence_identity_for_test(module, 0, second),
            "the fixture should expose the retained identity of its first occurrence",
        );
        assert_eq!(
            validate_interface_evidence(program)
                .expect_err("the retained MethodId must equal the occurrence MethodId")
                .reason(),
            EvidenceValidationReason::InvalidEvidenceRoot,
        );
    }

    #[test]
    fn rejects_wrong_concrete_method_relationship_for_same_shaped_occurrence() {
        let mut program = same_shaped_method_program();
        let group = &program.groups()[0];
        let module = group.module();
        let implementation = &group.implementation_facts()[0];
        let [first, second] = implementation.methods.as_ref() else {
            panic!("the fixture should retain two implementation methods");
        };
        let forged = implementation_selection_for_argument(
            implementation.id,
            implementation.interface(),
            &[second.id, first.id],
            Type::Bool,
        );
        assert!(
            program.replace_nth_direct_method_occurrence_selection_for_test(module, 0, forged),
            "the fixture should expose its concrete method occurrence",
        );
        assert_eq!(
            validate_interface_evidence(program)
                .expect_err("concrete evidence must retain the canonical ImplMethodId relation")
                .reason(),
            EvidenceValidationReason::InvalidEvidenceRoot,
        );
    }

    #[test]
    fn rejects_wrong_abstract_method_relationship_for_same_shaped_occurrence() {
        let mut program = entry_program(concat!(
            "interface Choose<I> {\n",
            "first<A> : (I, A) -> I\n",
            "second<B> : (I, B) -> I\n",
            "}\n\n",
            "relay<I, A> : (I, A) -> I where Choose<I>\n",
            "relay pair = first(pair)\n\n",
            "impl Choose<Bool> {\n",
            "first pair = true\n",
            "second pair = true\n",
            "}\n\n",
            "main : Unit -> Bool\n",
            "main () = relay((true, false))\n",
        ));
        let group = &program.groups()[0];
        let module = group.module();
        let interface = &group.interface_facts()[0];
        let requirement = group
            .schemes()
            .iter()
            .find(|scheme| scheme.spelling == "relay")
            .and_then(|scheme| scheme.scheme.requirements.first())
            .expect("relay should retain its abstract requirement");
        let second = interface.methods[1].id;
        let mut builder = EvidenceSelectionBuilder::new();
        let root = builder
            .push_abstract(
                requirement.id,
                &[second],
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the forged abstract method row should fit");
        let forged = finish_width_one(
            builder,
            root,
            interface.id,
            requirement.arguments()[0].clone(),
        )
        .expect("the forged abstract selection should have a root");
        assert!(
            program.replace_nth_direct_method_occurrence_selection_for_test(module, 0, forged),
            "the relay should expose its abstract method occurrence",
        );
        assert_eq!(
            validate_interface_evidence(program)
                .expect_err("abstract evidence must retain the selected MethodId relation")
                .reason(),
            EvidenceValidationReason::InvalidEvidenceRoot,
        );
    }

    #[test]
    fn rejects_wrong_exact_current_impl_method_relationship() {
        let mut program = entry_program(concat!(
            "interface Choose<I> {\n",
            "first<A> : (I, A) -> I\n",
            "second<B> : (I, B) -> I\n",
            "}\n\n",
            "impl Choose<Bool> {\n",
            "first pair = first(pair)\n",
            "second pair = true\n",
            "}\n\n",
            "main : Unit -> Bool\n",
            "main () = first((true, false))\n",
        ));
        let group = &program.groups()[0];
        let module = group.module();
        let implementation = &group.implementation_facts()[0];
        let [first, second] = implementation.methods.as_ref() else {
            panic!("the exact-current fixture should retain two implementation methods");
        };
        let forged = implementation_selection_for_argument(
            implementation.id,
            implementation.interface(),
            &[second.id, first.id],
            Type::Bool,
        );
        assert!(
            program.replace_nth_direct_method_occurrence_selection_for_test(module, 0, forged),
            "the implementation should expose its exact-current occurrence",
        );
        assert_eq!(
            validate_interface_evidence(program)
                .expect_err(
                    "exact-current evidence must retain the canonical ImplMethodId relation"
                )
                .reason(),
            EvidenceValidationReason::InvalidEvidenceRoot,
        );
    }

    #[test]
    fn rejects_polymorphic_method_occurrence_argument_and_identity_tampering() {
        enum Mutation {
            Missing,
            Extra,
            Reordered,
            WrongKind,
            WrongCheckedType,
            WrongMethod,
        }

        for mutation in [
            Mutation::Missing,
            Mutation::Extra,
            Mutation::Reordered,
            Mutation::WrongKind,
            Mutation::WrongCheckedType,
            Mutation::WrongMethod,
        ] {
            let mut program = polymorphic_method_program();
            let module = program.groups()[0].module();
            let changed = match mutation {
                Mutation::Missing => program
                    .replace_nth_direct_method_occurrence_arguments_for_test(
                        module,
                        1,
                        Box::new([]),
                    ),
                Mutation::Extra => program.replace_nth_direct_method_occurrence_arguments_for_test(
                    module,
                    1,
                    Box::new([
                        Type::Nominal(NominalTypeId::new(module, 0)),
                        Type::Bool,
                        Type::Int,
                        Type::Unit,
                    ]),
                ),
                Mutation::Reordered => program
                    .replace_nth_direct_method_occurrence_arguments_for_test(
                        module,
                        1,
                        Box::new([
                            Type::Nominal(NominalTypeId::new(module, 0)),
                            Type::Int,
                            Type::Bool,
                        ]),
                    ),
                Mutation::WrongKind => program
                    .replace_nth_direct_method_occurrence_arguments_for_test(
                        module,
                        1,
                        Box::new([Type::Bool, Type::Bool, Type::Int]),
                    ),
                Mutation::WrongCheckedType => program
                    .replace_nth_direct_method_occurrence_checked_type_for_test(
                        module,
                        1,
                        Type::Int,
                    ),
                Mutation::WrongMethod => program
                    .replace_nth_direct_method_occurrence_identity_for_test(
                        module,
                        1,
                        MethodId::new(InterfaceId::new(module, 0), u32::MAX),
                    ),
            };
            assert!(
                changed,
                "the fixture should expose its concrete method occurrence"
            );
            let expected = if matches!(mutation, Mutation::WrongMethod) {
                EvidenceValidationReason::UnknownIdentity
            } else {
                EvidenceValidationReason::InvalidEvidenceRoot
            };
            assert_eq!(
                validate_interface_evidence(program)
                    .expect_err("forged method occurrence evidence must fail before Core")
                    .reason(),
                expected,
            );
        }
    }

    #[test]
    fn rejects_reordered_implementation_head_then_method_binder_relationship() {
        let mut program = polymorphic_method_program();
        let module = program.groups()[0].module();
        assert!(
            program.swap_first_implementation_method_scheme_parameters_for_test(module),
            "the fixture should retain the combined head-then-method scheme",
        );
        assert_eq!(
            validate_interface_evidence(program)
                .expect_err("a reordered combined implementation method scheme must fail")
                .reason(),
            EvidenceValidationReason::UnknownIdentity,
        );
    }

    #[test]
    fn rejects_forged_implementation_head_method_partition_before_capability() {
        let mut program = polymorphic_method_program();
        let module = program.groups()[0].module();
        let method = &program.groups()[0].implementation_facts()[0].methods[0];
        assert_eq!(method.head_type_parameter_count(), 1);
        assert_eq!(method.scheme.type_parameters.len(), 4);
        assert!(
            program.replace_first_implementation_method_head_parameter_count_for_test(module, 0),
            "the fixture should expose only its stored head/method partition",
        );

        assert_eq!(
            validate_interface_evidence(program)
                .expect_err("a forged partition must publish no validation capability")
                .reason(),
            EvidenceValidationReason::UnknownIdentity,
        );
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
        builder.finish(
            root,
            InterfaceApplication::new(interface, Box::new([argument])),
        )
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
            LinkedGlobalParameterRowMutationForTest::SurplusOwnerPosition,
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
                LinkedGlobalParameterRowMutationForTest::SurplusOwnerPosition
                | LinkedGlobalParameterRowMutationForTest::ExtraRow => result_span,
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
                LinkedGlobalParameterRowMutationForTest::SurplusOwnerPosition => {
                    let rows = program.registry().global_parameter_rows();
                    assert_eq!(rows.len(), 2);
                    assert_eq!([rows[0].owner(), rows[1].owner()], original_owners);
                    assert_eq!(
                        program.registry().global_parameter_position_count(),
                        rows.len() + 1,
                    );
                    assert!(
                        program
                            .registry()
                            .global_parameter_row(empty_owner)
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
        const GROUPS: usize = 2;
        const TYPE_VARIABLES: usize = 4;
        const GLOBAL_SCHEMES: usize = 3;
        const GLOBAL_ROWS: usize = 2;
        const GLOBAL_PARAMETERS: usize = 4;
        const ROOT_VISIT_WORK: usize = 1;
        const AUTHENTICATION_INDEX_WORK: usize = GROUPS + TYPE_VARIABLES;
        const GROUP_VISIT_WORK: usize = GROUPS;
        const GLOBAL_SCHEME_VISIT_WORK: usize = GLOBAL_SCHEMES;
        const GLOBAL_OWNER_IDENTITY_WORK: usize = GLOBAL_PARAMETERS;
        const OWNER_COVERAGE_WORK: usize = 1;
        const ROW_AUTHENTICATION_WORK: usize = GLOBAL_ROWS + GLOBAL_PARAMETERS;
        const EXACT_AUTHENTICATION_WORK: usize = ROOT_VISIT_WORK
            + AUTHENTICATION_INDEX_WORK
            + GROUP_VISIT_WORK
            + GLOBAL_SCHEME_VISIT_WORK
            + GLOBAL_OWNER_IDENTITY_WORK
            + OWNER_COVERAGE_WORK
            + ROW_AUTHENTICATION_WORK;
        const AUTHENTICATION_PREFIX_WORK: usize =
            EXACT_AUTHENTICATION_WORK - OWNER_COVERAGE_WORK - ROW_AUTHENTICATION_WORK;

        let program = linked_registry_row_program();
        let row_count = program.registry().global_parameter_rows().len();
        let parameter_count = program
            .registry()
            .global_parameter_rows()
            .iter()
            .map(|row| row.parameters().len())
            .sum::<usize>();
        let exact_row_work = row_count + parameter_count;
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
        assert_eq!(exact_row_work, ROW_AUTHENTICATION_WORK);
        assert_eq!(EXACT_AUTHENTICATION_WORK, 23);

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

        let mut authentication_short =
            InterfaceConstraintBudget::with_limit(EXACT_AUTHENTICATION_WORK - 1);
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
        assert_eq!(authentication_short.used(), EXACT_AUTHENTICATION_WORK - 1,);
        assert_eq!(untouched_type_work.used(), 0);

        let mut authentication_exact =
            InterfaceConstraintBudget::with_limit(AUTHENTICATION_PREFIX_WORK);
        authenticate_linked_registry_facts(&retry, &mut authentication_exact)
            .expect("the immutable fixture must retry with the exact pre-method prefix");
        assert_eq!(authentication_exact.used(), AUTHENTICATION_PREFIX_WORK);

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
            .expect("the all-owner linked registry prefix should authenticate");
        let exact_work = measured.used();
        assert!(exact_work > index_boundary);
        let mut one_short = InterfaceConstraintBudget::with_limit(exact_work - 1);
        assert!(authenticate_linked_registry_facts(&program, &mut one_short).is_err());
        for _ in 0..2 {
            let mut exact = InterfaceConstraintBudget::with_limit(exact_work);
            authenticate_linked_registry_facts(&program, &mut exact)
                .expect("the immutable all-owner registry prefix should remain reusable");
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
            &fact.arguments()[0],
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
    fn interface_substitution_compares_effectful_methods_exactly_and_retryably() {
        let program = entry_program(
            "interface Read<A> {\nread : A -> A\n}\nmain : Unit -> Unit\nmain () = ()\n",
        );
        let parameters = &program.groups()[0].interface_facts()[0].parameters;
        let span = program.result().span;
        let effect = crate::types::EffectId::new(ModuleId::new(77), 0);
        let free = TypeVariableId::generated(900);
        let function = |argument| {
            Type::function_computation(
                Type::Variable(free),
                crate::types::ComputationType::new(
                    Type::Int,
                    crate::types::EffectRow::singleton(crate::types::EffectInstance::new(
                        effect,
                        Box::new([argument]),
                    )),
                ),
            )
        };
        let source = function(Type::Variable(parameters[0].id));
        let actual = function(Type::Bool);
        let mut measured = InterfaceConstraintBudget::default();
        assert!(
            same_type_after_interface_substitution(
                &source,
                parameters,
                &[Type::Bool],
                &actual,
                &mut measured,
                span
            )
            .unwrap()
        );
        let exact = measured.used();
        let error = same_type_after_interface_substitution(
            &source,
            parameters,
            &[Type::Bool],
            &actual,
            &mut InterfaceConstraintBudget::with_limit(exact - 1),
            span,
        )
        .unwrap_err();
        assert_eq!(
            error.reason(),
            EvidenceValidationReason::ConstraintResourceExhausted
        );
        for _ in 0..2 {
            assert!(
                same_type_after_interface_substitution(
                    &source,
                    parameters,
                    &[Type::Bool],
                    &actual,
                    &mut InterfaceConstraintBudget::with_limit(exact),
                    span
                )
                .unwrap()
            );
        }
        assert!(
            !same_type_after_interface_substitution(
                &source,
                parameters,
                &[Type::Int],
                &actual,
                &mut InterfaceConstraintBudget::default(),
                span
            )
            .unwrap()
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
            5 * (WIDE - NARROW) as usize,
            "each nullary member owns equality, collection, validation, shape, and retained-member work"
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

    fn relational_application_program() -> ResolvedModuleProgram {
        entry_program(concat!(
            "type Wrap<A> = Wrap(A)\n\n",
            "interface Relation<F : Type -> Type, Key, Dep> where (F, Key) -> Dep {\n",
            "relate<X> : (F<Key>, X) -> F<Dep>\n",
            "}\n\n",
            "impl Relation<Wrap, Int, Bool> {\n",
            "relate pair = Wrap(true)\n",
            "}\n\n",
            "relay<F : Type -> Type, Key, Dep, X> : (F<Key>, X) -> F<Dep> ",
            "where Relation<F, Key, Dep>\n",
            "relay pair = relate(pair)\n\n",
            "main : Unit -> Wrap<Bool>\n",
            "main () = relate((Wrap(1), ()))\n",
        ))
    }

    fn hidden_relational_application_program() -> ResolvedModuleProgram {
        entry_program(concat!(
            "type Hidden = HiddenValue(Int)\n",
            "type HiddenTwin = HiddenTwinValue(Int)\n",
            "type Wrap<A> = Wrap(A)\n\n",
            "interface Relation<F : Type -> Type, Key, Dep> where (F, Key) -> Dep {\n",
            "relate<X> : (F<Key>, X) -> F<Dep>\n",
            "}\n\n",
            "hidden<F : Type -> Type, Key, X> : (F<Key>, X) -> F<Hidden> ",
            "where Relation<F, Key, Hidden>\n",
            "hidden pair = relate(pair)\n\n",
            "main : Unit -> Unit\n",
            "main () = ()\n",
        ))
    }

    fn implementation_selection_for_application(
        fact: &CheckedImplementationFact,
        arguments: Box<[Type]>,
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
            .finish(root, InterfaceApplication::new(fact.interface(), arguments))
            .expect("a forged application root should remain representable")
    }

    fn abstract_selection_for_application(
        requirement: RequirementId,
        interface: &CheckedInterfaceFact,
        arguments: Box<[Type]>,
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
            .finish(root, InterfaceApplication::new(interface.id, arguments))
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
            method_evidence: _,
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
        let group = &program.groups()[0];
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
        let group = &program.groups()[0];
        let fact = &group.implementation_facts()[0];
        let registry =
            LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                .expect("the canonical linked registry should authenticate");

        for arguments in [
            Box::new([]),
            vec![Type::Int, Type::Bool, Type::Unit].into_boxed_slice(),
            vec![Type::Bool, Type::Int].into_boxed_slice(),
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
    fn rejects_selection_root_application_that_differs_from_its_frozen_slot() {
        let mut program = two_application_parameter_program();
        let group = &program.groups()[0];
        let module = group.module();
        let fact = &group.implementation_facts()[0];
        let forged = implementation_selection_for_application(
            fact,
            vec![Type::Bool, Type::Int].into_boxed_slice(),
        );
        assert!(
            program.replace_nth_direct_method_occurrence_selection_for_test(module, 0, forged),
            "the direct method occurrence should retain one frozen slot"
        );

        assert_eq!(
            validate_interface_evidence(program)
                .expect_err("a selection root must equal the already frozen checked application")
                .reason(),
            EvidenceValidationReason::InvalidEvidenceRoot,
        );
    }

    #[test]
    fn rejects_relational_linked_parameter_and_application_tampering_before_core() {
        let mutations = [
            LinkedCarrierMutationForTest::RelationalInterfaceParameterMissing,
            LinkedCarrierMutationForTest::RelationalInterfaceParameterExtra,
            LinkedCarrierMutationForTest::RelationalInterfaceParameterReordered,
            LinkedCarrierMutationForTest::RelationalInterfaceParameterWrongKind,
            LinkedCarrierMutationForTest::RelationalInterfaceParameterWrongIdentity,
            LinkedCarrierMutationForTest::RelationalApplicationArgumentMissing,
            LinkedCarrierMutationForTest::RelationalApplicationArgumentExtra,
            LinkedCarrierMutationForTest::RelationalApplicationArgumentReordered,
            LinkedCarrierMutationForTest::RelationalApplicationArgumentWrongKind,
            LinkedCarrierMutationForTest::RelationalApplicationArgumentWrongIdentity,
        ];

        validate_interface_evidence(two_application_parameter_program())
            .expect("the canonical relational linked fixture should validate");
        for mutation in mutations {
            let mut program = two_application_parameter_program();
            let module = program.groups()[0].module();
            assert!(
                program.corrupt_linked_carrier_for_test(module, mutation),
                "the relational linked fixture should retain {mutation:?}",
            );
            assert_eq!(
                validate_interface_evidence(program)
                    .expect_err("the forged relational linked carrier must fail before Core")
                    .reason(),
                EvidenceValidationReason::UnknownIdentity,
                "{mutation:?}",
            );
        }
    }

    #[test]
    fn rejects_relational_application_relationship_tampering_before_core() {
        #[derive(Clone, Copy, Debug)]
        enum Mutation {
            KeyCarrier,
            DependentCarrier,
            AbstractSelection,
            ImplementationSelection,
            SameShapedHiddenDependent,
        }

        for mutation in [
            Mutation::KeyCarrier,
            Mutation::DependentCarrier,
            Mutation::AbstractSelection,
            Mutation::ImplementationSelection,
            Mutation::SameShapedHiddenDependent,
        ] {
            let mut program = match mutation {
                Mutation::SameShapedHiddenDependent => hidden_relational_application_program(),
                _ => relational_application_program(),
            };
            let module = program.groups()[0].module();
            match mutation {
                Mutation::KeyCarrier => assert!(program.corrupt_linked_carrier_for_test(
                    module,
                    LinkedCarrierMutationForTest::RelationalApplicationKeyMismatch,
                )),
                Mutation::DependentCarrier => assert!(program.corrupt_linked_carrier_for_test(
                    module,
                    LinkedCarrierMutationForTest::RelationalApplicationDependentMismatch,
                )),
                Mutation::AbstractSelection => {
                    let group = &program.groups()[0];
                    let interface = &group.interface_facts()[0];
                    let requirement = group
                        .schemes()
                        .iter()
                        .find(|scheme| scheme.spelling == "relay")
                        .and_then(|scheme| scheme.scheme.requirements.first())
                        .expect("relay should retain its relational requirement");
                    let mut arguments = requirement.arguments().to_vec();
                    arguments[2] = Type::Int;
                    let forged = abstract_selection_for_application(
                        requirement.id,
                        interface,
                        arguments.into_boxed_slice(),
                    );
                    assert!(
                        program.replace_nth_direct_method_occurrence_selection_for_test(
                            module, 0, forged,
                        )
                    );
                }
                Mutation::ImplementationSelection => {
                    let group = &program.groups()[0];
                    let fact = &group.implementation_facts()[0];
                    let mut arguments = fact.arguments().to_vec();
                    arguments[1] = Type::Bool;
                    let forged = implementation_selection_for_application(
                        fact,
                        arguments.into_boxed_slice(),
                    );
                    assert!(
                        program.replace_nth_direct_method_occurrence_selection_for_test(
                            module, 1, forged,
                        )
                    );
                }
                Mutation::SameShapedHiddenDependent => {
                    let group = &program.groups()[0];
                    let interface = &group.interface_facts()[0];
                    let requirement = group
                        .schemes()
                        .iter()
                        .find(|scheme| scheme.spelling == "hidden")
                        .and_then(|scheme| scheme.scheme.requirements.first())
                        .expect("hidden should retain its relational requirement");
                    let hidden = program
                        .registry()
                        .nominals()
                        .iter()
                        .find(|nominal| nominal.spelling == "Hidden")
                        .expect("Hidden should retain its nominal identity");
                    let twin = program
                        .registry()
                        .nominals()
                        .iter()
                        .find(|nominal| nominal.spelling == "HiddenTwin")
                        .expect("HiddenTwin should retain its distinct nominal identity");
                    assert_ne!(hidden.id, twin.id);
                    let mut arguments = requirement.arguments().to_vec();
                    assert_eq!(arguments[2], Type::Nominal(hidden.id));
                    arguments[2] = Type::Nominal(twin.id);
                    let forged = abstract_selection_for_application(
                        requirement.id,
                        interface,
                        arguments.into_boxed_slice(),
                    );
                    assert!(
                        program.replace_nth_direct_method_occurrence_selection_for_test(
                            module, 0, forged,
                        )
                    );
                }
            }

            let expected = match mutation {
                Mutation::KeyCarrier | Mutation::DependentCarrier => {
                    EvidenceValidationReason::UnknownIdentity
                }
                Mutation::AbstractSelection
                | Mutation::ImplementationSelection
                | Mutation::SameShapedHiddenDependent => {
                    EvidenceValidationReason::InvalidEvidenceRoot
                }
            };
            assert_eq!(
                validate_interface_evidence(program)
                    .expect_err("each fresh relational relationship forgery must fail before Core")
                    .reason(),
                expected,
                "{mutation:?}",
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
    fn linked_global_dependent_only_allowance_rejects_coherent_tampering() {
        validate_interface_evidence(dependent_only_global_program())
            .expect("an honest dependent-only global binder must authenticate before Core");

        let mut no_edge = dependent_only_global_program();
        let module = no_edge.groups()[0].module();
        assert!(no_edge.coherently_remove_first_interface_determination_for_test(module));
        assert_eq!(
            validate_interface_evidence(no_edge)
                .expect_err("a no-edge global must not retain a dependent-only binder")
                .reason(),
            EvidenceValidationReason::UnknownIdentity,
        );

        let mut missing_key = dependent_only_global_program();
        let module = missing_key.groups()[0].module();
        assert!(
            missing_key.coherently_make_first_determined_global_key_only_unused_for_test(module)
        );
        assert_eq!(
            validate_interface_evidence(missing_key)
                .expect_err("a determined key-only unused binder must be rejected")
                .reason(),
            EvidenceValidationReason::UnknownIdentity,
        );
    }

    #[test]
    fn linked_global_dependent_only_authentication_has_an_exact_retry_boundary() {
        // Requirement retention (1), determinant-position authentication (1),
        // two argument classifications (2), two atomic variable walks (6),
        // required/dependent exclusion (1), scheme membership (2), and output
        // publication (1).
        const EXACT_WORK: usize = 14;
        let program = dependent_only_global_program();
        let group = &program.groups()[0];
        let scheme = group
            .schemes()
            .iter()
            .find(|scheme| !scheme.scheme.requirements.is_empty())
            .expect("the fixture should retain its constrained global scheme");
        let registry =
            LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                .expect("the linked interface registry should authenticate");
        let span = scheme.origin.primary_span();
        let exercise = |budget: &mut InterfaceConstraintBudget| {
            authenticated_global_dependent_only_binders(
                &program,
                &registry,
                &scheme.scheme,
                budget,
                span,
            )
        };

        let mut one_short = InterfaceConstraintBudget::with_limit(EXACT_WORK - 1);
        assert!(matches!(
            exercise(&mut one_short),
            Err(EvidenceValidationFailure {
                reason: EvidenceValidationReason::ConstraintResourceExhausted,
                ..
            })
        ));
        assert_eq!(one_short.used(), EXACT_WORK - 1);
        for _ in 0..2 {
            let mut exact = InterfaceConstraintBudget::with_limit(EXACT_WORK);
            let allowed = exercise(&mut exact)
                .expect("the exact dependent-only allowance budget should fit")
                .expect("the determined global should use the global-only path");
            assert_eq!(allowed.len(), 1);
            assert_eq!(exact.used(), EXACT_WORK);
        }
    }

    #[test]
    fn linked_generic_prerequisite_decrease_uses_determined_selection_keys() {
        validate_interface_evidence(linked_determined_generic_decrease_program()).expect(
            "linked generic decrease must compare the determined key and retain the complete prerequisite only for groundness",
        );
    }

    #[test]
    fn linked_generic_prerequisite_selection_key_has_an_exact_public_retry_boundary() {
        // Generic decrease owns 2D=2 head-key cells, P=2 complete-prerequisite
        // cells, 2D=2 prerequisite-key cells, and 17 groundness/subterm cells.
        // The complete public validator owns 371 other structural, mirror,
        // kind, method, and publication cells.
        const RELATIONSHIP_WORK: usize = 2 + 2 + 2 + 17;
        const PUBLIC_WORK_OUTSIDE_RELATIONSHIP: usize = 371;
        const EXACT_CONSTRAINT_WORK: usize = PUBLIC_WORK_OUTSIDE_RELATIONSHIP + RELATIONSHIP_WORK;
        const EXACT_TYPE_WORK: usize = 22;

        let relationship_program = linked_determined_generic_decrease_program();
        let group = &relationship_program.groups()[0];
        let interface = &group.interface_facts()[0];
        let fact = &group.implementation_facts()[0];
        let prerequisite = &fact.prerequisites[0];
        let exercise_relationship = |work: &mut InterfaceConstraintBudget| {
            let head_key =
                linked_selection_key_types(interface, fact.arguments(), work, fact.span)?;
            let complete =
                linked_type_references(prerequisite.arguments(), work, prerequisite.span)?;
            let prerequisite_key = linked_selection_key_types(
                interface,
                prerequisite.arguments(),
                work,
                prerequisite.span,
            )?;
            crate::interface::implementation_prerequisite_selection_key_terminates(
                &complete,
                &prerequisite_key,
                &head_key,
                work,
            )
            .map_err(|()| resource(prerequisite.span))
        };
        let mut relationship_short = InterfaceConstraintBudget::with_limit(RELATIONSHIP_WORK - 1);
        assert_eq!(
            exercise_relationship(&mut relationship_short)
                .expect_err("one missing linked relationship cell must reject")
                .reason(),
            EvidenceValidationReason::ConstraintResourceExhausted,
        );
        assert_eq!(relationship_short.used(), RELATIONSHIP_WORK - 1);
        for _ in 0..2 {
            let mut relationship_exact = InterfaceConstraintBudget::with_limit(RELATIONSHIP_WORK);
            assert!(
                exercise_relationship(&mut relationship_exact)
                    .expect("the exact borrowed linked relationship should fit")
            );
            assert_eq!(relationship_exact.used(), RELATIONSHIP_WORK);
            assert_eq!(fact.arguments().len(), 2);
            assert_eq!(prerequisite.arguments().len(), 2);
        }

        let mut constraint_work = InterfaceConstraintBudget::default();
        let mut type_work = TypeWorkBudget::default();
        validate_interface_evidence_with_budget(
            linked_determined_generic_decrease_program(),
            &mut constraint_work,
            &mut type_work,
        )
        .expect("the measured generic decrease program should authenticate");
        assert_eq!(constraint_work.used(), EXACT_CONSTRAINT_WORK);
        assert_eq!(type_work.used(), EXACT_TYPE_WORK);

        let mut constraint_short = InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK - 1);
        let mut exact_type = TypeWorkBudget::with_limit(EXACT_TYPE_WORK);
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
        assert_eq!(constraint_short.used(), EXACT_CONSTRAINT_WORK - 1);
        assert_eq!(exact_type.used(), EXACT_TYPE_WORK);

        let mut exact_constraint = InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK);
        let mut type_short = TypeWorkBudget::with_limit(EXACT_TYPE_WORK - 1);
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
        assert_eq!(exact_constraint.used(), 374);
        assert_eq!(type_short.used(), EXACT_TYPE_WORK - 1);

        for _ in 0..2 {
            let mut exact_constraint = InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK);
            let mut exact_type = TypeWorkBudget::with_limit(EXACT_TYPE_WORK);
            validate_interface_evidence_with_budget(
                linked_determined_generic_decrease_program(),
                &mut exact_constraint,
                &mut exact_type,
            )
            .expect("the exact linked relationship boundary should remain retryable");
            assert_eq!(exact_constraint.used(), EXACT_CONSTRAINT_WORK);
            assert_eq!(exact_type.used(), EXACT_TYPE_WORK);
        }
    }

    #[test]
    fn linked_generic_prerequisite_rejects_dependent_only_strictness_after_coherent_tampering() {
        let mut program = entry_program(concat!(
            "type List<A> =\n",
            "Nil\n",
            "| Cons(A, List<A>)\n",
            "interface Relation<A, B> where A -> B {\n",
            "relate : A -> Int\n",
            "}\n",
            "impl<X> Relation<List<X>, List<X>> where Relation<X, X> {\n",
            "relate value = 0\n",
            "}\n",
            "main : Unit -> Unit\n",
            "main () = ()\n",
        ));
        let implementation = program.groups()[0].implementation_facts()[0].id;
        assert!(
            program.replace_implementation_prerequisite_argument_with_head_for_test(
                implementation,
                0,
                0,
            ),
            "the linked fixture should retain every prerequisite mirror",
        );
        let fact = &program.groups()[0].implementation_facts()[0];
        let prerequisite = &fact.prerequisites[0];
        assert_eq!(prerequisite.arguments()[0], fact.arguments()[0]);
        assert_ne!(prerequisite.arguments()[1], fact.arguments()[1]);

        assert_eq!(
            validate_interface_evidence(program)
                .expect_err("dependent-only strictness cannot authenticate generic decrease")
                .reason(),
            EvidenceValidationReason::UnknownIdentity,
        );
    }

    #[test]
    fn rejects_every_source_token_and_fact_determination_mutation_before_core() {
        const SOURCE: &str = concat!(
            "interface Relation<A, B, C> where (A, B) -> C {\n",
            "relation : (A, B, C) -> Unit\n",
            "}\n\n",
            "interface Other<X, Y, Z> where Y -> (X, Z) {\n",
            "other : (X, Y, Z) -> Unit\n",
            "}\n\n",
            "interface Ordinary<L, R, V> {\n",
            "ordinary : (L, R, V) -> Unit\n",
            "}\n\n",
            "main : Unit -> Unit\n",
            "main () = ()\n",
        );
        let mutations = [
            (
                LinkedDeterminationCarrierForTest::Source,
                LinkedDeterminationMutationForTest::Missing,
            ),
            (
                LinkedDeterminationCarrierForTest::Source,
                LinkedDeterminationMutationForTest::Extra,
            ),
            (
                LinkedDeterminationCarrierForTest::Source,
                LinkedDeterminationMutationForTest::Duplicate,
            ),
            (
                LinkedDeterminationCarrierForTest::Source,
                LinkedDeterminationMutationForTest::Reordered,
            ),
            (
                LinkedDeterminationCarrierForTest::Source,
                LinkedDeterminationMutationForTest::OutOfRange,
            ),
            (
                LinkedDeterminationCarrierForTest::Source,
                LinkedDeterminationMutationForTest::WrongInterface,
            ),
            (
                LinkedDeterminationCarrierForTest::Source,
                LinkedDeterminationMutationForTest::MismatchedPositions,
            ),
            (
                LinkedDeterminationCarrierForTest::Source,
                LinkedDeterminationMutationForTest::WrongSourceSpelling,
            ),
            (
                LinkedDeterminationCarrierForTest::Source,
                LinkedDeterminationMutationForTest::WrongSourceOrigin,
            ),
            (
                LinkedDeterminationCarrierForTest::Token,
                LinkedDeterminationMutationForTest::Missing,
            ),
            (
                LinkedDeterminationCarrierForTest::Token,
                LinkedDeterminationMutationForTest::Extra,
            ),
            (
                LinkedDeterminationCarrierForTest::Token,
                LinkedDeterminationMutationForTest::Duplicate,
            ),
            (
                LinkedDeterminationCarrierForTest::Token,
                LinkedDeterminationMutationForTest::Reordered,
            ),
            (
                LinkedDeterminationCarrierForTest::Token,
                LinkedDeterminationMutationForTest::OutOfRange,
            ),
            (
                LinkedDeterminationCarrierForTest::Token,
                LinkedDeterminationMutationForTest::MismatchedPositions,
            ),
            (
                LinkedDeterminationCarrierForTest::Fact,
                LinkedDeterminationMutationForTest::Missing,
            ),
            (
                LinkedDeterminationCarrierForTest::Fact,
                LinkedDeterminationMutationForTest::Extra,
            ),
            (
                LinkedDeterminationCarrierForTest::Fact,
                LinkedDeterminationMutationForTest::Duplicate,
            ),
            (
                LinkedDeterminationCarrierForTest::Fact,
                LinkedDeterminationMutationForTest::Reordered,
            ),
            (
                LinkedDeterminationCarrierForTest::Fact,
                LinkedDeterminationMutationForTest::OutOfRange,
            ),
            (
                LinkedDeterminationCarrierForTest::Fact,
                LinkedDeterminationMutationForTest::MismatchedPositions,
            ),
        ];

        validate_interface_evidence(entry_program(SOURCE))
            .expect("the honest three-interface fixture should authenticate");
        let mut unexpectedly_accepted = Vec::new();
        for (carrier, mutation) in mutations {
            let mut program = entry_program(SOURCE);
            let module = program.groups()[0].module();
            assert!(
                program.corrupt_linked_determination_for_test(module, carrier, mutation),
                "the fixture should retain {carrier:?} {mutation:?}",
            );
            match validate_interface_evidence(program) {
                Err(failure) => assert_eq!(
                    failure.reason(),
                    EvidenceValidationReason::UnknownIdentity,
                    "{carrier:?} {mutation:?}",
                ),
                Ok(_) => unexpectedly_accepted.push((carrier, mutation)),
            }
        }
        assert!(
            unexpectedly_accepted.is_empty(),
            "linked validation accepted {unexpectedly_accepted:?}",
        );
    }

    #[test]
    fn linked_determination_authentication_has_an_exact_public_retry_boundary() {
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
            validate_interface_evidence_with_budget(
                program(determined),
                &mut constraint_work,
                &mut type_work,
            )
            .expect("the measured linked program should authenticate");
            (constraint_work.used(), type_work.used())
        };

        const ORDINARY_CONSTRAINT_WORK: usize = 149;
        const DETERMINED_CONSTRAINT_WORK: usize = 165;
        const EXACT_TYPE_WORK: usize = 16;
        const PARAMETER_COUNT: usize = 3;
        const DETERMINANT_COUNT: usize = 2;
        const THREE_WAY_AUTH_DELTA: usize = 2 * PARAMETER_COUNT + 2 * DETERMINANT_COUNT;
        const SEED_RETENTION_DELTA: usize = DETERMINANT_COUNT;
        const METHOD_SEED_DELTA: usize = 2 * DETERMINANT_COUNT;
        const TOTAL_KEY_DELTA: usize =
            THREE_WAY_AUTH_DELTA + SEED_RETENTION_DELTA + METHOD_SEED_DELTA;

        let ordinary = measure(false);
        let determined = measure(true);
        assert_eq!(ordinary, (ORDINARY_CONSTRAINT_WORK, EXACT_TYPE_WORK));
        assert_eq!(determined, (DETERMINED_CONSTRAINT_WORK, EXACT_TYPE_WORK),);
        assert_eq!(
            DETERMINED_CONSTRAINT_WORK - ORDINARY_CONSTRAINT_WORK,
            TOTAL_KEY_DELTA,
        );

        let mut short = InterfaceConstraintBudget::with_limit(DETERMINED_CONSTRAINT_WORK - 1);
        let failure = validate_interface_evidence_with_budget(
            program(true),
            &mut short,
            &mut TypeWorkBudget::with_limit(EXACT_TYPE_WORK),
        )
        .expect_err("one-short linked key work must not publish a capability");
        assert_eq!(
            failure.reason(),
            EvidenceValidationReason::ConstraintResourceExhausted,
        );
        assert_eq!(short.used(), DETERMINED_CONSTRAINT_WORK - 1);

        for _ in 0..2 {
            let mut exact = InterfaceConstraintBudget::with_limit(DETERMINED_CONSTRAINT_WORK);
            let mut exact_type = TypeWorkBudget::with_limit(EXACT_TYPE_WORK);
            validate_interface_evidence_with_budget(program(true), &mut exact, &mut exact_type)
                .expect("the exact linked key boundary should remain retryable");
            assert_eq!(exact.used(), DETERMINED_CONSTRAINT_WORK);
            assert_eq!(exact_type.used(), EXACT_TYPE_WORK);
        }
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
            &fact.arguments()[0],
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
    fn rejects_non_predecessor_resolved_source_carriers_without_panicking() {
        for mutation in [
            LinkedCarrierMutationForTest::InterfaceSourceParametersEmpty,
            LinkedCarrierMutationForTest::InterfaceSourceParametersExtra,
            LinkedCarrierMutationForTest::InterfaceSourceDetermination,
            LinkedCarrierMutationForTest::ImplementationSourceArgumentsEmpty,
            LinkedCarrierMutationForTest::ImplementationSourceArgumentsExtra,
            LinkedCarrierMutationForTest::ImplementationSourceWideLatePrerequisiteArgumentsExtra,
        ] {
            let (mut program, base) = linked_higher_kinded_diamond_program();
            assert!(
                program.corrupt_linked_carrier_for_test(base, mutation),
                "the linked fixture should support {mutation:?}",
            );
            let observed = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                validate_interface_evidence(program)
            }));
            let failure = match observed {
                Ok(Err(failure)) => failure,
                Ok(Ok(_)) => panic!("linked validation accepted {mutation:?}"),
                Err(_) => panic!("linked validation panicked for {mutation:?}"),
            };
            assert_eq!(
                failure.reason(),
                EvidenceValidationReason::UnknownIdentity,
                "{mutation:?}",
            );
        }
    }

    #[test]
    fn wide_mismatched_source_prerequisites_do_not_bypass_the_linked_budget() {
        let (mut program, base) = linked_higher_kinded_diamond_program();
        let registry =
            LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                .expect("the canonical linked registry should authenticate");
        assert!(program.corrupt_linked_carrier_for_test(
            base,
            LinkedCarrierMutationForTest::ImplementationSourceWideLatePrerequisiteArgumentsExtra,
        ));
        let group = program
            .groups()
            .iter()
            .find(|group| group.module() == base)
            .expect("the fixture should retain its defining group");
        let implementation_index = group
            .implementation_facts()
            .iter()
            .position(|fact| {
                fact.head_parameters
                    .first()
                    .is_some_and(|parameter| matches!(parameter.kind, Kind::Arrow(_, _)))
                    && !fact.prerequisites.is_empty()
            })
            .expect("the fixture should retain its prerequisite implementation");
        let fact = &group.implementation_facts()[implementation_index];
        let source = group.implementations()[implementation_index].source();
        assert_eq!(source.prerequisites.len(), 32);
        assert_eq!(
            source
                .prerequisites
                .last()
                .unwrap()
                .application
                .arguments
                .len(),
            2
        );
        let initial_fact_work = fact
            .head_parameters
            .len()
            .saturating_add(fact.prerequisites.len())
            .saturating_add(fact.methods.len())
            .saturating_add(1);
        let mut type_work = TypeWorkBudget::default();
        let mut kind_environments = build_linked_kind_environments(
            program.registry(),
            &mut type_work,
            program.result().span,
        )
        .expect("the linked kind environments should fit");
        let mut exact_initial = InterfaceConstraintBudget::with_limit(initial_fact_work);
        let failure = validate_implementation_consistency(
            &program,
            &registry,
            &group.implementations()[implementation_index],
            &group.checked_implementations()[implementation_index],
            fact,
            &mut kind_environments,
            &mut exact_initial,
            &mut type_work,
        )
        .expect_err("source prerequisite width must not be scanned outside the budget");

        assert_eq!(
            failure.reason(),
            EvidenceValidationReason::ConstraintResourceExhausted
        );
        assert_eq!(exact_initial.used(), initial_fact_work);
    }

    #[test]
    fn late_relational_source_requirement_has_an_exact_matching_boundary() {
        const WIDTH: usize = 32;
        // The final deliberately over-wide source row reaches its arity check
        // only after both retained positional application visits.
        const EXACT_WORK: usize = 6 * WIDTH - 3;

        fn rows(
            module: ModuleId,
            span: Span,
        ) -> (
            Vec<CheckedRequirement>,
            Vec<crate::resolved::ResolvedRequirement>,
        ) {
            let interface = InterfaceId::new(module, 0);
            let owner = RequirementOwner::Global(BinderId::resolved(module, 0));
            let resolved_type = || crate::resolved::ResolvedType {
                ty: Type::Int,
                provenance: crate::resolved::ResolvedTypeProvenance::new(
                    vec![crate::resolved::ResolvedTypeProvenanceNode::Fact(span)],
                    0,
                ),
                origin: Origin::Source(span),
                span,
            };
            let mut checked = Vec::new();
            let mut source = Vec::new();
            for index in 0..WIDTH {
                let id = RequirementId::new(
                    owner,
                    u32::try_from(index).expect("the fixture width should fit"),
                );
                checked.push(CheckedRequirement {
                    id,
                    application: InterfaceApplication::new(interface, Box::new([Type::Int])),
                    origin: Origin::Source(span),
                    span,
                });
                let mut arguments = vec![resolved_type()];
                if index + 1 == WIDTH {
                    arguments.push(resolved_type());
                }
                source.push(crate::resolved::ResolvedRequirement {
                    id,
                    application: crate::resolved::ResolvedInterfaceApplication {
                        interface: crate::resolved::ResolvedInterfaceOccurrence {
                            id: interface,
                            spelling: "Relation".to_owned(),
                            origin: Origin::Source(span),
                        },
                        arguments: arguments.into_boxed_slice(),
                        span,
                    },
                });
            }
            (checked, source)
        }

        let (program, module) = linked_higher_kinded_diamond_program();
        let span = program.result().span;
        let (short_checked, short_source) = rows(module, span);
        let mut short = InterfaceConstraintBudget::with_limit(EXACT_WORK - 1);
        assert_eq!(
            requirements_match(
                &short_checked,
                &short_source,
                &[],
                &program,
                &mut short,
                span,
            )
            .expect_err("one missing row unit should exhaust linked requirement matching")
            .reason(),
            EvidenceValidationReason::ConstraintResourceExhausted,
        );
        assert_eq!(short.used(), EXACT_WORK - 1);

        let (exact_checked, exact_source) = rows(module, span);
        let mut exact = InterfaceConstraintBudget::with_limit(EXACT_WORK);
        assert!(
            !requirements_match(
                &exact_checked,
                &exact_source,
                &[],
                &program,
                &mut exact,
                span,
            )
            .expect("the exact budget should reach the late relational row")
        );
        assert_eq!(exact.used(), EXACT_WORK);
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
    fn rejects_surplus_canonical_variable_at_linked_owner_boundary() {
        let mut program = polymorphic_method_program();
        let module = program.groups()[0].module();
        assert!(program.add_surplus_registry_type_variable_for_test(module));

        assert_eq!(
            validate_interface_evidence(program)
                .expect_err("an unowned canonical binder must publish no capability")
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
            let parameter = group.interface_facts()[0].parameters[0].id;
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
            &fact.arguments()[0],
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
        let application = InterfaceApplication::new(fact.interface(), Box::new([goal.clone()]));
        assert_eq!(
            validate_checked_selection_in_scope(
                &program,
                &registry,
                group,
                &selection,
                &application,
                EvidenceScope {
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
            &fact.arguments()[0],
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
        let owner = generic.arguments()[0]
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
        const EXACT_WORK: usize = 74;
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
        let owner = generic.arguments()[0]
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
        let group = &program.groups()[0];
        let fact = &group.implementation_facts()[0];
        let [first, second] = fact.head_parameters.as_ref() else {
            panic!("the fixture should retain two head parameters");
        };
        let goal = Type::Tuple(vec![Type::Int, Type::Bool].into_boxed_slice());
        let reordered = match_implementation_head_structurally(
            [second.id, first.id].into_iter(),
            &fact.arguments()[0],
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
        let group = &program.groups()[0];
        let left = &group.implementation_facts()[0];
        let right = &group.implementation_facts()[1];
        let generic = &group.implementation_facts()[2];
        let owner = generic.arguments()[0]
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
        let group = &program.groups()[0];
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
            selected_requirement.arguments()[0].clone(),
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
        let group = &program.groups()[0];
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
            requirement.arguments()[0].clone(),
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
        let outer_nominal = outer.arguments()[0]
            .outer_nominal()
            .expect("the enclosing implementation should retain a nominal head");
        let nested = finish_width_one(
            nested_builder,
            nested_root,
            outer.interface(),
            Type::apply_arguments(
                Type::Nominal(outer_nominal),
                [requirement.arguments()[0].clone()],
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
            implementation_requirement.arguments()[0].clone(),
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
        let group = &program.groups()[0];
        let shadowed = &group.schemes()[0];
        let [requirement] = shadowed.scheme.requirements.as_ref() else {
            panic!("the constrained global should retain one abstract requirement");
        };
        let variables = [shadowed.scheme.type_parameters[0].0];
        let scope = EvidenceScope {
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
        const EXACT_WORK: usize = 87 + 15 + 4 + 1 + 1;
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
            current.arguments()[0].clone(),
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
        let group = &program.groups()[0];
        let ground = &group.implementation_facts()[0];
        let generic = &group.implementation_facts()[1];
        let owner = generic.arguments()[0]
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
            .find(|implementation| implementation.arguments() == [Type::Bool])
            .expect("the fixture should retain its Bool implementation");
        let methods = bool_implementation
            .methods
            .iter()
            .map(|method| method.id)
            .collect::<Vec<_>>();
        let forged = implementation_selection_for_argument(
            bool_implementation.id,
            bool_implementation.interface(),
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
            keep.interface(),
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
        // The later body-free value-scheme pass owns the fact/method indexed
        // defense, so this build does not repeat those two traversal cells.
        const PREDECESSOR_RELATION_WORK: usize = 92;
        // The one retained implementation head is additionally authenticated
        // against canonical IOTA: two total-synthesis cells for `Int` and
        // one `Type`/`Type` Kind comparison cell.
        const IMPLEMENTATION_HEAD_KIND_WORK: usize = 3;
        // The retained `(A, A) -> Bool` interface method authenticates its
        // free-variable closure and outer Function shape in the same Kind/type
        // walk that validates the linked value, so it has no standalone
        // constraint traversal. Complete checked implementation applications
        // add two retained positional carrier cells here.
        // Six newly iterative Source-Origin cells displace five cells from the
        // removed standalone checked/source value-type equality walk.
        const FUSED_CARRIER_NET_WORK: usize = 6 - 5 + 2;
        // The checked implementation token independently authenticates its
        // complete unary head against the checked fact: one retained pair and
        // one atomic Type comparison cell.
        const CHECKED_TOKEN_APPLICATION_WORK: usize = 2;
        let program = local_program();
        let mut measured = InterfaceConstraintBudget::default();
        drop(
            LinkedInterfaceRegistry::build(&program, &mut measured)
                .expect("the linked registry should fit the default budget"),
        );
        let limit = measured.used();
        assert_eq!(
            limit,
            PREDECESSOR_RELATION_WORK
                + IMPLEMENTATION_HEAD_KIND_WORK
                + FUSED_CARRIER_NET_WORK
                + CHECKED_TOKEN_APPLICATION_WORK,
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
        // implementation inventory cells. Its interface binder contributes
        // one uniqueness cell. The method binder's canonical record is retained
        // here, while its owner/mirror visit is fused into the consuming linked
        // method-index pass. TypeWork
        // owns each binder's retained record, Type Kind, and canonical-variable
        // staging cell.
        const CONSTRAINT_WORK: usize = 7 + 6 + 1;
        const TYPE_WORK: usize = 2 * 3;
        let fixture = ValidationFixture::create(concat!(
            "interface Equal<A> {\nequal<B> : (A, B) -> Bool\n}\n\n",
            "impl Equal<Int> {\nequal (left, ignored) = left == left\n}\n\n",
            "main : Unit -> Bool\nmain () = equal((1, true))\n",
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
        assert_eq!(
            constraint_short.used(),
            CONSTRAINT_WORK - 2,
            "the final two-cell combined precharge is atomic",
        );
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
        let mut program = generic_program();
        let module = program.groups()[0].module();
        let closed = Type::function_computation(
            Type::Unit,
            crate::types::ComputationType::new(
                Type::Bool,
                crate::types::EffectRow::singleton(crate::types::EffectInstance::new(
                    crate::types::EffectId::new(module, 0),
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
        let group = &program.groups()[0];
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

        let registry =
            LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                .expect("the source-free registry should build");
        for headers_only in [false, true] {
            for limit in [7, 8, 8] {
                let mut budget = InterfaceConstraintBudget::with_limit(limit);
                let mut types = TypeWorkBudget::with_limit(0);
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
                    headers_only.then_some((&program, &registry, &[], &mut types)),
                );
                if limit == 7 {
                    assert_eq!(
                        result
                            .expect_err("one-short source-free scheduling rejects")
                            .reason(),
                        EvidenceValidationReason::ConstraintResourceExhausted
                    );
                    assert!(pending.is_empty());
                } else {
                    result.expect("the lexical scheduler preserves the predecessor's exact cost");
                    assert_eq!(budget.used(), 8);
                    assert_eq!(pending.len(), 4);
                }
                assert!(heads.is_empty());
                assert!(sources.is_empty());
                assert!(scopes.is_empty());
                assert_eq!(types.used(), 0);
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
