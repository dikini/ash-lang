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
    module::ModuleId,
    resolved::{
        BinderId, CheckedImplementationFact, CheckedInterfaceFact, ImplementationRoute,
        ResolvedBlock, ResolvedDeclarationIndex, ResolvedDefinitionKind, ResolvedExpr,
        ResolvedExprKind, ResolvedLocalDeclaration, ResolvedModuleGroup, ResolvedModuleProgram,
        ResolvedOccurrence, ResolvedRegistry, ResolvedTermName,
    },
    source::{Origin, Span},
    types::{NominalTypeId, Type, TypeVariableId, discard_type_iteratively},
};

/// Stable reason owned by pre-Core interface-evidence validation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EvidenceValidationReason {
    /// A linked checked identity is absent, duplicated, or owned by another declaration.
    UnknownIdentity,
    /// A selected implementation is not in the occurrence module's direct environment.
    UnavailableImplementation,
    /// An occurrence selection does not authenticate its checked interface obligation.
    InvalidEvidenceRoot,
    /// The persistent graph-wide interface and constraint budget was exhausted.
    ConstraintResourceExhausted,
}

impl fmt::Display for EvidenceValidationReason {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::UnknownIdentity => "evidence.validation.unknown-identity",
            Self::UnavailableImplementation => "evidence.validation.unavailable-implementation",
            Self::InvalidEvidenceRoot => "evidence.validation.invalid-root",
            Self::ConstraintResourceExhausted => "internal.resource.constraint-work",
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

/// Owned identity locations into the checked facts retained by module groups.
#[derive(Debug)]
struct LinkedInterfaceRegistry {
    modules: HashMap<ModuleId, usize>,
    interfaces: HashMap<InterfaceId, FactLocation>,
    methods: HashMap<MethodId, MethodLocation>,
    implementations: HashMap<ImplId, FactLocation>,
    implementation_methods: HashMap<ImplMethodId, ImplementationMethodLocation>,
    schemes: HashMap<BinderId, SchemeLocation>,
    binders: HashMap<BinderId, ()>,
}

impl LinkedInterfaceRegistry {
    fn build(
        program: &ResolvedModuleProgram,
        budget: &mut InterfaceConstraintBudget,
    ) -> Result<Self, EvidenceValidationFailure> {
        let mut registry = Self {
            modules: HashMap::new(),
            interfaces: HashMap::new(),
            methods: HashMap::new(),
            implementations: HashMap::new(),
            implementation_methods: HashMap::new(),
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
        }
        registry.validate_references(program, budget)?;
        Ok(registry)
    }

    fn validate_references(
        &self,
        program: &ResolvedModuleProgram,
        budget: &mut InterfaceConstraintBudget,
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
            validate_group_consistency(program, self, group, budget)?;
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
                validate_requirements(
                    &scheme.scheme,
                    RequirementOwner::Global(scheme.binder),
                    &scheme.scheme.type_parameters,
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
                validate_linked_type(
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
            for available_index in 0..group.available_implementations().len() {
                charge(budget, 1, group.span())?;
                let available = group
                    .available_implementations()
                    .get(available_index)
                    .ok_or_else(|| unknown(group.span()))?;
                let Some(location) = self.implementations.get(&available.id()).copied() else {
                    return Err(unknown(group.span()));
                };
                let defining_group = program
                    .groups()
                    .get(location.group)
                    .ok_or_else(|| unknown(group.span()))?;
                let defining_module = defining_group.module();
                match available.route() {
                    ImplementationRoute::Local if defining_module == group.module() => {}
                    ImplementationRoute::DirectImport {
                        direct_dependency,
                        available_at,
                    } => {
                        charge(budget, 1, group.span())?;
                        let published = defining_group
                            .implementations()
                            .get(location.fact)
                            .is_some_and(|body| {
                                body.id() == available.id() && body.source().public
                            });
                        if defining_module != direct_dependency
                            || available.id().module() != direct_dependency
                            || !self.modules.contains_key(&direct_dependency)
                            || !published
                            || !has_direct_dependency(
                                group,
                                direct_dependency,
                                available_at,
                                budget,
                            )?
                        {
                            return Err(unknown(group.span()));
                        }
                    }
                    ImplementationRoute::Local => return Err(unknown(group.span())),
                }
            }
        }
        Ok(())
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

fn validate_group_consistency(
    program: &ResolvedModuleProgram,
    registry: &LinkedInterfaceRegistry,
    group: &ResolvedModuleGroup,
    budget: &mut InterfaceConstraintBudget,
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
            || fact.parameter != source.parameter
            || fact.origin != source.origin
            || fact.span != source.span
            || fact.methods.len() != source.methods.len()
            || program
                .registry()
                .type_variable(fact.parameter.id)
                .is_none_or(|parameter| parameter != &fact.parameter)
        {
            return Err(unknown(source.span));
        }
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
                || method.origin != source_method.origin
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
            validate_linked_type(
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
        validate_global_scheme(program, definition, checked, budget)?;
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
        validate_implementation_consistency(program, registry, body, token, fact, budget)?;
    }
    Ok(())
}

fn validate_global_scheme(
    program: &ResolvedModuleProgram,
    definition: &crate::resolved::CheckedDefinition,
    checked: &crate::resolved::CheckedGlobalScheme,
    budget: &mut InterfaceConstraintBudget,
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
    if checked.binder != name.id
        || checked.spelling != name.spelling
        || checked.origin != name.origin
        || !checked
            .scheme
            .type_parameters
            .iter()
            .copied()
            .eq(parameters.iter().map(|parameter| parameter.id))
        || !requirements_match(
            &checked.scheme.requirements,
            requirements,
            &checked.scheme.type_parameters,
            program,
            budget,
            span,
        )?
    {
        return Err(unknown(span));
    }
    validate_linked_type(
        &checked.scheme.value_type,
        program.registry(),
        &checked.scheme.type_parameters,
        budget,
        span,
    )?;
    let value_matches = match definition.kind() {
        ResolvedDefinitionKind::Equational(global) => same_type_charged(
            &checked.scheme.value_type,
            &global.interface.annotation.ty,
            budget,
            span,
        )?,
        ResolvedDefinitionKind::InlineOperational(global) => {
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
        validate_linked_type(
            &checked.argument,
            program.registry(),
            variables,
            budget,
            checked.span,
        )?;
        if checked.id != source.id
            || checked.interface != source.interface.id
            || checked.origin != Origin::Source(source.span)
            || checked.span != source.span
            || !same_type_charged(&checked.argument, &source.argument.ty, budget, source.span)?
        {
            return Ok(false);
        }
    }
    Ok(true)
}

fn validate_implementation_consistency(
    program: &ResolvedModuleProgram,
    registry: &LinkedInterfaceRegistry,
    body: &crate::resolved::CheckedImplementationBody,
    token: &crate::interface::CheckedImplementation,
    fact: &CheckedImplementationFact,
    budget: &mut InterfaceConstraintBudget,
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
        || fact.head_parameters.as_ref() != source.head_parameters.as_ref()
        || fact.origin != Origin::Source(source.span)
        || fact.span != source.span
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
    validate_linked_type(&fact.argument, program.registry(), &variables, budget, span)?;
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
        if method.id != checked.id
            || method.method != checked.method
            || method.binder != checked.binder
            || checked.method != interface_method.id
            || group.method != Some(method.method)
            || group.identity != Some(method.id)
            || group.binder.id != method.binder
            || method.span != group.span
            || method.scheme.type_parameters.as_ref() != variables.as_slice()
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
        validate_linked_type(
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

fn validate_linked_type(
    ty: &Type,
    registry: &ResolvedRegistry,
    variables: &[TypeVariableId],
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<(), EvidenceValidationFailure> {
    match validate_type(ty, registry, variables, budget, span) {
        Ok(()) => Ok(()),
        Err(failure)
            if failure.reason() == EvidenceValidationReason::ConstraintResourceExhausted =>
        {
            Err(failure)
        }
        Err(_) => Err(unknown(span)),
    }
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
            (Type::AppliedNominal(left_id, left), Type::AppliedNominal(right_id, right))
                if left_id == right_id && left.len() == right.len() =>
            {
                reserve_type_pairs(&mut pending, left.len(), budget, span)?;
                pending.extend(left.iter().zip(right).rev());
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
/// direct implementation route, or occurrence evidence root is malformed.
pub fn validate_interface_evidence(
    program: ResolvedModuleProgram,
) -> Result<ValidatedInterfaceProgram, EvidenceValidationFailure> {
    validate_interface_evidence_with_budget(program, &mut InterfaceConstraintBudget::default())
}

pub(crate) fn validate_interface_evidence_with_budget(
    program: ResolvedModuleProgram,
    budget: &mut InterfaceConstraintBudget,
) -> Result<ValidatedInterfaceProgram, EvidenceValidationFailure> {
    let linked_interfaces = LinkedInterfaceRegistry::build(&program, budget)?;
    validate_occurrences(&program, &linked_interfaces, budget)?;
    Ok(ValidatedInterfaceProgram { source: program })
}

fn validate_occurrences(
    program: &ResolvedModuleProgram,
    registry: &LinkedInterfaceRegistry,
    budget: &mut InterfaceConstraintBudget,
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
                    validate_definition(program, registry, group, definition, budget)?;
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
                    validate_implementation(program, registry, group, implementation, budget)?;
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
        budget,
    )
}

fn validate_definition(
    program: &ResolvedModuleProgram,
    registry: &LinkedInterfaceRegistry,
    group: &ResolvedModuleGroup,
    definition: &crate::resolved::CheckedDefinition,
    budget: &mut InterfaceConstraintBudget,
) -> Result<(), EvidenceValidationFailure> {
    let binder = match definition.kind() {
        ResolvedDefinitionKind::Equational(global) => global.interface.name.id,
        ResolvedDefinitionKind::InlineOperational(global) => global.header.name.id,
    };
    let scheme = registry
        .scheme(program, binder)
        .ok_or_else(|| unknown(definition.span()))?;
    let scope = EvidenceScope {
        owner: Some(RequirementOwner::Global(binder)),
        variables: &scheme.type_parameters,
    };
    match definition.kind() {
        ResolvedDefinitionKind::Equational(global) => {
            for equation_index in 0..global.equations.len() {
                charge(budget, 1, definition.span())?;
                let equation = global
                    .equations
                    .get(equation_index)
                    .ok_or_else(|| unknown(definition.span()))?;
                validate_expression(program, registry, group, scope, &equation.body, budget)?;
            }
        }
        ResolvedDefinitionKind::InlineOperational(global) => {
            let mut pending = Vec::new();
            schedule_block(&mut pending, &global.body, budget)?;
            validate_pending_expressions(program, registry, group, scope, &mut pending, budget)?;
        }
    }
    Ok(())
}

fn validate_implementation(
    program: &ResolvedModuleProgram,
    registry: &LinkedInterfaceRegistry,
    group: &ResolvedModuleGroup,
    implementation: &crate::resolved::CheckedImplementationBody,
    budget: &mut InterfaceConstraintBudget,
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
            validate_expression(program, registry, group, scope, &equation.body, budget)?;
        }
    }
    Ok(())
}

fn validate_expression(
    program: &ResolvedModuleProgram,
    registry: &LinkedInterfaceRegistry,
    group: &ResolvedModuleGroup,
    scope: EvidenceScope<'_>,
    root: &ResolvedExpr,
    budget: &mut InterfaceConstraintBudget,
) -> Result<(), EvidenceValidationFailure> {
    let mut pending = Vec::new();
    reserve_expressions(&mut pending, 1, budget, root.span)?;
    pending.push(root);
    validate_pending_expressions(program, registry, group, scope, &mut pending, budget)
}

fn validate_pending_expressions(
    program: &ResolvedModuleProgram,
    registry: &LinkedInterfaceRegistry,
    group: &ResolvedModuleGroup,
    scope: EvidenceScope<'_>,
    pending: &mut Vec<&ResolvedExpr>,
    budget: &mut InterfaceConstraintBudget,
) -> Result<(), EvidenceValidationFailure> {
    while let Some(expression) = pending.pop() {
        charge(budget, 1, expression.span)?;
        match &expression.kind {
            ResolvedExprKind::Occurrence(occurrence) => {
                validate_occurrence(program, registry, group, scope, occurrence, budget)?;
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

fn validate_occurrence(
    program: &ResolvedModuleProgram,
    registry: &LinkedInterfaceRegistry,
    group: &ResolvedModuleGroup,
    scope: EvidenceScope<'_>,
    occurrence: &ResolvedOccurrence,
    budget: &mut InterfaceConstraintBudget,
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
                    budget,
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
                budget,
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
    validate_checked_selection_in_scope(
        program,
        registry,
        group,
        selection,
        expected_interface,
        selection.argument(),
        scope,
        budget,
        span,
    )
}

#[allow(clippy::too_many_arguments)]
fn validate_checked_selection_in_scope(
    program: &ResolvedModuleProgram,
    registry: &LinkedInterfaceRegistry,
    group: &ResolvedModuleGroup,
    selection: &EvidenceSelection,
    expected_interface: InterfaceId,
    expected_argument: &Type,
    scope: EvidenceScope<'_>,
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<(), EvidenceValidationFailure> {
    charge(budget, 2, span)?;
    validate_type(
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
        &mut visited,
        &mut pending,
        budget,
        span,
    )?;
    while let Some(goal) = pending.0.pop() {
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
            if !implementation_is_available(group, implementation, budget, span)? {
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
                pending.0.push(PendingGoal::new(
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
    validate_type(&fact.argument, registry, scope_variables, budget, span)?;
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

fn reserve_pending_goals(
    pending: &mut PendingGoals,
    additional: usize,
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<(), EvidenceValidationFailure> {
    charge(budget, additional, span)?;
    pending
        .0
        .try_reserve(additional)
        .map_err(|_| resource(span))
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
    validate_type(&fact.argument, registry, &head_variables, budget, span)?;
    for (parameter, binding) in fact.head_parameters.iter().zip(substitution) {
        charge(budget, 1, span)?;
        validate_type(binding.argument(), registry, goal_variables, budget, span)?;
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
            (Type::AppliedNominal(left_id, left), Type::AppliedNominal(right_id, right))
                if left_id == right_id && left.len() == right.len() =>
            {
                reserve_type_pairs(&mut pending, left.len(), budget, span)?;
                pending.extend(left.iter().zip(right).rev());
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

fn validate_type(
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
                    Type::Nominal(id)
                        if registry
                            .nominal_parameters(*id)
                            .is_some_and(<[_]>::is_empty) => {}
                    Type::Nominal(_) | Type::Inference(_) | Type::Forall(_, _) => {
                        return Err(invalid_root(span));
                    }
                    Type::Variable(variable) if unique.contains(variable) => {}
                    Type::Variable(_) => return Err(invalid_root(span)),
                    Type::AppliedNominal(id, arguments) => {
                        if registry
                            .nominal_parameters(*id)
                            .is_none_or(|parameters| parameters.len() != arguments.len())
                        {
                            return Err(invalid_root(span));
                        }
                        charge(budget, 1, span)?;
                        pending.try_reserve(1).map_err(|_| resource(span))?;
                        pending.push(Task::Sequence(arguments.iter()));
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
            (Type::AppliedNominal(left_id, left), Type::AppliedNominal(right_id, right))
                if left_id == right_id && left.len() == right.len() =>
            {
                reserve_type_pairs(&mut pending, left.len(), budget, span)?;
                pending.extend(left.iter().zip(right).rev());
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
        FinishApplied(NominalTypeId, usize),
        FinishFunction,
    }

    let mut work = Vec::new();
    charge(budget, 1, span)?;
    work.try_reserve(1).map_err(|_| resource(span))?;
    work.push(Task::Visit(root, true));
    let mut rebuilt = TypeBuffer(Vec::new());
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
            Task::Visit(Type::AppliedNominal(id, arguments), substitute) => {
                charge(budget, 2, span)?;
                work.try_reserve(2).map_err(|_| resource(span))?;
                work.push(Task::FinishApplied(*id, arguments.len()));
                work.push(Task::Sequence(arguments.iter(), substitute));
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
                if count > rebuilt.0.len() {
                    return Err(invalid_root(span));
                }
                reserve_rebuilt_type(&mut rebuilt, budget, span)?;
                let values = rebuilt.0.split_off(rebuilt.0.len() - count);
                rebuilt.0.push(Type::Tuple(values.into_boxed_slice()));
            }
            Task::FinishApplied(id, count) => {
                if count > rebuilt.0.len() {
                    return Err(invalid_root(span));
                }
                reserve_rebuilt_type(&mut rebuilt, budget, span)?;
                let values = rebuilt.0.split_off(rebuilt.0.len() - count);
                rebuilt
                    .0
                    .push(Type::AppliedNominal(id, values.into_boxed_slice()));
            }
            Task::FinishFunction => {
                if rebuilt.0.len() < 2 {
                    return Err(invalid_root(span));
                }
                reserve_rebuilt_type(&mut rebuilt, budget, span)?;
                let codomain = rebuilt.0.pop().ok_or_else(|| invalid_root(span))?;
                let domain = rebuilt.0.pop().ok_or_else(|| invalid_root(span))?;
                rebuilt
                    .0
                    .push(Type::Function(Box::new(domain), Box::new(codomain)));
            }
        }
    }
    if rebuilt.0.len() != 1 {
        return Err(invalid_root(span));
    }
    Ok(rebuilt.0.pop().expect("one reconstructed evidence type"))
}

fn charge_and_push_type(
    rebuilt: &mut TypeBuffer,
    ty: Type,
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<(), EvidenceValidationFailure> {
    charge(budget, 1, span)?;
    rebuilt.0.try_reserve(1).map_err(|_| resource(span))?;
    rebuilt.0.push(ty);
    Ok(())
}

fn reserve_rebuilt_type(
    rebuilt: &mut TypeBuffer,
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<(), EvidenceValidationFailure> {
    charge(budget, 1, span)?;
    rebuilt.0.try_reserve(1).map_err(|_| resource(span))
}

fn implementation_is_available(
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
        if available.id() == implementation
            && match available.route() {
                ImplementationRoute::Local => implementation.module() == group.module(),
                ImplementationRoute::DirectImport {
                    direct_dependency, ..
                } => direct_dependency == implementation.module(),
            }
        {
            return Ok(true);
        }
    }
    Ok(false)
}

fn has_direct_dependency(
    group: &ResolvedModuleGroup,
    target: ModuleId,
    import_span: Span,
    budget: &mut InterfaceConstraintBudget,
) -> Result<bool, EvidenceValidationFailure> {
    for index in 0..group.direct_dependencies().len() {
        charge(budget, 1, import_span)?;
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
    validate_linked_type(
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

#[cfg(test)]
mod tests {
    use std::{
        fs,
        path::PathBuf,
        sync::atomic::{AtomicU64, Ordering},
    };

    use super::*;
    use crate::{
        elaborate::{check_module, link_modules, link_modules_with_budget},
        interface::{EvidenceSelectionBuilder, match_implementation_head},
        module::{ModuleGraph, ModuleRoots, load_module_graph},
        resolve::{DependencyExports, resolve_module},
        resolved::CheckedModule,
        types::{InferenceVariableId, Type, TypeVariableId, TypeWorkBudget},
    };

    static FIXTURE_IDS: AtomicU64 = AtomicU64::new(0);

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

    fn single_substitution(
        parameter: crate::types::TypeVariableId,
        argument: &Type,
    ) -> Box<[crate::interface::EvidenceSubstitution]> {
        match_implementation_head(
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
    fn rejects_wrong_generic_substitution_and_prerequisite_argument() {
        let program = generic_program();
        let group = &program.groups()[0];
        let generic = &group.implementation_facts()[1];
        let Type::AppliedNominal(owner, _) = &generic.argument else {
            panic!("the generic fixture head should be a nominal application");
        };
        let selection = nested_generic_selection(
            &program,
            &Type::Bool,
            Type::AppliedNominal(*owner, vec![Type::Int].into_boxed_slice()),
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
    fn rejects_reordered_two_parameter_substitution() {
        let program = two_parameter_program();
        let group = &program.groups()[0];
        let fact = &group.implementation_facts()[0];
        let [first, second] = fact.head_parameters.as_ref() else {
            panic!("the fixture should retain two head parameters");
        };
        let goal = Type::Tuple(vec![Type::Int, Type::Bool].into_boxed_slice());
        let reordered = match_implementation_head(
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
        let Type::AppliedNominal(owner, _) = &generic.argument else {
            panic!("the generic implementation should retain a nominal head");
        };
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
                    Type::AppliedNominal(*owner, vec![Type::Int].into_boxed_slice()),
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
            Type::Variable(first.scheme.type_parameters[0]),
        );
        let registry =
            LinkedInterfaceRegistry::build(&program, &mut InterfaceConstraintBudget::default())
                .expect("the valid linked registry should authenticate");
        let scope = EvidenceScope {
            owner: Some(RequirementOwner::Global(second.binder)),
            variables: &second.scheme.type_parameters,
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
        let scope = EvidenceScope {
            owner: Some(RequirementOwner::Global(first.binder)),
            variables: &first.scheme.type_parameters,
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
        let scope = EvidenceScope {
            owner: Some(RequirementOwner::Global(shadowed.binder)),
            variables: &shadowed.scheme.type_parameters,
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
                    &Type::Variable(*scope_parameter),
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
                    &Type::Variable(*scope_parameter),
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
                    &Type::Variable(*scope_parameter),
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
        let Type::AppliedNominal(outer_nominal, _) = &outer.argument else {
            panic!("the enclosing implementation should retain a nominal head");
        };
        let nested = nested_builder
            .finish(
                nested_root,
                outer.interface,
                Type::AppliedNominal(
                    *outer_nominal,
                    vec![requirement.argument.clone()].into_boxed_slice(),
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
        let scope = EvidenceScope {
            owner: Some(RequirementOwner::Global(shadowed.binder)),
            variables: &shadowed.scheme.type_parameters,
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
            exact, 6,
            "owner lookup, requirement visit, and exact Wrap<A> identity are charged"
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
            exact, 73,
            "exact-current relationships and the mandated abstract prerequisite are charged"
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
        let Type::AppliedNominal(owner, _) = &generic.argument else {
            panic!("the generic fixture should retain its nominal head");
        };
        let methods = ground
            .methods
            .iter()
            .map(|method| method.id)
            .collect::<Vec<_>>();
        let malformed = [
            Type::Nominal(NominalTypeId::new(group.module(), 99)),
            Type::Nominal(*owner),
            Type::AppliedNominal(*owner, Box::new([])),
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
        .expect_err("a transitive implementation should be unavailable in the entry module");

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
    fn rejects_dependency_private_implementation_forged_into_importer_availability() {
        let fixture = ValidationFixture::create(concat!(
            "import dependency as Dependency\n",
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
        let program = local_program();
        let mut measured = InterfaceConstraintBudget::default();
        drop(
            LinkedInterfaceRegistry::build(&program, &mut measured)
                .expect("the linked registry should fit the default budget"),
        );
        let limit = measured.used();
        assert_eq!(limit, 99, "every retained registry relationship is charged");

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
        assert_eq!(link_used, 7, "every linked retained entry is charged");
        drop(
            validate_interface_evidence_with_budget(linked, &mut measured)
                .expect("the linked evidence should validate on the same budget"),
        );
        let total = measured.used();
        assert!(total > link_used);

        let mut one_short = InterfaceConstraintBudget::with_limit(total - 1);
        let linked = link_modules_with_budget(check_graph(&graph), graph.entry(), &mut one_short)
            .expect("the full link prefix should fit below the total validation boundary");
        assert_eq!(one_short.used(), link_used);
        assert_eq!(
            validate_interface_evidence_with_budget(linked, &mut one_short)
                .expect_err("one unit below the combined boundary must fail in validation")
                .reason(),
            EvidenceValidationReason::ConstraintResourceExhausted,
        );

        let mut exact = InterfaceConstraintBudget::with_limit(total);
        let linked = link_modules_with_budget(check_graph(&graph), graph.entry(), &mut exact)
            .expect("the exact combined boundary should admit linking");
        drop(
            validate_interface_evidence_with_budget(linked, &mut exact)
                .expect("the exact combined boundary should admit validation"),
        );
        assert_eq!(exact.used(), total);
    }

    #[test]
    fn evidence_node_validation_has_an_exact_constraint_limit() {
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
            limit, 15,
            "root goal, type, node, exact head, method slot, and availability are charged"
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
    fn one_available_implementation_visit_requires_exactly_one_unit() {
        let program = local_program();
        let group = &program.groups()[0];
        let implementation = group.implementation_facts()[0].id;
        assert_eq!(group.available_implementations().len(), 1);

        assert_eq!(
            implementation_is_available(
                group,
                implementation,
                &mut InterfaceConstraintBudget::with_limit(0),
                group.span(),
            )
            .expect_err("the first availability visit must charge before inspection")
            .reason(),
            EvidenceValidationReason::ConstraintResourceExhausted,
        );
        assert!(
            implementation_is_available(
                group,
                implementation,
                &mut InterfaceConstraintBudget::with_limit(1),
                group.span(),
            )
            .expect("one exact availability unit should fit")
        );
    }

    #[test]
    fn one_direct_dependency_visit_requires_exactly_one_unit() {
        let fixture = ValidationFixture::create(concat!(
            "import dependency as Dependency\n",
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
        let [route] = entry.direct_dependencies() else {
            panic!("the entry should retain one authenticated direct edge");
        };

        assert_eq!(
            has_direct_dependency(
                entry,
                route.target(),
                route.import_span(),
                &mut InterfaceConstraintBudget::with_limit(0),
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
}
