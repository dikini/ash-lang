//! Authentication of linked checked interface evidence before Core synthesis.

use std::{collections::HashMap, error::Error, fmt, sync::Arc};

use crate::{
    interface::{
        CheckedRequirement, ConstrainedScheme, EvidenceNode, EvidenceNodeId, EvidenceSelection,
        ImplId, ImplMethodId, InterfaceConstraintBudget, InterfaceId, MethodId, RequirementId,
        RequirementOwner,
    },
    module::ModuleId,
    resolved::{
        BinderId, CheckedImplementationFact, CheckedInterfaceFact, ImplementationRoute,
        ResolvedBlock, ResolvedDeclarationIndex, ResolvedDefinitionKind, ResolvedExpr,
        ResolvedExprKind, ResolvedLocalDeclaration, ResolvedModuleGroup, ResolvedModuleProgram,
        ResolvedOccurrence, ResolvedRegistry, ResolvedTermName,
    },
    source::Span,
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
                        self,
                        program,
                        budget,
                    )?;
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
                let defining_module = program.groups()[location.group].module();
                match available.route() {
                    ImplementationRoute::Local if defining_module == group.module() => {}
                    ImplementationRoute::DirectImport {
                        direct_dependency,
                        available_at,
                    } if defining_module == direct_dependency
                        && available.id().module() == direct_dependency
                        && self.modules.contains_key(&direct_dependency)
                        && has_direct_dependency(
                            group,
                            direct_dependency,
                            available_at,
                            budget,
                        )? => {}
                    ImplementationRoute::Local | ImplementationRoute::DirectImport { .. } => {
                        return Err(unknown(group.span()));
                    }
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

/// A checked module program whose retained interface evidence has been authenticated.
#[derive(Debug)]
pub struct ValidatedInterfaceProgram {
    source: ResolvedModuleProgram,
    _linked_interfaces: LinkedInterfaceRegistry,
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

    pub(crate) const fn source(&self) -> &ResolvedModuleProgram {
        &self.source
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
    Ok(ValidatedInterfaceProgram {
        source: program,
        _linked_interfaces: linked_interfaces,
    })
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
                ResolvedDeclarationIndex::Type(_) | ResolvedDeclarationIndex::Interface(_) => {}
                ResolvedDeclarationIndex::Global(_)
                | ResolvedDeclarationIndex::Implementation(_) => return Err(unknown(group.span())),
            }
        }
        if next_definition != group.definitions().len()
            || next_implementation != group.implementations().len()
        {
            return Err(unknown(group.span()));
        }
    }
    Ok(())
}

fn validate_definition(
    program: &ResolvedModuleProgram,
    registry: &LinkedInterfaceRegistry,
    group: &ResolvedModuleGroup,
    definition: &crate::resolved::CheckedDefinition,
    budget: &mut InterfaceConstraintBudget,
) -> Result<(), EvidenceValidationFailure> {
    match definition.kind() {
        ResolvedDefinitionKind::Equational(global) => {
            for equation_index in 0..global.equations.len() {
                charge(budget, 1, definition.span())?;
                let equation = global
                    .equations
                    .get(equation_index)
                    .ok_or_else(|| unknown(definition.span()))?;
                validate_expression(program, registry, group, &equation.body, budget)?;
            }
        }
        ResolvedDefinitionKind::InlineOperational(global) => {
            let mut pending = Vec::new();
            schedule_block(&mut pending, &global.body, budget)?;
            validate_pending_expressions(program, registry, group, &mut pending, budget)?;
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
            validate_expression(program, registry, group, &equation.body, budget)?;
        }
    }
    Ok(())
}

fn validate_expression(
    program: &ResolvedModuleProgram,
    registry: &LinkedInterfaceRegistry,
    group: &ResolvedModuleGroup,
    root: &ResolvedExpr,
    budget: &mut InterfaceConstraintBudget,
) -> Result<(), EvidenceValidationFailure> {
    let mut pending = Vec::new();
    reserve_expressions(&mut pending, 1, budget, root.span)?;
    pending.push(root);
    validate_pending_expressions(program, registry, group, &mut pending, budget)
}

fn validate_pending_expressions(
    program: &ResolvedModuleProgram,
    registry: &LinkedInterfaceRegistry,
    group: &ResolvedModuleGroup,
    pending: &mut Vec<&ResolvedExpr>,
    budget: &mut InterfaceConstraintBudget,
) -> Result<(), EvidenceValidationFailure> {
    while let Some(expression) = pending.pop() {
        charge(budget, 1, expression.span)?;
        match &expression.kind {
            ResolvedExprKind::Occurrence(occurrence) => {
                validate_occurrence(program, registry, group, occurrence, budget)?;
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
                let selection = slot.selection().ok_or_else(|| invalid_root(span))?;
                validate_selection(
                    program,
                    registry,
                    group,
                    selection,
                    requirement.interface,
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
            let selection = slot.selection().ok_or_else(|| invalid_root(span))?;
            validate_selection(
                program,
                registry,
                group,
                selection,
                method.id.interface(),
                budget,
                span,
            )?;
        }
    }
    Ok(())
}

fn validate_selection(
    program: &ResolvedModuleProgram,
    registry: &LinkedInterfaceRegistry,
    group: &ResolvedModuleGroup,
    selection: &EvidenceSelection,
    expected_interface: InterfaceId,
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<(), EvidenceValidationFailure> {
    charge(budget, 2, span)?;
    budget
        .charge_type(selection.argument())
        .map_err(|()| resource(span))?;
    if selection.interface() != expected_interface
        || registry.interface(program, selection.interface()).is_none()
        || selection.node(selection.root()).is_none()
    {
        return Err(invalid_root(span));
    }
    let mut pending = Vec::new();
    reserve_nodes(&mut pending, 1, budget, span)?;
    pending.push((selection.root(), expected_interface));
    while let Some((node, expected_interface)) = pending.pop() {
        charge(budget, 1, span)?;
        let interface = registry
            .interface(program, expected_interface)
            .ok_or_else(|| unknown(span))?;
        match selection.node(node).ok_or_else(|| invalid_root(span))? {
            EvidenceNode::Abstract {
                requirement,
                methods,
            } => {
                charge(budget, methods.len().saturating_add(1), span)?;
                let requirement = registry
                    .requirement(program, requirement)
                    .ok_or_else(|| unknown(span))?;
                if requirement.interface != expected_interface
                    || !methods
                        .iter()
                        .copied()
                        .eq(interface.methods.iter().map(|method| method.id))
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
                if fact.interface != expected_interface
                    || !implementation_is_available(group, implementation, budget, span)?
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
                reserve_nodes(&mut pending, prerequisites.len(), budget, span)?;
                for (prerequisite, requirement) in
                    prerequisites.iter().copied().zip(&fact.prerequisites).rev()
                {
                    if prerequisite.index() >= node.index() {
                        return Err(invalid_root(span));
                    }
                    pending.push((prerequisite, requirement.interface));
                }
            }
        }
    }
    Ok(())
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
    registry: &LinkedInterfaceRegistry,
    program: &ResolvedModuleProgram,
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<(), EvidenceValidationFailure> {
    for (ordinal, requirement) in scheme.requirements.iter().enumerate() {
        validate_requirement(requirement, owner, ordinal, registry, program, budget)?;
    }
    charge(budget, 0, span)
}

fn validate_requirement(
    requirement: &CheckedRequirement,
    owner: RequirementOwner,
    ordinal: usize,
    registry: &LinkedInterfaceRegistry,
    program: &ResolvedModuleProgram,
    budget: &mut InterfaceConstraintBudget,
) -> Result<(), EvidenceValidationFailure> {
    charge(budget, 1, requirement.span)?;
    budget
        .charge_type(&requirement.argument)
        .map_err(|()| resource(requirement.span))?;
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
        let count = match declaration {
            ResolvedLocalDeclaration::Binding(_) => 1,
            ResolvedLocalDeclaration::Recursive(group) => group.members.len(),
        };
        additional = additional
            .checked_add(count)
            .ok_or_else(|| resource(block.span))?;
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

fn reserve_nodes(
    pending: &mut Vec<(EvidenceNodeId, InterfaceId)>,
    additional: usize,
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<(), EvidenceValidationFailure> {
    reserve_expressions(pending, additional, budget, span)
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
        interface::EvidenceSelectionBuilder,
        module::{ModuleGraph, ModuleRoots, load_module_graph},
        resolve::{DependencyExports, resolve_module},
        resolved::CheckedModule,
        types::Type,
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
            .finish(root, interface, Type::Int)
            .expect("the implementation root should exist")
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
    fn linked_registry_entries_have_an_exact_constraint_limit() {
        let program = local_program();
        let mut measured = InterfaceConstraintBudget::default();
        drop(
            LinkedInterfaceRegistry::build(&program, &mut measured)
                .expect("the linked registry should fit the default budget"),
        );
        let limit = measured.used();
        assert_eq!(limit, 20, "every retained registry relationship is charged");

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
            limit, 9,
            "root, goal, node, method slot, and availability are charged"
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
}
