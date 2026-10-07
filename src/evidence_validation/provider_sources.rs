//! Source-side authentication of sealed forwarding dictionaries. This borrows
//! checked preparation; executable scope authority is admitted independently.
use super::{
    EvidenceScope, EvidenceValidationFailure, ExpectedEquation, LinkedInterfaceRegistry,
    LinkedLocalScope, OwnerReplacements, charge, invalid_root, linked_selection_key_types,
    map_kind_constraint_failure, map_kind_type_failure, resource, same_application_parts_charged,
    same_argument_charged, same_type_charged, type_resource, unknown,
    validate_argument_with_policy,
};
use crate::resolved::{OwnerId, ResolvedProviderResourceExpr};
use crate::{
    core::dialect::MethodEvidenceMethod,
    interface::{InterfaceApplication, InterfaceConstraintBudget, MethodId},
    kind::KindEnvironments,
    module::ModuleId,
    resolved::{CheckedInterfaceFact, ResolvedModuleProgram},
    source::Span,
    types::{
        EffectRowVariable, IterativeTypeOwner, Kind, KindedArgument, Type, TypeWorkBudget,
        clone_kinded_argument_with_budget, substitute_type_and_row_variables_with,
    },
};
use std::collections::HashMap;

/// Original declaration coordinates, never checker-retained application facts.
#[derive(Clone, Copy)]
pub(super) struct OriginalLexicalContext {
    pub(super) equation: Option<ExpectedEquation>,
    pub(super) owner: Option<crate::interface::RequirementOwner>,
    pub(super) local_head: Option<usize>,
}
impl OriginalLexicalContext {
    #[cfg(test)]
    pub(super) const NONE: Self = Self {
        equation: None,
        owner: None,
        local_head: None,
    };
}

#[derive(Clone, Copy)]
pub(super) enum LinkedLexicalSource<'a> {
    Declared(
        &'a crate::resolved::ResolvedLexicalEvidence,
        OriginalLexicalContext,
    ),
    Provider(&'a ResolvedProviderResourceExpr),
}
impl<'a> LinkedLexicalSource<'a> {
    pub(super) fn id(self) -> crate::interface::LexicalEvidenceId {
        match self {
            Self::Declared(source, _) => source.id,
            Self::Provider(source) => source.provider,
        }
    }
    pub(super) fn application(
        self,
        span: Span,
    ) -> Result<&'a InterfaceApplication, EvidenceValidationFailure> {
        match self {
            Self::Declared(source, _) => source.checked.get().map(|checked| &checked.application),
            Self::Provider(source) => source
                .prepared
                .get()
                .map(|plan| plan.forwarding_application()),
        }
        .ok_or_else(|| invalid_root(span))
    }
    #[allow(clippy::too_many_arguments)] // Original lexical context and independent validation ledgers stay separate.
    pub(super) fn same_application(
        self,
        program: &ResolvedModuleProgram,
        registry: &LinkedInterfaceRegistry,
        application: &InterfaceApplication,
        scope: EvidenceScope<'_>,
        budget: &mut InterfaceConstraintBudget,
        work: &mut TypeWorkBudget,
        span: Span,
    ) -> Result<bool, EvidenceValidationFailure> {
        match self {
            Self::Declared(source, original) => {
                if application.interface() != source.application.interface.id
                    || application.arguments().len() != source.application.arguments.len()
                {
                    return Ok(false);
                }
                let expected = lexical_context_rows(
                    program,
                    registry,
                    source,
                    EvidenceScope {
                        expected_equation: original.equation,
                        owner: original.owner,
                        ..scope
                    },
                    scope.local_scopes,
                    original.local_head,
                    budget,
                    work,
                )?;
                for (actual, resolved) in application
                    .arguments()
                    .iter()
                    .zip(&source.application.arguments)
                {
                    let qualified =
                        crate::types::qualify_kinded_argument_with_row_contexts_with_budget(
                            &resolved.ty,
                            expected.iter(),
                            work,
                        )
                        .map_err(|()| type_resource(span))?
                        .map_err(|_| invalid_root(span))?;
                    let qualified = qualified.map(crate::types::IterativeArgumentOwner::new);
                    if !same_argument_charged(
                        actual,
                        qualified.as_deref().unwrap_or(&resolved.ty),
                        budget,
                        span,
                    )? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Self::Provider(_) => {
                let actual = self.application(span)?;
                same_application_parts_charged(
                    actual,
                    application.interface(),
                    application.arguments(),
                    budget,
                    span,
                )
            }
        }
    }
}

pub(super) fn validate_provider_selection(
    source: &ResolvedProviderResourceExpr,
    module: ModuleId,
    interface: &CheckedInterfaceFact,
    methods: &[MethodId],
    application: &InterfaceApplication,
    budget: &mut InterfaceConstraintBudget,
    span: Span,
) -> Result<(), EvidenceValidationFailure> {
    let plan = source.prepared.get().ok_or_else(|| invalid_root(span))?;
    charge(
        budget,
        methods
            .len()
            .checked_add(source.forwarding.len())
            .ok_or_else(|| resource(span))?,
        span,
    )?;
    if source.provider.module() != module
        || plan.provider() != source.provider
        || methods.len() != source.forwarding.len()
        || !methods
            .iter()
            .copied()
            .eq(interface.methods.iter().map(|method| method.id))
        || !same_application_parts_charged(
            plan.forwarding_application(),
            application.interface(),
            application.arguments(),
            budget,
            span,
        )?
    {
        return Err(invalid_root(span));
    }
    let mut supplied = plan.forwarding_methods();
    for (method, binder) in methods.iter().zip(&source.forwarding) {
        let (checked_method, checked_binder, _) =
            supplied.next().ok_or_else(|| invalid_root(span))?;
        if *method != binder.method
            || checked_method != *method
            || checked_binder != binder.binder.id
            || binder.binder.id.module() != Some(module)
            || binder.parameter.id.module() != Some(module)
        {
            return Err(invalid_root(span));
        }
    }
    if supplied.next().is_some() {
        return Err(invalid_root(span));
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub(super) fn authenticate_provider_source<'a>(
    program: &'a ResolvedModuleProgram,
    registry: &LinkedInterfaceRegistry,
    source: &ResolvedProviderResourceExpr,
    scope: EvidenceScope<'_>,
    locals: &[(LinkedLocalScope<'_>, Option<usize>)],
    local_head: Option<usize>,
    environments: &mut KindEnvironments<'a>,
    budget: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
    span: Span,
) -> Result<(), EvidenceValidationFailure> {
    let plan = source.prepared.get().ok_or_else(|| invalid_root(span))?;
    let definition = plan.definition();
    let canonical = program
        .registry()
        .type_variable(source.identity.id)
        .ok_or_else(|| invalid_root(span))?;
    charge(
        budget,
        canonical
            .spelling
            .len()
            .checked_add(2)
            .ok_or_else(|| resource(span))?,
        span,
    )?;
    if plan.provider() != source.provider
        || definition.id != source.definition
        || definition.family != source.family
        || source.identity.id.module() != Some(source.provider.module())
        || canonical.kind != Kind::Type
        || canonical.spelling != source.identity.spelling
        || canonical.origin.primary_span() != source.identity.origin.primary_span()
        || program
            .registry()
            .resource_signature_family(source.definition)
            != Some(source.family)
        || !matches!(plan.arguments().first(), Some(KindedArgument::TypeArg(Type::Variable(id))) if *id == source.identity.id)
        || plan.arguments().len() != definition.parameters.len()
    {
        return Err(invalid_root(span));
    }
    program
        .registry()
        .authenticate_owner_signature(
            OwnerId::Resource(source.definition),
            Some(source.family),
            &definition.parameters,
            type_work,
        )
        .map_err(|failure| {
            if failure.is_resource_exhaustion() {
                type_resource(span)
            } else {
                invalid_root(span)
            }
        })?;
    type_work
        .charge(program.registry().provider_contract_count())
        .map_err(|()| type_resource(span))?;
    let certificate = program
        .registry()
        .provider_contracts()
        .find(|(module, _)| **module == source.definition.module())
        .map(|(_, certificate)| certificate)
        .ok_or_else(|| invalid_root(span))?;
    type_work
        .charge(certificate.resource_count())
        .map_err(|()| type_resource(span))?;
    if !certificate
        .resource_contracts()
        .any(|(_, _, original)| std::ptr::eq(original.as_ref(), definition))
    {
        return Err(invalid_root(span));
    }
    if let Some(arguments) = &source.arguments {
        if arguments.len().checked_add(1) != Some(plan.arguments().len()) {
            return Err(invalid_root(span));
        }
        let expected = if arguments.is_empty() {
            None
        } else {
            preceding_equation_row(
                program, registry, scope, locals, local_head, budget, type_work, span,
            )?
        };
        for (written, actual) in arguments.iter().zip(plan.arguments().iter().skip(1)) {
            let qualified = crate::types::qualify_kinded_argument_with_expected_row_with_budget(
                &written.ty,
                expected.as_ref(),
                type_work,
            )
            .map_err(|()| type_resource(span))?
            .map_err(|_| invalid_root(span))?
            .map(crate::types::IterativeArgumentOwner::new);
            let written = qualified
                .as_ref()
                .map_or(&written.ty, |owner| owner.as_ref());
            if !same_argument_charged(written, actual, budget, span)? {
                return Err(invalid_root(span));
            }
        }
    } else if definition
        .parameters
        .iter()
        .any(|parameter| parameter.kind == Kind::EffectRow)
    {
        return Err(invalid_root(span));
    }
    let count = scope
        .variables
        .len()
        .checked_add(1)
        .ok_or_else(|| resource(span))?;
    charge(budget, count, span)?;
    let mut variables = Vec::new();
    variables
        .try_reserve_exact(count)
        .map_err(|_| resource(span))?;
    variables.extend_from_slice(scope.variables);
    if variables.contains(&source.identity.id) {
        return Err(invalid_root(span));
    }
    variables.push(source.identity.id);
    for argument in plan.arguments() {
        validate_argument_with_policy(argument, program.registry(), &variables, budget, span)?;
    }
    environments
        .install_canonical_owner_ids(program.registry(), &variables, type_work, span)
        .map_err(|failure| map_kind_type_failure(failure, span))?;
    let access = IterativeTypeOwner::new(
        plan.access_type(type_work)
            .map_err(|failure| preparation_failure(failure, span))?,
    );
    environments
        .expect_body_free_exact_kind_with_ledger(&access, &Kind::Type, span, budget)
        .map_err(|failure| map_kind_constraint_failure(failure, span))?;
    let application = plan.forwarding_application();
    let interface = registry
        .interface(program, application.interface())
        .ok_or_else(|| unknown(span))?;
    environments
        .expect_body_free_interface_argument_with_ledger(
            application.interface(),
            application.arguments(),
            span,
            budget,
        )
        .map_err(|failure| map_kind_constraint_failure(failure, span))?;
    charge(budget, source.forwarding.len(), span)?;
    let mut methods = Vec::new();
    methods
        .try_reserve_exact(source.forwarding.len())
        .map_err(|_| resource(span))?;
    methods.extend(source.forwarding.iter().map(|method| method.method));
    validate_provider_selection(
        source,
        source.provider.module(),
        interface,
        &methods,
        application,
        budget,
        span,
    )?;
    let keys = linked_selection_key_types(interface, application.arguments(), budget, span)?;
    let mut head = scope.lexical_head;
    while let Some(index) = head {
        charge(budget, 1, span)?;
        let (earlier, parent) = scope
            .lexical_sources
            .get(index)
            .ok_or_else(|| invalid_root(span))?;
        let earlier = earlier.application(span)?;
        if earlier.interface() == interface.id {
            let earlier_keys =
                linked_selection_key_types(interface, earlier.arguments(), budget, span)?;
            let mut equal = true;
            for (actual, previous) in keys.iter().zip(earlier_keys) {
                if !same_argument_charged(actual, previous, budget, span)? {
                    equal = false;
                    break;
                }
            }
            if equal {
                return Err(invalid_root(span));
            }
        }
        head = *parent;
    }
    Ok(())
}

/// Rebuilds exactly the row pushed by ordinary equation preparation. A pure
/// equation pushes no row and therefore inherits its preceding context.
fn equation_row(
    scheme: &Type,
    arity: usize,
    work: &mut TypeWorkBudget,
    span: Span,
) -> Result<Option<crate::types::EffectRow>, EvidenceValidationFailure> {
    if arity == 0 {
        return Err(invalid_root(span));
    }
    let mut remainder = scheme;
    let mut effects = None;
    for _ in 0..arity {
        work.charge(1).map_err(|()| type_resource(span))?;
        let function = remainder
            .function_view()
            .ok_or_else(|| invalid_root(span))?;
        effects = function.effects();
        remainder = function.value();
    }
    let Some(effects) = effects else {
        return Ok(None);
    };
    if !matches!(
        effects.tail().map(|tail| tail.variable()),
        Some(EffectRowVariable::Rigid(_))
    ) {
        return crate::types::clone_effect_row_with_budget(effects, work)
            .map(Some)
            .map_err(|()| type_resource(span));
    }
    let mut rows = HashMap::new();
    crate::types::qualify_scheme_row_replacements_with_budget(
        scheme,
        &HashMap::new(),
        &mut rows,
        true,
        work,
    )
    .map_err(|()| type_resource(span))?;
    let qualified = IterativeTypeOwner::new(
        substitute_type_and_row_variables_with(
            scheme,
            &HashMap::new(),
            &rows,
            |cells| work.charge(cells),
            || (),
        )
        .map_err(|()| type_resource(span))?
        .map_err(|_| invalid_root(span))?,
    );
    let mut remainder = &*qualified;
    let mut effects = None;
    for _ in 0..arity {
        work.charge(1).map_err(|()| type_resource(span))?;
        let function = remainder
            .function_view()
            .ok_or_else(|| invalid_root(span))?;
        effects = function.effects();
        remainder = function.value();
    }
    effects
        .map(|row| crate::types::clone_effect_row_with_budget(row, work))
        .transpose()
        .map_err(|()| type_resource(span))
}

/// Canonical method facts and the original lexical application authenticate
/// this row; the checked resource specialization supplies no facts here.
#[allow(clippy::too_many_arguments)]
fn lexical_equation_row(
    program: &ResolvedModuleProgram,
    registry: &LinkedInterfaceRegistry,
    source: &crate::resolved::ResolvedLexicalEvidence,
    group: &crate::resolved::ResolvedImplementationMethodGroup,
    arity: usize,
    budget: &mut InterfaceConstraintBudget,
    work: &mut TypeWorkBudget,
    span: Span,
) -> Result<Option<crate::types::EffectRow>, EvidenceValidationFailure> {
    let method = group.method.ok_or_else(|| invalid_root(span))?;
    charge(budget, 2, span)?;
    let canonical = registry
        .method(program, method)
        .ok_or_else(|| unknown(span))?;
    let interface = registry
        .interface(program, method.interface())
        .ok_or_else(|| unknown(span))?;
    if source.application.interface.id != interface.id
        || group.identity.is_some()
        || interface.parameters.len() != source.application.arguments.len()
        || canonical.authoritative_type_parameters().len() != group.contextual_parameters.len()
    {
        return Err(invalid_root(span));
    }
    let count = interface
        .parameters
        .len()
        .checked_add(group.contextual_parameters.len())
        .ok_or_else(|| type_resource(span))?;
    work.charge(
        count
            .checked_add(source.application.arguments.len())
            .ok_or_else(|| type_resource(span))?,
    )
    .map_err(|()| type_resource(span))?;
    let row_count = source
        .application
        .arguments
        .iter()
        .filter(|argument| matches!(&argument.ty, KindedArgument::RowArg(_)))
        .count();
    let mut replacements = OwnerReplacements {
        types: HashMap::new(),
        rows: HashMap::new(),
    };
    replacements
        .types
        .try_reserve(count - row_count)
        .map_err(|_| type_resource(span))?;
    replacements
        .rows
        .try_reserve(row_count)
        .map_err(|_| type_resource(span))?;
    for (parameter, argument) in interface
        .parameters
        .iter()
        .zip(&source.application.arguments)
    {
        let argument = clone_kinded_argument_with_budget(&argument.ty, work)
            .map_err(|()| type_resource(span))?;
        if replacements.insert_discarding_previous(parameter.id, argument) {
            return Err(invalid_root(span));
        }
    }
    for (parameter, contextual) in canonical
        .authoritative_type_parameters()
        .iter()
        .zip(&group.contextual_parameters)
    {
        work.charge(1).map_err(|()| type_resource(span))?;
        if parameter.kind == Kind::EffectRow
            || !crate::types::same_kind_with_budget(&parameter.kind, &contextual.kind, work)
                .map_err(|()| type_resource(span))?
            || replacements.insert_discarding_previous(
                parameter.id,
                KindedArgument::TypeArg(Type::Variable(contextual.id)),
            )
        {
            return Err(invalid_root(span));
        }
    }
    let scheme = IterativeTypeOwner::new(
        substitute_type_and_row_variables_with(
            canonical.value_type(),
            &replacements.types,
            &replacements.rows,
            |cells| work.charge(cells),
            || (),
        )
        .map_err(|()| type_resource(span))?
        .map_err(|_| invalid_root(span))?,
    );
    equation_row(&scheme, arity, work, span)
}

#[allow(clippy::too_many_arguments)]
pub(super) fn preceding_equation_row(
    program: &ResolvedModuleProgram,
    registry: &LinkedInterfaceRegistry,
    scope: EvidenceScope<'_>,
    locals: &[(LinkedLocalScope<'_>, Option<usize>)],
    mut head: Option<usize>,
    budget: &mut InterfaceConstraintBudget,
    work: &mut TypeWorkBudget,
    span: Span,
) -> Result<Option<crate::types::EffectRow>, EvidenceValidationFailure> {
    // Only nonempty equation rows push the elaborator's expected-row stack.
    // Anonymous functions inherit it; operational globals establish none.
    while let Some(index) = head {
        charge(budget, 1, span)?;
        let (local, parent) = locals.get(index).ok_or_else(|| invalid_root(span))?;
        if let LinkedLocalScope::Equation {
            source,
            method,
            arity,
        } = local
            && let Some(row) = lexical_equation_row(
                program, registry, source, method, *arity, budget, work, span,
            )?
        {
            return Ok(Some(row));
        }
        head = *parent;
    }
    let Some(equation) = scope.expected_equation else {
        return Ok(None);
    };
    charge(budget, 1, span)?;
    let (scheme, arity) = match equation {
        ExpectedEquation::Global { binder, arity }
            if scope.owner == Some(crate::interface::RequirementOwner::Global(binder)) =>
        {
            (
                &registry
                    .scheme(program, binder)
                    .ok_or_else(|| unknown(span))?
                    .value_type,
                arity,
            )
        }
        ExpectedEquation::Implementation { method, arity }
            if scope.owner
                == Some(crate::interface::RequirementOwner::Impl(
                    method.implementation(),
                )) =>
        {
            (
                &registry
                    .implementation_method(program, method)
                    .ok_or_else(|| unknown(span))?
                    .scheme
                    .value_type,
                arity,
            )
        }
        _ => return Err(invalid_root(span)),
    };
    equation_row(scheme, arity, work, span)
}

/// Original written declarations establish facts for every formal row in their
/// complete type, including latent parameter rows. Parent declarations remain
/// active inside a supplied method. Neither the checked application nor its
/// resource plan contributes exclusions.
#[allow(clippy::too_many_arguments)]
pub(super) fn lexical_context_rows(
    program: &ResolvedModuleProgram,
    registry: &LinkedInterfaceRegistry,
    source: &crate::resolved::ResolvedLexicalEvidence,
    scope: EvidenceScope<'_>,
    locals: &[(LinkedLocalScope<'_>, Option<usize>)],
    mut head: Option<usize>,
    budget: &mut InterfaceConstraintBudget,
    work: &mut TypeWorkBudget,
) -> Result<
    Vec<HashMap<crate::types::TypeVariableId, crate::types::EffectRow>>,
    EvidenceValidationFailure,
> {
    let span = source.span;
    if scope.expected_equation.is_none() && scope.owner.is_none() && head.is_none() {
        return Ok(Vec::new());
    }
    if !crate::types::kinded_arguments_have_rigid_rows_with_budget(
        source
            .application
            .arguments
            .iter()
            .map(|argument| &argument.ty),
        work,
    )
    .map_err(|()| type_resource(span))?
    {
        return Ok(Vec::new());
    }
    let mut enclosing = Vec::new();
    while let Some(index) = head {
        charge(budget, 1, span)?;
        let (local, parent) = locals.get(index).ok_or_else(|| invalid_root(span))?;
        if matches!(
            local,
            LinkedLocalScope::Equation { .. } | LinkedLocalScope::Annotation(_)
        ) {
            work.charge(1).map_err(|()| type_resource(span))?;
            enclosing.try_reserve(1).map_err(|_| type_resource(span))?;
            enclosing.push(local);
        }
        head = *parent;
    }
    let mut contexts = Vec::new();
    {
        let mut retain =
            |scheme: &Type, work: &mut TypeWorkBudget| -> Result<(), EvidenceValidationFailure> {
                let mut rows = HashMap::new();
                crate::types::qualify_scheme_row_replacements_with_budget(
                    scheme,
                    &HashMap::new(),
                    &mut rows,
                    true,
                    work,
                )
                .map_err(|()| type_resource(span))?;
                if !rows.is_empty() {
                    work.charge(1).map_err(|()| type_resource(span))?;
                    contexts.try_reserve(1).map_err(|_| type_resource(span))?;
                    contexts.push(rows);
                }
                Ok(())
            };
        if scope.expected_equation.is_none()
            && let Some(crate::interface::RequirementOwner::Global(binder)) = scope.owner
        {
            charge(budget, 1, span)?;
            retain(
                &registry
                    .scheme(program, binder)
                    .ok_or_else(|| unknown(span))?
                    .value_type,
                work,
            )?;
        }
        if let Some(equation) = scope.expected_equation {
            charge(budget, 1, span)?;
            let scheme = match equation {
                ExpectedEquation::Global { binder, .. }
                    if scope.owner == Some(crate::interface::RequirementOwner::Global(binder)) =>
                {
                    &registry
                        .scheme(program, binder)
                        .ok_or_else(|| unknown(span))?
                        .value_type
                }
                ExpectedEquation::Implementation { method, .. }
                    if scope.owner
                        == Some(crate::interface::RequirementOwner::Impl(
                            method.implementation(),
                        )) =>
                {
                    &registry
                        .implementation_method(program, method)
                        .ok_or_else(|| unknown(span))?
                        .scheme
                        .value_type
                }
                _ => return Err(invalid_root(span)),
            };
            retain(scheme, work)?;
        }
    }
    for local in enclosing.into_iter().rev() {
        let scheme = match local {
            LinkedLocalScope::Annotation(annotation) => {
                let mut rows = HashMap::new();
                crate::types::qualify_scheme_row_replacements_with_budget(
                    &annotation.ty,
                    &HashMap::new(),
                    &mut rows,
                    true,
                    work,
                )
                .map_err(|()| type_resource(span))?;
                if !crate::types::rigid_row_requirements_entailed_with_budget(
                    &rows, &contexts, work,
                )
                .map_err(|()| type_resource(span))?
                {
                    return Err(invalid_root(span));
                }
                // A local annotation refers to existing rigid binders. Its
                // written rows cannot extend the original enclosing contract.
                continue;
            }
            LinkedLocalScope::Equation {
                source,
                method: group,
                ..
            } => {
                let method = group.method.ok_or_else(|| invalid_root(span))?;
                charge(budget, 2, span)?;
                let canonical = registry
                    .method(program, method)
                    .ok_or_else(|| unknown(span))?;
                let interface = registry
                    .interface(program, method.interface())
                    .ok_or_else(|| unknown(span))?;
                if source.application.interface.id != interface.id
                    || group.identity.is_some()
                    || interface.parameters.len() != source.application.arguments.len()
                    || canonical.authoritative_type_parameters().len()
                        != group.contextual_parameters.len()
                {
                    return Err(invalid_root(span));
                }
                let mut replacements = OwnerReplacements {
                    types: HashMap::new(),
                    rows: HashMap::new(),
                };
                let count = interface
                    .parameters
                    .len()
                    .checked_add(group.contextual_parameters.len())
                    .ok_or_else(|| type_resource(span))?;
                work.charge(count).map_err(|()| type_resource(span))?;
                replacements
                    .types
                    .try_reserve(count)
                    .map_err(|_| type_resource(span))?;
                replacements
                    .rows
                    .try_reserve(count)
                    .map_err(|_| type_resource(span))?;
                for (parameter, argument) in interface
                    .parameters
                    .iter()
                    .zip(&source.application.arguments)
                {
                    let qualified =
                        crate::types::qualify_kinded_argument_with_row_contexts_with_budget(
                            &argument.ty,
                            contexts.iter(),
                            work,
                        )
                        .map_err(|()| type_resource(span))?
                        .map_err(|_| invalid_root(span))?;
                    let argument = if let Some(argument) = qualified {
                        argument
                    } else {
                        clone_kinded_argument_with_budget(&argument.ty, work)
                            .map_err(|()| type_resource(span))?
                    };
                    if replacements.insert_discarding_previous(parameter.id, argument) {
                        return Err(invalid_root(span));
                    }
                }
                for (parameter, contextual) in canonical
                    .authoritative_type_parameters()
                    .iter()
                    .zip(&group.contextual_parameters)
                {
                    work.charge(1).map_err(|()| type_resource(span))?;
                    if parameter.kind == Kind::EffectRow
                        || !crate::types::same_kind_with_budget(
                            &parameter.kind,
                            &contextual.kind,
                            work,
                        )
                        .map_err(|()| type_resource(span))?
                        || replacements.insert_discarding_previous(
                            parameter.id,
                            KindedArgument::TypeArg(Type::Variable(contextual.id)),
                        )
                    {
                        return Err(invalid_root(span));
                    }
                }
                IterativeTypeOwner::new(
                    substitute_type_and_row_variables_with(
                        canonical.value_type(),
                        &replacements.types,
                        &replacements.rows,
                        |cells| work.charge(cells),
                        || (),
                    )
                    .map_err(|()| type_resource(span))?
                    .map_err(|_| invalid_root(span))?,
                )
            }
            _ => return Err(invalid_root(span)),
        };
        let mut rows = HashMap::new();
        crate::types::qualify_scheme_row_replacements_with_budget(
            &scheme,
            &HashMap::new(),
            &mut rows,
            true,
            work,
        )
        .map_err(|()| type_resource(span))?;
        if !crate::types::rigid_row_requirements_entailed_with_budget(&rows, &contexts, work)
            .map_err(|()| type_resource(span))?
        {
            return Err(invalid_root(span));
        }
    }
    Ok(contexts)
}

#[allow(clippy::too_many_arguments)]
pub(super) fn retain_provider_lexical_owners(
    program: &ResolvedModuleProgram,
    source: &ResolvedProviderResourceExpr,
    span: Span,
    methods: &[MethodEvidenceMethod],
    owners: &mut Vec<crate::core::dialect::MethodEvidenceLexicalOwner>,
    budget: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
) -> Result<(), EvidenceValidationFailure> {
    let plan = source.prepared.get().ok_or_else(|| invalid_root(span))?;
    charge(
        budget,
        owners
            .len()
            .checked_add(source.forwarding.len())
            .ok_or_else(|| resource(span))?,
        span,
    )?;
    if owners.iter().any(|owner| owner.source == source.provider)
        || plan.provider() != source.provider
    {
        return Err(invalid_root(span));
    }
    owners
        .try_reserve(source.forwarding.len())
        .map_err(|_| resource(span))?;
    let mut checked_methods = plan.forwarding_methods();
    for forwarding in &source.forwarding {
        let (method, binder, ty) = checked_methods.next().ok_or_else(|| invalid_root(span))?;
        charge(budget, methods.len(), span)?;
        let canonical = methods
            .iter()
            .find(|candidate| candidate.id == method)
            .ok_or_else(|| unknown(span))?;
        if method != forwarding.method
            || binder != forwarding.binder.id
            || !canonical.parameters.is_empty()
            || plan.forwarding_application().interface() != method.interface()
            || canonical.interface_parameters.len()
                != plan.forwarding_application().arguments().len()
            || program
                .registry()
                .type_variable(source.identity.id)
                .is_none()
        {
            return Err(invalid_root(span));
        }
        let mut replacements = OwnerReplacements {
            types: HashMap::new(),
            rows: HashMap::new(),
        };
        charge(budget, canonical.interface_parameters.len(), span)?;
        let row_count = plan
            .forwarding_application()
            .arguments()
            .iter()
            .filter(|argument| matches!(argument, KindedArgument::RowArg(_)))
            .count();
        replacements
            .types
            .try_reserve(canonical.interface_parameters.len() - row_count)
            .map_err(|_| resource(span))?;
        replacements
            .rows
            .try_reserve(row_count)
            .map_err(|_| resource(span))?;
        for (parameter, argument) in canonical
            .interface_parameters
            .iter()
            .zip(plan.forwarding_application().arguments())
        {
            replacements.insert_discarding_previous(
                *parameter,
                clone_kinded_argument_with_budget(argument, type_work)
                    .map_err(|()| type_resource(span))?,
            );
        }
        let expected = IterativeTypeOwner::new(
            substitute_type_and_row_variables_with(
                &canonical.value_type,
                &replacements.types,
                &replacements.rows,
                |units| charge(budget, units, span),
                || resource(span),
            )?
            .map_err(|_| invalid_root(span))?,
        );
        if !same_type_charged(&expected, ty, budget, span)? {
            return Err(invalid_root(span));
        }
        // Guard the complete owner arguments before another fallible copy.
        let resource = crate::core::dialect::MethodEvidenceResourceOwner::Provider(
            crate::core::dialect::ProviderEvidenceOwner {
                definition: source.definition,
                family: source.family,
                identity: source.identity.id,
                arguments: crate::types::clone_kinded_arguments_with_budget(
                    plan.arguments().iter(),
                    type_work,
                )
                .map_err(|()| type_resource(span))?,
            },
        );
        let application = plan
            .forwarding_application()
            .clone_with_budget(type_work)
            .map_err(|()| type_resource(span))?;
        owners.push(crate::core::dialect::MethodEvidenceLexicalOwner {
            resource: Some(resource),
            source_parameters: Box::new([]),
            source: source.provider,
            method,
            binder,
            application,
            captures: Box::new([]),
        });
    }
    if checked_methods.next().is_some() {
        return Err(invalid_root(span));
    }
    Ok(())
}

pub(super) fn preparation_failure(
    failure: crate::elaborate::TypeError,
    span: Span,
) -> EvidenceValidationFailure {
    match failure {
        crate::elaborate::TypeError::Internal(
            crate::elaborate::ElaborationFailure::TypeResourceExhausted,
        ) => type_resource(span),
        crate::elaborate::TypeError::Internal(
            crate::elaborate::ElaborationFailure::ConstraintResourceExhausted,
        ) => resource(span),
        _ => invalid_root(span),
    }
}

pub(super) struct ValidatedProviderFamilySelection {
    pub(super) member: usize,
    pub(super) binder: crate::resolved::BinderId,
    pub(super) requirements: Box<[InterfaceApplication]>,
}

/// Reconstructs a concrete family dictionary from the original checked family
/// and the occurrence's complete owner actuals. A member index is only a locator.
#[allow(clippy::too_many_arguments)]
pub(super) fn validate_provider_family_selection(
    program: &ResolvedModuleProgram,
    source: &ResolvedProviderResourceExpr,
    selection: &crate::interface::EvidenceSelection,
    node: crate::interface::EvidenceNodeId,
    method: MethodId,
    budget: &mut InterfaceConstraintBudget,
    work: &mut TypeWorkBudget,
    span: Span,
) -> Result<ValidatedProviderFamilySelection, EvidenceValidationFailure> {
    let Some(crate::interface::EvidenceNode::ProviderFamily { source: candidate, definition, parameter, application, prerequisites, methods }) = selection.node(node) else {
        return Err(invalid_root(span));
    };
    charge(budget, methods.len(), span)?;
    let plan = source.prepared.get().ok_or_else(|| invalid_root(span))?;
    if candidate.module() != source.provider.module() || candidate == source.provider
        || source.family_provider != Some(candidate) || definition != source.definition
        || plan.definition().id != definition || !methods.contains(&method) { return Err(invalid_root(span)); }
    work.charge(program.registry().provider_contract_count()).map_err(|()| type_resource(span))?;
    let certificate = program.registry().provider_contracts().find(|(module, _)| **module == definition.module())
        .map(|(_, certificate)| certificate).ok_or_else(|| invalid_root(span))?;
    work.charge(certificate.resource_count()).map_err(|()| type_resource(span))?;
    let identity = certificate.family_identity(definition).ok_or_else(|| invalid_root(span))?;
    let header = certificate.family_provider_application(definition).ok_or_else(|| invalid_root(span))?;
    let declared = certificate.family_requirements(definition).ok_or_else(|| invalid_root(span))?;
    if identity.parameter != parameter || declared.len() != prerequisites.len()
        || plan.arguments().len() != plan.definition().parameters.len()
        || !certificate.resource_contracts().any(|(_, _, original)| std::ptr::eq(original.as_ref(), plan.definition())) {
        return Err(invalid_root(span));
    }
    let mut replacements = OwnerReplacements { types: HashMap::new(), rows: HashMap::new() };
    let count = plan.arguments().len().checked_add(1).ok_or_else(|| type_resource(span))?;
    work.charge(count).map_err(|()| type_resource(span))?;
    replacements.types.try_reserve(count).map_err(|_| type_resource(span))?;
    replacements.rows.try_reserve(count).map_err(|_| type_resource(span))?;
    for (formal, actual) in plan.definition().parameters.iter().zip(plan.arguments()) {
        let actual = clone_kinded_argument_with_budget(actual, work).map_err(|()| type_resource(span))?;
        if replacements.insert_discarding_previous(formal.id, actual) { return Err(invalid_root(span)); }
    }
    fn apply(application: &InterfaceApplication, replacements: &OwnerReplacements, work: &mut TypeWorkBudget, span: Span)
        -> Result<InterfaceApplication, EvidenceValidationFailure> {
        work.charge(application.arguments().len()).map_err(|()| type_resource(span))?;
        let mut arguments = FamilyArguments(Vec::new());
        arguments.0.try_reserve_exact(application.arguments().len()).map_err(|_| type_resource(span))?;
        for argument in application.arguments() {
            arguments.0.push(crate::types::substitute_kinded_argument_with(argument, &replacements.types, &replacements.rows,
                |units| work.charge(units)).map_err(|()| type_resource(span))?.map_err(|_| invalid_root(span))?);
        }
        Ok(InterfaceApplication::new_kinded(application.interface(), std::mem::take(&mut arguments.0).into_boxed_slice()))
    }
    let expected = apply(header, &replacements, work, span)?;
    charge(budget, expected.arguments().len().checked_add(application.arguments().len()).ok_or_else(|| resource(span))?, span)?;
    let mut pattern = Vec::new(); let mut goal = Vec::new();
    pattern.try_reserve_exact(expected.arguments().len()).map_err(|_| resource(span))?;
    goal.try_reserve_exact(application.arguments().len()).map_err(|_| resource(span))?;
    pattern.extend(expected.arguments()); goal.extend(application.arguments());
    if expected.interface() != application.interface() { return Err(invalid_root(span)); }
    let canonical = crate::interface::authenticate_implementation_application_goal(program.registry(),
        crate::interface::InterfaceOperationWork::new(span, budget, work), &goal)
        .map_err(|failure| family_match_failure(failure, span))?;
    let substitution = crate::interface::match_implementation_application_head_against_canonical_goal(program.registry(),
        crate::interface::InterfaceOperationWork::new(span, budget, work), &[parameter], &pattern, &canonical)
        .map_err(|failure| family_match_failure(failure, span))?.ok_or_else(|| invalid_root(span))?;
    let [substitution] = &*substitution else { return Err(invalid_root(span)); };
    if substitution.parameter() != parameter || !matches!(substitution.argument(), Type::Unit | Type::Bool | Type::Int) { return Err(invalid_root(span)); }
    if replacements.insert_discarding_previous(parameter, KindedArgument::TypeArg(crate::types::clone_type_with_budget(substitution.argument(), work)
        .map_err(|()| type_resource(span))?)) { return Err(invalid_root(span)); }
    work.charge(plan.family_members().len()).map_err(|()| type_resource(span))?;
    let mut selected = None;
    for (index, member) in plan.family_members().iter().enumerate() {
        if member.source() != candidate || member.identity() != identity { continue; }
        if same_application_parts_charged(member.application(), application.interface(), application.arguments(), budget, span)? {
            if selected.is_some() { return Err(invalid_root(span)); }
            selected = Some((index, member));
        }
    }
    let (member_index, member) = selected.ok_or_else(|| invalid_root(span))?;
    if member.requirements().len() != prerequisites.len() { return Err(invalid_root(span)); }
    charge(budget, prerequisites.len(), span)?;
    for ((retained, retained_node), actual) in member.requirements().iter().zip(prerequisites) {
        if retained_node != actual || actual.index() >= node.index() || !retained.shares_plan_with(selection) { return Err(invalid_root(span)); }
    }
    work.charge(program.groups().len()).map_err(|()| type_resource(span))?;
    let mut canonical_interface = None;
    for group in program.groups() {
        work.charge(group.interface_facts().len()).map_err(|()| type_resource(span))?;
        if let Some(interface) = group.interface_facts().iter().find(|interface| interface.id == application.interface()) {
            if canonical_interface.replace(interface.as_ref()).is_some() { return Err(invalid_root(span)); }
        }
    }
    let interface = canonical_interface.ok_or_else(|| invalid_root(span))?;
    charge(budget, interface.methods.len().checked_add(methods.len()).ok_or_else(|| resource(span))?, span)?;
    if methods.len() != interface.methods.len() || !methods.iter().copied().eq(interface.methods.iter().map(|method| method.id)) {
        return Err(invalid_root(span));
    }
    let mut binder = None;
    let mut actuals = member.forwarding_methods();
    let mut seen_binders = std::collections::HashSet::new();
    seen_binders.try_reserve(interface.methods.len()).map_err(|_| resource(span))?;
    for canonical in &interface.methods {
        let (candidate_method, candidate_binder, ty) = actuals.next().ok_or_else(|| invalid_root(span))?;
        if candidate_method != canonical.id || !matches!(candidate_binder, crate::resolved::BinderId::Generated(_))
            || !seen_binders.insert(candidate_binder) || !canonical.authoritative_type_parameters().is_empty()
            || !super::same_type_after_interface_substitution(canonical.value_type(), &interface.parameters,
                application.arguments(), ty, budget, span)? { return Err(invalid_root(span)); }
        if candidate_method == method { binder = Some(candidate_binder); }
    }
    if actuals.next().is_some() { return Err(invalid_root(span)); }
    let binder = binder.ok_or_else(|| invalid_root(span))?;
    work.charge(declared.len()).map_err(|()| type_resource(span))?;
    let mut requirements = Vec::new();
    requirements.try_reserve_exact(declared.len()).map_err(|_| type_resource(span))?;
    for (ordinal, requirement) in declared.iter().enumerate() {
        if requirement.id.owner() != crate::interface::RequirementOwner::ResourceFamily(definition)
            || usize::try_from(requirement.id.declaration()).ok() != Some(ordinal) { return Err(invalid_root(span)); }
        requirements.push(apply(requirement.application(), &replacements, work, span)?);
    }
    Ok(ValidatedProviderFamilySelection { member: member_index, binder, requirements: requirements.into_boxed_slice() })
}

fn family_match_failure(failure: crate::interface::HeadMatchFailure, span: Span) -> EvidenceValidationFailure {
    match failure {
        crate::interface::HeadMatchFailure::TypeResource => type_resource(span),
        crate::interface::HeadMatchFailure::ConstraintResource => resource(span),
        _ => invalid_root(span),
    }
}

struct FamilyArguments(Vec<KindedArgument>);
impl Drop for FamilyArguments {
    fn drop(&mut self) {
        for argument in self.0.drain(..) { crate::types::discard_kinded_argument_iteratively(argument); }
    }
}
