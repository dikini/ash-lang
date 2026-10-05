//! Source-side authentication of sealed forwarding dictionaries. This borrows
//! checked preparation; executable scope authority is admitted independently.
use super::{
    EvidenceScope, EvidenceValidationFailure, LinkedInterfaceRegistry, OwnerReplacements, charge,
    invalid_root, linked_selection_key_types, map_kind_constraint_failure, map_kind_type_failure,
    resource, same_application_parts_charged, same_argument_charged,
    same_source_application_charged, same_type_charged, type_resource, unknown,
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
        IterativeTypeOwner, Kind, KindedArgument, Type, TypeWorkBudget,
        clone_kinded_argument_with_budget, substitute_type_and_row_variables_with,
    },
};
use std::collections::HashMap;

#[derive(Clone, Copy)]
pub(super) enum LinkedLexicalSource<'a> {
    Declared(&'a crate::resolved::ResolvedLexicalEvidence),
    Provider(&'a ResolvedProviderResourceExpr),
}
impl<'a> LinkedLexicalSource<'a> {
    pub(super) fn id(self) -> crate::interface::LexicalEvidenceId {
        match self {
            Self::Declared(source) => source.id,
            Self::Provider(source) => source.provider,
        }
    }
    pub(super) fn application(
        self,
        span: Span,
    ) -> Result<&'a InterfaceApplication, EvidenceValidationFailure> {
        match self {
            Self::Declared(source) => source.checked.get().map(|checked| &checked.application),
            Self::Provider(source) => source
                .prepared
                .get()
                .map(|plan| plan.forwarding_application()),
        }
        .ok_or_else(|| invalid_root(span))
    }
    pub(super) fn same_application(
        self,
        application: &InterfaceApplication,
        budget: &mut InterfaceConstraintBudget,
        span: Span,
    ) -> Result<bool, EvidenceValidationFailure> {
        match self {
            Self::Declared(source) => {
                same_source_application_charged(application, &source.application, budget, span)
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
        for (written, actual) in arguments.iter().zip(plan.arguments().iter().skip(1)) {
            if !same_argument_charged(&written.ty, actual, budget, span)? {
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
