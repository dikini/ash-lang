//! Original ordinary lexical context and row qualification.
use super::{
    EvidenceScope, EvidenceValidationFailure, ExpectedEquation, LinkedInterfaceRegistry,
    LinkedLocalScope, OwnerReplacements, charge, invalid_root, same_argument_charged,
    type_resource, unknown,
};
use crate::{
    interface::{InterfaceApplication, InterfaceConstraintBudget},
    resolved::ResolvedModuleProgram,
    source::Span,
    types::{
        EffectRowVariable, IterativeTypeOwner, Kind, KindedArgument, Type, TypeWorkBudget,
        clone_kinded_argument_with_budget, substitute_type_and_row_variables_with,
    },
};
use std::collections::HashMap;
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
}
impl<'a> LinkedLexicalSource<'a> {
    pub(super) fn id(self) -> crate::interface::LexicalEvidenceId {
        match self {
            Self::Declared(source, _) => source.id,
        }
    }
    pub(super) fn application(
        self,
        span: Span,
    ) -> Result<&'a InterfaceApplication, EvidenceValidationFailure> {
        match self {
            Self::Declared(source, _) => source.checked.get().map(|checked| &checked.application),
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
        }
    }
}

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
