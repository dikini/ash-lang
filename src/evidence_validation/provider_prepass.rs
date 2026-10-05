//! Bounded inventory of original source occurrences for final provider copying.

use super::{EvidenceValidationFailure, invalid_root, type_resource};
use crate::{
    resolved::{
        ResolvedDefinitionKind, ResolvedExpr, ResolvedExprKind, ResolvedLocalDeclaration,
        ResolvedModuleProgram,
    },
    source::Span,
    types::TypeWorkBudget,
};
use std::collections::HashSet;

pub(crate) struct SourceProviderOccurrence<'a> {
    pub(crate) resource: &'a crate::resolved::ResolvedProviderResourceExpr,
    pub(crate) span: Span,
}

enum SourceItem<'a> {
    Expression(&'a ResolvedExpr),
    Block(&'a crate::resolved::ResolvedBlock),
    Declaration(&'a ResolvedLocalDeclaration),
}

/// Inventories original occurrences before allocating any final copy identity.
/// It uses checked source bodies, including implementation and lexical method
/// bodies; defining templates are preparation authorities, not source instances.
pub(crate) fn source_provider_occurrences<'a>(
    program: &'a ResolvedModuleProgram,
    work: &mut TypeWorkBudget,
) -> Result<Vec<SourceProviderOccurrence<'a>>, EvidenceValidationFailure> {
    let span = program.result().span;
    // Without an admitted defining family no source provider instance can have
    // passed module checking. Keep the ordinary pipeline's prior work path.
    if program.registry().provider_contract_count() == 0 {
        return Ok(Vec::new());
    }
    let mut pending = Vec::new();
    push(
        &mut pending,
        SourceItem::Expression(program.result()),
        work,
        span,
    )?;
    for group in program.groups() {
        work.charge(1).map_err(|()| type_resource(group.span()))?;
        for definition in group.definitions() {
            match definition.kind() {
                ResolvedDefinitionKind::Equational(global) => {
                    for equation in &global.equations {
                        push(
                            &mut pending,
                            SourceItem::Expression(&equation.body),
                            work,
                            equation.span,
                        )?;
                    }
                }
                ResolvedDefinitionKind::InlineOperational(global) => {
                    push(
                        &mut pending,
                        SourceItem::Block(&global.body),
                        work,
                        global.body.span,
                    )?;
                }
            }
        }
        for implementation in group.implementations() {
            for method in implementation.method_groups() {
                for equation in &method.equations {
                    push(
                        &mut pending,
                        SourceItem::Expression(&equation.body),
                        work,
                        equation.span,
                    )?;
                }
            }
        }
    }
    let mut output = Vec::new();
    let mut identities = HashSet::new();
    while let Some(item) = pending.pop() {
        work.charge(1).map_err(|()| type_resource(span))?;
        match item {
            SourceItem::Block(block) => {
                push(
                    &mut pending,
                    SourceItem::Expression(&block.result),
                    work,
                    block.span,
                )?;
                for declaration in &block.declarations {
                    push(
                        &mut pending,
                        SourceItem::Declaration(declaration),
                        work,
                        block.span,
                    )?;
                }
            }
            SourceItem::Declaration(ResolvedLocalDeclaration::Binding(binding)) => {
                push(
                    &mut pending,
                    SourceItem::Expression(&binding.initializer),
                    work,
                    binding.span,
                )?;
            }
            SourceItem::Declaration(ResolvedLocalDeclaration::Recursive(group)) => {
                for member in &group.members {
                    push(
                        &mut pending,
                        SourceItem::Expression(&member.initializer),
                        work,
                        group.span,
                    )?;
                }
            }
            SourceItem::Declaration(ResolvedLocalDeclaration::Evidence(source)) => {
                for method in &source.method_groups {
                    for equation in &method.equations {
                        push(
                            &mut pending,
                            SourceItem::Expression(&equation.body),
                            work,
                            equation.span,
                        )?;
                    }
                }
            }
            SourceItem::Declaration(ResolvedLocalDeclaration::Newtype(_)) => {}
            SourceItem::Expression(expression) => match &expression.kind {
                ResolvedExprKind::ProviderResource(resource) => {
                    work.charge(2)
                        .map_err(|()| type_resource(expression.span))?;
                    if resource.prepared.get().is_none() || identities.contains(&resource.provider)
                    {
                        return Err(invalid_root(expression.span));
                    }
                    output
                        .try_reserve(1)
                        .map_err(|_| type_resource(expression.span))?;
                    identities
                        .try_reserve(1)
                        .map_err(|_| type_resource(expression.span))?;
                    identities.insert(resource.provider);
                    output.push(SourceProviderOccurrence {
                        resource,
                        span: expression.span,
                    });
                    push(
                        &mut pending,
                        SourceItem::Expression(&resource.body),
                        work,
                        expression.span,
                    )?;
                    push(
                        &mut pending,
                        SourceItem::Expression(&resource.initializer),
                        work,
                        expression.span,
                    )?;
                }
                ResolvedExprKind::Block(block) => push(
                    &mut pending,
                    SourceItem::Block(block),
                    work,
                    expression.span,
                )?,
                ResolvedExprKind::Function(function) => push(
                    &mut pending,
                    SourceItem::Block(&function.body),
                    work,
                    expression.span,
                )?,
                ResolvedExprKind::Apply(application) => {
                    push(
                        &mut pending,
                        SourceItem::Expression(&application.argument),
                        work,
                        expression.span,
                    )?;
                    push(
                        &mut pending,
                        SourceItem::Expression(&application.function),
                        work,
                        expression.span,
                    )?;
                }
                ResolvedExprKind::Tuple(elements) => {
                    for element in elements {
                        push(
                            &mut pending,
                            SourceItem::Expression(element),
                            work,
                            expression.span,
                        )?;
                    }
                }
                ResolvedExprKind::Add(binary)
                | ResolvedExprKind::Multiply(binary)
                | ResolvedExprKind::Equal(binary) => {
                    push(
                        &mut pending,
                        SourceItem::Expression(&binary.left),
                        work,
                        expression.span,
                    )?;
                    push(
                        &mut pending,
                        SourceItem::Expression(&binary.right),
                        work,
                        expression.span,
                    )?;
                }
                ResolvedExprKind::Match(matched) => {
                    push(
                        &mut pending,
                        SourceItem::Expression(&matched.scrutinee),
                        work,
                        expression.span,
                    )?;
                    for arm in &matched.arms {
                        push(
                            &mut pending,
                            SourceItem::Expression(&arm.body),
                            work,
                            expression.span,
                        )?;
                    }
                }
                ResolvedExprKind::Resource(resource) => {
                    push(
                        &mut pending,
                        SourceItem::Expression(&resource.body),
                        work,
                        expression.span,
                    )?;
                    push(
                        &mut pending,
                        SourceItem::Expression(&resource.initializer),
                        work,
                        expression.span,
                    )?;
                }
                ResolvedExprKind::Cleanup(cleanup) => {
                    push(
                        &mut pending,
                        SourceItem::Expression(&cleanup.body),
                        work,
                        expression.span,
                    )?;
                    push(
                        &mut pending,
                        SourceItem::Expression(&cleanup.action),
                        work,
                        expression.span,
                    )?;
                }
                ResolvedExprKind::Perform(request) => push(
                    &mut pending,
                    SourceItem::Expression(&request.operand),
                    work,
                    expression.span,
                )?,
                ResolvedExprKind::Handle(handler) => {
                    push(
                        &mut pending,
                        SourceItem::Expression(&handler.body),
                        work,
                        expression.span,
                    )?;
                    for clause in &handler.clauses {
                        push(
                            &mut pending,
                            SourceItem::Expression(&clause.body),
                            work,
                            expression.span,
                        )?;
                    }
                }
                ResolvedExprKind::Resume(resume) => push(
                    &mut pending,
                    SourceItem::Expression(&resume.value),
                    work,
                    expression.span,
                )?,
                ResolvedExprKind::Integer(_)
                | ResolvedExprKind::Boolean(_)
                | ResolvedExprKind::Unit
                | ResolvedExprKind::Occurrence(_)
                | ResolvedExprKind::Constructor(_)
                | ResolvedExprKind::Discard(_) => {}
            },
        }
    }
    Ok(output)
}

fn push<'a>(
    pending: &mut Vec<SourceItem<'a>>,
    item: SourceItem<'a>,
    work: &mut TypeWorkBudget,
    span: Span,
) -> Result<(), EvidenceValidationFailure> {
    work.charge(1).map_err(|()| type_resource(span))?;
    pending.try_reserve(1).map_err(|_| type_resource(span))?;
    pending.push(item);
    Ok(())
}
