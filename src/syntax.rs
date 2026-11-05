//! Expansion of checked expression templates before ordinary resolution.

use crate::{
    source::Span,
    surface::{
        SurfaceBlock, SurfaceDefinitionKind, SurfaceExpr, SurfaceExprKind, SurfaceLocalDeclaration,
        SurfaceModule, SurfaceSyntaxDeclaration,
    },
};

pub(crate) struct SelectedSyntax {
    pub(crate) name: String,
    pub(crate) declaration: SurfaceSyntaxDeclaration,
}

/// Reject forms that still need definition-site binding and authority.
pub(crate) fn validate_template(declaration: &SurfaceSyntaxDeclaration) -> Result<(), Span> {
    fn check(expression: &SurfaceExpr, capture: &str) -> Result<(), Span> {
        match &expression.kind {
            SurfaceExprKind::TemplateSplice(name) if name.text == capture => Ok(()),
            SurfaceExprKind::Integer(_)
            | SurfaceExprKind::String(_)
            | SurfaceExprKind::Boolean(_)
            | SurfaceExprKind::Unit => Ok(()),
            SurfaceExprKind::Tuple(elements) => {
                for element in elements {
                    check(element, capture)?;
                }
                Ok(())
            }
            SurfaceExprKind::Apply(application) => {
                check(&application.function, capture)?;
                check(&application.argument, capture)
            }
            SurfaceExprKind::Multiply(binary)
            | SurfaceExprKind::Add(binary)
            | SurfaceExprKind::Equal(binary) => {
                check(&binary.left, capture)?;
                check(&binary.right, capture)
            }
            SurfaceExprKind::Block(block) if block.declarations.is_empty() => {
                check(&block.result, capture)
            }
            _ => Err(expression.span),
        }
    }
    check(&declaration.template, &declaration.capture.text)
}

fn substitute(expression: &mut SurfaceExpr, capture: &SurfaceExpr) -> Result<(), Span> {
    match &mut expression.kind {
        SurfaceExprKind::TemplateSplice(_) => *expression = capture.clone(),
        SurfaceExprKind::Tuple(elements) => {
            for element in elements {
                substitute(element, capture)?;
            }
        }
        SurfaceExprKind::Apply(application) => {
            substitute(&mut application.function, capture)?;
            substitute(&mut application.argument, capture)?;
        }
        SurfaceExprKind::Multiply(binary)
        | SurfaceExprKind::Add(binary)
        | SurfaceExprKind::Equal(binary) => {
            substitute(&mut binary.left, capture)?;
            substitute(&mut binary.right, capture)?;
        }
        SurfaceExprKind::Block(block) if block.declarations.is_empty() => {
            substitute(&mut block.result, capture)?;
        }
        SurfaceExprKind::Integer(_)
        | SurfaceExprKind::String(_)
        | SurfaceExprKind::Boolean(_)
        | SurfaceExprKind::Unit => {}
        _ => return Err(expression.span),
    }
    Ok(())
}

pub(crate) fn expand_module(
    module: &mut SurfaceModule,
    selected: &[SelectedSyntax],
) -> Result<(), Span> {
    for definition in &mut module.definitions {
        match &mut definition.kind {
            SurfaceDefinitionKind::Equational(global) => {
                for equation in &mut global.equations {
                    expand_expression(&mut equation.body, selected)?;
                }
            }
            SurfaceDefinitionKind::InlineOperational(global) => {
                expand_block(&mut global.body, selected)?;
            }
        }
    }
    for implementation in &mut module.implementations {
        for equation in &mut implementation.equations {
            expand_expression(&mut equation.body, selected)?;
        }
    }
    for resource in &mut module.resources {
        expand_expression(&mut resource.acquire, selected)?;
        expand_expression(&mut resource.finish, selected)?;
        for clause in &mut resource.handlers {
            expand_expression(&mut clause.body, selected)?;
        }
        if let Some(family) = &mut resource.family {
            for clause in &mut family.handlers {
                expand_expression(&mut clause.body, selected)?;
            }
        }
    }
    Ok(())
}

fn expand_block(block: &mut SurfaceBlock, selected: &[SelectedSyntax]) -> Result<(), Span> {
    for declaration in &mut block.declarations {
        match declaration {
            SurfaceLocalDeclaration::Evidence(evidence) => {
                for equation in &mut evidence.equations {
                    expand_expression(&mut equation.body, selected)?;
                }
            }
            SurfaceLocalDeclaration::Binding(binding) => {
                expand_expression(&mut binding.initializer, selected)?;
            }
            SurfaceLocalDeclaration::Recursive(group) => {
                for member in &mut group.members {
                    expand_expression(&mut member.initializer, selected)?;
                }
            }
            SurfaceLocalDeclaration::Newtype(_) => {}
        }
    }
    expand_expression(&mut block.result, selected)
}

fn expand_expression(
    expression: &mut SurfaceExpr,
    selected: &[SelectedSyntax],
) -> Result<(), Span> {
    match &mut expression.kind {
        SurfaceExprKind::SyntaxInvocation { name, capture } => {
            let invocation = expression.span;
            let declaration = selected
                .iter()
                .find(|syntax| syntax.name == name.text)
                .map(|syntax| &syntax.declaration)
                .ok_or(expression.span)?;
            let mut replacement = declaration.template.clone();
            substitute(&mut replacement, capture)?;
            // The complete expansion occupies the invocation in the caller.
            // Its children keep their own capture and template source spans.
            replacement.span = invocation;
            if let SurfaceExprKind::Block(block) = &mut replacement.kind {
                block.span = invocation;
            }
            *expression = replacement;
            return expand_expression(expression, selected);
        }
        SurfaceExprKind::TemplateSplice(_) => return Err(expression.span),
        SurfaceExprKind::Integer(_)
        | SurfaceExprKind::String(_)
        | SurfaceExprKind::Boolean(_)
        | SurfaceExprKind::Unit
        | SurfaceExprKind::Name(_)
        | SurfaceExprKind::Discard
        | SurfaceExprKind::Retain => {}
        SurfaceExprKind::Tuple(elements) => {
            for element in elements {
                expand_expression(element, selected)?;
            }
        }
        SurfaceExprKind::Apply(application) => {
            expand_expression(&mut application.function, selected)?;
            expand_expression(&mut application.argument, selected)?;
        }
        SurfaceExprKind::Multiply(binary)
        | SurfaceExprKind::Add(binary)
        | SurfaceExprKind::Equal(binary) => {
            expand_expression(&mut binary.left, selected)?;
            expand_expression(&mut binary.right, selected)?;
        }
        SurfaceExprKind::Block(block) => expand_block(block, selected)?,
        SurfaceExprKind::Function(function) => expand_block(&mut function.body, selected)?,
        SurfaceExprKind::Match(matching) => {
            expand_expression(&mut matching.scrutinee, selected)?;
            for arm in &mut matching.arms {
                expand_expression(&mut arm.body, selected)?;
            }
        }
        SurfaceExprKind::Perform(perform) => expand_expression(&mut perform.operand, selected)?,
        SurfaceExprKind::Handle(handler) => {
            expand_expression(&mut handler.body, selected)?;
            if let Some(store) = &mut handler.store {
                expand_expression(store, selected)?;
            }
            for clause in &mut handler.clauses {
                expand_expression(&mut clause.body, selected)?;
            }
        }
        SurfaceExprKind::Resume(value) => expand_expression(value, selected)?,
        SurfaceExprKind::Resource(resource) => {
            expand_expression(&mut resource.initializer, selected)?;
            expand_block(&mut resource.body, selected)?;
        }
        SurfaceExprKind::Region(region) => {
            if let Some(provider) = &mut region.provider {
                expand_expression(provider, selected)?;
            }
            expand_block(&mut region.body, selected)?;
        }
        SurfaceExprKind::RegionSelection(selection) => {
            expand_expression(&mut selection.region, selected)?;
            expand_block(&mut selection.body, selected)?;
        }
        SurfaceExprKind::ProviderResource(resource) => {
            expand_expression(&mut resource.initializer, selected)?;
            expand_block(&mut resource.body, selected)?;
        }
        SurfaceExprKind::Hook(hook) => expand_block(&mut hook.body, selected)?,
        SurfaceExprKind::Registration(registration) => {
            expand_expression(&mut registration.transformer, selected)?;
            expand_block(&mut registration.body, selected)?;
        }
        SurfaceExprKind::Cleanup(cleanup) => {
            expand_expression(&mut cleanup.action, selected)?;
            expand_block(&mut cleanup.body, selected)?;
        }
    }
    Ok(())
}
