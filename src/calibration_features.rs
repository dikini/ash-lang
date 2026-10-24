//! Diagnostic input metrics collected before resolution or inference.
//!
//! Each loaded module contributes once, including builtin and foreign source.
//! `nodes` counts visited structural surface records: modules, imports and
//! selectors, declarations, constructor and method records, equations, explicit
//! parameters, expressions, blocks, local declarations and recursive members,
//! patterns, types, kinds, rows, effect instances, and interface applications.
//! Names, references, spans, visibility tags, and declaration-order indices do
//! not add nodes. `binders` counts written type parameters only; it excludes
//! implicit quantification and term binders. `scope_depth` counts nested
//! `SurfaceBlock` records, not all semantic binder scopes. All type metrics
//! describe written syntax, never substitutions or inferred types.

use std::collections::HashMap;

use serde::Serialize;
use sha2::{Digest, Sha256};

use crate::{
    module::ModuleGraph,
    surface::{
        SurfaceBlock, SurfaceDefinition, SurfaceDefinitionKind, SurfaceEffectInstance,
        SurfaceEffectRow, SurfaceEquation, SurfaceExpr, SurfaceExprKind, SurfaceHandlerClause,
        SurfaceImportSelection, SurfaceInterfaceApplication, SurfaceKind, SurfaceKindKind,
        SurfaceLocalDeclaration, SurfaceModule, SurfacePattern, SurfacePatternKind, SurfaceType,
        SurfaceTypeDeclaration, SurfaceTypeKind, SurfaceTypeParameter,
    },
};

#[derive(Default, Serialize)]
struct Features {
    bytes: usize,
    modules: usize,
    nodes: usize,
    type_nodes: usize,
    type_depth: usize,
    kind_nodes: usize,
    kind_depth: usize,
    row_nodes: usize,
    effect_instances: usize,
    binders: usize,
    requirements: usize,
    interface_members: usize,
    imports: usize,
    import_selectors: usize,
    dependency_edges: usize,
    module_depth: usize,
    resource_definitions: usize,
    resource_sites: usize,
    scope_depth: usize,
    definitions: usize,
    type_declarations: usize,
    interfaces: usize,
    implementations: usize,
    effects: usize,
    expressions: usize,
    patterns: usize,
    applications: usize,
    functions: usize,
    matches: usize,
    handlers: usize,
    literal_string_bytes: usize,
}

enum Visit<'a> {
    Nominal(&'a SurfaceTypeDeclaration),
    Definition(&'a SurfaceDefinition),
    Equation(&'a SurfaceEquation, usize),
    Block(&'a SurfaceBlock, usize),
    Local(&'a SurfaceLocalDeclaration, usize),
    Expr(&'a SurfaceExpr, usize),
    Pattern(&'a SurfacePattern),
    Type(&'a SurfaceType, usize),
    Kind(&'a SurfaceKind, usize),
    Parameter(&'a SurfaceTypeParameter),
    Row(&'a SurfaceEffectRow, usize),
    Effect(&'a SurfaceEffectInstance, usize),
    Application(&'a SurfaceInterfaceApplication, bool),
    Handler(&'a SurfaceHandlerClause, usize),
}

/// Emits one immutable source-graph feature record for the calibration harness.
/// The caller places this entire observation in a separate metrics phase.
pub(crate) fn observe_input(graph: &ModuleGraph) {
    let mut features = Features::default();
    let mut sources = Vec::with_capacity(graph.modules().len());
    let mut depths = HashMap::with_capacity(graph.modules().len());
    let mut pending = Vec::new();

    for module in graph.modules() {
        let source = module.source().text();
        features.bytes += source.len();
        features.modules += 1;
        sources.push(serde_json::json!({
            "path": module.canonical_path().to_string_lossy(),
            "bytes": source.len(),
            "sha256": format!("{:x}", Sha256::digest(source.as_bytes())),
        }));
        // Loaded graphs are ordered with dependencies before their dependents.
        // A source with no dependencies has depth one.
        let depth = module
            .dependencies()
            .iter()
            .filter_map(|edge| depths.get(&edge.target()).copied())
            .max()
            .unwrap_or(0_usize)
            + 1;
        depths.insert(module.id(), depth);
        features.module_depth = features.module_depth.max(depth);
        features.dependency_edges += module.dependencies().len();
        seed_module(module.surface(), &mut features, &mut pending);
        walk(&mut features, &mut pending);
    }

    eprintln!(
        "ASH_CALIBRATION {}",
        serde_json::json!({
            "event": "input",
            "schema": "surface-input-v1",
            "features": features,
            "sources": sources,
            "omissions": ["implicit type binders", "term binders", "reference/name nodes"],
            "scope_depth_basis": "nested SurfaceBlock records",
            "module_depth_basis": "dependency path in module vertices; leaf is one",
        })
    );
}

fn seed_module<'a>(
    module: &'a SurfaceModule,
    features: &mut Features,
    pending: &mut Vec<Visit<'a>>,
) {
    features.nodes += 1;
    features.imports += module.imports.len();
    features.nodes += module.imports.len();
    for import in &module.imports {
        if let SurfaceImportSelection::Targeted(selectors) = &import.selection {
            features.import_selectors += selectors.len();
            features.nodes += selectors.len();
        }
    }
    pending.extend(module.type_declarations.iter().map(Visit::Nominal));
    pending.extend(module.definitions.iter().map(Visit::Definition));
    features.interfaces += module.interfaces.len();
    features.nodes += module.interfaces.len();
    for interface in &module.interfaces {
        pending.extend(interface.parameters.iter().map(Visit::Parameter));
        if interface.determination.is_some() {
            // The determination record and its two side records.
            features.nodes += 3;
        }
        features.interface_members += interface.methods.len();
        features.nodes += interface.methods.len();
        for method in &interface.methods {
            if let Some(parameters) = &method.type_parameters {
                pending.extend(parameters.iter().map(Visit::Parameter));
            }
            pending.push(Visit::Type(&method.annotation, 1));
        }
    }
    features.effects += module.effects.len();
    features.nodes += module.effects.len();
    for effect in &module.effects {
        pending.extend(effect.parameters.iter().map(Visit::Parameter));
        features.interface_members += effect.operations.len();
        features.nodes += effect.operations.len();
        pending.extend(
            effect
                .operations
                .iter()
                .map(|operation| Visit::Type(&operation.annotation, 1)),
        );
    }
    features.implementations += module.implementations.len();
    features.nodes += module.implementations.len();
    for implementation in &module.implementations {
        if let Some(parameters) = &implementation.type_parameters {
            pending.extend(parameters.iter().map(Visit::Parameter));
        }
        pending.push(Visit::Application(&implementation.head, false));
        pending.extend(
            implementation
                .prerequisites
                .iter()
                .map(|requirement| Visit::Application(requirement, true)),
        );
        pending.extend(
            implementation
                .equations
                .iter()
                .map(|equation| Visit::Equation(equation, 0)),
        );
    }
    features.resource_definitions += module.resources.len();
    features.nodes += module.resources.len();
    for resource in &module.resources {
        pending.extend(resource.parameters.iter().map(Visit::Parameter));
        pending.push(Visit::Parameter(&resource.answer));
        pending.push(Visit::Type(&resource.input, 1));
        pending.push(Visit::Type(&resource.state, 1));
        pending.push(Visit::Type(&resource.result, 1));
        pending.push(Visit::Application(&resource.provider, true));
        pending.push(Visit::Effect(&resource.provided, 1));
        pending.push(Visit::Effect(&resource.interpreted, 1));
        pending.push(Visit::Expr(&resource.acquire, 0));
        pending.push(Visit::Expr(&resource.finish, 0));
        pending.extend(
            resource
                .handlers
                .iter()
                .map(|handler| Visit::Handler(handler, 0)),
        );
    }
    features.resource_definitions += module.source_resources.len();
    features.nodes += module.source_resources.len();
    for resource in &module.source_resources {
        pending.extend(resource.parameters.iter().map(Visit::Parameter));
        pending.extend(resource.result_parameters.iter().map(Visit::Parameter));
        for ty in [
            &resource.input,
            &resource.state,
            &resource.data,
            &resource.acquisition,
            &resource.completion,
            &resource.result,
            &resource.provider,
        ] {
            pending.push(Visit::Type(ty, 1));
        }
        pending.push(Visit::Effect(&resource.provided, 1));
        pending.extend(
            resource
                .interpreted
                .iter()
                .map(|effect| Visit::Effect(effect, 1)),
        );
        for pattern in [
            &resource.acquire_pattern,
            &resource.finish_pattern,
            &resource.handlers_pattern,
        ] {
            pending.push(Visit::Pattern(pattern));
        }
        pending.push(Visit::Expr(&resource.acquire, 0));
        pending.push(Visit::Expr(&resource.finish, 0));
        pending.extend(
            resource
                .handlers
                .iter()
                .map(|handler| Visit::Handler(handler, 0)),
        );
    }
}

fn walk<'a>(features: &mut Features, pending: &mut Vec<Visit<'a>>) {
    while let Some(visit) = pending.pop() {
        features.nodes += 1;
        match visit {
            Visit::Nominal(declaration) => {
                features.type_declarations += 1;
                pending.extend(declaration.parameters.iter().map(Visit::Parameter));
                features.nodes += declaration.constructors.len();
                for constructor in &declaration.constructors {
                    pending.extend(constructor.fields.iter().map(|ty| Visit::Type(ty, 1)));
                }
            }
            Visit::Definition(definition) => {
                features.definitions += 1;
                match &definition.kind {
                    SurfaceDefinitionKind::Equational(global) => {
                        if let Some(parameters) = &global.interface.type_parameters {
                            pending.extend(parameters.iter().map(Visit::Parameter));
                        }
                        pending.push(Visit::Type(&global.interface.annotation, 1));
                        pending.extend(
                            global
                                .interface
                                .requirements
                                .iter()
                                .map(|requirement| Visit::Application(requirement, true)),
                        );
                        pending.extend(
                            global
                                .equations
                                .iter()
                                .map(|equation| Visit::Equation(equation, 0)),
                        );
                    }
                    SurfaceDefinitionKind::InlineOperational(global) => {
                        if let Some(parameters) = &global.header.type_parameters {
                            pending.extend(parameters.iter().map(Visit::Parameter));
                        }
                        features.nodes += global.header.parameters.len();
                        for parameter in &global.header.parameters {
                            pending.push(Visit::Pattern(&parameter.pattern));
                            pending.push(Visit::Type(&parameter.annotation, 1));
                        }
                        pending.push(Visit::Type(&global.header.result_type, 1));
                        if let Some(row) = &global.header.result_effects {
                            pending.push(Visit::Row(row, 1));
                        }
                        pending.extend(
                            global
                                .header
                                .requirements
                                .iter()
                                .map(|requirement| Visit::Application(requirement, true)),
                        );
                        pending.push(Visit::Block(&global.body, 0));
                    }
                }
            }
            Visit::Equation(equation, scope) => {
                pending.extend(equation.patterns.iter().map(Visit::Pattern));
                pending.push(Visit::Expr(&equation.body, scope));
            }
            Visit::Block(block, scope) => {
                let scope = scope + 1;
                features.scope_depth = features.scope_depth.max(scope);
                pending.extend(
                    block
                        .declarations
                        .iter()
                        .map(|declaration| Visit::Local(declaration, scope)),
                );
                pending.push(Visit::Expr(&block.result, scope));
            }
            Visit::Local(declaration, scope) => match declaration {
                SurfaceLocalDeclaration::Evidence(evidence) => {
                    pending.push(Visit::Application(&evidence.application, true));
                    pending.extend(
                        evidence
                            .equations
                            .iter()
                            .map(|equation| Visit::Equation(equation, scope)),
                    );
                }
                SurfaceLocalDeclaration::Binding(binding) => {
                    pending.push(Visit::Pattern(&binding.pattern));
                    if let Some(annotation) = &binding.annotation {
                        pending.push(Visit::Type(annotation, 1));
                    }
                    pending.push(Visit::Expr(&binding.initializer, scope));
                }
                SurfaceLocalDeclaration::Recursive(group) => {
                    features.nodes += group.members.len();
                    for member in &group.members {
                        pending.push(Visit::Type(&member.annotation, 1));
                        pending.push(Visit::Expr(&member.initializer, scope));
                    }
                }
                SurfaceLocalDeclaration::Newtype(declaration) => {
                    pending.push(Visit::Nominal(declaration));
                }
            },
            Visit::Expr(expression, scope) => {
                features.expressions += 1;
                match &expression.kind {
                    SurfaceExprKind::String(value) => {
                        features.literal_string_bytes += value.len();
                    }
                    SurfaceExprKind::Integer(_)
                    | SurfaceExprKind::Boolean(_)
                    | SurfaceExprKind::Unit
                    | SurfaceExprKind::Name(_)
                    | SurfaceExprKind::Discard => {}
                    SurfaceExprKind::Tuple(elements) => {
                        pending.extend(elements.iter().map(|value| Visit::Expr(value, scope)));
                    }
                    SurfaceExprKind::Apply(application) => {
                        features.applications += 1;
                        pending.push(Visit::Expr(&application.function, scope));
                        pending.push(Visit::Expr(&application.argument, scope));
                    }
                    SurfaceExprKind::Multiply(binary)
                    | SurfaceExprKind::Add(binary)
                    | SurfaceExprKind::Equal(binary) => {
                        pending.push(Visit::Expr(&binary.left, scope));
                        pending.push(Visit::Expr(&binary.right, scope));
                    }
                    SurfaceExprKind::Block(block) => pending.push(Visit::Block(block, scope)),
                    SurfaceExprKind::Function(function) => {
                        features.functions += 1;
                        pending.push(Visit::Pattern(&function.parameter));
                        pending.push(Visit::Block(&function.body, scope));
                    }
                    SurfaceExprKind::Match(matching) => {
                        features.matches += 1;
                        pending.push(Visit::Expr(&matching.scrutinee, scope));
                        features.nodes += matching.arms.len();
                        for arm in &matching.arms {
                            pending.push(Visit::Pattern(&arm.pattern));
                            pending.push(Visit::Expr(&arm.body, scope));
                        }
                    }
                    SurfaceExprKind::Perform(perform) => {
                        pending.extend(perform.arguments.iter().map(|ty| Visit::Type(ty, 1)));
                        pending.push(Visit::Expr(&perform.operand, scope));
                    }
                    SurfaceExprKind::Handle(handler) => {
                        features.handlers += 1;
                        pending.push(Visit::Expr(&handler.body, scope));
                        pending.push(Visit::Effect(&handler.effect, 1));
                        pending.extend(
                            handler
                                .clauses
                                .iter()
                                .map(|clause| Visit::Handler(clause, scope)),
                        );
                    }
                    SurfaceExprKind::Resume(operand) => {
                        pending.push(Visit::Expr(operand, scope));
                    }
                    SurfaceExprKind::Resource(resource) => {
                        features.resource_sites += 1;
                        pending.push(Visit::Expr(&resource.initializer, scope));
                        pending.push(Visit::Block(&resource.body, scope));
                    }

                    SurfaceExprKind::CopyWindow(window) => {
                        pending.push(Visit::Type(&window.family, 1));
                        pending.push(Visit::Expr(&window.state, scope));
                        pending.push(Visit::Block(&window.body, scope));
                    }
                    SurfaceExprKind::ProviderResource(resource) => {
                        features.resource_sites += 1;
                        pending.extend(resource.arguments.iter().map(|ty| Visit::Type(ty, 1)));
                        pending.push(Visit::Expr(&resource.initializer, scope));
                        pending.push(Visit::Block(&resource.body, scope));
                    }
                    SurfaceExprKind::Hook(hook) => {
                        pending.push(Visit::Effect(&hook.effect, 1));
                        pending.push(Visit::Block(&hook.body, scope));
                    }
                    SurfaceExprKind::Registration(registration) => {
                        pending.push(Visit::Effect(&registration.effect, 1));
                        pending.push(Visit::Expr(&registration.transformer, scope));
                        pending.push(Visit::Block(&registration.body, scope));
                    }
                    SurfaceExprKind::Cleanup(cleanup) => {
                        pending.push(Visit::Expr(&cleanup.action, scope));
                        pending.push(Visit::Block(&cleanup.body, scope));
                    }
                }
            }
            Visit::Pattern(pattern) => {
                features.patterns += 1;
                match &pattern.kind {
                    SurfacePatternKind::Tuple(elements) => {
                        pending.extend(elements.iter().map(Visit::Pattern));
                    }
                    SurfacePatternKind::Constructor { payload, .. } => {
                        if let Some(payload) = payload {
                            pending.push(Visit::Pattern(payload));
                        }
                    }
                    SurfacePatternKind::Binder(_)
                    | SurfacePatternKind::Wildcard
                    | SurfacePatternKind::Boolean(_)
                    | SurfacePatternKind::Unit => {}
                }
            }
            Visit::Type(ty, depth) => {
                features.type_nodes += 1;
                features.type_depth = features.type_depth.max(depth);
                match &ty.kind {
                    SurfaceTypeKind::RowArgument(row) => {
                        pending.push(Visit::Row(row, depth + 1));
                    }
                    SurfaceTypeKind::Application { arguments, .. }
                    | SurfaceTypeKind::Tuple(arguments) => {
                        pending.extend(arguments.iter().map(|ty| Visit::Type(ty, depth + 1)));
                    }
                    SurfaceTypeKind::Function(function) => {
                        pending.push(Visit::Type(&function.domain, depth + 1));
                        pending.push(Visit::Type(&function.codomain, depth + 1));
                        if let Some(row) = &function.effects {
                            pending.push(Visit::Row(row, depth + 1));
                        }
                    }
                    SurfaceTypeKind::Int
                    | SurfaceTypeKind::Bytes
                    | SurfaceTypeKind::String
                    | SurfaceTypeKind::Bool
                    | SurfaceTypeKind::Unit
                    | SurfaceTypeKind::Named(_) => {}
                }
            }
            Visit::Kind(kind, depth) => {
                features.kind_nodes += 1;
                features.kind_depth = features.kind_depth.max(depth);
                match &kind.kind {
                    SurfaceKindKind::Function { domain, codomain } => {
                        pending.push(Visit::Kind(domain, depth + 1));
                        pending.push(Visit::Kind(codomain, depth + 1));
                    }
                    SurfaceKindKind::Type | SurfaceKindKind::EffectRow => {}
                }
            }
            Visit::Parameter(parameter) => {
                features.binders += 1;
                if let Some(kind) = &parameter.kind {
                    pending.push(Visit::Kind(kind, 1));
                }
            }
            Visit::Row(row, depth) => {
                features.row_nodes += 1;
                pending.extend(
                    row.effects
                        .iter()
                        .map(|effect| Visit::Effect(effect, depth)),
                );
            }
            Visit::Effect(effect, depth) => {
                features.effect_instances += 1;
                pending.extend(effect.arguments.iter().map(|ty| Visit::Type(ty, depth)));
            }
            Visit::Application(application, requirement) => {
                features.requirements += usize::from(requirement);
                pending.extend(application.arguments.iter().map(|ty| Visit::Type(ty, 1)));
            }
            Visit::Handler(handler, scope) => {
                pending.push(Visit::Pattern(&handler.pattern));
                pending.push(Visit::Expr(&handler.body, scope));
            }
        }
    }
}
