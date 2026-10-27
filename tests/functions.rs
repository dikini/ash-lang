use std::{
    collections::HashSet,
    fs,
    path::PathBuf,
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    core::{
        EffectExprKind, EffectOperation, EffectOperationFamily, PureComputation, PureExprKind,
        ValidatedEffectProgram, dialect::CoreOperationFamily, validate_effect_modules,
    },
    driver::{FileFailure, Observation, RunConfiguration, run_path},
    elaborate::{
        EffectElaborator, Elaborator, TypeContext, TypeError, TypeReason, check_module,
        link_modules,
    },
    eval::{TraceEvent, Value, evaluate_effect},
    evidence_validation::validate_interface_evidence,
    module::{ModuleGraph, ModuleRoots, load_module_graph},
    resolve::{DependencyExports, resolve_module},
    resolved::{
        CheckedModule, ResolvedDefinitionKind, ResolvedExpr, ResolvedExprKind,
        ResolvedLocalDeclaration, ResolvedModule, ResolvedPatternKind,
    },
    source::GeneratedReason,
    types::{EffectInstance, EffectRow, Type},
};

const V002_EQUATIONAL: &str = include_str!("fixtures/first-stratum/valid/v002-equational.ash");
const V002_OPERATIONAL: &str = include_str!("fixtures/first-stratum/valid/v002-operational.ash");
const V004: &str = include_str!("fixtures/first-stratum/valid/v004-capture.ash");
const V005: &str = include_str!("fixtures/first-stratum/valid/v005-higher-order.ash");
const V008: &str = include_str!("fixtures/first-stratum/valid/v008-mixed.ash");

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct TempFile(PathBuf);

impl TempFile {
    fn write(text: &str) -> Self {
        let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
        let path =
            std::env::temp_dir().join(format!("ash-functions-{}-{id}.ash", std::process::id()));
        fs::write(&path, text).expect("test input should be writable");
        Self(path)
    }
}

impl Drop for TempFile {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
    }
}

struct ModuleFixture {
    file: TempFile,
    graph: ModuleGraph,
}

impl ModuleFixture {
    fn load(text: &str) -> Self {
        let file = TempFile::write(text);
        let graph = load_module_graph(&file.0, &ModuleRoots::empty())
            .expect("single-module fixture should load");
        Self { file, graph }
    }

    fn resolve(&self) -> ResolvedModule {
        let mut checked = Vec::<CheckedModule>::new();
        for module in self.graph.modules() {
            let dependencies = module
                .dependencies()
                .iter()
                .map(|edge| {
                    let target = checked
                        .iter()
                        .find(|target| target.module() == edge.target())
                        .expect("the exact dependency target precedes its importer");
                    DependencyExports::new(edge, target.exports())
                        .expect("the actual edge authenticates")
                })
                .collect::<Vec<_>>();
            let resolved = resolve_module(module, &dependencies).expect("the fixture resolves");
            if module.id() == self.graph.entry() {
                return resolved;
            }
            checked.push(check_module(resolved).expect("preceding dependencies check"));
        }
        panic!("the actual entry remains loaded");
    }

    fn run(&self) -> Result<Observation, FileFailure> {
        run_path(RunConfiguration {
            entry: self.file.0.clone(),
            roots: ModuleRoots::empty(),
        })
    }

    fn sources(&self) -> Vec<&ash::source::SourceFile> {
        self.graph
            .modules()
            .iter()
            .map(|module| module.source())
            .collect()
    }

    fn module_sources(&self) -> Vec<(ash::module::ModuleId, ash::source::SourceId)> {
        self.graph
            .modules()
            .iter()
            .map(|module| (module.id(), module.source().id()))
            .collect()
    }
}

fn main_body(module: &ResolvedModule) -> &ResolvedExpr {
    module
        .definitions()
        .iter()
        .find_map(|definition| match &definition.kind {
            ResolvedDefinitionKind::Equational(definition)
            | ResolvedDefinitionKind::ForeignConstant(definition)
                if definition.interface.name.spelling == "main" =>
            {
                Some(
                    &definition
                        .equations
                        .first()
                        .expect("main should have an equation")
                        .body,
                )
            }
            ResolvedDefinitionKind::Equational(_)
            | ResolvedDefinitionKind::ForeignConstant(_)
            | ResolvedDefinitionKind::InlineOperational(_) => None,
        })
        .expect("fixture should declare equational main")
}

fn check_graph(graph: &ModuleGraph) -> Result<Vec<CheckedModule>, TypeError> {
    let mut checked = Vec::<CheckedModule>::new();
    for module in graph.modules() {
        let dependencies = module
            .dependencies()
            .iter()
            .map(|edge| {
                let dependency = checked
                    .iter()
                    .find(|dependency| dependency.module() == edge.target())
                    .expect("dependency order should publish the target first");
                DependencyExports::new(edge, dependency.exports())
                    .expect("checked summary should authenticate its edge")
            })
            .collect::<Vec<_>>();
        let resolved = resolve_module(module, &dependencies).expect("module should resolve");
        drop(dependencies);
        checked.push(check_module(resolved)?);
    }
    Ok(checked)
}

fn validated_effect_program(fixture: &ModuleFixture) -> (ValidatedEffectProgram, Type) {
    let checked = check_graph(&fixture.graph).expect("module should check");
    let entry = checked
        .iter()
        .find(|module| module.module() == fixture.graph.entry())
        .expect("checked graph should retain its entry");
    let main = entry
        .schemes()
        .iter()
        .find(|scheme| scheme.spelling == "main")
        .expect("entry should declare main");
    let function = main
        .scheme
        .value_type()
        .function_view()
        .expect("main should have a function scheme");
    assert_eq!(function.domain(), &Type::Unit);
    assert_eq!(function.effects(), Some(&allocation_row(fixture, &checked)));
    let expected_type = function.value().clone();
    let linked = link_modules(checked, fixture.graph.entry())
        .expect("checked single-module graph should link");
    let linked = validate_interface_evidence(linked).expect("linked evidence should validate");
    let mut elaborator =
        EffectElaborator::for_module_program(&linked).expect("binder reservation should fit");
    let typed = elaborator
        .synthesize_effect_module_program(&linked)
        .expect("linked program should elaborate");
    let ty = typed.ty;
    assert_eq!(ty, expected_type);
    let unchecked = elaborator.finish(typed.node).expect("root should finish");
    let sources = fixture.sources();
    let module_sources = fixture.module_sources();
    let validated = validate_effect_modules(unchecked, &sources, &module_sources)
        .expect("function Core should validate");
    (validated, ty)
}

fn allocation_row(fixture: &ModuleFixture, checked: &[CheckedModule]) -> EffectRow {
    let defining = checked
        .iter()
        .find(|module| {
            fixture
                .graph
                .module(module.module())
                .unwrap()
                .source()
                .display_path()
                == "@compiler.region"
        })
        .unwrap();
    let effects = defining
        .effects()
        .iter()
        .filter(|effect| effect.spelling == "DefaultAlloc")
        .collect::<Vec<_>>();
    let [effect] = effects.as_slice() else {
        panic!("the defining service effect is unique");
    };
    assert_eq!(effect.id.module(), defining.module());
    assert!(effect.parameters.is_empty());
    EffectRow::singleton(EffectInstance::new(effect.id, Box::new([])))
}

fn owned_nodes(
    program: &ValidatedEffectProgram,
    root: ash::core::NodeId,
) -> HashSet<ash::core::NodeId> {
    let mut pending = vec![root];
    let mut seen = HashSet::new();
    while let Some(id) = pending.pop() {
        if seen.insert(id) {
            let kind = &program.node(id).unwrap().kind;
            pending.extend((0..kind.child_count()).filter_map(|i| kind.child_at(i)));
        }
    }
    seen
}

fn source_initializer(
    program: &ValidatedEffectProgram,
    fixture: &ModuleFixture,
    spelling: &str,
) -> ash::core::NodeId {
    let checked = check_graph(&fixture.graph).unwrap();
    let entry = checked
        .iter()
        .find(|module| module.module() == fixture.graph.entry())
        .unwrap();
    let binder = entry
        .schemes()
        .iter()
        .find(|scheme| scheme.spelling == spelling)
        .unwrap()
        .binder;
    let main = entry
        .schemes()
        .iter()
        .find(|scheme| scheme.spelling == "main")
        .unwrap()
        .binder;
    let initializers = owned_nodes(program, program.root())
        .into_iter()
        .filter_map(|id| {
            let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::RecursiveBind(
                group,
            ))) = &program.node(id)?.kind
            else {
                return None;
            };
            let member = group
                .members()
                .iter()
                .find(|member| member.binder().id() == binder)?;
            assert!(
                group
                    .members()
                    .iter()
                    .any(|member| member.binder().id() == main)
            );
            Some(member.initializer())
        })
        .collect::<Vec<_>>();
    let [initializer] = initializers.as_slice() else {
        panic!("the original source binder owns one group member");
    };
    *initializer
}

#[test]
fn anonymous_function_checks_only_with_a_structural_function_context() {
    let fixture =
        ModuleFixture::load("main : Unit -> Int -> Int\nmain () = fn(value) {\n    value\n}\n");
    let module = fixture.resolve();
    let expression = main_body(&module);
    let ResolvedExprKind::Function(surface_function) = &expression.kind else {
        panic!("expected resolved anonymous function");
    };
    let ResolvedPatternKind::Binder(surface_parameter) = &surface_function.pattern.kind else {
        panic!("expected binder parameter");
    };
    let parameter_id = surface_parameter.id;

    let (validated, ty) = validated_effect_program(&fixture);
    let function = ty
        .function_view()
        .expect("the returned anonymous function remains callable");
    assert_eq!(function.domain(), &Type::Int);
    assert_eq!(function.value(), &Type::Int);
    assert_eq!(
        function.effects(),
        Some(&allocation_row(
            &fixture,
            &check_graph(&fixture.graph).unwrap()
        ))
    );
    let main = source_initializer(&validated, &fixture, "main");
    let matches = owned_nodes(&validated, main)
        .into_iter()
        .filter_map(|id| {
            let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Match(group))) =
                &validated.node(id)?.kind
            else {
                return None;
            };
            (validated.node(group.scrutinee())?.ty == Type::Unit).then_some(group)
        })
        .collect::<Vec<_>>();
    let [body_match] = matches.as_slice() else {
        panic!("main retains its unique Unit pattern match");
    };
    assert_eq!(body_match.arms().len(), 1);
    let functions = owned_nodes(&validated, body_match.arms()[0].body())
        .into_iter()
        .filter_map(|id| {
            let node = validated.node(id)?;
            (matches!(
                node.kind,
                EffectExprKind::Operation(EffectOperation::RegionClosure(_))
            ) && node.ty == ty)
                .then_some(node)
        })
        .collect::<Vec<_>>();
    let [function_node] = functions.as_slice() else {
        panic!("the Unit arm owns one exact anonymous function");
    };
    let mut parameters = Vec::new();
    EffectOperationFamily::visit_operation_binders(&function_node.kind, &mut |parameter| {
        parameters.push((parameter.id(), parameter.ty().clone()))
    });
    assert_eq!(parameters, [(parameter_id, Type::Int)]);
    assert_eq!(function_node.origin.primary_span(), expression.span);
    assert_eq!(
        function_node.origin.generated_reason(),
        Some(GeneratedReason::FunctionLowering)
    );
}

#[test]
fn anonymous_function_synthesis_has_the_specific_missing_context_reason_and_span() {
    let fixture =
        ModuleFixture::load("main : Unit -> Int -> Int\nmain () = fn(value) {\n    value\n}\n");
    let module = fixture.resolve();
    let expression = main_body(&module);
    let mut elaborator = Elaborator::new();

    let error = elaborator
        .synthesize(expression, &TypeContext::new())
        .expect_err("anonymous functions do not synthesize");
    let TypeError::Source(diagnostic) = error else {
        panic!("expected a source type diagnostic");
    };
    assert_eq!(diagnostic.reason, TypeReason::FunctionNeedsContext);
    assert_eq!(diagnostic.primary.span(), expression.span);
    assert!(diagnostic.related.is_empty());
}

#[test]
fn anonymous_function_with_a_non_function_expectation_uses_the_current_context_category() {
    let fixture =
        ModuleFixture::load("main : Unit -> Int -> Int\nmain () = fn(value) {\n    value\n}\n");
    let module = fixture.resolve();
    let expression = main_body(&module);
    let mut elaborator = Elaborator::new();

    let error = elaborator
        .check(expression, &Type::Int, &TypeContext::new())
        .expect_err("an Int expectation is not a function context");
    let TypeError::Source(diagnostic) = error else {
        panic!("expected the current source diagnostic category");
    };
    assert_eq!(diagnostic.reason, TypeReason::FunctionNeedsContext);
    assert_eq!(diagnostic.primary.span(), expression.span);
}

#[test]
fn application_rejects_a_non_function_at_the_function_position() {
    let fixture = ModuleFixture::load("main : Unit -> Int\nmain () = 1 2\n");
    let module = fixture.resolve();
    let (function_span, application_span) = {
        let expression = main_body(&module);
        let ResolvedExprKind::Apply(application) = &expression.kind else {
            panic!("expected an application");
        };
        (application.function.span, expression.span)
    };

    let error = check_module(module).expect_err("an integer is not applicable");
    let TypeError::Source(diagnostic) = error else {
        panic!("expected a source type diagnostic");
    };
    assert_eq!(diagnostic.reason, TypeReason::NotApplicable);
    assert_eq!(diagnostic.primary.span(), function_span);
    assert_eq!(diagnostic.related.len(), 1);
    assert_eq!(diagnostic.related[0].span(), application_span);
    assert_eq!(diagnostic.expected.as_deref(), Some("function"));
    assert_eq!(diagnostic.found.as_deref(), Some("Int"));
}

#[test]
fn application_argument_mismatch_relates_the_argument_to_the_global_domain_annotation() {
    let fixture = ModuleFixture::load(concat!(
        "increment : Int -> Int\n",
        "increment value = value + 1\n",
        "main : Unit -> Int\n",
        "main () = increment true\n",
    ));
    let module = fixture.resolve();
    let (argument_span, domain_span) = {
        let ResolvedDefinitionKind::Equational(definition) = &module.definitions()[0].kind else {
            panic!("expected an equational definition");
        };
        let (domain, _) = definition
            .interface
            .annotation
            .provenance
            .function_parts()
            .expect("expected a function annotation");
        let ResolvedExprKind::Apply(application) = &main_body(&module).kind else {
            panic!("expected an application");
        };
        (application.argument.span, domain.span())
    };

    let error = check_module(module).expect_err("Bool does not check against the Int domain");
    let TypeError::Source(diagnostic) = error else {
        panic!("expected a source type diagnostic");
    };
    assert_eq!(diagnostic.reason, TypeReason::Argument);
    assert_eq!(diagnostic.primary.span(), argument_span);
    assert!(
        diagnostic
            .related
            .iter()
            .any(|label| domain_span == Some(label.span()))
    );
    assert_eq!(diagnostic.expected.as_deref(), Some("Int"));
    assert_eq!(diagnostic.found.as_deref(), Some("Bool"));
}

#[test]
fn equational_returned_function_argument_uses_the_inner_domain_provenance() {
    let fixture = ModuleFixture::load(concat!(
        "make : Unit -> Int -> Int\n",
        "make ignored = fn(value) {\n    value\n}\n",
        "main : Unit -> Int\n",
        "main () = make () true\n",
    ));
    let module = fixture.resolve();
    let (outer_domain_span, returned_domain_span) = {
        let ResolvedDefinitionKind::Equational(definition) = &module.definitions()[0].kind else {
            panic!("expected an equational definition");
        };
        let (outer_domain, returned) = definition
            .interface
            .annotation
            .provenance
            .function_parts()
            .expect("expected an outer function type");
        let (returned_domain, _) = returned
            .function_parts()
            .expect("expected a returned function type");
        (outer_domain.span(), returned_domain.span())
    };

    let error = check_module(module).expect_err("Bool does not match the returned Int domain");
    let TypeError::Source(diagnostic) = error else {
        panic!("expected an application argument diagnostic");
    };
    assert_eq!(diagnostic.reason, TypeReason::Argument);
    assert_eq!(diagnostic.expected.as_deref(), Some("Int"));
    assert_eq!(diagnostic.found.as_deref(), Some("Bool"));
    assert!(
        diagnostic
            .related
            .iter()
            .any(|label| Some(label.span()) == returned_domain_span),
        "expected returned domain {:?} in {diagnostic:?}",
        returned_domain_span
    );
    assert!(
        !diagnostic
            .related
            .iter()
            .any(|label| Some(label.span()) == outer_domain_span)
    );
}

#[test]
fn operational_returned_function_argument_uses_the_inner_domain_provenance() {
    let fixture = ModuleFixture::load(concat!(
        "fn make(ignored : Unit) -> Int -> Int {\n",
        "    fn(value) {\n        value\n    }\n",
        "}\n",
        "main : Unit -> Int\n",
        "main () = make () true\n",
    ));
    let module = fixture.resolve();
    let (returned_domain_span, parameter_span) = {
        let ResolvedDefinitionKind::InlineOperational(definition) = &module.definitions()[0].kind
        else {
            panic!("expected an operational definition");
        };
        let (returned_domain, _) = definition
            .header
            .result_type
            .provenance
            .function_parts()
            .expect("expected a returned function type");
        (
            returned_domain.span(),
            definition.header.parameters[0].annotation.span,
        )
    };

    let error = check_module(module).expect_err("Bool does not match the returned Int domain");
    let TypeError::Source(diagnostic) = error else {
        panic!("expected an application argument diagnostic");
    };
    assert_eq!(diagnostic.reason, TypeReason::Argument);
    assert_eq!(diagnostic.expected.as_deref(), Some("Int"));
    assert_eq!(diagnostic.found.as_deref(), Some("Bool"));
    assert!(
        diagnostic
            .related
            .iter()
            .any(|label| Some(label.span()) == returned_domain_span),
        "expected returned domain {:?} in {diagnostic:?}",
        returned_domain_span
    );
    assert!(
        !diagnostic
            .related
            .iter()
            .any(|label| label.span() == parameter_span)
    );
}

#[test]
fn both_v002_presentations_converge_to_function_and_recursive_core_with_distinct_origins() {
    let equational = ModuleFixture::load(V002_EQUATIONAL);
    let operational = ModuleFixture::load(V002_OPERATIONAL);
    let (equational_core, equational_type) = validated_effect_program(&equational);
    let (operational_core, operational_type) = validated_effect_program(&operational);

    assert_eq!(equational_type, Type::Int);
    assert_eq!(operational_type, Type::Int);
    let equational_initializer = source_initializer(&equational_core, &equational, "increment");
    let operational_initializer = source_initializer(&operational_core, &operational, "increment");
    let callable = |program: &ValidatedEffectProgram, initializer| {
        let expected = &program.node(initializer).unwrap().ty;
        let functions = owned_nodes(program, initializer)
            .into_iter()
            .filter(|id| {
                let node = program.node(*id).unwrap();
                matches!(
                    node.kind,
                    EffectExprKind::Operation(EffectOperation::RegionClosure(_))
                ) && &node.ty == expected
            })
            .collect::<Vec<_>>();
        let [function] = functions.as_slice() else {
            panic!("the original increment initializer owns one exact function");
        };
        *function
    };
    let equational_function = equational_core
        .node(callable(&equational_core, equational_initializer))
        .unwrap();
    let operational_function = operational_core
        .node(callable(&operational_core, operational_initializer))
        .unwrap();
    for (node, fixture) in [
        (equational_function, &equational),
        (operational_function, &operational),
    ] {
        let function = node.ty.function_view().expect("increment remains callable");
        assert_eq!(function.domain(), &Type::Int);
        assert_eq!(function.value(), &Type::Int);
        assert_eq!(
            function.effects(),
            Some(&allocation_row(
                fixture,
                &check_graph(&fixture.graph).unwrap()
            ))
        );
    }
    assert_eq!(
        equational_function.origin.generated_reason(),
        Some(GeneratedReason::FunctionLowering)
    );
    assert_eq!(
        operational_function.origin.generated_reason(),
        Some(GeneratedReason::FunctionLowering)
    );
    assert_ne!(
        equational_function.origin.primary_span().range(),
        operational_function.origin.primary_span().range()
    );
}

#[test]
fn a_mid_module_type_failure_prevents_checked_module_and_core_completion() {
    let fixture = ModuleFixture::load(concat!(
        "first : Int -> Int\n",
        "first value = value\n",
        "second : Int -> Bool\n",
        "second value = value\n",
        "main : Unit -> Int\n",
        "main () = 1\n",
    ));
    let module = fixture.resolve();
    let second_body_span = match &module.definitions()[1].kind {
        ResolvedDefinitionKind::Equational(definition)
        | ResolvedDefinitionKind::ForeignConstant(definition) => definition.equations[0].body.span,
        ResolvedDefinitionKind::InlineOperational(_) => {
            panic!("second should be equational")
        }
    };

    let error = check_module(module).expect_err("the second definition result should be rejected");
    let TypeError::Source(diagnostic) = error else {
        panic!("expected the definition-result diagnostic");
    };
    assert_eq!(diagnostic.reason, TypeReason::DefinitionResult);
    assert_eq!(diagnostic.primary.span(), second_body_span);
}

#[test]
fn a_later_global_types_and_runs_with_an_earlier_global_in_lexical_scope() {
    let fixture = ModuleFixture::load(concat!(
        "first : Int -> Int\n",
        "first value = value + 1\n",
        "second : Int -> Int\n",
        "second value = first value\n",
        "main : Unit -> Int\n",
        "main () = second 41\n",
    ));

    let observation = fixture
        .run()
        .expect("the completed first global should be in scope");

    assert_eq!(observation.value().to_string(), "42");
    assert_eq!(observation.ty(), &Type::Int);
}

#[test]
fn definition_result_mismatch_relates_the_body_to_the_declared_codomain() {
    let fixture = ModuleFixture::load(concat!(
        "wrong : Int -> Bool\n",
        "wrong value = value\n",
        "main : Unit -> Int\n",
        "main () = 1\n",
    ));
    let module = fixture.resolve();
    let (body_span, codomain_span) = {
        let ResolvedDefinitionKind::Equational(definition) = &module.definitions()[0].kind else {
            panic!("expected an equational definition");
        };
        let (_, codomain) = definition
            .interface
            .annotation
            .provenance
            .function_parts()
            .expect("expected a function interface");
        (definition.equations[0].body.span, codomain.span())
    };

    let error = check_module(module).expect_err("the declared Bool result should reject Int");
    let TypeError::Source(diagnostic) = error else {
        panic!("expected a source type diagnostic");
    };
    assert_eq!(diagnostic.reason, TypeReason::DefinitionResult);
    assert_eq!(diagnostic.primary.span(), body_span);
    assert!(
        diagnostic
            .related
            .iter()
            .any(|label| Some(label.span()) == codomain_span)
    );
    assert_eq!(diagnostic.expected.as_deref(), Some("Bool"));
    assert_eq!(diagnostic.found.as_deref(), Some("Int"));
}

#[test]
fn equational_interface_must_expose_one_function_domain() {
    let fixture = ModuleFixture::load(concat!(
        "answer : Int\n",
        "answer value = value\n",
        "main : Unit -> Int\n",
        "main () = 1\n",
    ));
    let module = fixture.resolve();
    let (annotation_span, equation_name_span) = {
        let ResolvedDefinitionKind::Equational(definition) = &module.definitions()[0].kind else {
            panic!("expected an equational definition");
        };
        (
            definition.interface.annotation.span,
            definition.equations[0].name.origin.primary_span(),
        )
    };

    let error = check_module(module).expect_err("a non-function interface has no equation rule");
    let TypeError::Source(diagnostic) = error else {
        panic!("expected a source type diagnostic");
    };
    assert_eq!(diagnostic.reason, TypeReason::EquationInterfaceNotFunction);
    assert_eq!(diagnostic.primary.span(), annotation_span);
    assert!(
        diagnostic
            .related
            .iter()
            .any(|label| label.span() == equation_name_span)
    );
    assert_eq!(diagnostic.expected.as_deref(), Some("function"));
    assert_eq!(diagnostic.found.as_deref(), Some("Int"));
}

#[test]
fn every_function_corpus_module_evaluates_to_42_as_an_int() {
    for (name, text) in [
        ("v002-equational.ash", V002_EQUATIONAL),
        ("v002-operational.ash", V002_OPERATIONAL),
        ("v004-capture.ash", V004),
        ("v005-higher-order.ash", V005),
        ("v008-mixed.ash", V008),
    ] {
        let fixture = ModuleFixture::load(text);
        let observation = fixture.run().expect("valid function program should run");
        assert_eq!(observation.value().to_string(), "42", "{name}");
        assert_eq!(observation.ty(), &Type::Int, "{name}");
    }
}

#[test]
fn a_returned_function_exposes_its_code_origin_and_captured_environment() {
    let fixture = ModuleFixture::load(concat!(
        "main : Unit -> Int -> Int\n",
        "main () = {\n",
        "    let offset = 40\n",
        "    let add_offset : Int -> Int = fn(value) {\n",
        "        value + offset\n",
        "    }\n",
        "    add_offset\n",
        "}\n",
    ));
    let resolved = fixture.resolve();
    let ResolvedExprKind::Block(block) = &main_body(&resolved).kind else {
        panic!("main retains its source block");
    };
    let ResolvedLocalDeclaration::Binding(offset) = &block.declarations[0] else {
        panic!("the first binding retains offset");
    };
    let ResolvedPatternKind::Binder(offset) = &offset.pattern.kind else {
        panic!("offset retains its binder");
    };
    let offset_id = offset.id;
    let ResolvedLocalDeclaration::Binding(add_offset) = &block.declarations[1] else {
        panic!("the second binding retains the callable");
    };
    let ResolvedExprKind::Function(source_function) = &add_offset.initializer.kind else {
        panic!("the callable retains its source function");
    };
    let ResolvedPatternKind::Binder(parameter) = &source_function.pattern.kind else {
        panic!("the source parameter remains a binder");
    };
    let parameter_id = parameter.id;
    let function_span = add_offset.initializer.span;
    let (program, ty) = validated_effect_program(&fixture);
    let function = ty.function_view().expect("the result remains callable");
    assert_eq!(function.domain(), &Type::Int);
    assert_eq!(function.value(), &Type::Int);
    assert_eq!(
        function.effects(),
        Some(&allocation_row(
            &fixture,
            &check_graph(&fixture.graph).unwrap()
        ))
    );
    let main = source_initializer(&program, &fixture, "main");
    let owned = owned_nodes(&program, main);
    let offsets = owned
        .iter()
        .filter_map(|id| {
            let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(binding))) =
                &program.node(*id)?.kind
            else {
                return None;
            };
            (binding.binder().id() == offset_id).then_some(binding)
        })
        .collect::<Vec<_>>();
    let [offset] = offsets.as_slice() else {
        panic!("the original offset has one actual Core binding");
    };
    assert_eq!(offset.binder().ty(), &Type::Int);
    let functions = owned
        .iter()
        .filter_map(|id| {
            let node = program.node(*id)?;
            (matches!(
                node.kind,
                EffectExprKind::Operation(EffectOperation::RegionClosure(_))
            ) && node.ty == ty
                && node.origin.primary_span() == function_span)
                .then_some(node)
        })
        .collect::<Vec<_>>();
    let [function_node] = functions.as_slice() else {
        panic!("main owns one exact source callable/code origin");
    };
    let mut parameters = Vec::new();
    EffectOperationFamily::visit_operation_binders(&function_node.kind, &mut |parameter| {
        parameters.push((parameter.id(), parameter.ty().clone()))
    });
    assert_eq!(parameters, [(parameter_id, Type::Int)]);
    assert_eq!(
        function_node.origin.generated_reason(),
        Some(GeneratedReason::FunctionLowering)
    );
    assert!((0..function_node.kind.child_count()).filter_map(|i| function_node.kind.child_at(i)).any(|id|
        matches!(program.node(id).unwrap().kind, EffectExprKind::Pure(PureExprKind::Variable(variable)) if variable.binder() == offset_id)),
        "the returned callable retains its exact preceding offset");
    let observation = fixture.run().expect("function value should evaluate");
    let Value::RegionFunction(closure) = observation.value() else {
        panic!("expected the stored function value");
    };
    assert!(matches!(
        evaluate_effect(&program)
            .expect("the same validated callable executes")
            .value,
        Value::RegionFunction(_)
    ));
    // Public execution loads a separate graph namespace; retain its complete
    // displayed row rather than comparing private service IDs across graphs.
    assert_eq!(observation.type_display(), "Int -> Int ! {DefaultAlloc}");
    let debug = format!("{closure:?}");
    assert!(!debug.contains("nodes:"));
    assert!(!debug.contains("program:"));
    let invoked = ModuleFixture::load(
        &fixture
            .graph
            .module(fixture.graph.entry())
            .unwrap()
            .source()
            .text()
            .replace("main : Unit -> Int -> Int\n", "main : Unit -> Int\n")
            .replace("    add_offset\n", "    add_offset(2)\n"),
    );
    assert_eq!(
        invoked
            .run()
            .expect("the same retained offset remains usable")
            .value_display(),
        "42"
    );
}

#[test]
fn an_escaped_function_uses_its_captured_environment_not_the_caller_environment() {
    let fixture = ModuleFixture::load(concat!(
        "main : Unit -> Int\n",
        "main () = {\n",
        "    let escaped : Unit -> Int = {\n",
        "        let captured = 42\n",
        "        fn(ignored) {\n",
        "            captured\n",
        "        }\n",
        "    }\n",
        "    escaped ()\n",
        "}\n",
    ));
    let observation = fixture
        .run()
        .expect("the escaped closure should retain captured");

    assert_eq!(observation.value().to_string(), "42");
    assert_eq!(observation.ty(), &Type::Int);
}

#[test]
fn application_trace_enters_function_before_argument_then_runs_the_closure_body() {
    let fixture = ModuleFixture::load(V002_EQUATIONAL);
    let resolved = fixture.resolve();
    let ResolvedDefinitionKind::Equational(increment_source) = &resolved.definitions()[0].kind
    else {
        panic!("increment retains its source equation");
    };
    let ResolvedPatternKind::Binder(increment_parameter) =
        &increment_source.equations[0].patterns[0].kind
    else {
        panic!("increment retains its parameter");
    };
    let ResolvedExprKind::Add(addition) = &increment_source.equations[0].body.kind else {
        panic!("increment retains source addition");
    };
    let arithmetic_span = increment_source.equations[0].body.span;
    let application_span = main_body(&resolved).span;
    let (validated, _) = validated_effect_program(&fixture);
    let checked = check_graph(&fixture.graph).unwrap();
    let entry = checked
        .iter()
        .find(|module| module.module() == fixture.graph.entry())
        .unwrap();
    let main_binder = entry
        .schemes()
        .iter()
        .find(|scheme| scheme.spelling == "main")
        .unwrap()
        .binder;
    let increment_binder = entry
        .schemes()
        .iter()
        .find(|scheme| scheme.spelling == "increment")
        .unwrap()
        .binder;
    let groups = owned_nodes(&validated, validated.root())
        .into_iter()
        .filter_map(|id| {
            let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::RecursiveBind(
                group,
            ))) = &validated.node(id)?.kind
            else {
                return None;
            };
            group
                .members()
                .iter()
                .any(|member| member.binder().id() == main_binder)
                .then_some((id, group))
        })
        .collect::<Vec<_>>();
    let [(group_node, group)] = groups.as_slice() else {
        panic!("the original main owns one source group");
    };
    assert_eq!(
        group
            .members()
            .iter()
            .map(|member| member.binder().id())
            .collect::<Vec<_>>(),
        [increment_binder, main_binder]
    );
    let entry_application_node = group.body();
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(entry_application))) =
        &validated.node(entry_application_node).unwrap().kind
    else {
        panic!("the source group retains its entry application");
    };
    let EffectExprKind::Pure(PureExprKind::Variable(main_variable)) =
        &validated.node(entry_application.function()).unwrap().kind
    else {
        panic!("entry calls the original main");
    };
    assert_eq!(main_variable.binder(), main_binder);
    let closure = |initializer| {
        let ty = &validated.node(initializer).unwrap().ty;
        let nodes = owned_nodes(&validated, initializer)
            .into_iter()
            .filter(|id| {
                let node = validated.node(*id).unwrap();
                matches!(
                    node.kind,
                    EffectExprKind::Operation(EffectOperation::RegionClosure(_))
                ) && &node.ty == ty
            })
            .collect::<Vec<_>>();
        let [node] = nodes.as_slice() else {
            panic!("each original initializer owns one exact callable");
        };
        *node
    };
    let increment_closure = closure(source_initializer(&validated, &fixture, "increment"));
    let main_closure = closure(source_initializer(&validated, &fixture, "main"));
    let main_node = validated.node(main_closure).unwrap();
    let matches = (0..main_node.kind.child_count())
        .filter_map(|i| main_node.kind.child_at(i))
        .filter_map(|id| {
            let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Match(group))) =
                &validated.node(id)?.kind
            else {
                return None;
            };
            (validated.node(group.scrutinee())?.ty == Type::Unit).then_some((id, group))
        })
        .collect::<Vec<_>>();
    let [(main_body, main_match)] = matches.as_slice() else {
        panic!("main owns its exact Unit match");
    };
    assert_eq!(main_match.arms().len(), 1);
    let application_node = main_match.arms()[0].body();
    let application = validated.node(application_node).unwrap();
    assert_eq!(application.origin.primary_span(), application_span);
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(application))) =
        &application.kind
    else {
        panic!("the source application remains ordinary");
    };
    let EffectExprKind::Pure(PureExprKind::Variable(increment_variable)) =
        &validated.node(application.function()).unwrap().kind
    else {
        panic!("the source call retains increment");
    };
    assert_eq!(increment_variable.binder(), increment_binder);
    let increment_node = validated.node(increment_closure).unwrap();
    let bodies = (0..increment_node.kind.child_count())
        .filter_map(|i| increment_node.kind.child_at(i))
        .filter(|id| {
            let node = validated.node(*id).unwrap();
            node.ty == Type::Int && node.origin.primary_span() == arithmetic_span
        })
        .collect::<Vec<_>>();
    let [function_body] = bodies.as_slice() else {
        panic!("the original callable owns its exact arithmetic body");
    };
    let arithmetic = owned_nodes(&validated, *function_body)
        .into_iter()
        .filter(|id| {
            let node = validated.node(*id).unwrap();
            matches!(
                node.kind,
                EffectExprKind::Operation(EffectOperation::RegionBuffer(_))
            ) && node.origin.primary_span() == arithmetic_span
        })
        .collect::<Vec<_>>();
    let [arithmetic] = arithmetic.as_slice() else {
        panic!("the source addition retains one supplied integer operation");
    };
    let node = validated.node(*arithmetic).unwrap();
    let children = (0..node.kind.child_count())
        .filter_map(|i| node.kind.child_at(i))
        .collect::<Vec<_>>();
    let operand = |span| {
        let nodes = children
            .iter()
            .filter(|id| {
                let node = validated.node(**id).unwrap();
                node.ty == Type::Int && node.origin.primary_span() == span
            })
            .collect::<Vec<_>>();
        let [node] = nodes.as_slice() else {
            panic!("the original source operand is an exact immediate child");
        };
        **node
    };
    let left = operand(addition.left.span);
    let right = operand(addition.right.span);
    let EffectExprKind::Pure(PureExprKind::Variable(parameter)) =
        &validated.node(left).unwrap().kind
    else {
        panic!("the left operand retains the source parameter");
    };
    assert_eq!(parameter.binder(), increment_parameter.id);
    assert!(
        children.iter().position(|id| *id == left) < children.iter().position(|id| *id == right)
    );
    let evaluation = evaluate_effect(&validated).expect("function Core should evaluate");
    assert_eq!(evaluation.value.to_string(), "42");
    let entered = evaluation
        .trace
        .iter()
        .map(|event| match event {
            TraceEvent::Enter(id) => *id,
        })
        .collect::<Vec<_>>();
    let roles = [
        *group_node,
        entry_application_node,
        entry_application.function(),
        entry_application.argument(),
        *main_body,
        main_match.scrutinee(),
        application_node,
        application.function(),
        application.argument(),
        *function_body,
        left,
        right,
    ];
    assert_eq!(roles.iter().copied().collect::<HashSet<_>>().len(), 12);
    assert!(
        (0..main_node.kind.child_count())
            .filter_map(|i| main_node.kind.child_at(i))
            .any(|id| id == application.function()),
        "main retains the exact increment variable as a stored capture"
    );
    let mut domain = roles.to_vec();
    domain.extend([increment_closure, main_closure]);
    assert_eq!(domain.iter().copied().collect::<HashSet<_>>().len(), 14);
    let actual_roles = entered
        .iter()
        .copied()
        .filter(|id| domain.contains(id))
        .collect::<Vec<_>>();
    // Source callables are created once in member order; main captures increment
    // before the entry call and reads that same occurrence again at application.
    assert_eq!(
        actual_roles,
        [
            *group_node,
            increment_closure,
            main_closure,
            application.function(),
            entry_application_node,
            entry_application.function(),
            entry_application.argument(),
            *main_body,
            main_match.scrutinee(),
            application_node,
            application.function(),
            application.argument(),
            *function_body,
            left,
            right,
        ]
    );
}

#[test]
fn cli_observes_a_global_function_opaquely_with_an_unambiguous_arrow_type() {
    let source = TempFile::write(concat!(
        "identity : Int -> Int\n",
        "identity value = value\n",
        "main : Unit -> Int -> Int\n",
        "main () = identity\n",
    ));
    let output = Command::new(env!("CARGO_BIN_EXE_ash"))
        .arg(&source.0)
        .output()
        .expect("the Ash executable should start");

    assert!(output.status.success());
    assert_eq!(output.stdout, b"<function> : Int -> Int ! {DefaultAlloc}\n");
    assert!(output.stderr.is_empty());
}

#[test]
fn each_function_fixture_has_the_exact_cli_observation() {
    for path in [
        "tests/fixtures/first-stratum/valid/v002-equational.ash",
        "tests/fixtures/first-stratum/valid/v002-operational.ash",
        "tests/fixtures/first-stratum/valid/v004-capture.ash",
        "tests/fixtures/first-stratum/valid/v005-higher-order.ash",
        "tests/fixtures/first-stratum/valid/v008-mixed.ash",
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_ash"))
            .arg(path)
            .output()
            .expect("the Ash executable should start");
        assert!(output.status.success(), "{path}");
        assert_eq!(output.stdout, b"42 : Int\n", "{path}");
        assert!(output.stderr.is_empty(), "{path}");
    }
}

#[test]
fn structural_arrow_rendering_parenthesizes_only_a_function_domain() {
    let higher_order = Type::Function(
        Box::new(Type::Function(Box::new(Type::Int), Box::new(Type::Int))),
        Box::new(Type::Function(Box::new(Type::Bool), Box::new(Type::Unit))),
    );

    assert_eq!(higher_order.to_string(), "(Int -> Int) -> Bool -> Unit");
}
