use std::{
    fs,
    path::PathBuf,
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    core::{PureComputation, PureExprKind, PureValue, ValidatedProgram, validate_modules},
    driver::{FileFailure, Observation, RunConfiguration, run_path},
    elaborate::{Elaborator, TypeContext, TypeError, TypeReason, check_module, link_modules},
    eval::{TraceEvent, Value, evaluate},
    evidence_validation::validate_interface_evidence,
    module::{ModuleGraph, ModuleRoots, load_module_graph},
    resolve::{DependencyExports, resolve_module},
    resolved::{
        CheckedModule, ResolvedDefinitionKind, ResolvedExpr, ResolvedExprKind, ResolvedModule,
        ResolvedPatternKind,
    },
    source::GeneratedReason,
    types::Type,
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
        let module = self
            .graph
            .modules()
            .iter()
            .find(|module| module.id() == self.graph.entry())
            .expect("entry module should be loaded");
        assert!(module.dependencies().is_empty());
        resolve_module(module, &[]).expect("single-module fixture should resolve")
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

fn validated_program(fixture: &ModuleFixture) -> (ValidatedProgram, Type) {
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
    let Type::Function(domain, codomain) = main.scheme.value_type() else {
        panic!("main should have a function scheme");
    };
    assert_eq!(domain.as_ref(), &Type::Unit);
    let expected_type = codomain.as_ref().clone();
    let linked = link_modules(checked, fixture.graph.entry())
        .expect("checked single-module graph should link");
    let linked = validate_interface_evidence(linked).expect("linked evidence should validate");
    let mut elaborator =
        Elaborator::for_module_program(&linked).expect("binder reservation should fit");
    let typed = elaborator
        .synthesize_module_program(&linked)
        .expect("linked program should elaborate");
    let ty = typed.ty;
    assert_eq!(ty, expected_type);
    let unchecked = elaborator.finish(typed.node).expect("root should finish");
    let sources = fixture.sources();
    let module_sources = fixture.module_sources();
    let validated = validate_modules(unchecked, &sources, &module_sources)
        .expect("function Core should validate");
    (validated, ty)
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

    let (validated, ty) = validated_program(&fixture);
    assert_eq!(ty, Type::Function(Box::new(Type::Int), Box::new(Type::Int)));
    let root = validated.node(validated.root()).expect("global binding");
    let PureExprKind::Computation(PureComputation::RecursiveBind(group)) = &root.kind else {
        panic!("expected the module's recursive group");
    };
    let main = validated
        .node(group.members()[0].initializer())
        .expect("main initializer");
    let PureExprKind::Value(PureValue::Function(main)) = &main.kind else {
        panic!("expected main function Core");
    };
    let body_match = validated.node(main.body()).expect("main pattern match");
    let PureExprKind::Computation(PureComputation::Match(body_match)) = &body_match.kind else {
        panic!("expected main's Unit pattern match");
    };
    let function_node = validated
        .node(body_match.arms()[0].body())
        .expect("anonymous function body");
    let PureExprKind::Value(PureValue::Function(function)) = &function_node.kind else {
        panic!("expected shared function Core");
    };
    assert_eq!(function.parameter().id(), parameter_id);
    assert_eq!(function.parameter().ty(), &Type::Int);
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
    let (equational_core, equational_type) = validated_program(&equational);
    let (operational_core, operational_type) = validated_program(&operational);

    assert_eq!(equational_type, Type::Int);
    assert_eq!(operational_type, Type::Int);
    let equational_root = equational_core.node(equational_core.root()).expect("root");
    let operational_root = operational_core
        .node(operational_core.root())
        .expect("root");
    let PureExprKind::Computation(PureComputation::RecursiveBind(equational_group)) =
        &equational_root.kind
    else {
        panic!("expected an outer recursive group");
    };
    let PureExprKind::Computation(PureComputation::RecursiveBind(operational_group)) =
        &operational_root.kind
    else {
        panic!("expected an outer recursive group");
    };
    let equational_function = equational_core
        .node(equational_group.members()[0].initializer())
        .expect("equational function");
    let operational_function = operational_core
        .node(operational_group.members()[0].initializer())
        .expect("operational function");
    assert!(matches!(
        equational_function.kind,
        PureExprKind::Value(PureValue::Function(_))
    ));
    assert!(matches!(
        operational_function.kind,
        PureExprKind::Value(PureValue::Function(_))
    ));
    assert_eq!(equational_function.ty, operational_function.ty);
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
        ResolvedDefinitionKind::Equational(definition) => definition.equations[0].body.span,
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
    let observation = fixture.run().expect("function value should evaluate");
    let Value::Function(closure) = observation.value() else {
        panic!("expected an inspectable function value");
    };

    assert_eq!(
        closure.environment.len(),
        3,
        "the closure retains main, its Unit parameter, and the local offset"
    );
    assert!(closure.program.node(closure.body).is_some());
    assert_eq!(
        closure.origin.generated_reason(),
        Some(GeneratedReason::FunctionLowering)
    );
    assert_eq!(observation.ty().to_string(), "Int -> Int");
    let debug = format!("{closure:?}");
    assert!(debug.contains("Closure"));
    assert!(!debug.contains("nodes:"));
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
    let (validated, _) = validated_program(&fixture);
    let root = validated.node(validated.root()).expect("global binding");
    let PureExprKind::Computation(PureComputation::RecursiveBind(group)) = &root.kind else {
        panic!("expected global recursive group");
    };
    let entry_application = validated.node(group.body()).expect("entry application");
    let PureExprKind::Computation(PureComputation::Apply(entry_application)) =
        &entry_application.kind
    else {
        panic!("expected generated main application Core");
    };
    let increment = validated
        .node(group.members()[0].initializer())
        .expect("increment initializer");
    let PureExprKind::Value(PureValue::Function(increment)) = &increment.kind else {
        panic!("expected increment function Core");
    };
    let main = validated
        .node(group.members()[1].initializer())
        .expect("main initializer");
    let PureExprKind::Value(PureValue::Function(main)) = &main.kind else {
        panic!("expected main function Core");
    };
    let main_match = validated.node(main.body()).expect("main pattern match");
    let PureExprKind::Computation(PureComputation::Match(main_match)) = &main_match.kind else {
        panic!("expected main's Unit pattern match");
    };
    let application = validated
        .node(main_match.arms()[0].body())
        .expect("increment application");
    let PureExprKind::Computation(PureComputation::Apply(application)) = &application.kind else {
        panic!("expected increment application Core");
    };
    let function_body = validated
        .node(increment.body())
        .expect("increment function body");
    let PureExprKind::Computation(PureComputation::Primitive(function_body)) = &function_body.kind
    else {
        panic!("expected primitive function body");
    };

    let evaluation = evaluate(&validated).expect("function Core should evaluate");
    assert_eq!(evaluation.value.to_string(), "42");
    let entered = evaluation
        .trace
        .iter()
        .map(|event| match event {
            TraceEvent::Enter(node) => *node,
        })
        .collect::<Vec<_>>();
    assert_eq!(
        entered,
        vec![
            validated.root(),
            group.body(),
            entry_application.function(),
            entry_application.argument(),
            main.body(),
            main_match.scrutinee(),
            main_match.arms()[0].body(),
            application.function(),
            application.argument(),
            increment.body(),
            function_body.left(),
            function_body.right(),
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
    assert_eq!(output.stdout, b"<function> : Int -> Int\n");
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
