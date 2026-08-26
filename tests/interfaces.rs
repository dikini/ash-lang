use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    core::{PureComputation, PureExprKind, PureValue, validate_modules},
    driver::{RunConfiguration, run_path},
    elaborate::{Elaborator, TypeError, check_module, link_modules},
    eval::{TraceEvent, evaluate},
    evidence_validation::validate_interface_evidence,
    interface::RequirementOwner,
    module::{ModuleGraph, ModuleRoots, load_module_graph},
    resolve::{DependencyExports, resolve_module},
    resolved::CheckedModule,
    types::Type,
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct InterfaceFixture(PathBuf);

impl InterfaceFixture {
    fn create(text: &str) -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let directory = std::env::temp_dir()
                .join(format!("ash-interface-check-{}-{id}", std::process::id()));
            match fs::create_dir(&directory) {
                Ok(()) => {
                    let path = directory.join("entry.ash");
                    fs::write(&path, text).expect("the interface fixture should be writable");
                    return Self(path);
                }
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("interface fixture directory should be creatable: {error}"),
            }
        }
    }
}

impl Drop for InterfaceFixture {
    fn drop(&mut self) {
        if let Some(directory) = self.0.parent() {
            let _ = fs::remove_dir_all(directory);
        }
    }
}

fn check_error(text: &str) -> TypeError {
    let fixture = InterfaceFixture::create(text);
    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty())
        .expect("the interface fixture should load");
    let loaded = graph
        .module(graph.entry())
        .expect("the entry module should remain admitted");
    let resolved = resolve_module(loaded, &[]).expect("the interface fixture should resolve");
    check_module(resolved).expect_err("the interface fixture should fail checking")
}

fn checked_module(text: &str) -> CheckedModule {
    let fixture = InterfaceFixture::create(text);
    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty())
        .expect("the interface fixture should load");
    let loaded = graph
        .module(graph.entry())
        .expect("the entry module should remain admitted");
    let resolved = resolve_module(loaded, &[]).expect("the interface fixture should resolve");
    check_module(resolved).expect("the interface fixture should check")
}

fn checked_graph(graph: &ModuleGraph) -> Vec<CheckedModule> {
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
                    .expect("checked dependency exports should authenticate their edge")
            })
            .collect::<Vec<_>>();
        let resolved = resolve_module(module, &dependencies)
            .expect("the interface fixture graph should resolve");
        checked.push(check_module(resolved).expect("the interface fixture graph should check"));
    }
    checked
}

fn check_valid(text: &str) {
    drop(checked_module(text));
}

fn reason(error: &TypeError) -> String {
    let TypeError::Interface(diagnostic) = error else {
        panic!("the fixture should produce a source checking error");
    };
    diagnostic.reason.to_string()
}

fn observe_source(text: &str, expected_value: &str, expected_type: Type) {
    let fixture = InterfaceFixture::create(text);
    let observation = run_path(RunConfiguration {
        entry: fixture.0.clone(),
        roots: ModuleRoots::empty(),
    })
    .expect("the interface fixture should complete the modular pipeline");

    assert_eq!(observation.value_display(), expected_value);
    assert_eq!(observation.ty(), &expected_type);
}

#[test]
fn rejects_interface_method_without_parameter_occurrence() {
    let error = check_error("interface Equal<A> {\nequal : (Int, Int) -> Bool\n}\n");

    assert_eq!(reason(&error), "interface.method-parameter");
}

#[test]
fn rejects_duplicate_global_requirement_before_scheme_construction() {
    let error = check_error(
        "interface Equal<A> {\nequal : (A, A) -> Bool\n}\n\nsame : A -> Bool where Equal<A>, Equal<A>\nsame value = true\n",
    );

    assert_eq!(reason(&error), "constraint.duplicate-requirement");
}

#[test]
fn rejects_interface_method_without_function_arrow() {
    let error = check_error("interface Marker<A> {\nmarker : A\n}\n");

    assert_eq!(reason(&error), "interface.method-not-function");
}

#[test]
fn rejects_interface_method_with_only_nested_function_arrow() {
    let error = check_error("interface Callable<A> {\ncallable : (A, Int -> Int)\n}\n");

    assert_eq!(reason(&error), "interface.method-not-function");
}

#[test]
fn rejects_invalid_parameter_before_nested_function_shape() {
    let error = check_error("interface Callable<A> {\ncallable : (B, Int -> Int)\n}\n");

    assert_eq!(reason(&error), "interface.method-parameter");
}

#[test]
fn accepts_top_level_function_with_nested_function_domain() {
    check_valid("interface Transform<A> {\ntransform : (A, Int -> Int) -> Int\n}\n");
}

#[test]
fn accepts_top_level_function_with_function_valued_codomain() {
    check_valid("interface Transform<A> {\ntransform : A -> Int -> Int\n}\n");
}

#[test]
fn top_level_function_with_nested_function_domain_completes_the_pipeline() {
    observe_source(
        concat!(
            "interface Transform<A> {\ntransform : (A, Int -> Int) -> Int\n}\n\n",
            "impl Transform<Int> {\n",
            "transform (value, operation) = operation value\n",
            "}\n\n",
            "increment : Int -> Int\n",
            "increment value = value + 1\n\n",
            "main : Unit -> Int\n",
            "main () = transform((41, increment))\n",
        ),
        "42",
        Type::Int,
    );
}

#[test]
fn rejects_interface_method_local_type_variable() {
    let error = check_error("interface Combine<A> {\ncombine : (A, B) -> A\n}\n");

    assert_eq!(reason(&error), "interface.method-parameter");
}

#[test]
fn rejects_undetermined_global_requirement_parameter() {
    let error = check_error(
        "interface Equal<A> {\nequal : (A, A) -> Bool\n}\n\nsame : A -> Bool where Equal<B>\nsame value = true\n",
    );

    assert_eq!(reason(&error), "constraint.undetermined-parameter");
}

#[test]
fn rejects_public_global_requirement_on_private_interface() {
    let error = check_error(
        "interface Equal<A> {\nequal : (A, A) -> Bool\n}\n\npub same : A -> Bool where Equal<A>\nsame value = true\n",
    );

    assert_eq!(reason(&error), "constraint.private-interface");
}

#[test]
fn accepts_private_global_requirement_on_private_interface() {
    check_valid(
        "interface Equal<A> {\nequal : (A, A) -> Bool\n}\n\nsame : A -> Bool where Equal<A>\nsame value = true\n",
    );
}

#[test]
fn accepts_public_method_signature_that_retains_a_hidden_nominal_identity() {
    check_valid("type Hidden = Hidden\n\npub interface Reveal<A> {\nreveal : A -> Hidden\n}\n");
}

#[test]
fn checked_equational_and_operational_schemes_keep_ordered_requirements_outside_types() {
    let checked = checked_module(concat!(
        "interface Equal<A> {\n",
        "equal : (A, A) -> Bool\n",
        "}\n",
        "same : A -> Bool where Equal<A>\n",
        "same value = true\n",
        "fn same_operational(value : B) -> Bool where Equal<B> {\n",
        "true\n",
        "}\n",
    ));

    assert_eq!(checked.schemes().len(), 2);
    for scheme in checked.schemes() {
        assert_eq!(scheme.scheme.type_parameters.len(), 1);
        assert_eq!(scheme.scheme.requirements.len(), 1);
        assert!(matches!(scheme.scheme.value_type(), Type::Function(_, _)));
        let requirement = &scheme.scheme.requirements[0];
        assert_eq!(
            requirement.id.owner(),
            RequirementOwner::Global(scheme.binder)
        );
        assert_eq!(requirement.id.declaration(), 0);
        assert_eq!(
            requirement.argument(),
            &Type::Variable(scheme.scheme.type_parameters[0])
        );
    }
}

#[test]
fn cross_module_constraint_lowers_to_method_evidence() {
    let fixture = InterfaceFixture::create(concat!(
        "import library as Library\n",
        "import library (impl Equal)\n",
        "main : Unit -> Bool\n",
        "main () = Library.same((1, 1))\n",
    ));
    fs::write(
        fixture
            .0
            .parent()
            .expect("entry fixture has a parent")
            .join("library.ash"),
        concat!(
            "pub interface Equal<A> {\n",
            "equal : (A, A) -> Bool\n",
            "}\n",
            "pub impl Equal<Int> {\n",
            "equal (left, right) = left == right\n",
            "}\n",
            "pub same : (A, A) -> Bool where Equal<A>\n",
            "same pair = equal pair\n",
        ),
    )
    .expect("the dependency fixture should be writable");

    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty())
        .expect("the interface fixture graph should load");
    let checked = checked_graph(&graph);
    let library = checked
        .iter()
        .find(|module| module.module() != graph.entry())
        .expect("the dependency should remain checked");
    let implementation_method = library.implementation_facts()[0].methods[0].binder;
    let same = library
        .schemes()
        .iter()
        .find(|scheme| scheme.spelling == "same")
        .expect("the constrained dependency global should remain checked")
        .binder;
    let main = checked
        .iter()
        .find(|module| module.module() == graph.entry())
        .expect("the entry module should remain checked")
        .schemes()
        .iter()
        .find(|scheme| scheme.spelling == "main")
        .expect("the entry main should remain checked")
        .binder;
    let linked = link_modules(checked, graph.entry()).expect("the checked graph should link");
    let linked =
        validate_interface_evidence(linked).expect("the linked evidence should authenticate");
    let mut elaborator =
        Elaborator::for_module_program(&linked).expect("the graph namespace should reserve");
    let typed = elaborator
        .synthesize_module_program(&linked)
        .expect("validated interface evidence should lower through ordinary Core");
    assert_eq!(typed.ty, Type::Bool);
    let unchecked = elaborator
        .finish(typed.node)
        .expect("the final Core builder should finish");
    let sources = graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let module_sources = graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    let core = validate_modules(unchecked, &sources, &module_sources)
        .expect("ordinary Core emitted from evidence lowering should validate");

    let PureExprKind::Computation(PureComputation::RecursiveBind(library_group)) =
        &core.node(core.root()).expect("Core root should exist").kind
    else {
        panic!("the dependency should lower to its ordinary recursive group");
    };
    let same_initializer = library_group
        .members()
        .iter()
        .find(|member| member.binder().id() == same)
        .expect("the constrained global should remain a dependency group member")
        .initializer();
    let PureExprKind::Computation(PureComputation::TypeAbstraction(abstraction)) = &core
        .node(same_initializer)
        .expect("same initializer should exist")
        .kind
    else {
        panic!("a constrained global must type-abstract before evidence binders");
    };
    let PureExprKind::Value(PureValue::Function(evidence_binder)) = &core
        .node(abstraction.body())
        .expect("type abstraction body should exist")
        .kind
    else {
        panic!("a constrained global must bind its flattened evidence after type abstraction");
    };
    assert!(matches!(
        core.node(evidence_binder.body())
            .expect("evidence binder body should exist")
            .kind,
        PureExprKind::Value(PureValue::Function(_))
    ));
    assert!(
        library_group
            .members()
            .iter()
            .any(|member| member.binder().id() == implementation_method)
    );

    let PureExprKind::Computation(PureComputation::RecursiveBind(entry_group)) = &core
        .node(library_group.body())
        .expect("the entry group should follow its dependency group")
        .kind
    else {
        panic!("the entry should lower to its ordinary recursive group");
    };
    let main_initializer = entry_group
        .members()
        .iter()
        .find(|member| member.binder().id() == main)
        .expect("main should remain an entry group member")
        .initializer();
    let PureExprKind::Value(PureValue::Function(main_function)) = &core
        .node(main_initializer)
        .expect("main initializer should exist")
        .kind
    else {
        panic!("main should lower to a source function");
    };
    let main_body = match &core
        .node(main_function.body())
        .expect("main body should exist")
        .kind
    {
        PureExprKind::Computation(PureComputation::Match(group)) => group
            .arms()
            .first()
            .expect("the checked Unit equation should retain its one arm")
            .body(),
        _ => main_function.body(),
    };
    let PureExprKind::Computation(PureComputation::Apply(source_application)) = &core
        .node(main_body)
        .expect("main equation body should exist")
        .kind
    else {
        panic!("the source argument should be applied after evidence");
    };
    let PureExprKind::Computation(PureComputation::Apply(evidence_application)) = &core
        .node(source_application.function())
        .expect("source application function should exist")
        .kind
    else {
        panic!("selected evidence should be applied before the source argument");
    };
    assert!(matches!(
        core.node(evidence_application.function())
            .expect("evidence application function should exist")
            .kind,
        PureExprKind::Computation(PureComputation::TypeApplication(_))
    ));
    let PureExprKind::Variable(evidence_method) = core
        .node(evidence_application.argument())
        .expect("evidence argument should exist")
        .kind
    else {
        panic!("concrete evidence should lower through its hidden implementation-method binder");
    };
    assert_eq!(evidence_method.binder(), implementation_method);
}

#[test]
fn facade_selection_lowers_through_the_original_core_binder() {
    let fixture = InterfaceFixture::create(concat!(
        "import facade (Equal, equal, same, impl Equal)\n",
        "main : Unit -> Bool\n",
        "main () = same((1, 1))\n",
    ));
    let directory = fixture.0.parent().expect("entry fixture has a parent");
    fs::write(
        directory.join("library.ash"),
        concat!(
            "pub interface Equal<A> {\n",
            "equal : (A, A) -> Bool\n",
            "}\n",
            "pub impl Equal<Int> {\n",
            "equal (left, right) = left == right\n",
            "}\n",
            "pub same : (A, A) -> Bool where Equal<A>\n",
            "same pair = equal pair\n",
        ),
    )
    .expect("the defining fixture should be writable");
    fs::write(
        directory.join("facade.ash"),
        "pub import library (Equal, equal, same, impl Equal)\n",
    )
    .expect("the facade fixture should be writable");

    let observation = run_path(RunConfiguration {
        entry: fixture.0.clone(),
        roots: ModuleRoots::empty(),
    })
    .expect("the facade program should complete the public pipeline");
    assert_eq!(observation.value_display(), "true");
    assert_eq!(observation.ty(), &Type::Bool);

    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty())
        .expect("the facade interface graph should load");
    let checked = checked_graph(&graph);
    let library = checked
        .iter()
        .find(|module| !module.implementation_facts().is_empty())
        .expect("the defining module should retain the implementation");
    let implementation_method = library.implementation_facts()[0].methods[0].binder;
    let main = checked
        .iter()
        .find(|module| module.module() == graph.entry())
        .and_then(|module| {
            module
                .schemes()
                .iter()
                .find(|scheme| scheme.spelling == "main")
        })
        .expect("the entry main should remain checked")
        .binder;
    let linked =
        link_modules(checked, graph.entry()).expect("the checked facade graph should link");
    let linked = validate_interface_evidence(linked)
        .expect("the complete facade authorization should authenticate before Core");
    let mut elaborator =
        Elaborator::for_module_program(&linked).expect("the graph namespace should reserve");
    let typed = elaborator
        .synthesize_module_program(&linked)
        .expect("facade evidence should lower through ordinary Core");
    let unchecked = elaborator
        .finish(typed.node)
        .expect("the final Core builder should finish");
    let sources = graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let module_sources = graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    let core = validate_modules(unchecked, &sources, &module_sources)
        .expect("facade lowering should pass the independent Core validator");

    let PureExprKind::Computation(PureComputation::RecursiveBind(library_group)) = &core
        .node(core.root())
        .expect("the defining Core group should exist")
        .kind
    else {
        panic!("the defining module should lower to an ordinary recursive group");
    };
    assert!(
        library_group
            .members()
            .iter()
            .any(|member| member.binder().id() == implementation_method),
        "the original implementation-method binder should remain the sole evidence body",
    );
    let PureExprKind::Computation(PureComputation::RecursiveBind(entry_group)) = &core
        .node(library_group.body())
        .expect("the entry Core group should follow the defining group")
        .kind
    else {
        panic!("the body-free facade should add no runtime or Core group");
    };
    let main_initializer = entry_group
        .members()
        .iter()
        .find(|member| member.binder().id() == main)
        .expect("main should remain an entry group member")
        .initializer();
    let PureExprKind::Value(PureValue::Function(main_function)) = &core
        .node(main_initializer)
        .expect("main initializer should exist")
        .kind
    else {
        panic!("main should lower to a source function");
    };
    let main_body = match &core
        .node(main_function.body())
        .expect("main body should exist")
        .kind
    {
        PureExprKind::Computation(PureComputation::Match(group)) => group
            .arms()
            .first()
            .expect("the checked Unit equation should retain one arm")
            .body(),
        _ => main_function.body(),
    };
    let PureExprKind::Computation(PureComputation::Apply(source_application)) = &core
        .node(main_body)
        .expect("main equation body should exist")
        .kind
    else {
        panic!("the source argument should remain an ordinary term application");
    };
    let PureExprKind::Computation(PureComputation::Apply(evidence_application)) = &core
        .node(source_application.function())
        .expect("the source application function should exist")
        .kind
    else {
        panic!("selected evidence should remain an ordinary term application");
    };
    assert!(matches!(
        core.node(evidence_application.function())
            .expect("the constrained global function should exist")
            .kind,
        PureExprKind::Computation(PureComputation::TypeApplication(_))
    ));
    let PureExprKind::Variable(evidence_method) = core
        .node(evidence_application.argument())
        .expect("the evidence argument should exist")
        .kind
    else {
        panic!("facade evidence should lower to the defining implementation method");
    };
    assert_eq!(evidence_method.binder(), implementation_method);
}

#[test]
fn generic_option_impl_constructs_prerequisite_evidence() {
    observe_source(
        concat!(
            "type Option<A> =\nNone\n| Some(A)\n\n",
            "interface Equal<A> {\nequal : (A, A) -> Bool\n}\n\n",
            "impl Equal<Int> {\n",
            "equal (left, right) = left == right\n",
            "}\n\n",
            "impl Equal<Option<A>> where Equal<A> {\n",
            "equal (None, None) = true\n",
            "equal (Some(left), Some(right)) = equal((left, right))\n",
            "equal pair = false\n",
            "}\n\n",
            "main : Unit -> Bool\n",
            "main () = equal((Some(42), Some(42)))\n",
        ),
        "true",
        Type::Bool,
    );
}

#[test]
fn generic_prerequisite_evidence_preserves_same_typed_method_slot_order() {
    observe_source(
        concat!(
            "type Option<A> =\nNone\n| Some(A)\n\n",
            "interface Compare<A> {\n",
            "same : (A, A) -> Bool\n",
            "different : (A, A) -> Bool\n",
            "}\n\n",
            "impl Compare<Int> {\n",
            "same (left, right) = left == right\n",
            "different pair = false\n",
            "}\n\n",
            "impl Compare<Option<A>> where Compare<A> {\n",
            "same (Some(left), Some(right)) = same((left, right))\n",
            "same pair = false\n",
            "different pair = false\n",
            "}\n\n",
            "main : Unit -> Bool\n",
            "main () = same((Some(42), Some(42)))\n",
        ),
        "true",
        Type::Bool,
    );
}

#[test]
fn generic_two_prerequisite_slots_preserve_declaration_order() {
    observe_source(
        concat!(
            "type Wrap<A> = Wrap(A)\n\n",
            "interface First<A> {\nfirst : A -> Int\n}\n\n",
            "interface Second<A> {\nsecond : A -> Int\n}\n\n",
            "interface Combine<A> {\ncombine : A -> Int\n}\n\n",
            "impl First<Int> {\nfirst value = 4\n}\n\n",
            "impl Second<Int> {\nsecond value = 2\n}\n\n",
            "impl Combine<Wrap<A>> where First<A>, Second<A> {\n",
            "combine (Wrap(value)) = first value * 10 + second value\n",
            "}\n\n",
            "main : Unit -> Int\n",
            "main () = combine(Wrap(0))\n",
        ),
        "42",
        Type::Int,
    );
}

#[test]
fn generic_prerequisite_evidence_has_a_bounded_unspecialized_evaluation_trace() {
    let fixture = InterfaceFixture::create(concat!(
        "type Wrap<A> = Wrap(A)\n\n",
        "interface Read<A> {\nread : A -> Int\n}\n\n",
        "impl Read<Int> {\nread value = value\n}\n\n",
        "impl Read<Wrap<A>> where Read<A> {\n",
        "read (Wrap(value)) = read value\n",
        "}\n\n",
        "main : Unit -> Int\n",
        "main () = read(Wrap(42))\n",
    ));
    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty())
        .expect("the generic evidence fixture should load");
    let checked = checked_graph(&graph);
    let module = checked
        .first()
        .expect("the one-module fixture should remain checked");
    let [ground_implementation, generic_implementation] = module.implementation_facts() else {
        panic!("the fixture should retain its ground and generic implementations");
    };
    let ground_method = ground_implementation.methods[0].binder;
    let generic_method = generic_implementation.methods[0].binder;
    let main = module
        .schemes()
        .iter()
        .find(|scheme| scheme.spelling == "main")
        .expect("the fixture should retain main")
        .binder;

    let linked = link_modules(checked, graph.entry()).expect("the fixture should link");
    let linked =
        validate_interface_evidence(linked).expect("the generic evidence should authenticate");
    let mut elaborator =
        Elaborator::for_module_program(&linked).expect("the fixture namespace should reserve");
    let typed = elaborator
        .synthesize_module_program(&linked)
        .expect("the generic evidence should lower");
    let unchecked = elaborator
        .finish(typed.node)
        .expect("the generic evidence Core should finish");
    let sources = graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let module_sources = graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    let core = validate_modules(unchecked, &sources, &module_sources)
        .expect("the unspecialized generic evidence Core should validate");

    let PureExprKind::Computation(PureComputation::RecursiveBind(group)) =
        &core.node(core.root()).expect("Core root should exist").kind
    else {
        panic!("the module should lower to one recursive group");
    };
    let main_initializer = group
        .members()
        .iter()
        .find(|member| member.binder().id() == main)
        .expect("main should remain a group member")
        .initializer();
    let PureExprKind::Value(PureValue::Function(main_function)) = &core
        .node(main_initializer)
        .expect("main initializer should exist")
        .kind
    else {
        panic!("main should lower to a function");
    };
    let source_application_node = match &core
        .node(main_function.body())
        .expect("main body should exist")
        .kind
    {
        PureExprKind::Computation(PureComputation::Match(match_node)) => {
            match_node.arms()[0].body()
        }
        _ => main_function.body(),
    };
    let PureExprKind::Computation(PureComputation::Apply(source_application)) = &core
        .node(source_application_node)
        .expect("the source application should exist")
        .kind
    else {
        panic!("the selected method should receive its source value last");
    };
    let evidence_application_node = source_application.function();
    let PureExprKind::Computation(PureComputation::Apply(evidence_application)) = &core
        .node(evidence_application_node)
        .expect("the evidence application should exist")
        .kind
    else {
        panic!("the generic method should receive prerequisite evidence");
    };
    let type_application_node = evidence_application.function();
    let PureExprKind::Computation(PureComputation::TypeApplication(type_application)) = &core
        .node(type_application_node)
        .expect("the generic method type application should exist")
        .kind
    else {
        panic!("the generic method should be type-applied before evidence");
    };
    let generic_method_node = type_application.function();
    let PureExprKind::Variable(generic_method_variable) = core
        .node(generic_method_node)
        .expect("the generic method variable should exist")
        .kind
    else {
        panic!("the generic evidence should use the linked implementation-method binder");
    };
    assert_eq!(generic_method_variable.binder(), generic_method);
    let prerequisite_node = evidence_application.argument();
    let PureExprKind::Variable(prerequisite_variable) = core
        .node(prerequisite_node)
        .expect("the prerequisite method variable should exist")
        .kind
    else {
        panic!("the prerequisite should remain an ordinary method function");
    };
    assert_eq!(prerequisite_variable.binder(), ground_method);

    let evaluation = evaluate(&core).expect("the unspecialized generic evidence should evaluate");
    assert_eq!(evaluation.value.to_string(), "42");
    let entered = evaluation
        .trace
        .iter()
        .map(|event| match event {
            TraceEvent::Enter(node) => *node,
        })
        .collect::<Vec<_>>();
    let source_application_index = entered
        .iter()
        .position(|node| *node == source_application_node)
        .expect("evaluation should enter the source application");
    assert_eq!(
        entered.get(source_application_index..source_application_index + 5),
        Some(
            [
                source_application_node,
                evidence_application_node,
                type_application_node,
                generic_method_node,
                prerequisite_node,
            ]
            .as_slice(),
        ),
    );
    let prerequisite_index = entered
        .iter()
        .position(|node| *node == prerequisite_node)
        .expect("evaluation should construct prerequisite evidence");
    let source_argument_index = entered
        .iter()
        .position(|node| *node == source_application.argument())
        .expect("evaluation should enter the source value argument");
    assert!(prerequisite_index < source_argument_index);
    assert!(evaluation.trace.len() <= 32);
    assert!(evaluation.max_frame_depth <= 6);
}

#[test]
fn generic_exact_current_self_carries_abstract_prerequisite_evidence() {
    observe_source(
        concat!(
            "type Option<A> =\nNone\n| Some(A)\n\n",
            "interface Score<A> {\nscore : A -> Int\n}\n\n",
            "impl Score<Int> {\nscore value = value\n}\n\n",
            "impl Score<Option<A>> where Score<A> {\n",
            "score None = 4\n",
            "score (Some(value)) = {\n",
            "let empty : Option<A> = None\n",
            "score empty * 10 + score value\n",
            "}\n",
            "}\n\n",
            "main : Unit -> Int\n",
            "main () = score(Some(2))\n",
        ),
        "42",
        Type::Int,
    );
}

#[test]
fn generic_impl_constructor_result_zonks_before_core_alpha_renaming() {
    observe_source(
        concat!(
            "type Option<A> =\nNone\n| Some(A)\n\n",
            "type Wrap<A> = Wrap(A)\n\n",
            "interface Lift<A> {\nlift : A -> Option<A>\n}\n\n",
            "impl Lift<Wrap<A>> {\n",
            "lift value = Some(value)\n",
            "}\n\n",
            "unwrap : Option<Wrap<Int>> -> Int\n",
            "unwrap None = 0\n",
            "unwrap (Some(Wrap(value))) = value\n\n",
            "main : Unit -> Int\n",
            "main () = unwrap(lift(Wrap(42)))\n",
        ),
        "42",
        Type::Int,
    );
}

#[test]
fn generic_current_impl_does_not_freshly_instantiate_its_rigid_head() {
    let error = check_error(concat!(
        "type Option<A> =\nNone\n| Some(A)\n\n",
        "interface Keep<A> {\nkeep : A -> A\n}\n\n",
        "impl Keep<Option<A>> where Keep<A> {\n",
        "keep value = {\n",
        "let unrelated = keep(Some(1))\n",
        "value\n",
        "}\n",
        "}\n",
    ));

    assert_eq!(reason(&error), "constraint.unsatisfied");
}

#[test]
fn ground_cross_interface_prerequisite_cycle_has_the_exact_reason() {
    let error = check_error(concat!(
        "interface First<A> {\nfirst : A -> A\n}\n\n",
        "interface Second<A> {\nsecond : A -> A\n}\n\n",
        "impl First<Int> where Second<Int> {\nfirst value = value\n}\n\n",
        "impl Second<Int> where First<Int> {\nsecond value = value\n}\n\n",
        "main : Unit -> Int\n",
        "main () = first 1\n",
    ));

    assert_eq!(reason(&error), "constraint.cycle");
}

#[test]
fn deep_generic_prerequisite_chain_completes_the_pipeline_on_a_small_stack() {
    const DEPTH: usize = 96;
    let worker = std::thread::Builder::new()
        .name("deep-generic-prerequisite-chain".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut nested = "Option<".repeat(DEPTH);
            nested.push_str("Int");
            nested.push_str(&">".repeat(DEPTH));
            let source = format!(
                concat!(
                    "type Option<A> =\nNone\n| Some(A)\n\n",
                    "interface Keep<A> {{\nkeep : A -> A\n}}\n\n",
                    "impl Keep<Int> {{\nkeep value = value\n}}\n\n",
                    "impl Keep<Option<A>> where Keep<A> {{\nkeep value = value\n}}\n\n",
                    "probe : {0} -> {0}\n",
                    "probe value = keep value\n\n",
                    "main : Unit -> Int\n",
                    "main () = 42\n",
                ),
                nested,
            );

            observe_source(&source, "42", Type::Int);
        })
        .expect("the small-stack generic selection worker should start");

    worker
        .join()
        .expect("generic prerequisite selection and destruction should remain iterative");
}
