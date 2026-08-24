use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    core::{PureComputation, PureExprKind, PureValue, validate_modules},
    elaborate::{Elaborator, TypeError, check_module, link_modules},
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
fn rejects_interface_method_without_function_shape() {
    let error = check_error("interface Marker<A> {\nmarker : A\n}\n");

    assert_eq!(reason(&error), "interface.method-not-function");
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
        assert!(matches!(scheme.scheme.value_type, Type::Function(_, _)));
        let requirement = &scheme.scheme.requirements[0];
        assert_eq!(
            requirement.id.owner(),
            RequirementOwner::Global(scheme.binder)
        );
        assert_eq!(requirement.id.declaration(), 0);
        assert_eq!(
            requirement.argument,
            Type::Variable(scheme.scheme.type_parameters[0])
        );
    }
}

#[test]
fn cross_module_constraint_lowers_to_method_evidence() {
    let fixture = InterfaceFixture::create(concat!(
        "import library as Library\n",
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
    let PureExprKind::Computation(PureComputation::Apply(source_application)) = &core
        .node(main_function.body())
        .expect("main body should exist")
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
