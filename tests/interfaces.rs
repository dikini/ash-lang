use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    elaborate::{TypeError, check_module},
    interface::RequirementOwner,
    module::{ModuleRoots, load_module_graph},
    resolve::resolve_module,
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
