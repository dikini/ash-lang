use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    elaborate::{TypeError, check_module},
    module::{ModuleGraph, ModuleRoots, load_module_graph},
    resolve::{DependencyExports, resolve_module},
    resolved::CheckedModule,
    types::Type,
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct ImplementationFixture(PathBuf);

impl ImplementationFixture {
    fn create(entry: &str, dependencies: &[(&str, &str)]) -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let directory = std::env::temp_dir().join(format!(
                "ash-implementation-check-{}-{id}",
                std::process::id()
            ));
            match fs::create_dir(&directory) {
                Ok(()) => {
                    let entry_path = directory.join("entry.ash");
                    fs::write(&entry_path, entry)
                        .expect("the implementation fixture entry should be writable");
                    for (path, text) in dependencies {
                        fs::write(directory.join(path), text)
                            .expect("the implementation fixture dependency should be writable");
                    }
                    return Self(entry_path);
                }
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => {
                    panic!("implementation fixture directory should be creatable: {error}")
                }
            }
        }
    }
}

impl Drop for ImplementationFixture {
    fn drop(&mut self) {
        if let Some(directory) = self.0.parent() {
            let _ = fs::remove_dir_all(directory);
        }
    }
}

fn check_graph(graph: &ModuleGraph) -> Result<Vec<CheckedModule>, TypeError> {
    let mut checked: Vec<CheckedModule> = Vec::new();
    for module in graph.modules() {
        let dependencies = module
            .dependencies()
            .iter()
            .map(|edge| {
                let dependency = checked
                    .iter()
                    .find(|checked| checked.module() == edge.target())
                    .expect("dependency order should check the target first");
                DependencyExports::new(edge, dependency.exports())
                    .expect("checked summary should authenticate its edge")
            })
            .collect::<Vec<_>>();
        let resolved = resolve_module(module, &dependencies)
            .expect("the implementation fixture should resolve");
        checked.push(check_module(resolved)?);
    }
    Ok(checked)
}

fn check_error(text: &str) -> TypeError {
    let fixture = ImplementationFixture::create(text, &[]);
    check_fixture_error(&fixture)
}

fn check_error_with_dependencies(text: &str, dependencies: &[(&str, &str)]) -> TypeError {
    let fixture = ImplementationFixture::create(text, dependencies);
    check_fixture_error(&fixture)
}

fn check_fixture_error(fixture: &ImplementationFixture) -> TypeError {
    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty())
        .expect("the implementation fixture should load");
    check_graph(&graph).expect_err("the implementation fixture should fail checking")
}

fn public_impl_failure_does_not_publish(text: &str, expected_reason: &str) {
    let fixture = ImplementationFixture::create(
        "import broken as Broken\nentry : Unit -> Unit\nentry () = ()\n",
        &[("broken.ash", text)],
    );
    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty())
        .expect("the implementation fixture should load");
    let broken = graph
        .modules()
        .iter()
        .find(|module| module.source().display_path().ends_with("broken.ash"))
        .expect("the fixture should retain the broken dependency");
    let resolved = resolve_module(broken, &[]).expect("the broken dependency should resolve");

    let published = match check_module(resolved) {
        Ok(checked) => {
            let _summary = checked.exports();
            true
        }
        Err(error) => {
            let actual_reason = match &error {
                TypeError::Interface(diagnostic) => diagnostic.reason.to_string(),
                TypeError::Source(diagnostic) => diagnostic.reason.to_string(),
                TypeError::Mismatch(_) | TypeError::Internal(_) => {
                    panic!("expected a categorized public implementation failure, found {error:?}")
                }
            };
            assert_eq!(actual_reason, expected_reason);
            false
        }
    };

    assert!(
        !published,
        "a failed public implementation must not produce a checked export summary"
    );
}

fn checked_valid(text: &str) -> Vec<CheckedModule> {
    let fixture = ImplementationFixture::create(text, &[]);
    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty())
        .expect("the implementation fixture should load");
    check_graph(&graph).expect("the implementation fixture should check")
}

fn check_valid(text: &str) {
    drop(checked_valid(text));
}

fn reason(error: &TypeError) -> String {
    let TypeError::Interface(diagnostic) = error else {
        panic!("expected an interface diagnostic, found {error:?}");
    };
    diagnostic.reason.to_string()
}

fn source_reason(error: &TypeError) -> String {
    let TypeError::Source(diagnostic) = error else {
        panic!("expected a typed source diagnostic, found {error:?}");
    };
    diagnostic.reason.to_string()
}

#[test]
fn rejects_bare_type_variable_impl_head() {
    let error = check_error(
        "interface Equal<A> {\nequal : A -> A\n}\n\nimpl Equal<A> {\nequal value = value\n}\n",
    );

    assert_eq!(reason(&error), "impl.variable-head");
}

#[test]
fn invalid_bare_variable_head_precedes_imported_implementation_overlap() {
    let error = check_error_with_dependencies(
        concat!(
            "import equality (Equal, equal, impl Equal)\n",
            "impl Equal<A> {\nequal value = value\n}\n",
        ),
        &[(
            "equality.ash",
            concat!(
                "pub interface Equal<A> {\nequal : A -> A\n}\n",
                "pub impl Equal<Int> {\nequal value = value\n}\n",
            ),
        )],
    );

    assert_eq!(reason(&error), "impl.variable-head");
}

#[test]
fn orphan_header_precedes_imported_implementation_overlap() {
    let error = check_error_with_dependencies(
        concat!(
            "import equality (Equal, equal, impl Equal)\n",
            "impl Equal<Int> {\nequal value = value\n}\n",
        ),
        &[(
            "equality.ash",
            concat!(
                "pub interface Equal<A> {\nequal : A -> A\n}\n",
                "pub impl Equal<Int> {\nequal value = value\n}\n",
            ),
        )],
    );

    assert_eq!(reason(&error), "impl.orphan");
}

#[test]
fn rejects_prerequisite_only_impl_variable() {
    let error = check_error(concat!(
        "type Option<A> =\nNone\n| Some(A)\n",
        "interface Equal<A> {\nequal : A -> A\n}\n\n",
        "impl Equal<Option<A>> where Equal<B> {\nequal value = value\n}\n",
    ));

    assert_eq!(reason(&error), "impl.prerequisite-variable");
}

#[test]
fn accepts_impl_for_local_interface() {
    check_valid(
        "interface Equal<A> {\nequal : A -> A\n}\n\nimpl Equal<Int> {\nequal value = value\n}\n",
    );
}

#[test]
fn accepts_impl_for_local_outer_nominal() {
    check_valid(concat!(
        "type Local = Local\n",
        "interface Equal<A> {\nequal : A -> A\n}\n\n",
        "impl Equal<Local> {\nequal value = value\n}\n",
    ));
}

#[test]
fn accepts_strict_subterm_prerequisite() {
    check_valid(concat!(
        "type Option<A> =\nNone\n| Some(A)\n",
        "interface Equal<A> {\nequal : A -> A\n}\n\n",
        "impl Equal<Option<A>> where Equal<A> {\nequal value = value\n}\n",
    ));
}

#[test]
fn rejects_expanding_prerequisite() {
    let error = check_error(concat!(
        "type Option<A> =\nNone\n| Some(A)\n",
        "interface Equal<A> {\nequal : A -> A\n}\n\n",
        "impl Equal<Option<A>> where Equal<Option<Option<A>>> {\nequal value = value\n}\n",
    ));

    assert_eq!(reason(&error), "impl.prerequisite-not-decreasing");
}

#[test]
fn rejects_missing_impl_method() {
    let error = check_error(concat!(
        "interface Pair<A> {\nfirst : A -> A\nsecond : A -> A\n}\n\n",
        "impl Pair<Int> {\nfirst value = value\n}\n",
    ));

    assert_eq!(reason(&error), "impl.missing-method");
}

#[test]
fn rejects_duplicate_impl_method_group() {
    let error = check_error(concat!(
        "interface Pair<A> {\nfirst : A -> A\nsecond : A -> A\n}\n\n",
        "impl Pair<Int> {\n",
        "first value = value\n",
        "second value = value\n",
        "first value = value\n",
        "}\n",
    ));

    assert_eq!(reason(&error), "impl.duplicate-method");
}

#[test]
fn rejects_extra_impl_method() {
    let error = check_error(concat!(
        "interface Equal<A> {\nequal : A -> A\n}\n\n",
        "impl Equal<Int> {\nextra value = value\n}\n",
    ));

    assert_eq!(reason(&error), "impl.extra-method");
}

#[test]
fn rejects_method_from_another_interface() {
    let error = check_error(concat!(
        "interface Equal<A> {\nequal : A -> A\n}\n",
        "interface Render<A> {\nrender : A -> A\n}\n\n",
        "impl Equal<Int> {\nrender value = value\n}\n",
    ));

    assert_eq!(reason(&error), "impl.extra-method");
}

#[test]
fn rejects_public_impl_for_private_interface() {
    let error = check_error(
        "interface Equal<A> {\nequal : A -> A\n}\n\npub impl Equal<Int> {\nequal value = value\n}\n",
    );

    assert_eq!(reason(&error), "impl.private-interface");
}

#[test]
fn accepts_private_impl_for_private_interface() {
    check_valid(
        "interface Equal<A> {\nequal : A -> A\n}\n\nimpl Equal<Int> {\nequal value = value\n}\n",
    );
}

#[test]
fn rejects_public_impl_with_private_prerequisite() {
    let error = check_error(concat!(
        "type Option<A> =\nNone\n| Some(A)\n",
        "interface Equal<A> {\nequal : A -> A\n}\n",
        "pub interface Render<A> {\nrender : A -> A\n}\n\n",
        "pub impl Render<Option<A>> where Equal<A> {\nrender value = value\n}\n",
    ));

    assert_eq!(reason(&error), "impl.private-interface");
}

#[test]
fn accepts_ground_prerequisite_without_subterm_decrease() {
    check_valid(concat!(
        "type Option<A> =\nNone\n| Some(A)\n",
        "interface Equal<A> {\nequal : A -> A\n}\n\n",
        "impl Equal<Option<A>> where Equal<Int> {\nequal value = value\n}\n",
    ));
}

#[test]
fn invalid_header_precedes_missing_method_membership() {
    let error = check_error("interface Equal<A> {\nequal : A -> A\n}\n\nimpl Equal<A> {\n}\n");

    assert_eq!(reason(&error), "impl.variable-head");
}

#[test]
fn checked_membership_uses_interface_order_and_authenticates_source_groups() {
    let checked = checked_valid(concat!(
        "interface Pair<A> {\nfirst : A -> A\nsecond : A -> A\n}\n\n",
        "impl Pair<Int> {\nsecond value = value\nfirst value = value\n}\n",
    ));
    let module = checked
        .last()
        .expect("the fixture should retain its module");
    let implementation = &module.checked_implementations()[0];

    assert_eq!(implementation.source_index, 0);
    assert_eq!(implementation.methods.len(), 2);
    assert_eq!(implementation.methods[0].source_group, 1);
    assert_eq!(implementation.methods[1].source_group, 0);
    assert_eq!(
        implementation.methods[0].id.method(),
        implementation.methods[0].method
    );
    assert_eq!(
        implementation.methods[1].id.method(),
        implementation.methods[1].method
    );
}

#[test]
fn checked_impl_method_owns_substituted_constrained_scheme() {
    let checked = checked_valid(concat!(
        "type Option<A> =\nNone\n| Some(A)\n",
        "interface Equal<A> {\nequal : A -> A\n}\n\n",
        "impl Equal<Option<A>> where Equal<A> {\nequal value = value\n}\n",
    ));
    let module = checked
        .last()
        .expect("the fixture should retain its module");
    let [implementation] = module.implementation_facts() else {
        panic!("the module should retain one checked implementation fact");
    };
    let [method] = implementation.methods.as_ref() else {
        panic!("the implementation should retain one checked method fact");
    };
    let [parameter] = implementation.head_parameters.as_ref() else {
        panic!("the implementation should retain its generic head parameter");
    };
    let [prerequisite] = implementation.prerequisites.as_ref() else {
        panic!("the implementation should retain its prerequisite");
    };

    assert_eq!(method.scheme.type_parameters.as_ref(), &[parameter.id]);
    let [method_requirement] = method.scheme.requirements.as_ref() else {
        panic!("the method scheme should retain its implementation prerequisite");
    };
    assert_eq!(method_requirement.id, prerequisite.id);
    assert_eq!(method_requirement.interface, prerequisite.interface);
    assert_eq!(method_requirement.argument(), prerequisite.argument());
    let Type::Function(domain, codomain) = method.scheme.value_type() else {
        panic!("the substituted method scheme should remain callable");
    };
    assert_eq!(domain.as_ref(), implementation.argument());
    assert_eq!(codomain.as_ref(), implementation.argument());
    assert_eq!(method.id.implementation(), implementation.id);
    assert_eq!(method.id.method(), method.method);
}

#[test]
fn rejects_identity_equal_local_implementation_heads() {
    let error = check_error(concat!(
        "interface Equal<A> {\nequal : A -> A\n}\n\n",
        "impl Equal<Int> {\nequal value = value\n}\n",
        "impl Equal<Int> {\nequal value = value\n}\n",
    ));

    assert_eq!(reason(&error), "impl.overlap");
}

#[test]
fn rejects_generic_local_overlap_after_pair_local_freshening() {
    let error = check_error(concat!(
        "type Option<A> =\nNone\n| Some(A)\n",
        "interface Equal<A> {\nequal : A -> A\n}\n\n",
        "impl Equal<Option<A>> {\nequal value = value\n}\n",
        "impl Equal<Option<B>> {\nequal value = value\n}\n",
    ));

    assert_eq!(reason(&error), "impl.overlap");
}

#[test]
fn allows_distinct_non_unifiable_local_heads() {
    check_valid(concat!(
        "interface Equal<A> {\nequal : A -> A\n}\n\n",
        "impl Equal<Int> {\nequal value = value\n}\n",
        "impl Equal<Bool> {\nequal value = value\n}\n",
    ));
}

#[test]
fn overlap_precedes_missing_method_membership() {
    let error = check_error(concat!(
        "interface Equal<A> {\nequal : A -> A\n}\n\n",
        "impl Equal<Int> {\nequal value = value\n}\n",
        "impl Equal<Int> {\n}\n",
    ));

    assert_eq!(reason(&error), "impl.overlap");
}

#[test]
fn checks_impl_method_body_against_the_substituted_interface_signature() {
    check_valid(concat!(
        "interface Increment<A> {\nincrement : A -> A\n}\n\n",
        "impl Increment<Int> {\nincrement value = value + 1\n}\n",
    ));
}

#[test]
fn rejects_wrong_impl_method_result_type() {
    let error = check_error(concat!(
        "interface Measure<A> {\nmeasure : A -> Int\n}\n\n",
        "impl Measure<Bool> {\nmeasure value = false\n}\n",
    ));

    assert_eq!(source_reason(&error), "type.definition-result");
}

#[test]
fn rejects_impl_method_equation_arity() {
    let error = check_error(concat!(
        "interface Keep<A> {\nkeep : A -> A\n}\n\n",
        "impl Keep<Int> {\nkeep left right = left\n}\n",
    ));

    assert_eq!(source_reason(&error), "equation.arity");
}

#[test]
fn rejects_invalid_interface_method_shape_before_impl_equation_arity() {
    let error = check_error(concat!(
        "interface Keep<A> {\nkeep : (A, Int -> Int)\n}\n\n",
        "impl Keep<Int> {\nkeep left right = left\n}\n",
    ));

    assert_eq!(reason(&error), "interface.method-not-function");
}

#[test]
fn rejects_impl_method_pattern_with_the_wrong_instantiated_type() {
    let error = check_error(concat!(
        "interface Keep<A> {\nkeep : A -> A\n}\n",
        "impl Keep<Int> {\nkeep true = 1\n}\n",
    ));

    assert_eq!(source_reason(&error), "pattern.type-mismatch");
}

#[test]
fn rejects_non_exhaustive_impl_method_equations() {
    let error = check_error(concat!(
        "interface Decide<A> {\ndecide : A -> Int\n}\n\n",
        "impl Decide<Bool> {\ndecide true = 1\n}\n",
    ));

    assert_eq!(source_reason(&error), "coverage.non-exhaustive");
}

#[test]
fn rejects_redundant_impl_method_equation() {
    let error = check_error(concat!(
        "interface Decide<A> {\ndecide : A -> Int\n}\n\n",
        "impl Decide<Bool> {\ndecide value = 1\ndecide true = 2\n}\n",
    ));

    assert_eq!(source_reason(&error), "coverage.redundant-case");
}

#[test]
fn failed_public_impl_stages_never_produce_a_checked_summary() {
    public_impl_failure_does_not_publish(
        concat!(
            "pub interface Equal<A> {\nequal : A -> A\n}\n",
            "pub impl Equal<A> {\nequal value = value\n}\n",
        ),
        "impl.variable-head",
    );

    public_impl_failure_does_not_publish(
        concat!(
            "pub interface Equal<A> {\nequal : A -> A\n}\n",
            "pub impl Equal<Int> {\n}\n",
        ),
        "impl.missing-method",
    );

    public_impl_failure_does_not_publish(
        concat!(
            "pub interface Equal<A> {\nequal : A -> A\n}\n",
            "pub impl Equal<Int> {\nequal value = false\n}\n",
        ),
        "type.definition-result",
    );
}
