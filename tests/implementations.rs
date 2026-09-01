use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    elaborate::{TypeError, check_module},
    kind::KindFailure,
    module::{ModuleGraph, ModuleRoots, load_module_graph},
    resolve::{DependencyExports, ResolveModuleError, resolve_module},
    resolved::CheckedModule,
    types::{Kind, Type},
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

fn kind_reason(text: &str) -> String {
    let fixture = ImplementationFixture::create(text, &[]);
    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty())
        .expect("the implementation kind fixture should load");
    let loaded = graph
        .module(graph.entry())
        .expect("the implementation kind fixture should retain its entry");
    match resolve_module(loaded, &[]).expect_err("the implementation kind fixture should fail") {
        ResolveModuleError::Kind(KindFailure::Source(error)) => error.reason.to_string(),
        other => panic!("expected a source kind failure, found {other:?}"),
    }
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

fn check_valid_with_dependencies(text: &str, dependencies: &[(&str, &str)]) {
    let fixture = ImplementationFixture::create(text, dependencies);
    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty())
        .expect("the implementation fixture should load");
    drop(check_graph(&graph).expect("the implementation fixture should check"));
}

fn reason(error: &TypeError) -> String {
    let TypeError::Interface(diagnostic) = error else {
        panic!("expected an interface diagnostic, found {error:?}");
    };
    diagnostic.reason.to_string()
}

#[test]
fn complete_interface_arity_is_reported_for_every_source_application_owner() {
    const DECLARATIONS: &str = concat!(
        "interface Pair<Left, Right> {\n",
        "pair : (Left, Right) -> Left\n",
        "}\n\n",
        "interface Keep<Value> {\n",
        "keep : Value -> Value\n",
        "}\n\n",
    );
    let cases = [
        (
            "global requirement missing an argument",
            "value : Unit -> Unit where Pair<Int>\nvalue () = ()\n",
        ),
        (
            "global requirement has an extra argument",
            "value : Unit -> Unit where Pair<Int, Bool, Unit>\nvalue () = ()\n",
        ),
        (
            "implementation head is missing an argument",
            "impl Pair<Int> {\npair value = 1\n}\n",
        ),
        (
            "implementation head has an extra argument",
            "impl Pair<Int, Bool, Unit> {\npair value = 1\n}\n",
        ),
        (
            "implementation prerequisite is missing an argument",
            "impl Keep<Int> where Pair<Int> {\nkeep value = value\n}\n",
        ),
        (
            "implementation prerequisite has an extra argument",
            "impl Keep<Int> where Pair<Int, Bool, Unit> {\nkeep value = value\n}\n",
        ),
    ];

    for (label, declaration) in cases {
        let error = check_error(&format!("{DECLARATIONS}{declaration}"));
        assert_eq!(reason(&error), "interface.argument-count", "{label}");
    }
}

#[test]
fn interface_argument_count_precedes_positional_kind_checking() {
    let error = check_error(concat!(
        "type Option<A> =\nNone\n| Some(A)\n\n",
        "interface Higher<F : Type -> Type, Value> {\n",
        "higher : F<Value> -> Value\n",
        "}\n\n",
        "value : Unit -> Unit where Higher<Int, Option, Bool>\n",
        "value () = ()\n",
    ));

    assert_eq!(reason(&error), "interface.argument-count");
}

fn source_reason(error: &TypeError) -> String {
    let TypeError::Source(diagnostic) = error else {
        panic!("expected a typed source diagnostic, found {error:?}");
    };
    diagnostic.reason.to_string()
}

#[test]
fn implementation_prerequisites_classify_complete_identity_before_determined_key() {
    const DECLARATIONS: &str = concat!(
        "interface Relation<Key, Value> where Key -> Value {\n",
        "relate : Key -> Int\n",
        "}\n\n",
        "interface Target<A> {\n",
        "target : A -> A\n",
        "}\n\n",
    );
    for (label, prerequisites, expected) in [
        (
            "complete determined duplicate",
            "Relation<Int, Bool>, Relation<Int, Bool>",
            "constraint.duplicate-requirement",
        ),
        (
            "same determined key with distinct dependents",
            "Relation<Int, Bool>, Relation<Int, Unit>",
            "constraint.determination-conflict",
        ),
    ] {
        let error = check_error(&format!(
            "{DECLARATIONS}impl Target<Int> where {prerequisites} {{\ntarget value = value\n}}\n"
        ));
        assert_eq!(reason(&error), expected, "{label}");
    }
}

#[test]
fn application_preflight_precedes_implementation_prerequisite_classification() {
    let arity = check_error(concat!(
        "interface Pair<Left, Right> {\npair : (Left, Right) -> Left\n}\n\n",
        "interface Target<A> {\ntarget : A -> A\n}\n\n",
        "impl Target<Int> where Pair<Int>, Pair<Int> {\n",
        "target value = value\n",
        "}\n",
    ));
    assert_eq!(reason(&arity), "interface.argument-count");

    let kind = kind_reason(concat!(
        "type Option<A> =\nNone\n| Some(A)\n",
        "interface Higher<F : Type -> Type, Value> {\n",
        "higher : F<Value> -> Value\n",
        "}\n\n",
        "interface Target<A> {\ntarget : A -> A\n}\n\n",
        "impl Target<Int> where Higher<Int, Bool>, Higher<Int, Bool> {\n",
        "target value = value\n",
        "}\n",
    ));
    assert_eq!(kind, "kind.argument");
}

#[test]
fn no_edge_implementation_prerequisite_duplicates_retain_predecessor_behavior() {
    let error = check_error(concat!(
        "interface Inspect<A> {\ninspect : A -> A\n}\n\n",
        "impl Inspect<Int> where Inspect<Bool>, Inspect<Bool> {\n",
        "inspect value = value\n",
        "}\n",
    ));

    assert_eq!(reason(&error), "constraint.duplicate-requirement");
}

#[test]
fn distinct_implementation_prerequisite_keys_remain_valid_with_and_without_an_edge() {
    check_valid(concat!(
        "type Pair<A, B> = Pair(A, B)\n",
        "interface Inspect<A> {\ninspect : A -> Int\n}\n\n",
        "impl<A, B> Inspect<Pair<A, B>> where Inspect<A>, Inspect<B> {\n",
        "inspect value = 0\n",
        "}\n",
    ));
    check_valid(concat!(
        "type List<A> =\nNil\n| Cons(A, List<A>)\n",
        "interface Relation<Key, Value> where Key -> Value {\n",
        "relate : Key -> Int\n",
        "}\n\n",
        "impl<A> Relation<List<A>, A> where Relation<A, A>, Relation<Bool, Unit> {\n",
        "relate value = 0\n",
        "}\n",
    ));
}

#[test]
fn duplicate_prerequisites_precede_all_later_implementation_header_failures() {
    let early_header_failures = check_error(concat!(
        "interface Requirement<A> {\nrequirement : A -> Int\n}\n\n",
        "interface Relation<Key, Value> where Key -> Value {\n",
        "relate : Key -> Int\n",
        "}\n\n",
        "impl<Key, Value> Relation<Key, Value> ",
        "where Requirement<Missing>, Requirement<Missing> {\n",
        "relate value = 0\n",
        "}\n",
    ));
    assert_eq!(
        reason(&early_header_failures),
        "constraint.duplicate-requirement",
        "prerequisite classification must precede variable-head, containment, and coverage",
    );

    let later_header_failures = check_error_with_dependencies(
        concat!(
            "import dependency (Foreign, foreign)\n",
            "interface Private<A> {\nprivate : A -> Int\n}\n\n",
            "pub impl<A> Foreign<A -> A> ",
            "where Private<A -> A>, Private<A -> A> {\n",
            "foreign value = 0\n",
            "}\n",
        ),
        &[(
            "dependency.ash",
            "pub interface Foreign<A> {\nforeign : A -> Int\n}\n",
        )],
    );
    assert_eq!(
        reason(&later_header_failures),
        "constraint.duplicate-requirement",
        "prerequisite classification must precede orphan ownership, decrease, and privacy",
    );
}

#[test]
fn rejects_bare_type_variable_impl_head() {
    let error = check_error(
        "interface Equal<A> {\nequal : A -> A\n}\n\nimpl Equal<A> {\nequal value = value\n}\n",
    );

    assert_eq!(reason(&error), "impl.variable-head");
}

#[test]
fn determined_impl_rejects_a_dependent_variable_absent_from_the_key() {
    let error = check_error(concat!(
        "interface Relation<A, B> where A -> B {\n",
        "relate : A -> Int\n",
        "}\n\n",
        "impl<B> Relation<Int, B> {\n",
        "relate value = 0\n",
        "}\n",
    ));

    assert_eq!(reason(&error), "impl.determination-coverage");
}

#[test]
fn determined_impl_rejects_an_all_bare_key_with_a_constant_dependent() {
    let error = check_error(concat!(
        "interface Relation<A, B> where A -> B {\n",
        "relate : A -> Int\n",
        "}\n\n",
        "impl<A> Relation<A, Bool> {\n",
        "relate value = 0\n",
        "}\n",
    ));

    assert_eq!(reason(&error), "impl.variable-head");
}

#[test]
fn determined_impl_accepts_constant_and_key_constructed_dependents() {
    check_valid(concat!(
        "type List<A> =\nNil\n| Cons(A, List<A>)\n",
        "interface Relation<A, B> where A -> B {\n",
        "relate : A -> Int\n",
        "}\n\n",
        "impl Relation<Int, Bool> {\nrelate value = 0\n}\n",
        "impl<A> Relation<List<A>, A> {\nrelate value = 0\n}\n",
    ));
}

#[test]
fn variable_head_precedes_prerequisite_containment_and_determination_coverage() {
    let error = check_error(concat!(
        "interface Relation<A, B> where A -> B {\n",
        "relate : A -> Int\n",
        "}\n\n",
        "impl<A, B> Relation<A, B> where Relation<Int, C> {\n",
        "relate value = 0\n",
        "}\n",
    ));

    assert_eq!(reason(&error), "impl.variable-head");
}

#[test]
fn prerequisite_containment_precedes_determination_coverage() {
    let error = check_error(concat!(
        "interface Relation<A, B> where A -> B {\n",
        "relate : A -> Int\n",
        "}\n\n",
        "impl<B> Relation<Int, B> where Relation<Int, C> {\n",
        "relate value = 0\n",
        "}\n",
    ));

    assert_eq!(reason(&error), "impl.prerequisite-variable");
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
fn explicit_impl_prerequisite_only_candidate_keeps_interface_failure_ownership() {
    let error = check_error(concat!(
        "type Head<A> = Head(A)\n",
        "type Pair<Left, Right> = Pair(Left, Right)\n",
        "interface Equal<A> {\nequal : A -> A\n}\n\n",
        "impl<A : Type> Equal<Head<A>> where Equal<Pair<A, B>> {\n",
        "equal value = value\n",
        "}\n",
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
fn foreign_interface_accepts_a_bare_local_nominal_owner() {
    check_valid_with_dependencies(
        concat!(
            "import owners (Owner, owner)\n",
            "type Local<Left, Right> = Local(Left, Right)\n\n",
            "impl Owner<Local> {\nowner value = 0\n}\n",
        ),
        &[(
            "owners.ash",
            concat!(
                "pub interface Owner<F : Type -> Type -> Type> {\n",
                "owner : F<Int, Bool> -> Int\n",
                "}\n",
            ),
        )],
    );
}

#[test]
fn foreign_interface_accepts_a_partial_local_nominal_owner() {
    check_valid_with_dependencies(
        concat!(
            "import owners (Owner, owner)\n",
            "type Local<Left, Right> = Local(Left, Right)\n\n",
            "impl Owner<Local<Int>> {\nowner value = 0\n}\n",
        ),
        &[(
            "owners.ash",
            concat!(
                "pub interface Owner<F : Type -> Type> {\n",
                "owner : F<Int> -> Int\n",
                "}\n",
            ),
        )],
    );
}

#[test]
fn foreign_interface_accepts_a_saturated_local_nominal_owner() {
    check_valid_with_dependencies(
        concat!(
            "import owners (Owner, owner)\n",
            "type Local<Left, Right> = Local(Left, Right)\n\n",
            "impl Owner<Local<Int, Bool>> {\nowner value = 0\n}\n",
        ),
        &[(
            "owners.ash",
            "pub interface Owner<A> {\nowner : A -> Int\n}\n",
        )],
    );
}

#[test]
fn foreign_relational_interface_accepts_local_nominal_ownership_in_the_second_argument() {
    check_valid_with_dependencies(
        concat!(
            "import owners (Owner, owner)\n",
            "type Local = Local\n\n",
            "impl Owner<Int, Local> {\nowner value = 0\n}\n",
        ),
        &[(
            "owners.ash",
            concat!(
                "pub interface Owner<Left, Right> {\n",
                "owner : (Left, Right) -> Int\n",
                "}\n",
            ),
        )],
    );
}

#[test]
fn foreign_determined_interface_rejects_local_nominal_ownership_only_in_a_dependent() {
    let error = check_error_with_dependencies(
        concat!(
            "import owners (Owner, owner)\n",
            "type Local = Local\n\n",
            "impl Owner<Int, Local> {\nowner value = 0\n}\n",
        ),
        &[(
            "owners.ash",
            concat!(
                "pub interface Owner<Key, Dependent> where Key -> Dependent {\n",
                "owner : Key -> Int\n",
                "}\n",
            ),
        )],
    );

    assert_eq!(reason(&error), "impl.orphan");
}

#[test]
fn foreign_determined_interface_accepts_a_local_outer_nominal_in_the_key() {
    check_valid_with_dependencies(
        concat!(
            "import owners (Owner, owner)\n",
            "type Local = Local\n\n",
            "impl Owner<Local, Bool> {\nowner value = 0\n}\n",
        ),
        &[(
            "owners.ash",
            concat!(
                "pub interface Owner<Key, Dependent> where Key -> Dependent {\n",
                "owner : Key -> Int\n",
                "}\n",
            ),
        )],
    );
}

#[test]
fn foreign_determined_interface_rejects_a_local_nominal_below_the_key_spine() {
    let error = check_error_with_dependencies(
        concat!(
            "import owners (Foreign, Owner, owner)\n",
            "type Local = Local\n\n",
            "impl Owner<Foreign<Local>, Bool> {\nowner value = 0\n}\n",
        ),
        &[(
            "owners.ash",
            concat!(
                "pub type Foreign<A> = Foreign(A)\n",
                "pub interface Owner<Key, Dependent> where Key -> Dependent {\n",
                "owner : Key -> Int\n",
                "}\n",
            ),
        )],
    );

    assert_eq!(reason(&error), "impl.orphan");
}

#[test]
fn foreign_interface_rejects_local_nominal_outside_the_function_spine() {
    const OWNERS: &str = concat!(
        "pub type Foreign<A> = Foreign(A)\n",
        "pub interface Owner<A> {\nowner : A -> Int\n}\n",
    );
    for head in ["Foreign<Local>", "(Local, Int)", "Local -> Int"] {
        let source = format!(
            concat!(
                "import owners (Foreign, Owner, owner)\n",
                "type Local = Local\n\n",
                "impl Owner<{head}> {{\nowner value = 0\n}}\n",
            ),
            head = head,
        );
        let error = check_error_with_dependencies(&source, &[("owners.ash", OWNERS)]);

        assert_eq!(reason(&error), "impl.orphan", "unexpected owner for {head}");
    }
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
fn accepts_application_function_child_as_a_strict_subterm_prerequisite() {
    check_valid(concat!(
        "type Pair<Left, Right> = Pair(Left, Right)\n",
        "interface Construct<F : Type -> Type> {\nconstruct : F<Int> -> Bool\n}\n",
        "interface Inspect<A> {\ninspect : A -> Bool\n}\n\n",
        "impl<Left : Type, Right : Type> Inspect<Pair<Left, Right>> ",
        "where Construct<Pair<Left>> {\n",
        "inspect value = true\n",
        "}\n",
    ));
}

#[test]
fn rejects_a_different_partial_constructor_as_a_function_child_subterm() {
    let error = check_error(concat!(
        "type Pair<Left, Right> = Pair(Left, Right)\n",
        "interface Construct<F : Type -> Type> {\nconstruct : F<Int> -> Bool\n}\n",
        "interface Inspect<A> {\ninspect : A -> Bool\n}\n\n",
        "impl<Left : Type, Right : Type> Inspect<Pair<Left, Right>> ",
        "where Construct<Pair<Right>> {\n",
        "inspect value = true\n",
        "}\n",
    ));

    assert_eq!(reason(&error), "impl.prerequisite-not-decreasing");
}

#[test]
fn rejects_an_expansion_of_the_application_argument_subterm() {
    let error = check_error(concat!(
        "type Option<A> =\nNone\n| Some(A)\n",
        "type Pair<Left, Right> = Pair(Left, Right)\n",
        "interface Inspect<A> {\ninspect : A -> Bool\n}\n\n",
        "impl<Left : Type, Right : Type> Inspect<Pair<Left, Right>> ",
        "where Inspect<Option<Right>> {\n",
        "inspect value = true\n",
        "}\n",
    ));

    assert_eq!(reason(&error), "impl.prerequisite-not-decreasing");
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
fn invalid_relational_variable_head_precedes_private_interface_exposure() {
    let error = check_error(concat!(
        "interface Relation<Left, Right> {\n",
        "relation : (Left, Right) -> Bool\n",
        "}\n\n",
        "pub impl Relation<Left, Right> {\n",
        "relation pair = true\n",
        "}\n",
    ));

    assert_eq!(reason(&error), "impl.variable-head");
}

#[test]
fn accepts_private_impl_for_private_interface() {
    check_valid(
        "interface Equal<A> {\nequal : A -> A\n}\n\nimpl Equal<Int> {\nequal value = value\n}\n",
    );
}

#[test]
fn representation_does_not_supply_nominal_interface_evidence() {
    let error = check_error(concat!(
        "newtype UserId = UserId(Int)\n\n",
        "interface Render<A> {\nrender : A -> Int\n}\n\n",
        "impl Render<Int> {\nrender value = value\n}\n\n",
        "main : Unit -> Int\n",
        "main () = render(UserId(41))\n",
    ));

    assert_eq!(reason(&error), "constraint.unsatisfied");
}

#[test]
fn explicit_nominal_newtype_implementation_supplies_its_own_evidence() {
    check_valid(concat!(
        "newtype UserId = UserId(Int)\n\n",
        "interface Render<A> {\nrender : A -> Int\n}\n\n",
        "impl Render<UserId> {\nrender (UserId(value)) = value\n}\n\n",
        "main : Unit -> Int\n",
        "main () = render(UserId(41))\n",
    ));
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
fn accepts_ground_prerequisite_with_a_different_interface_width() {
    check_valid(concat!(
        "type List<A> =\nNil\n| Cons(A, List<A>)\n",
        "interface Relation<Left, Right> {\nrelation : (Left, Right) -> Bool\n}\n",
        "interface Show<Value> {\nshow : Value -> Bool\n}\n\n",
        "impl Relation<List<A>, A> where Show<Int> {\nrelation value = true\n}\n",
    ));
}

#[test]
fn rejects_non_ground_prerequisite_with_a_different_interface_width() {
    let error = check_error(concat!(
        "type List<A> =\nNil\n| Cons(A, List<A>)\n",
        "interface Relation<Left, Right> {\nrelation : (Left, Right) -> Bool\n}\n",
        "interface Show<Value> {\nshow : Value -> Bool\n}\n\n",
        "impl Relation<List<A>, A> where Show<A> {\nrelation value = true\n}\n",
    ));

    assert_eq!(reason(&error), "impl.prerequisite-not-decreasing");
}

#[test]
fn relational_prerequisite_accepts_pointwise_equality_with_strict_second_argument() {
    check_valid(concat!(
        "type List<A> =\nNil\n| Cons(A, List<A>)\n",
        "interface Relation<Left, Right> {\nrelation : (Left, Right) -> Bool\n}\n\n",
        "impl Relation<List<A>, List<A>> where Relation<List<A>, A> {\n",
        "relation value = true\n",
        "}\n",
    ));
}

#[test]
fn relational_prerequisite_rejects_a_non_pointwise_expansion() {
    let error = check_error(concat!(
        "type List<A> =\nNil\n| Cons(A, List<A>)\n",
        "interface Relation<Left, Right> {\nrelation : (Left, Right) -> Bool\n}\n\n",
        "impl Relation<List<A>, A> where Relation<A, List<A>> {\n",
        "relation value = true\n",
        "}\n",
    ));

    assert_eq!(reason(&error), "impl.prerequisite-not-decreasing");
}

#[test]
fn relational_prerequisite_rejects_pointwise_equality_without_a_strict_position() {
    let error = check_error(concat!(
        "type List<A> =\nNil\n| Cons(A, List<A>)\n",
        "interface Relation<Left, Right> {\nrelation : (Left, Right) -> Bool\n}\n\n",
        "impl Relation<List<A>, A> where Relation<List<A>, A> {\n",
        "relation value = true\n",
        "}\n",
    ));

    assert_eq!(reason(&error), "impl.prerequisite-not-decreasing");
}

#[test]
fn determined_prerequisite_rejects_decrease_only_in_a_dependent_argument() {
    let error = check_error(concat!(
        "type List<A> =\nNil\n| Cons(A, List<A>)\n",
        "interface Relation<A, B> where A -> B {\n",
        "relate : A -> Int\n",
        "}\n\n",
        "impl<A> Relation<List<A>, List<A>> where Relation<List<A>, A> {\n",
        "relate value = 0\n",
        "}\n",
    ));

    assert_eq!(reason(&error), "impl.prerequisite-not-decreasing");
}

#[test]
fn determined_multi_input_prerequisite_accepts_equal_and_strict_key_components() {
    check_valid(concat!(
        "type List<A> =\nNil\n| Cons(A, List<A>)\n",
        "type Option<A> =\nNone\n| Some(A)\n",
        "interface Relation<A, B, C> where (A, B) -> C {\n",
        "relate : (A, B) -> Int\n",
        "}\n\n",
        "impl<A, B> Relation<List<A>, Option<B>, (A, B)> ",
        "where Relation<A, Option<B>, (A, B)> {\n",
        "relate pair = 0\n",
        "}\n",
    ));
}

#[test]
fn determined_multi_input_prerequisite_rejects_all_equal_key_components() {
    let error = check_error(concat!(
        "type List<A> =\nNil\n| Cons(A, List<A>)\n",
        "type Option<A> =\nNone\n| Some(A)\n",
        "interface Relation<A, B, C> where (A, B) -> C {\n",
        "relate : (A, B) -> Int\n",
        "}\n\n",
        "impl<A, B> Relation<List<A>, Option<B>, (A, B)> ",
        "where Relation<List<A>, Option<B>, (A, B)> {\n",
        "relate pair = 0\n",
        "}\n",
    ));

    assert_eq!(reason(&error), "impl.prerequisite-not-decreasing");
}

#[test]
fn determined_multi_input_prerequisite_rejects_a_non_subterm_key_component() {
    let error = check_error(concat!(
        "type List<A> =\nNil\n| Cons(A, List<A>)\n",
        "type Option<A> =\nNone\n| Some(A)\n",
        "interface Relation<A, B, C> where (A, B) -> C {\n",
        "relate : (A, B) -> Int\n",
        "}\n\n",
        "impl<A, B> Relation<List<A>, Option<B>, (A, B)> ",
        "where Relation<A, List<B>, (A, B)> {\n",
        "relate pair = 0\n",
        "}\n",
    ));

    assert_eq!(reason(&error), "impl.prerequisite-not-decreasing");
}

#[test]
fn determined_generic_prerequisite_rejects_a_different_key_width() {
    let error = check_error(concat!(
        "type List<A> =\nNil\n| Cons(A, List<A>)\n",
        "type Option<A> =\nNone\n| Some(A)\n",
        "interface Wide<A, B, C> where (A, B) -> C {\n",
        "wide : (A, B) -> Int\n",
        "}\n",
        "interface Narrow<A, B> where A -> B {\n",
        "narrow : A -> Int\n",
        "}\n\n",
        "impl<A, B> Wide<List<A>, Option<B>, (A, B)> where Narrow<A, A> {\n",
        "wide pair = 0\n",
        "}\n",
    ));

    assert_eq!(reason(&error), "impl.prerequisite-not-decreasing");
}

#[test]
fn determined_ground_prerequisite_keeps_the_complete_application_exemption() {
    check_valid(concat!(
        "type List<A> =\nNil\n| Cons(A, List<A>)\n",
        "type Option<A> =\nNone\n| Some(A)\n",
        "interface Wide<A, B, C> where (A, B) -> C {\n",
        "wide : (A, B) -> Int\n",
        "}\n",
        "interface Narrow<A, B> where A -> B {\n",
        "narrow : A -> Int\n",
        "}\n\n",
        "impl<A, B> Wide<List<A>, Option<B>, (A, B)> where Narrow<Int, Bool> {\n",
        "wide pair = 0\n",
        "}\n",
    ));
}

#[test]
fn determined_prerequisite_accepts_dependent_growth_when_the_key_strictly_decreases() {
    check_valid(concat!(
        "type List<A> =\nNil\n| Cons(A, List<A>)\n",
        "interface Relation<A, B> where A -> B {\n",
        "relate : A -> Int\n",
        "}\n\n",
        "impl<A> Relation<List<A>, A> where Relation<A, List<A>> {\n",
        "relate value = 0\n",
        "}\n",
    ));
}

#[test]
fn invalid_header_precedes_missing_method_membership() {
    let error = check_error("interface Equal<A> {\nequal : A -> A\n}\n\nimpl Equal<A> {\n}\n");

    assert_eq!(reason(&error), "impl.variable-head");
}

#[test]
fn polymorphic_method_membership_uses_interface_order_and_authenticates_source_groups() {
    let checked = checked_valid(concat!(
        "interface Pair<A> {\nfirst<X> : (A, X) -> A\nsecond<Y> : (A, Y) -> A\n}\n\n",
        "impl Pair<Int> {\nsecond (value, ignored) = value\nfirst (value, ignored) = value\n}\n",
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
        module.interface_facts()[0].methods[0]
            .type_parameters()
            .len(),
        1
    );
    assert_eq!(
        module.interface_facts()[0].methods[1]
            .type_parameters()
            .len(),
        1
    );
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

    let [(method_parameter, method_kind)] = method.scheme.type_parameters.as_ref() else {
        panic!("the method scheme should retain its generic head parameter");
    };
    assert_eq!(*method_parameter, parameter.id);
    assert_eq!(method_kind, &parameter.kind);
    let [method_requirement] = method.scheme.requirements.as_ref() else {
        panic!("the method scheme should retain its implementation prerequisite");
    };
    assert_eq!(method_requirement.id, prerequisite.id);
    assert_eq!(method_requirement.interface(), prerequisite.interface());
    assert_eq!(method_requirement.arguments(), prerequisite.arguments());
    let Type::Function(domain, codomain) = method.scheme.value_type() else {
        panic!("the substituted method scheme should remain callable");
    };
    let [head_argument] = implementation.arguments() else {
        panic!("the unary implementation should retain one head argument");
    };
    assert_eq!(domain.as_ref(), head_argument);
    assert_eq!(codomain.as_ref(), head_argument);
    assert_eq!(method.id.implementation(), implementation.id);
    assert_eq!(method.id.method(), method.method);
}

#[test]
fn checked_impl_method_scheme_retains_declared_function_kind() {
    let checked = checked_valid(concat!(
        "type Holder<F : Type -> Type> = Holder\n\n",
        "interface Observe<A> {\nobserve : A -> Bool\n}\n\n",
        "impl<F : Type -> Type> Observe<Holder<F>> {\n",
        "observe value = true\n",
        "}\n",
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
    let [(parameter, kind)] = method.scheme.type_parameters.as_ref() else {
        panic!("the method scheme should retain one canonical binder");
    };

    assert_eq!(*parameter, implementation.head_parameters[0].id);
    assert_eq!(
        kind,
        &Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type))
    );
}

#[test]
fn implementation_method_scheme_orders_head_then_method_parameters() {
    let checked = checked_valid(concat!(
        "type Holder<H> = Holder(H)\n\n",
        "interface Keep<I> {\n",
        "keep<A, F : Type -> Type> : (I, A, F<A>) -> F<A>\n",
        "}\n\n",
        "impl<H> Keep<Holder<H>> {\n",
        "keep (owner, key, value) = value\n",
        "}\n",
    ));
    let module = checked
        .last()
        .expect("the fixture should retain its module");
    let [interface] = module.interface_facts() else {
        panic!("the module should retain one checked interface fact");
    };
    let [interface_method] = interface.methods.as_ref() else {
        panic!("the interface should retain one checked method scheme");
    };
    let [implementation] = module.implementation_facts() else {
        panic!("the module should retain one checked implementation fact");
    };
    let [implementation_method] = implementation.methods.as_ref() else {
        panic!("the implementation should retain one checked method fact");
    };
    let [head] = implementation.head_parameters.as_ref() else {
        panic!("the implementation should retain one rigid head parameter");
    };
    let [method_argument, method_constructor] = interface_method.type_parameters() else {
        panic!("the interface method should retain its two ordered local parameters");
    };
    let [
        (first, first_kind),
        (second, second_kind),
        (third, third_kind),
    ] = implementation_method.scheme.type_parameters.as_ref()
    else {
        panic!("the implementation scheme should retain head then method parameters");
    };

    assert_eq!(implementation_method.head_type_parameter_count(), 1);
    assert_eq!((*first, first_kind), (head.id, &head.kind));
    assert_eq!(
        (*second, second_kind),
        (method_argument.id, &method_argument.kind)
    );
    assert_eq!(
        (*third, third_kind),
        (method_constructor.id, &method_constructor.kind)
    );
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
fn relational_implementation_heads_differing_only_in_argument_two_do_not_overlap() {
    check_valid(concat!(
        "interface Relation<Left, Right> {\nrelation : (Left, Right) -> Bool\n}\n\n",
        "impl Relation<Int, Bool> {\nrelation value = true\n}\n",
        "impl Relation<Int, Unit> {\nrelation value = true\n}\n",
    ));
}

#[test]
fn relational_implementation_heads_unifying_only_through_argument_two_overlap() {
    let error = check_error(concat!(
        "type Wrap<A> = Wrap(A)\n",
        "interface Relation<Left, Right> {\nrelation : (Left, Right) -> Bool\n}\n\n",
        "impl Relation<Int, Wrap<A>> {\nrelation value = true\n}\n",
        "impl Relation<Int, Wrap<Bool>> {\nrelation value = true\n}\n",
    ));

    assert_eq!(reason(&error), "impl.overlap");
}

#[test]
fn determined_local_generic_and_ground_heads_with_one_key_conflict() {
    let error = check_error(concat!(
        "type List<A> =\nNil\n| Cons(A, List<A>)\n",
        "interface Relation<A, B> where A -> B {\n",
        "relate : A -> Int\n",
        "}\n\n",
        "impl<A> Relation<List<A>, A> {\nrelate value = 0\n}\n",
        "impl Relation<List<Int>, Bool> {\nrelate value = 0\n}\n",
    ));

    assert_eq!(reason(&error), "impl.determination-conflict");
}

#[test]
fn determined_heads_that_unify_completely_retain_overlap_ownership() {
    let error = check_error(concat!(
        "type List<A> =\nNil\n| Cons(A, List<A>)\n",
        "interface Relation<A, B> where A -> B {\n",
        "relate : A -> Int\n",
        "}\n\n",
        "impl<A> Relation<List<A>, A> {\nrelate value = 0\n}\n",
        "impl Relation<List<Int>, Int> {\nrelate value = 0\n}\n",
    ));

    assert_eq!(reason(&error), "impl.overlap");
}

#[test]
fn determined_heads_with_nonunifying_keys_are_coherent() {
    check_valid(concat!(
        "type List<A> =\nNil\n| Cons(A, List<A>)\n",
        "interface Relation<A, B> where A -> B {\n",
        "relate : A -> Int\n",
        "}\n\n",
        "impl<A> Relation<List<A>, A> {\nrelate value = 0\n}\n",
        "impl Relation<Int, Bool> {\nrelate value = 0\n}\n",
    ));
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
fn rejects_overlapping_higher_kinded_partial_heads() {
    let error = check_error(concat!(
        "type Pair<Left, Right> = Pair(Left, Right)\n",
        "interface Construct<F : Type -> Type> {\nconstruct : F<Int> -> Bool\n}\n\n",
        "impl<Left : Type> Construct<Pair<Left>> {\nconstruct value = true\n}\n",
        "impl<Right : Type> Construct<Pair<Right>> {\nconstruct value = true\n}\n",
    ));

    assert_eq!(reason(&error), "impl.overlap");
}

#[test]
fn allows_distinct_higher_kinded_partial_heads() {
    check_valid(concat!(
        "type First<Left, Right> = First(Left, Right)\n",
        "type Second<Left, Right> = Second(Left, Right)\n",
        "interface Construct<F : Type -> Type> {\nconstruct : F<Int> -> Bool\n}\n\n",
        "impl<Left : Type> Construct<First<Left>> {\nconstruct value = true\n}\n",
        "impl<Right : Type> Construct<Second<Right>> {\nconstruct value = true\n}\n",
    ));
}

#[test]
fn allows_heads_that_overlap_only_with_higher_order_matching() {
    check_valid(concat!(
        "type Box<A> = Box(A)\n",
        "type Option<A> =\nNone\n| Some(A)\n",
        "interface Mark<A> {\nmark : A -> Bool\n}\n\n",
        "impl<F : Type -> Type> Mark<Box<F<Int>>> {\nmark value = true\n}\n",
        "impl Mark<Box<Option<Bool>>> {\nmark value = true\n}\n",
        "main : Unit -> Bool\n",
        "main () = mark(Box(Some(true)))\n",
    ));
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
            "pub interface Inspect<A> {\ninspect : A -> A\n}\n",
            "pub impl Inspect<Int> where Inspect<Bool>, Inspect<Bool> {\n",
            "inspect value = value\n",
            "}\n",
        ),
        "constraint.duplicate-requirement",
    );

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
