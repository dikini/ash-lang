use std::{
    fs,
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    core::{PureComputation, PureExprKind, transform::identity_traversal, validate_modules},
    elaborate::{ElaborationFailure, Elaborator, TypeError, check_module, link_modules},
    eval::evaluate,
    evidence_validation::validate_interface_evidence,
    module::{ModuleGraph, ModuleId, ModuleRoots, load_module_graph},
    resolve::{DependencyExports, resolve_module},
    resolved::CheckedModule,
    types::Type,
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct TempTree(PathBuf);

impl TempTree {
    fn create() -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "ash-module-elaboration-{}-{id}",
                std::process::id()
            ));
            match fs::create_dir(&path) {
                Ok(()) => return Self(path),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("test tree should be creatable: {error}"),
            }
        }
    }

    fn write(&self, relative: &str, text: &str) -> PathBuf {
        let path = self.0.join(relative);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).expect("fixture parent should be creatable");
        }
        fs::write(&path, text).expect("fixture should be writable");
        path
    }
}

impl Drop for TempTree {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn load(tree: &TempTree, entry: &str, dependencies: &[(&str, &str)]) -> ModuleGraph {
    let entry = tree.write("entry.ash", entry);
    for (path, text) in dependencies {
        tree.write(path, text);
    }
    load_module_graph(&entry, &ModuleRoots::empty()).expect("fixture graph should load")
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

fn checked_module<'a>(
    graph: &ModuleGraph,
    checked: &'a [CheckedModule],
    file_name: &str,
) -> &'a CheckedModule {
    let id = graph
        .modules()
        .iter()
        .find(|module| {
            Path::new(module.source().display_path()).file_name() == Some(file_name.as_ref())
        })
        .map(|module| module.id())
        .expect("loaded module should be present");
    checked
        .iter()
        .find(|module| module.module() == id)
        .expect("checked module should retain its identity")
}

fn contains_inference(root: &Type) -> bool {
    let mut pending = vec![root];
    while let Some(ty) = pending.pop() {
        match ty {
            Type::Inference(_) => return true,
            Type::Tuple(elements) | Type::AppliedNominal(_, elements) => {
                pending.extend(elements.iter());
            }
            Type::Function(domain, codomain) => {
                pending.push(codomain);
                pending.push(domain);
            }
            Type::Forall(_, body) => pending.push(body),
            Type::Int | Type::Bool | Type::Unit | Type::Nominal(_) | Type::Variable(_) => {}
        }
    }
    false
}

#[test]
fn imported_polymorphic_scheme_instantiates_at_unrelated_types_without_re_generalizing() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        concat!(
            "import dependency as Dep\n",
            "at_int : Int -> Int\n",
            "at_int value = Dep.id(value)\n",
            "at_bool : Bool -> Bool\n",
            "at_bool value = Dep.id(value)\n",
        ),
        &[("dependency.ash", "pub id : A -> A\nid value = value\n")],
    );

    let checked = check_graph(&graph).expect("both instantiations should type-check");
    let dependency = checked_module(&graph, &checked, "dependency.ash");
    let exported = dependency
        .schemes()
        .iter()
        .find(|scheme| scheme.spelling == "id")
        .expect("the dependency should retain its checked id scheme");

    assert_eq!(exported.scheme.type_parameters.len(), 1);
    assert!(exported.scheme.requirements.is_empty());
    assert!(!contains_inference(&exported.scheme.value_type));
    assert_eq!(dependency.exports().module(), dependency.module());
}

#[test]
fn failed_module_body_never_publishes_an_export_summary() {
    let tree = TempTree::create();
    let graph = load(&tree, "pub broken : Unit -> Int\nbroken () = false\n", &[]);

    let error = check_graph(&graph).expect_err("the declared result and body disagree");

    assert!(matches!(
        error,
        TypeError::Mismatch(_) | TypeError::Source(_)
    ));
}

#[test]
fn checked_modules_keep_their_stable_graph_identity() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "private : Unit -> Unit\nprivate value = value\n",
        &[],
    );
    let expected: ModuleId = graph.entry();

    let checked = check_graph(&graph).expect("the module should check");

    assert_eq!(checked[0].module(), expected);
}

#[test]
fn linker_rejects_an_omitted_direct_dependency_even_when_the_import_is_unused() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import dependency as Dependency\n\npub main : Unit -> Int\nmain () = 42\n",
        &[("dependency.ash", "pub value : Unit -> Int\nvalue () = 1\n")],
    );
    let checked = check_graph(&graph).expect("the complete graph should check");
    let entry = checked
        .into_iter()
        .find(|module| module.module() == graph.entry())
        .expect("the entry module should be checked");

    let error = link_modules(vec![entry], graph.entry())
        .expect_err("linking should require every retained direct dependency");

    assert_eq!(error, TypeError::Internal(ElaborationFailure::InvalidState));
}

#[test]
fn linker_rejects_a_direct_dependency_after_its_importer() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import dependency as Dependency\n\npub main : Unit -> Int\nmain () = 42\n",
        &[("dependency.ash", "pub value : Unit -> Int\nvalue () = 1\n")],
    );
    let mut checked = check_graph(&graph).expect("the complete graph should check");
    checked.reverse();

    let error = link_modules(checked, graph.entry())
        .expect_err("linking should require dependencies before their importers");

    assert_eq!(error, TypeError::Internal(ElaborationFailure::InvalidState));
}

#[test]
fn linker_rejects_an_unrelated_checked_module_from_another_graph() {
    let entry_tree = TempTree::create();
    let entry_graph = load(&entry_tree, "pub main : Unit -> Int\nmain () = 42\n", &[]);
    let unrelated_tree = TempTree::create();
    let unrelated_graph = load(
        &unrelated_tree,
        "pub value : Unit -> Int\nvalue () = 1\n",
        &[],
    );
    let mut checked = check_graph(&unrelated_graph).expect("the unrelated graph should check");
    checked.extend(check_graph(&entry_graph).expect("the entry graph should check"));

    let error = link_modules(checked, entry_graph.entry())
        .expect_err("linking should reject modules outside the entry dependency closure");

    assert_eq!(error, TypeError::Internal(ElaborationFailure::InvalidState));
}

#[test]
fn linker_rejects_a_surplus_module_that_depends_on_the_selected_entry() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import dependency as Dependency\n\npub value : Unit -> Int\nvalue () = Dependency.main(())\n",
        &[("dependency.ash", "pub main : Unit -> Int\nmain () = 42\n")],
    );
    let checked = check_graph(&graph).expect("the complete graph should check");
    let selected_entry = checked_module(&graph, &checked, "dependency.ash").module();

    let error = link_modules(checked, selected_entry)
        .expect_err("linking should retain only the selected entry's dependency closure");

    assert_eq!(error, TypeError::Internal(ElaborationFailure::InvalidState));
}

#[test]
fn linked_modules_form_dependency_ordered_core_groups_and_evaluate() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        concat!(
            "import middle as Middle\n",
            "pub main : Unit -> Int\n",
            "main () = Middle.pass(())\n",
        ),
        &[
            (
                "middle.ash",
                concat!(
                    "import base as Base\n",
                    "pub pass : Unit -> Int\n",
                    "pass () = Base.answer(())\n",
                ),
            ),
            ("base.ash", "pub answer : Unit -> Int\nanswer () = 42\n"),
        ],
    );
    let checked = check_graph(&graph).expect("the module chain should check");
    let linked = link_modules(checked, graph.entry()).expect("the graph should link");
    let linked = validate_interface_evidence(linked).expect("linked evidence should validate");
    let mut elaborator =
        Elaborator::for_module_program(&linked).expect("the graph namespace should reserve");
    let typed = elaborator
        .synthesize_module_program(&linked)
        .expect("final lowering should preserve checked schemes");
    assert_eq!(typed.ty, Type::Int);
    let unchecked = elaborator
        .finish(typed.node)
        .expect("the one final builder should finish");
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
    let validated = validate_modules(unchecked, &sources, &module_sources)
        .expect("all canonical module sources should validate");

    let mut node = validated.root();
    for _ in 0..3 {
        let expression = validated.node(node).expect("group node should exist");
        assert!(matches!(
            expression.kind,
            PureExprKind::Computation(PureComputation::RecursiveBind(_))
        ));
        node = expression
            .kind
            .child_at(expression.kind.child_count() - 1)
            .expect("a recursive group should end in its body");
    }
    assert!(matches!(
        validated.node(node).map(|expression| &expression.kind),
        Some(PureExprKind::Computation(PureComputation::Apply(_)))
    ));

    let evaluation = evaluate(&validated).expect("linked Core should evaluate");
    assert_eq!(evaluation.value.to_string(), "42");

    let transformed = identity_traversal(&validated)
        .expect("a validated linked graph should preserve every identity");
    let revalidated = validate_modules(transformed, &sources, &module_sources)
        .expect("transformed module identities should validate independently");
    let reevaluation = evaluate(&revalidated).expect("transformed linked Core should evaluate");
    assert_eq!(reevaluation.value.to_string(), "42");
}
