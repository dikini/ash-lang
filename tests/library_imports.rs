//! Resolution and checking evidence for independent library import channels.

use std::{
    fs,
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    elaborate::{TypeError, check_module},
    interface::InterfaceReason,
    module::{LoadedModule, ModuleGraph, ModuleRoots, load_module_graph},
    resolve::{DependencyExports, ResolveReason, resolve_module},
    resolved::{ResolvedDefinitionKind, ResolvedExprKind, ResolvedTermName},
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct ModuleTree(PathBuf);

impl ModuleTree {
    fn create() -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir()
                .join(format!("ash-library-imports-{}-{id}", std::process::id()));
            match fs::create_dir(&path) {
                Ok(()) => return Self(path),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("library import fixture should be creatable: {error}"),
            }
        }
    }

    fn write(&self, relative: &str, source: &str) -> PathBuf {
        let path = self.0.join(relative);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).expect("fixture parent should be creatable");
        }
        fs::write(&path, source).expect("fixture source should be writable");
        path
    }
}

impl Drop for ModuleTree {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn load(tree: &ModuleTree, entry: &str, dependencies: &[(&str, &str)]) -> ModuleGraph {
    let entry = tree.write("entry.ash", entry);
    for (path, source) in dependencies {
        tree.write(path, source);
    }
    load_module_graph(&entry, &ModuleRoots::empty()).expect("fixture graph should load")
}

fn module_named<'a>(graph: &'a ModuleGraph, file_name: &str) -> &'a LoadedModule {
    graph
        .modules()
        .iter()
        .find(|module| {
            Path::new(module.source().display_path()).file_name() == Some(file_name.as_ref())
        })
        .expect("fixture module should be present")
}

fn resolve_entry_error(graph: &ModuleGraph) -> ash::resolve::ResolveError {
    let entry = module_named(graph, "entry.ash");
    let mut checked = Vec::new();
    for module in graph.modules() {
        let dependencies = module
            .dependencies()
            .iter()
            .map(|edge| {
                let dependency = checked
                    .iter()
                    .find(|dependency: &&ash::resolved::CheckedModule| {
                        dependency.module() == edge.target()
                    })
                    .expect("dependencies should check before their importer");
                DependencyExports::new(edge, dependency.exports())
                    .expect("the dependency summary should authenticate its edge")
            })
            .collect::<Vec<_>>();
        let resolved = resolve_module(module, &dependencies);
        if module.id() == entry.id() {
            return resolved.expect_err("the entry fixture should fail resolution");
        }
        checked.push(
            check_module(resolved.expect("a dependency fixture should resolve"))
                .expect("a dependency fixture should check"),
        );
    }
    panic!("the graph should contain its entry module");
}

#[test]
fn name_only_import_does_not_select_implementation() {
    let tree = ModuleTree::create();
    let graph = load(
        &tree,
        concat!(
            "import equality (Equal, equal)\n\n",
            "main : Unit -> Bool\n",
            "main () = equal(1, 1)\n",
        ),
        &[(
            "equality.ash",
            concat!(
                "pub interface Equal<A> {\n",
                "equal : (A, A) -> Bool\n",
                "}\n\n",
                "pub impl Equal<Int> {\n",
                "equal (left, right) = left == right\n",
                "}\n",
            ),
        )],
    );
    let equality = module_named(&graph, "equality.ash");
    let equality_checked = check_module(
        resolve_module(equality, &[]).expect("the equality dependency should resolve"),
    )
    .expect("the equality dependency should check");
    let [interface] = equality_checked.interface_facts() else {
        panic!("the dependency should publish one interface fact");
    };
    let [implementation] = equality_checked.implementation_facts() else {
        panic!("the dependency should publish one implementation fact");
    };
    let entry = module_named(&graph, "entry.ash");
    let [edge] = entry.dependencies() else {
        panic!("the entry should have one direct dependency");
    };
    let dependency = DependencyExports::new(edge, equality_checked.exports())
        .expect("the entry edge should authenticate the dependency summary");
    let resolved =
        resolve_module(entry, &[dependency]).expect("the name-only import should resolve");
    let retained_interface = resolved.imported_facts().interface(interface.id).is_some();
    let retained_implementation = resolved
        .imported_facts()
        .implementation(implementation.id)
        .is_some();

    let error = check_module(resolved)
        .expect_err("a name-only import should not satisfy the method obligation");
    let TypeError::Interface(diagnostic) = error else {
        panic!("the method occurrence should retain an interface diagnostic");
    };
    let occurrence_start = entry
        .source()
        .text()
        .rfind("equal")
        .expect("the entry should contain the method occurrence");

    assert_eq!(diagnostic.reason, InterfaceReason::Unsatisfied);
    assert_eq!(diagnostic.reason.to_string(), "constraint.unsatisfied");
    assert_eq!(diagnostic.primary.span().source(), entry.source().id());
    assert_eq!(
        diagnostic.primary.span().range().start(),
        u32::try_from(occurrence_start).expect("the fixture offset should fit")
    );
    assert_eq!(diagnostic.primary.span().range().end(), {
        u32::try_from(occurrence_start + "equal".len()).expect("the fixture offset should fit")
    });
    assert!(retained_interface);
    assert!(!retained_implementation);
}

#[test]
fn implementation_only_import_selects_evidence_without_binding_names() {
    let tree = ModuleTree::create();
    let graph = load(
        &tree,
        concat!(
            "import equality as Equality\n",
            "import equality (impl Equal)\n\n",
            "type Equal = LocalEqual\n\n",
            "equal : Bool -> Bool\n",
            "equal value = value\n\n",
            "main : Unit -> Bool\n",
            "main () = Equality.equal(1, 1)\n",
        ),
        &[(
            "equality.ash",
            concat!(
                "pub interface Equal<A> {\n",
                "equal : (A, A) -> Bool\n",
                "}\n\n",
                "pub impl Equal<Int> {\n",
                "equal (left, right) = left == right\n",
                "}\n",
            ),
        )],
    );
    let equality = module_named(&graph, "equality.ash");
    let equality_checked = check_module(
        resolve_module(equality, &[]).expect("the equality dependency should resolve"),
    )
    .expect("the equality dependency should check");
    let [defining_interface] = equality_checked.interface_facts() else {
        panic!("the dependency should publish one interface fact");
    };
    let [defining_implementation] = equality_checked.implementation_facts() else {
        panic!("the dependency should publish one implementation fact");
    };
    let expected_method = defining_interface.methods[0].id;
    let expected_implementation = defining_implementation.id;
    let expected_implementation_method = defining_implementation.methods[0].id;
    let entry = module_named(&graph, "entry.ash");
    let dependencies = entry
        .dependencies()
        .iter()
        .map(|edge| {
            DependencyExports::new(edge, equality_checked.exports())
                .expect("the entry edges should authenticate the dependency summary")
        })
        .collect::<Vec<_>>();
    let resolved = resolve_module(entry, &dependencies)
        .expect("the implementation selector should bind no unqualified names");
    let imported = resolved
        .imported_facts()
        .implementation(expected_implementation)
        .expect("the implementation selector should retain its matching public fact");
    let ResolvedDefinitionKind::Equational(main) = &resolved.definitions()[1].kind else {
        panic!("the entry should retain its main equation");
    };
    let ResolvedExprKind::Apply(application) = &main.equations[0].body.kind else {
        panic!("main should apply the qualified method");
    };
    let ResolvedExprKind::Occurrence(occurrence) = &application.function.kind else {
        panic!("main should retain the qualified method occurrence");
    };
    let resolved_method = occurrence.term;
    let imported_implementation = imported.id;
    let imported_method = imported.methods[0].id;

    let checked = check_module(resolved)
        .expect("the selected implementation should satisfy the qualified method call");

    assert_eq!(resolved_method, ResolvedTermName::Method(expected_method));
    assert_eq!(imported_implementation, expected_implementation);
    assert_eq!(imported_method, expected_implementation_method);
    assert_eq!(checked.available_implementations().len(), 1);
    assert_eq!(
        checked.available_implementations()[0].id(),
        expected_implementation
    );
}

#[test]
fn implementation_selector_rejects_an_unavailable_interface() {
    for (selected, dependency) in [
        (
            "Missing",
            "pub interface Equal<A> {\nequal : (A, A) -> Bool\n}\n",
        ),
        (
            "Private",
            "interface Private<A> {\nprivate : (A, A) -> Bool\n}\n",
        ),
    ] {
        let tree = ModuleTree::create();
        let graph = load(
            &tree,
            &format!("import dependency (impl {selected})\n"),
            &[("dependency.ash", dependency)],
        );

        let error = resolve_entry_error(&graph);

        assert_eq!(error.reason, ResolveReason::UnavailableExport, "{selected}");
        assert_eq!(
            error.diagnostic().primary.span().source(),
            module_named(&graph, "entry.ash").source().id(),
            "{selected}"
        );
    }
}

#[test]
fn implementation_selector_rejects_a_public_nominal() {
    let tree = ModuleTree::create();
    let graph = load(
        &tree,
        "import dependency (impl Nominal)\n",
        &[("dependency.ash", "pub type Nominal = Nominal\n")],
    );

    let error = resolve_entry_error(&graph);

    assert_eq!(error.reason, ResolveReason::InterfaceKind);
    assert_eq!(error.reason.to_string(), "resolve.interface-kind");
}
