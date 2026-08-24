use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    elaborate::{TypeError, TypeReason, check_module},
    module::{ModuleGraph, ModuleRoots, load_module_graph},
    resolve::{DependencyExports, resolve_module},
    resolved::CheckedModule,
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct TempTree(PathBuf);

impl TempTree {
    fn create() -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "ash-module-elaboration-nominals-{}-{id}",
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

fn load(entry: &str, dependencies: &[(&str, &str)]) -> (TempTree, ModuleGraph) {
    let tree = TempTree::create();
    let entry = tree.write("entry.ash", entry);
    for (path, text) in dependencies {
        tree.write(path, text);
    }
    let graph =
        load_module_graph(&entry, &ModuleRoots::empty()).expect("fixture module graph should load");
    (tree, graph)
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

#[test]
fn imported_transparent_parameterized_constructor_checks_at_its_type_argument() {
    let (_tree, graph) = load(
        concat!(
            "import dependency as Dep\n",
            "round_trip : Dep.Boxed<A> -> Dep.Boxed<A>\n",
            "round_trip Dep.Boxed(value) = Dep.Boxed(value)\n",
        ),
        &[("dependency.ash", "pub type Boxed<A> = Boxed(A)\n")],
    );

    check_graph(&graph).expect("the imported constructor should retain its type parameter");
}

#[test]
fn targeted_constructor_import_retains_unselected_siblings_for_coverage() {
    let (_tree, graph) = load(
        concat!(
            "import dependency (Choice, First)\n",
            "first : Choice<Int> -> Int\n",
            "first value = match value {\n",
            "First(payload) => payload\n",
            "}\n",
        ),
        &[(
            "dependency.ash",
            concat!("pub type Choice<A> =\n", "First(A)\n", "| Second(A)\n",),
        )],
    );

    let error = check_graph(&graph)
        .expect_err("the unselected Second constructor should remain a missing case");

    assert!(
        matches!(
            &error,
            TypeError::Source(diagnostic) if diagnostic.reason == TypeReason::NonExhaustive
        ),
        "expected a non-exhaustive match, found {error:?}"
    );
}

#[test]
fn imported_opaque_nominal_is_not_an_empty_constructor_family() {
    let (_tree, graph) = load(
        concat!(
            "import dependency as Dep\n",
            "inspect : Unit -> Int\n",
            "inspect () = match Dep.make(()) {\n",
            "_ => 0\n",
            "}\n",
        ),
        &[(
            "dependency.ash",
            concat!(
                "pub opaque type Token = Token(Int)\n",
                "pub make : Unit -> Token\n",
                "make () = Token(0)\n",
            ),
        )],
    );

    check_graph(&graph).expect("a wildcard should cover an imported opaque value");
}

#[test]
fn imported_hidden_nominal_is_not_an_empty_constructor_family() {
    let (_tree, graph) = load(
        concat!(
            "import dependency as Dep\n",
            "inspect : Unit -> Int\n",
            "inspect () = {\n",
            "let hidden = Dep.make(())\n",
            "match hidden {\n",
            "_ => Dep.observe(hidden)\n",
            "}\n",
            "}\n",
        ),
        &[(
            "dependency.ash",
            concat!(
                "type Hidden = Hidden(Int)\n",
                "pub make : Unit -> Hidden\n",
                "make () = Hidden(0)\n",
                "pub observe : Hidden -> Int\n",
                "observe Hidden(value) = value\n",
            ),
        )],
    );

    check_graph(&graph).expect("a wildcard should cover an imported hidden value");
}

#[test]
fn hidden_identity_mismatch_uses_private_names_and_export_provenance() {
    let (_tree, graph) = load(
        concat!(
            "import producer as Producer\n",
            "import consumer as Consumer\n",
            "bad : Unit -> Int\n",
            "bad () = Consumer.observe(Producer.make(()))\n",
        ),
        &[
            (
                "producer.ash",
                concat!(
                    "type Produced = Produced(Int)\n",
                    "pub make : Unit -> Produced\n",
                    "make () = Produced(0)\n",
                ),
            ),
            (
                "consumer.ash",
                concat!(
                    "type Consumed = Consumed(Int)\n",
                    "pub observe : Consumed -> Int\n",
                    "observe Consumed(value) = value\n",
                ),
            ),
        ],
    );

    let error = check_graph(&graph).expect_err("distinct hidden identities must not unify");
    let TypeError::Source(diagnostic) = error else {
        panic!("the mismatch should retain a source diagnostic");
    };
    assert!(
        diagnostic
            .expected
            .as_deref()
            .is_some_and(|display| display.contains("<private Consumed>"))
    );
    assert!(
        diagnostic
            .found
            .as_deref()
            .is_some_and(|display| display.contains("<private Produced>"))
    );
    assert!(
        diagnostic
            .related
            .iter()
            .any(|label| label.span().source() != diagnostic.primary.span().source()),
        "the imported declaration should remain a separate cross-source label"
    );
}

#[test]
fn imported_constructor_argument_mismatch_keeps_declaration_provenance() {
    let (_tree, graph) = load(
        concat!(
            "import dependency as Dep\n",
            "bad : Unit -> Dep.Boxed\n",
            "bad () = Dep.Boxed(false)\n",
        ),
        &[("dependency.ash", "pub type Boxed = Boxed(Int)\n")],
    );

    let error = check_graph(&graph).expect_err("the constructor payload should require Int");
    let TypeError::Source(diagnostic) = error else {
        panic!("the mismatch should retain a source diagnostic");
    };
    assert!(
        diagnostic
            .related
            .iter()
            .any(|label| label.span().source() != diagnostic.primary.span().source()),
        "the constructor declaration should remain a separate cross-source label"
    );
}
