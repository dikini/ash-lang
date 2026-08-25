//! Integration evidence for the pre-Core interface-validation capability.

use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    elaborate::{check_module, link_modules},
    evidence_validation::validate_interface_evidence,
    module::{ModuleGraph, ModuleRoots, load_module_graph},
    resolve::{DependencyExports, resolve_module},
    resolved::CheckedModule,
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct ValidationFixture(PathBuf);

impl ValidationFixture {
    fn create(entry: &str) -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let directory = std::env::temp_dir().join(format!(
                "ash-interface-validation-{}-{id}",
                std::process::id()
            ));
            match fs::create_dir(&directory) {
                Ok(()) => {
                    let entry_path = directory.join("entry.ash");
                    fs::write(&entry_path, entry).expect("entry fixture should be writable");
                    return Self(entry_path);
                }
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("validation fixture should be creatable: {error}"),
            }
        }
    }

    fn write(&self, relative: &str, text: &str) {
        let path = self
            .0
            .parent()
            .expect("fixture entry should have a parent")
            .join(relative);
        fs::write(path, text).expect("dependency fixture should be writable");
    }
}

impl Drop for ValidationFixture {
    fn drop(&mut self) {
        if let Some(directory) = self.0.parent() {
            let _ = fs::remove_dir_all(directory);
        }
    }
}

fn check_graph(graph: &ModuleGraph) -> Vec<CheckedModule> {
    let mut checked = Vec::new();
    for module in graph.modules() {
        let dependencies = module
            .dependencies()
            .iter()
            .map(|edge| {
                let dependency = checked
                    .iter()
                    .find(|module: &&CheckedModule| module.module() == edge.target())
                    .expect("dependency order should check dependencies first");
                DependencyExports::new(edge, dependency.exports())
                    .expect("the dependency edge should authenticate its export summary")
            })
            .collect::<Vec<_>>();
        let resolved = resolve_module(module, &dependencies)
            .expect("the interface-validation fixture should resolve");
        checked.push(check_module(resolved).expect("the fixture module should check"));
    }
    checked
}

#[test]
fn validates_cross_module_concrete_selection_before_core() {
    let fixture = ValidationFixture::create(concat!(
        "import dependency as Dependency\n",
        "import dependency (impl Equal)\n",
        "main : Unit -> Bool\n",
        "main () = Dependency.equal((42, 42))\n",
    ));
    fixture.write(
        "dependency.ash",
        concat!(
            "pub interface Equal<A> {\nequal : (A, A) -> Bool\n}\n\n",
            "pub impl Equal<Int> {\nequal (left, right) = left == right\n}\n",
        ),
    );
    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty())
        .expect("the validation fixture graph should load");
    let linked =
        link_modules(check_graph(&graph), graph.entry()).expect("the checked graph should link");

    let validated = validate_interface_evidence(linked)
        .expect("the checked concrete evidence should authenticate before Core");

    assert_eq!(validated.entry(), graph.entry());
    assert_eq!(validated.groups().len(), graph.modules().len());
}

#[test]
fn linked_groups_retain_only_public_implementation_authorization_routes() {
    let fixture = ValidationFixture::create(concat!(
        "pub import facade (Equal, equal, impl Equal)\n",
        "main : Unit -> Bool\n",
        "main () = equal((42, 42))\n",
    ));
    fixture.write(
        "base.ash",
        concat!(
            "pub interface Equal<A> {\nequal : (A, A) -> Bool\n}\n\n",
            "pub impl Equal<Int> {\nequal (left, right) = left == right\n}\n",
        ),
    );
    fixture.write("facade.ash", "pub import base (Equal, equal, impl Equal)\n");
    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty())
        .expect("the transitive validation graph should load");
    let linked =
        link_modules(check_graph(&graph), graph.entry()).expect("the checked graph should link");
    let [base, facade, entry] = linked.groups() else {
        panic!("the linked graph should retain three dependency-ordered groups");
    };

    assert_eq!(base.implementations().len(), 1);
    assert_eq!(base.checked_implementations().len(), 1);
    assert_eq!(base.implementation_facts().len(), 1);
    assert_eq!(base.implementation_facts()[0].methods.len(), 1);
    assert_eq!(facade.implementations().len(), 0);
    assert_eq!(facade.checked_implementations().len(), 0);
    assert_eq!(facade.implementation_facts().len(), 0);
    assert_eq!(entry.implementations().len(), 0);
    assert_eq!(entry.checked_implementations().len(), 0);
    assert_eq!(entry.implementation_facts().len(), 0);

    let implementation = base.implementation_facts()[0].id;
    for (group, expected_hops) in [(base, 0), (facade, 1), (entry, 2)] {
        let [published] = group.public_implementation_authorizations() else {
            panic!("each publisher should retain one lightweight public authorization");
        };
        assert_eq!(published.id(), implementation);
        assert_eq!(published.authorization().hops().len(), expected_hops);
    }
}
