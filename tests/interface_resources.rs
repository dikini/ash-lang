//! Cross-stage resource evidence for interfaces and implementations.

use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    driver::{FileFailure, PipelineFailure, RunConfiguration, run_path},
    elaborate::{TypeError, check_module, link_modules},
    evidence_validation::{EvidenceValidationReason, validate_interface_evidence},
    module::{ModuleGraph, ModuleRoots, load_module_graph},
    resolve::{DependencyExports, resolve_module},
    resolved::CheckedModule,
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct ResourceFixture(PathBuf);

impl ResourceFixture {
    fn create(entry: &str) -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let directory = std::env::temp_dir().join(format!(
                "ash-interface-resource-{}-{id}",
                std::process::id()
            ));
            match fs::create_dir(&directory) {
                Ok(()) => {
                    let entry_path = directory.join("entry.ash");
                    fs::write(&entry_path, entry).expect("entry fixture should be writable");
                    return Self(entry_path);
                }
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("resource fixture should be creatable: {error}"),
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

    fn run(&self) -> Result<ash::driver::Observation, FileFailure> {
        run_path(RunConfiguration {
            entry: self.0.clone(),
            roots: ModuleRoots::empty(),
        })
    }
}

impl Drop for ResourceFixture {
    fn drop(&mut self) {
        if let Some(directory) = self.0.parent() {
            let _ = fs::remove_dir_all(directory);
        }
    }
}

fn public_interfaces(width: usize) -> String {
    let mut source = String::new();
    for index in 0..width {
        source.push_str(&format!(
            "pub interface Marker{index}<A> {{\nmark{index} : A -> A\n}}\n\n"
        ));
    }
    source
}

fn public_interface_implementations(width: usize) -> String {
    let mut source = String::new();
    for index in 0..width {
        source.push_str(&format!(
            "pub interface Marker{index}<A> {{\nmark{index} : A -> A\n}}\n\n\
             pub impl Marker{index}<Int> {{\nmark{index} value = value\n}}\n\n"
        ));
    }
    source
}

fn public_route_reexports(module: &str, width: usize) -> String {
    let mut selected = Vec::with_capacity(width * 3);
    let mut repeated_implementations = Vec::with_capacity(width);
    for index in 0..width {
        selected.push(format!("Marker{index}"));
        selected.push(format!("mark{index}"));
        selected.push(format!("impl Marker{index}"));
        repeated_implementations.push(format!("impl Marker{index}"));
    }
    format!(
        "pub import {module} ({})\npub import {module} ({})\n",
        selected.join(", "),
        repeated_implementations.join(", ")
    )
}

fn deep_public_route_fixture(depth: usize, width: usize) -> ResourceFixture {
    assert!(depth > 0);
    assert!(width > 0);
    let last_layer = format!("layer{}", depth - 1);
    let entry = format!(
        "{}main : Unit -> Int\nmain () = mark0(42)\n",
        public_route_reexports(&last_layer, width)
    );
    let fixture = ResourceFixture::create(&entry);
    fixture.write("base.ash", &public_interface_implementations(width));
    let mut dependency = String::from("base");
    for layer in 0..depth {
        let module = format!("layer{layer}");
        fixture.write(
            &format!("{module}.ash"),
            &public_route_reexports(&dependency, width),
        );
        dependency = module;
    }
    fixture
}

fn check_graph_with_fresh_stage_budgets(graph: &ModuleGraph) -> Vec<CheckedModule> {
    let mut checked = Vec::new();
    for module in graph.modules() {
        let dependencies = module
            .dependencies()
            .iter()
            .map(|edge| {
                let dependency = checked
                    .iter()
                    .find(|checked: &&CheckedModule| checked.module() == edge.target())
                    .expect("dependency order should check dependencies first");
                DependencyExports::new(edge, dependency.exports())
                    .expect("the import edge should authenticate its dependency summary")
            })
            .collect::<Vec<_>>();
        let resolved = resolve_module(module, &dependencies)
            .expect("each module should resolve on a fresh stage budget");
        checked.push(
            check_module(resolved).expect("each module should check on a fresh stage budget"),
        );
    }
    checked
}

#[test]
fn one_constraint_budget_persists_from_dependency_admission_through_validation() {
    const WIDTH: usize = 6_000;
    let fixture = ResourceFixture::create(concat!(
        "import dependency as Dependency\n",
        "main : Unit -> Int\n",
        "main () = 42\n",
    ));
    fixture.write("dependency.ash", &public_interfaces(WIDTH));

    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty())
        .expect("the resource fixture graph should load");
    let linked = link_modules(check_graph_with_fresh_stage_budgets(&graph), graph.entry())
        .expect("linking alone should fit a fresh constraint budget");
    drop(
        validate_interface_evidence(linked)
            .expect("evidence validation alone should fit a fresh constraint budget"),
    );

    let failure = fixture
        .run()
        .expect_err("cumulative imported, linked, and validation work should exhaust one budget");

    assert_eq!(failure.reason_code(), "internal.resource.constraint-work");
    let FileFailure::Pipeline(PipelineFailure::EvidenceValidation(validation)) = &failure else {
        panic!("the shared prefix should fit until interface-evidence validation: {failure:?}");
    };
    assert_eq!(
        validation.reason(),
        EvidenceValidationReason::ConstraintResourceExhausted,
    );
}

#[test]
fn cycle_precedes_constraint_resource_exhaustion_after_import_admission() {
    const WIDTH: usize = 6_000;
    let fixture = ResourceFixture::create(concat!(
        "import dependency as Dependency\n\n",
        "interface First<A> {\nfirst : A -> A\n}\n\n",
        "interface Second<A> {\nsecond : A -> A\n}\n\n",
        "impl First<Int> where Second<Int> {\nfirst value = value\n}\n\n",
        "impl Second<Int> where First<Int> {\nsecond value = value\n}\n\n",
        "main : Unit -> Int\n",
        "main () = first 1\n",
    ));
    fixture.write("dependency.ash", &public_interfaces(WIDTH));

    let failure = fixture
        .run()
        .expect_err("the active prerequisite must be recognized as a cycle");

    assert_eq!(failure.reason_code(), "constraint.cycle");
    let FileFailure::Pipeline(PipelineFailure::Typing(TypeError::Interface(_))) = failure else {
        panic!("the cycle should remain owned by interface checking");
    };
}

#[test]
fn public_run_admits_and_drops_deep_public_routes_on_a_small_stack() {
    const DEPTH: usize = 48;
    const WIDTH: usize = 4;
    const STACK_SIZE: usize = 256 * 1024;

    std::thread::Builder::new()
        .name(String::from("public-deep-route"))
        .stack_size(STACK_SIZE)
        .spawn(|| {
            let fixture = deep_public_route_fixture(DEPTH, WIDTH);
            let observation = fixture
                .run()
                .expect("the public runner should admit the deep public route fixture");
            assert_eq!(observation.value_display(), "42");
            drop(observation);
        })
        .expect("the public small-stack witness thread should spawn")
        .join()
        .expect("the public runner should admit and dispose deep routes on a small stack");
}
