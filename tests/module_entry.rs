use std::{
    fs,
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    driver::{EntryReason, FileFailure, PipelineFailure, RunConfiguration, run_path},
    module::ModuleRoots,
    types::Type,
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct TempTree(PathBuf);

impl TempTree {
    fn create() -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let path =
                std::env::temp_dir().join(format!("ash-module-driver-{}-{id}", std::process::id()));
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

fn run(entry: &Path) -> Result<ash::driver::Observation, ash::driver::FileFailure> {
    run_path(RunConfiguration {
        entry: entry.to_path_buf(),
        roots: ModuleRoots::empty(),
    })
}

#[test]
fn evaluates_entry_main_across_the_loaded_module_graph() {
    let tree = TempTree::create();
    let entry = tree.write(
        "entry.ash",
        concat!(
            "import dependency as Dependency\n",
            "main : Unit -> Int\n",
            "main () = Dependency.answer(()) + 1\n",
        ),
    );
    tree.write(
        "dependency.ash",
        "pub answer : Unit -> Int\nanswer () = 41\n",
    );

    let observation = run(&entry).expect("the modular program should run");

    assert_eq!(observation.value_display(), "42");
    assert_eq!(observation.ty(), &Type::Int);
    assert_eq!(observation.type_display(), "Int");
}

#[test]
fn accepts_a_private_main_declared_in_the_entry_module() {
    let tree = TempTree::create();
    let entry = tree.write("entry.ash", "main : Unit -> Bool\nmain () = true\n");

    let observation = run(&entry).expect("entry main need not be public");

    assert_eq!(observation.value_display(), "true");
    assert_eq!(observation.ty(), &Type::Bool);
}

#[test]
fn rejects_effect_syntax_before_final_pure_core_and_evaluation() {
    let tree = TempTree::create();
    let entry = tree.write(
        "entry.ash",
        concat!(
            "effect Tick {\nping : Unit -> Unit\n}\n\n",
            "main : Unit -> Unit\n",
            "main () = handle (perform Tick.ping ()) with Tick {\n",
            "ping ignored => resume ()\n",
            "}\n",
        ),
    );

    let failure = run(&entry).expect_err("effect syntax cannot enter retained pure Core");
    assert_eq!(failure.reason_code(), "effect.core-unavailable");
    assert!(!failure.is_source_rejection());
}

#[test]
fn rejects_an_entry_module_without_a_local_main() {
    let tree = TempTree::create();
    let entry = tree.write("entry.ash", "helper : Unit -> Unit\nhelper value = value\n");

    let failure = run(&entry).expect_err("the entry contract requires local main");

    assert_eq!(failure.reason_code(), "entry.missing-main");
    assert!(failure.is_source_rejection());
}

#[test]
fn rejects_an_imported_main_even_when_it_is_public() {
    let tree = TempTree::create();
    let entry = tree.write("entry.ash", "import dependency (main)\n");
    tree.write("dependency.ash", "pub main : Unit -> Int\nmain () = 42\n");

    let failure = run(&entry).expect_err("an imported main is not entry-local");

    assert_eq!(failure.reason_code(), "entry.missing-main");
    assert!(failure.is_source_rejection());
}

#[test]
fn rejects_a_main_whose_domain_is_not_unit() {
    let tree = TempTree::create();
    let entry = tree.write("entry.ash", "main : Int -> Int\nmain value = value\n");

    let failure = run(&entry).expect_err("main must accept Unit");

    assert_eq!(failure.reason_code(), "entry.main-domain");
    assert!(failure.is_source_rejection());
}

#[test]
fn rejects_a_nonempty_entry_effect_row_before_core_lowering() {
    let tree = TempTree::create();
    let entry = tree.write(
        "entry.ash",
        concat!(
            "effect Choice {\nchoose : Unit -> Int\n}\n",
            "main : Unit -> Int ! {Choice}\n",
            "main () = perform Choice.choose ()\n",
        ),
    );

    let failure = run(&entry).expect_err("the linked entry row must be empty");

    assert_eq!(failure.reason_code(), "entry.main-effects");
    assert!(failure.is_source_rejection());
}

#[test]
fn rejects_a_polymorphic_main_before_inspecting_its_domain() {
    let tree = TempTree::create();
    let entry = tree.write("entry.ash", "main : A -> A\nmain value = value\n");

    let failure = run(&entry).expect_err("main must have a monomorphic scheme");

    assert_eq!(failure.reason_code(), "entry.main-polymorphic");
    assert!(failure.is_source_rejection());
}

#[test]
fn rejects_a_constrained_main_before_lowering_entry_evidence() {
    let tree = TempTree::create();
    let entry = tree.write(
        "entry.ash",
        concat!(
            "interface Marker<A> {\n",
            "marker : A -> Bool\n",
            "}\n",
            "main : Unit -> Int where Marker<Int>\n",
            "main () = 42\n",
        ),
    );

    let failure = run(&entry).expect_err("main must not require interface evidence");

    assert_eq!(failure.reason_code(), "entry.main-constrained");
    assert!(failure.is_source_rejection());
}

#[test]
fn existing_entry_shape_failures_precede_main_constrained() {
    let cases = [
        (
            concat!(
                "interface Marker<A> {\nmarker : A -> Bool\n}\n",
                "main : A -> A where Marker<A>\n",
                "main value = value\n",
            ),
            EntryReason::MainPolymorphic,
        ),
        (
            concat!(
                "interface Marker<A> {\nmarker : A -> Bool\n}\n",
                "main : Int -> Int where Marker<Int>\n",
                "main value = value\n",
            ),
            EntryReason::MainDomain,
        ),
    ];

    for (source, expected) in cases {
        let tree = TempTree::create();
        let entry = tree.write("entry.ash", source);
        let failure = run(&entry).expect_err("the earlier entry-shape judgment should reject main");
        let FileFailure::Pipeline(PipelineFailure::Entry(failure)) = failure else {
            panic!("entry precedence should retain an entry-contract failure");
        };

        assert_eq!(failure.reason(), expected);
    }
}

#[test]
fn retains_source_caused_module_loading_failures() {
    let tree = TempTree::create();
    let entry = tree.write(
        "entry.ash",
        concat!(
            "import absent as Absent\n",
            "main : Unit -> Unit\n",
            "main value = value\n",
        ),
    );

    let failure = run(&entry).expect_err("the imported module does not exist");

    assert_eq!(failure.reason_code(), "module.not-found");
    assert!(failure.is_source_rejection());
}
