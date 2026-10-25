use ash::{
    driver::{RunConfiguration, run_path},
    module::ModuleRoots,
};
use std::{
    fs,
    sync::atomic::{AtomicU64, Ordering},
};

static NEXT_SOURCE: AtomicU64 = AtomicU64::new(0);

fn run_result(source: &str) -> Result<ash::driver::Observation, ash::driver::FileFailure> {
    let path = std::env::temp_dir().join(format!(
        "ash-region-runtime-{}-{}.ash",
        std::process::id(),
        NEXT_SOURCE.fetch_add(1, Ordering::Relaxed)
    ));
    fs::write(&path, source).unwrap();
    let result = run_path(RunConfiguration {
        entry: path.clone(),
        roots: ModuleRoots::empty(),
    });
    fs::remove_file(path).unwrap();
    result
}

fn run(source: &str) -> String {
    run_result(source)
        .unwrap_or_else(|failure| panic!("{failure:?}"))
        .value_display()
        .to_owned()
}

#[test]
fn declared_host_region_constructs_and_consumes_a_tuple_before_close() {
    assert_eq!(
        run(
            "main : Unit -> Int\nmain () = region<R> r {\nlet pair = (20, 22)\nmatch pair {\n(left, right) => left + right\n}\n}\n"
        ),
        "42"
    );
}

#[test]
fn explicit_selection_constructs_under_an_enclosing_live_region() {
    assert_eq!(
        run(
            "main : Unit -> Int\nmain () = region<R> outer {\nregion<S> inner {\nusing outer {\nlet pair = (20, 22)\nmatch pair {\n(left, right) => left + right\n}\n}\n}\n}\n"
        ),
        "42"
    );
}

#[test]
fn ordinary_construction_without_selection_uses_generated_root() {
    assert_eq!(
        run("main : Unit -> Int\nmain () = match (20, 22) {\n(left, right) => left + right\n}\n"),
        "42"
    );
}

#[test]
fn generated_root_does_not_hide_unrelated_outstanding_effects() {
    let failure = run_result("effect Console {\nwrite : Unit -> Unit\n}\nmain : Unit -> Unit ! {Console}\nmain () = perform Console.write ()\n").unwrap_err();
    let ash::driver::FileFailure::Pipeline(diagnostic) = failure else {
        panic!("expected source rejection");
    };
    assert!(format!("{diagnostic:?}").contains("MainEffects"));
}

#[test]
fn binding_facade_imports_share_the_generated_service_identity() {
    assert_eq!(
        run(concat!(
            "import @builtin.regions as Region\n",
            "import @builtin.foreign as Foreign\n",
            "inspect : Region.Request -> Int\ninspect request = Region.usable_bytes request\n",
            "adapt<R> : (Region.Request, Foreign.Address, Int, Int) -> Region.Storage<R>\nadapt value = Region.from_backing value\n",
            "main : Unit -> Int\nmain () = 42\n",
        )),
        "42"
    );
}

#[test]
fn binding_facade_does_not_export_the_generated_default_effect() {
    let failure = run_result("import @builtin.regions as Region\nmain : Unit -> Unit ! {Region.DefaultAlloc}\nmain () = ()\n").unwrap_err();
    assert!(format!("{failure:?}").contains("Resolve"), "{failure:?}");
}

#[test]
fn binding_facade_does_not_export_private_view_types() {
    for hidden in ["RegionView", "StorageView"] {
        let source = format!(
            "import @builtin.regions as Region\nprobe : Region.{hidden} -> Unit\nprobe value = ()\nmain : Unit -> Unit\nmain () = ()\n"
        );
        let failure = run_result(&source).unwrap_err();
        assert!(format!("{failure:?}").contains("Resolve"), "{failure:?}");
    }
}

#[test]
fn generated_service_has_no_user_import_spelling() {
    let failure = run_result(
        "import @builtin.region_service as Service\nmain : Unit -> Unit\nmain () = ()\n",
    )
    .unwrap_err();
    assert!(
        format!("{failure:?}").contains("UnknownBuiltin"),
        "{failure:?}"
    );
}

#[test]
fn region_access_cannot_be_used_after_its_owner_closes() {
    assert!(run_result("main : Unit -> Int\nmain () = {\nlet leaked = region<R> r { r }\nusing leaked { 42 }\n}\n").is_err());
}

#[test]
fn outer_selected_tuple_remains_readable_after_inner_close() {
    assert_eq!(
        run(concat!(
            "main : Unit -> Int\nmain () = region<R> outer {\n",
            "let kept = region<S> inner {\nlet local = (1, 2)\n",
            "let total = match local {\n(a, b) => a + b\n}\n",
            "using outer {\n(20, 22)\n}\n}\n",
            "match kept {\n(a, b) => a + b\n}\n}\n",
        )),
        "42"
    );
}

#[test]
fn generated_root_backing_survives_tuple_observation() {
    assert_eq!(
        run("main : Unit -> (Int, Int)\nmain () = (20, 22)\n"),
        "(20, 22)"
    );
}

#[test]
fn a_whole_tuple_cannot_escape_its_declared_region() {
    let failure = run_result("main : Unit -> (Int, Int)\nmain () = region<R> r {\n(20, 22)\n}\n")
        .unwrap_err();
    let ash::driver::FileFailure::Pipeline(diagnostic) = failure else {
        panic!("expected the source lifetime diagnostic");
    };
    let ash::driver::PipelineFailure::Typing(ash::elaborate::TypeError::Source(error)) =
        diagnostic.failure()
    else {
        panic!("expected source resource escape, got {diagnostic:?}");
    };
    assert_eq!(error.reason, ash::elaborate::TypeReason::ResourceEscape);
}
