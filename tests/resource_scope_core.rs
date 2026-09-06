use ash::{
    driver::{RunConfiguration, run_path},
    module::ModuleRoots,
    source::SourceFile,
};

// Structural Core positives and corruption tests live with the private Core
// validator. The production entry point must not expose their lifetime-unproved
// fixture as an executable program.
#[test]
fn resource_programs_cannot_reach_execution_before_dependency_proof() {
    let path = std::env::temp_dir().join(format!(
        "ash-resource-admission-{}-{}.ash",
        std::process::id(),
        SourceFile::new("identity", "").unwrap().id().value(),
    ));
    for body in [
        "42",
        "Cell.read c",
        "let delayed = fn(ignored) {\nCell.read c\n}\n42",
    ] {
        std::fs::write(&path, format!(
            "import @builtin.cell as Cell\nmain : Unit -> Int\nmain () = resource cell<R> c = 41 {{\n{body}\n}}\n"
        )).unwrap();
        let failure = run_path(RunConfiguration {
            entry: path.clone(),
            roots: ModuleRoots::empty(),
        })
        .unwrap_err();
        assert_eq!(
            failure.reason_code(),
            "resource.proof-unavailable",
            "{body}: {failure:?}"
        );
    }
    std::fs::remove_file(path).unwrap();
}
