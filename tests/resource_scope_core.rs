use ash::{
    driver::{RunConfiguration, run_path},
    module::ModuleRoots,
    source::SourceFile,
};

// Source dependency proof permits publication, but the production entry point
// must still reject execution until resource acquisition and release exist.
#[test]
fn resource_programs_cannot_reach_execution_before_resource_runtime() {
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
            "core.validation.resource-proof-unavailable",
            "{body}: {failure:?}"
        );
    }
    std::fs::remove_file(path).unwrap();
}
