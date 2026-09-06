use ash::{
    driver::{RunConfiguration, run_path},
    module::ModuleRoots,
    source::SourceFile,
};

// The production entry point independently validates resource ownership before
// evaluating the acquired body, including unused resource-dependent closures.
#[test]
fn resource_programs_execute_after_independent_ownership_validation() {
    let path = std::env::temp_dir().join(format!(
        "ash-resource-admission-{}-{}.ash",
        std::process::id(),
        SourceFile::new("identity", "").unwrap().id().value(),
    ));
    for (body, expected) in [
        ("42", "42"),
        ("Cell.read c", "41"),
        ("let delayed = fn(ignored) {\nCell.read c\n}\n42", "42"),
    ] {
        std::fs::write(&path, format!(
            "import @builtin.cell as Cell\nmain : Unit -> Int\nmain () = resource cell<R> c = 41 {{\n{body}\n}}\n"
        )).unwrap();
        let observation = run_path(RunConfiguration {
            entry: path.clone(),
            roots: ModuleRoots::empty(),
        })
        .unwrap();
        assert_eq!(observation.value().to_string(), expected, "{body}");
    }
    std::fs::remove_file(path).unwrap();
}
