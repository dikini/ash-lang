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

#[test]
fn generic_cell_dependency_admission_does_not_grant_execution_permission() {
    let path = std::env::temp_dir().join(format!(
        "ash-generic-cell-admission-{}.ash",
        SourceFile::new("identity", "").unwrap().id().value()
    ));
    std::fs::write(&path, "import @builtin.generic_cell as Cell\nmain : Unit -> Int\nmain () = resource Cell.Cell<R, Int> c = 41 {\nlet _ = Cell.write (c, 42)\nCell.read c\n}\n").unwrap();
    let compiled = ash::driver::compile_path(RunConfiguration {
        entry: path.clone(),
        roots: ModuleRoots::empty(),
    })
    .expect("source and independent Core dependency proof should succeed");
    let output = path.with_extension("executable");
    let failure = ash::build::prepare_program(
        &compiled,
        ash::build::BuildConfiguration::new(output.clone()),
    )
    .unwrap_err();
    assert_eq!(failure.reason_code(), "build.unsupported-program");
    assert!(
        !output.exists(),
        "dependency admission cannot publish a generic executable"
    );
    assert_eq!(
        ash::driver::execute(&compiled).unwrap_err().reason_code(),
        "runtime.invalid-control-state"
    );
    let failure = run_path(RunConfiguration {
        entry: path.clone(),
        roots: ModuleRoots::empty(),
    })
    .unwrap_err();
    assert_eq!(failure.reason_code(), "runtime.invalid-control-state");
    std::fs::remove_file(path).unwrap();
}
