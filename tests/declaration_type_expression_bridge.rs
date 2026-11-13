use std::path::PathBuf;

use ash::{
    driver::{RunConfiguration, compile_path, execute},
    module::ModuleRoots,
};

fn run(path: &str) {
    let configuration = RunConfiguration {
        entry: PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(path),
        roots: ModuleRoots::empty(),
    };
    let program =
        compile_path(configuration).unwrap_or_else(|failure| panic!("{path}: {failure:?}"));
    let value = execute(&program).expect("the generated function executes");
    assert_eq!(value.value_display(), "42");
    assert_eq!(value.type_display(), "Int");
}

fn reject(path: &str) {
    let configuration = RunConfiguration {
        entry: PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(path),
        roots: ModuleRoots::empty(),
    };
    let failure = compile_path(configuration).expect_err("the protected bridge stays guarded");
    assert_eq!(
        failure.reason_code(),
        "internal.projection.malformed-tree",
        "{failure:?}"
    );
}

#[test]
fn imported_template_keeps_the_captured_type_and_definition_context() {
    run("tests/fixtures/surface-macros/type-expression-bridge/keep_main.ash");
}

#[test]
fn imported_template_copies_the_captured_type_for_each_splice() {
    run("tests/fixtures/surface-macros/type-expression-bridge/twice_main.ash");
}

#[test]
fn imported_templates_preserve_captured_types_on_a_512k_stack() {
    const CHILD: &str = "ASH_TYPE_EXPRESSION_BRIDGE_512K_CHILD";
    if std::env::var_os(CHILD).is_none() {
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "imported_templates_preserve_captured_types_on_a_512k_stack",
                "--nocapture",
                "--test-threads=1",
            ])
            .env(CHILD, "1")
            .output()
            .unwrap();
        print!("{}", String::from_utf8_lossy(&output.stdout));
        let stderr = String::from_utf8_lossy(&output.stderr);
        eprint!("{stderr}");
        assert!(output.status.success(), "512 KiB child failed");
        assert!(stderr.contains("type expression stack: keep and twice executed 42"));
        return;
    }

    std::thread::Builder::new()
        .stack_size(512 * 1024)
        .spawn(|| {
            run("tests/fixtures/surface-macros/type-expression-bridge/keep_main.ash");
            run("tests/fixtures/surface-macros/type-expression-bridge/twice_main.ash");
            eprintln!("type expression stack: keep and twice executed 42");
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn protected_type_cannot_reach_an_expression_transformer() {
    reject("tests/fixtures/surface-macros/type-expression-bridge/blocked_main.ash");
}

#[test]
fn protected_type_cannot_cross_a_nested_expression_invocation() {
    reject("tests/fixtures/surface-macros/type-expression-bridge/nested_main.ash");
    reject("tests/fixtures/surface-macros/type-expression-bridge/outer_blocked_main.ash");
}
