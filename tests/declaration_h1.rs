use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    driver::{RunConfiguration, compile_path, execute},
    module::ModuleRoots,
};

fn fixture(name: &str) -> RunConfiguration {
    RunConfiguration {
        entry: PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("docs/design/macros/fixtures/nested")
            .join(name),
        roots: ModuleRoots::empty(),
    }
}

#[test]
fn i20_forward_declarations_reach_the_ordinary_module_collector() {
    let program = compile_path(fixture("forward.ash")).expect("the fixed I20 graph compiles");
    assert_eq!(execute(&program).unwrap().value_display(), "42");
}

#[test]
fn i20_nested_selection_uses_the_definition_owner() {
    let program = compile_path(fixture("main.ash")).expect("the fixed nested I20 graph compiles");
    assert_eq!(execute(&program).unwrap().value_display(), "42");
}

#[test]
fn i20_handwritten_controls_remain_unchanged() {
    for name in ["control_forward.ash", "control.ash"] {
        let program = compile_path(fixture(name)).expect("the handwritten control compiles");
        assert_eq!(execute(&program).unwrap().value_display(), "42");
    }
}

#[test]
fn imported_renamed_declarations_coexist_with_expression_syntax() {
    let fixtures =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("docs/design/macros/fixtures/header_compat");
    for name in ["renamed.ash", "both.ash"] {
        let program = compile_path(RunConfiguration {
            entry: fixtures.join(name),
            roots: ModuleRoots::empty(),
        })
        .expect("the selected declaration syntax should reach ordinary collection");
        assert_eq!(execute(&program).unwrap().value_display(), "42");
    }
}

#[test]
fn generated_expression_syntax_uses_its_owner_after_declaration_introduction() {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let path = std::env::temp_dir().join(format!(
        "ash-h1-owner-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&path).unwrap();
    struct Fixture(PathBuf);
    impl Drop for Fixture {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }
    let fixture = Fixture(path);
    for (name, text) in [
        (
            "expression.ash",
            "helper : Unit -> Int\nhelper () = 42\npub syntax reveal $x:expr => {\nhelper($x)\n}\n",
        ),
        (
            "declarations.ash",
            "import expression (syntax reveal)\npub syntax declaration: (emit) $name:ident => {\n$name : Unit -> Int\n$name () = reveal ()\n}\n",
        ),
        (
            "entry.ash",
            "import declarations (syntax emit)\nemit answer\nmain : Unit -> Int\nmain () = answer(())\n",
        ),
    ] {
        fs::write(fixture.0.join(name), text).unwrap();
    }
    let program = compile_path(RunConfiguration {
        entry: fixture.0.join("entry.ash"),
        roots: ModuleRoots::empty(),
    })
    .expect("the emitted expression syntax retains its definition owner");
    assert_eq!(execute(&program).unwrap().value_display(), "42");
}
