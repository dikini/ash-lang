use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    driver::{RunConfiguration, compile_path, execute},
    module::ModuleRoots,
};

#[test]
fn imported_empty_template_captures_a_complete_declaration() {
    let entry = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/surface-macros/declaration-capture/main.ash");
    let program = compile_path(RunConfiguration {
        entry,
        roots: ModuleRoots::empty(),
    })
    .expect("the imported empty template accepts one complete source declaration");
    assert_eq!(execute(&program).unwrap().value_display(), "42");
}

struct Fixture(PathBuf);

impl Fixture {
    fn new() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "ash-d5-capture-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }

    fn compile(
        &self,
        forms: &str,
        invocation: &str,
    ) -> Result<ash::driver::CompiledProgram, ash::driver::FileFailure> {
        fs::write(self.0.join("forms.ash"), forms).unwrap();
        fs::write(
            self.0.join("main.ash"),
            format!(
                "import forms (syntax sink)\n\n{invocation}\n\nmain : Unit -> Int\nmain () = 42\n"
            ),
        )
        .unwrap();
        compile_path(RunConfiguration {
            entry: self.0.join("main.ash"),
            roots: ModuleRoots::empty(),
        })
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn source_sink_accepts_each_ordinary_declaration_category() {
    let fixture = Fixture::new();
    let forms = include_str!("fixtures/surface-macros/declaration-capture/forms.ash");
    for declaration in [
        "type Color = Red(Int)",
        "newtype Box = Box(Int)",
        "interface Marker<A> {\n    mark : A -> Bool\n}",
        "impl Marker<Int> {\n    mark _ = true\n}",
        "effect Ask {\n    ask : Unit -> Int\n}",
        "foreign library Fixture {\n    profile \"x86_64-unknown-linux-gnu\"\n    symbol Make : Unit -> F.Address { name \"fixture_make\" }\n}",
        "passed : Unit -> Int\npassed () = 42",
        "fn same(value: Int) -> Int {\n    value\n}",
    ] {
        let program = fixture
            .compile(forms, &format!("sink {{\n{declaration}\n}}"))
            .unwrap_or_else(|error| panic!("{declaration}: {error:?}"));
        assert_eq!(execute(&program).unwrap().value_display(), "42");
    }
}

#[test]
fn source_capture_rejects_incomplete_multiple_or_excluded_declarations() {
    let fixture = Fixture::new();
    let forms = include_str!("fixtures/surface-macros/declaration-capture/forms.ash");
    for declaration in [
        "",
        "passed : Unit -> Int",
        "passed () = 42",
        "type One = One\ntype Two = Two",
        "type One = One trailing",
        "type Broken =",
        "import other (name)",
        "pub syntax declaration: (other) => {}",
        "sink { type Nested = Nested }",
        "resource Forbidden {}",
    ] {
        assert!(
            fixture
                .compile(forms, &format!("sink {{\n{declaration}\n}}"))
                .is_err(),
            "accepted {declaration:?}"
        );
    }
}

#[test]
fn removing_one_equation_can_leave_a_complete_declaration() {
    let fixture = Fixture::new();
    let forms = include_str!("fixtures/surface-macros/declaration-capture/forms.ash");
    let declaration = "passed : Bool -> Int\npassed true = 42\npassed false = 0";
    for source in [
        declaration.to_owned(),
        declaration.replace("\npassed false = 0", ""),
    ] {
        let program = fixture
            .compile(forms, &format!("sink {{\n{source}\n}}"))
            .expect("a remaining equation is syntactically complete");
        assert_eq!(execute(&program).unwrap().value_display(), "42");
    }
}

#[test]
fn nonempty_and_procedural_declaration_capture_definitions_are_not_admitted() {
    let fixture = Fixture::new();
    for forms in [
        "pub syntax declaration: (sink) $item:declaration => { $item }\n",
        "pub syntax declaration: (sink) $item:declaration => { type Item = Item }\n",
        "pub syntax declaration: (sink) $item:declaration => using transform\n",
    ] {
        assert!(fixture.compile(forms, "").is_err(), "accepted {forms:?}");
    }
}
