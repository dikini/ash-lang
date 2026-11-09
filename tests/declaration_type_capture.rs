use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    driver::{RunConfiguration, compile_path, execute},
    module::ModuleRoots,
};

fn declaration_fixture(name: &str) -> RunConfiguration {
    RunConfiguration {
        entry: PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("docs/design/macros/fixtures/declarations")
            .join(name),
        roots: ModuleRoots::empty(),
    }
}

struct Fixture(PathBuf);

impl Fixture {
    fn new() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "ash-declaration-type-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }

    fn write(&self, name: &str, text: &str) {
        fs::write(self.0.join(name), text).unwrap();
    }

    fn configuration(&self) -> RunConfiguration {
        RunConfiguration {
            entry: self.0.join("entry.ash"),
            roots: ModuleRoots::empty(),
        }
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn i07_type_captures_reach_the_ordinary_driver() {
    let control = compile_path(declaration_fixture("control_07.ash"))
        .expect("the handwritten I07 control compiles");
    assert_eq!(execute(&control).unwrap().value_display(), "42");

    let generated =
        compile_path(declaration_fixture("case_07.ash")).expect("the I07 macro graph compiles");
    assert_eq!(execute(&generated).unwrap().value_display(), "42");
}

#[test]
fn imported_templates_forward_and_duplicate_a_type_capture() {
    let fixture = Fixture::new();
    fixture.write(
        "entry.ash",
        "import layer0 (syntax step0)\n\
         step0 Witness constructor Witness for Int\n\
         main : Unit -> Int\n\
         main () = match Witness(((1, 2), (3, 4))) {\n\
             Witness(_) => 42\n\
         }\n",
    );
    for index in 0..2 {
        fixture.write(
            &format!("layer{index}.ash"),
            &format!(
                "import layer{} (syntax step{})\n\
                 pub syntax declaration: (step{index}) $Name:ident constructor $Ctor:ident for $T:type => {{\n\
                     step{} $Name constructor $Ctor for ($T, $T)\n\
                 }}\n",
                index + 1,
                index + 1,
                index + 1,
            ),
        );
    }
    fixture.write(
        "layer2.ash",
        "pub syntax declaration: (step2) $Name:ident constructor $Ctor:ident for $T:type => {\n\
             pub type $Name = $Ctor($T)\n\
         }\n",
    );

    let program = compile_path(fixture.configuration()).expect("the imported type chain compiles");
    assert_eq!(execute(&program).unwrap().value_display(), "42");
}
