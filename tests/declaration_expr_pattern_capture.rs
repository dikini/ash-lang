use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    driver::{RunConfiguration, compile_path, execute},
    module::ModuleRoots,
};

fn captures_fixture(name: &str) -> RunConfiguration {
    RunConfiguration {
        entry: PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("docs/design/macros/fixtures/captures")
            .join(name),
        roots: ModuleRoots::empty(),
    }
}

struct Fixture(PathBuf);

impl Fixture {
    fn new() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "ash-declaration-expr-pattern-{}-{}",
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
fn i19_handwritten_binder_control_reaches_the_ordinary_driver() {
    let program = compile_path(captures_fixture("control_binder.ash"))
        .expect("the unchanged handwritten binder control compiles");
    assert_eq!(execute(&program).unwrap().value_display(), "42");
}

#[test]
fn i19_imported_pattern_binder_and_expression_keep_the_caller_context() {
    let program = compile_path(captures_fixture("binder.ash"))
        .expect("the unchanged imported binder graph compiles");
    assert_eq!(execute(&program).unwrap().value_display(), "42");
}

fn write_forwarding_chain(fixture: &Fixture, count: usize, duplicate: bool) {
    fixture.write(
        "entry.ash",
        "import layer0 (syntax step0)\n\
         step0 answer matching value yields 10\n\
         main : Unit -> Int\n\
         main () = answer(0)\n",
    );
    for index in 0..count {
        let body = if duplicate {
            "($body + $body)"
        } else {
            "($body)"
        };
        fixture.write(
            &format!("layer{index}.ash"),
            &format!(
                "import layer{} (syntax step{})\n\
                 pub syntax declaration: (step{index}) $name:ident matching $pattern:pattern yields $body:expr => {{\n\
                     step{} $name matching ($pattern) yields {body}\n\
                 }}\n",
                index + 1,
                index + 1,
                index + 1,
            ),
        );
    }
    fixture.write(
        &format!("layer{count}.ash"),
        &format!(
            "pub syntax declaration: (step{count}) $name:ident matching $pattern:pattern yields $body:expr => {{\n\
                 pub $name : Int -> Int\n\
                 $name $pattern = $body + 2\n\
             }}\n"
        ),
    );
}

#[test]
fn imported_pattern_and_expression_forwarding_duplicates_the_caller_expression() {
    let fixture = Fixture::new();
    write_forwarding_chain(&fixture, 2, true);
    let program =
        compile_path(fixture.configuration()).expect("the imported forwarding chain compiles");
    assert_eq!(execute(&program).unwrap().value_display(), "42");
}

#[test]
fn protected_expression_with_nested_expression_syntax_is_refused() {
    let fixture = Fixture::new();
    fixture.write(
        "forms.ash",
        "pub syntax declaration: (emit) $name:ident for $body:expr => {\n\
             pub $name : Unit -> Int\n\
             $name () = $body\n\
         }\n",
    );
    fixture.write(
        "helpers.ash",
        "pub syntax keep $body:expr => {\n $body\n}\n",
    );
    let entry = |body: &str| {
        format!(
            "import forms (syntax emit)\n\
             import helpers (syntax keep)\n\
             emit answer for {body}\n\
             main : Unit -> Int\n\
             main () = answer(())\n"
        )
    };
    fixture.write("entry.ash", &entry("(40 + 2)"));
    let program =
        compile_path(fixture.configuration()).expect("the ordinary expression is accepted");
    assert_eq!(execute(&program).unwrap().value_display(), "42");
    drop(program);

    fixture.write("entry.ash", &entry("(keep 42)"));
    let failure = compile_path(fixture.configuration())
        .expect_err("a protected expression cannot carry nested expression syntax");
    assert_eq!(
        failure.reason_code(),
        "internal.projection.malformed-tree",
        "{failure:?}"
    );
}

#[test]
fn forwarded_expression_in_generated_expression_syntax_argument_is_refused() {
    let fixture = Fixture::new();
    fixture.write(
        "helpers.ash",
        "pub syntax keep $body:expr => {\n $body\n}\n",
    );
    fixture.write(
        "entry.ash",
        "import forms (syntax emit)\n\
         emit answer for 42\n\
         main : Unit -> Int\n\
         main () = answer(())\n",
    );
    let forms = |body: &str| {
        format!(
            "import helpers (syntax keep)\n\
             pub syntax declaration: (emit) $name:ident for $body:expr => {{\n\
                 pub $name : Unit -> Int\n\
                 $name () = keep ({body})\n\
             }}\n"
        )
    };
    fixture.write("forms.ash", &forms("42"));
    let program =
        compile_path(fixture.configuration()).expect("an ordinary generated argument works");
    assert_eq!(execute(&program).unwrap().value_display(), "42");
    drop(program);

    fixture.write("forms.ash", &forms("$body"));
    let failure = compile_path(fixture.configuration())
        .expect_err("a forwarded expression inside an expression-syntax argument is guarded");
    assert_eq!(
        failure.reason_code(),
        "internal.projection.malformed-tree",
        "{failure:?}"
    );
}

#[test]
fn forwarded_pattern_in_generated_expression_syntax_argument_is_refused() {
    let fixture = Fixture::new();
    fixture.write(
        "helpers.ash",
        "pub syntax keep $body:expr => {\n $body\n}\n",
    );
    fixture.write(
        "entry.ash",
        "import forms (syntax emit)\n\
         emit answer matching value\n\
         main : Unit -> Int\n\
         main () = answer(())\n",
    );
    let forms = |pattern: &str| {
        format!(
            "import helpers (syntax keep)\n\
             pub syntax declaration: (emit) $name:ident matching $pattern:pattern => {{\n\
                 pub $name : Unit -> Int\n\
                 $name () = keep ({{\n\
                     let {pattern} = 42\n\
                     42\n\
                 }})\n\
             }}\n"
        )
    };
    fixture.write("forms.ash", &forms("_"));
    let program =
        compile_path(fixture.configuration()).expect("an ordinary generated pattern works");
    assert_eq!(execute(&program).unwrap().value_display(), "42");
    drop(program);

    fixture.write("forms.ash", &forms("$pattern"));
    let failure = compile_path(fixture.configuration())
        .expect_err("a forwarded pattern inside an expression-syntax argument is guarded");
    assert_eq!(
        failure.reason_code(),
        "internal.projection.malformed-tree",
        "{failure:?}"
    );
}
