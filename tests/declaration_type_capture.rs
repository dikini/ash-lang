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

#[test]
fn i07_missing_type_is_reported_at_the_invocation() {
    use ash::{module::LoadGraphError, parser::{ExpectedForm, FoundToken, ParseReason}};

    let fixture = Fixture::new();
    fixture.write(
        "forms.ash",
        include_str!("../docs/design/macros/fixtures/declarations/forms.ash"),
    );
    let entry = include_str!("../docs/design/macros/fixtures/declarations/case_07.ash")
        .replace("make_identity id for Int", "make_identity id for");
    fixture.write("entry.ash", &entry);
    let failure = compile_path(fixture.configuration()).expect_err("the type is missing");
    assert_eq!(failure.reason_code(), "parse.expected-form");
    let Some(LoadGraphError::Syntax(syntax)) = failure.graph_failure() else {
        panic!("expected an invocation parse failure: {failure:?}");
    };
    assert!(syntax.source.display_path().ends_with("entry.ash"));
    let diagnostic = &syntax.parser[0];
    assert_eq!(diagnostic.reason, ParseReason::ExpectedForm);
    assert_eq!(diagnostic.expected_form(), Some(ExpectedForm::Type));
    assert_eq!(diagnostic.found_token(), Some(FoundToken::LineEnd));
    let position = entry.find("make_identity id for\n").unwrap() + "make_identity id for".len();
    assert_eq!(diagnostic.primary.span().range().start() as usize, position);
}

#[test]
fn imported_generated_type_combines_applications_grouping_and_capture_depth() {
    let fixture = Fixture::new();
    let generated = format!("{}$T{}", "Layer<(".repeat(40), ")>".repeat(40));
    fixture.write(
        "forms.ash",
        &format!(
            "pub type Layer<A> = Layer(A)\n\
             pub syntax declaration: (emit) $name:ident for $T:type => {{\n\
                 pub $name : {generated} -> Int\n\
                 $name _ = 42\n\
             }}\n"
        ),
    );
    let entry = |height: usize| {
        let capture = format!("{}Int{}", "(".repeat(height), ", Int)".repeat(height));
        format!(
            "import forms (syntax emit)\n\
             emit answer for {capture}\n\
             main : Unit -> Int\n\
             main () = 42\n"
        )
    };
    fixture.write("entry.ash", &entry(46));
    let program = compile_path(fixture.configuration())
        .expect("the combined depth at the limit reaches ordinary checking");
    assert_eq!(execute(&program).unwrap().value_display(), "42");
    drop(program);

    fixture.write("entry.ash", &entry(47));
    let failure = compile_path(fixture.configuration())
        .expect_err("one more captured tuple exceeds the combined depth");
    assert_eq!(failure.reason_code(), "internal.resource.structural-depth");
}

#[test]
fn forwarded_type_in_generated_expression_invocation_is_refused() {
    let fixture = Fixture::new();
    fixture.write(
        "entry.ash",
        "import forms (syntax emit)\n\
         import helpers (syntax keep)\n\
         emit answer through keep for Int\n\
         main : Unit -> Int\n\
         main () = answer(0)\n",
    );
    fixture.write("helpers.ash", "pub syntax keep $body:expr => {\n $body\n}\n");
    let forms = |expression: &str| {
        format!(
            "pub syntax declaration: (emit) $name:ident through $macro:ident for $T:type => {{\n\
                 pub fn $name(value: $T) -> Int {{\n\
                     {expression}\n\
                 }}\n\
             }}\n"
        )
    };
    fixture.write("forms.ash", &forms("$macro 42"));
    let program = compile_path(fixture.configuration())
        .expect("a type capture and an ordinary generated expression both work");
    assert_eq!(execute(&program).unwrap().value_display(), "42");
    drop(program);

    fixture.write(
        "forms.ash",
        &forms("$macro ({\n let copy : ($T) = value\n copy\n })"),
    );
    let failure = compile_path(fixture.configuration())
        .expect_err("a forwarded type inside a nested expression argument is guarded");
    assert_eq!(failure.reason_code(), "internal.projection.malformed-tree", "{failure:?}");
}

#[test]
fn imported_expression_syntax_refuses_a_nested_forwarded_type() {
    let fixture = Fixture::new();
    fixture.write(
        "entry.ash",
        "import forms (syntax emit)\n\
         emit answer for Int\n\
         main : Unit -> Int\n\
         main () = answer(0)\n",
    );
    fixture.write("helpers.ash", "pub syntax keep $body:expr => {\n $body\n}\n");
    let forms = |expression: &str| {
        format!(
            "import helpers (syntax keep)\n\
             pub syntax declaration: (emit) $name:ident for $T:type => {{\n\
                 pub fn $name(value: $T) -> Int {{\n\
                     {expression}\n\
                 }}\n\
             }}\n"
        )
    };
    fixture.write("forms.ash", &forms("keep 42"));
    let program = compile_path(fixture.configuration())
        .expect("the imported expression syntax executes in generated code");
    assert_eq!(execute(&program).unwrap().value_display(), "42");
    drop(program);

    fixture.write(
        "forms.ash",
        &forms("keep ({\n let copy : ($T) = value\n copy\n })"),
    );
    let failure = compile_path(fixture.configuration())
        .expect_err("a forwarded type inside a nested expression argument is guarded");
    assert_eq!(failure.reason_code(), "internal.projection.malformed-tree", "{failure:?}");
}

#[test]
fn imported_doubling_stops_at_the_shared_work_limit() {
    let fixture = Fixture::new();
    fixture.write(
        "entry.ash",
        "import layer0 (syntax step0)\n\
         type Earlier = Earlier(Int)\n\
         step0 Witness constructor Witness for Int\n\
         main : Unit -> Int\n\
         main () = 42\n",
    );
    for index in 0..25 {
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
        "layer25.ash",
        "pub syntax declaration: (step25) $Name:ident constructor $Ctor:ident for $T:type => {\n\
             pub type $Name = $Ctor($T)\n\
         }\n",
    );
    let failure = compile_path(fixture.configuration())
        .expect_err("repeated imported copies exceed the default shared allowance");
    assert_eq!(failure.reason_code(), "internal.resource.syntax-work");
}

#[test]
fn investigate_mixed_consumer() {
    let fixture = Fixture::new();
    for (applications, height) in [(0, 0), (1, 0), (0, 1), (1, 1), (10, 10), (20, 20), (40, 46)] {
        let capture = format!("{}Int{}", "(".repeat(height), ", Int)".repeat(height));
        for mode in ["generated_function", "generated_function_imported", "handwritten_function", "generated_type"] {
            let protected = if mode == "handwritten_function" { capture.as_str() } else { "$T" };
            let generated = format!("{}{protected}{}", "Layer<(".repeat(applications), ")>".repeat(applications));
            let declaration = if mode == "generated_type" {
                format!("pub type Subject = Subject({generated})\n")
            } else if mode.starts_with("generated_function") {
                format!("pub $name : {generated} -> Int\n$name _ = 42\n")
            } else {
                format!("pub answer : {generated} -> Int\nanswer _ = 42\n")
            };
            let (forms, entry) = if mode == "handwritten_function" {
                ("pub type Layer<A> = Layer(A)\n".to_owned(), format!("import forms (Layer)\n{declaration}main : Unit -> Int\nmain () = 42\n"))
            } else if mode.starts_with("generated_function") {
                let imports = if mode == "generated_function_imported" { "Layer, syntax emit" } else { "syntax emit" };
                (format!("pub type Layer<A> = Layer(A)\npub syntax declaration: (emit) $name:ident for $T:type => {{\n{declaration}}}\n"), format!("import forms ({imports})\nemit answer for {capture}\nmain : Unit -> Int\nmain () = 42\n"))
            } else {
                (format!("pub type Layer<A> = Layer(A)\npub syntax declaration: (emit) $T:type => {{\n{declaration}}}\n"), format!("import forms (syntax emit)\nemit {capture}\nmain : Unit -> Int\nmain () = 42\n"))
            };
            fixture.write("forms.ash", &forms);
            fixture.write("entry.ash", &entry);
            match compile_path(fixture.configuration()) {
                Ok(program) => eprintln!("{mode} applications={applications} height={height}: OK {}", execute(&program).unwrap().value_display()),
                Err(failure) => eprintln!("{mode} applications={applications} height={height}: {} {:?}", failure.reason_code(), failure.pipeline_failure()),
            }
        }
    }
}
