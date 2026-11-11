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
fn i01_identifier_captures_reach_the_ordinary_driver() {
    for name in ["control_01.ash", "case_01.ash"] {
        let program = compile_path(declaration_fixture(name))
            .expect("the fixed I01 declaration and its control compile");
        assert_eq!(execute(&program).unwrap().value_display(), "42");
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
fn introduced_signature_uses_its_definition_context_nominal() {
    let fixture = Fixture::new();
    fixture.write(
        "forms.ash",
        "pub type Layer<A> = Layer(A)\n\
         pub syntax declaration: (emit) $name:ident => {\n\
             pub $name : Layer<(Int, Int)> -> Int\n\
             $name _ = 42\n\
         }\n",
    );
    fixture.write(
        "entry.ash",
        "import forms (syntax emit)\n\
         emit answer\n\
         main : Unit -> Int\n\
         main () = 42\n",
    );

    let program = compile_path(fixture.configuration())
        .expect("the introduced type uses the syntax owner's nominal");
    assert_eq!(execute(&program).unwrap().value_display(), "42");
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
    use ash::{
        module::LoadGraphError,
        parser::{ExpectedForm, FoundToken, ParseReason},
    };

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
#[ignore = "blocked by the separately tracked definition-context nominal typing failure"]
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
fn imported_mixed_depth_control_reaches_checking_at_the_limit() {
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
            "import forms (Layer, syntax emit)\n\
             emit answer for {capture}\n\
             main : Unit -> Int\n\
             main () = 42\n"
        )
    };
    fixture.write("entry.ash", &entry(46));
    let program = compile_path(fixture.configuration())
        .expect("the supplemental mixed-depth graph reaches checking at the limit");
    assert_eq!(execute(&program).unwrap().value_display(), "42");
    drop(program);
    fixture.write("entry.ash", &entry(47));
    let failure = compile_path(fixture.configuration())
        .expect_err("one more captured tuple exceeds the combined depth");
    assert_eq!(failure.reason_code(), "internal.resource.structural-depth");
}

#[test]
fn imported_effect_row_combines_all_type_depth_edges() {
    let fixture = Fixture::new();
    let generated = format!("{}$T{}", "Layer<(".repeat(40), ")>".repeat(40));
    fixture.write(
        "forms.ash",
        &format!(
            "pub type Layer<A> = Layer(A)\n\
             pub effect Read<A> {{\n read : Unit -> A\n }}\n\
             pub syntax declaration: (emit) $name:ident for $T:type => {{\n\
                 pub $name : Unit -> Int ! {{Read<{generated}>}}\n\
                 $name () = 42\n\
             }}\n"
        ),
    );
    let entry = |height: usize| {
        let capture = format!("{}Int{}", "(".repeat(height), ", Int)".repeat(height));
        format!(
            "import forms (Layer, Read, syntax emit)\n\
             emit answer for {capture}\n\
             main : Unit -> Int\n\
             main () = 42\n"
        )
    };
    fixture.write("entry.ash", &entry(44));
    let program = compile_path(fixture.configuration())
        .expect("function, effect row, applications, groups and captured tuple fit");
    assert_eq!(execute(&program).unwrap().value_display(), "42");
    drop(program);
    fixture.write("entry.ash", &entry(45));
    let failure = compile_path(fixture.configuration())
        .expect_err("one more captured tuple exceeds the effect-row depth");
    assert_eq!(failure.reason_code(), "internal.resource.structural-depth");
}

#[test]
fn generated_raw_type_leaves_respect_the_composed_depth() {
    let fixture = Fixture::new();
    fixture.write(
        "entry.ash",
        "import forms (Layer, Leaf, syntax emit)\n\
         emit answer for Int\n\
         main : Unit -> Int\n\
         main () = 42\n",
    );
    let mut unexpected = Vec::new();
    for leaf in ["Int", "Leaf"] {
        for extra_group in [false, true] {
            let raw = if extra_group {
                format!("({leaf})")
            } else {
                leaf.to_owned()
            };
            let nested = format!("{}{raw}{}", "Layer<(".repeat(63), ")>".repeat(63));
            fixture.write(
                "forms.ash",
                &format!(
                    "pub type Layer<A> = Layer(A)\n\
                     pub type Leaf = Leaf\n\
                     pub syntax declaration: (emit) $name:ident for $T:type => {{\n\
                         pub $name : {nested} -> $T\n\
                         $name _ = 42\n\
                     }}\n"
                ),
            );
            match (extra_group, compile_path(fixture.configuration())) {
                (false, Ok(program)) => {
                    assert_eq!(execute(&program).unwrap().value_display(), "42");
                }
                (true, Err(failure))
                    if failure.reason_code() == "internal.resource.structural-depth" => {}
                (extra, result) => unexpected.push((
                    leaf,
                    extra,
                    result.err().map(|failure| failure.reason_code()),
                )),
            }
        }
    }
    assert!(
        unexpected.is_empty(),
        "unexpected raw-leaf outcomes: {unexpected:?}"
    );
}

#[test]
fn forwarded_type_in_generated_expression_invocation_is_supported() {
    let fixture = Fixture::new();
    fixture.write(
        "entry.ash",
        "import forms (syntax emit)\n\
         import helpers (syntax keep)\n\
         emit answer through keep for Int\n\
         main : Unit -> Int\n\
         main () = answer(0)\n",
    );
    fixture.write(
        "helpers.ash",
        "pub syntax keep $body:expr => {\n $body\n}\n",
    );
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
    let program = compile_path(fixture.configuration())
        .expect("the generated expression argument retains its forwarded type");
    let result = execute(&program).unwrap();
    assert_eq!(result.value_display(), "0");
    assert_eq!(result.type_display(), "Int");
}

#[test]
fn imported_expression_syntax_preserves_a_forwarded_type() {
    let fixture = Fixture::new();
    fixture.write(
        "entry.ash",
        "import forms (syntax emit)\n\
         emit answer for Int\n\
         main : Unit -> Int\n\
         main () = answer(0)\n",
    );
    fixture.write(
        "helpers.ash",
        "pub syntax keep $body:expr => {\n $body\n}\n",
    );
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
    let program = compile_path(fixture.configuration())
        .expect("the imported template retains the expression argument's forwarded type");
    let result = execute(&program).unwrap();
    assert_eq!(result.value_display(), "0");
    assert_eq!(result.type_display(), "Int");
}

fn write_prior_generated_type(fixture: &Fixture) {
    fixture.write(
        "prior.ash",
        "pub syntax declaration: (before) $Name:ident constructor $Ctor:ident => {\n\
             pub type $Name = $Ctor(Int)\n\
         }\n",
    );
}

fn write_doubling_chain(fixture: &Fixture, count: usize) {
    write_prior_generated_type(fixture);
    fixture.write(
        "entry.ash",
        "import layer0 (syntax step0)\n\
         import prior (syntax before)\n\
         before Earlier constructor Earlier\n\
         step0 Witness constructor Witness for Int\n\
         main : Unit -> Int\n\
         main () = 42\n",
    );
    for index in 0..count {
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
        &format!("layer{count}.ash"),
        &format!("pub syntax declaration: (step{count}) $Name:ident constructor $Ctor:ident for $T:type => {{\n\
             pub type $Name = $Ctor($T)\n\
         }}\n"),
    );
}

#[test]
fn imported_doubling_stops_at_the_shared_work_limit() {
    let fixture = Fixture::new();
    write_doubling_chain(&fixture, 25);
    let failure = compile_path(fixture.configuration())
        .expect_err("repeated imported copies exceed the default shared allowance");
    assert_eq!(failure.reason_code(), "internal.resource.syntax-work");
}

fn write_group_chain(fixture: &Fixture, count: usize) {
    write_prior_generated_type(fixture);
    fixture.write(
        "entry.ash",
        "import layer0 (syntax step0)\n\
         import prior (syntax before)\n\
         before Earlier constructor Earlier\n\
         step0 answer for Int\n\
         main : Unit -> Int\n\
         main () = answer(42)\n",
    );
    for index in 0..count {
        fixture.write(
            &format!("layer{index}.ash"),
            &format!(
                "import layer{} (syntax step{})\n\
                 pub syntax declaration: (step{index}) $name:ident for $T:type => {{\n\
                     step{} $name for ($T)\n\
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
            "pub syntax declaration: (step{count}) $name:ident for $T:type => {{\n\
                 pub $name : $T -> $T\n\
                 $name value = value\n\
             }}\n"
        ),
    );
}

#[test]
fn imported_group_only_forwarding_checks_retained_depth() {
    let fixture = Fixture::new();
    write_group_chain(&fixture, 42);
    let program = compile_path(fixture.configuration())
        .expect("42 imported grouping-only forwards fit the retained depth");
    assert_eq!(execute(&program).unwrap().value_display(), "42");
    drop(program);
    write_group_chain(&fixture, 43);
    let failure = compile_path(fixture.configuration())
        .expect_err("one more grouping-only forward exceeds retained depth");
    assert_eq!(failure.reason_code(), "internal.resource.structural-depth");
}

#[test]
fn protected_types_small_stack_child() {
    if std::env::var_os("ASH_TASK_0068_SMALL_STACK_CHILD").is_none() {
        return;
    }
    std::thread::Builder::new()
        .stack_size(512 * 1024)
        .spawn(|| {
            let fixture = Fixture::new();
            write_group_chain(&fixture, 42);
            let program = compile_path(fixture.configuration())
                .expect("near-boundary grouped forwarding checks on the small stack");
            let result = execute(&program).unwrap();
            assert_eq!(result.value_display(), "42");
            drop(result);
            drop(program);
            eprintln!("SMALL_STACK_SUCCESS_AND_DROP");

            write_group_chain(&fixture, 43);
            let failure = compile_path(fixture.configuration()).expect_err("late depth failure");
            assert_eq!(failure.reason_code(), "internal.resource.structural-depth");
            drop(failure);
            eprintln!("SMALL_STACK_LATE_DEPTH_DROP");
            write_doubling_chain(&fixture, 25);
            let failure = compile_path(fixture.configuration()).expect_err("late work failure");
            assert_eq!(failure.reason_code(), "internal.resource.syntax-work");
            drop(failure);
            eprintln!("SMALL_STACK_LATE_WORK_DROP");
        })
        .expect("the small-stack worker starts")
        .join()
        .expect("success and late failures clean up on the small stack");
}

#[test]
fn protected_types_survive_small_stack_success_and_failures() {
    let output = std::process::Command::new(std::env::current_exe().unwrap())
        .args([
            "--exact",
            "protected_types_small_stack_child",
            "--nocapture",
        ])
        .env("ASH_TASK_0068_SMALL_STACK_CHILD", "1")
        .output()
        .expect("the isolated small-stack child starts");
    assert!(
        output.status.success(),
        "small-stack child failed: {}\n{}\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stdout.contains("test protected_types_small_stack_child ... ok"));
    for marker in [
        "SMALL_STACK_SUCCESS_AND_DROP",
        "SMALL_STACK_LATE_DEPTH_DROP",
        "SMALL_STACK_LATE_WORK_DROP",
    ] {
        assert!(stderr.contains(marker), "missing child marker: {marker}");
    }
}
