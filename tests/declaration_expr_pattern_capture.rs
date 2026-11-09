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

#[test]
fn nested_declaration_admission_reports_its_depth_failure_through_the_driver() {
    use ash::{
        driver::{FileFailure, PipelineFailure},
        parser::ResourceFailure,
    };

    let fixture = Fixture::new();
    fixture.write(
        "inner.ash",
        "pub syntax declaration: (inner) $pattern:pattern yields $body:expr => {}\n",
    );
    fixture.write(
        "entry.ash",
        "import outer (syntax outer)\nmain : Unit -> Int\nmain () = 42\n",
    );
    let outer = |groups: usize| {
        format!(
            "import inner (syntax inner)\npub syntax declaration: (outer) $pattern:pattern yields $body:expr => {{\nprior : Unit -> Int\nprior () = 42\ninner $pattern yields {}$body{}\n}}\n",
            "(".repeat(groups),
            ")".repeat(groups),
        )
    };
    fixture.write("outer.ash", &outer(125));
    let program =
        compile_path(fixture.configuration()).expect("the at-limit nested template is admitted");
    assert_eq!(execute(&program).unwrap().value_display(), "42");
    fixture.write("outer.ash", &outer(126));
    let failure = compile_path(fixture.configuration())
        .expect_err("the over-limit nested capture is refused");
    assert_eq!(failure.reason_code(), "internal.resource.structural-depth");
    let FileFailure::Pipeline(context) = failure else {
        panic!("template admission must retain the pipeline failure");
    };
    let PipelineFailure::Syntax(syntax) = context.failure() else {
        panic!("template admission must retain the syntax resource failure");
    };
    assert_eq!(
        syntax.resource,
        Some(ResourceFailure::StructuralDepth { limit: 128 })
    );
}

fn write_forwarding_chain(fixture: &Fixture, count: usize, duplicate: bool) {
    fixture.write(
        "prior.ash",
        "pub syntax declaration: (before) $name:ident => {\n\
             pub $name : Unit -> Int\n\
             $name () = 0\n\
         }\n",
    );
    let initial = if duplicate { "10" } else { "40" };
    fixture.write(
        "entry.ash",
        &format!(
            "import layer0 (syntax step0)\n\
             import prior (syntax before)\n\
             before earlier\n\
             step0 answer matching value yields {initial}\n\
             main : Unit -> Int\n\
             main () = answer(0)\n"
        ),
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

fn group_boundary(fixture: &Fixture) -> usize {
    let mut succeeds = 0;
    let mut fails = 48;
    write_forwarding_chain(fixture, succeeds, false);
    let program = compile_path(fixture.configuration()).expect("the ungrouped chain compiles");
    assert_eq!(execute(&program).unwrap().value_display(), "42");
    drop(program);
    write_forwarding_chain(fixture, fails, false);
    let failure = compile_path(fixture.configuration()).expect_err("deep groups are bounded");
    assert_eq!(failure.reason_code(), "internal.resource.structural-depth");
    drop(failure);
    while fails - succeeds > 1 {
        let middle = (succeeds + fails) / 2;
        write_forwarding_chain(fixture, middle, false);
        match compile_path(fixture.configuration()) {
            Ok(program) => {
                assert_eq!(execute(&program).unwrap().value_display(), "42");
                succeeds = middle;
            }
            Err(failure) => {
                assert_eq!(failure.reason_code(), "internal.resource.structural-depth");
                fails = middle;
            }
        }
    }
    eprintln!("EP_GROUP_SUCCESS={succeeds} EP_GROUP_FAILURE={fails}");
    succeeds
}

#[test]
fn imported_grouped_forwarding_and_doubling_obey_the_shared_limits() {
    let fixture = Fixture::new();
    let boundary = group_boundary(&fixture);
    write_forwarding_chain(&fixture, boundary, false);
    let program = compile_path(fixture.configuration()).expect("the last grouped chain compiles");
    assert_eq!(execute(&program).unwrap().value_display(), "42");
    drop(program);
    write_forwarding_chain(&fixture, boundary + 1, false);
    let failure = compile_path(fixture.configuration()).expect_err("the next grouped chain fails");
    assert_eq!(failure.reason_code(), "internal.resource.structural-depth");
    drop(failure);

    write_forwarding_chain(&fixture, 25, true);
    let failure = compile_path(fixture.configuration()).expect_err("doubling exhausts shared work");
    assert_eq!(failure.reason_code(), "internal.resource.syntax-work");
}

#[test]
fn protected_expr_pattern_small_stack_child() {
    if std::env::var_os("ASH_TASK_0068_EP_SMALL_STACK_CHILD").is_none() {
        return;
    }
    std::thread::Builder::new()
        .stack_size(512 * 1024)
        .spawn(|| {
            let fixture = Fixture::new();
            let boundary = group_boundary(&fixture);
            write_forwarding_chain(&fixture, boundary, false);
            let program = compile_path(fixture.configuration()).expect("grouped chain succeeds");
            let result = execute(&program).unwrap();
            assert_eq!(result.value_display(), "42");
            drop(result);
            drop(program);
            eprintln!("EP_SMALL_STACK_SUCCESS_AND_DROP");

            write_forwarding_chain(&fixture, boundary + 1, false);
            let failure = compile_path(fixture.configuration()).expect_err("late depth failure");
            assert_eq!(failure.reason_code(), "internal.resource.structural-depth");
            drop(failure);
            eprintln!("EP_SMALL_STACK_LATE_DEPTH_DROP");

            write_forwarding_chain(&fixture, 25, true);
            let failure = compile_path(fixture.configuration()).expect_err("late work failure");
            assert_eq!(failure.reason_code(), "internal.resource.syntax-work");
            drop(failure);
            eprintln!("EP_SMALL_STACK_LATE_WORK_DROP");
        })
        .expect("the small-stack worker starts")
        .join()
        .expect("success and failures clean up on the small stack");
}

#[test]
fn protected_expr_pattern_survives_small_stack_success_and_failures() {
    let output = std::process::Command::new(std::env::current_exe().unwrap())
        .args([
            "--exact",
            "protected_expr_pattern_small_stack_child",
            "--nocapture",
        ])
        .env("ASH_TASK_0068_EP_SMALL_STACK_CHILD", "1")
        .output()
        .expect("the isolated small-stack child starts");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "{}\n{stdout}\n{stderr}",
        output.status
    );
    assert!(stdout.contains("test protected_expr_pattern_small_stack_child ... ok"));
    for marker in [
        "EP_SMALL_STACK_SUCCESS_AND_DROP",
        "EP_SMALL_STACK_LATE_DEPTH_DROP",
        "EP_SMALL_STACK_LATE_WORK_DROP",
    ] {
        assert!(stderr.contains(marker), "missing {marker}: {stderr}");
        eprintln!("{marker}");
    }
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
fn ordinary_expression_syntax_remains_available() {
    let fixture = Fixture::new();
    fixture.write(
        "helpers.ash",
        "pub syntax keep $body:expr => {\n $body\n}\n",
    );
    fixture.write(
        "entry.ash",
        "import helpers (syntax keep)\n\
         main : Unit -> Int\n\
         main () = keep 42\n",
    );
    let program =
        compile_path(fixture.configuration()).expect("ordinary expression syntax compiles");
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
