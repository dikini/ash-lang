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
        loop {
            let path = std::env::temp_dir().join(format!(
                "ash-declaration-expr-pattern-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            match fs::create_dir(&path) {
                Ok(()) => return Self(path),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("cannot create fixture: {error}"),
            }
        }
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
fn i19_handwritten_main_and_count_controls_match_the_fixed_results() {
    for (entry, expected) in [("control.ash", "128"), ("control_counts.ash", "42")] {
        let program = compile_path(captures_fixture(entry)).expect(entry);
        assert_eq!(execute(&program).unwrap().value_display(), expected);
    }
}

#[test]
fn i19_complete_capture_and_repetition_graph_reaches_the_ordinary_driver() {
    let program = compile_path(captures_fixture("main.ash"))
        .expect("the unchanged I19 capture and repetition graph compiles");
    assert_eq!(execute(&program).unwrap().value_display(), "128");
}

#[test]
fn i19_repetition_counts_reach_the_ordinary_driver() {
    let program = compile_path(captures_fixture("counts.ash"))
        .expect("the unchanged I19 repetition counts graph compiles");
    assert_eq!(execute(&program).unwrap().value_display(), "42");
}

#[test]
fn equal_repetition_drivers_generate_all_paired_declarations() {
    let fixture = Fixture::new();
    fixture.write(
        "forms.ash",
        include_str!("../docs/design/macros/fixtures/captures/forms.ash"),
    );
    fixture.write("entry.ash", "import forms (syntax paired)\npaired left first, second right third, fourth\nmain : Unit -> Int\nmain () = 36 + first(()) + second(()) + third(()) + fourth(())\n");
    let program = compile_path(fixture.configuration())
        .expect("equal repetition drivers generate their declarations");
    assert_eq!(execute(&program).unwrap().value_display(), "42");
}

#[test]
fn i19_imported_pattern_binder_and_expression_keep_the_caller_context() {
    let program = compile_path(captures_fixture("binder.ash"))
        .expect("the unchanged imported binder graph compiles");
    assert_eq!(execute(&program).unwrap().value_display(), "42");
}

#[test]
fn repeated_expression_captures_reach_the_module_consumer_in_order() {
    let fixture = Fixture::new();
    fixture.write(
        "forms.ash",
        "pub syntax declaration: (terms) $( $name:ident from $value:expr ),+ => {\n$(\npub $name : Unit -> Int\n$name () = $value\n)+\n}\n",
    );
    fixture.write(
        "entry.ash",
        "import forms (syntax terms)\nterms first from 20, second from 22\nmain : Unit -> Int\nmain () = first(()) + second(())\n",
    );
    let program = compile_path(fixture.configuration())
        .expect("repeated expressions pass through the ordinary module consumer");
    assert_eq!(execute(&program).unwrap().value_display(), "42");
}

#[test]
fn repeated_type_and_pattern_captures_keep_their_categories() {
    let fixture = Fixture::new();
    fixture.write("forms.ash", "pub syntax declaration: (ids) $( $name:ident as $T:type ),+ => {\n$(\npub $name : $T -> $T\n$name value = value\n)+\n}\npub syntax declaration: (preds) $( $name:ident when $pat:pattern ),+ => {\n$(\npub $name : Bool -> Int\n$name $pat = 21\n$name _ = 0\n)+\n}\n");
    fixture.write("entry.ash", "import forms (syntax ids, syntax preds)\nids identity as Int, other as Int\npreds yes when true, no when false\nmain : Unit -> Int\nmain () = identity(yes(true)) + other(no(false))\n");
    let program =
        compile_path(fixture.configuration()).expect("repeated type and pattern captures compile");
    assert_eq!(execute(&program).unwrap().value_display(), "42");
}

#[test]
fn repeated_declaration_packets_remain_complete_module_declarations() {
    let fixture = Fixture::new();
    fixture.write(
        "forms.ash",
        "pub syntax declaration: (pass_all) $( $item:declaration ),+ => {\n$(\n$item\n)+\n}\n",
    );
    fixture.write("entry.ash", "import forms (syntax pass_all)\npass_all {\nfirst : Unit -> Int\nfirst () = 20\n}, {\nsecond : Unit -> Int\nsecond () = 22\n}\nmain : Unit -> Int\nmain () = first(()) + second(())\n");
    let program = compile_path(fixture.configuration())
        .expect("repeated declaration packets remain distinct");
    assert_eq!(execute(&program).unwrap().value_display(), "42");
}

#[test]
fn nested_ragged_repetitions_use_inner_splices_as_outer_drivers() {
    let fixture = Fixture::new();
    fixture.write("forms.ash", "pub syntax declaration: (leaves) $( row ( $( $inner:ident ),* ) );+ => {\n$(\n$(\npub $inner : Unit -> Int\n$inner () = 1\n)*\n)+\n}\n");
    fixture.write("entry.ash", "import forms (syntax leaves)\nleaves row (first, second); row (); row (third)\nmain : Unit -> Int\nmain () = first(()) + second(()) + third(()) + 39\n");
    let program = compile_path(fixture.configuration()).expect("ragged nested repetitions compile");
    assert_eq!(execute(&program).unwrap().value_display(), "42");
}

#[test]
fn a_group_boundary_stops_a_preceding_expression_capture() {
    let fixture = Fixture::new();
    fixture.write("forms.ash", "pub syntax declaration: (make) $value:expr ( $name:ident ) => {\npub $name : Unit -> Int\n$name () = $value\n}\n");
    fixture.write(
        "entry.ash",
        "import forms (syntax make)\nmake 42 (answer)\nmain : Unit -> Int\nmain () = answer(())\n",
    );
    let program =
        compile_path(fixture.configuration()).expect("the group delimiter stops the expression");
    assert_eq!(execute(&program).unwrap().value_display(), "42");
}

#[test]
fn generated_nested_invocation_keeps_repeated_expression_captures() {
    let fixture = Fixture::new();
    fixture.write("inner.ash", "pub syntax declaration: (inner) $( $name:ident from $value:expr ),+ => {\n$(\npub $name : Unit -> Int\n$name () = $value\n)+\n}\n");
    fixture.write("outer.ash", "import inner (syntax inner)\npub syntax declaration: (outer) $( $name:ident from $value:expr ),+ => {\ninner $( $name from $value ),+\n}\n");
    fixture.write("entry.ash", "import outer (syntax outer)\nouter first from 20, second from 22\nmain : Unit -> Int\nmain () = first(()) + second(())\n");
    let program = compile_path(fixture.configuration())
        .expect("nested generated invocation keeps its repeated captures");
    assert_eq!(execute(&program).unwrap().value_display(), "42");
}

#[test]
fn nullable_matcher_repetitions_preserve_following_capture_stops() {
    let fixture = Fixture::new();
    fixture.write("forms.ash", "pub syntax declaration: (take) $out:ident from $value:expr $( , $unused:ident )* done => {\npub $out : Unit -> Int\n$out () = $value\n}\npub syntax declaration: (many) $( item $out:ident from $value:expr $( , $unused:ident )* done );+ => {\n$(\npub $out : Unit -> Int\n$out () = $value\n)+\n}\n");
    fixture.write("entry.ash", "import forms (syntax take, syntax many)\ntake first from 20 done\nmany item second from 22, ignored done\nmain : Unit -> Int\nmain () = first(()) + second(())\n");
    let program = compile_path(fixture.configuration())
        .expect("nullable repetition and its following literal both stop the capture");
    assert_eq!(execute(&program).unwrap().value_display(), "42");
}

#[test]
fn repeat_follow_checks_use_each_capture_category() {
    let fixture = Fixture::new();
    fixture.write(
        "entry.ash",
        "import forms (syntax sink)\nmain : Unit -> Int\nmain () = 42\n",
    );
    for (matcher, ambiguous) in [
        ("$( $value:expr ),* 1", true),
        ("$( $value:ident ),* 1", false),
        ("$( $value:pattern ),* true", true),
        ("$( $T:type ),* true", false),
        ("$( $T:type ),* tail", false),
        ("$( $value:declaration ),* {}", true),
    ] {
        fixture.write(
            "forms.ash",
            &format!("pub syntax declaration: (sink) {matcher} => {{}}\n"),
        );
        let result = compile_path(fixture.configuration());
        if ambiguous {
            assert_eq!(
                result.expect_err(matcher).reason_code(),
                "parse.matcher-repetition-ambiguous",
                "{matcher}"
            );
        } else {
            let program = result.unwrap_or_else(|failure| panic!("{matcher}: {failure:?}"));
            assert_eq!(execute(&program).unwrap().value_display(), "42");
        }
    }
}

#[test]
fn unused_repeat_body_is_checked_even_when_its_driver_can_be_empty() {
    let fixture = Fixture::new();
    fixture.write(
        "forms.ash",
        "pub syntax declaration: (bad) $( $name:ident ),* => {\n$(\n$name : Unit ->\n)*\n}\n",
    );
    fixture.write(
        "entry.ash",
        "import forms (syntax bad)\nmain : Unit -> Int\nmain () = 42\n",
    );
    let failure =
        compile_path(fixture.configuration()).expect_err("the unused repetition body is malformed");
    assert_eq!(failure.reason_code(), "parse.expected-form", "{failure:?}");
    let diagnostics = ash::presentation::compile_file_diagnostics(&failure).unwrap();
    let mut json = Vec::new();
    ash::presentation::write_json(&mut json, &diagnostics[0]).unwrap();
    let json: serde_json::Value = serde_json::from_slice(&json).unwrap();
    assert!(
        json["labels"][0]["path"]
            .as_str()
            .unwrap()
            .ends_with("forms.ash"),
        "{json}"
    );
}

fn write_nested_repetition_fixture(fixture: &Fixture, depth: usize) {
    let mut matcher = "$name:ident".to_owned();
    let mut argument = "answer".to_owned();
    for index in (0..depth).rev() {
        matcher = format!("$( row_{index} ( {matcher} ) );+");
        argument = format!("row_{index} ( {argument} )");
    }
    let body = format!(
        "{}pub $name : Unit -> Int\n$name () = 42\n{}",
        "$(\n".repeat(depth),
        ")+\n".repeat(depth)
    );
    fixture.write(
        "forms.ash",
        &format!("pub syntax declaration: (rows) {matcher} => {{\n{body}}}\n"),
    );
    fixture.write("entry.ash", &format!("import forms (syntax rows)\nrows {argument}\nmain : Unit -> Int\nmain () = answer(())\n"));
}

#[test]
fn nested_repetition_small_stack_child() {
    if std::env::var_os("ASH_TASK_0068_I19_SMALL_STACK_CHILD").is_none() {
        return;
    }
    std::thread::Builder::new()
        .stack_size(512 * 1024)
        .spawn(|| {
            let fixture = Fixture::new();
            // Admission must also handle a deep, unused matcher on this stack.
            let mut matcher = "$name:ident".to_owned();
            for index in (0..63).rev() {
                matcher = format!("$( row_{index} ( {matcher} ) );+");
            }
            fixture.write(
                "forms.ash",
                &format!("pub syntax declaration: (rows) {matcher} => {{}}\n"),
            );
            fixture.write(
                "entry.ash",
                "import forms (syntax rows)\nmain : Unit -> Int\nmain () = 42\n",
            );
            let unused =
                compile_path(fixture.configuration()).expect("the unused nested matcher compiles");
            drop(unused);
            eprintln!("I19_EMPTY_MATCHER_ADMITTED_AND_DROPPED");
            write_nested_repetition_fixture(&fixture, 63);
            let program =
                compile_path(fixture.configuration()).expect("nested repeated output succeeds");
            assert_eq!(execute(&program).unwrap().value_display(), "42");
            drop(program);
            eprintln!("I19_REPEAT_SMALL_STACK_SUCCESS_AND_DROP");
            write_nested_repetition_fixture(&fixture, 64);
            let failure = compile_path(fixture.configuration())
                .expect_err("nested matcher exceeds structural depth");
            assert_eq!(failure.reason_code(), "internal.resource.structural-depth");
            drop(failure);
            eprintln!("I19_REPEAT_SMALL_STACK_DEPTH_DROP");
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn nested_repetition_success_and_depth_failure_drop_on_a_small_stack() {
    let output = std::process::Command::new(std::env::current_exe().unwrap())
        .args([
            "--exact",
            "nested_repetition_small_stack_child",
            "--nocapture",
        ])
        .env("ASH_TASK_0068_I19_SMALL_STACK_CHILD", "1")
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "{}\n{stdout}\n{stderr}",
        output.status
    );
    for marker in [
        "I19_EMPTY_MATCHER_ADMITTED_AND_DROPPED",
        "I19_REPEAT_SMALL_STACK_SUCCESS_AND_DROP",
        "I19_REPEAT_SMALL_STACK_DEPTH_DROP",
    ] {
        assert!(stderr.contains(marker), "missing {marker}: {stderr}");
        eprintln!("{marker}");
    }
}

#[test]
fn nested_repetition_composed_depth_boundary() {
    std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(|| {
            let fixture = Fixture::new();
            write_nested_repetition_fixture(&fixture, 63);
            let program = compile_path(fixture.configuration())
                .expect("the composed repetition depth at the limit succeeds");
            assert_eq!(execute(&program).unwrap().value_display(), "42");
            drop(program);
            write_nested_repetition_fixture(&fixture, 64);
            let failure = compile_path(fixture.configuration())
                .expect_err("one more matcher level exceeds the structural limit");
            assert_eq!(failure.reason_code(), "internal.resource.structural-depth");
            drop(failure);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn fixed_repetition_failures_keep_their_actual_causes() {
    use ash::{
        message::{Catalogue, Locale},
        presentation::{compile_file_diagnostics, write_human, write_json},
    };
    for (entry, reason, primary_file, relationship, invocation) in [
        (
            "missing_driver_definition.ash",
            "parse.repetition-missing-driver",
            "missing_driver_forms.ash",
            "repetition_missing_driver",
            false,
        ),
        (
            "mismatched.ash",
            "parse.repetition-length-mismatch",
            "mismatched.ash",
            "repetition_length_mismatch",
            true,
        ),
        (
            "empty_plus.ash",
            "parse.matcher-repetition-empty",
            "empty_plus.ash",
            "matcher_repetition_empty",
            true,
        ),
        (
            "trailing_separator.ash",
            "parse.matcher-trailing-separator",
            "trailing_separator.ash",
            "matcher_trailing_separator",
            true,
        ),
        (
            "ambiguous_definition.ash",
            "parse.matcher-repetition-ambiguous",
            "ambiguous_forms.ash",
            "matcher_repetition_ambiguous",
            false,
        ),
    ] {
        let failure = compile_path(captures_fixture(entry)).expect_err(entry);
        assert_eq!(failure.reason_code(), reason, "{entry}: {failure:?}");
        let diagnostics = compile_file_diagnostics(&failure).unwrap();
        let mut human = Vec::new();
        write_human(
            &mut human,
            &diagnostics[0],
            &Catalogue::new(Locale::English).unwrap(),
        )
        .unwrap();
        let human = String::from_utf8(human).unwrap();
        assert!(human.contains(primary_file), "{entry}: {human}");
        let mut json = Vec::new();
        write_json(&mut json, &diagnostics[0]).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&json).unwrap();
        let labels = json["labels"].as_array().unwrap();
        assert_eq!(labels[0]["relationship"], relationship, "{entry}: {json}");
        assert!(
            labels[0]["path"].as_str().unwrap().ends_with(primary_file),
            "{entry}: {json}"
        );
        if invocation {
            assert!(
                labels
                    .iter()
                    .any(|label| label["relationship"] == "syntax_definition"
                        && label["path"]
                            .as_str()
                            .is_some_and(|path| path.ends_with("forms.ash"))),
                "{entry}: {json}"
            );
            assert!(human.contains("forms.ash"), "{entry}: {human}");
        }
        if entry == "trailing_separator.ash" {
            let source =
                include_str!("../docs/design/macros/fixtures/captures/trailing_separator.ash");
            let comma = source.find("first,").unwrap() + "first".len();
            assert_eq!(labels[0]["byte_start"], comma, "{json}");
            assert_eq!(labels[0]["byte_end"], comma + 1, "{json}");
        }
    }
}

#[test]
fn fixed_declaration_capture_rejects_incomplete_and_two_declaration_mutations() {
    let fixture = Fixture::new();
    fixture.write(
        "forms.ash",
        include_str!("../docs/design/macros/fixtures/captures/forms.ash"),
    );
    let original = include_str!("../docs/design/macros/fixtures/captures/main.ash");
    for (label, mutated) in [
        ("incomplete", original.replace("    passed () = 42\n", "")),
        (
            "two declarations",
            original.replace(
                "    passed () = 42\n",
                "    passed () = 42\n    extra : Unit -> Int\n    extra () = 0\n",
            ),
        ),
    ] {
        assert_ne!(mutated, original, "{label}");
        fixture.write("entry.ash", &mutated);
        let failure = compile_path(fixture.configuration()).expect_err(label);
        assert_eq!(
            failure.reason_code(),
            "parse.expected-form",
            "{label}: {failure:?}"
        );
        let syntax = failure.graph_failure().expect("caller parse failure");
        let ash::module::LoadGraphError::Syntax(syntax) = syntax else {
            panic!("{label}: {failure:?}");
        };
        assert!(
            syntax.source.display_path().ends_with("entry.ash"),
            "{label}"
        );
    }
}

#[test]
fn fixed_missing_and_type_capture_failures_keep_parser_and_source_roles() {
    use ash::{
        message::{Catalogue, Locale},
        parser::{ExpectedForm, FoundToken},
        presentation::{compile_file_diagnostics, write_human, write_json},
    };
    let fixture = Fixture::new();
    fixture.write(
        "forms.ash",
        include_str!("../docs/design/macros/fixtures/declarations/forms.ash"),
    );
    let original = include_str!("../docs/design/macros/fixtures/declarations/case_07.ash");
    for (replacement, found) in [
        ("make_identity id for", FoundToken::LineEnd),
        ("make_identity id for 42", FoundToken::Integer),
    ] {
        let entry = original.replace("make_identity id for Int", replacement);
        assert_ne!(entry, original);
        fixture.write("entry.ash", &entry);
        let failure = compile_path(fixture.configuration()).expect_err(replacement);
        assert_eq!(failure.reason_code(), "parse.expected-form");
        let Some(ash::module::LoadGraphError::Syntax(syntax)) = failure.graph_failure() else {
            panic!("{failure:?}");
        };
        assert_eq!(syntax.parser[0].expected_form(), Some(ExpectedForm::Type));
        assert_eq!(syntax.parser[0].found_token(), Some(found));
        let diagnostics = compile_file_diagnostics(&failure).unwrap();
        let mut human = Vec::new();
        write_human(
            &mut human,
            &diagnostics[0],
            &Catalogue::new(Locale::English).unwrap(),
        )
        .unwrap();
        let human = String::from_utf8(human).unwrap();
        assert!(
            human.contains("entry.ash") && human.contains("forms.ash"),
            "{human}"
        );
        let mut json = Vec::new();
        write_json(&mut json, &diagnostics[0]).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&json).unwrap();
        let labels = json["labels"].as_array().unwrap();
        assert!(
            labels[0]["path"].as_str().unwrap().ends_with("entry.ash"),
            "{json}"
        );
        assert!(
            labels
                .iter()
                .any(|label| label["relationship"] == "syntax_definition"
                    && label["path"]
                        .as_str()
                        .is_some_and(|path| path.ends_with("forms.ash"))),
            "{json}"
        );
    }

    let missing = RunConfiguration {
        entry: PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("docs/design/macros/fixtures/diagnostics/missing.ash"),
        roots: ModuleRoots::empty(),
    };
    let failure = compile_path(missing).expect_err("the fixed I15 matcher input is incomplete");
    assert_eq!(failure.reason_code(), "parse.expected-form");
    let diagnostics = compile_file_diagnostics(&failure).unwrap();
    let mut human = Vec::new();
    write_human(
        &mut human,
        &diagnostics[0],
        &Catalogue::new(Locale::English).unwrap(),
    )
    .unwrap();
    let human = String::from_utf8(human).unwrap();
    assert!(
        human.contains("missing.ash") && human.contains("typed_forms.ash"),
        "{human}"
    );
    let mut json = Vec::new();
    write_json(&mut json, &diagnostics[0]).unwrap();
    let json: serde_json::Value = serde_json::from_slice(&json).unwrap();
    let labels = json["labels"].as_array().unwrap();
    assert!(
        labels[0]["path"].as_str().unwrap().ends_with("missing.ash"),
        "{json}"
    );
    assert!(
        labels
            .iter()
            .any(|label| label["relationship"] == "syntax_definition"
                && label["path"]
                    .as_str()
                    .is_some_and(|path| path.ends_with("typed_forms.ash"))),
        "{json}"
    );
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
