use ash::{
    driver::{RunConfiguration, run_path},
    module::ModuleRoots,
    source::SourceFile,
};

fn check(source: &str) -> Result<String, String> {
    let path = std::env::temp_dir().join(format!(
        "ash-cleanup-{}-{}.ash",
        std::process::id(),
        SourceFile::new("cleanup", "").unwrap().id().value()
    ));
    std::fs::write(&path, source).unwrap();
    let result = run_path(RunConfiguration {
        entry: path.clone(),
        roots: ModuleRoots::empty(),
    });
    std::fs::remove_file(path).unwrap();
    result
        .map(|value| value.value_display())
        .map_err(|error| error.reason_code())
}

#[test]
fn initialization_once_inner_before_outer_and_saved_body_value() {
    assert_eq!(
        check(
            r#"import @builtin.cell as Cell
main : Unit -> Int
main () = resource cell<R> trace = 0 {
    let result = cleanup ({
        let ignored = Cell.write (trace, 1)
        fn(ignored) {
            Cell.write (trace, (Cell.read trace) * 10 + 3)
        }
    }) {
        cleanup fn(ignored) {
            Cell.write (trace, (Cell.read trace) * 10 + 2)
        } {
            42
        }
    }
    result * 1000 + Cell.read trace
}
"#
        ),
        Ok("42123".into())
    );
}

#[test]
fn callback_domain_and_result_use_ordinary_type_errors() {
    for (ty, parameter, body) in [
        ("Int -> Unit", "value", "()"),
        ("Unit -> Int", "ignored", "42"),
    ] {
        let source = format!(
            "action : {ty}\naction {parameter} = {body}\nmain : Unit -> Int\nmain () = cleanup action {{\n42\n}}\n"
        );
        assert_eq!(check(&source), Err("type.mismatch".into()));
    }
}

#[test]
fn action_local_reporting_handler_completes() {
    assert_eq!(
        check(
            "effect Report {\nreport : Int -> Unit\n}\nmain : Unit -> Int\nmain () = cleanup fn(ignored) {\nhandle (perform Report.report 7) with Report {\nreport error => resume ()\n}\n} {\n42\n}\n"
        ),
        Ok("42".into())
    );
}

#[test]
fn saved_result_cannot_export_a_cell_capture() {
    assert_eq!(
        check(
            "import @builtin.cell as Cell\nmain : Unit -> (Unit -> Int)\nmain () = resource cell<R> c = 42 {\ncleanup fn(ignored) {\n()\n} {\nlet escaped : Unit -> Int = fn(ignored) {\nlet held = c\n42\n}\nescaped\n}\n}\n"
        ),
        Err("type.resource-escape".into())
    );
}

#[test]
fn body_local_handler_does_not_discharge_cleanup_effects() {
    assert_eq!(
        check(
            "effect Report {\nreport : Int -> Unit\n}\naction : Unit -> Unit ! {Report}\naction ignored = perform Report.report 7\nmain : Unit -> Int\nmain () = cleanup action {\nhandle {\nlet ignored = perform Report.report 0\n42\n} with Report {\nreport error => resume ()\n}\n}\n"
        ),
        Err("effect.row-union-ambiguous".into())
    );
}

#[test]
fn armed_and_running_cleanup_cannot_be_abandoned_yet() {
    for source in [
        "effect Stop {\nstop : Unit -> Unit\n}\nmain : Unit -> Int\nmain () = handle (cleanup fn(ignored) {\n()\n} {\nlet ignored = perform Stop.stop ()\n42\n}) with Stop {\nstop ignored => {\nlet done = discard\n42\n}\n}\n",
        "effect Stop {\nstop : Unit -> Unit\n}\nmain : Unit -> Int\nmain () = handle (cleanup fn(ignored) {\nperform Stop.stop ()\n} {\n42\n}) with Stop {\nstop ignored => {\nlet done = discard\n42\n}\n}\n",
    ] {
        assert_eq!(
            check(source),
            Err("effect.discard-unsafe".into()),
            "{source}"
        );
    }
}

#[test]
fn action_local_discard_preserves_running_completion() {
    assert_eq!(
        check(
            "effect Stop {\nstop : Unit -> Unit\n}\nmain : Unit -> Int\nmain () = cleanup fn(ignored) {\nhandle (perform Stop.stop ()) with Stop {\nstop ignored => discard\n}\n} {\n42\n}\n"
        ),
        Ok("42".into())
    );
}

#[test]
fn contextual_match_action_infers_latent_effects() {
    assert_eq!(
        check(
            "effect Report {\nreport : Int -> Unit\n}\nmain : Unit -> Int\nmain () = handle (cleanup (match true {\ntrue => fn(ignored) {\nperform Report.report 1\n}\nfalse => fn(ignored) {\nperform Report.report 2\n}\n}) {\n42\n}) with Report {\nreport error => resume ()\n}\n"
        ),
        Ok("42".into())
    );
}

#[test]
fn contextual_match_action_unions_pure_and_effectful_anonymous_branches() {
    let mut results = Vec::new();
    for (first, second) in [
        ("()", "perform Report.report 1"),
        ("perform Report.report 1", "()"),
    ] {
        let source = format!(
            "effect Report {{\nreport : Int -> Unit\n}}\nmain : Unit -> Int\nmain () = handle (cleanup (match true {{\ntrue => fn(ignored) {{\n{first}\n}}\nfalse => fn(ignored) {{\n{second}\n}}\n}}) {{\n42\n}}) with Report {{\nreport error => resume ()\n}}\n"
        );
        let annotated = source
            .replace(
                "handle (cleanup (match",
                "handle ({\nlet chosen : Unit -> Unit ! {Report} = match",
            )
            .replace("}) {\n42\n}) with", "}\ncleanup chosen {\n42\n}\n}) with");
        assert_eq!(check(&annotated), Ok("42".into()), "{annotated}");
        results.push(check(&source));
    }
    assert_eq!(results, vec![Ok("42".into()), Ok("42".into())]);
}

#[test]
fn named_action_alternatives_keep_invariant_latent_rows() {
    for (first, second) in [("pure", "reporting"), ("reporting", "pure")] {
        let source = format!(
            "effect Report {{\nreport : Int -> Unit\n}}\npure : Unit -> Unit\npure () = ()\nreporting : Unit -> Unit ! {{Report}}\nreporting () = perform Report.report 1\nmain : Unit -> Int\nmain () = handle (cleanup (match true {{\ntrue => {first}\nfalse => {second}\n}}) {{\n42\n}}) with Report {{\nreport error => resume ()\n}}\n"
        );
        assert_eq!(check(&source), Err("type.mismatch".into()), "{source}");
    }
}

#[test]
fn action_context_does_not_collect_unrelated_function_bodies() {
    assert_eq!(
        check(
            "effect Report {\nreport : Int -> Unit\n}\nmain : Unit -> Int\nmain () = cleanup {\nlet unrelated : Unit -> Unit ! {Report} = fn(ignored) {\nperform Report.report 1\n}\nfn(ignored) {\n()\n}\n} {\n42\n}\n"
        ),
        Ok("42".into())
    );
}

#[test]
fn captures_resume_armed_and_running_cleanup_in_structural_order() {
    assert_eq!(
        check(
            r#"import @builtin.cell as Cell
effect Pause {
pause : Unit -> Unit
}
main : Unit -> Int
main () = resource cell<R> trace = 0 {
    let result = handle (cleanup fn(ignored) {
        let paused = perform Pause.pause ()
        Cell.write (trace, (Cell.read trace) * 10 + 2)
    } {
        let paused = perform Pause.pause ()
        Cell.write (trace, 1)
    }) with Pause {
        pause ignored => resume ()
    }
    Cell.read trace
}
"#
        ),
        Ok("12".into())
    );
}

#[test]
fn reports_preserve_saved_body_and_emission_order() {
    assert_eq!(
        check(
            r#"type Failures = None
| Item(Int, Failures)
type Report = Report(Int, Failures)
effect Failure {
report : Int -> Unit
}

outer : Unit -> Unit ! {Failure}
outer ignored = perform Failure.report 11
inner : Unit -> Unit ! {Failure}
inner ignored = perform Failure.report 22
main : Unit -> Int
main () = {
    let result = handle {
        let body = cleanup outer {
            cleanup inner {
                42
            }
        }
        Report(body, None)
    } with Failure {
        report error => match (resume ()) {
            Report(body, errors) => Report(body, Item(error, errors))
        }
    }
    match result {
        Report(body, Item(first, Item(second, None))) => body * 10000 + first * 100 + second
        _ => 0
    }
}
"#
        ),
        Ok("422211".into())
    );
}

#[test]
fn reported_error_cannot_export_an_action_cell_capture() {
    assert_eq!(
        check(
            "import @builtin.cell as Cell\neffect Report {\nreport : (Unit -> Int) -> Unit\n}\nmain : Unit -> Int\nmain () = handle (resource cell<R> c = 42 {\ncleanup fn(ignored) {\nlet saved : Unit -> Int = fn(ignored) {\nlet held = c\n42\n}\nperform Report.report saved\n} {\n42\n}\n}) with Report {\nreport error => resume ()\n}\n"
        ),
        Err("type.resource-escape".into())
    );
}
