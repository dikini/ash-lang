use ash::{
    driver::{RunConfiguration, run_path},
    module::ModuleRoots,
    source::SourceFile,
};

fn check(source: &str) -> Result<String, String> {
    let path = std::env::temp_dir().join(format!(
        "ash-cleanup-reporting-{}-{}.ash",
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

const PROTOCOL: &str = r#"type CloseResult<E> = Closed
| CloseFailed(E)
type Failures<E> = NoFailures
| FailureItem(E, Failures<E>)
type Report<A, E> = Report(A, Failures<E>)
effect CleanupFailure<E> {
    report : E -> Unit
}
reportClose<E> : CloseResult<E> -> Unit ! {CleanupFailure<E>}
reportClose result = match result {
    Closed => ()
    CloseFailed(error) => perform CleanupFailure<E>.report error
}
"#;

#[test]
fn closed_action_preserves_body_without_errors() {
    assert_eq!(
        check(&format!(
            "{PROTOCOL}{}",
            r#"
action : Unit -> Unit ! {CleanupFailure<Int>}
action ignored = {
    let result : CloseResult<Int> = Closed
    reportClose result
}
main : Unit -> Int
main () = {
    let observed : Report<Int, Int> = handle {
        let body = cleanup action {
            42
        }
        Report(body, NoFailures)
    } with CleanupFailure<Int> {
        report error => match (resume ()) {
            Report(body, errors) => Report(body, FailureItem(error, errors))
        }
    }
    match observed {
        Report(body, NoFailures) => body
        _ => 0
    }
}
"#
        )),
        Ok("42".into())
    );
}

#[test]
fn ignored_close_failure_is_not_implicitly_reported() {
    assert_eq!(
        check(&format!(
            "{PROTOCOL}{}",
            r#"
main : Unit -> Int
main () = cleanup fn(ignored) {
    let ignored = CloseFailed 7
    ()
} {
    42
}
"#
        )),
        Ok("42".into())
    );
}

#[test]
fn reporting_failure_does_not_retry_action() {
    assert_eq!(
        check(&format!(
            "import @builtin.cell as Cell\n{PROTOCOL}{}",
            r#"
main : Unit -> Int
main () = resource cell<R> attempts = 0 {
    let observed : Report<Int, Int> = handle {
        let body = cleanup fn(ignored) {
            let counted = Cell.write (attempts, (Cell.read attempts) + 1)
            reportClose (CloseFailed 7)
        } {
            42
        }
        Report(body, NoFailures)
    } with CleanupFailure<Int> {
        report error => match (resume ()) {
            Report(body, errors) => Report(body, FailureItem(error, errors))
        }
    }
    match observed {
        Report(body, FailureItem(error, NoFailures)) => body * 1000 + error * 10 + Cell.read attempts
        _ => 0
    }
}
"#
        )),
        Ok("42071".into())
    );
}

#[test]
fn application_primary_and_cleanup_errors_keep_distinct_types() {
    assert_eq!(
        check(&format!(
            "{PROTOCOL}{}",
            r#"
type Primary = Primary(Bool)
type CloseError = CloseError(Int)
type Outcome = Failed(Primary)
effect Stop {
    stop : Primary -> Unit
}
main : Unit -> Int
main () = {
    let observed : Report<Outcome, CloseError> = handle {
        let body = handle (cleanup fn(ignored) {
            reportClose (CloseFailed (CloseError 9))
        } {
            let stopped = perform Stop.stop (Primary true)
            Failed (Primary false)
        }) with Stop {
            stop primary => {
                let done = discard
                Failed primary
            }
        }
        Report(body, NoFailures)
    } with CleanupFailure<CloseError> {
        report error => match (resume ()) {
            Report(body, errors) => Report(body, FailureItem(error, errors))
        }
    }
    match observed {
        Report(Failed(Primary(true)), FailureItem(CloseError(error), NoFailures)) => error
        _ => 0
    }
}
"#
        )),
        Ok("9".into())
    );
}

#[test]
fn explicit_sum_collects_distinct_cleanup_errors() {
    assert_eq!(
        check(&format!(
            "{PROTOCOL}{}",
            r#"
type CloseError = FileError(Int)
| SocketError(Bool)
main : Unit -> Int
main () = {
    let observed : Report<Int, CloseError> = handle {
        let body = cleanup fn(ignored) {
            reportClose (CloseFailed (FileError 3))
        } {
            cleanup fn(ignored) {
                reportClose (CloseFailed (SocketError true))
            } {
                42
            }
        }
        Report(body, NoFailures)
    } with CleanupFailure<CloseError> {
        report error => match (resume ()) {
            Report(body, errors) => Report(body, FailureItem(error, errors))
        }
    }
    match observed {
        Report(body, FailureItem(SocketError(true), FailureItem(FileError(error), NoFailures))) => body + error
        _ => 0
    }
}
"#
        )),
        Ok("45".into())
    );
}

#[test]
fn independent_typed_collectors_survive_abandonment() {
    assert_eq!(
        check(&format!(
            "{PROTOCOL}{}",
            r#"
effect Stop {
    stop : Unit -> Unit
}
main : Unit -> Int
main () = {
    let observed : Report<Report<Int, Int>, Bool> = handle {
        let integers : Report<Int, Int> = handle {
            let body = handle (cleanup fn(ignored) {
                reportClose (CloseFailed 3)
            } {
                cleanup fn(ignored) {
                    reportClose (CloseFailed true)
                } {
                    let stopped = perform Stop.stop ()
                    42
                }
            }) with Stop {
                stop ignored => {
                    let done = discard
                    7
                }
            }
            Report(body, NoFailures)
        } with CleanupFailure<Int> {
            report error => match (resume ()) {
                Report(body, errors) => Report(body, FailureItem(error, errors))
            }
        }
        Report(integers, NoFailures)
    } with CleanupFailure<Bool> {
        report error => match (resume ()) {
            Report(body, errors) => Report(body, FailureItem(error, errors))
        }
    }
    match observed {
        Report(Report(body, FailureItem(error, NoFailures)), FailureItem(true, NoFailures)) => body * 10 + error
        _ => 0
    }
}
"#
        )),
        Ok("73".into())
    );
}

#[test]
fn abortive_report_handler_cannot_skip_running_cleanup_or_drain() {
    for abandoned in [false, true] {
        let body = if abandoned {
            "let stopped = perform Stop.stop ()\n42"
        } else {
            "42"
        };
        let cleanup = format!(
            r#"cleanup fn(ignored) {{
    ()
}} {{
    cleanup fn(ignored) {{
        reportClose (CloseFailed 7)
    }} {{
        {body}
    }}
}}"#
        );
        let computation = if abandoned {
            format!(
                r#"handle ({cleanup}) with Stop {{
    stop ignored => {{
        let done = discard
        9
    }}
}}"#
            )
        } else {
            cleanup
        };
        let source = format!(
            r#"{PROTOCOL}
effect Stop {{
    stop : Unit -> Unit
}}
main : Unit -> Int
main () = handle ({computation}) with CleanupFailure<Int> {{
    report error => {{
        let done = discard
        0
    }}
}}
"#
        );
        assert_eq!(
            check(&source),
            Err("effect.discard-unsafe".into()),
            "{source}"
        );
    }
}

#[test]
fn abandoned_cleanup_cannot_report_cell_capture_outside_owner() {
    assert_eq!(
        check(
            r#"import @builtin.cell as Cell
effect Report {
    report : (Unit -> Int) -> Unit
}
effect Stop {
    stop : Unit -> Unit
}
main : Unit -> Int
main () = handle (handle (resource cell<R> c = 42 {
    cleanup fn(ignored) {
        let saved : Unit -> Int = fn(ignored) {
            let held = c
            42
        }
        perform Report.report saved
    } {
        let stopped = perform Stop.stop ()
        42
    }
}) with Stop {
    stop ignored => {
        let done = discard
        7
    }
}) with Report {
    report error => resume ()
}
"#
        ),
        Err("type.resource-escape".into())
    );
}
