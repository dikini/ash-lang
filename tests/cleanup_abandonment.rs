use ash::{
    driver::{RunConfiguration, run_path},
    module::ModuleRoots,
    source::SourceFile,
};

fn check(source: &str) -> Result<String, String> {
    let path = std::env::temp_dir().join(format!(
        "ash-cleanup-abandonment-{}-{}.ash",
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

const FAILURE_REPORT: &str = r#"type Outcome<T, P> = Success(T)
| Failed(P)
type CloseResult<E> = Closed
| CloseFailed(E)
type Failures<E> = NoFailures
| FailureItem(E, Failures<E>)
type Report<A, E> = Report(A, Failures<E>)

effect CleanupFailure<E> {
    report : E -> Unit
}
effect Stop {
    stop : Int -> Unit
}

reportClose<E> : CloseResult<E> -> Unit ! {CleanupFailure<E>}
reportClose result = match result {
    Closed => ()
    CloseFailed(error) => perform CleanupFailure<E>.report error
}

outer : Unit -> Unit ! {CleanupFailure<Int>}
outer ignored = reportClose (CloseFailed 11)
inner : Unit -> Unit ! {CleanupFailure<Int>}
inner ignored = reportClose (CloseFailed 22)

main : Unit -> Int
main () = {
    let observed : Report<Outcome<Int, Int>, Int> = handle {
        let outcome : Outcome<Int, Int> = handle (cleanup outer {
            cleanup inner {
                let ignored = perform Stop.stop 7
                Success 42
            }
        }) with Stop {
            stop primary => {
                let done = discard
                Failed primary
            }
        }
        Report(outcome, NoFailures)
    } with CleanupFailure<Int> {
        report error => match (resume ()) {
            Report(outcome, errors) => Report(outcome, FailureItem(error, errors))
        }
    }
    match observed {
        Report(Failed(primary), FailureItem(first, FailureItem(second, NoFailures))) => primary * 10000 + first * 100 + second
        _ => 0
    }
}
"#;

#[test]
fn exact_proposal_reports_inner_then_outer_and_preserves_primary() {
    assert_eq!(check(FAILURE_REPORT), Ok("72211".into()));
}

#[test]
fn opaque_body_cannot_hide_cleanup_that_needs_its_removed_handler() {
    let source = r#"effect H {
    ask : Unit -> Unit
}
effect B {
    ask : Unit -> Unit
}
run : (Unit -> Unit ! {H}) -> Unit
run action = handle (handle (action ()) with H {
    ask ignored => {
        let requested = perform B.ask ()
        resume ()
    }
}) with B {
    ask ignored => discard
}
action : Unit -> Unit ! {H}
action ignored = cleanup fn(ignored) {
    perform H.ask ()
} {
    perform H.ask ()
}
main : Unit -> Unit
main () = run action
"#;
    assert_eq!(check(source), Err("effect.row-union-ambiguous".into()));
    let source = source
        .replace(
            "run : (Unit -> Unit ! {H}) -> Unit",
            "run : (Unit -> Unit ! {H}) -> Unit ! {H}",
        )
        .replace(
            "main () = run action",
            "main () = handle (run action) with H {\nask ignored => resume ()\n}",
        );
    let result = check(&source);
    assert!(
        matches!(&result, Err(error) if matches!(error.as_str(), "effect.cleanup-context" | "effect.discard-unsafe")),
        "{result:?}"
    );
}

#[test]
fn imported_and_local_discard_node_indices_do_not_share_row_authority() {
    let directory = std::env::temp_dir().join(format!(
        "ash-cleanup-import-{}-{}",
        std::process::id(),
        SourceFile::new("cleanup", "").unwrap().id().value()
    ));
    std::fs::create_dir(&directory).unwrap();
    let declarations = r#"pub effect Log {
    log : Unit -> Unit
}
effect Stop {
    stop : Unit -> Unit
}
pub run : Unit -> Int ! {Log}
run ignored = handle (cleanup fn(ignored) {
    perform Log.log ()
} {
    let stopped = perform Stop.stop ()
    42
}) with Stop {
    stop ignored => {
        let done = discard
        7
    }
}
"#;
    let library = directory.join("library.ash");
    let entry = directory.join("main.ash");
    std::fs::write(&library, declarations).unwrap();
    std::fs::write(
        &entry,
        format!(
            "import library as Lib\n{declarations}{}",
            r#"main : Unit -> Int
main () = {
    let first = handle (Lib.run ()) with Lib.Log {
        log ignored => resume ()
    }
    let second = handle (run ()) with Log {
        log ignored => resume ()
    }
    first + second
}
"#
        ),
    )
    .unwrap();
    let result = run_path(RunConfiguration {
        entry: entry.clone(),
        roots: ModuleRoots::empty(),
    });
    std::fs::remove_file(entry).unwrap();
    std::fs::remove_file(library).unwrap();
    std::fs::remove_dir(directory).unwrap();
    assert_eq!(
        result
            .map(|value| value.value_display())
            .map_err(|error| error.reason_code()),
        Ok("14".into())
    );
}

#[test]
fn returned_generic_closure_checks_opaque_capture_after_solving_its_lexical_row() {
    assert_eq!(
        check(
            r#"effect Log<T> {
    log : T -> Unit
}
effect Stop {
    stop : Unit -> Unit
}
make<T> : ((Unit -> Int ! {Stop}), (Unit -> Unit ! {Log<T>})) -> (Unit -> Int ! {Log<T>})
make (body, action) = fn(ignored) {
    handle (cleanup action {
        body ()
    }) with Stop {
        stop ignored => {
            let done = discard
            7
        }
    }
}
body : Unit -> Int ! {Stop}
body ignored = {
    let stopped = perform Stop.stop ()
    42
}
main : Unit -> Int
main () = {
    let logInt : Unit -> Unit ! {Log<Int>} = fn(ignored) {
        perform Log<Int>.log 1
    }
    let logBool : Unit -> Unit ! {Log<Bool>} = fn(ignored) {
        perform Log<Bool>.log true
    }
    let first = make (body, logInt)
    let second = make (body, logBool)
    let a = handle (first ()) with Log<Int> {
        log value => resume ()
    }
    let b = handle (second ()) with Log<Bool> {
        log value => resume ()
    }
    a + b
}
"#
        ),
        Err("effect.discard-unsafe".into())
    );
}

#[test]
fn one_generic_discard_keeps_its_lexical_row_at_two_instantiations() {
    assert_eq!(
        check(
            r#"effect Log<T> {
    log : T -> Unit
}
effect Stop {
    stop : Unit -> Unit
}
run<T> : T -> Int ! {Log<T>}
run value = handle (cleanup fn(ignored) {
    perform Log<T>.log value
} {
    let stopped = perform Stop.stop ()
    42
}) with Stop {
    stop ignored => {
        let done = discard
        7
    }
}
main : Unit -> Int
main () = {
    let first = handle (run 1) with Log<Int> {
        log value => resume ()
    }
    let second = handle (run true) with Log<Bool> {
        log value => resume ()
    }
    first + second
}
"#
        ),
        Ok("14".into())
    );
}

#[test]
fn owned_cell_and_unused_registration_close_before_clause_continues() {
    for body in [
        "resource cell<R> c = 42 {\nperform Stop.stop ()\n}",
        "register Adjust identity {\nperform Stop.stop ()\n}",
    ] {
        assert_eq!(
            check(&format!(
                "import @builtin.cell as Cell\neffect Adjust {{\npublish : Int -> Int\n}}\neffect Stop {{\nstop : Unit -> Unit\n}}\nidentity : Int -> Int\nidentity value = value\nmain : Unit -> Int\nmain () = hook Adjust {{\nlet ignored = handle ({body}) with Stop {{\nstop ignored => {{\nlet done = discard\n()\n}}\n}}\n42\n}}\n"
            )),
            Ok("42".into())
        );
    }
}

#[test]
fn owned_cleanup_uses_retained_cell_and_skips_body_suffix() {
    assert_eq!(
        check(
            "import @builtin.cell as Cell\neffect Stop {\nstop : Unit -> Unit\n}\nmain : Unit -> Int\nmain () = resource cell<R> trace = 0 {\nlet result = handle (cleanup fn(ignored) {\nCell.write (trace, (Cell.read trace) * 10 + 2)\n} {\nlet ignored = perform Stop.stop ()\nlet ignored = Cell.write (trace, 9)\n42\n}) with Stop {\nstop ignored => {\nlet done = discard\nlet written = Cell.write (trace, (Cell.read trace) * 10 + 3)\n7\n}\n}\nCell.read trace\n}\n"
        ),
        Ok("23".into())
    );
}

#[test]
fn removed_handler_compatibility_depends_on_action_closing_position() {
    let prefix = "effect Stop {\nstop : Unit -> Unit\n}\neffect Log {\nlog : Unit -> Unit\n}\naction : Unit -> Unit ! {Log}\naction ignored = perform Log.log ()\nmain : Unit -> Int\nmain () = handle {\nlet logged = perform Log.log ()\nhandle (";
    let suffix = ") with Stop {\nstop ignored => {\nlet done = discard\n7\n}\n}\n} with Log {\nlog ignored => resume ()\n}\n";
    let removed = "handle (cleanup action {\nlet ignored = perform Stop.stop ()\n42\n}) with Log {\nlog ignored => (resume ()) + 1\n}";
    assert_eq!(
        check(&format!("{prefix}{removed}{suffix}")),
        Err("effect.cleanup-context".into())
    );
    let passed = "cleanup action {\nhandle {\nlet ignored = perform Log.log ()\nlet ignored = perform Stop.stop ()\n42\n} with Log {\nlog ignored => (resume ()) + 1\n}\n}";
    assert_eq!(check(&format!("{prefix}{passed}{suffix}")), Ok("7".into()));
}

#[test]
fn restored_structural_order_precedes_later_acquisition_time() {
    for completion in ["resume ()", "{\nlet done = discard\n7\n}"] {
        let source = format!(
            "import @builtin.cell as Cell\neffect A {{\nask : Unit -> Unit\n}}\neffect Stop {{\nstop : Unit -> Unit\n}}\nmain : Unit -> Int\nmain () = resource cell<R> trace = 0 {{\nlet result = handle (handle (cleanup fn(ignored) {{\nCell.write (trace, (Cell.read trace) * 10 + 1)\n}} {{\nlet a = perform A.ask ()\nlet stopped = perform Stop.stop ()\n42\n}}) with A {{\nask ignored => cleanup fn(ignored) {{\nCell.write (trace, (Cell.read trace) * 10 + 2)\n}} {{\nresume ()\n}}\n}}) with Stop {{\nstop ignored => {completion}\n}}\nCell.read trace\n}}\n"
        );
        assert_eq!(check(&source), Ok("12".into()), "{source}");
    }
}

#[test]
fn live_nested_capture_closes_at_its_clause_without_clause_suffix() {
    assert_eq!(
        check(
            "import @builtin.cell as Cell\neffect A {\nask : Unit -> Unit\n}\neffect B {\nask : Unit -> Unit\n}\nmain : Unit -> Int\nmain () = resource cell<R> trace = 0 {\nlet result = handle (handle (cleanup fn(ignored) {\nCell.write (trace, (Cell.read trace) * 10 + 1)\n} {\nlet a = perform A.ask ()\n42\n}) with A {\nask ignored => cleanup fn(ignored) {\nCell.write (trace, (Cell.read trace) * 10 + 2)\n} {\nlet b = perform B.ask ()\nlet resumed = resume ()\nlet wrong = Cell.write (trace, 9)\nresumed\n}\n}) with B {\nask ignored => {\nlet done = discard\n7\n}\n}\nCell.read trace\n}\n"
        ),
        Ok("21".into())
    );
}

#[test]
fn clause_local_handler_checks_discard_effects_through_forward_and_recursive_helpers() {
    let mut results = Vec::new();
    for helper in [
        "work ignored = cleanup action {\nlet stopped = perform Stop.stop ()\n42\n}",
        "work again = cleanup action {\nmatch again {\ntrue => work false\nfalse => {\nlet stopped = perform Stop.stop ()\n42\n}\n}\n}",
    ] {
        let source = format!(
            "effect Log {{\nlog : Unit -> Unit\n}}\neffect Stop {{\nstop : Unit -> Unit\n}}\naction : Unit -> Unit ! {{Log}}\naction ignored = perform Log.log ()\nmain : Unit -> Int\nmain () = handle (handle (work true) with Stop {{\nstop ignored => {{\nlet done = handle (discard) with Log {{\nlog ignored => resume ()\n}}\n7\n}}\n}}) with Log {{\nlog ignored => resume ()\n}}\nwork : Bool -> Int ! {{Log, Stop}}\n{helper}\n"
        );
        results.push((check(&source), source));
    }
    for (result, source) in results {
        assert_eq!(result, Ok("7".into()), "{source}");
    }
}
