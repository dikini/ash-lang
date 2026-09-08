use ash::{
    driver::{RunConfiguration, run_path},
    module::ModuleRoots,
    source::SourceFile,
};

fn check(source: &str) -> Result<String, String> {
    let path = std::env::temp_dir().join(format!(
        "ash-cleanup-interactions-{}-{}.ash",
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
fn cleanup_actions_observe_cells_and_registration_closing_order() {
    assert_eq!(
        check(
            r#"import @builtin.cell as Cell
effect Record {
    digit : Int -> Unit
}
effect Adjust {
    publish : Int -> Int
}
visit : Int -> Unit ! {Record, Adjust}
visit depth = resource cell<R> local = depth {
    cleanup fn(ignored) {
        perform Record.digit (perform Adjust.publish 0)
    } {
        register Adjust (fn(value) {
            value + depth
        }) {
            cleanup fn(ignored) {
                let recorded = perform Record.digit (Cell.read local)
                perform Record.digit (perform Adjust.publish 0)
            } {
                ()
            }
        }
    }
}
main : Unit -> Int
main () = resource cell<T> trace = 0 {
    let done = handle (hook Adjust {
        visit 1
    }) with Record {
        digit value => {
            let written = Cell.write (trace, (Cell.read trace) * 10 + value)
            resume ()
        }
    }
    Cell.read trace
}
"#
        ),
        Ok("110".into())
    );
}

#[test]
fn recursive_cleanup_site_has_distinct_overlapping_activations() {
    assert_eq!(
        check(
            r#"import @builtin.cell as Cell
effect Record {
    digit : Int -> Unit
}
visit : Int -> Unit ! {Record}
visit depth = cleanup fn(ignored) {
    perform Record.digit depth
} {
    match depth == 2 {
        true => ()
        false => visit (depth + 1)
    }
}
main : Unit -> Int
main () = resource cell<R> trace = 0 {
    let done = handle (visit 1) with Record {
        digit value => {
            let written = Cell.write (trace, (Cell.read trace) * 10 + value)
            resume ()
        }
    }
    Cell.read trace
}
"#
        ),
        Ok("21".into())
    );
}

#[test]
fn subscriber_abandonment_skips_pending_callbacks_and_removes_registrations() {
    assert_eq!(
        check(
            r#"import @builtin.cell as Cell
effect Adjust {
    publish : Int -> Int
}
effect Stop {
    stop : Unit -> Unit
}
main : Unit -> Int
main () = resource cell<R> trace = 0 {
    hook Adjust {
        let first : Int -> Int ! {Cell.Ops<R>, Stop} = fn(value) {
            let entered = Cell.write (trace, (Cell.read trace) * 10 + 1)
            let stopped = perform Stop.stop ()
            let suffix = Cell.write (trace, (Cell.read trace) * 10 + 8)
            value
        }
        let pending : Int -> Int ! {Cell.Ops<R>} = fn(value) {
            let wrong = Cell.write (trace, (Cell.read trace) * 10 + 9)
            value
        }
        let result = handle (register Adjust first {
            register Adjust pending {
                cleanup fn(ignored) {
                    Cell.write (trace, (Cell.read trace) * 10 + 2)
                } {
                    let published = perform Adjust.publish 5
                    let suffix = Cell.write (trace, (Cell.read trace) * 10 + 6)
                    42
                }
            }
        }) with Stop {
            stop ignored => {
                let done = discard
                let continued = Cell.write (trace, (Cell.read trace) * 10 + 3)
                7
            }
        }
        let later = perform Adjust.publish 5
        result * 10000 + later * 1000 + Cell.read trace
    }
}
"#
        ),
        Ok("75123".into())
    );
}

#[test]
fn removed_cell_override_cannot_fall_back_to_the_live_builtin() {
    let action = "fn(ignored) {\nCell.write (c, (Cell.read c) + 1)\n}";
    let body = "let read = Cell.read c\nlet stopped = perform Stop.stop ()\n42";
    let clauses = "read ignored => resume 41\nwrite ignored => resume ()";
    for (computation, expected) in [
        (
            format!("handle (cleanup {action} {{\n{body}\n}}) with Cell.Ops<R> {{\n{clauses}\n}}"),
            Err("effect.cleanup-context".into()),
        ),
        (
            format!(
                "cleanup {action} {{\nhandle {{\n{body}\n}} with Cell.Ops<R> {{\n{clauses}\n}}\n}}"
            ),
            Ok("72".into()),
        ),
    ] {
        let source = format!(
            r#"import @builtin.cell as Cell
effect Stop {{
    stop : Unit -> Unit
}}
main : Unit -> Int
main () = resource cell<R> c = 1 {{
    let result = handle ({computation}) with Stop {{
        stop ignored => {{
            let done = discard
            7
        }}
    }}
    result * 10 + Cell.read c
}}
"#
        );
        assert_eq!(check(&source), expected, "{source}");
    }
}

#[test]
fn captured_hook_interpreter_is_checked_at_the_action_closing_position() {
    let action = "fn(ignored) {\nlet published = perform Adjust.publish 1\n()\n}";
    let body = "let published = perform Adjust.publish 2\nlet stopped = perform Stop.stop ()\n42";
    for (computation, expected) in [
        (
            format!("hook Adjust {{\ncleanup {action} {{\n{body}\n}}\n}}"),
            Err("effect.cleanup-context".into()),
        ),
        (
            format!("cleanup {action} {{\nhook Adjust {{\n{body}\n}}\n}}"),
            Ok("7".into()),
        ),
    ] {
        let source = format!(
            r#"effect Adjust {{
    publish : Int -> Int
}}
effect Stop {{
    stop : Unit -> Unit
}}
main : Unit -> Int
main () = hook Adjust {{
    handle ({computation}) with Stop {{
        stop ignored => {{
            let done = discard
            7
        }}
    }}
}}
"#
        );
        assert_eq!(check(&source), expected, "{source}");
    }
}

#[test]
fn cleanup_open_callback_row_uses_existing_hook_lacks_authority() {
    for (computation, rows, invocation) in [
        (
            "cleanup action {\n42\n}",
            vec![("Adjust | R", true), ("| R", false)],
            "scoped closed",
        ),
        (
            "handle (cleanup action {\nlet stopped = perform Stop.stop ()\n42\n}) with Stop {\nstop ignored => {\nlet done = discard\n42\n}\n}",
            vec![
                ("Adjust, Stop | R", true),
                ("Adjust | R", false),
                ("Stop | R", false),
            ],
            "handle (scoped closed) with Stop {\nstop ignored => resume ()\n}",
        ),
    ] {
        for (row, admitted) in rows {
            let expected = if admitted {
                Ok("42".into())
            } else {
                Err("effect.row-union-ambiguous".into())
            };
            let source = format!(
                r#"effect Adjust {{
    publish : Int -> Int
}}
effect Stop {{
    stop : Unit -> Unit
}}
scoped<R : EffectRow> : (Unit -> Unit ! {{| R}}) -> Int ! {{{row}}}
scoped action = hook Adjust {{
    {computation}
}}
closed : Unit -> Unit
closed ignored = ()
main : Unit -> Int
main () = hook Adjust {{
    {invocation}
}}
"#
            );
            assert_eq!(check(&source), expected, "{source}");
        }
    }
}
