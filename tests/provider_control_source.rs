//! Public DN-0036 source witnesses for ordinary callbacks and owned control.
//! These programs exercise the selected experiment; they do not define Ash.
use ash::{
    driver::{FileFailure, PipelineFailure, RunConfiguration, run_path_with_foreign_runtime},
    foreign::{ForeignRegistrations, provider_manifest, runtime::ForeignRuntime},
    module::{ForeignRegistrationId, ModuleRoots},
};
use ash_foreign_adapter::sqlite_manifest;
use ash_foreign_adapter::{
    Event, Observations, SqliteFinishFaults, sqlite_binding_with_finish_faults,
};
use std::{
    fs,
    path::{Path, PathBuf},
    sync::{
        Arc,
        atomic::{AtomicU64, Ordering},
    },
};

fn fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/provider-experiments/control-source")
        .join(name)
}

fn execute(
    entry: &Path,
    faults: SqliteFinishFaults,
) -> (Result<String, FileFailure>, Observations, ForeignRuntime) {
    let registrations = ForeignRegistrations::new([
        provider_manifest(ForeignRegistrationId::new(1)).unwrap(),
        sqlite_manifest(ForeignRegistrationId::new(2)).unwrap(),
    ])
    .unwrap();
    let observations = Observations::default();
    let binding = sqlite_binding_with_finish_faults(
        Arc::clone(registrations.get("@foreign.sqlite").unwrap()),
        observations.clone(),
        faults,
    )
    .unwrap();
    let mut runtime = ForeignRuntime::new(vec![binding]).unwrap();
    let result = run_path_with_foreign_runtime(
        RunConfiguration {
            entry: entry.to_path_buf(),
            roots: ModuleRoots::empty().with_foreign_registrations(registrations),
        },
        &mut runtime,
    )
    .map(|observation| observation.value_display());
    (result, observations, runtime)
}

fn real(name: &str) -> (String, Observations, ForeignRuntime) {
    let (result, observations, runtime) = execute(&fixture(name), SqliteFinishFaults::default());
    let value = result.unwrap_or_else(|failure| panic!("{name}: {failure:?}"));
    assert!(
        !observations
            .events()
            .iter()
            .any(|event| matches!(event, Event::FaultInjected { .. }))
    );
    (value, observations, runtime)
}

fn call_position(events: &[Event], name: &str) -> usize {
    events
        .iter()
        .position(|event| {
            matches!(event,
                Event::Call { operation, .. } | Event::Query { operation } if *operation == name,
            )
        })
        .unwrap_or_else(|| panic!("missing actual native observation {name}: {events:?}"))
}

#[test]
fn formal_open_delta_callback_executes_before_resume_under_surviving_handlers() {
    let (value, observations, runtime) = real("callback-open.ash");
    assert_eq!(value, "(Completed(MissingRow, Closed), 42)");
    assert_eq!(observations.calls("open"), 1);
    assert_eq!(observations.calls("close"), 1);
    assert_eq!(runtime.retained_owner_count(), 0);
    // The imported library checks the formal open Delta function, while the
    // concrete caller supplies {J}. The original declaration adds only the
    // written-row exclusion Delta lacks H, never an exclusion of E<C,Delta>.
    let source = fs::read_to_string(fixture("callback_library.ash")).unwrap();
    assert!(source.contains("! {H | Delta}"));
    assert!(source.contains("resource Connection<C, {| Delta}>"));
    assert!(source.contains("let ignored = callback ()\n            resume MissingRow"));
}

#[test]
fn captured_native_scopes_resume_without_reacquisition() {
    let (value, observations, runtime) = real("resume.ash");
    assert_eq!(value, "Completed(Completed(42, Closed), Closed)");
    for operation in ["open", "prepare", "finalize", "close"] {
        assert_eq!(observations.calls(operation), 1, "{operation}");
    }
    assert_eq!(runtime.retained_owner_count(), 0);
}

#[test]
fn curried_global_uses_the_last_consumed_arrow_for_open_resource_actuals() {
    let tree = FixtureCopy::new();
    tree.replace(
        "callback_library.ash",
        "pub client<Delta : EffectRow> : (Unit -> Unit ! {| Delta}) ->",
        "pub client<Delta : EffectRow> : Unit -> (Unit -> Unit ! {| Delta}) ->",
    );
    tree.replace(
        "callback_library.ash",
        "client callback =",
        "client ignored callback =",
    );
    tree.replace(
        "callback-open.ash",
        "Library.client observe",
        "Library.client () observe",
    );
    let (result, observations, runtime) = execute(
        &tree.0.join("callback-open.ash"),
        SqliteFinishFaults::default(),
    );
    assert_eq!(result.unwrap(), "(Completed(MissingRow, Closed), 42)");
    assert_eq!(observations.calls("open"), 1);
    assert_eq!(observations.calls("close"), 1);
    assert_eq!(runtime.retained_owner_count(), 0);
}

#[test]
fn enclosing_result_type_determines_a_no_capture_resource_body_method() {
    let tree = FixtureCopy::new();
    let entry = tree.0.join("outer-result.ash");
    fs::write(
        &entry,
        r#"import @foreign.sqlite as Native
import provider as Provider
import callback_library as Library

interface Make<A> {
make : Unit -> A
}
impl Make<Int> {
make ignored = 42
}

main : Unit -> Provider.Scope<Native.OpenError, Native.CloseError, Int>
main ignored = resource Library.Connection<C, {}> db = Native.InMemory {
make ()
}
"#,
    )
    .unwrap();
    let (result, observations, runtime) = execute(&entry, SqliteFinishFaults::default());
    assert_eq!(result.unwrap(), "Completed(42, Closed)");
    assert_eq!(observations.calls("open"), 1);
    assert_eq!(observations.calls("close"), 1);
    assert_eq!(runtime.retained_owner_count(), 0);
}

#[test]
fn enclosing_tuple_result_determines_a_no_capture_resource_body_function() {
    let tree = FixtureCopy::new();
    let entry = tree.0.join("no-capture-function-context.ash");
    fs::write(
        &entry,
        r#"import @foreign.sqlite as Native
import provider as Provider
import callback_library as Library

main : Unit -> (Provider.Scope<Native.OpenError, Native.CloseError, (Int -> Int)>, Unit)
main ignored = (
resource Library.Connection<C, {}> db = Native.InMemory {
let identity = fn(value) {
value
}
identity
}, {
let identity = fn(value) {
value
}
()
})
"#,
    )
    .unwrap();
    let (result, observations, runtime) = execute(&entry, SqliteFinishFaults::default());
    assert!(result.is_ok(), "{result:?}");
    assert_eq!(observations.calls("open"), 1);
    assert_eq!(observations.calls("close"), 1);
    assert_eq!(runtime.retained_owner_count(), 0);
}

#[test]
fn enclosing_result_types_determine_conditional_capture_resource_body_methods() {
    for tuple in [false, true] {
        let tree = FixtureCopy::new();
        let entry = tree.0.join("capture-outer-result.ash");
        let scope = "Provider.Scope<Native.OpenError, Native.CloseError, Int>";
        let result = if tuple {
            format!("({scope}, Unit)")
        } else {
            scope.to_owned()
        };
        let resource = r#"handle (resource Library.Probe<P> db = Native.InMemory {
let ignored = Library.probe (db, Library.without_owner)
make ()
}) with Library.H {
op ignored => resume ()
}"#;
        let body = if tuple {
            format!("({resource}, ())")
        } else {
            resource.to_owned()
        };
        fs::write(
            &entry,
            format!(
                r#"import @foreign.sqlite as Native
import provider as Provider
import capture_library as Library

interface Make<A> {{
make : Unit -> A
}}
impl Make<Int> {{
make ignored = 42
}}

main : Unit -> {result}
main ignored = {body}
"#
            ),
        )
        .unwrap();
        let (result, observations, runtime) = execute(&entry, SqliteFinishFaults::default());
        assert_eq!(
            result.unwrap(),
            if tuple {
                "(Completed(42, Closed), ())"
            } else {
                "Completed(42, Closed)"
            }
        );
        assert_eq!(observations.calls("open"), 1);
        assert_eq!(observations.calls("close"), 1);
        assert_eq!(runtime.retained_owner_count(), 0);
    }
}

#[test]
fn an_unrelated_function_binding_cannot_close_a_conditional_scope_before_tuple_context() {
    let tree = FixtureCopy::new();
    let entry = tree.0.join("capture-function-binding-context.ash");
    fs::write(
        &entry,
        r#"import @foreign.sqlite as Native
import provider as Provider
import capture_library as Library

main : Unit -> (Provider.Scope<Native.OpenError, Native.CloseError, (Int -> Int)>, Unit)
main ignored = handle (
(resource Library.Probe<P> db = Native.InMemory {
let identity = fn(value) {
value
}
identity
}, {
let identity = fn(value) {
value
}
()
})
) with Library.H {
op ignored => resume ()
}
"#,
    )
    .unwrap();
    let (result, observations, runtime) = execute(&entry, SqliteFinishFaults::default());
    assert!(result.is_ok(), "{result:?}");
    assert_eq!(observations.calls("open"), 1);
    assert_eq!(observations.calls("close"), 1);
    assert_eq!(runtime.retained_owner_count(), 0);
}

#[test]
fn local_annotations_require_the_enclosing_rigid_row_exclusion() {
    for lexical_body in [false, true] {
        for established in [false, true] {
            let tree = FixtureCopy::new();
            let callback_row = if established { "H | Delta" } else { "| Delta" };
            let accepted_body = if lexical_body {
                "newtype Token = Token(Unit)\nwith Run<Token, {| Delta}> {\nrun (token, callback) = callback ()\n}\n()\n"
            } else {
                "()\n"
            };
            let source = format!(
                "effect H {{\nop : Unit -> Unit\n}}\n\
                 interface Run<Key : Type, Rows : EffectRow> {{\n\
                 run : (Key, Unit -> Unit ! {{| Rows}}) -> Unit ! {{H | Rows}}\n}}\n\
                 caller<Delta : EffectRow> : (Unit -> Unit ! {{{callback_row}}}) -> Unit\n\
                 caller callback = {{\n\
                 let accept : (Unit -> Unit ! {{H | Delta}}) -> Unit = fn(accepted) {{\n()\n}}\n\
                 accept (fn(ignored) {{\n{accepted_body}}})\n}}\n\
                 observe : Unit -> Unit ! {{H}}\nobserve () = perform H.op ()\n\
                 main : Unit -> Int\nmain () = {{\nlet ignored = caller observe\n42\n}}\n"
            );
            let entry = tree.0.join("rigid-row-annotation.ash");
            fs::write(&entry, source).unwrap();
            let (result, observations, runtime) = execute(&entry, SqliteFinishFaults::default());
            if established {
                assert_eq!(result.unwrap(), "42");
            } else {
                let failure =
                    result.expect_err("a local annotation cannot strengthen arbitrary rigid Delta");
                assert!(failure.is_source_rejection(), "{failure:?}");
                assert_eq!(failure.reason_code(), "effect.row-exclusion");
                assert!(
                    matches!(failure.pipeline_failure(), Some(PipelineFailure::Typing(_))),
                    "{failure:?}"
                );
            }
            assert_eq!(observations.calls("open"), 0);
            assert_eq!(runtime.retained_owner_count(), 0);
        }
    }
}

#[test]
fn a_bare_local_row_preserves_the_enclosing_declarations_exclusions() {
    let tree = FixtureCopy::new();
    let entry = tree.0.join("established-bare-row.ash");
    fs::write(
        &entry,
        r#"effect H {
op : Unit -> Unit
}
caller<Delta : EffectRow> : (Unit -> Unit ! {| Delta}) -> Unit ! {H | Delta}
caller callback = {
let invoke : Unit -> Unit ! {| Delta} = fn(ignored) {
callback ()
}
()
}
main : Unit -> Int
main () = 42
"#,
    )
    .unwrap();
    let (result, observations, runtime) = execute(&entry, SqliteFinishFaults::default());
    assert_eq!(result.unwrap(), "42");
    assert_eq!(observations.calls("open"), 0);
    assert_eq!(runtime.retained_owner_count(), 0);
}

#[test]
fn nested_lexical_method_resource_actuals_use_the_authenticated_open_owner_row() {
    for missing_lacks in [false, true] {
        let tree = FixtureCopy::new();
        tree.replace("callback_library.ash",
            "pub client<Delta : EffectRow>",
            "pub interface Run<Key : Type, Rows : EffectRow> {\n    run : (Key, Unit -> Unit ! {| Rows}) -> Provider.Scope<Native.OpenError, Native.CloseError, Error> ! {H | Rows}\n}\n\npub client<Delta : EffectRow>");
        tree.replace("callback_library.ash",
            "client callback = resource Connection<C, {| Delta}> db = Native.InMemory {\n    let ignored = perform H.op ()\n    diagnostic (db, callback)\n}\n",
            "client callback = {\n    newtype Token = Token(Unit)\n    with Run<Token, {| Delta}> {\n        run (token, callback) = resource Connection<C, {| Delta}> db = Native.InMemory {\n            let ignored = perform H.op ()\n            diagnostic (db, callback)\n        }\n    }\n    run (Token(()), callback)\n}\n");
        if missing_lacks {
            // Remove the existing written H exclusion from both authenticated
            // rows. No surrounding scheme may supply that absent fact.
            tree.replace("callback_library.ash", "! {H | Rows}", "! {| Rows}");
            tree.replace("callback_library.ash", "! {H | Delta}", "! {| Delta}");
        }
        let (result, observations, runtime) = execute(
            &tree.0.join("callback-open.ash"),
            SqliteFinishFaults::default(),
        );
        if missing_lacks {
            let failure = result
                .expect_err("the lexical method's open row cannot invent its missing H exclusion");
            assert!(failure.is_source_rejection(), "{failure:?}");
            assert_eq!(failure.reason_code(), "effect.row-union-ambiguous");
            assert!(
                matches!(failure.pipeline_failure(), Some(PipelineFailure::Typing(_))),
                "{failure:?}"
            );
            assert_eq!(observations.calls("open"), 0);
        } else {
            assert_eq!(result.unwrap(), "(Completed(MissingRow, Closed), 42)");
            assert_eq!(observations.calls("open"), 1);
            assert_eq!(observations.calls("close"), 1);
        }
        assert_eq!(runtime.retained_owner_count(), 0);
    }
}

#[test]
fn checked_implementation_method_preserves_its_closed_inherited_owner_row() {
    let tree = FixtureCopy::new();
    tree.replace(
        "callback_library.ash",
        "pub client<Delta : EffectRow> : (Unit -> Unit ! {| Delta}) -> Provider.Scope<Native.OpenError, Native.CloseError, Error> ! {H | Delta}\nclient callback = resource Connection<C, {| Delta}> db = Native.InMemory {",
        "pub interface Run<Rows : EffectRow> {\nrun : (Unit -> Unit ! {| Rows}) -> Provider.Scope<Native.OpenError, Native.CloseError, Error> ! {H | Rows}\n}\npub impl Run<{J}> {\nrun callback = resource Connection<C, {J}> db = Native.InMemory {",
    );
    tree.replace(
        "callback_library.ash",
        "diagnostic (db, callback)\n}\n",
        "diagnostic (db, callback)\n}\n}\n",
    );
    tree.replace(
        "callback-open.ash",
        "import callback_library as Library",
        "import callback_library as Library\nimport callback_library (impl Run)",
    );
    tree.replace(
        "callback-open.ash",
        "Library.client observe",
        "Library.run observe",
    );
    let (result, observations, runtime) = execute(
        &tree.0.join("callback-open.ash"),
        SqliteFinishFaults::default(),
    );
    assert_eq!(result.unwrap(), "(Completed(MissingRow, Closed), 42)");
    assert_eq!(observations.calls("open"), 1);
    assert_eq!(observations.calls("close"), 1);
    assert_eq!(runtime.retained_owner_count(), 0);
}

#[test]
fn local_originals_release_a_helper_before_the_next_original_component() {
    let (value, observations, runtime) = real("mixed-local-order.ash");
    assert_eq!(value, "Completed(Completed(Ok(42), Closed), Closed)");
    // Statement's step original calls a helper that opens Connection. The
    // helper needs Connection's originals before Statement can be checked.
    assert_eq!(observations.calls("open"), 3);
    assert_eq!(observations.calls("close"), 3);
    assert_eq!(observations.calls("prepare"), 1);
    assert_eq!(observations.calls("finalize"), 1);
    assert_eq!(observations.calls("step"), 2);
    assert_eq!(runtime.retained_owner_count(), 0);
}

#[test]
fn local_template_preparation_excludes_an_unrelated_unclosed_helper() {
    let (value, observations, runtime) = real("local-order.ash");
    assert_eq!(value, "Completed(Completed(Ok(42), Closed), Closed)");
    // The resource-free unused helper calls the deferred main consumer. It is
    // typed once, excluded from the closed defining component, and retained
    // for the later complete module capture pass.
    for operation in [
        "open",
        "prepare",
        "bind_int64",
        "column_int64",
        "finalize",
        "close",
    ] {
        assert_eq!(observations.calls(operation), 1, "{operation}");
    }
    assert_eq!(observations.calls("step"), 2);
    assert_eq!(runtime.retained_owner_count(), 0);
}

#[test]
fn owned_discard_finishes_structurally_and_cleanup_can_use_the_outer_resource() {
    let (value, observations, runtime) = real("discard.ash");
    // The clause returns its own Int. Neither abandoned 99 nor the outer 88
    // nor an abandoned Scope result reaches the caller.
    assert_eq!(value, "42");
    for operation in ["open", "prepare", "finalize", "close", "errcode", "errmsg"] {
        assert_eq!(observations.calls(operation), 1, "{operation}");
    }
    let events = observations.events();
    assert!(call_position(&events, "errcode") < call_position(&events, "finalize"));
    assert!(call_position(&events, "finalize") < call_position(&events, "close"));
    assert_eq!(runtime.retained_owner_count(), 0);
}

#[test]
fn finite_same_provider_arguments_and_body_row_have_distinct_capture_demands() {
    let (value, observations, runtime) = real("capture-demand.ash");
    assert_eq!(value, "(Completed((MissingRow, MissingRow), Closed), 42)");
    // Both requests use the same live Probe<P> and scalar body remainder {}.
    // One callback's Stop captures an Inner owner with completion demand H;
    // the other's Stop captures none. The single original nested discard port
    // is inside the provider template, and the outer resume returns hidden A.
    let source = fs::read_to_string(fixture("capture_library.ash")).unwrap();
    assert_eq!(source.matches("stop ignored => discard").count(), 1);
    assert!(source.contains("probe (db, with_owner)"));
    assert!(source.contains("probe (db, without_owner)"));
    assert_eq!(observations.calls("open"), 2);
    assert_eq!(observations.calls("close"), 2);
    assert_eq!(runtime.retained_owner_count(), 0);
    // This runtime witness must accompany independent Core checks of exact
    // original-port / per-request input correspondence. Result and native
    // observations alone are not that proof.
}

#[test]
fn genuine_step_failure_preserves_body_error_and_consumed_finalize_error() {
    let (value, observations, runtime) = real("consumed-real.ash");
    assert!(value.contains("StepError(ForeignError("), "{value}");
    assert!(value.contains("ConsumedError(FinalizeFailure("), "{value}");
    assert!(
        value.ends_with(", Closed)"),
        "the connection must still close: {value}"
    );
    let events = observations.events();
    for operation in ["step", "finalize"] {
        assert!(
            events.iter().any(|event| matches!(event,
                Event::Call { operation: actual, code } if *actual == operation && *code != 0,
            )),
            "missing genuine native {operation} failure: {events:?}"
        );
    }
    assert_eq!(observations.calls("finalize"), 1);
    assert_eq!(observations.calls("close"), 1);
    assert_eq!(runtime.retained_owner_count(), 0);
}

#[test]
fn injected_consumed_completion_is_distinct_from_native_failure_and_retention() {
    let (result, observations, runtime) = execute(
        &fixture("completion.ash"),
        SqliteFinishFaults {
            consumed_finalize: true,
            retained_close: false,
        },
    );
    let value = result.unwrap();
    assert!(
        value.contains("Completed(42, ConsumedError(FinalizeFailure("),
        "{value}"
    );
    assert!(value.ends_with(", Closed)"), "{value}");
    assert!(observations.events().contains(&Event::FaultInjected {
        operation: "sqlite3_finalize",
        code: 1
    }));
    assert!(observations.events().contains(&Event::Call {
        operation: "finalize",
        code: 0
    }));
    assert_eq!(observations.calls("finalize"), 1);
    assert_eq!(observations.calls("close"), 1);
    assert_eq!(runtime.retained_owner_count(), 0);
}

#[test]
fn injected_retained_completion_quarantines_the_same_owner_until_host_teardown() {
    let (result, observations, runtime) = execute(
        &fixture("completion.ash"),
        SqliteFinishFaults {
            consumed_finalize: false,
            retained_close: true,
        },
    );
    let value = result.unwrap();
    assert!(
        value.contains("Completed(Completed(42, Closed), RetainedError(CloseFailure("),
        "{value}"
    );
    assert_eq!(runtime.retained_owner_count(), 1);
    assert_eq!(observations.calls("finalize"), 1);
    assert_eq!(
        observations.calls("close"),
        0,
        "no automatic source retry or close_v2 substitution"
    );
    assert!(observations.events().contains(&Event::FaultInjected {
        operation: "sqlite3_close",
        code: 5
    }));
    drop(runtime);
    assert_eq!(
        observations.calls("close"),
        1,
        "safe native host destruction is separate from source completion"
    );
}

struct FixtureCopy(PathBuf);
impl FixtureCopy {
    fn new() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "ash-provider-control-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        for entry in fs::read_dir(fixture("")).unwrap() {
            let entry = entry.unwrap();
            fs::copy(entry.path(), path.join(entry.file_name())).unwrap();
        }
        Self(path)
    }
    fn replace(&self, name: &str, before: &str, after: &str) {
        let path = self.0.join(name);
        let source = fs::read_to_string(&path).unwrap();
        assert!(
            source.contains(before),
            "source mutation must reach its intended site"
        );
        fs::write(path, source.replacen(before, after, 1)).unwrap();
    }
}
impl Drop for FixtureCopy {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn open_callback_union_does_not_invent_a_missing_lacks_condition() {
    let tree = FixtureCopy::new();
    tree.replace("callback_library.ash", "! {H | Delta}", "! {| Delta}");
    let (result, observations, runtime) = execute(
        &tree.0.join("callback-open.ash"),
        SqliteFinishFaults::default(),
    );
    let failure =
        result.expect_err("Delta without its written H exclusion cannot justify union with H");
    assert!(failure.is_source_rejection(), "{failure:?}");
    assert_eq!(failure.reason_code(), "effect.row-union-ambiguous");
    assert!(
        matches!(failure.pipeline_failure(), Some(PipelineFailure::Typing(_))),
        "{failure:?}"
    );
    assert_eq!(observations.calls("open"), 0);
    assert_eq!(runtime.retained_owner_count(), 0);
}

#[test]
fn removed_ordinary_provider_override_cannot_replace_the_exact_resource_interpreter() {
    let action = "fn(ignored) {\nlet diagnostic = Sqlite.diagnostic db\n()\n}";
    let body = "let diagnostic = Sqlite.diagnostic db\nlet ignored = perform Stop.stop ()\n99";
    let clauses = "diagnostic ignored => resume Sqlite.MissingRow";
    for (computation, accepted) in [
        (
            format!(
                "handle (cleanup {action} {{\n{body}\n}}) with Sqlite.ConnectionOps<C> {{\n{clauses}\n}}"
            ),
            false,
        ),
        (
            format!(
                "cleanup {action} {{\nhandle {{\n{body}\n}} with Sqlite.ConnectionOps<C> {{\n{clauses}\n}}\n}}"
            ),
            true,
        ),
    ] {
        let tree = FixtureCopy::new();
        let source = format!(
            "import sqlite as Sqlite\neffect Stop {{\nstop : Unit -> Unit\n}}\nmain : Unit -> Int\nmain () = handle {{\nlet abandoned = resource Sqlite.Connection<C> db = (Sqlite.memory ()) {{\n{computation}\n}}\n88\n}} with Stop {{\nstop ignored => {{\nlet ignored = discard\n42\n}}\n}}\n"
        );
        fs::write(tree.0.join("ordinary-override.ash"), &source).unwrap();
        let (result, observations, runtime) = execute(
            &tree.0.join("ordinary-override.ash"),
            SqliteFinishFaults::default(),
        );
        if accepted {
            assert_eq!(result.unwrap(), "42", "{source}");
            for operation in ["open", "errcode", "errmsg", "close"] {
                assert_eq!(observations.calls(operation), 1, "{operation}: {source}");
            }
            assert!(
                call_position(&observations.events(), "errcode")
                    < call_position(&observations.events(), "close")
            );
        } else {
            let failure =
                result.expect_err("the nearer removed ordinary override blocks cleanup fallback");
            assert!(failure.is_source_rejection(), "{failure:?}");
            assert_eq!(
                failure.reason_code(),
                "effect.cleanup-context",
                "{source}: {failure:?}"
            );
            assert_eq!(observations.calls("open"), 0);
            assert_eq!(observations.calls("close"), 0);
            assert_eq!(observations.calls("errcode"), 0);
        }
        assert_eq!(runtime.retained_owner_count(), 0);
    }
}

#[test]
fn repeated_same_source_provider_discard_closes_each_actual_activation_once() {
    let tree = FixtureCopy::new();
    fs::write(tree.0.join("repeated-discard.ash"), "import sqlite as Sqlite\neffect Stop {\nstop : Unit -> Unit\n}\nclient : Unit -> Int\nclient () = handle {\nlet abandoned = resource Sqlite.Connection<C> db = (Sqlite.memory ()) {\ncleanup fn(ignored) {\nlet diagnostic = Sqlite.diagnostic db\n()\n} {\nlet ignored = perform Stop.stop ()\n99\n}\n}\n88\n} with Stop {\nstop ignored => {\nlet ignored = discard\n42\n}\n}\nmain : Unit -> Int\nmain () = {\nlet first = client ()\nlet second = client ()\nfirst + second\n}\n").unwrap();
    let (result, observations, runtime) = execute(
        &tree.0.join("repeated-discard.ash"),
        SqliteFinishFaults::default(),
    );
    assert_eq!(result.unwrap(), "84");
    for operation in ["open", "errcode", "errmsg", "close"] {
        assert_eq!(observations.calls(operation), 2, "{operation}");
    }
    let events = observations.events();
    let position = |name| {
        events.iter().enumerate().filter_map(|(index, event)| {
        matches!(event, Event::Call { operation, .. } | Event::Query { operation } if *operation == name).then_some(index)
    }).collect::<Vec<_>>()
    };
    let opens = position("open");
    let diagnostics = position("errcode");
    let closes = position("close");
    assert!(opens[0] < diagnostics[0] && diagnostics[0] < closes[0]);
    assert!(closes[0] < opens[1] && opens[1] < diagnostics[1] && diagnostics[1] < closes[1]);
    assert_eq!(runtime.retained_owner_count(), 0);
}

#[test]
fn resource_dependent_access_cannot_leave_its_lexical_scope() {
    let tree = FixtureCopy::new();
    fs::write(tree.0.join("escape.ash"), "import sqlite as Sqlite\nmain : Unit -> Unit\nmain () = {\nlet escaped = resource Sqlite.Connection<C> db = (Sqlite.memory ()) {\ndb\n}\n()\n}\n").unwrap();
    let (result, observations, runtime) =
        execute(&tree.0.join("escape.ash"), SqliteFinishFaults::default());
    let failure = result
        .expect_err("even an ignored result cannot carry the fresh identity out of its scope");
    assert!(failure.is_source_rejection(), "{failure:?}");
    assert!(
        matches!(failure.pipeline_failure(), Some(PipelineFailure::Typing(_))),
        "{failure:?}"
    );
    assert_eq!(observations.calls("open"), 0);
    assert_eq!(runtime.retained_owner_count(), 0);
}
