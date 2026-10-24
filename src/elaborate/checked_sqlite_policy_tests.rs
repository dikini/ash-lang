//! Source-only library controls. These tests do not execute SQLite or arena native code.
use super::*;

const SQLITE: &str = include_str!("../../libraries/sqlite_checked.ash");
// Exact independent producer from reviewed df39297d, separate from pending dependent admission.
const CONNECTION: &str = include_str!("../../tests/fixtures/checked-sqlite/connection-source.ash");
const ARENA: &str = include_str!("../../libraries/arena_checked.ash");

#[test]
fn checked_connection_source_links_core_identity_and_fold() {
    let entry = r#"import @builtin.foreign as Foreign
import producer as SQLite
main : Unit -> Foreign.CheckedScope<Int, SQLite.InitError, SQLite.CloseError>
main () = foreign host H {
    match perform SQLite.Initialize<H>.call () {
        Foreign.CheckedReturned(status) => match status == 0 {
            true => resource SQLite.Connection<H, C> connection = ":memory:" {
                SQLite.open_status connection
            }
            false => Foreign.CheckedNotAcquired (SQLite.NativeOpenError status)
        }
        Foreign.CheckedConversionFailed(error) => Foreign.CheckedNotAcquired (SQLite.OpenConversion error)
        Foreign.BoundaryFailed(reason) => Foreign.CheckedNotAcquired (SQLite.OpenBoundary reason)
    }
}
"#;
    let graph = graph_with_entry(CONNECTION, Some(entry));
    let checked = check_graph(&graph).expect("real Connection source and body-free consumer");
    let producer = checked
        .iter()
        .find(|module| module.source_resource_code().is_some())
        .unwrap();
    let code = producer.source_resource_code().unwrap();
    let header = code.headers().next().unwrap();
    assert!(header.dependencies.is_empty());
    assert!(matches!(
        header.acquire.owner_role(),
        Some(
            crate::foreign::source_contract::PreparedOwnerCall::OutputAcquire { offset: None, .. }
        )
    ));
    assert!(matches!(
        header.teardown.owner_role(),
        Some(crate::foreign::source_contract::PreparedOwnerCall::StatusTeardown { .. })
    ));
    assert!(Arc::ptr_eq(
        header.acquire.owner().unwrap(),
        header.teardown.owner().unwrap()
    ));
    validate_latest_payload_core(&graph);
}

#[test]
fn checked_arena_source_links_core_identity_and_fold() {
    let graph = graph_with_entry(
        ARENA,
        Some(
            "import @builtin.foreign as Foreign\nimport producer as Arena\nmain : Unit -> Foreign.CheckedScope<Int, Arena.InitError, Arena.FinishError>\nmain () = foreign host H {\n    resource Arena.Arena<H, R> arena = 8 {\n        Arena.capacity arena\n    }\n}\n",
        ),
    );
    check_graph(&graph).expect("actual contrasting arena resource");
    validate_latest_payload_core(&graph);
    let original = "let outcome = perform Free<H, R>.call state";
    assert_eq!(ARENA.matches(original).count(), 1);
    let duplicate = ARENA.replace(original, "let second = perform Free<H, R>.call state\n        let outcome = perform Free<H, R>.call state");
    let error = check_graph(&super::graph(&duplicate, false))
        .expect_err("once-Finish rejects repeated native teardown");
    assert!(
        matches!(error, TypeError::Source(_)),
        "semantic once-Finish refusal: {error:?}"
    );
}

#[test]
fn checked_connection_finish_rejects_switched_disposition_and_boundary() {
    check_graph(&graph(CONNECTION, false))
        .expect("preserved independent producer before hostile controls");
    let (before, connection) = CONNECTION
        .split_once("pub resource Connection<H, C>")
        .unwrap();
    let (connection, after) = connection
        .split_once("pub type OpenPolicy")
        .unwrap();
    for (from, to) in [
        (
            "                let reject : Foreign.ViolationCause -> Foreign.CheckedCall<Unit> ! {Foreign.NativeHost<H>} = Foreign.checked_reject_acquisition\n                let denied = reject (Foreign.UnexpectedStatus status)",
            "                let denied = Foreign.checked_quarantine (state, Foreign.UnexpectedStatus status)",
        ),
        (
            "Foreign.CheckedReturned(Foreign.Retained(status)) => Foreign.FinishedRetained(state, NativeCloseError status)",
            "Foreign.CheckedReturned(Foreign.Retained(status)) => Foreign.FinishedConsumed Foreign.FinishOk",
        ),
        (
            "Foreign.BoundaryFailed(reason) => Foreign.FinishedBoundary reason",
            "Foreign.BoundaryFailed(reason) => Foreign.FinishedConsumed Foreign.FinishOk",
        ),
    ] {
        assert_eq!(connection.matches(from).count(), 1);
        let changed = format!(
            "{before}pub resource Connection<H, C>{}pub type OpenPolicy{after}",
            connection.replace(from, to)
        );
        let error = check_graph(&graph(&changed, false))
            .expect_err("source authority rejects Fresh quarantine or a different finish witness");
        assert!(
            matches!(error, TypeError::Source(_)),
            "semantic refusal: {error:?}"
        );
    }
}

#[test]
fn checked_policy_trace_is_ordinary_source_without_native_authority() {
    // Extract the actual pure policy section rather than reimplementing the transition model in Rust.
    let policy = SQLITE.split_once("pub type OpenPolicy").unwrap().1;
    let source = format!(
        "import @builtin.foreign as Foreign\nimport @builtin.bytes as B\nimport @builtin.string as Text\npub type OpenPolicy{policy}\n{}",
        include_str!("../../tests/fixtures/checked-sqlite/policy-traces.ash")
    );
    let entry =
        "import producer as SQLite\nmain : Unit -> Bool\nmain () = SQLite.policy_traces ()\n";
    let (core, _) = checked_owner_passive_program_for_source(&source, entry);
    let result = crate::eval::evaluate_effect(&core).expect("ordinary policy trace evaluation");
    assert!(
        matches!(result.value, crate::eval::Value::Boolean(true)),
        "policy trace must reach its expected independent coordinates"
    );
    // Mutations demonstrate that traces observe B, pre-entry preservation, and loss independently.
    for (from, to) in [
        (
            "ReturnedStatus(_) => Policy(Prepared, bindings, availability)",
            "ReturnedStatus(_) => Policy(Prepared, Known, availability)",
        ),
        (
            "PreEntryRefused => Policy(execution, bindings, availability)",
            "PreEntryRefused => Policy(Prepared, Known, availability)",
        ),
        (
            "BoundaryLost => Policy(execution, bindings, Unavailable)",
            "BoundaryLost => Policy(execution, bindings, Usable)",
        ),
    ] {
        let changed = source.replace(from, to);
        assert_ne!(source, changed);
        let (core, _) = checked_owner_passive_program_for_source(&changed, entry);
        let result =
            crate::eval::evaluate_effect(&core).expect("mutated ordinary policy evaluation");
        assert!(matches!(result.value, crate::eval::Value::Boolean(false)));
    }
}

#[test]
fn checked_statement_tail_policy_rejects_actual_negative_and_outside_offsets() {
    let policy = SQLITE.split_once("pub type OpenPolicy").unwrap().1;
    let source = format!("import @builtin.foreign as Foreign\nimport @builtin.bytes as B\nimport @builtin.string as Text\npub foreign library Offsets {{\n profile \"x86_64-unknown-linux-gnu\"\n repr Signed = signed(64)\n const Negative : Signed = -1\n}}\npub negative_offset : Unit -> Int\nnegative_offset () = Offsets.Negative\npub type OpenPolicy{policy}\n");
    for (offset, expected) in [(-1, false), (0, false), (9, true), (10, true), (11, false)] {
        // Signed foreign constants already admit negative values. The ordinary
        // helper supplies an actual negative Int without extending expression grammar.
        let offset = if offset < 0 { "SQLite.negative_offset ()".to_owned() } else { offset.to_string() };
        let entry = format!("import producer as SQLite\nmain : Unit -> Bool\nmain () = SQLite.valid_tail (\"SELECT 1; \", {offset})\n");
        let (core, _) = checked_owner_passive_program_for_source(&source, &entry);
        let result = crate::eval::evaluate_effect(&core).unwrap();
        assert!(matches!(result.value, crate::eval::Value::Boolean(actual) if actual == expected));
    }
}
