//! Conditional DN-0036 SQLite control drafts, pending verified common control integration.
//! These cases assert candidate outcomes; they are not evidence of a passing run.

#[path = "support/sqlite_copying.rs"]
mod sqlite_copying_support;

use ash_foreign_adapter::{Event, Observations};
use sqlite_copying_support::{Fixture, assert_closed_probe, copied_sizes};

fn position(observations: &Observations, operation: &str) -> usize {
    observations
        .events()
        .iter()
        .position(|event| {
            matches!(event, Event::Call { operation: name, .. } | Event::Query { operation: name } if *name == operation)
        })
        .unwrap_or_else(|| panic!("missing native observation {operation}"))
}

fn assert_source_finish_once(observations: &Observations) {
    let events = observations.events();
    for operation in ["finalize", "close"] {
        assert_eq!(observations.calls(operation), 1, "{operation}");
        assert!(events.contains(&Event::Call { operation, code: 0 }));
    }
    assert!(position(observations, "finalize") < position(observations, "close"));
    assert_eq!(observations.calls("close_v2"), 0);
}

#[test]
fn captured_statement_and_connection_resume_actual_copied_query_without_reacquisition() {
    let fixture = Fixture::new();
    let (value, observations) = fixture.run("control-resume.ash");
    assert_eq!(
        value,
        "Completed(Completed(Ok(CopiedRow(TextValue(\"héllo 世界\"), BlobBytes([0, 255]))), Closed), Closed)"
    );
    assert_closed_probe(&observations, 2);
    assert_source_finish_once(&observations);
    assert_eq!(observations.calls("column_text"), 1);
    assert_eq!(observations.calls("column_blob"), 1);
    assert_eq!(copied_sizes(&observations), (vec![], vec![13, 2]));
    assert!(position(&observations, "prepare") < position(&observations, "step"));
    assert!(position(&observations, "column_blob") < position(&observations, "finalize"));
}

#[test]
fn owned_discard_runs_source_cleanup_then_statement_finish_before_connection_close() {
    let fixture = Fixture::new();
    let (value, observations) = fixture.run("control-discard.ash");
    // Discard supplies the clause's Int, with no abandoned body or fabricated Scope.
    assert_eq!(value, "42");
    assert_closed_probe(&observations, 0);
    assert_source_finish_once(&observations);
    for operation in ["errcode", "errmsg"] {
        assert_eq!(observations.calls(operation), 1, "{operation}");
        assert!(position(&observations, operation) < position(&observations, "finalize"));
    }
    assert_eq!(observations.calls("column_text"), 0);
    assert_eq!(observations.calls("column_blob"), 0);
    assert_eq!(copied_sizes(&observations), (vec![], vec![]));
    // The actual diagnostic comes from source cleanup while the outer access is live.
    // Native host destruction does not execute that Ash cleanup. Fixture::run also
    // checks an empty quarantine before host runtime teardown and forbids injected faults.
    // assert_closed_probe requires authenticated binding finish dispatches, which
    // native guard destruction does not emit.
}
