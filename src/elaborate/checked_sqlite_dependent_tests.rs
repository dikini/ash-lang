//! Pending dependent OutputAcquire/offset + StatusTeardown carrier controls.
//! Ignored selectors are an explicit future gate, never a passing/skipped gate receipt.
use super::*;

const SOURCE: &str = include_str!("../../libraries/sqlite_checked.ash");
const ENTRY: &str = include_str!("../../tests/fixtures/checked-sqlite/dependent-entry.ash");

#[test]
#[ignore = "pending checked dependent OutputAcquire/offset and dependent StatusTeardown source/Core carrier"]
fn checked_sqlite_dependent_source_preserves_original_parent_core_and_transforms() {
    let graph = graph_with_entry(SOURCE, Some(ENTRY));
    let checked =
        check_graph(&graph).expect("future canonical dependent source before any hostile control");
    let producer = checked
        .iter()
        .find(|module| module.source_resource_code().is_some())
        .unwrap();
    let code = producer.source_resource_code().unwrap();
    let parent = code
        .headers()
        .find(|header| header.original.spelling == "Connection")
        .unwrap();
    let child = code
        .headers()
        .find(|header| header.original.spelling == "Statement")
        .unwrap();
    assert_eq!(child.original.host.unwrap().position, 0);
    assert_eq!(child.original.owned_position, 2);
    assert_eq!(
        child.dependencies.as_ref(),
        &[child.original.parameters[1].id]
    );
    assert_eq!(child.owner.owner().retained_parameters(), &[1]);
    assert!(Arc::ptr_eq(
        child.acquire.owner().unwrap(),
        child.teardown.owner().unwrap()
    ));
    assert!(matches!(
        child.acquire.owner_role(),
        Some(
            crate::foreign::source_contract::PreparedOwnerCall::OutputAcquire {
                offset: Some(_),
                ..
            }
        )
    ));
    assert!(matches!(
        child.teardown.owner_role(),
        Some(crate::foreign::source_contract::PreparedOwnerCall::StatusTeardown { .. })
    ));
    assert_eq!(
        child
            .teardown
            .owner_role()
            .unwrap()
            .dispositions()
            .collect::<Vec<_>>(),
        [(true, true)]
    );
    assert_eq!(parent.original.parameters[0].spelling, "H");
    validate_latest_payload_core(&graph);
}

#[test]
#[ignore = "pending canonical dependent source; run explicitly with --ignored after common carriers"]
fn checked_sqlite_dependent_source_rejects_wrong_host_suspect_finalize_and_fresh_quarantine() {
    check_graph(&graph_with_entry(SOURCE, Some(ENTRY))).expect("canonical source before mutations");
    for (from, to) in [
        (
            "    state StatementState<H, C, S>",
            "    state StatementState<H, S, C>",
        ),
        (
            "perform Prepare<H, C, S>.call (enclosing, sql, length)",
            "perform Prepare<S, C, H>.call (enclosing, sql, length)",
        ),
        (
            "                        let denied = quarantine (enclosing, Foreign.UnexpectedStatus status)",
            "let denied = quarantine (state, Foreign.UnexpectedStatus status)",
        ),
        (
            "                        let denied = quarantine (enclosing, Foreign.UnexpectedStatus status)",
            "let denied = perform Finalize<H, C, S>.call state",
        ),
    ] {
        assert_eq!(SOURCE.matches(from).count(), 1);
        let error = check_graph(&graph_with_entry(&SOURCE.replace(from, to), Some(ENTRY)))
            .expect_err("wrong original authority must refuse");
        assert!(
            matches!(error, TypeError::Source(_) | TypeError::Mismatch(_)),
            "semantic refusal, not missing canonical support: {error:?}"
        );
    }
}

#[test]
#[ignore = "pending dependent StatusTeardown + canonical source; run explicitly with --ignored"]
fn checked_sqlite_dependent_finish_rejects_duplicate_and_retained_witnesses() {
    check_graph(&graph_with_entry(SOURCE, Some(ENTRY)))
        .expect("canonical source before finish mutations");
    let (before, statement) = SOURCE
        .split_once("pub resource Statement<H, C, S>")
        .unwrap();
    for (from, to) in [
        (
            "let outcome = perform Finalize<H, C, S>.call state",
            "let duplicate = perform Finalize<H, C, S>.call state\n        let outcome = perform Finalize<H, C, S>.call state",
        ),
        (
            "Foreign.FinishedConsumed (Foreign.FinishError (NativeFinalizeError status))",
            "Foreign.FinishedRetained(state, NativeFinalizeError status)",
        ),
        (
            "Foreign.BoundaryFailed(reason) => Foreign.FinishedBoundary reason",
            "Foreign.BoundaryFailed(reason) => Foreign.FinishedConsumed Foreign.FinishOk",
        ),
    ] {
        assert_eq!(statement.matches(from).count(), 1);
        let changed = format!(
            "{before}pub resource Statement<H, C, S>{}",
            statement.replace(from, to)
        );
        let error = check_graph(&graph_with_entry(&changed, Some(ENTRY)))
            .expect_err("one exact consumed finish witness is mandatory");
        assert!(
            matches!(error, TypeError::Source(_)),
            "semantic finish refusal: {error:?}"
        );
    }
}

#[test]
fn checked_sqlite_dependent_pure_prepare_and_tail_policy_traces() {
    let policy = SOURCE.split_once("pub type OpenPolicy").unwrap().1;
    let source = format!(
        "import @builtin.bytes as B\nimport @builtin.string as Text\npub type OpenPolicy{policy}\n{}",
        include_str!("../../tests/fixtures/checked-sqlite/dependent-policy-traces.ash")
    );
    let entry = "import producer as SQLite\nmain : Unit -> Bool\nmain () = SQLite.dependent_policy_traces ()\n";
    let (core, _) = checked_owner_passive_program_for_source(&source, entry);
    let result =
        crate::eval::evaluate_effect(&core).expect("pure classifiers exercise no native lifecycle");
    assert!(matches!(result.value, crate::eval::Value::Boolean(true)));
    for (from, to) in [
        (
            "false => match nonnull { true => PrepareReject false => PrepareNativeFailure }",
            "false => match nonnull { true => PrepareNativeFailure false => PrepareNativeFailure }",
        ),
        ("B.InvalidIndex => false", "B.InvalidIndex => true"),
    ] {
        assert_eq!(source.matches(from).count(), 1);
        let changed = source.replace(from, to);
        let (core, _) = checked_owner_passive_program_for_source(&changed, entry);
        let result = crate::eval::evaluate_effect(&core).expect("mutated pure classifier trace");
        assert!(matches!(result.value, crate::eval::Value::Boolean(false)));
    }
}
