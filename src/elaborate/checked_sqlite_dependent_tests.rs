//! Pending dependent OutputAcquire/offset + StatusTeardown carrier controls.
//! Ignored selectors are an explicit future gate, never a passing/skipped gate receipt.
use super::*;

const SOURCE: &str = include_str!("../../libraries/sqlite_checked.ash");
const ENTRY: &str = include_str!("../../tests/fixtures/checked-sqlite/dependent-entry.ash");

#[test]
#[ignore = "pending dependent OutputAcquire/offset, StatusTeardown, and post-consumption Enclosing denial source/Core carriers"]
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
    let (core, provenance) = checked_owner_passive_program_for_source(SOURCE, ENTRY);
    crate::core::source_resource::checked_dependency_tests::assert_statement_core_controls(
        &core,
        &provenance,
    );
    crate::build::checked_owner_dependency_image_controls(
        &core,
        &provenance,
        crate::build::CheckedDependencyStandalone::Fits,
    );
    // Native/runtime admission remains deliberately closed for the same real header.
    crate::foreign::assert_dependent_header_refused_before_entry(parent, child);
}

#[test]
#[ignore = "pending canonical dependent source including post-consumption Enclosing denial; run explicitly with --ignored after common carriers"]
fn checked_sqlite_dependent_source_rejects_wrong_host_suspect_finalize_and_fresh_quarantine() {
    check_graph(&graph_with_entry(SOURCE, Some(ENTRY))).expect("canonical source before mutations");
    for (from, to) in [
        ("output 4 as offset_into(1)", "output 4 as offset_into(0)"),
        ("        retains C", "        retains S"),
    ] {
        assert_eq!(SOURCE.matches(from).count(), 1);
        super::checked_owner_dependency_tests::binding_refuses(&SOURCE.replace(from, to));
    }
    assert_eq!(SOURCE.matches("abi (pointer(Address), pointer(InputAddress), CInt, out(pointer(Address)), out(pointer(InputAddress))) -> CInt").count(), 1);
    let wide_length = SOURCE.replacen("    repr CInt = signed(32)", "    repr CInt = signed(32)\n    repr Wide = signed(64)", 1)
        .replace("abi (pointer(Address), pointer(InputAddress), CInt, out(pointer(Address)), out(pointer(InputAddress))) -> CInt", "abi (pointer(Address), pointer(InputAddress), Wide, out(pointer(Address)), out(pointer(InputAddress))) -> CInt");
    assert_ne!(wide_length, SOURCE);
    super::checked_owner_dependency_tests::binding_refuses(&wide_length);
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
    // Keep the mutant well typed so only Fresh-vs-Enclosing authority can reject it.
    let from = "                        let quarantine : (ConnectionState<H, C>, Foreign.ViolationCause) -> Foreign.CheckedCall<Unit> ! {Foreign.NativeHost<H>} = Foreign.checked_quarantine\n                        let denied = quarantine (enclosing, Foreign.UnexpectedStatus status)";
    let to = "                        let quarantine : (StatementState<H, C, S>, Foreign.ViolationCause) -> Foreign.CheckedCall<Unit> ! {Foreign.NativeHost<H>} = Foreign.checked_quarantine\n                        let denied = quarantine (state, Foreign.UnexpectedStatus status)";
    assert_eq!(SOURCE.matches(from).count(), 1);
    let error = check_graph(&graph_with_entry(&SOURCE.replace(from, to), Some(ENTRY)))
        .expect_err("well-typed Fresh State is not Enclosing quarantine authority");
    assert!(
        matches!(error, TypeError::Source(_)),
        "require source authority refusal, not a type mismatch: {error:?}"
    );
}

#[test]
#[ignore = "pending dependent StatusTeardown, post-consumption Enclosing denial, and canonical source; run explicitly with --ignored"]
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
            "                    let quarantine : (ConnectionState<H, C>, Foreign.ViolationCause) -> Foreign.CheckedCall<Unit> ! {Foreign.NativeHost<H>} = Foreign.checked_quarantine\n                    let denied = quarantine (enclosing, Foreign.UnexpectedStatus status)",
            "                    let quarantine : (StatementState<H, C, S>, Foreign.ViolationCause) -> Foreign.CheckedCall<Unit> ! {Foreign.NativeHost<H>} = Foreign.checked_quarantine\n                    let denied = quarantine (state, Foreign.UnexpectedStatus status)",
        ),
        (
            "                    let denied = quarantine (enclosing, Foreign.UnexpectedStatus status)\n                    Foreign.FinishedConsumed (Foreign.FinishError (FinalizeContradiction status))",
            "                    let denied = quarantine (enclosing, Foreign.UnexpectedStatus status)\n                    let duplicate = perform Finalize<H, C, S>.call state\n                    Foreign.FinishedConsumed (Foreign.FinishError (FinalizeContradiction status))",
        ),
        (
            "Foreign.BoundaryFailed(reason) => Foreign.FinishedBoundary reason",
            "Foreign.BoundaryFailed(reason) => Foreign.FinishedConsumed Foreign.FinishOk",
        ),
        (
            "Foreign.BoundaryFailed(reason) => Foreign.FinishedBoundary reason",
            "Foreign.BoundaryFailed(reason) => {\n                let enclosing = perform ConnectionOps<Connection<H, C>, ConnectionState<H, C>>.borrow connection\n                let quarantine : (ConnectionState<H, C>, Foreign.ViolationCause) -> Foreign.CheckedCall<Unit> ! {Foreign.NativeHost<H>} = Foreign.checked_quarantine\n                let denied = quarantine (enclosing, Foreign.UnexpectedStatus 21)\n                Foreign.FinishedBoundary reason\n            }",
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
            "true => PrepareReject\n                    false => PrepareNativeFailure",
            "true => PrepareNativeFailure\n                    false => PrepareNativeFailure",
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

// Preserve actual nonempty Row arguments around H/C/S rather than specializing
// the admission proof to the minimal fixture's Type-only vector.
#[test]
#[ignore = "pending explicit static gate including complete Row and post-consumption denial carriers"]
fn checked_sqlite_dependent_rows_preserve_full_original_vectors() {
    let mut source = SOURCE.to_owned();
    for (kind, name, args) in [
        ("owner", "ConnectionState", "H, C"),
        ("owner", "StatementState", "H, C, S"),
        ("symbol", "Open", "H, C"),
        ("symbol", "Close", "H, C"),
        ("symbol", "Prepare", "H, C, S"),
        ("symbol", "Finalize", "H, C, S"),
        ("resource", "Connection", "H, C"),
        ("resource", "Statement", "H, C, S"),
    ] {
        let from = format!("{kind} {name}<{args}>");
        assert_eq!(source.matches(&from).count(), 1);
        source = source.replace(
            &from,
            &format!("{kind} {name}<Before : EffectRow, {args}, After : EffectRow>"),
        );
    }
    for (name, args) in [
        ("ConnectionState", "H, C"),
        ("StatementState", "H, C, S"),
        ("Open", "H, C"),
        ("Close", "H, C"),
        ("Prepare", "H, C, S"),
        ("Finalize", "H, C, S"),
        ("Connection", "H, C"),
        ("Statement", "H, C, S"),
    ] {
        source = source.replace(
            &format!("{name}<{args}>"),
            &format!("{name}<{{| Before}}, {args}, {{| After}}>"),
        );
    }
    let entry = ENTRY.replace("import producer as SQLite", "import producer as SQLite\neffect BeforeMark {\n    before_mark : Unit -> Unit\n}\neffect AfterMark {\n    after_mark : Unit -> Unit\n}")
        .replace("SQLite.Connection<H, C>", "SQLite.Connection<{BeforeMark}, H, C, {AfterMark}>")
        .replace("SQLite.Statement<H, C, S>", "SQLite.Statement<{BeforeMark}, H, C, S, {AfterMark}>");
    let (core, provenance) = checked_owner_passive_program_for_source(&source, &entry);
    crate::core::source_resource::checked_dependency_tests::assert_core_controls(
        &core,
        &provenance,
        false,
    );
}
