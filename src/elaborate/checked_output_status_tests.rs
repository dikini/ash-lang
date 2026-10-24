//! Genuine independent output/status source; no native execution or library policy claim.
use super::*;

const SOURCE: &str = include_str!("../../tests/fixtures/checked-owner-lifecycle/output-status.ash");

#[test]
fn independent_output_status_preserves_originals_through_link_core_and_transforms() {
    let graph = graph(SOURCE, true);
    let checked = check_graph(&graph).expect("genuine independent output/status source");
    let producer = checked.iter().find(|module| module.source_resource_code().is_some()).unwrap();
    let code = producer.source_resource_code().unwrap();
    let header = code.headers().next().unwrap();
    assert!(header.dependencies.is_empty());
    assert!(matches!(header.acquire.owner_role(), Some(crate::foreign::source_contract::PreparedOwnerCall::OutputAcquire { offset: None, .. })));
    assert!(matches!(header.teardown.owner_role(), Some(crate::foreign::source_contract::PreparedOwnerCall::StatusTeardown { .. })));
    assert!(Arc::ptr_eq(header.acquire.owner().unwrap(), header.teardown.owner().unwrap()));
    assert_eq!(header.teardown.owner_role().unwrap().dispositions().collect::<Vec<_>>(), [(true, true), (false, true)]);
    validate_latest_payload_core(&graph);
}

#[test]
fn independent_status_finish_cannot_swap_disposition_or_boundary_lineage() {
    check_graph(&graph(SOURCE, false)).expect("canonical source before hostile finish controls");
    for (from, to) in [
        ("Foreign.CheckedReturned(Foreign.Retained(status)) => Foreign.FinishedRetained(state, ())", "Foreign.CheckedReturned(Foreign.Retained(status)) => Foreign.FinishedConsumed Foreign.FinishOk"),
        ("Foreign.CheckedReturned(Foreign.Consumed(status)) => Foreign.FinishedConsumed Foreign.FinishOk", "Foreign.CheckedReturned(Foreign.Consumed(status)) => Foreign.FinishedRetained(state, ())"),
        ("Foreign.BoundaryFailed(reason) => Foreign.FinishedBoundary reason", "Foreign.BoundaryFailed(reason) => Foreign.FinishedRetained(state, ())"),
    ] {
        assert_eq!(SOURCE.matches(from).count(), 1);
        let error = check_graph(&graph(&SOURCE.replace(from, to), false)).expect_err("exact request-specific finish relation must reject mutation");
        assert!(matches!(error, TypeError::Source(_)), "semantic refusal, not setup/resource failure: {error:?}");
    }
}
