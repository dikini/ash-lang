use super::checked_wrapper_tests::{WRAPPER_SOURCE, authenticate, wrapper_summary_from_source};
use super::*;

fn selected_summary() -> ExportSummary {
    wrapper_summary_from_source(&format!(
        "{}{}",
        WRAPPER_SOURCE.replace("pub closed", "closed"),
        r#"pub interface Read<A> {
    read : A -> Foreign.CheckedCall<Int>
}
pub impl Read<Int> {
    read value = closed value
}
"#
    ))
}

#[test]
fn checked_selected_method_control_retains_native_assumptions() {
    let summary = selected_summary();
    authenticate(&summary).unwrap();
    assert_eq!(summary.implementations.len(), 1);
    assert_eq!(summary.implementations[0].fact.methods.len(), 1);
    assert_eq!(summary.native_symbols.len(), 1);
    assert!(
        summary.terms.is_empty(),
        "only selected method reaches native work"
    );
    assert!(
        summary
            .requires_checked_foreign_profile(&mut TypeWorkBudget::unbounded())
            .unwrap()
    );
    let symbol = summary.native_symbols.values().next().unwrap();
    assert!(
        !symbol.prepared().checked_contract().unwrap().symbols()[0]
            .minimum_assumptions()
            .is_empty()
    );
}

#[test]
fn checked_selected_method_rejects_capture_erasure() {
    let mut summary = selected_summary();
    authenticate(&summary).unwrap();
    summary.implementations[0].fact.methods[0].capture =
        crate::core::capture::CaptureValueSummary::default();
    assert!(
        authenticate(&summary).is_err(),
        "selected method capture erasure was accepted"
    );
}

#[test]
fn checked_selected_method_rejects_coordinated_capture_and_native_erasure() {
    let mut summary = selected_summary();
    authenticate(&summary).unwrap();
    summary.implementations[0].fact.methods[0].capture =
        crate::core::capture::CaptureValueSummary::default();
    summary.native_symbols.clear();
    summary
        .effects
        .retain(|effect| effect.native_contract.is_none());
    summary.effect_positions = summary
        .effects
        .iter()
        .enumerate()
        .map(|(index, effect)| (effect.id, index))
        .collect();
    assert!(
        authenticate(&summary).is_err(),
        "coordinated selected method closure erasure was accepted"
    );
}
