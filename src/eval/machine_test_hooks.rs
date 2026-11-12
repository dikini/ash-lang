//! Test-only generic machine storage/refusal observations.
use std::cell::Cell;

type TransformerEvaluationObserver =
    fn(&crate::core::validate::ValidatedMacroEntry, &super::Evaluation);
type IdentifierCaptureObserver = fn(usize, &mut super::Value);

std::thread_local! {
    pub(crate) static TRANSFORMER_EVALUATION_OBSERVER: Cell<Option<TransformerEvaluationObserver>> = const { Cell::new(None) };
    pub(crate) static IDENTIFIER_CAPTURE_OBSERVER: Cell<Option<IdentifierCaptureObserver>> = const { Cell::new(None) };
    pub(crate) static FAIL_DISPOSAL_GROWTH: Cell<bool> = const { Cell::new(false) };
    pub(crate) static FAIL_CONTROL_RESERVATION: Cell<Option<crate::eval::ResourceFailureCause>> = const { Cell::new(None) };
    pub(crate) static ROOT_CLOSES: Cell<usize> = const { Cell::new(0) };
    pub(crate) static FAIL_ROOT_CLOSE: Cell<bool> = const { Cell::new(false) };
    pub(crate) static TRANSFORMER_DROPS: Cell<usize> = const { Cell::new(0) };
    pub(crate) static ACTIVE_ROOT_DROPS: Cell<usize> = const { Cell::new(0) };
    pub(crate) static ACTIVE_ROOT_RECORDS: Cell<usize> = const { Cell::new(0) };
    pub(crate) static SYNTAX_REQUESTS: Cell<usize> = const { Cell::new(0) };
    pub(crate) static QUOTE_REACHES: Cell<usize> = const { Cell::new(0) };
    pub(crate) static QUOTE_COMPLETIONS: Cell<usize> = const { Cell::new(0) };
    pub(crate) static FIRST_QUOTE_COMPLETION_WORK: Cell<Option<usize>> = const { Cell::new(None) };
    pub(crate) static TRANSFER_ATTEMPTS: Cell<usize> = const { Cell::new(0) };
    pub(crate) static TRANSFER_FAILURES: Cell<usize> = const { Cell::new(0) };
    pub(crate) static TRANSFER_GROUPS_COMPLETED: Cell<usize> = const { Cell::new(0) };
    pub(crate) static DECLARATION_CAPTURES: Cell<usize> = const { Cell::new(0) };
    pub(crate) static DECLARATION_UNWRAPS: Cell<usize> = const { Cell::new(0) };
    pub(crate) static DECLARATION_TRANSFERS_BEFORE_DROP: Cell<usize> = const { Cell::new(0) };
    pub(crate) static SCALAR_LEX_STARTS: Cell<usize> = const { Cell::new(0) };
    pub(crate) static SCALAR_UTF8_SCANS: Cell<usize> = const { Cell::new(0) };
}

pub(crate) fn reset() {
    TRANSFORMER_EVALUATION_OBSERVER.set(None);
    IDENTIFIER_CAPTURE_OBSERVER.set(None);
    FAIL_DISPOSAL_GROWTH.set(false);
    FAIL_CONTROL_RESERVATION.set(None);
    ROOT_CLOSES.set(0);
    FAIL_ROOT_CLOSE.set(false);
    TRANSFORMER_DROPS.set(0);
    ACTIVE_ROOT_DROPS.set(0);
    ACTIVE_ROOT_RECORDS.set(0);
    SYNTAX_REQUESTS.set(0);
    QUOTE_REACHES.set(0);
    QUOTE_COMPLETIONS.set(0);
    FIRST_QUOTE_COMPLETION_WORK.set(None);
    TRANSFER_ATTEMPTS.set(0);
    TRANSFER_FAILURES.set(0);
    TRANSFER_GROUPS_COMPLETED.set(0);
    DECLARATION_CAPTURES.set(0);
    DECLARATION_UNWRAPS.set(0);
    DECLARATION_TRANSFERS_BEFORE_DROP.set(0);
    SCALAR_LEX_STARTS.set(0);
    SCALAR_UTF8_SCANS.set(0);
}
