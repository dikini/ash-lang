//! Test-only generic machine storage/refusal observations.
use std::cell::Cell;

std::thread_local! {
    pub(crate) static FAIL_DISPOSAL_GROWTH: Cell<bool> = const { Cell::new(false) };
    pub(crate) static FAIL_CONTROL_RESERVATION: Cell<Option<crate::eval::ResourceFailureCause>> = const { Cell::new(None) };
    pub(crate) static ROOT_CLOSES: Cell<usize> = const { Cell::new(0) };
    pub(crate) static FAIL_ROOT_CLOSE: Cell<bool> = const { Cell::new(false) };
    pub(crate) static TRANSFORMER_DROPS: Cell<usize> = const { Cell::new(0) };
    pub(crate) static ACTIVE_ROOT_DROPS: Cell<usize> = const { Cell::new(0) };
    pub(crate) static ACTIVE_ROOT_RECORDS: Cell<usize> = const { Cell::new(0) };
    pub(crate) static SYNTAX_REQUESTS: Cell<usize> = const { Cell::new(0) };
    pub(crate) static TRANSFER_ATTEMPTS: Cell<usize> = const { Cell::new(0) };
    pub(crate) static TRANSFER_FAILURES: Cell<usize> = const { Cell::new(0) };
    pub(crate) static TRANSFER_GROUPS_COMPLETED: Cell<usize> = const { Cell::new(0) };
}

pub(crate) fn reset() {
    FAIL_DISPOSAL_GROWTH.set(false);
    FAIL_CONTROL_RESERVATION.set(None);
    ROOT_CLOSES.set(0);
    FAIL_ROOT_CLOSE.set(false);
    TRANSFORMER_DROPS.set(0);
    ACTIVE_ROOT_DROPS.set(0);
    ACTIVE_ROOT_RECORDS.set(0);
    SYNTAX_REQUESTS.set(0);
    TRANSFER_ATTEMPTS.set(0);
    TRANSFER_FAILURES.set(0);
    TRANSFER_GROUPS_COMPLETED.set(0);
}
