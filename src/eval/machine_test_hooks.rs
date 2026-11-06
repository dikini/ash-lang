//! Test-only generic machine storage/refusal observations.
use std::cell::Cell;

std::thread_local! {
    pub(crate) static FAIL_DISPOSAL_GROWTH: Cell<bool> = const { Cell::new(false) };
    pub(crate) static FAIL_CONTROL_RESERVATION: Cell<Option<crate::eval::ResourceFailureCause>> = const { Cell::new(None) };
    pub(crate) static ROOT_CLOSES: Cell<usize> = const { Cell::new(0) };
    pub(crate) static FAIL_ROOT_CLOSE: Cell<bool> = const { Cell::new(false) };
}

pub(crate) fn reset() {
    FAIL_DISPOSAL_GROWTH.set(false);
    FAIL_CONTROL_RESERVATION.set(None);
    ROOT_CLOSES.set(0);
    FAIL_ROOT_CLOSE.set(false);
}
