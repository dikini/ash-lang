//! Test-only generic machine storage/refusal observations.
use std::cell::Cell;

std::thread_local! {
    pub(crate) static FAIL_DISPOSAL_GROWTH: Cell<bool> = const { Cell::new(false) };
    pub(crate) static FAIL_CONTROL_RESERVATION: Cell<Option<crate::eval::ResourceFailureCause>> = const { Cell::new(None) };
}

pub(crate) fn reset() {
    FAIL_DISPOSAL_GROWTH.set(false);
    FAIL_CONTROL_RESERVATION.set(None);
}
