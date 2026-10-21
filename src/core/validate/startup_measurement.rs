//! Opt-in, current-thread startup measurements for the bounded reproducer only.
//!
//! These events never supply validation authority or alter charged work. Call
//! `reset` immediately before reconstruction and `snapshot` before reporting its
//! Result, including on failure. Snapshot disables recording on this thread.

use std::cell::RefCell;

#[derive(Clone, Debug)]
pub(crate) struct Event {
    pub(crate) stage: &'static str,
    pub(crate) before: usize,
    pub(crate) after: usize,
}

thread_local! {
    static EVENTS: RefCell<Option<Vec<Event>>> = const { RefCell::new(None) };
}

pub(crate) fn reset() {
    EVENTS.with(|events| *events.borrow_mut() = Some(Vec::new()));
}

pub(crate) fn snapshot() -> Vec<Event> {
    EVENTS.with(|events| events.borrow_mut().take().unwrap_or_default())
}

pub(crate) fn record(stage: &'static str, before: usize, after: usize) {
    EVENTS.with(|events| {
        if let Some(events) = events.borrow_mut().as_mut() {
            events.push(Event {
                stage,
                before,
                after,
            });
        }
    });
}

pub(crate) fn count(stage: &'static str) {
    record(stage, 0, 0);
}

pub(crate) fn is_recording() -> bool {
    EVENTS.with(|events| events.borrow().is_some())
}

/// Aggregate trace-only calls/work. A labelled isolated run starts another group.
/// For `.total` events, `before` is call count and `after` is summed local work.
pub(crate) fn accumulate(stage: &'static str, before: usize, after: usize) {
    EVENTS.with(|events| {
        if let Some(events) = events.borrow_mut().as_mut() {
            let start = events
                .iter()
                .rposition(|event| event.stage == "control.isolated.enter")
                .map_or(0, |index| index + 1);
            if let Some(event) = events[start..]
                .iter_mut()
                .find(|event| event.stage == stage)
            {
                event.before += 1;
                event.after += after - before;
            } else {
                events.push(Event {
                    stage,
                    before: 1,
                    after: after - before,
                });
            }
        }
    });
}
