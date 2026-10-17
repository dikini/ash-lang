//! Evaluator-scoped failure observation for the existing disposal worklists.
//!
//! Type, kind and frame walkers consume each owned structural cell once.
//! Environment walkers detach at most two outgoing edges from each uniquely
//! owned entry; shared roots are dismantled only by their last owner. The
//! worklists add no reachability scan or recursive destruction of abandoned
//! remainders. The first failure stops all subsequent worklist growth.

use std::cell::Cell;

use super::{
    CleanupStatus, ResourceFailure, ResourceFailureCause, RuntimeFailure, RuntimePhase,
    RuntimeResource,
};

#[derive(Clone, Copy, Default)]
struct State {
    active: bool,
    no_growth: bool,
    failure: Option<ResourceFailure>,
}

thread_local! {
    static STATE: Cell<State> = const { Cell::new(State { active: false, no_growth: false, failure: None }) };
    #[cfg(test)]
    static GROWTH_ATTEMPTS: Cell<usize> = const { Cell::new(0) };
}

pub(crate) struct Scope(State);

impl Scope {
    pub(crate) fn enter() -> Self {
        Self(STATE.replace(State {
            active: true,
            ..State::default()
        }))
    }

    pub(crate) fn finish<T>(&self, result: Result<T, RuntimeFailure>) -> Result<T, RuntimeFailure> {
        match (result, failure()) {
            (Ok(value), None) => Ok(value),
            (Ok(value), Some(first)) => {
                // Keep the scope active while discarding an unpublishable result.
                drop(value);
                Err(report(first))
            }
            (Err(mut primary), failure) => {
                if let Some(secondary) = failure {
                    if primary == report(secondary) {
                        return Err(primary);
                    }
                    primary = primary.with_teardown_failure(secondary, CleanupStatus::Incomplete);
                } else if let RuntimeFailure::Report(report) = &mut primary {
                    report.cleanup = CleanupStatus::Complete;
                }
                Err(primary)
            }
        }
    }
}

impl Drop for Scope {
    fn drop(&mut self) {
        STATE.set(self.0);
    }
}

#[cfg(test)]
pub(crate) struct NoGrowth(bool);

#[cfg(test)]
impl NoGrowth {
    pub(crate) fn enter() -> Self {
        let mut state = STATE.get();
        let previous = state.no_growth;
        state.no_growth = true;
        STATE.set(state);
        Self(previous)
    }
}

#[cfg(test)]
impl Drop for NoGrowth {
    fn drop(&mut self) {
        STATE.set(State {
            no_growth: self.0,
            ..STATE.get()
        });
    }
}

pub(crate) fn failure() -> Option<ResourceFailure> {
    STATE.get().failure
}

pub(crate) fn check() -> Result<(), RuntimeFailure> {
    failure().map_or(Ok(()), |failure| Err(report(failure)))
}

fn report(failure: ResourceFailure) -> RuntimeFailure {
    let mut failure = RuntimeFailure::resource(failure);
    if let RuntimeFailure::Report(report) = &mut failure {
        report.cleanup = CleanupStatus::Incomplete;
    }
    failure
}

#[cfg(test)]
pub(crate) fn growth_attempts() -> usize {
    GROWTH_ATTEMPTS.get()
}

#[cfg(test)]
pub(crate) fn reset_growth_attempts() {
    GROWTH_ATTEMPTS.set(0);
}

fn record(
    cause: ResourceFailureCause,
    resource: RuntimeResource,
    requested: usize,
    available: Option<usize>,
) {
    let mut state = STATE.get();
    if state.failure.is_none() {
        state.failure = Some(ResourceFailure::new(
            cause,
            RuntimePhase::Teardown,
            resource,
            Some(requested),
            available,
        ));
        STATE.set(state);
    }
}

// Eight retained slots cover the fixed local branching of these walkers.
// They are not a source depth limit. Ordinary disposal can grow the spill
// storage fallibly; native-refusal delivery must stay within retained storage.
const INLINE: usize = 8;

pub(crate) struct Pending<T> {
    inline: [Option<T>; INLINE],
    used: usize,
    spill: Vec<T>,
    resource: RuntimeResource,
}

impl<T> Pending<T> {
    pub(crate) fn new(resource: RuntimeResource) -> Self {
        Self::from_vec(Vec::new(), resource)
    }

    pub(crate) fn from_vec(spill: Vec<T>, resource: RuntimeResource) -> Self {
        Self {
            inline: std::array::from_fn(|_| None),
            used: 0,
            spill,
            resource,
        }
    }

    pub(crate) fn push(&mut self, value: T) {
        let state = STATE.get();
        if state.failure.is_some() {
            std::mem::forget(value);
            return;
        }
        if self.spill.is_empty() && self.used < INLINE {
            self.inline[self.used] = Some(value);
            self.used += 1;
            return;
        }
        if self.spill.len() == self.spill.capacity() && (state.active || state.no_growth) {
            if state.no_growth {
                record(
                    ResourceFailureCause::ConfiguredCapacity,
                    self.resource,
                    1,
                    Some(0),
                );
                std::mem::forget(value);
                return;
            }
            #[cfg(test)]
            GROWTH_ATTEMPTS.set(GROWTH_ATTEMPTS.get() + 1);
            #[cfg(test)]
            if super::machine::refuse_disposal_growth() {
                record(
                    ResourceFailureCause::AllocatorRefused,
                    self.resource,
                    1,
                    None,
                );
                std::mem::forget(value);
                return;
            }
            if self.spill.try_reserve(1).is_err() {
                record(
                    ResourceFailureCause::StorageReservationFailed,
                    self.resource,
                    1,
                    None,
                );
                std::mem::forget(value);
                return;
            }
        }
        self.spill.push(value);
    }

    pub(crate) fn pop(&mut self) -> Option<T> {
        if failure().is_some() {
            self.abandon();
            return None;
        }
        self.pop_retained()
    }

    fn pop_retained(&mut self) -> Option<T> {
        self.spill.pop().or_else(|| {
            if self.used == 0 {
                None
            } else {
                self.used -= 1;
                self.inline[self.used].take()
            }
        })
    }

    fn abandon(&mut self) {
        while let Some(value) = self.pop_retained() {
            std::mem::forget(value);
        }
    }
}

impl<T> Drop for Pending<T> {
    fn drop(&mut self) {
        // Walkers consume each owned item once. Undismantled tails must not
        // reenter recursive Rust drop after a resource failure.
        self.abandon();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn inline_and_spill_preserve_lifo_and_scopes_are_nested_and_thread_local() {
        let outer = Scope::enter();
        let mut pending = Pending::new(RuntimeResource::TypeDisposal);
        for value in 0..32 {
            pending.push(value);
        }
        for value in (0..32).rev() {
            assert_eq!(pending.pop(), Some(value));
        }
        let _bounded = NoGrowth::enter();
        let mut bounded = Pending::new(RuntimeResource::TypeDisposal);
        for value in 0..9 {
            bounded.push(value);
        }
        let first = failure().unwrap();
        assert_eq!(first.available, Some(0));
        {
            let nested = Scope::enter();
            assert!(failure().is_none());
            assert!(nested.finish(Ok::<_, RuntimeFailure>(())).is_ok());
        }
        assert_eq!(failure(), Some(first));
        std::thread::spawn(|| assert!(failure().is_none()))
            .join()
            .unwrap();
        assert!(outer.finish(Ok::<_, RuntimeFailure>(())).is_err());
    }

    #[test]
    fn failed_scope_discards_success_inside_scope_without_retrying_growth() {
        struct ResultOwner;
        impl Drop for ResultOwner {
            fn drop(&mut self) {
                assert!(STATE.get().active);
                assert!(failure().is_some());
                let mut pending = Pending::new(RuntimeResource::KindDisposal);
                for _ in 0..32 {
                    pending.push(0u8);
                }
            }
        }
        let scope = Scope::enter();
        let _bounded = NoGrowth::enter();
        reset_growth_attempts();
        let mut pending = Pending::new(RuntimeResource::TypeDisposal);
        for _ in 0..9 {
            pending.push(0u8);
        }
        assert!(scope.finish(Ok(ResultOwner)).is_err());
        assert_eq!(growth_attempts(), 0);
    }
}
