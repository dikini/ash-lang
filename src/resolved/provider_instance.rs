//! One-shot compiler preparation attached to an original resource occurrence.
//!
//! Storage does not mint executable authority. The elaborator supplies a
//! complete immutable plan and final Core validates its original relationships.

use std::{
    collections::HashSet,
    fmt,
    sync::{Arc, OnceLock},
};

use super::ResolvedBuildFailure;
use crate::{elaborate::PreparedProviderInstance, types::TypeWorkBudget};

pub(crate) struct ProviderInstanceSlot(Arc<OnceLock<Arc<PreparedProviderInstance>>>);

impl ProviderInstanceSlot {
    pub(crate) fn empty_with_budget(
        work: &mut TypeWorkBudget,
    ) -> Result<Self, ResolvedBuildFailure> {
        work.charge(1)
            .map_err(|()| ResolvedBuildFailure::TypeResource)?;
        Ok(Self::empty())
    }

    fn empty() -> Self {
        Self(Arc::new(OnceLock::new()))
    }

    pub(crate) fn get(&self) -> Option<&PreparedProviderInstance> {
        self.0.get().map(AsRef::as_ref)
    }

    #[cfg(test)]
    pub(crate) fn retain_for_test(&self) -> Self {
        Self(Arc::clone(&self.0))
    }

    #[cfg(test)]
    pub(crate) fn prepared_for_test(&self) -> Option<Arc<PreparedProviderInstance>> {
        self.0.get().map(Arc::clone)
    }

    /// Keep the exact empty original occurrence within source preparation.
    /// Ordinary Clone continues to freshen empty source slots.
    pub(crate) fn retain_unpublished(
        &self,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, ResolvedBuildFailure> {
        work.charge(1)
            .map_err(|()| ResolvedBuildFailure::TypeResource)?;
        if self.get().is_some() {
            return Err(ResolvedBuildFailure::InvalidState);
        }
        Ok(Self(Arc::clone(&self.0)))
    }

    fn storage_id(&self) -> usize {
        Arc::as_ptr(&self.0) as usize
    }
}

impl Clone for ProviderInstanceSlot {
    fn clone(&self) -> Self {
        if self.0.get().is_some() {
            Self(Arc::clone(&self.0))
        } else {
            Self::empty()
        }
    }
}

impl fmt::Debug for ProviderInstanceSlot {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("ProviderInstanceSlot")
            .field("prepared", &self.0.get().is_some())
            .finish()
    }
}

impl PartialEq for ProviderInstanceSlot {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0) || (self.0.get().is_none() && other.0.get().is_none())
    }
}
impl Eq for ProviderInstanceSlot {}

#[derive(Default)]
pub(crate) struct PendingProviderInstancePublication {
    plans: Vec<(ProviderInstanceSlot, Arc<PreparedProviderInstance>)>,
    slots: HashSet<usize>,
}

impl fmt::Debug for PendingProviderInstancePublication {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("PendingProviderInstancePublication")
            .field("plans", &self.plans.len())
            .finish()
    }
}

impl PendingProviderInstancePublication {
    /// Retains the exact still-empty original occurrence for this compiler
    /// transaction. Ordinary empty-slot cloning intentionally freshens instead.
    pub(crate) fn stage(
        &mut self,
        slot: &ProviderInstanceSlot,
        plan: Arc<PreparedProviderInstance>,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ResolvedBuildFailure> {
        work.charge(3)
            .map_err(|()| ResolvedBuildFailure::TypeResource)?;
        let identity = slot.storage_id();
        if slot.get().is_some() || self.slots.contains(&identity) {
            return Err(ResolvedBuildFailure::InvalidState);
        }
        self.plans
            .try_reserve(1)
            .map_err(|_| ResolvedBuildFailure::TypeResource)?;
        self.slots
            .try_reserve(1)
            .map_err(|_| ResolvedBuildFailure::TypeResource)?;
        self.slots.insert(identity);
        self.plans
            .push((ProviderInstanceSlot(Arc::clone(&slot.0)), plan));
        Ok(())
    }

    /// Finalize source-owned preparation after normal typing, before any slot
    /// is filled. Shared plan ownership cannot authorize a mutable replacement.
    pub(crate) fn finalize_unpublished<E>(
        &mut self,
        mut update: impl FnMut(&mut PreparedProviderInstance) -> Result<(), E>,
        invalid: fn() -> E,
    ) -> Result<(), E> {
        for (slot, plan) in &mut self.plans {
            if slot.get().is_some() || !self.slots.contains(&slot.storage_id()) {
                return Err(invalid());
            }
            update(Arc::get_mut(plan).ok_or_else(invalid)?)?;
        }
        Ok(())
    }

    pub(crate) fn len(&self) -> usize {
        self.plans.len()
    }

    /// Preflights every original slot before any plan or evidence publication.
    /// This token and the evidence token must be prepared before either commits.
    pub(crate) fn prepare_publication(
        mut self,
        work: &mut TypeWorkBudget,
    ) -> Result<PreflightedProviderInstancePublication, ResolvedBuildFailure> {
        work.charge(self.plans.len())
            .map_err(|()| ResolvedBuildFailure::TypeResource)?;
        if self.plans.len() != self.slots.len() {
            return Err(ResolvedBuildFailure::InvalidState);
        }
        for (slot, _) in &self.plans {
            if slot.get().is_some() || !self.slots.remove(&slot.storage_id()) {
                return Err(ResolvedBuildFailure::InvalidState);
            }
        }
        if !self.slots.is_empty() {
            return Err(ResolvedBuildFailure::InvalidState);
        }
        Ok(PreflightedProviderInstancePublication { publication: self })
    }
}

#[derive(Debug)]
pub(crate) struct PreflightedProviderInstancePublication {
    publication: PendingProviderInstancePublication,
}

impl PreflightedProviderInstancePublication {
    /// The sole compiler batch must not fill its private slots between
    /// preflight and this allocation-free, charge-free commit.
    pub(crate) fn commit(mut self) {
        while let Some((slot, plan)) = self.publication.plans.pop() {
            assert!(
                slot.0.set(plan).is_ok(),
                "preflighted instance slots remain one-shot empty"
            );
        }
    }
}
