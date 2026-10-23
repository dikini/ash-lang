//! Pre-entry storage for authenticated checked source boundary reports.
use super::source_owner_phases::OwnerPhaseFailure;
use super::{HeapCell, Location, Value};
use crate::{
    foreign::source_runtime::{
        CheckedCompletion as Completion, CheckedNativeFact as Native, SyntheticFinishWitness,
    },
    module::{FOREIGN_NATIVE_HOST_LOCAL, ForeignCheckedNominalRole as Role, ModuleId},
    resolved::ResolvedRegistry,
    types::{ConstructorId, EffectId, NominalTypeId, TypeWorkBudget},
};

impl super::Machine<'_> {
    /// Transfer the actual ledger obligation before its structural frame is
    /// destroyed. A previously published closing observation stays unchanged;
    /// this cannot complete the separately owned source continuation.
    pub(super) fn settle_checked_observer(
        &mut self,
        checked: &crate::foreign::source_runtime::NativeOwnerBoundary,
        slot: Option<&super::super::checked_reports::ResourceReportSlot>,
        point: super::super::GuardInspectionPoint,
    ) -> Option<usize> {
        use crate::foreign::source_runtime::{CheckedLocalCompletion as K, CheckedNativeFact as Native};
        checked.output_failed();
        if slot.is_some_and(|slot| slot.settled()) { return slot.and_then(|slot| slot.published()); }
        let (completion, k, native, unresolved) = checked.closing_record()
            .expect("checked source frame retains its reserved ledger slot");
        // A pre-entry or observed-null acquisition created no owner K. There
        // is no structural owner closing record to manufacture in that case.
        if k == K::Absent && native == Native::NoOwner && !unresolved {
            if let Some(slot) = slot { slot.cancel_unacquired(); }
            return None;
        }
        if k == K::Absent {
            self.inspect_unpublished_guard(checked, slot, point);
            return None;
        }
        let record = super::super::ResourceReport::closing_facts(
            completion, k, native, unresolved, checked.closing_status(),
        ).expect("terminal checked owner has transferred or discharged K");
        let reports = self.checked_reports.as_mut().expect("checked entry reserved report storage");
        Some(reports.commit_owner(slot.expect("armed owner retained its funded report slot"), record))
    }
    /// Observe only the guard category. Successful source refusal/discard is
    /// not an output failure and cannot create a source closing transition.
    pub(super) fn inspect_unpublished_guard(
        &mut self,
        checked: &crate::foreign::source_runtime::NativeOwnerBoundary,
        slot: Option<&super::super::checked_reports::ResourceReportSlot>,
        point: super::super::GuardInspectionPoint,
    ) {
        use crate::foreign::source_runtime::{CheckedLocalCompletion as K, CheckedNativeFact as Native};
        use super::super::{GuardBackingObservation, ResourceNativeFact, UnpublishedGuardInspection};
        if slot.is_some_and(|slot| slot.settled()) { return; }
        let (_, k, native, unresolved) = checked.closing_record().expect("funded unpublished guard ledger");
        assert_eq!(k, K::Absent, "guard inspection cannot enter the scope-closing channel");
        if native == Native::NoOwner && !unresolved {
            if let Some(slot) = slot { slot.cancel_unacquired(); }
            return;
        }
        let native = match native { Native::NoOwner => ResourceNativeFact::NoOwner,
            Native::Owned => ResourceNativeFact::Owned, Native::Consumed => ResourceNativeFact::Consumed };
        let backing = if checked.retains_backing() { GuardBackingObservation::Retained }
            else { GuardBackingObservation::Unknown };
        let observation = UnpublishedGuardInspection::observed(native, unresolved, checked.latest_status(), checked.acquisition_status(), backing, point);
        self.checked_reports.as_mut().expect("checked entry reserved observation storage")
            .commit_guard(slot.expect("armed guard retained its funded inspection slot"), observation);
    }

}

/// These constructor identities are reconstructed from the original builtin
/// inventory before entry. No spelling or source-created constructor approves it.
#[derive(Debug)]
pub(super) struct LocalBoundaryReport {
    first: Location,
    fields: Box<[Value]>,
    module: ModuleId,
    boundary_failed: ConstructorId,
}
impl LocalBoundaryReport {
    pub(super) fn admit(
        returned: ConstructorId,
        registry: &ResolvedRegistry,
        heap: &mut Vec<HeapCell>,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, OwnerPhaseFailure> {
        let module = returned.owner().module();
        work.charge(2)
            .map_err(|()| OwnerPhaseFailure::WorkReservation)?;
        if returned.owner() != NominalTypeId::new(module, Role::CheckedCall.local())
            || returned.constructor() != 0
            || !module.is_builtin_foreign()
        {
            return Err(OwnerPhaseFailure::Authority);
        }
        let host = registry
            .effect(EffectId::new(module, FOREIGN_NATIVE_HOST_LOCAL))
            .ok_or(OwnerPhaseFailure::Authority)?;
        let facts = crate::foreign::checked_builtins::authenticate_checked_builtins(
            registry, module, host.span, work,
        )
        .map_err(|error| {
            if error.is_resource_exhaustion() {
                OwnerPhaseFailure::WorkReservation
            } else {
                OwnerPhaseFailure::Authority
            }
        })?;
        // Seven immutable cells and four tuple fields are funded and allocated
        // while the enclosing boundary still owns its live guard.
        work.charge(7 + 4 + 4)
            .map_err(|()| OwnerPhaseFailure::WorkReservation)?;
        heap.try_reserve(7)
            .map_err(|_| OwnerPhaseFailure::HeapReservation(7))?;
        let mut fields = Vec::new();
        fields
            .try_reserve_exact(4)
            .map_err(|_| OwnerPhaseFailure::HeapReservation(4))?;
        fields.resize(4, Value::Unit);
        let first = heap.len();
        for _ in 0..7 {
            heap.push(HeapCell::Uninitialized);
        }
        Ok(Self {
            first,
            fields: fields.into_boxed_slice(),
            module,
            boundary_failed: facts.boundary_failed(),
        })
    }
    fn constructor(&self, role: Role, ordinal: u32) -> ConstructorId {
        ConstructorId::new(NominalTypeId::new(self.module, role.local()), ordinal)
    }
    pub(super) fn report(
        mut self,
        witness: &SyntheticFinishWitness,
        heap: &mut [HeapCell],
        returned: Location,
    ) -> Result<(), OwnerPhaseFailure> {
        let first = self.first;
        if !heap.get(first..first + 7).is_some_and(|cells| {
            cells
                .iter()
                .all(|cell| matches!(cell, HeapCell::Uninitialized))
        }) || !matches!(heap.get(returned), Some(HeapCell::Uninitialized))
        {
            return Err(OwnerPhaseFailure::HeapSlotInvariant);
        }
        let reason = match witness.completion() {
            Completion::SessionLost => 0,
            Completion::DependencyBlocked => 1,
            Completion::Quarantined => 2,
            Completion::Observed(_) => return Err(OwnerPhaseFailure::Authority),
        };
        let native = match witness.native() {
            Native::NoOwner => 0,
            Native::Owned => 1,
            Native::Consumed => 2,
        };
        let status_id = self.constructor(Role::NativeStatus, 0);
        let native_id = self.constructor(Role::NativeFact, native);
        let absence_id = self.constructor(Role::DiagnosticAbsence, 0);
        let diagnostic_id = self.constructor(Role::Diagnostic, 0);
        let record_id = self.constructor(Role::BoundaryRecord, 0);
        let failure_id = self.constructor(Role::BoundaryFailure, reason);
        self.fields[0] = Value::Location(first);
        self.fields[1] = Value::Location(first + 1);
        self.fields[2] = Value::Boolean(witness.unresolved());
        self.fields[3] = Value::Location(first + 3);
        heap[first] = HeapCell::Constructor(status_id, None);
        heap[first + 1] = HeapCell::Constructor(native_id, None);
        heap[first + 2] = HeapCell::Constructor(absence_id, None);
        heap[first + 3] = HeapCell::Constructor(diagnostic_id, Some(Value::Location(first + 2)));
        heap[first + 4] = HeapCell::Tuple(self.fields);
        heap[first + 5] = HeapCell::Constructor(record_id, Some(Value::Location(first + 4)));
        heap[first + 6] = HeapCell::Constructor(failure_id, Some(Value::Location(first + 5)));
        heap[returned] =
            HeapCell::Constructor(self.boundary_failed, Some(Value::Location(first + 6)));
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn local_boundary_report_storage_authenticates_roles_and_prepays_entry() {
        let (program, _) = crate::elaborate::checked_owner_passive_program_for_source(
            include_str!("../../tests/fixtures/checked-owner-runtime/owner.ash"),
            "import @builtin.foreign as Foreign\nimport producer as Producer\nmain : Unit -> Foreign.CheckedScope<Producer.CopyProbe, Unit, Unit>\nmain () = Producer.run ()\n",
        );
        let module = program
            .registry()
            .effects()
            .iter()
            .find(|effect| effect.id.module().is_builtin_foreign())
            .unwrap()
            .id
            .module();
        let returned = ConstructorId::new(NominalTypeId::new(module, Role::CheckedCall.local()), 0);
        let mut measured = TypeWorkBudget::default();
        let mut heap = Vec::new();
        let canonical =
            LocalBoundaryReport::admit(returned, program.registry(), &mut heap, &mut measured)
                .unwrap();
        assert_eq!(heap.len(), 7);
        assert_eq!(canonical.fields.len(), 4);
        let cost = measured.used();
        for prefix in [0, 11] {
            let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
            short.charge(prefix).unwrap();
            assert!(matches!(
                LocalBoundaryReport::admit(
                    returned,
                    program.registry(),
                    &mut Vec::new(),
                    &mut short
                ),
                Err(OwnerPhaseFailure::WorkReservation)
            ));
            assert!(
                LocalBoundaryReport::admit(
                    returned,
                    program.registry(),
                    &mut Vec::new(),
                    &mut short
                )
                .is_err()
            );
            let mut fresh = TypeWorkBudget::with_limit(prefix + cost);
            fresh.charge(prefix).unwrap();
            assert!(
                LocalBoundaryReport::admit(
                    returned,
                    program.registry(),
                    &mut Vec::new(),
                    &mut fresh
                )
                .is_ok()
            );
            assert_eq!(fresh.used(), prefix + cost);
        }
        let donor = ConstructorId::new(returned.owner(), 1);
        assert!(matches!(
            LocalBoundaryReport::admit(
                donor,
                program.registry(),
                &mut Vec::new(),
                &mut TypeWorkBudget::default()
            ),
            Err(OwnerPhaseFailure::Authority)
        ));
    }
}
