import SourceHandlerClosingInsertion
import SourceDependencySchemes

/-! Full source request transport when a different-effect handler enters its
captured prefix. The closing schedule and owner bound are derived from the
old request; only the finite callback interference check is additional. -/
namespace Ash.OneShot.SourceHandlerRequests
open ScopedExpressions ProtectionContracts
open SourceDependencyCapture
open SourceDependencyChecks (Local Pending)
open SourceDependencyProjection (project)
open SourceDependencyOwners (owners PendingWithin)
open SourceHandlerRequirements (reaches)

theorem forClosing_inserted (front : Scope) :
    (front.append (.handler effect table families tail)).forClosing = (front.append tail).forClosing := by
  induction front <;> simp_all [Scope.append, Scope.forClosing]

theorem owners_inserted (front : Scope) :
    owners (front.append (.handler effect table families tail)) = owners (front.append tail) := by
  induction front <;> simp_all [Scope.append, owners]

theorem pending_owners_inserted (front : Scope)
    (checked : PendingWithin world owned (front.append tail)) :
    PendingWithin world owned (front.append (.handler effect table families tail)) := by
  induction front with
  | nil => exact .handler checked
  | plain dependencies rest ih => cases checked with | plain code next => exact .plain code (ih next)
  | handler other priorTable priorFamilies rest ih => cases checked with | handler next => exact .handler (ih next)
  | cell identity rest ih => cases checked with | cell next => exact .cell (ih next)
  | cleanup needs callback rest ih => cases checked with | cleanup next => exact .cleanup (ih next)
  | running rest ih => cases checked with | running next => exact .running (ih next)
  | spent owner rest ih => cases checked with | spent next => exact .spent (ih next)
  | live owner saved rest ihSaved ihRest => cases checked with | live inside outside => exact .live inside (ihRest outside)

/-- Preserve every field of the source request constructor. Closing removes
the inserted handler, so its callback schedule is the old schedule, rather
than an assumed checked successor. The independent owner bound transports. -/
theorem bypassed_request
    (passed : reaches requested front = true) (different : requested ≠ effect)
    (found : select requested operation outside = some (.handler captured tail contract modes))
    (checked : Local outward actions phases world (.request requested operation) (front.append outside))
    (shielded : contract.dispose = true → SourceHandlerInterference.check effect front.shape [] = true) :
    Local outward actions phases world (.request requested operation)
      (front.append (.handler effect table families outside)) := by
  have before := SourceHandlerSelection.selected_outside passed found
  have after := SourceHandlerSelection.inserted_bypassed (table := table) (families := families) passed different found
  apply Local.request_selected after
  · exact check_capture_iff.mpr (SourceHandlerClosingInsertion.bypassed_guard_transport passed different found
      (check_capture_iff.mp checked.request_guard) shielded)
  · intro disposes
    simpa only [forClosing_inserted] using checked.request_schedule before disposes
  · intro disposes
    simpa only [owners_inserted] using pending_owners_inserted (effect := effect) (table := table)
      (families := families) front (checked.request_owners before disposes)

theorem project_reaches (scope : Scope) : reaches effect (project scope) = reaches effect scope := by
  induction scope <;> simp_all [project, reaches]

theorem project_interference (scope : Scope) :
    SourceHandlerInterference.check effect (project scope).shape context =
      SourceHandlerInterference.check effect scope.shape context := by
  induction scope generalizing context <;>
    simp_all [project, Scope.shape, SourceHandlerInterference.check, SourceDependencyProjection.project_normal]

/-- The stronger source layers use the established spent-marker projection.
Reuse its exact lookup law and the same finite interference check. -/
theorem checked_bypassed_request
    (passed : reaches requested front = true) (different : requested ≠ effect)
    (found : select requested operation outside = some (.handler captured tail contract modes))
    (checked : SourceDependencySchemes.Checked outward actions phases world (.request requested operation) (front.append outside))
    (shielded : contract.dispose = true → SourceHandlerInterference.check effect front.shape [] = true) :
    SourceDependencySchemes.Checked outward actions phases world (.request requested operation)
      (front.append (.handler effect table families outside)) := by
  have selected : select requested operation (project outside) =
      some (.handler (project captured) (project tail) contract modes) := by
    rw [SourceDependencyProjection.project_select, found]
    rfl
  have transported := bypassed_request (front := project front) (table := table) (families := families)
    (by simpa only [project_reaches] using passed) different selected
    (by simpa only [SourceDependencySchemes.Checked, SourceDependencyProjection.project_append] using checked)
    (fun permitted => by simpa only [project_interference] using shielded permitted)
  simpa only [SourceDependencySchemes.Checked, SourceDependencyProjection.project_append, project] using transported

end Ash.OneShot.SourceHandlerRequests

#print axioms Ash.OneShot.SourceHandlerRequests.forClosing_inserted
#print axioms Ash.OneShot.SourceHandlerRequests.owners_inserted
#print axioms Ash.OneShot.SourceHandlerRequests.pending_owners_inserted
#print axioms Ash.OneShot.SourceHandlerRequests.bypassed_request
#print axioms Ash.OneShot.SourceHandlerRequests.project_reaches
#print axioms Ash.OneShot.SourceHandlerRequests.project_interference
#print axioms Ash.OneShot.SourceHandlerRequests.checked_bypassed_request
