import SourceScheduledReceiverRechecking
import SourceScheduledHandlerTransport
import SourceHandlerBoundaryComposition

/-! Derive source rechecking when a new interpretation is bypassed by an
already selected request. The original capture supplies its closing bound;
closing erases the inserted handler, so original callback code is reused. -/
namespace Ash.OneShot.SourceScheduledSourceRechecking
open SourceDependencyCapture (Scope)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledCapabilityAnnotations (Code Retained DeclarationPolicy)
open SourceScheduledHandlerRequests (cut_prefix)
open SourceDependencyOwners (PendingWithin owners)
open SourceHandlerInterference (exposed)
open SourceRecursiveRoutes (scopeProviders)

/-- The old checked disposing capture authenticates the callback bound.
Splitting that bound at the actual insertion restores providers hidden by the
captured suffix before checking the newly installed effect's separation. -/
theorem shield_from_original_capture
    (passed : SourceHandlerRequirements.reaches requested front = true)
    (found : SourceDependencyCapture.select requested operation outside =
      some (.handler captured waiting contract modes))
    (checked : SourceDependencyCapture.CaptureGuard outward (front.append outside) requested operation)
    (separate : contract.dispose = true → installed ∉ scopeProviders captured.shape.normal ++ outward) :
    contract.dispose = true → SourceHandlerInterference.check installed front.shape [] = true := by
  intro disposes
  obtain ⟨_, closing, _⟩ := SourceDependencyCapture.disposing_capture
    (SourceDependencyCapture.check_capture_iff.mpr checked)
    (SourceHandlerSelection.selected_outside passed found) disposes
  have covered : exposed (front.append captured).shape ⊆ outward := by
    simpa only [scopeProviders, List.nil_append] using SourceHandlerInterference.exposed_bound closing
  have inside := ((SourceHandlerBoundaryComposition.boundary_append_iff front captured).mp covered).1
  apply (SourceHandlerInterference.check_summary front.shape).mpr
  intro member
  exact False.elim (separate disposes (inside member))

variable [declarations : DeclarationPolicy]

/-- Handler erasure identifies the actual closing forest, so its original
annotation rechecks by reflexivity. No replacement callback is supplied. -/
theorem RetainedChange.erased_handler
    {frontHints : Hints frontScope} {savedHints : Hints savedScope}
    (front : Forest frontHints) (saved : Forest savedHints)
    {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
    (source : Retained world (front.append saved).forClosing outside) :
    RetainedChange outward actions phases source
      (front.append (.handler (effect := installed) (table := table) (families := families)
        (required := required) saved)).forClosing outside :=
  (SourceScheduledRecomposition.predicate_congr
    (SourceHandlerRequests.forClosing_inserted frontScope)
    (SourceScheduledHandlerRequests.hints_forClosing_inserted frontHints savedHints)
    (SourceScheduledHandlerRequests.forest_forClosing_inserted front saved)
    (fun closing => RetainedChange outward actions phases source closing outside)).mpr .same

/-- Derive all selected-request rechecking premises from the original checked
request and an exact finite shielding check. Selected modes, callback code and
ownership bounds are retained using the existing insertion theorems. -/
theorem Expression.bypassed_selected
    {frontHints : Hints frontScope} {outsideHints : Hints outsideScope}
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    (front : Forest frontHints) {outside : Forest outsideHints}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (passed : SourceHandlerRequirements.reaches requested frontScope = true)
    (different : requested ≠ installed)
    (cut : SourceScheduledNeutral.Cut requested operation contract modes outside saved waiting)
    {oldCut : SourceScheduledNeutral.Cut requested operation contract modes (front.append outside) (front.append saved) waiting}
    {oldBound : contract.dispose = true → PendingWithin world
      (owners (frontScope.append savedScope)) (frontScope.append savedScope)}
    {oldClosing : contract.dispose = true → Retained world
      (front.append saved).forClosing (.running waiting)}
    (ready : (Code.selected (world := world) oldCut oldBound oldClosing).Valid outward actions phases)
    (shielded : contract.dispose = true → SourceHandlerInterference.check installed frontScope.shape [] = true) :
    Expression outward actions phases (Code.selected oldCut oldBound oldClosing)
      (front.append (.handler (effect := installed) (table := table) (families := families)
        (required := required) outside)) := by
  apply Expression.selected
    (cut_prefix front passed (SourceScheduledNeutral.Cut.handler (table := table) (families := families) (required := required) different cut))
  · exact SourceDependencyCapture.check_capture_iff.mpr
      (SourceHandlerClosingInsertion.bypassed_guard_transport passed different cut.erase.lookup
        (SourceDependencyCapture.check_capture_iff.mp ready.1) shielded)
  · intro disposes
    simpa only [SourceHandlerRequests.owners_inserted] using
      SourceHandlerRequests.pending_owners_inserted (effect := installed) (table := table)
        (families := families) frontScope (oldBound disposes)
  · intro disposes
    exact RetainedChange.erased_handler front saved (oldClosing disposes)

/-- A declaration-level exclusion and the original request derive the shield.
No target guard, target closing derivation or target validity is a premise. -/
theorem Expression.bypassed_selected_from_bound
    {frontHints : Hints frontScope} {outsideHints : Hints outsideScope}
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    (front : Forest frontHints) {outside : Forest outsideHints}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (passed : SourceHandlerRequirements.reaches requested frontScope = true)
    (different : requested ≠ installed)
    (cut : SourceScheduledNeutral.Cut requested operation contract modes outside saved waiting)
    {oldCut : SourceScheduledNeutral.Cut requested operation contract modes (front.append outside) (front.append saved) waiting}
    {oldBound : contract.dispose = true → PendingWithin world
      (owners (frontScope.append savedScope)) (frontScope.append savedScope)}
    {oldClosing : contract.dispose = true → Retained world
      (front.append saved).forClosing (.running waiting)}
    (ready : (Code.selected (world := world) oldCut oldBound oldClosing).Valid outward actions phases)
    (separate : contract.dispose = true → installed ∉ scopeProviders savedScope.shape.normal ++ outward) :
    Expression outward actions phases (Code.selected oldCut oldBound oldClosing)
      (front.append (.handler (effect := installed) (table := table) (families := families)
        (required := required) outside)) :=
  Expression.bypassed_selected front passed different cut ready
    (shield_from_original_capture passed cut.erase.lookup
      (SourceDependencyCapture.check_capture_iff.mp ready.1) separate)

/-- When the actual capture is unchanged, its original guard and owner bound
are reused. The only recursive obligation concerns the original closing source
at the changed waiting suffix, not a newly authenticated normal prefix. -/
theorem Expression.same_capture_selected
    {beforeHints : Hints beforeScope} {afterHints : Hints afterScope}
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope} {nextHints : Hints nextScope}
    {before : Forest beforeHints} {after : Forest afterHints}
    {saved : Forest savedHints} {waiting : Forest waitingHints} {next : Forest nextHints}
    {oldCut : SourceScheduledNeutral.Cut effect operation contract modes before saved waiting}
    {oldBound : contract.dispose = true → PendingWithin world (owners savedScope) savedScope}
    {oldClosing : contract.dispose = true → Retained world saved.forClosing (.running waiting)}
    (targetCut : SourceScheduledNeutral.Cut effect operation contract modes after saved next)
    (ready : (Code.selected oldCut oldBound oldClosing).Valid outward actions phases)
    (closing : ∀ disposes, ReceiverChange outward actions phases (oldClosing disposes) (.running next)) :
    Expression outward actions phases (Code.selected oldCut oldBound oldClosing) after := by
  exact .selected targetCut
    (SourceDependencyCapture.check_capture_iff.mpr
      (SourceHandlerSelection.guard_same_capture oldCut.erase.lookup targetCut.erase.lookup
        (SourceDependencyCapture.check_capture_iff.mp ready.1)))
    oldBound (fun disposes => (closing disposes).rechecking)

/-- A changed waiting suffix leaves the selected capture, mode, guard and
owner bound intact. Only the original closing annotation needs recursive
receiver rechecking; no independently checked target guard is required. -/
theorem Expression.waiting_selected
    {wholeHints : Hints wholeScope} {savedHints : Hints savedScope}
    {waitingHints : Hints waitingScope} {nextHints : Hints nextScope}
    {whole : Forest wholeHints} {saved : Forest savedHints}
    {waiting : Forest waitingHints} (next : Forest nextHints)
    {cut : SourceScheduledNeutral.Cut requested operation contract modes whole saved waiting}
    {oldBound : contract.dispose = true → PendingWithin world (owners savedScope) savedScope}
    {oldClosing : contract.dispose = true → Retained world saved.forClosing (.running waiting)}
    (ready : (Code.selected cut oldBound oldClosing).Valid outward actions phases)
    (closing : ∀ disposes, ReceiverChange outward actions phases (oldClosing disposes) (.running next)) :
    Expression outward actions phases (Code.selected cut oldBound oldClosing) (saved.append next) := by
  exact .same_capture_selected (SourceScheduledHandlerRequests.replace_waiting cut next) ready closing

end Ash.OneShot.SourceScheduledSourceRechecking

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.shield_from_original_capture
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.RetainedChange.erased_handler
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.Expression.bypassed_selected
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.Expression.bypassed_selected_from_bound
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.Expression.waiting_selected

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.Expression.same_capture_selected
