import SourceHandlerRequests
import SourceScheduledRecomposition
import SourceScheduledNeutralChecks
import SourceScheduledPendingSites

/-! Handler insertion in a captured request retains the actual callback
plans. Closing erases the inserted frame, permitting reuse of the existing
schedule and authenticated source cut. -/
namespace Ash.OneShot.SourceScheduledHandlerRequests
open ScopedExpressions ProtectionContracts
open SourceDependencyCapture (Scope)
open SourceContextualHints (Hints)
open SourceContextualInvocationHints (forClosing)
open SourceRetainedPlans (Forest)
open SourceScheduledChecks (Local Pending)
open SourceHandlerRequirements (reaches)

theorem hints_forClosing_inserted (front : Hints frontScope) (tail : Hints tailScope) :
    HEq (forClosing (front.append (.handler (effect := effect) (table := table) (families := families) required tail)))
      (forClosing (front.append tail)) := by
  induction front with
  | nil => rfl
  | plain rest ih | handler oldRequired rest ih | spent rest ih => exact ih
  | cell rest ih =>
      exact SourcePlannedRecomposition.lift_heq
        (SourceHandlerRequests.forClosing_inserted _) ih (fun hints => .cell hints)
  | cleanup rest ih =>
      exact SourcePlannedRecomposition.lift_heq
        (SourceHandlerRequests.forClosing_inserted _) ih (fun hints => .cleanup hints)
  | running rest ih =>
      exact SourcePlannedRecomposition.lift_heq
        (SourceHandlerRequests.forClosing_inserted _) ih (fun hints => .running hints)
  | live saved rest ihSaved ihRest =>
      exact SourcePlannedRecomposition.lift_heq
        (SourceHandlerRequests.forClosing_inserted _) ihRest (fun hints => (forClosing saved).append (.running hints))

theorem forest_forClosing_inserted {frontHints : Hints frontScope} {tailHints : Hints tailScope}
    (front : Forest frontHints) (tail : Forest tailHints) :
    HEq (front.append (.handler (effect := effect) (table := table) (families := families) (required := required) tail)).forClosing
      (front.append tail).forClosing := by
  induction front with
  | nil => rfl
  | plain plan rest ih | handler rest ih | spent rest ih => exact ih
  | cell rest ih =>
      exact SourceScheduledNeutral.lift_heq (decorate := fun hints => .cell hints)
        (SourceHandlerRequests.forClosing_inserted _) (hints_forClosing_inserted _ _) ih (fun forest => .cell forest)
  | cleanup plan rest ih =>
      exact SourceScheduledNeutral.lift_heq (decorate := fun hints => .cleanup hints)
        (SourceHandlerRequests.forClosing_inserted _) (hints_forClosing_inserted _ _) ih (fun forest => .cleanup plan forest)
  | running rest ih =>
      exact SourceScheduledNeutral.lift_heq (decorate := fun hints => .running hints)
        (SourceHandlerRequests.forClosing_inserted _) (hints_forClosing_inserted _ _) ih (fun forest => .running forest)
  | live saved rest ihSaved ihRest =>
      exact SourceScheduledNeutral.lift_heq
        (decorate := fun hints => (forClosing _).append (.running hints))
        (SourceHandlerRequests.forClosing_inserted _) (hints_forClosing_inserted _ _) ihRest
        (fun forest => saved.forClosing.append (.running forest))

/-- Lift the same authenticated cut through every preceding frame that
passes its effect. Dormant saved forests are retained without reinterpretation. -/
theorem cut_prefix {frontHints : Hints frontScope} (front : Forest frontHints)
    (passed : reaches effect frontScope = true)
    (cut : SourceScheduledNeutral.Cut effect operation contract modes whole saved waiting) :
    SourceScheduledNeutral.Cut effect operation contract modes (front.append whole) (front.append saved) waiting := by
  induction front with
  | nil => exact cut
  | plain plan rest ih => exact .plain (ih passed)
  | handler rest ih =>
      rename_i other table families required
      have different : effect ≠ other := by intro same; simp [reaches, same] at passed
      exact .handler different (ih (by simpa only [reaches, if_neg different] using passed))
  | cell rest ih =>
      rename_i identity
      have different : effect ≠ .cell identity := by intro same; simp [reaches, same] at passed
      exact .cell different (ih (by simpa only [reaches, if_neg different] using passed))
  | cleanup plan rest ih => exact .cleanup (ih passed)
  | running rest ih => exact .running (ih passed)
  | live saved rest ihSaved ihRest => exact .live (ihRest passed)
  | spent rest ih => exact .spent (ih passed)

/-- The actual retained request schedule is reused after removing the new
handler during closing. The cut fixes both old and new plan-carrying pieces. -/
theorem bypassed_request {frontHints : Hints frontScope} {outsideHints : Hints outsideScope}
    {savedHints : Hints captured} {waitingHints : Hints tail}
    (front : Forest frontHints) (outside : Forest outsideHints)
    (saved : Forest savedHints) (waiting : Forest waitingHints)
    (passed : reaches requested frontScope = true) (different : requested ≠ effect)
    (cut : SourceScheduledNeutral.Cut requested operation contract modes outside saved waiting)
    (checked : Local outward actions phases world (.request (effect := requested) (operation := operation)) (front.append outside))
    (shielded : contract.dispose = true → SourceHandlerInterference.check effect frontScope.shape [] = true) :
    Local outward actions phases world (.request (effect := requested) (operation := operation))
      (front.append (.handler (effect := effect) (table := table) (families := families) (required := required) outside)) := by
  have before := cut_prefix front passed cut
  have after := cut_prefix front passed (SourceScheduledNeutral.Cut.handler (required := required) (table := table) (families := families) different cut)
  cases checked with
  | request legacy scheduled =>
      refine .request (SourceHandlerRequests.checked_bypassed_request passed different cut.erase.lookup legacy shielded) ?_
      intro actualCaptured actualTail actualSaved actualWaiting actualContract actualModes targetCut targetSaved targetWaiting targetSame disposes
      cases Option.some.inj (after.erase.lookup.symm.trans targetCut.lookup)
      obtain ⟨rfl, rfl⟩ := after.erase.unique targetCut.hints
      obtain ⟨rfl, rfl⟩ := Forest.append_injective (eq_of_heq (after.forest.symm.trans targetSame))
      have oldSchedule := scheduled _ _ _ _ _ _ before.erase _ _ before.forest disposes
      exact (SourceScheduledRecomposition.predicate_congr
        (SourceHandlerRequests.forClosing_inserted _)
        (hints_forClosing_inserted _ _)
        (forest_forClosing_inserted front saved)
        (fun closing => Pending outward actions phases world closing (.running waiting))).mpr oldSchedule

/-- Reuse the authenticated captured prefix with another waiting forest.
All lookup side conditions belong to the unchanged prefix. -/
theorem replace_waiting (cut : SourceScheduledNeutral.Cut effect operation contract modes whole saved waiting)
    (next : Forest nextHints) :
    SourceScheduledNeutral.Cut effect operation contract modes (saved.append next) saved next := by
  induction cut with
  | hit known declared => exact .hit known declared
  | plain cut ih => exact .plain ih
  | handler different cut ih => exact .handler different ih
  | cell different cut ih => exact .cell different ih
  | cleanup cut ih => exact .cleanup ih
  | running cut ih => exact .running ih
  | live cut ih => exact .live ih
  | spent cut ih => exact .spent ih

/-- The same captured scope retains its independent guard and owner bound.
A schedule transported at the actual plan layer also supplies the older lower
checker by erasure; there is no second scheduling proof to construct. -/
theorem request_same_capture {beforeHints : Hints beforeScope} {afterHints : Hints afterScope}
    {savedHints : Hints captured} {waitingHints : Hints tail} {nextHints : Hints nextScope}
    {before : Forest beforeHints} {after : Forest afterHints}
    {saved : Forest savedHints} {waiting : Forest waitingHints} {next : Forest nextHints}
    (beforeCut : SourceScheduledNeutral.Cut effect operation contract modes before saved waiting)
    (afterCut : SourceScheduledNeutral.Cut effect operation contract modes after saved next)
    (checked : Local outward actions phases world (.request (effect := effect) (operation := operation)) before)
    (scheduled : contract.dispose = true → Pending outward actions phases world saved.forClosing (.running next)) :
    Local outward actions phases world (.request (effect := effect) (operation := operation)) after := by
  cases checked with
  | request checked oldSchedule =>
      have beforeFound : SourceDependencyCapture.select effect operation (SourceDependencyProjection.project beforeScope) =
          some (.handler (SourceDependencyProjection.project captured) (SourceDependencyProjection.project tail) contract modes) := by
        rw [SourceDependencyProjection.project_select, beforeCut.erase.lookup]
        rfl
      have afterFound : SourceDependencyCapture.select effect operation (SourceDependencyProjection.project afterScope) =
          some (.handler (SourceDependencyProjection.project captured) (SourceDependencyProjection.project nextScope) contract modes) := by
        rw [SourceDependencyProjection.project_select, afterCut.erase.lookup]
        rfl
      refine .request (SourceDependencyChecks.Local.request_selected afterFound ?_ ?_ ?_) ?_
      · exact SourceDependencyCapture.check_capture_iff.mpr
          (SourceHandlerSelection.guard_same_capture beforeFound afterFound
            (SourceDependencyCapture.check_capture_iff.mp checked.request_guard))
      · intro disposes
        simpa only [SourceDependencySchemes.Retained, SourceDependencyProjection.project_forClosing,
          SourceDependencyProjection.project_idempotent, SourceDependencyProjection.project] using
          (scheduled disposes).erase.erase
      · intro disposes
        exact checked.request_owners beforeFound disposes
      · intro targetCaptured targetTail targetSavedHints targetWaitingHints targetContract targetModes targetCut
          targetSaved targetWaiting targetSame disposes
        cases Option.some.inj (afterCut.erase.lookup.symm.trans targetCut.lookup)
        obtain ⟨rfl, rfl⟩ := afterCut.erase.unique targetCut.hints
        obtain ⟨rfl, rfl⟩ := Forest.append_injective (eq_of_heq (afterCut.forest.symm.trans targetSame))
        exact scheduled disposes

/-- Waiting insertion reuses the original disposal schedule. The new finite
exposed-operation interface and transport of affected local code sites rebuild
its Pending proof; neither a replacement Pending proof nor a future state is
a source-admission premise. The local transformer remains an obligation of the
full mutual source-transport proof. -/
theorem waiting_request {wholeHints : Hints wholeScope} {savedHints : Hints captured}
    {waitingHints : Hints tail} {nextHints : Hints nextScope}
    {whole : Forest wholeHints} {saved : Forest savedHints}
    {waiting : Forest waitingHints} {next : Forest nextHints}
    (cut : SourceScheduledNeutral.Cut effect operation contract modes whole saved waiting)
    (changed : SourceScheduledInterpretationInsertion.Insertion frame waiting next)
    (checked : Local outward actions phases world (.request (effect := effect) (operation := operation)) whole)
    (supplied : contract.dispose = true → SourceContextualHints.checkRequirements (.running nextScope)
      (SourceHandlerRequirements.exposed (forClosing savedHints)) = true)
    (transfer : contract.dispose = true →
      ∀ {dependencies oldScope targetScope} {plan : SourceDeclarationPlans.Plan dependencies}
        {oldHints : Hints oldScope} {targetHints : Hints targetScope}
        (old : Forest oldHints) (target : Forest targetHints),
        SourceScheduledPendingSites.Site saved.forClosing (.running waiting) plan old →
        SourceScheduledInterpretationInsertion.Insertion frame old target →
        Local outward actions phases world plan old → Local outward actions phases world plan target) :
    Local outward actions phases world (.request (effect := effect) (operation := operation)) (saved.append next) := by
  apply request_same_capture cut (replace_waiting cut next) checked
  intro disposes
  have original : Pending outward actions phases world saved.forClosing (.running waiting) := by
    cases checked with
    | request guarded scheduled => exact scheduled _ _ _ _ _ _ cut.erase saved waiting cut.forest disposes
  exact SourceScheduledPendingSites.pending_outside original (.running changed) (supplied disposes) (transfer disposes)

end Ash.OneShot.SourceScheduledHandlerRequests

#print axioms Ash.OneShot.SourceScheduledHandlerRequests.hints_forClosing_inserted
#print axioms Ash.OneShot.SourceScheduledHandlerRequests.forest_forClosing_inserted
#print axioms Ash.OneShot.SourceScheduledHandlerRequests.cut_prefix
#print axioms Ash.OneShot.SourceScheduledHandlerRequests.bypassed_request

#print axioms Ash.OneShot.SourceScheduledHandlerRequests.replace_waiting
#print axioms Ash.OneShot.SourceScheduledHandlerRequests.request_same_capture
#print axioms Ash.OneShot.SourceScheduledHandlerRequests.waiting_request
