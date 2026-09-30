import SourceScheduledProviders
import SourceScheduledNeutralChecks
import SourceScheduledPendingSites

/-! Transport the actual retained source schedules through one builtin
provider. All plans, clauses and phases are preserved; interpreter selection
can change to the builtin. No successor invariant is an admission premise. -/
namespace Ash.OneShot.SourceScheduledProviderChecks
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledChecks (Local Pending)
open SourceScheduledProviders (Insertion Split)
open SourceScheduledNeutralChecks (owner_of_parts resume_at dispose_at)

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]

/-- Erased checking is reused; the stronger schedule follows the actual
plan-carrying cut when the request still selects a source handler. -/
theorem request_transport {beforeHints : Hints first} {afterHints : Hints second}
    {before : Forest beforeHints} {after : Forest afterHints}
    (checked : SourceDependencySchemes.Checked outward actions phases world (.request effect operation) first)
    (changed : Insertion identity before after)
    (scheduled : ∀ {captured tail} {savedHints : Hints captured} {waitingHints : Hints tail}
      (saved : Forest savedHints) (waiting : Forest waitingHints) contract modes,
      SourceScheduledNeutral.Cut effect operation contract modes before saved waiting → contract.dispose = true →
      ∀ {nextCaptured nextScope} {closingHints : Hints nextCaptured} {nextHints : Hints nextScope}
        (closing : Forest closingHints) (outside : Forest nextHints),
        Split identity saved.forClosing (.running waiting) closing outside →
        Pending outward actions phases world closing outside) :
    Local outward actions phases world (.request (effect := effect) (operation := operation)) after := by
  refine .request (SourceDependencyProviders.local_transport checked
    (SourceDependencyProviders.insertion_projected changed.erase)) ?_
  intro captured tail savedHints waitingHints contract modes targetCut targetSaved targetWaiting targetSame disposes
  have guard := SourceDependencyCapture.check_capture_iff.mp (SourceDependencySchemes.checked_request checked)
  cases guard with
  | builtin found =>
      obtain ⟨_, nextFound⟩ := changed.erase.builtin found
      cases Option.some.inj (nextFound.symm.trans targetCut.lookup)
  | handler found permission row body closing =>
      obtain ⟨savedHints, waitingHints, selected⟩ := SourcePlannedCuts.of_lookup beforeHints found
      obtain ⟨saved, waiting, cut⟩ := SourceScheduledNeutral.of_cut selected before
      rcases changed.cut cut with nextFound | ⟨_, _, _, _, nextSaved, nextWaiting, nextCut, pieces⟩
      · cases Option.some.inj (nextFound.symm.trans targetCut.lookup)
      · cases Option.some.inj (nextCut.erase.lookup.symm.trans targetCut.lookup)
        obtain ⟨rfl, rfl⟩ := nextCut.erase.unique targetCut.hints
        obtain ⟨rfl, rfl⟩ := Forest.append_injective (eq_of_heq (nextCut.forest.symm.trans targetSame))
        exact scheduled saved waiting _ _ cut disposes _ _ pieces.forClosing

theorem local_transport {plan : SourceDeclarationPlans.Plan dependencies} {hints : Hints scope} {forest : Forest hints}
    (checked : Local outward actions phases world plan forest) {nextHints : Hints nextScope} {next : Forest nextHints}
    (changed : Insertion identity forest next) : Local outward actions phases world plan next := by
  refine (Local.rec
    (motive_1 := fun phases world _ _ _ plan forest _ => ∀ {nextScope} {nextHints : Hints nextScope} (next : Forest nextHints),
      Insertion identity forest next → Local outward actions phases world plan next)
    (motive_2 := fun phases world _ _ _ _ forest outside _ => ∀ {nextScope nextOutside}
      {nextHints : Hints nextScope} {nextOutsideHints : Hints nextOutside}
      (next : Forest nextHints) (nextOutsideForest : Forest nextOutsideHints),
      Split identity forest outside next nextOutsideForest → Pending outward actions phases world next nextOutsideForest)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (t := checked)) next changed
  · intros; exact .pure
  · intros
    rename_i guard scheduled ih nextScope nextHints next changed
    apply request_transport guard changed
    intro captured tail savedHints waitingHints saved waiting contract modes cut disposes nextCaptured nextOutside closingHints outsideHints closing outside pieces
    exact ih _ _ _ _ contract modes cut.erase saved waiting cut.forest disposes closing outside pieces
  · intros
    rename_i found access same restored ih nextScope nextHints next changed
    have cut := owner_of_parts found same
    obtain ⟨_, _, _, _, front, tail, nextCut, pieces⟩ := changed.owner_cut cut
    obtain ⟨result, nextAccess, related⟩ := SourcePlannedProviders.resume_transport changed.erase access
    exact .resume (front := front) (tail := tail) nextCut.found (resume_at nextAccess nextCut.found) nextCut.forest
      (ih _ _ (.inside (pieces.spent_append.prefix _)))
  · intros
    rename_i found access same scheduled ih nextScope nextHints next changed
    have cut := owner_of_parts found same
    obtain ⟨_, _, _, _, front, tail, nextCut, pieces⟩ := changed.owner_cut cut
    obtain ⟨result, nextAccess, related⟩ := SourcePlannedProviders.dispose_transport changed.erase access
    exact .dispose (front := front) (tail := tail) nextCut.found (dispose_at nextAccess nextCut.found) nextCut.forest
      (ih _ _ (.inside ((Insertion.running pieces.spent_append).prefix _)))
  · intros
    rename_i first second ihFirst ihSecond nextScope nextHints next changed
    exact .sequence (ihFirst _ (.plain changed)) (ihSecond _ changed)
  · intros
    rename_i first second ihFirst ihSecond nextScope nextHints next changed
    exact .choice (ihFirst _ changed) (ihSecond _ changed)
  · intros
    rename_i recipes declarations supplied body ih nextScope nextHints next changed
    exact .handler recipes declarations (changed.erase.requirements supplied) (ih _ (.handler changed))
  · intros
    rename_i body completion ihBody ihCompletion nextScope nextHints next changed
    exact .cleanup (ihBody _ (.cleanup changed)) (ihCompletion _ (.running changed))
  · intros
    rename_i body ih nextScope nextHints next changed
    exact .resource (fun identity fresh => ih identity fresh _ (.cell changed))
  · intros
    rename_i nextScope nextOutside nextHints nextOutsideHints next nextOutsideForest changed
    cases changed with
    | inside inserted => cases inserted; exact .cell .nil
    | outside inserted => exact .nil
  · intros
    rename_i code tail ihCode ihTail nextScope nextOutside nextHints nextOutsideHints next nextOutsideForest changed
    cases changed with
    | outside inserted =>
        exact .plain (ihCode _ (inserted.prefix _))
          (ihTail _ _ (.outside inserted))
    | inside inserted => cases inserted with
      | here => exact .cell (.plain code tail)
      | plain inserted =>
          exact .plain (ihCode _ (inserted.suffix _))
            (ihTail _ _ (.inside inserted))
  · intros
    rename_i restHints rest outsideHints outside supplied tail ih nextScope nextOutside nextHints nextOutsideHints next nextOutsideForest changed
    cases changed with
    | outside inserted => exact .handler ((inserted.prefix rest).erase.requirements supplied) (ih _ _ (.outside inserted))
    | inside inserted => cases inserted with
      | here => exact .cell (.handler supplied tail)
      | handler inserted => exact .handler ((inserted.suffix outside).erase.requirements supplied) (ih _ _ (.inside inserted))
  · intros
    rename_i tail ih nextScope nextOutside nextHints nextOutsideHints next nextOutsideForest changed
    cases changed with
    | outside inserted => exact .cell (ih _ _ (.outside inserted))
    | inside inserted => cases inserted with
      | here => exact .cell (.cell tail)
      | cell inserted => exact .cell (ih _ _ (.inside inserted))
  · intros
    rename_i completion tail ihCompletion ihTail nextScope nextOutside nextHints nextOutsideHints next nextOutsideForest changed
    cases changed with
    | outside inserted =>
        exact .cleanup (ihCompletion _ (.running (inserted.prefix _)))
          (ihTail _ _ (.outside inserted))
    | inside inserted => cases inserted with
      | here => exact .cell (.cleanup completion tail)
      | cleanup inserted =>
          exact .cleanup (ihCompletion _ (.running (inserted.suffix _)))
            (ihTail _ _ (.inside inserted))
  · intros
    rename_i tail ih nextScope nextOutside nextHints nextOutsideHints next nextOutsideForest changed
    cases changed with
    | outside inserted => exact .running (ih _ _ (.outside inserted))
    | inside inserted => cases inserted with
      | here => exact .cell (.running tail)
      | running inserted => exact .running (ih _ _ (.inside inserted))
  · intros
    rename_i saved tail ihSaved ihTail nextScope nextOutside nextHints nextOutsideHints next nextOutsideForest changed
    cases changed with
    | outside inserted =>
        exact .live (ihSaved _ _ (.outside (inserted.prefix _)))
          (ihTail _ _ (.outside inserted))
    | inside inserted => cases inserted with
      | here => exact .cell (.live saved tail)
      | live inserted =>
          exact .live (ihSaved _ _ (.outside (inserted.suffix _)))
            (ihTail _ _ (.inside inserted))
  · intros
    rename_i tail ih nextScope nextOutside nextHints nextOutsideHints next nextOutsideForest changed
    cases changed with
    | outside inserted => exact .spent (ih _ _ (.outside inserted))
    | inside inserted => cases inserted with
      | here => exact .cell (.spent tail)
      | spent inserted => exact .spent (ih _ _ (.inside inserted))

/-- Outside insertion rechecks dormant plans against their new receiving scope. -/
theorem pending_outside_transport {hints : Hints scope} {beforeHints : Hints first} {afterHints : Hints second}
    {forest : Forest hints} {before : Forest beforeHints} {after : Forest afterHints}
    (checked : Pending outward actions phases world forest before) (changed : Insertion identity before after) :
    Pending outward actions phases world forest after := by
  have offered := changed.erase.requirements
    (SourceHandlerRequirements.exposed_requirements hints
      (SourceScheduledPendingSites.pending_iff.mp checked).1)
  apply SourceScheduledPendingSites.pending_outside checked changed.shared offered
  intro dependencies oldScope nextScope plan oldHints nextHints old next site inserted supplied
  exact local_transport supplied (Insertion.of_shared inserted)

theorem pending_inside_transport {hints : Hints scope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints} {nextHints : Hints nextScope} {next : Forest nextHints}
    (checked : Pending outward actions phases world forest outside) (changed : Insertion identity forest next) :
    Pending outward actions phases world next outside := by
  apply SourceScheduledPendingSites.pending_transport checked (.inside changed.shared)
    (changed.erase.check outsideHints (SourceScheduledPendingSites.pending_iff.mp checked).1)
  intro dependencies oldScope targetScope plan oldHints targetHints old target site inserted supplied
  exact local_transport supplied (Insertion.of_shared inserted)

/-- Apply the checked provider insertion once for each actual caller cell. -/
theorem provider_local (provided : List Nat) {plan : SourceDeclarationPlans.Plan dependencies}
    {hints : Hints scope} {forest : Forest hints} (checked : Local outward actions phases world plan forest) :
    Local outward actions phases world plan (SourceScheduledProviders.providerForest provided forest) := by
  induction provided with
  | nil => exact checked
  | cons identity rest ih => exact local_transport ih .here

end Ash.OneShot.SourceScheduledProviderChecks

#print axioms Ash.OneShot.SourceScheduledProviderChecks.request_transport
#print axioms Ash.OneShot.SourceScheduledProviderChecks.local_transport
#print axioms Ash.OneShot.SourceScheduledProviderChecks.pending_outside_transport
#print axioms Ash.OneShot.SourceScheduledProviderChecks.pending_inside_transport

#print axioms Ash.OneShot.SourceScheduledProviderChecks.provider_local
