import SourceDependencyProviders
import SourcePlannedChecks

/-! Provider insertion preserves actual declaration plans and contextual
invocation checks. The dependency transport supplies the erased checks; exact
cuts retain the source schedule when a request still selects a handler. -/
namespace Ash.OneShot.SourcePlannedProviders
open SourceContextualHints (Hints)
open SourceContextualInvocationHints (forClosing)
open SourceContextualHintChecking (Compatible check_iff)
open SourcePlannedChecks (Local Pending)
open SourceProviderInsertion (Insertion Split)

theorem compatible (changed : Insertion identity before after)
    (checked : Compatible before .nil) : Compatible after .nil :=
  (check_iff _).mp (changed.check .nil ((check_iff _).mpr checked))

theorem resume_transport (changed : Insertion identity before after)
    (admitted : SourceContextualInvocations.Resume actions phases owner before restored) :
    ∃ next, SourceContextualInvocations.Resume actions phases owner after next ∧
      Insertion identity restored.hints next.hints := by
  cases admitted with
  | checked found access supplied =>
      obtain ⟨next, foundNext, related⟩ := changed.find_owner found
      obtain ⟨_, _, _, nextAccess, _⟩ := changed.resume_access access
      refine ⟨_, .checked foundNext (SourceContextualInvocations.resume_access foundNext ?_)
        (compatible related.resumed supplied), related.resumed⟩
      rw [SourceDependencyCapture.check_resume_iff.mpr nextAccess]
      rfl

theorem dispose_transport (changed : Insertion identity before after)
    (admitted : SourceContextualInvocations.Dispose outward actions phases owner before scheduled) :
    ∃ next, SourceContextualInvocations.Dispose outward actions phases owner after next ∧
      Insertion identity scheduled.hints next.hints := by
  cases admitted with
  | checked found access supplied =>
      obtain ⟨next, foundNext, related⟩ := changed.find_owner found
      obtain ⟨_, _, _, nextAccess, _⟩ := changed.dispose_access access
      refine ⟨_, .checked foundNext (SourceContextualInvocations.dispose_access foundNext ?_)
        (compatible related.disposed supplied), related.disposed⟩
      rw [SourceDependencyCapture.check_dispose_iff.mpr nextAccess]
      rfl

/-- The source guard is transported by the lower checker. Scheduling retains
an exact annotated cut, or becomes vacuous when the request selects a builtin. -/
theorem request_transport {before : Hints first} {after : Hints second}
    (checked : SourceDependencySchemes.Checked outward actions phases world (.request effect operation) first)
    (changed : Insertion identity before after)
    (scheduled : ∀ {captured tail} (saved : Hints captured) (waiting : Hints tail) contract modes,
      SourcePlannedCuts.Cut effect operation contract modes before saved waiting → contract.dispose = true →
      ∀ {nextCaptured nextOutside} (closing : Hints nextCaptured) (outside : Hints nextOutside),
        Split identity (forClosing saved) (.running waiting) closing outside →
        Pending outward actions phases world closing outside) :
    Local outward actions phases world (.request (effect := effect) (operation := operation)) after := by
  refine .request (SourceDependencyProviders.local_transport checked
    (SourceDependencyProviders.insertion_projected changed)) ?_
  intro captured tail saved waiting contract modes same actual disposes
  have guard := SourceDependencyCapture.check_capture_iff.mp (SourceDependencySchemes.checked_request checked)
  cases guard with
  | builtin found =>
      obtain ⟨_, nextFound⟩ := changed.builtin found
      cases Option.some.inj (nextFound.symm.trans actual)
  | handler found permission row body closing =>
      obtain ⟨beforeSaved, beforeWaiting, cut⟩ := SourcePlannedCuts.of_lookup before found
      rcases changed.cut cut with nextFound | ⟨_, _, nextSaved, nextWaiting, nextCut, pieces⟩
      · cases Option.some.inj (nextFound.symm.trans actual)
      · cases Option.some.inj (nextCut.lookup.symm.trans actual)
        obtain ⟨rfl, rfl⟩ := nextCut.unique same
        apply scheduled beforeSaved beforeWaiting _ _ cut disposes
        cases pieces with
        | inside inserted => exact .inside inserted.forClosing
        | outside inserted => exact .outside (.running inserted)

theorem local_transport {plan : SourceDeclarationPlans.Plan dependencies} {hints : Hints scope}
    (checked : Local outward actions phases world plan hints) {next : Hints nextScope}
    (changed : Insertion identity hints next) : Local outward actions phases world plan next := by
  refine (Local.rec
    (motive_1 := fun phases world _ _ plan hints _ => ∀ {nextScope} (next : Hints nextScope),
      Insertion identity hints next → Local outward actions phases world plan next)
    (motive_2 := fun phases world _ _ hints outside _ => ∀ {nextScope nextOutside}
      (next : Hints nextScope) (nextOutsideHints : Hints nextOutside),
      Split identity hints outside next nextOutsideHints → Pending outward actions phases world next nextOutsideHints)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (t := checked)) next changed
  · intros; exact .pure
  · intros
    rename_i guard scheduled ih nextScope next changed
    apply request_transport guard changed
    intro captured tail saved waiting contract modes cut disposes nextCaptured nextOutside closing outside pieces
    exact ih _ _ saved waiting contract modes cut.hints cut.lookup disposes closing outside pieces
  · intros
    rename_i access restored ih nextScope next changed
    obtain ⟨afterNext, accessNext, related⟩ := resume_transport changed access
    exact .resume accessNext (ih _ _ (.inside related))
  · intros
    rename_i access scheduled ih nextScope next changed
    obtain ⟨afterNext, accessNext, related⟩ := dispose_transport changed access
    exact .dispose accessNext (ih _ _ (.inside related))
  · intros
    rename_i first second ihFirst ihSecond nextScope next changed
    exact .sequence (ihFirst _ (.plain changed)) (ihSecond _ changed)
  · intros
    rename_i first second ihFirst ihSecond nextScope next changed
    exact .choice (ihFirst _ changed) (ihSecond _ changed)
  · intros
    rename_i recipes declarations supplied body ih nextScope next changed
    exact .handler recipes declarations (changed.requirements supplied) (ih _ (.handler changed))
  · intros
    rename_i body completion ihBody ihCompletion nextScope next changed
    exact .cleanup (ihBody _ (.cleanup changed)) (ihCompletion _ (.running changed))
  · intros
    rename_i body ih nextScope next changed
    exact .resource (fun identity fresh => ih identity fresh _ (.cell changed))
  · intros
    rename_i nextScope nextOutside next nextOutsideHints changed
    cases changed with
    | inside inserted => cases inserted; exact .cell .nil
    | outside inserted => exact .nil
  · intros
    rename_i code tail ihCode ihTail nextScope nextOutside next nextOutsideHints changed
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
    rename_i tail ih nextScope nextOutside next nextOutsideHints changed
    cases changed with
    | outside inserted => exact .handler (ih _ _ (.outside inserted))
    | inside inserted => cases inserted with
      | here => exact .cell (.handler tail)
      | handler inserted => exact .handler (ih _ _ (.inside inserted))
  · intros
    rename_i tail ih nextScope nextOutside next nextOutsideHints changed
    cases changed with
    | outside inserted => exact .cell (ih _ _ (.outside inserted))
    | inside inserted => cases inserted with
      | here => exact .cell (.cell tail)
      | cell inserted => exact .cell (ih _ _ (.inside inserted))
  · intros
    rename_i completion tail ihCompletion ihTail nextScope nextOutside next nextOutsideHints changed
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
    rename_i tail ih nextScope nextOutside next nextOutsideHints changed
    cases changed with
    | outside inserted => exact .running (ih _ _ (.outside inserted))
    | inside inserted => cases inserted with
      | here => exact .cell (.running tail)
      | running inserted => exact .running (ih _ _ (.inside inserted))
  · intros
    rename_i saved tail ihSaved ihTail nextScope nextOutside next nextOutsideHints changed
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
    rename_i tail ih nextScope nextOutside next nextOutsideHints changed
    cases changed with
    | outside inserted => exact .spent (ih _ _ (.outside inserted))
    | inside inserted => cases inserted with
      | here => exact .cell (.spent tail)
      | spent inserted => exact .spent (ih _ _ (.inside inserted))

/-- Adding an outside provider also preserves dormant stored plans. -/
theorem pending_outside_transport {hints : Hints scope} {outsideHints : Hints outside}
    (checked : Pending outward actions phases world hints outsideHints) {next : Hints nextScope}
    (changed : Insertion identity outsideHints next) : Pending outward actions phases world hints next := by
  induction hints generalizing outside nextScope with
  | nil => exact .nil
  | plain rest ih => cases checked with
    | plain code tail => exact .plain (local_transport code (changed.prefix rest)) (ih tail changed)
  | handler required rest ih => cases checked with | handler tail => exact .handler (ih tail changed)
  | cell rest ih => cases checked with | cell tail => exact .cell (ih tail changed)
  | cleanup rest ih => cases checked with
    | cleanup callback tail => exact .cleanup (local_transport callback (.running (changed.prefix rest))) (ih tail changed)
  | running rest ih => cases checked with | running tail => exact .running (ih tail changed)
  | live saved rest ihSaved ihRest => cases checked with
    | live inside tail => exact .live (ihSaved inside (changed.prefix rest)) (ihRest tail changed)
  | spent rest ih => cases checked with | spent tail => exact .spent (ih tail changed)

theorem pending_inside_transport {hints : Hints scope} {outsideHints : Hints outside}
    (checked : Pending outward actions phases world hints outsideHints) {next : Hints nextScope}
    (changed : Insertion identity hints next) : Pending outward actions phases world next outsideHints := by
  induction changed with
  | here => exact .cell checked
  | plain changed ih => cases checked with
    | plain code tail => exact .plain (local_transport code (changed.suffix outsideHints)) (ih tail)
  | handler changed ih => cases checked with | handler tail => exact .handler (ih tail)
  | cell changed ih => cases checked with | cell tail => exact .cell (ih tail)
  | cleanup changed ih => cases checked with
    | cleanup callback tail => exact .cleanup (local_transport callback (.running (changed.suffix outsideHints))) (ih tail)
  | running changed ih => cases checked with | running tail => exact .running (ih tail)
  | live changed ih => cases checked with
    | live saved tail => exact .live (pending_outside_transport saved (changed.suffix outsideHints)) (ih tail)
  | spent changed ih => cases checked with | spent tail => exact .spent (ih tail)

/-- Interpret the local-provider annotation in the actual caller order. -/
def providerHints (provided : List Nat) (hints : Hints scope) :
    Hints (SourceContextualRequirements.providerScope provided scope) :=
  match provided with
  | [] => hints
  | identity :: rest => .cell (identity := identity) (providerHints rest hints)

theorem provider_local (provided : List Nat) {plan : SourceDeclarationPlans.Plan dependencies} {hints : Hints scope}
    (checked : Local outward actions phases world plan hints) :
    Local outward actions phases world plan (providerHints provided hints) := by
  induction provided with
  | nil => exact checked
  | cons identity rest ih => exact local_transport ih .here

/-- Reuse the operation capability at the current annotated receiving scope. -/
theorem request_from_capability {hints : Hints scope}
    (capability : SourceContextualClauses.RequestCapability effect operation scope) :
    Local outward actions phases world (.request (effect := effect) (operation := operation)) hints := by
  refine .request (SourceContextualRequirements.request_checked capability) ?_
  intro captured tail saved waiting contract modes same actual disposes
  cases capability with
  | builtin found => cases Option.some.inj (found.symm.trans actual)
  | handler found resumes rows bodies =>
      cases Option.some.inj (found.symm.trans actual)
      simp [resumes] at disposes

end Ash.OneShot.SourcePlannedProviders

#print axioms Ash.OneShot.SourcePlannedProviders.compatible
#print axioms Ash.OneShot.SourcePlannedProviders.resume_transport
#print axioms Ash.OneShot.SourcePlannedProviders.dispose_transport
#print axioms Ash.OneShot.SourcePlannedProviders.request_transport
#print axioms Ash.OneShot.SourcePlannedProviders.local_transport
#print axioms Ash.OneShot.SourcePlannedProviders.pending_outside_transport
#print axioms Ash.OneShot.SourcePlannedProviders.pending_inside_transport

#print axioms Ash.OneShot.SourcePlannedProviders.provider_local

#print axioms Ash.OneShot.SourcePlannedProviders.request_from_capability
