import SourcePlannedCuts
import SourcePlannedNeutralFrames

/-! Transport the structural source checks through insertion of pure pending
frames, pure callbacks and spent markers, preserving the selected handler and
rebuilding its closing check from
the retained annotated pieces. -/
namespace Ash.OneShot.SourcePlannedNeutralChecks
open SourceContextualHints (Hints)
open SourceDependencyCapture (Scope)
open SourceDependencyProjection (project project_select project_forClosing project_idempotent)
open SourceContextualInvocationHints (forClosing)
open SourcePlannedChecks (Local Pending)
open SourcePlannedNeutralFrames (Expansion)
open SourceDependencyOwners (PendingWithin)

theorem pending_owners_project (checked : PendingWithin world owned scope) :
    PendingWithin world owned (project scope) := by
  induction checked with
  | nil => exact .nil
  | plain code rest ih => exact .plain code ih
  | handler rest ih => exact .handler ih
  | cell rest ih => exact .cell ih
  | cleanup rest ih => exact .cleanup ih
  | running rest ih => exact .running ih
  | live saved rest ihSaved ihRest => exact .live ihSaved ihRest
  | spent rest ih => exact ih

variable [certification : SourcePlannedChecks.DeclarationPolicy]

/-- Reconstruct a request from its original source guard and the recursively
transported callback checks. Each schedule is tied to the exact structural cut;
no whole successor judgment is a premise. -/
theorem request_transport {before : Hints first} {after : Hints second}
    (checked : SourceDependencySchemes.Checked outward actions phases world (.request effect operation) first)
    (changed : Expansion before after)
    (scheduled : ∀ {captured tail} (saved : Hints captured) (waiting : Hints tail) contract modes,
      SourcePlannedCuts.Cut effect operation contract modes before saved waiting → contract.dispose = true →
      ∀ {nextCaptured nextOutside} (closing : Hints nextCaptured) (outside : Hints nextOutside),
        Expansion (forClosing saved) closing → Expansion (.running waiting) outside →
        Pending outward actions phases world closing outside) :
    Local outward actions phases world (.request (effect := effect) (operation := operation)) after := by
  have guard := SourceDependencyCapture.check_capture_iff.mp (SourceDependencySchemes.checked_request checked)
  cases guard with
  | builtin found => exact SourcePlannedRecomposition.builtin_request (SourcePlannedCuts.builtin_expand changed found)
  | handler found permission row body closing =>
      rename_i captured tail contract modes footprint family
      obtain ⟨saved, waiting, cut⟩ := SourcePlannedCuts.of_lookup before found
      obtain ⟨nextCaptured, nextTail, nextSaved, nextWaiting, nextCut, inside, outside⟩ := SourcePlannedCuts.expand changed cut
      have scheduledNext : ∀ disposes : contract.dispose = true,
          Pending outward actions phases world (forClosing nextSaved) (.running nextWaiting) := by
        intro disposes
        exact scheduled saved waiting _ _ cut disposes _ _ inside.forClosing (.running outside)
      have nextGuard : SourceDependencyCapture.CaptureGuard outward second effect operation :=
        .handler nextCut.lookup (inside.held ▸ permission) (inside.held ▸ row) (inside.held ▸ body)
          (fun disposes => SourceDependencyCapture.check_closing_iff.mp (by
            rw [← inside.closing_check]
            exact SourceDependencyCapture.check_closing_iff.mpr (closing disposes)))
      have selected : SourceDependencyCapture.select effect operation (project second) =
          some (.handler (project nextCaptured) (project nextTail) contract modes) := by
        rw [project_select, nextCut.lookup]
        rfl
      refine .request (SourceDependencyChecks.Local.request_selected selected ?_ ?_ ?_) ?_
      · simpa only [SourceDependencyProjection.project_checkCapture] using SourceDependencyCapture.check_capture_iff.mpr nextGuard
      · intro disposes
        simpa only [SourceDependencySchemes.Retained, project_forClosing, project_idempotent, project] using
          (scheduledNext disposes).erase
      · intro disposes
        have bounded := inside.pending_owners (SourceDependencySchemes.checked_request_owners checked found disposes)
        rw [inside.owners] at bounded
        simpa only [SourceDependencySchemes.owners_project] using pending_owners_project bounded
      · intro captured tail saved waiting contract modes same actual disposes
        cases Option.some.inj (nextCut.lookup.symm.trans actual)
        obtain ⟨rfl, rfl⟩ := nextCut.unique same
        exact scheduledNext disposes

theorem local_transport {plan : SourceDeclarationPlans.Plan dependencies} {hints : Hints scope}
    (checked : Local outward actions phases world plan hints) {next : Hints nextScope}
    (changed : Expansion hints next) : Local outward actions phases world plan next := by
  refine (Local.rec
    (motive_1 := fun phases world _ _ plan hints _ => ∀ {nextScope} (next : Hints nextScope),
      Expansion hints next → Local outward actions phases world plan next)
    (motive_2 := fun phases world _ _ hints outside _ => ∀ {nextScope nextOutside}
      (next : Hints nextScope) (nextOutsideHints : Hints nextOutside),
      Expansion hints next → Expansion outside nextOutsideHints →
        Pending outward actions phases world next nextOutsideHints)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (t := checked)) next changed
  · intros; exact .pure
  · intros
    rename_i scope hints effect operation guard scheduled ih nextScope next expanded
    apply request_transport guard expanded
    intro captured tail saved waiting contract modes cut disposes nextCaptured nextOutside closing outside insideExpansion outsideExpansion
    exact ih _ _ saved waiting contract modes cut.hints cut.lookup disposes closing outside insideExpansion outsideExpansion
  · intros
    rename_i owner hints after access restored ih nextScope next expanded
    obtain ⟨afterNext, accessNext, related⟩ := expanded.resume access
    exact .resume accessNext (ih _ _ related .refl)
  · intros
    rename_i owner hints after access scheduled ih nextScope next expanded
    obtain ⟨afterNext, accessNext, related⟩ := expanded.dispose access
    exact .dispose accessNext (ih _ _ related .refl)
  · intros
    rename_i beforeDep afterDep scope before after hints first second ihFirst ihSecond nextScope next expanded
    exact .sequence (ihFirst _ (.plain expanded)) (ihSecond _ expanded)
  · intros
    rename_i firstDep secondDep scope first second hints left right ihLeft ihRight nextScope next expanded
    exact .choice (ihLeft _ expanded) (ihRight _ expanded)
  · intros
    rename_i clauses families required plans scope hints dependencies code effect table recipes declarations supplied body ih nextScope next expanded
    exact .handler recipes declarations (expanded.requirements ▸ supplied) (ih _ (.handler expanded))
  · intros
    rename_i callbackDep callback scope hints dependencies code needs body completion ihBody ihCompletion nextScope next expanded
    exact .cleanup (ihBody _ (.cleanup expanded)) (ihCompletion _ (.running expanded))
  · intros
    rename_i family scope hints code body ih nextScope next expanded
    exact .resource (fun identity fresh => ih identity fresh _ (.cell expanded))
  · intros
    rename_i targetScope targetOutside target targetOutsideHints expanded outsideExpanded
    induction target <;> cases expanded
    all_goals first
      | exact .nil
      | (rename_i ihExtra extra; exact .plain (plan := .pure) .pure (ihExtra extra))
      | (rename_i ihHistory history; exact .spent (ihHistory history))
      | (rename_i ihCompletion completion; exact .cleanup (plan := .pure) .pure (ihCompletion completion))
  · intros
    rename_i restPlan code tail ihCode ihTail targetScope targetOutside target targetOutsideHints expanded outsideExpanded
    induction target <;> cases expanded
    all_goals first
      | (rename_i ihExtra extra; exact .plain (plan := .pure) .pure (ihExtra extra))
      | (rename_i ihHistory history; exact .spent (ihHistory history))
      | (rename_i ihCompletion completion; exact .cleanup (plan := .pure) .pure (ihCompletion completion))
      | (apply Pending.plain (plan := restPlan)
         · apply ihCode
           exact Expansion.append (by first | exact .refl | assumption) outsideExpanded
         · exact ihTail _ _ (by first | exact .refl | assumption) outsideExpanded)
  · intros
    rename_i required tail ih targetScope targetOutside target targetOutsideHints expanded outsideExpanded
    induction target <;> cases expanded
    all_goals first
      | (rename_i ihExtra extra; exact .plain (plan := .pure) .pure (ihExtra extra))
      | (rename_i ihHistory history; exact .spent (ihHistory history))
      | (rename_i ihCompletion completion; exact .cleanup (plan := .pure) .pure (ihCompletion completion))
      | exact .handler (ih _ _ (by first | exact .refl | assumption) outsideExpanded)
  · intros
    rename_i tail ih targetScope targetOutside target targetOutsideHints expanded outsideExpanded
    induction target <;> cases expanded
    all_goals first
      | (rename_i ihExtra extra; exact .plain (plan := .pure) .pure (ihExtra extra))
      | (rename_i ihHistory history; exact .spent (ihHistory history))
      | (rename_i ihCompletion completion; exact .cleanup (plan := .pure) .pure (ihCompletion completion))
      | exact .cell (ih _ _ (by first | exact .refl | assumption) outsideExpanded)
  · intros
    rename_i restPlan completion tail ihCompletion ihTail targetScope targetOutside target targetOutsideHints expanded outsideExpanded
    induction target <;> cases expanded
    all_goals first
      | (rename_i ihExtra extra; exact .plain (plan := .pure) .pure (ihExtra extra))
      | (rename_i ihHistory history; exact .spent (ihHistory history))
      | (rename_i ihCompletion completion; exact .cleanup (plan := .pure) .pure (ihCompletion completion))
      | (apply Pending.cleanup (plan := restPlan)
         · apply ihCompletion
           exact .running (Expansion.append (by first | exact .refl | assumption) outsideExpanded)
         · exact ihTail _ _ (by first | exact .refl | assumption) outsideExpanded)
  · intros
    rename_i tail ih targetScope targetOutside target targetOutsideHints expanded outsideExpanded
    induction target <;> cases expanded
    all_goals first
      | (rename_i ihExtra extra; exact .plain (plan := .pure) .pure (ihExtra extra))
      | (rename_i ihHistory history; exact .spent (ihHistory history))
      | (rename_i ihCompletion completion; exact .cleanup (plan := .pure) .pure (ihCompletion completion))
      | exact .running (ih _ _ (by first | exact .refl | assumption) outsideExpanded)
  · intros
    rename_i saved tail ihSaved ihTail targetScope targetOutside target targetOutsideHints expanded outsideExpanded
    induction target <;> cases expanded
    all_goals first
      | (rename_i ihExtra extra; exact .plain (plan := .pure) .pure (ihExtra extra))
      | (rename_i ihHistory history; exact .spent (ihHistory history))
      | (rename_i ihCompletion completion; exact .cleanup (plan := .pure) .pure (ihCompletion completion))
      | exact .live (ihSaved _ _ .refl (Expansion.append (by first | exact .refl | assumption) outsideExpanded))
          (ihTail _ _ (by first | exact .refl | assumption) outsideExpanded)
  · intros
    rename_i tail ih targetScope targetOutside target targetOutsideHints expanded outsideExpanded
    induction target <;> cases expanded
    all_goals first
      | (rename_i ihExtra extra; exact .plain (plan := .pure) .pure (ihExtra extra))
      | (rename_i ihHistory history; exact .spent (ihHistory history))
      | (rename_i ihCompletion completion; exact .cleanup (plan := .pure) .pure (ihCompletion completion))
      | exact .spent (ih _ _ (by first | exact .refl | assumption) outsideExpanded)

/-- Reuse local transport for every retained expression and callback while
only its outside receiving scope expands. -/
theorem pending_outside_transport {hints : Hints scope} {before : Hints first} {after : Hints second}
    (checked : Pending outward actions phases world hints before) (changed : Expansion before after) :
    Pending outward actions phases world hints after := by
  refine (Pending.rec
    (motive_1 := fun _ _ _ _ _ _ _ => True)
    (motive_2 := fun phases world _ _ hints outside _ => ∀ {nextScope} (next : Hints nextScope),
      Expansion outside next → Pending outward actions phases world hints next)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (t := checked)) after changed
  · intros; exact .nil
  · intros
    rename_i restPlan code tail ihCode ihTail targetScope target expanded
    exact .plain (local_transport code (expanded.prefix _)) (ihTail _ expanded)
  · intros
    rename_i required tail ih targetScope target expanded
    exact .handler (ih _ expanded)
  · intros
    rename_i tail ih targetScope target expanded
    exact .cell (ih _ expanded)
  · intros
    rename_i restPlan completion tail ihCompletion ihTail targetScope target expanded
    exact .cleanup (local_transport completion (.running (expanded.prefix _))) (ihTail _ expanded)
  · intros
    rename_i tail ih targetScope target expanded
    exact .running (ih _ expanded)
  · intros
    rename_i saved tail ihSaved ihTail targetScope target expanded
    exact .live (ihSaved _ (expanded.prefix _)) (ihTail _ expanded)
  · intros
    rename_i tail ih targetScope target expanded
    exact .spent (ih _ expanded)

/-- Transport both retained frames and their receiving scope. Extra frames
carry pure plans or callbacks; existing frames keep their original plans. -/
theorem pending_transport {before : Hints first} {after : Hints second}
    {outsideBefore : Hints firstOutside} {outsideAfter : Hints secondOutside}
    (checked : Pending outward actions phases world before outsideBefore)
    (inside : Expansion before after) (outside : Expansion outsideBefore outsideAfter) :
    Pending outward actions phases world after outsideAfter := by
  have retained := pending_outside_transport checked outside
  clear checked
  induction inside with
  | refl => exact retained
  | extra changed ih => exact .plain (plan := .pure) .pure (ih retained)
  | completion changed ih => exact .cleanup (plan := .pure) .pure (ih retained)
  | history changed ih => exact .spent (ih retained)
  | plain changed ih => cases retained with
    | plain code rest => exact .plain (local_transport code (changed.append .refl)) (ih rest)
  | handler changed ih => cases retained with | handler rest => exact .handler (ih rest)
  | cell changed ih => cases retained with | cell rest => exact .cell (ih rest)
  | cleanup changed ih => cases retained with
    | cleanup completion rest => exact .cleanup (local_transport completion (.running (changed.append .refl))) (ih rest)
  | running changed ih => cases retained with | running rest => exact .running (ih rest)
  | live changed ih => cases retained with
    | live saved rest => exact .live (pending_outside_transport saved (changed.append .refl)) (ih rest)
  | spent changed ih => cases retained with | spent rest => exact .spent (ih rest)

/-- A pure, effect-free callback may wrap any locally admitted body. It is
retained on capture and checked under running protection on completion. -/
theorem pure_cleanup {plan : SourceDeclarationPlans.Plan dependencies} {hints : Hints scope}
    (body : Local outward actions phases world plan hints) :
    Local outward actions phases world (.cleanup (needs := []) .pure plan) hints :=
  .cleanup (local_transport body (.completion .refl)) .pure

end Ash.OneShot.SourcePlannedNeutralChecks

#print axioms Ash.OneShot.SourcePlannedNeutralChecks.request_transport

#print axioms Ash.OneShot.SourcePlannedNeutralChecks.local_transport

#print axioms Ash.OneShot.SourcePlannedNeutralChecks.pending_outside_transport
#print axioms Ash.OneShot.SourcePlannedNeutralChecks.pending_transport

#print axioms Ash.OneShot.SourcePlannedNeutralChecks.pure_cleanup

#print axioms Ash.OneShot.SourcePlannedNeutralChecks.pending_owners_project
