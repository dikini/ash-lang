import SourceScheduledSavedPlans

/-! Invocation rules below arbitrary clause-local scopes. The caller prefix
may contain handlers, resources, cleanup actions and dormant captures. Saved
code is rechecked at its actual receiving suffix; head-only recipe proofs do
not justify transporting it through an arbitrary new interpretation. -/
namespace Ash.OneShot.SourceScheduledScopedInvocations
open ScopedExpressions ProtectionContracts
open SourceContextualHints (Hints)
open SourceContextualClauses (RequestCapability)
open SourceDependencyCapture (select check_capture_iff)
open SourceRetainedPlans (Forest)
open SourceScheduledChecks (Local Pending)
open SourceScheduledNeutral (OwnerCut)
open SourceScheduledRecomposition (pending_append_iff pending_outside_nil)
open SourceContextualInvocationHints (Selection selected_cut)
open SourceContextualInvocations (Resume Dispose)
open SourceContextualHintChecking (Compatible)
open OwnerPhaseTransitions (spend)

variable [admission : SourceScheduledChecks.DeclarationPolicy] [certification : SourcePlannedChecks.DeclarationPolicy]

/-- A resumptive operation capability suffices at its actual receiving scope.
No synthetic live owner or pending sequence is needed for this rule. -/
theorem request_from_capability {hints : Hints scope} {forest : Forest hints}
    (capability : RequestCapability effect operation scope) :
    Local outward actions phases world (.request (effect := effect) (operation := operation)) forest := by
  refine .request (SourceContextualRequirements.request_checked capability) ?_
  intro captured tail savedHints tailHints contract modes cut savedForest tailForest same disposes
  cases capability with
  | builtin found => cases Option.some.inj (found.symm.trans cut.lookup)
  | handler found resumes rows bodies =>
      cases Option.some.inj (found.symm.trans cut.lookup)
      simp [resumes] at disposes

variable {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
  {savedHints : Hints savedScope} {tailHints : Hints tailScope}
  {whole : Forest wholeHints} {front : Forest frontHints}
  {saved : Forest savedHints} {tail : Forest tailHints}

theorem pending_caller_iff :
    Pending outward actions phases world (front.append (.spent (owner := owner) tail)) .nil ↔
      Pending outward actions phases world front (.spent (owner := owner) tail) ∧
      Pending outward actions phases world tail .nil := by
  rw [pending_append_iff, pending_outside_nil]
  constructor
  · rintro ⟨before, after⟩
    cases after with | spent checked => exact ⟨before, checked⟩
  · rintro ⟨before, after⟩
    exact ⟨before, .spent after⟩

/-- The restored computation checks three structural pieces at the spent
phase: the saved segment, the caller prefix and the original waiting tail. -/
theorem pending_resume_iff :
    Pending outward actions phases world (saved.append (front.append (.spent (owner := owner) tail))) .nil ↔
      Pending outward actions phases world saved (front.append (.spent (owner := owner) tail)) ∧
      Pending outward actions phases world front (.spent (owner := owner) tail) ∧
      Pending outward actions phases world tail .nil := by
  rw [pending_append_iff, pending_outside_nil, pending_caller_iff]

theorem pending_dispose_iff :
    Pending outward actions phases world
      (saved.forClosing.append (.running (front.append (.spent (owner := owner) tail)))) .nil ↔
      Pending outward actions phases world saved.forClosing (.running (front.append (.spent (owner := owner) tail))) ∧
      Pending outward actions phases world front (.spent (owner := owner) tail) ∧
      Pending outward actions phases world tail .nil := by
  rw [pending_append_iff, pending_outside_nil]
  constructor
  · rintro ⟨closing, waiting⟩
    cases waiting with | running checked => exact ⟨closing, pending_caller_iff.mp checked⟩
  · rintro ⟨closing, before, after⟩
    exact ⟨closing, .running (pending_caller_iff.mpr ⟨before, after⟩)⟩

/-- Necessity and sufficiency for the actual selected owner, without restricting
the caller prefix to the inert frames supported by the older recipe grammar. -/
theorem resume_iff (cut : OwnerCut owner whole front saved tail) :
    Local outward actions phases world (.invoke (key := ⟨owner, .resume⟩)) whole ↔
      Resume actions phases owner wholeHints
        (Selection.resumed owner ⟨⟨frontScope, savedScope, tailScope⟩, frontHints, savedHints, tailHints⟩) ∧
      Pending outward actions (spend phases owner) world saved (front.append (.spent (owner := owner) tail)) ∧
      Pending outward actions (spend phases owner) world front (.spent (owner := owner) tail) ∧
      Pending outward actions (spend phases owner) world tail .nil := by
  constructor
  · intro checked
    cases checked with
    | resume actual access actualSame restored =>
        cases Option.some.inj (actual.symm.trans cut.found)
        obtain ⟨frontSame, liveSame⟩ := Forest.append_injective (eq_of_heq (actualSame.symm.trans cut.forest))
        obtain ⟨savedSame, tailSame⟩ := Forest.live.inj liveSame
        cases frontSame
        cases savedSame
        cases tailSame
        exact ⟨access, pending_resume_iff.mp restored⟩
  · rintro ⟨access, inside, before, after⟩
    exact .resume cut.found access cut.forest (pending_resume_iff.mpr ⟨inside, before, after⟩)

theorem dispose_iff (cut : OwnerCut owner whole front saved tail) :
    Local outward actions phases world (.invoke (key := ⟨owner, .dispose⟩)) whole ↔
      Dispose outward actions phases owner wholeHints
        (Selection.disposed owner ⟨⟨frontScope, savedScope, tailScope⟩, frontHints, savedHints, tailHints⟩) ∧
      Pending outward actions (spend phases owner) world saved.forClosing (.running (front.append (.spent (owner := owner) tail))) ∧
      Pending outward actions (spend phases owner) world front (.spent (owner := owner) tail) ∧
      Pending outward actions (spend phases owner) world tail .nil := by
  constructor
  · intro checked
    cases checked with
    | dispose actual access actualSame scheduled =>
        cases Option.some.inj (actual.symm.trans cut.found)
        obtain ⟨frontSame, liveSame⟩ := Forest.append_injective (eq_of_heq (actualSame.symm.trans cut.forest))
        obtain ⟨savedSame, tailSame⟩ := Forest.live.inj liveSame
        cases frontSame
        cases savedSame
        cases tailSame
        exact ⟨access, pending_dispose_iff.mp scheduled⟩
  · rintro ⟨access, closing, before, after⟩
    exact .dispose cut.found access cut.forest (pending_dispose_iff.mpr ⟨closing, before, after⟩)

theorem resume_from_parts (cut : OwnerCut owner whole front saved tail)
    (known : actions owner = some rights) (permission : rights.resume = true)
    (available : phases owner = .available)
    (inside : Pending outward actions (spend phases owner) world saved (front.append (.spent (owner := owner) tail)))
    (before : Pending outward actions (spend phases owner) world front (.spent (owner := owner) tail))
    (after : Pending outward actions (spend phases owner) world tail .nil)
    (compatible : Compatible (savedHints.append (frontHints.append (.spent (owner := owner) tailHints))) .nil) :
    Local outward actions phases world (.invoke (key := ⟨owner, .resume⟩)) whole :=
  (resume_iff cut).mpr ⟨.checked cut.found (.checked (selected_cut cut.found) known permission available) compatible,
    inside, before, after⟩

theorem dispose_from_parts (cut : OwnerCut owner whole front saved tail)
    (known : actions owner = some rights) (permission : rights.dispose = true)
    (available : phases owner = .available) (unprotected : savedScope.held = false)
    (route : SourceRecursiveRoutes.Closing outward savedScope.shape [] [])
    (closing : Pending outward actions (spend phases owner) world saved.forClosing (.running (front.append (.spent (owner := owner) tail))))
    (before : Pending outward actions (spend phases owner) world front (.spent (owner := owner) tail))
    (after : Pending outward actions (spend phases owner) world tail .nil)
    (compatible : Compatible ((SourceContextualInvocationHints.forClosing savedHints).append
      (.running (frontHints.append (.spent (owner := owner) tailHints)))) .nil) :
    Local outward actions phases world (.invoke (key := ⟨owner, .dispose⟩)) whole :=
  (dispose_iff cut).mpr ⟨.checked cut.found
    (.checked (selected_cut cut.found) known permission available unprotected route) compatible,
    closing, before, after⟩

end Ash.OneShot.SourceScheduledScopedInvocations

#print axioms Ash.OneShot.SourceScheduledScopedInvocations.pending_caller_iff
#print axioms Ash.OneShot.SourceScheduledScopedInvocations.pending_resume_iff
#print axioms Ash.OneShot.SourceScheduledScopedInvocations.pending_dispose_iff
#print axioms Ash.OneShot.SourceScheduledScopedInvocations.resume_iff
#print axioms Ash.OneShot.SourceScheduledScopedInvocations.dispose_iff
#print axioms Ash.OneShot.SourceScheduledScopedInvocations.resume_from_parts
#print axioms Ash.OneShot.SourceScheduledScopedInvocations.dispose_from_parts

#print axioms Ash.OneShot.SourceScheduledScopedInvocations.request_from_capability
