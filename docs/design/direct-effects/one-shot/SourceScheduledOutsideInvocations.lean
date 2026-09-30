import SourceScheduledCapabilityAnnotations

/-! Retained source may consume a distinct outside continuation. These are
source scheduling examples; rich expression admission remains a separate layer. -/
namespace Ash.OneShot.SourceScheduledOutsideInvocations
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledCapabilityAnnotations (Code Retained)
open SourceScheduledChecks (Local)
open SourceDependencyHandlerGap (actions phases)
open SourceDeclarationPlans (Plan)
open SourceDependencyCapture.Examples (effectE effectF)

def savedHints (outside : Nat) : Hints (.plain (.invoke ⟨outside, .resume⟩) .nil) := .plain .nil
def saved (outside : Nat) : Forest (savedHints outside) := .plain .invoke .nil
def tailHints (outside : Nat) : Hints (.live outside .nil .nil) := .live .nil .nil
def tail (outside : Nat) : Forest (tailHints outside) := .live .nil .nil

/-- Annotation construction does not assume that the owners are distinct or
that either is available. Those conditions are checked independently below. -/
def nested (owner outside : Nat) :
    Code [] (.invoke (key := ⟨owner, .resume⟩))
      (.live (owner := owner) (saved outside) (tail outside)) :=
  .resume .hit
    (.plain (.resume (.spent .hit) (.operations .nil) (.spent (.operations .nil)) (.operations .nil))
      (.operations .nil))
    (.operations .nil)
    (.live (.operations .nil) (.operations .nil))

/-- The recursive check spends the first owner before checking the saved
invocation. A distinct outside owner remains available by the existing law. -/
theorem nested_valid (different : outside ≠ owner) :
    (nested owner outside).Valid [] actions phases := by
  simp [nested, Code.Valid, Retained.Valid, SourceScheduledRetainedInterfaces.Interfaces.check,
    actions, SourceDependencyHandlerGap.rights, phases, OwnerPhaseTransitions.spend, different]

theorem nested_source (different : outside ≠ owner) :
    Local [] actions phases [] (.invoke (key := ⟨owner, .resume⟩))
      (.live (owner := owner) (saved outside) (tail outside)) :=
  (nested owner outside).compile (nested_valid different)

/-- Reusing the same owner is rejected in the restored code, despite the
second syntactic live marker. Operation requirements do not affect this test. -/
theorem repeated_owner_rejected : ¬ (nested owner owner).Valid [] actions phases := by
  simp [nested, Code.Valid, Retained.Valid, SourceScheduledRetainedInterfaces.Interfaces.check,
    OwnerPhaseTransitions.spend]

/-- Denying the outside owner's permission rejects the whole annotation even
though the first owner has the requested permission. -/
theorem outside_permission_rejected (different : outside ≠ owner) :
    ¬ (nested owner outside).Valid []
      (fun actual => if actual = outside then some ⟨false, true⟩ else some ⟨true, false⟩) phases := by
  simp [nested, Code.Valid, Retained.Valid, SourceScheduledRetainedInterfaces.Interfaces.check,
    Ne.symm different]

def disposingHints (outside : Nat) : Hints (.plain (.invoke ⟨outside, .dispose⟩) .nil) := .plain .nil
def disposing (outside : Nat) : Forest (disposingHints outside) := .plain .invoke .nil
def bothActions : Syntax.UsageTickets := fun _ => some ⟨true, true⟩

/-- Restored ordinary code may dispose another continuation. Its permission,
protection and closing route are validated independently of the outer resume. -/
def mixed (owner outside : Nat) :
    Code [] (.invoke (key := ⟨owner, .resume⟩))
      (.live (owner := owner) (disposing outside) (tail outside)) :=
  .resume .hit
    (.plain (.dispose (.spent .hit) (.operations .nil) (.spent (.operations .nil)) (.operations .nil))
      (.operations .nil))
    (.operations .nil)
    (.live (.operations .nil) (.operations .nil))

theorem mixed_valid (different : outside ≠ owner) :
    (mixed owner outside).Valid [] bothActions phases := by
  simp [mixed, Code.Valid, Retained.Valid, SourceScheduledRetainedInterfaces.Interfaces.check,
    bothActions, phases, OwnerPhaseTransitions.spend, different,
    SourceDependencyCapture.Scope.held, SourceDependencyCapture.Scope.shape, SourceDependencyCapture.checkClosing]

theorem mixed_source (different : outside ≠ owner) :
    Local [] bothActions phases [] (.invoke (key := ⟨owner, .resume⟩))
      (.live (owner := owner) (disposing outside) (tail outside)) :=
  (mixed owner outside).compile (mixed_valid different)

theorem disposal_permission_rejected : ¬ (mixed owner outside).Valid [] actions phases := by
  simp [mixed, Code.Valid, Retained.Valid, actions, SourceDependencyHandlerGap.rights]

private theorem internal_declarations : SourceScheduledSourceInterfaces.Declared world
    (SourcePlanSignatures.signature (SourceDeclarationPlans.HandledRequest.plan effectF 0)) :=
  .handler SourcePlannedRecipeDeclarations.handled_request_declarations (.sequence .pure .request)

/-- A selected disposer captures an armed effectful callback. This outer plan
is not the special empty-capture pattern accepted by operation footprints. -/
def initialPlan := Plan.handler (effect := effectE) (table := SourceDeclarationPlans.HandledRequest.table 0)
  [] (SourceDeclarationPlans.HandledRequest.declarations 0)
  (.cleanup (needs := []) (SourceDeclarationPlans.HandledRequest.plan effectF 0)
    (.sequence .pure (.request (effect := effectE) (operation := 0))))

def initialAnnotation : Code [] initialPlan .nil :=
  .handler SourcePlannedRecipeDeclarations.handled_request_declarations
    (.cleanup
      (.sequence (.operations [] .pure .pure)
        (.selected (.cleanup (.hit rfl rfl)) (fun _ => .cleanup (.handler .nil))
          (fun _ => .cleanup (.operations [] .handledRequest internal_declarations) (.operations .nil))))
      (.operations [] .handledRequest internal_declarations))

theorem selected_disposal_valid :
    initialAnnotation.Valid [] (fun _ => none) (OwnerPhaseTransitions.available []) := by
  refine ⟨rfl, ⟨⟨rfl, ⟨rfl, ?_⟩⟩, rfl⟩⟩
  intro disposes
  exact ⟨rfl, rfl⟩

theorem selected_disposal_source :
    Local [] (fun _ => none) (OwnerPhaseTransitions.available []) [] initialPlan .nil :=
  initialAnnotation.compile selected_disposal_valid

end Ash.OneShot.SourceScheduledOutsideInvocations

#print axioms Ash.OneShot.SourceScheduledOutsideInvocations.nested_valid
#print axioms Ash.OneShot.SourceScheduledOutsideInvocations.nested_source
#print axioms Ash.OneShot.SourceScheduledOutsideInvocations.repeated_owner_rejected
#print axioms Ash.OneShot.SourceScheduledOutsideInvocations.outside_permission_rejected
#print axioms Ash.OneShot.SourceScheduledOutsideInvocations.mixed_valid
#print axioms Ash.OneShot.SourceScheduledOutsideInvocations.mixed_source
#print axioms Ash.OneShot.SourceScheduledOutsideInvocations.disposal_permission_rejected
#print axioms Ash.OneShot.SourceScheduledOutsideInvocations.selected_disposal_valid
#print axioms Ash.OneShot.SourceScheduledOutsideInvocations.selected_disposal_source
