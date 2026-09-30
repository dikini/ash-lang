import SourceInterpretationInsertion
import SourceContextualInvocations

/-! Handler insertion preserves independent continuation access. Installed
handler requirements are checked separately by finite structural interfaces;
neither a pending-source proof nor a successor invariant is an interface field. -/
namespace Ash.OneShot.SourceHandlerInvocations
open ScopedExpressions
open SourceDependencyCapture (Scope)
open SourceContextualHints (Hints checkRequirements)
open SourceContextualHintChecking (Compatible check_iff check_append)
open SourceHandlerRequirements (exposed intercepted)
open SourceInterpretationInsertion (Insertion OwnerInsertion)
open SourceContextualInvocationHints (Selection findOwner)

/-- At a known insertion position, compatibility has exactly two new checks:
the inserted declaration's own requirements at its waiting scope, and the
preceding installed declarations' exposed operations intercepted by it. -/
theorem check_inserted (front : Hints frontScope) (tail : Hints tailScope)
    (checked : (front.append tail).check outside = true) :
    (front.append (.handler (effect := effect) (table := table) (families := families) required tail)).check outside = true ↔
      checkRequirements (tailScope.append outside) required = true ∧
      checkRequirements (.handler effect table families .nil) (intercepted effect (exposed front)) = true := by
  rw [check_append, Bool.and_eq_true] at checked
  have exposedCheck : front.check (.handler effect table families (tailScope.append outside)) = true ↔
      checkRequirements (.handler effect table families .nil) (intercepted effect (exposed front)) = true := by
    have passes : SourceHandlerRequirements.outwardRequirements .nil (exposed front) = exposed front :=
      List.filter_eq_self.mpr (fun _ _ => rfl)
    simpa only [Scope.append, passes] using
      SourceHandlerRequirements.check_handler_insert front (front := .nil) checked.1
        (effect := effect) (table := table) (families := families)
  constructor
  · intro supplied
    simp only [check_append, Hints.check, Scope.append, Bool.and_eq_true] at supplied
    exact ⟨supplied.2.1, exposedCheck.mp supplied.1⟩
  · intro supplied
    simp only [check_append, Hints.check, Scope.append, Bool.and_eq_true]
    exact ⟨exposedCheck.mpr supplied.2, supplied.1, checked.2⟩

/-- A finite interface along the changed active spine. Only operation lists
stored by declarations are checked. Dormant branches contribute their existing
finite exposed list at the new receiving scope. -/
inductive Interface (effect : Instance) (table : List (Nat × ProtectionContracts.ClauseContract))
    (families : SourceDependencyAnnotations.ClauseDependencies) (required : List SourceContextualHints.Requirement)
    (outside : Scope) : {first second : Scope} → Hints first → Hints second → Prop where
  | here {before : Hints scope}
      (supplied : checkRequirements (scope.append outside) required = true) :
      Interface effect table families required outside before (.handler (effect := effect) (table := table) (families := families) required before)
  | plain : Interface effect table families required outside before after →
      Interface effect table families required outside (.plain (dependencies := dependencies) before) (.plain (dependencies := dependencies) after)
  | handler {before : Hints first} {after : Hints second}
      (supplied : checkRequirements (second.append outside) needs = true)
      (next : Interface effect table families required outside before after) :
      Interface effect table families required outside
        (.handler (effect := other) (table := otherTable) (families := otherFamilies) needs before) (.handler (effect := other) (table := otherTable) (families := otherFamilies) needs after)
  | cell : Interface effect table families required outside before after →
      Interface effect table families required outside (.cell (identity := identity) before) (.cell (identity := identity) after)
  | cleanup : Interface effect table families required outside before after →
      Interface effect table families required outside
        (.cleanup (needs := needs) (callback := callback) before) (.cleanup (needs := needs) (callback := callback) after)
  | running : Interface effect table families required outside before after →
      Interface effect table families required outside (.running before) (.running after)
  | live {before : Hints first} {after : Hints second} {saved : Hints captured}
      (supplied : checkRequirements (second.append outside) (exposed saved) = true)
      (next : Interface effect table families required outside before after) :
      Interface effect table families required outside (.live (owner := owner) saved before) (.live (owner := owner) saved after)
  | spent : Interface effect table families required outside before after →
      Interface effect table families required outside (.spent (owner := owner) before) (.spent (owner := owner) after)

theorem Interface.insertion (supplied : Interface effect table families required outside before after) :
    Insertion (.handler effect table families required) before after := by
  induction supplied with
  | here checked => exact .here
  | plain next ih => exact .plain ih
  | handler checked next ih => exact .handler ih
  | cell next ih => exact .cell ih
  | cleanup next ih => exact .cleanup ih
  | running next ih => exact .running ih
  | live checked next ih => exact .live ih
  | spent next ih => exact .spent ih

/-- Existing internal compatibility plus the finite interface suffices. -/
theorem Interface.check (supplied : Interface effect table families required outside before after)
    (checked : before.check outside = true) : after.check outside = true := by
  induction supplied with
  | here offered => simp only [Hints.check, Bool.and_eq_true]; exact ⟨offered, checked⟩
  | plain next ih | cell next ih | cleanup next ih | running next ih | spent next ih => exact ih checked
  | handler offered next ih =>
      simp only [Hints.check, Bool.and_eq_true] at checked ⊢
      exact ⟨offered, ih checked.2⟩
  | live offered next ih =>
      simp only [Hints.check, Bool.and_eq_true] at checked ⊢
      exact ⟨SourceHandlerRequirements.check_transport _ checked.1 offered, ih checked.2⟩

/-- Every check in the interface is also necessary at the actual insertion;
this is not a conservative blanket prohibition on overlapping effects. -/
theorem interface_of_check (changed : Insertion (.handler effect table families required) before after)
    (checked : after.check outside = true) : Interface effect table families required outside before after := by
  induction changed with
  | here => exact .here (Bool.and_eq_true_iff.mp checked).1
  | plain next ih => exact .plain (ih checked)
  | handler next ih =>
      simp only [Hints.check, Bool.and_eq_true] at checked
      exact .handler checked.1 (ih checked.2)
  | cell next ih => exact .cell (ih checked)
  | cleanup next ih => exact .cleanup (ih checked)
  | running next ih => exact .running (ih checked)
  | live next ih =>
      simp only [Hints.check, Bool.and_eq_true] at checked
      exact .live (SourceHandlerRequirements.exposed_requirements _ checked.1) (ih checked.2)
  | spent next ih => exact .spent (ih checked)

theorem check_iff_interface (changed : Insertion (.handler effect table families required) before after)
    (checked : before.check outside = true) :
    after.check outside = true ↔ Interface effect table families required outside before after :=
  ⟨interface_of_check changed, fun supplied => supplied.check checked⟩

/-- Reuse the selected owner and its permissions. The separate finite
interface checks the recomposed scope's installed declaration requirements. -/
theorem resume_selected {before : Hints first} {after : Hints second}
    (found : findOwner owner before = some selected)
    (foundNext : findOwner owner after = some next)
    (access : SourceDependencyCapture.ResumeChecked actions phases owner first result)
    (compatible : Compatible (selected.resumed owner).hints .nil)
    (supplied : Interface effect table families required .nil (selected.resumed owner).hints (next.resumed owner).hints) :
    SourceContextualInvocations.Resume actions phases owner after (next.resumed owner) := by
  cases access with
  | checked cut known permission available =>
      cases Option.some.inj ((SourceContextualInvocationHints.selected_cut found).lookup.symm.trans cut.lookup)
      exact .checked foundNext
        (.checked (SourceContextualInvocationHints.selected_cut foundNext) known permission available)
        ((check_iff _).mp (supplied.check ((check_iff _).mpr compatible)))

/-- Saved protection and closing checks are unchanged by insertion in the
caller or waiting scope; the saved program is the same selected program. -/
theorem dispose_selected {before : Hints first} {after : Hints second}
    (found : findOwner owner before = some selected)
    (foundNext : findOwner owner after = some next)
    (related : OwnerInsertion (.handler effect table families required) selected next)
    (access : SourceDependencyCapture.DisposeChecked outward actions phases owner first result)
    (compatible : Compatible (selected.disposed owner).hints .nil)
    (supplied : Interface effect table families required .nil (selected.disposed owner).hints (next.disposed owner).hints) :
    SourceContextualInvocations.Dispose outward actions phases owner after (next.disposed owner) := by
  cases access with
  | checked cut known permission available unprotected closing =>
      cases Option.some.inj ((SourceContextualInvocationHints.selected_cut found).lookup.symm.trans cut.lookup)
      have savedSame : selected.scopes.captured = next.scopes.captured := by cases related <;> rfl
      exact .checked foundNext
        (.checked (SourceContextualInvocationHints.selected_cut foundNext) known permission available
          (savedSame ▸ unprotected) (savedSame ▸ closing))
        ((check_iff _).mp (supplied.check ((check_iff _).mpr compatible)))

theorem resume_admitted {before : Hints first} {after : Hints second}
    (found : findOwner owner before = some selected)
    (foundNext : findOwner owner after = some next)
    (admitted : SourceContextualInvocations.Resume actions phases owner before result)
    (supplied : Interface effect table families required .nil (selected.resumed owner).hints (next.resumed owner).hints) :
    SourceContextualInvocations.Resume actions phases owner after (next.resumed owner) := by
  cases admitted with
  | checked actual access compatible =>
      cases Option.some.inj (actual.symm.trans found)
      exact resume_selected found foundNext access compatible supplied

theorem dispose_admitted {before : Hints first} {after : Hints second}
    (found : findOwner owner before = some selected)
    (foundNext : findOwner owner after = some next)
    (related : OwnerInsertion (.handler effect table families required) selected next)
    (admitted : SourceContextualInvocations.Dispose outward actions phases owner before result)
    (supplied : Interface effect table families required .nil (selected.disposed owner).hints (next.disposed owner).hints) :
    SourceContextualInvocations.Dispose outward actions phases owner after (next.disposed owner) := by
  cases admitted with
  | checked actual access compatible =>
      cases Option.some.inj (actual.symm.trans found)
      exact dispose_selected found foundNext related access compatible supplied

namespace Examples
open SourceContextualInvocations.Examples (actions beforeHints selected disposalHints disposalSelection)
open SourceContextualHintChecking.Examples (savedHints frontHints tailHints)

private def freshEffect : Instance := .user 700 []
private def inCaller : Selection :=
  ⟨⟨_, _, _⟩, .handler (effect := freshEffect) (table := []) (families := []) [] frontHints, savedHints, tailHints⟩
private def inWaiting : Selection :=
  ⟨⟨_, _, _⟩, frontHints, savedHints, .handler (effect := freshEffect) (table := []) (families := []) [] tailHints⟩

/-- Reuse the admitted continuation, checking only affected operation lists. -/
theorem caller_resume : SourceContextualInvocations.Resume actions (OwnerPhaseTransitions.available [19]) 19
    (.handler (effect := freshEffect) (table := []) (families := []) [] beforeHints) (inCaller.resumed 19) :=
  resume_admitted (before := beforeHints) (selected := selected) rfl rfl
    SourceContextualInvocations.Examples.source_resume_admitted (.handler rfl (.here rfl))

theorem waiting_resume : SourceContextualInvocations.Resume actions (OwnerPhaseTransitions.available [19]) 19
    (frontHints.append (.live (owner := 19) savedHints
      (.handler (effect := freshEffect) (table := []) (families := []) [] tailHints))) (inWaiting.resumed 19) :=
  resume_admitted (before := beforeHints) (selected := selected) rfl rfl
    SourceContextualInvocations.Examples.source_resume_admitted (.handler rfl (.handler rfl (.spent (.here rfl))))

private def disposingCaller : Selection :=
  ⟨⟨_, _, _⟩, .handler (effect := freshEffect) (table := []) (families := []) [] .nil,
    disposalSelection.saved, .nil⟩

/-- A nested saved callback and owner survive as the same closing schedule;
the caller's inserted interpretation remains outside that saved program. -/
theorem caller_nested_disposal : SourceContextualInvocations.Dispose [] actions (OwnerPhaseTransitions.available [8, 6]) 8
    (.handler (effect := freshEffect) (table := []) (families := []) [] disposalHints) (disposingCaller.disposed 8) :=
  dispose_admitted (before := disposalHints) (selected := disposalSelection) rfl rfl (.caller .here)
    SourceContextualInvocations.Examples.nested_disposal_admitted
    (.cleanup (.running (.cell (.running (.here rfl)))))

private def masking : Hints (.handler SourceDependencyHandlerGap.effect [] []
    (SourceContextualRechecking.Examples.frontScope.append
      (.live 19 SourceContextualRechecking.Examples.capturedScope SourceDependencyHandlerGap.outside))) :=
  .handler [] beforeHints

/-- The original independent ticket check still succeeds. The separately
checked installed-handler interface rejects the new masking interpretation. -/
theorem masking_keeps_access_but_rejects_resume :
    (SourceDependencyCapture.checkResume actions (OwnerPhaseTransitions.available [19]) 19
      (.handler SourceDependencyHandlerGap.effect [] []
        (SourceContextualRechecking.Examples.frontScope.append
          (.live 19 SourceContextualRechecking.Examples.capturedScope SourceDependencyHandlerGap.outside)))).isSome = true ∧
    SourceContextualInvocationHints.checkResume actions (OwnerPhaseTransitions.available [19]) 19 masking = none :=
  ⟨rfl, rfl⟩

/-- Inserting an interpretation cannot restore a consumed one-shot ticket. -/
theorem spent_owner_still_rejected :
    SourceContextualInvocationHints.checkResume actions (OwnerPhaseTransitions.spend (OwnerPhaseTransitions.available [19]) 19) 19
      (.handler (effect := freshEffect) (table := []) (families := []) [] beforeHints) = none := rfl

end Examples

end Ash.OneShot.SourceHandlerInvocations

#print axioms Ash.OneShot.SourceHandlerInvocations.check_inserted
#print axioms Ash.OneShot.SourceHandlerInvocations.Interface.insertion
#print axioms Ash.OneShot.SourceHandlerInvocations.Interface.check
#print axioms Ash.OneShot.SourceHandlerInvocations.interface_of_check
#print axioms Ash.OneShot.SourceHandlerInvocations.check_iff_interface
#print axioms Ash.OneShot.SourceHandlerInvocations.resume_selected
#print axioms Ash.OneShot.SourceHandlerInvocations.dispose_selected

#print axioms Ash.OneShot.SourceHandlerInvocations.Examples.caller_resume
#print axioms Ash.OneShot.SourceHandlerInvocations.Examples.waiting_resume
#print axioms Ash.OneShot.SourceHandlerInvocations.Examples.caller_nested_disposal
#print axioms Ash.OneShot.SourceHandlerInvocations.Examples.masking_keeps_access_but_rejects_resume
#print axioms Ash.OneShot.SourceHandlerInvocations.Examples.spent_owner_still_rejected

#print axioms Ash.OneShot.SourceHandlerInvocations.resume_admitted
#print axioms Ash.OneShot.SourceHandlerInvocations.dispose_admitted
