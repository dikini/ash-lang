import SourceContextualInvocationHints
import SourceContextualHintChecking

/-! Structural invocation admission combines existing independent continuation
access with contextual handler requirements. The resulting certificate follows
the same selected source boundary and actual runtime continuation. -/
namespace Ash.OneShot.SourceContextualInvocations
open ScopedExpressions ScopedExecution
open SourceContextualHints (Hints)
open SourceContextualInvocationHints (Annotated Selection findOwner selected_cut checkResume checkDispose forClosing)
open SourceContextualHintChecking (Matches Compatible check_iff)
open SourceContextualRechecking (handlers)
open SourceContextualRequirements (DeclarationRecipes)
abbrev Receiving := SourceDependencyCapture.Scope

inductive Resume (actions : Syntax.UsageTickets) (phases : OwnerPhaseTransitions.Phases)
    (owner : Nat) {scope : Receiving} (hints : Hints scope) : Annotated → Prop where
  | checked (found : findOwner owner hints = some selected)
      (access : SourceDependencyCapture.ResumeChecked actions phases owner scope (selected.scopes.resumed owner))
      (compatible : Compatible (selected.resumed owner).hints .nil) :
      Resume actions phases owner hints (selected.resumed owner)

inductive Dispose (outward : List Instance) (actions : Syntax.UsageTickets)
    (phases : OwnerPhaseTransitions.Phases) (owner : Nat) {scope : Receiving}
    (hints : Hints scope) : Annotated → Prop where
  | checked (found : findOwner owner hints = some selected)
      (access : SourceDependencyCapture.DisposeChecked outward actions phases owner scope (selected.scopes.disposed owner))
      (compatible : Compatible (selected.disposed owner).hints .nil) :
      Dispose outward actions phases owner hints (selected.disposed owner)

private theorem present_iff (value : Option α) : value.isSome = true ↔ ∃ item, value = some item := by
  cases value <;> simp

theorem resume_access {hints : Hints scope} (found : findOwner owner hints = some selected)
    (present : (SourceDependencyCapture.checkResume actions phases owner scope).isSome = true) :
    SourceDependencyCapture.ResumeChecked actions phases owner scope (selected.scopes.resumed owner) := by
  obtain ⟨after, checked⟩ := (present_iff _).mp present
  cases SourceDependencyCapture.check_resume_iff.mp checked with
  | checked located known permission available =>
      cases Option.some.inj ((selected_cut found).lookup.symm.trans located.lookup)
      exact .checked located known permission available

theorem dispose_access {hints : Hints scope} (found : findOwner owner hints = some selected)
    (present : (SourceDependencyCapture.checkDispose outward actions phases owner scope).isSome = true) :
    SourceDependencyCapture.DisposeChecked outward actions phases owner scope (selected.scopes.disposed owner) := by
  obtain ⟨after, checked⟩ := (present_iff _).mp present
  cases SourceDependencyCapture.check_dispose_iff.mp checked with
  | checked located known permission available unprotected closing =>
      cases Option.some.inj ((selected_cut found).lookup.symm.trans located.lookup)
      exact .checked located known permission available unprotected closing

theorem check_resume_iff : checkResume actions phases owner hints = some after ↔
    Resume actions phases owner hints after := by
  constructor
  · intro checked
    unfold checkResume at checked
    cases found : findOwner owner hints with
    | none => simp [found] at checked
    | some selected =>
        simp only [found] at checked
        split at checked
        next accepted =>
          rw [Bool.and_eq_true] at accepted
          cases Option.some.inj checked
          exact .checked found (resume_access found accepted.1) ((check_iff _).mp accepted.2)
        next => cases checked
  · intro accepted
    cases accepted with
    | checked found access compatible =>
        simp only [checkResume, found, SourceDependencyCapture.check_resume_iff.mpr access,
          Option.isSome_some, (check_iff _).mpr compatible, Bool.true_and, if_true]

theorem check_dispose_iff : checkDispose outward actions phases owner hints = some after ↔
    Dispose outward actions phases owner hints after := by
  constructor
  · intro checked
    unfold checkDispose at checked
    cases found : findOwner owner hints with
    | none => simp [found] at checked
    | some selected =>
        simp only [found] at checked
        split at checked
        next accepted =>
          rw [Bool.and_eq_true] at accepted
          cases Option.some.inj checked
          exact .checked found (dispose_access found accepted.1) ((check_iff _).mp accepted.2)
        next => cases checked
  · intro accepted
    cases accepted with
    | checked found access compatible =>
        simp only [checkDispose, found, SourceDependencyCapture.check_dispose_iff.mpr access,
          Option.isSome_some, (check_iff _).mpr compatible, Bool.true_and, if_true]

theorem consumed_resume_rejected :
    checkResume actions (OwnerPhaseTransitions.spend phases owner) owner hints = none := by
  unfold checkResume
  cases findOwner owner hints <;> simp [SourceDependencyCapture.consumed_resume_rejected]

theorem consumed_dispose_rejected :
    checkDispose outward actions (OwnerPhaseTransitions.spend phases owner) owner hints = none := by
  unfold checkDispose
  cases findOwner owner hints <;> simp [SourceDependencyCapture.consumed_dispose_rejected]

/-- The selected annotated pieces authenticate against the same actual live
boundary. No separately supplied runtime cut or replacement annotations occur. -/
theorem Matches.find_owner {hints : Hints scope}
    (matched : Matches tables families required hints stack)
    (found : findOwner owner hints = some selected) :
    ∃ front captured tail input answer caller,
      stack = front.append (.live owner input answer captured caller tail) ∧
      Matches tables families required selected.front front ∧
      Matches tables families required selected.saved captured ∧
      Matches tables families required selected.tail tail := by
  induction matched generalizing selected with
  | nil => cases found
  | plain tail ih | handler tail ih | cell tail ih | cleanup tail ih
  | running tail ih | unwinding tail ih | closing tail ih | retiring tail ih =>
      simp only [findOwner, Option.map_eq_some_iff] at found
      obtain ⟨inside, located, rfl⟩ := found
      obtain ⟨front, captured, tail, input, answer, caller, shape, frontSource, saved, outside⟩ := ih located
      first
      | exact ⟨.push (.plain _) front, captured, tail, input, answer, caller,
          by rw [shape]; rfl, .plain frontSource, saved, outside⟩
      | exact ⟨.push (.handler _) front, captured, tail, input, answer, caller,
          by rw [shape]; rfl, .handler frontSource, saved, outside⟩
      | exact ⟨.push (.cell _ _ _ _) front, captured, tail, input, answer, caller,
          by rw [shape]; rfl, .cell frontSource, saved, outside⟩
      | exact ⟨.push (.armed _) front, captured, tail, input, answer, caller,
          by rw [shape]; rfl, .cleanup frontSource, saved, outside⟩
      | exact ⟨.push (.running _ _ _) front, captured, tail, input, answer, caller,
          by rw [shape]; rfl, .running frontSource, saved, outside⟩
      | exact ⟨.push (.unwinding _) front, captured, tail, input, answer, caller,
          by rw [shape]; rfl, .unwinding frontSource, saved, outside⟩
      | exact ⟨.push (.closing _ _) front, captured, tail, input, answer, caller,
          by rw [shape]; rfl, .closing frontSource, saved, outside⟩
      | exact ⟨.push (.retiring _) front, captured, tail, input, answer, caller,
          by rw [shape]; rfl, .retiring frontSource, saved, outside⟩
  | @live savedScope savedHints captured restScope restHints stack other input answer caller saved tail ihSaved ihTail =>
      by_cases same : owner = other
      · subst other
        simp only [findOwner, ↓reduceIte, Option.some.injEq] at found
        subst selected
        exact ⟨.nil, captured, stack, input, answer, caller, rfl, .nil, saved, tail⟩
      · simp only [findOwner, if_neg same, Option.map_eq_some_iff] at found
        obtain ⟨inside, located, rfl⟩ := found
        obtain ⟨front, capturedStack, tailStack, inputType, answerType, callerScope,
          shape, frontSource, insideSource, outside⟩ := ihTail located
        exact ⟨.live other input answer captured caller front, capturedStack, tailStack,
          inputType, answerType, callerScope, by rw [shape]; rfl, .live saved frontSource, insideSource, outside⟩
  | spent tail ih =>
      simp only [findOwner, Option.map_eq_some_iff] at found
      obtain ⟨inside, located, rfl⟩ := found
      obtain ⟨front, captured, tail, input, answer, caller, shape, frontSource, saved, outside⟩ := ih located
      exact ⟨.spent _ _ _ front, captured, tail, input, answer, caller, by rw [shape]; rfl,
        .spent frontSource, saved, outside⟩

/-- If a realized stack has no installed handler, every annotation of that
same scope authenticates. This applies to schedules before callback code runs. -/
theorem Matches.without_handlers
    (realized : SourceDependencyCapture.Realizes tables families scope stack)
    (empty : handlers stack = []) (hints : Hints scope) : Matches tables families required hints stack := by
  induction realized with
  | nil => cases hints; exact .nil
  | push frame tail ih =>
      cases frame <;> cases hints
      · exact .plain (ih empty _)
      · cases empty
      · exact .cell (ih empty _)
      · exact .cleanup (ih empty _)
      · exact .running (ih empty _)
      · exact .unwinding (ih empty _)
      · exact .closing (ih empty _)
      · exact .retiring (ih empty _)
  | live saved tail ihSaved ihTail =>
      cases hints with
      | live inside rest =>
          have parts := List.append_eq_nil_iff.mp empty
          exact .live (ihSaved parts.1 inside) (ihTail parts.2 rest)
  | spent tail ih => cases hints with | spent rest => exact .spent (ih empty rest)

/-- Reuse the existing closing-plan construction and owner accounting.
The schedule contains no installed handlers, so its hints authenticate directly. -/
theorem Matches.forClosing {hints : Hints scope}
    (matched : Matches tables families required hints stack) (unprotected : scope.held = false) :
    ∃ plan, SourceRecursiveRoutes.Realizes scope.shape stack plan ∧
      Matches tables families required (forClosing hints) (closeControl caller plan) := by
  obtain ⟨plan, shape, scheduled⟩ := matched.realizes.forClosing (caller := caller) unprotected
  exact ⟨plan, shape, Matches.without_handlers scheduled
    (SourceContextualRechecking.handlers_close_control plan) (SourceContextualInvocationHints.forClosing hints)⟩

theorem selected_unprotected
    (access : SourceDependencyCapture.DisposeChecked outward actions phases owner scope afterScope)
    (located : SourceDependencyCapture.OwnerCut owner scope selected) : selected.captured.held = false := by
  cases access with
  | checked actual known permission available unprotected closing =>
      cases Option.some.inj (located.lookup.symm.trans actual.lookup)
      exact unprotected

/-- Source admission selects the actual continuation and constructs its
restored annotations, contextual certificates and exact one-shot owner trace.
Pending-code and rich source typing are separate invariant components. -/
theorem Resume.step {hints : Hints scope}
    (admitted : Resume actions phases owner hints after)
    (matched : Matches tables families required hints stack)
    (recipes : ∀ handler ∈ handlers stack,
      DeclarationRecipes outward handler.clauses (families handler) (required handler))
    (unique : (ownedTickets stack).Nodup)
    (resolved : caller.resolve binder = some owner) (closed : ClosedValue value) :
    ∃ afterStack,
      RawStep ⟨.resume binder value, caller, stack⟩ ⟨value, caller, afterStack⟩ [] [.ticket owner] ∧
      Matches tables families required after.hints afterStack ∧
      SourceContextualForest.Forest outward tables families afterStack after.scope .nil ∧
      (ownedTickets stack).Perm (owner :: ownedTickets afterStack) ∧
      OwnerPhaseTransitions.Trace (OwnerPhaseTransitions.available (ownedTickets stack)) [owner]
        (OwnerPhaseTransitions.available (ownedTickets afterStack)) := by
  cases admitted with
  | checked found access compatible =>
      obtain ⟨front, captured, tail, input, answer, savedCaller, shape, frontSource, saved, outside⟩ :=
        Matches.find_owner matched found
      subst stack
      have restored := saved.append
        (frontSource.append (Matches.spent (owner := owner) (answer := answer) (caller := savedCaller) outside))
      refine ⟨_, RawStep.resume binder owner caller savedCaller input answer front captured tail value closed resolved,
        restored, ?_, OwnerPhaseTransitions.resume_owned_permutation, OwnerPhaseTransitions.resume_phase_trace unique⟩
      exact restored.recheck
        (fun handler member => recipes handler ((SourceContextualRechecking.resume_handlers handler).mp member))
        ((check_iff _).mpr compatible)

/-- Disposal constructs its closing plan from the same selected capture. The
old plan and phase lemmas account for all captured owners, including dormant
ones. Callback execution remains part of the shared-state integration. -/
theorem Dispose.step {hints : Hints scope}
    (admitted : Dispose outward actions phases owner hints after)
    (matched : Matches tables families required hints stack)
    (recipes : ∀ handler ∈ handlers stack,
      DeclarationRecipes outward handler.clauses (families handler) (required handler))
    (unique : (ownedTickets stack).Nodup) (resolved : caller.resolve binder = some owner) :
    ∃ afterStack captured plan,
      RawStep ⟨.discard binder, caller, stack⟩ ⟨.unit, caller, afterStack⟩ [.close closeId] [.ticket owner] ∧
      Matches tables families required after.hints afterStack ∧
      SourceContextualForest.Forest outward tables families afterStack after.scope .nil ∧
      makePlan captured = some plan ∧ (planOwners (plan.map CloseEntry.erase)).Perm captured.erase.owners ∧
      (ownedTickets stack).Perm (owner :: ownedTickets afterStack) ∧
      OwnerPhaseTransitions.Trace (OwnerPhaseTransitions.available (ownedTickets stack)) [owner]
        (OwnerPhaseTransitions.available (ownedTickets afterStack)) := by
  cases admitted with
  | checked found access compatible =>
      obtain ⟨front, captured, tail, input, answer, savedCaller, shape, frontSource, saved, outside⟩ :=
        Matches.find_owner matched found
      obtain ⟨plan, realizedPlan, scheduled⟩ := Matches.forClosing saved
        (caller := caller) (selected_unprotected access (selected_cut found))
      subst stack
      have restored := scheduled.append
        (Matches.closing (identity := closeId) (caller := caller)
          (frontSource.append (Matches.spent (owner := owner) (answer := answer) (caller := savedCaller) outside)))
      refine ⟨_, captured, plan,
        RawStep.discard binder owner closeId caller savedCaller input answer front captured tail plan resolved realizedPlan.built,
        restored, ?_, realizedPlan.built, realizedPlan.owner_accounting,
        OwnerClosingSource.discard_owned_permutation realizedPlan.built,
        OwnerClosingSource.discard_phase_trace realizedPlan.built unique⟩
      exact restored.recheck
        (fun handler member => recipes handler (SourceContextualRechecking.dispose_handlers plan member))
        ((check_iff _).mpr compatible)

namespace Examples
open SourceContextualHintChecking.Examples (savedHints frontHints tailHints maskingHints)

def actions : Syntax.UsageTickets := fun _ => some ⟨true, true⟩
def beforeHints := frontHints.append (.live (owner := 19) savedHints tailHints)
def selected : Selection := ⟨⟨_, _, _⟩, frontHints, savedHints, tailHints⟩

theorem source_resume_admitted : Resume actions (OwnerPhaseTransitions.available [19]) 19
    beforeHints (selected.resumed 19) :=
  check_resume_iff.mp (by rfl)

theorem masking_caller_rejected :
    (SourceDependencyCapture.checkResume actions (OwnerPhaseTransitions.available [19]) 19
      (SourceContextualHintChecking.Examples.maskingScope.append
        (.live 19 SourceContextualRechecking.Examples.capturedScope SourceDependencyHandlerGap.outside))).isSome = true ∧
    checkResume actions (OwnerPhaseTransitions.available [19]) 19
      (maskingHints.append (.live (owner := 19) savedHints tailHints)) = none := ⟨rfl, rfl⟩

theorem permission_checked_independently :
    (selected.resumed 19).hints.check .nil = true ∧
      checkResume (fun _ => some ⟨false, true⟩) (OwnerPhaseTransitions.available [19]) 19 beforeHints = none := ⟨rfl, rfl⟩

def nestedScope : Receiving := .live 6
  (.cleanup [.cell 4] (.request (.cell 4) 0) .nil) (.cell 4 .nil)
def nestedHints : Hints nestedScope := .live (.cleanup .nil) (.cell .nil)
def disposalHints : Hints (.live 8 nestedScope .nil) := .live nestedHints .nil
def disposalSelection : Selection := ⟨⟨.nil, nestedScope, .nil⟩, .nil, nestedHints, .nil⟩
def disposalStack : Stack := .live 8 .unit .unit ScopedPorts.CompletionExamples.nested .none .nil
def tables : CallableProtectionFrames.Tables := fun _ => []
def families : SourceDependencyCapture.Families := fun _ => []
def required : SourceContextualRechecking.Required := fun _ => []

theorem dormant_target_rejected : findOwner 6 disposalHints = none := rfl

theorem nested_disposal_admitted : Dispose [] actions (OwnerPhaseTransitions.available [8, 6]) 8
    disposalHints (disposalSelection.disposed 8) := check_dispose_iff.mp (by rfl)

theorem nested_disposal_matches : Matches tables families required disposalHints disposalStack :=
  .live (.live (.cleanup (action := ScopedPorts.CompletionExamples.action) .nil) (.cell .nil)) .nil

/-- An actual nested disposal consumes owner 8 while retaining owner 6 as
scheduled retirement work. Its callback and release plan come from the old
closing construction, and the contextual component follows the same step. -/
theorem nested_disposal_step :
    ∃ afterStack captured plan,
      RawStep ⟨.discard 0, .ticket 0 8, disposalStack⟩ ⟨.unit, .ticket 0 8, afterStack⟩ [.close 20] [.ticket 8] ∧
      Matches tables families required (disposalSelection.disposed 8).hints afterStack ∧
      SourceContextualForest.Forest [] tables families afterStack (disposalSelection.disposed 8).scope .nil ∧
      makePlan captured = some plan ∧ (planOwners (plan.map CloseEntry.erase)).Perm captured.erase.owners ∧
      (ownedTickets disposalStack).Perm (8 :: ownedTickets afterStack) ∧
      OwnerPhaseTransitions.Trace (OwnerPhaseTransitions.available (ownedTickets disposalStack)) [8]
        (OwnerPhaseTransitions.available (ownedTickets afterStack)) :=
  nested_disposal_admitted.step nested_disposal_matches
    (fun handler member => by cases member) (by decide) rfl

end Examples

end Ash.OneShot.SourceContextualInvocations

#print axioms Ash.OneShot.SourceContextualInvocations.resume_access
#print axioms Ash.OneShot.SourceContextualInvocations.dispose_access
#print axioms Ash.OneShot.SourceContextualInvocations.check_resume_iff
#print axioms Ash.OneShot.SourceContextualInvocations.check_dispose_iff
#print axioms Ash.OneShot.SourceContextualInvocations.consumed_resume_rejected
#print axioms Ash.OneShot.SourceContextualInvocations.consumed_dispose_rejected
#print axioms Ash.OneShot.SourceContextualInvocations.Matches.find_owner
#print axioms Ash.OneShot.SourceContextualInvocations.Matches.without_handlers
#print axioms Ash.OneShot.SourceContextualInvocations.Matches.forClosing
#print axioms Ash.OneShot.SourceContextualInvocations.selected_unprotected
#print axioms Ash.OneShot.SourceContextualInvocations.Resume.step
#print axioms Ash.OneShot.SourceContextualInvocations.Dispose.step
#print axioms Ash.OneShot.SourceContextualInvocations.Examples.source_resume_admitted
#print axioms Ash.OneShot.SourceContextualInvocations.Examples.masking_caller_rejected
#print axioms Ash.OneShot.SourceContextualInvocations.Examples.permission_checked_independently
#print axioms Ash.OneShot.SourceContextualInvocations.Examples.dormant_target_rejected
#print axioms Ash.OneShot.SourceContextualInvocations.Examples.nested_disposal_admitted
#print axioms Ash.OneShot.SourceContextualInvocations.Examples.nested_disposal_matches
#print axioms Ash.OneShot.SourceContextualInvocations.Examples.nested_disposal_step
