import SourceDependencyCapture

/-! Relate dependency scopes to the same actual recursive execution stack.
Selection, physical protection and closing-plan realization are connected at
one cut. Pending-code and callable typing remain the separate hereditary source
layer; this relation does not assume that arbitrary dependency annotations are
valid source derivations. -/
namespace Ash.OneShot.SourceDependencyCapture
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations (Dependencies ClauseDependencies)

abbrev Families := HandlerData → ClauseDependencies

/-- A frame's interpretation and cleanup requirements come from its actual
runtime data. Running, closing and retiring frames carry physical protection. -/
inductive Frame (tables : CallableProtectionFrames.Tables) (families : Families) : (Scope → Scope) → ExecFrame → Prop where
  | plain : Frame tables families (.plain dependencies) (.plain data)
  | handler : Frame tables families (.handler data.effectInst (tables data) (families data)) (.handler data)
  | cell : Frame tables families (.cell identity) (.cell identity payload caller answer)
  | cleanup : Frame tables families (.cleanup action.requests dependencies) (.armed action)
  | running : Frame tables families .running (.running action value closed)
  | unwinding : Frame tables families .running (.unwinding action)
  | closing : Frame tables families .running (.closing identity caller)
  | retiring : Frame tables families .running (.retiring owner)

inductive Realizes (tables : CallableProtectionFrames.Tables) (families : Families) : Scope → Stack → Prop where
  | nil : Realizes tables families .nil .nil
  | push (frame : Frame tables families layer entry) (tail : Realizes tables families rest stack) :
      Realizes tables families (layer rest) (.push entry stack)
  | live (inside : Realizes tables families captured saved) (outside : Realizes tables families rest stack) :
      Realizes tables families (.live owner captured rest) (.live owner input answer saved caller stack)
  | spent (tail : Realizes tables families rest stack) :
      Realizes tables families (.spent owner rest) (.spent owner answer caller stack)

def Scope.append : Scope → Scope → Scope
  | .nil, tail => tail
  | .plain dependencies rest, tail => .plain dependencies (rest.append tail)
  | .handler effect table dependencies rest, tail => .handler effect table dependencies (rest.append tail)
  | .cell identity rest, tail => .cell identity (rest.append tail)
  | .cleanup needs callback rest, tail => .cleanup needs callback (rest.append tail)
  | .running rest, tail => .running (rest.append tail)
  | .live owner captured rest, tail => .live owner captured (rest.append tail)
  | .spent owner rest, tail => .spent owner (rest.append tail)

theorem Frame.append (frame : Frame tables families layer entry) :
    (layer front).append tail = layer (front.append tail) := by cases frame <;> rfl

theorem Realizes.append (front : Realizes tables families first a) (tail : Realizes tables families second b) :
    Realizes tables families (first.append second) (a.append b) := by
  induction front with
  | nil => exact tail
  | push frame rest ih => rw [frame.append]; exact .push frame ih
  | live inside outside ihInside ihOutside => exact .live inside ihOutside
  | spent rest ih => exact .spent ih

theorem Frame.held (frame : Frame tables families layer entry) :
    (layer rest).held = (ProtectionContexts.frameProtected entry.erase || rest.held) := by
  cases frame <;> rfl

theorem Realizes.held (realized : Realizes tables families scope stack) :
    scope.held = ProtectionContexts.protectedMode stack.erase := by
  induction realized with
  | nil => rfl
  | push frame tail ih => rw [frame.held, ih]; rfl
  | live inside outside ihInside ihOutside => simp only [Scope.held, ihInside, ihOutside, Stack.erase, ProtectionContexts.protectedMode]
  | spent tail ih => exact ih

/-- Construct the old recursive plan realization from an unprotected actual
scope. No successful makePlan result or separate shape witness is assumed. -/
theorem Realizes.closing (realized : Realizes tables families scope stack) (unprotected : scope.held = false) :
    ∃ plan, SourceRecursiveRoutes.Realizes scope.shape stack plan := by
  induction realized with
  | nil => exact ⟨[], .nil⟩
  | push frame tail ih =>
      rw [frame.held, Bool.or_eq_false_iff] at unprotected
      obtain ⟨plan, rest⟩ := ih unprotected.2
      cases frame with
      | plain => exact ⟨plan, .plain rest⟩
      | handler => exact ⟨plan, .handler rest⟩
      | cell => exact ⟨_, .cell rest⟩
      | cleanup => exact ⟨_, .cleanup rest⟩
      | running | unwinding | closing | retiring => cases unprotected.1
  | live inside outside ihInside ihOutside =>
      simp only [Scope.held, Bool.or_eq_false_iff] at unprotected
      obtain ⟨first, captured⟩ := ihInside unprotected.1
      obtain ⟨second, rest⟩ := ihOutside unprotected.2
      exact ⟨_, .live captured rest⟩
  | spent tail ih =>
      obtain ⟨plan, rest⟩ := ih unprotected
      exact ⟨plan, .spent rest⟩

def chosen (operation : Nat) (table : List (Nat × ClauseContract)) (dependencies : ClauseDependencies)
    (capture tail : Scope) : Option Selection :=
  match lookup operation table, lookupDependencies operation dependencies with
  | some contract, some modes => some (.handler capture tail contract modes)
  | _, _ => none

theorem chosen_prepend (layer : Scope → Scope) :
    (chosen operation table dependencies capture tail).map (Selection.prepend layer) =
      chosen operation table dependencies (layer capture) tail := by
  unfold chosen
  cases found : lookup operation table <;> cases annotated : lookupDependencies operation dependencies <;>
    rfl

theorem Frame.select_miss (frame : Frame tables families layer entry)
    (miss : entry.erase.target ≠ some requested) :
    select requested operation (layer rest) = (select requested operation rest).map (Selection.prepend layer) := by
  cases frame with
  | plain | cleanup | running | unwinding | closing | retiring => rfl
  | @handler handler =>
      have different : requested ≠ handler.effectInst := by
        intro same; apply miss; simp [ExecFrame.erase, HandlerData.erase, Ash.OneShot.Frame.target, same]
      exact if_neg different
  | @cell identity payload caller answer =>
      have different : requested ≠ .cell identity := by
        intro same; apply miss; simp [ExecFrame.erase, Ash.OneShot.Frame.target, same]
      exact if_neg different

/-- An actual handler cut determines both annotated segments and the exact
source selection result for every operation. The handler tables and dependency
families are the ones attached to that same actual handler. -/
theorem Realizes.cut
    (cut : HandlerCut requested whole capture tail handler)
    (realized : Realizes tables families scope whole) :
    ∃ capturedScope tailScope,
      Realizes tables families capturedScope capture ∧ Realizes tables families tailScope tail ∧
      scope = capturedScope.append tailScope ∧
      ∀ operation, select requested operation scope = chosen operation (tables handler) (families handler) capturedScope tailScope := by
  induction cut generalizing scope with
  | hit handler tail same => cases realized with
    | push frame rest => cases frame with
      | handler =>
          refine ⟨_, _, .push .handler .nil, rest, rfl, ?_⟩
          intro operation
          simp only [select, if_pos same.symm, chosen]
          rfl
  | push entry rest capture tail handler miss next ih => cases realized with
    | push frame rest =>
        obtain ⟨capturedScope, tailScope, inside, outside, recomposed, selected⟩ := ih rest
        refine ⟨_, _, .push frame inside, outside, ?_, ?_⟩
        · rw [frame.append, ← recomposed]
        · intro operation
          rw [frame.select_miss miss, selected operation, chosen_prepend]
  | live owner input answer saved caller rest capture tail handler next ih => cases realized with
    | live inside outside =>
        obtain ⟨capturedScope, tailScope, captured, remaining, recomposed, selected⟩ := ih outside
        refine ⟨_, _, .live inside captured, remaining, ?_, ?_⟩
        · simp only [Scope.append, ← recomposed]
        · intro operation
          rw [select, selected operation, chosen_prepend]
  | spent owner answer caller rest capture tail handler next ih => cases realized with
    | spent outside =>
        obtain ⟨capturedScope, tailScope, captured, remaining, recomposed, selected⟩ := ih outside
        refine ⟨_, _, .spent captured, remaining, ?_, ?_⟩
        · simp only [Scope.append, ← recomposed]
        · intro operation
          rw [select, selected operation, chosen_prepend]

/-- The same saved and waiting source scopes realize full-prefix resumption.
No handler or resource frame is exchanged when the spent owner is inserted. -/
theorem resume_recomposition
    (saved : Realizes tables families capturedScope capture)
    (waiting : Realizes tables families frontScope front)
    (outside : Realizes tables families tailScope tail) :
    Realizes tables families (capturedScope.append (frontScope.append (.spent owner tailScope)))
      (capture.append (front.append (.spent owner answer caller tail))) :=
  saved.append (waiting.append (.spent outside))

/-- Join the local guard to the actual handler cut. Plan realization and exact
recursive owner accounting are derived for that capture, not supplied as
independent witnesses. -/
theorem checked_cut
    (cut : HandlerCut requested whole capture tail handler)
    (realized : Realizes tables families scope whole)
    (checked : checkCapture outward scope requested operation = true)
    (known : lookup operation (tables handler) = some contract)
    (disposes : contract.dispose = true) :
    ∃ capturedScope tailScope modes plan,
      Realizes tables families capturedScope capture ∧ Realizes tables families tailScope tail ∧
      scope = capturedScope.append tailScope ∧
      select requested operation scope = some (.handler capturedScope tailScope contract modes) ∧
      SourceRecursiveRoutes.Realizes capturedScope.shape capture plan ∧
      SourceRecursiveRoutes.Closing outward capturedScope.shape [] [] ∧
      ProtectionContexts.protectedMode capture.erase = false ∧
      makePlan capture = some plan ∧ (planOwners (plan.map CloseEntry.erase)).Perm capture.erase.owners := by
  obtain ⟨capturedScope, tailScope, saved, outside, same, selection⟩ := realized.cut cut
  cases annotated : lookupDependencies operation (families handler) with
  | none =>
      have absent : select requested operation scope = none := by
        simpa only [chosen, known, annotated] using selection operation
      simp [checkCapture, absent] at checked
  | some modes =>
      have found : select requested operation scope = some (.handler capturedScope tailScope contract modes) := by
        simpa only [chosen, known, annotated] using selection operation
      obtain ⟨unprotected, closing, available⟩ := disposing_capture checked found disposes
      obtain ⟨plan, shape⟩ := saved.closing unprotected
      exact ⟨capturedScope, tailScope, modes, plan, saved, outside, same, found, shape, closing,
        saved.held.symm.trans unprotected, shape.built, shape.owner_accounting⟩

/-- The same actual cut now obtains its complete existing closing certificate
without a separate successful plan or shape-realization premise. Ordinary
callback typing, resource support and one-shot owner inclusion are reused. -/
theorem checked_certificate
    (cut : HandlerCut requested whole capture tail handler)
    (realized : Realizes tables families scope whole)
    (checked : checkCapture record.annotation.closeEffects scope requested operation = true)
    (known : lookup operation (tables handler) = some contract)
    (disposes : contract.dispose = true)
    (supported : Supported capture.erase (Admission.outsideResources capture.erase))
    (typed : ScopedPorts.StackTyped signature tickets world capture input output)
    (internal : InternalUses capture.erase.liveTickets capture.erase.pending) :
    Nonempty (DeclaredClosingInvariant.Certificate signature world record capture) := by
  obtain ⟨capturedScope, tailScope, modes, plan, saved, outside, same, found, shape, closing, unprotected, built, owners⟩ :=
    checked_cut cut realized checked known disposes
  exact ⟨shape.certificate closing supported typed internal⟩

/-- Allocation retains the same recursively annotated saved scope. The
witnesses come from the actual cut rather than another candidate decomposition. -/
theorem capture_scope
    (cut : HandlerCut requested whole capture tail handler)
    (realized : Realizes tables families scope whole) :
    ∃ capturedScope tailScope,
      Realizes tables families capturedScope capture ∧ Realizes tables families tailScope tail ∧
      Realizes tables families (.live owner capturedScope tailScope) (.live owner input answer capture caller tail) ∧
      scope = capturedScope.append tailScope := by
  obtain ⟨capturedScope, tailScope, saved, outside, same, selected⟩ := realized.cut cut
  exact ⟨capturedScope, tailScope, saved, outside, .live saved outside, same⟩

namespace Examples

def actualTables : CallableProtectionFrames.Tables := fun _ => disposeTable
def actualFamilies : Families := fun _ => disposeDependencies
def actualStack : Stack := ScopedPorts.CompletionExamples.nested.append
  (.push (.handler InitialCleanupRouteGap.outerHandler) .nil)

theorem nested_stack_realized : Realizes actualTables actualFamilies nested actualStack := by
  have selected : Frame actualTables actualFamilies handlerE (.handler InitialCleanupRouteGap.outerHandler) := by
    change Frame actualTables actualFamilies
      (.handler InitialCleanupRouteGap.outerHandler.effectInst (actualTables InitialCleanupRouteGap.outerHandler)
        (actualFamilies InitialCleanupRouteGap.outerHandler)) (.handler InitialCleanupRouteGap.outerHandler)
    exact .handler
  exact .live (.push (Frame.cleanup (action := ScopedPorts.CompletionExamples.action)
    (dependencies := .request (.cell 4) 0)) .nil) (.push .cell (.push selected .nil))

theorem nested_stack_cut : HandlerCut effectE actualStack actualStack .nil InitialCleanupRouteGap.outerHandler := by
  apply HandlerCut.live
  apply HandlerCut.push
  · decide
  · exact .hit _ _ rfl

/-- Exercise the guard-to-plan theorem on the existing resource-bearing
callback inside a dormant continuation, using the actual outer handler. -/
theorem nested_checked_plan :
    ∃ plan, makePlan actualStack = some plan ∧
      plan = [.invoke ScopedPorts.CompletionExamples.action, .retire 6, .release 4 17] ∧
      (planOwners (plan.map CloseEntry.erase)).Perm actualStack.erase.owners := by
  obtain ⟨capturedScope, tailScope, modes, plan, saved, outside, same, found, shape, closing, unprotected, built, owners⟩ :=
    checked_cut nested_stack_cut nested_stack_realized nested_retained_cell_accepted (contract := ⟨true, some [], none⟩) rfl rfl
  have actual : makePlan actualStack = some [.invoke ScopedPorts.CompletionExamples.action, .retire 6, .release 4 17] := rfl
  exact ⟨plan, built, Option.some.inj (built.symm.trans actual), owners⟩

/-- An unrelated empty callback requirement list cannot realize the actual
cell-reading callback. The route check cannot be redirected to that scope. -/
theorem erased_callback_requirements_rejected :
    ¬ Realizes actualTables actualFamilies (.cleanup [] .pure .nil)
      (.push (.armed ScopedPorts.CompletionExamples.action) .nil) := by
  generalize scopeSame : Scope.cleanup [] .pure .nil = scope
  intro realized
  cases realized with
  | push frame rest => cases frame with
    | cleanup => cases scopeSame

end Examples

end Ash.OneShot.SourceDependencyCapture

#print axioms Ash.OneShot.SourceDependencyCapture.Frame.append
#print axioms Ash.OneShot.SourceDependencyCapture.Realizes.append
#print axioms Ash.OneShot.SourceDependencyCapture.Frame.held
#print axioms Ash.OneShot.SourceDependencyCapture.Realizes.held
#print axioms Ash.OneShot.SourceDependencyCapture.Realizes.closing
#print axioms Ash.OneShot.SourceDependencyCapture.chosen_prepend
#print axioms Ash.OneShot.SourceDependencyCapture.Frame.select_miss
#print axioms Ash.OneShot.SourceDependencyCapture.Realizes.cut
#print axioms Ash.OneShot.SourceDependencyCapture.resume_recomposition

#print axioms Ash.OneShot.SourceDependencyCapture.checked_cut

#print axioms Ash.OneShot.SourceDependencyCapture.checked_certificate

#print axioms Ash.OneShot.SourceDependencyCapture.capture_scope

#print axioms Ash.OneShot.SourceDependencyCapture.Examples.nested_stack_realized

#print axioms Ash.OneShot.SourceDependencyCapture.Examples.nested_stack_cut

#print axioms Ash.OneShot.SourceDependencyCapture.Examples.nested_checked_plan

#print axioms Ash.OneShot.SourceDependencyCapture.Examples.erased_callback_requirements_rejected


namespace Ash.OneShot.SourceDependencyCapture
open ScopedExpressions ScopedExecution ProtectionContracts

/-- Accessible source resources follow the active lexical spine. A dormant
    capture owns its cells but does not expose them to its caller. -/
def Scope.visibleResources : Scope → List Nat
  | .nil => []
  | .plain _ rest | .handler _ _ _ rest | .cleanup _ _ rest | .running rest | .spent _ rest => rest.visibleResources
  | .cell identity rest => identity :: rest.visibleResources
  | .live _ _ rest => rest.visibleResources

theorem Frame.visible_resources (frame : Frame tables families layer entry) :
    (layer rest).visibleResources = entry.erase.visible ++ rest.visibleResources := by
  cases frame <;> rfl

theorem Realizes.visible_resources (source : Realizes tables families scope stack) :
    scope.visibleResources = stack.erase.visible := by
  induction source with
  | nil => rfl
  | push frame tail ih => rw [frame.visible_resources, ih]; rfl
  | live inside outside ihInside ihOutside => exact ihOutside
  | spent tail ih => exact ih

/-- The selected source suffix is the actual handler's outer suffix. A finite
    operand annotation checked there supplies the runtime capture condition. -/
theorem source_payload_at_cut {operand : Code}
    (source : Realizes tables families scope whole)
    (cut : HandlerCut requested whole captured tail handler)
    (selected : select requested operation scope = some (.handler capturedScope tailScope contract modes))
    (operandSupport : Syntax.resourceDependencies operand.dependencies ⊆ bound)
    (available : bound ⊆ tailScope.visibleResources ++ ambient) :
    Syntax.resourceDependencies operand.dependencies ⊆ tail.erase.visible ++ ambient := by
  obtain ⟨actualCapture, actualTail, inside, outside, same, selection⟩ := source.cut cut
  rw [selection operation] at selected
  unfold chosen at selected
  cases known : lookup operation (tables handler) with
  | none => simp [known] at selected
  | some offered => cases annotated : lookupDependencies operation (families handler) with
    | none => simp [known, annotated] at selected
    | some dependencies =>
        simp only [known, annotated, Option.some.injEq] at selected
        cases selected
        simpa only [outside.visible_resources] using operandSupport.trans available

#print axioms Ash.OneShot.SourceDependencyCapture.Frame.visible_resources
#print axioms Ash.OneShot.SourceDependencyCapture.Realizes.visible_resources
#print axioms Ash.OneShot.SourceDependencyCapture.source_payload_at_cut
end Ash.OneShot.SourceDependencyCapture

namespace Ash.OneShot.SourceDependencyCapture
open ScopedExpressions ScopedExecution ProtectionContracts

/-- A finite lexical operand-support check supplies the ordinary machine's
capture condition for every runtime cut realizing that source selection. -/
theorem source_request_access {operand : Code}
    (source : Realizes tables families scope whole)
    (selected : select requested operation scope = some (.handler capturedScope tailScope contract modes))
    (operandSupport : Syntax.resourceDependencies operand.dependencies ⊆ bound)
    (available : bound ⊆ tailScope.visibleResources ++ ambient) :
    LexicalUnwind.AccessConditions
      ⟨.perform (Instantiation.freezeEffect requested) operation operand, caller, whole⟩ ambient := by
  constructor
  · intro identity payload answer savedScope current value tail same closed
    have expressionSame := congrArg Configuration.expression same
    dsimp only at expressionSame
    rw [← expressionSame] at closed
    cases closed.1
  · intro requested' operation' operand' caller' whole' capture tail handler same cut closed
    have expressionSame := congrArg Configuration.expression same
    have stackSame := congrArg Configuration.stack same
    dsimp only at expressionSame stackSame
    cases stackSame
    obtain ⟨effectSame, operationSame, operandSame⟩ := Code.perform.inj expressionSame
    cases freeze_effect_injective effectSame
    cases operationSame
    cases operandSame
    exact source_payload_at_cut source cut selected operandSupport available

end Ash.OneShot.SourceDependencyCapture
#print axioms Ash.OneShot.SourceDependencyCapture.source_request_access


namespace Ash.OneShot.SourceDependencyCapture
/-- Splitting the same physical prefix and complete lexical annotation fixes
both source fragments, without requiring unique typing derivations. -/
theorem Realizes.append_scopes_unique
    (first : Realizes tables families firstScope segment)
    (second : Realizes tables families secondScope segment)
    (same : firstScope.append firstTail = secondScope.append secondTail) :
    firstScope = secondScope ∧ firstTail = secondTail := by
  induction first generalizing secondScope firstTail secondTail with
  | nil => cases second; exact ⟨rfl, same⟩
  | push frame rest ih => cases second with
      | push other later =>
          cases frame <;> cases other <;> simp_all [Scope.append] <;>
            first | exact ih later same | exact ih later same.2
  | live saved rest ihSaved ihRest => cases second with
      | live other later =>
          simp_all [Scope.append]
          exact ihRest later same.2
  | spent rest ih => cases second with
      | spent later =>
          simp_all [Scope.append]
          exact ih later same
end Ash.OneShot.SourceDependencyCapture
#print axioms Ash.OneShot.SourceDependencyCapture.Realizes.append_scopes_unique
