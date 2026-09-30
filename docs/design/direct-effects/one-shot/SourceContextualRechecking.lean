import SourceContextualRequirements
import SourceContextualForest

/-! Reconstruct stored contextual certificates by checking finite requirements
at their actual receiving scopes. Handler recipes survive rearrangement as
source evidence; the new scope check determines whether their interpretations
remain suitable. This is not complete source admission for an invocation. -/
namespace Ash.OneShot.SourceContextualRechecking
open ScopedExpressions ScopedExecution
open SourceContextualRequirements (DeclarationRecipes checkRequirements)
abbrev Receiving := SourceDependencyCapture.Scope
abbrev Required := HandlerData → List SourceContextualRequirements.Requirement

def frameHandlers : ExecFrame → List HandlerData
  | .handler data => [data]
  | _ => []

def handlers : Stack → List HandlerData
  | .nil => []
  | .push entry rest => frameHandlers entry ++ handlers rest
  | .live _ _ _ captured _ rest => handlers captured ++ handlers rest
  | .spent _ _ _ rest => handlers rest

theorem handlers_append (first second : Stack) : handlers (first.append second) = handlers first ++ handlers second := by
  induction first <;> simp_all [Stack.append, handlers, List.append_assoc]

def checkFrame (required : Required) (entry : ExecFrame) (outside : Receiving) : Bool :=
  match entry with
  | .handler data => checkRequirements outside (required data)
  | _ => true

def checkForest (required : Required) : Stack → Receiving → Receiving → Bool
  | .nil, .nil, _ => true
  | .push entry rest, .plain _ restScope, outside
  | .push entry rest, .handler _ _ _ restScope, outside
  | .push entry rest, .cell _ restScope, outside
  | .push entry rest, .cleanup _ _ restScope, outside
  | .push entry rest, .running restScope, outside =>
      checkFrame required entry (restScope.append outside) && checkForest required rest restScope outside
  | .live _ _ _ captured _ rest, .live _ capturedScope restScope, outside =>
      checkForest required captured capturedScope (restScope.append outside) && checkForest required rest restScope outside
  | .spent _ _ _ rest, .spent _ restScope, outside => checkForest required rest restScope outside
  | _, _, _ => false

theorem check_forest_push (frame : SourceDependencyCapture.Frame tables families layer entry) :
    checkForest required (.push entry rest) (layer restScope) outside =
      (checkFrame required entry (restScope.append outside) && checkForest required rest restScope outside) := by
  cases frame <;> rfl

theorem recheck_frame
    (recipes : ∀ handler ∈ frameHandlers entry,
      DeclarationRecipes outward handler.clauses (families handler) (required handler))
    (checked : checkFrame required entry outside = true) :
    SourceContextualForest.Frame outward families outside entry := by
  cases entry with
  | handler data => exact .handler ((recipes data List.mem_cons_self).recheck checked)
  | plain => exact .plain
  | cell => exact .cell
  | armed => exact .armed
  | running => exact .running
  | unwinding => exact .unwinding
  | closing => exact .closing
  | retiring => exact .retiring

/-- The only supplied proof per handler is its structural source recipe.
The executable test supplies current interpretation capabilities at every
actual suffix, including suffixes inside dormant captures. -/
theorem recheck_forest
    (realized : SourceDependencyCapture.Realizes tables families scope stack)
    (recipes : ∀ handler ∈ handlers stack,
      DeclarationRecipes outward handler.clauses (families handler) (required handler))
    (checked : checkForest required stack scope outside = true) :
    SourceContextualForest.Forest outward tables families stack scope outside := by
  induction realized generalizing outside with
  | nil => exact .nil
  | push frame tail ih =>
      rw [check_forest_push frame, Bool.and_eq_true] at checked
      exact .push frame
        (recheck_frame (fun handler member => recipes handler (List.mem_append_left _ member)) checked.1)
        (ih (fun handler member => recipes handler (List.mem_append_right _ member)) checked.2)
  | live saved tail ihSaved ihTail =>
      rw [checkForest, Bool.and_eq_true] at checked
      exact .live
        (ihSaved (fun handler member => recipes handler (List.mem_append_left _ member)) checked.1)
        (ihTail (fun handler member => recipes handler (List.mem_append_right _ member)) checked.2)
  | spent tail ih => exact .spent (ih recipes checked)

/-- Full-prefix resumption reorders existing handler occurrences but does
not introduce a new declaration. This membership law transports source recipes
only; it does not exchange the receiving interpretations. -/
theorem resume_handlers {capture front tail : Stack} (handler : HandlerData) :
    handler ∈ handlers (capture.append (front.append (.spent owner answer caller tail))) ↔
      handler ∈ handlers (front.append (.live owner input answer capture savedCaller tail)) := by
  simp only [handlers_append, handlers, List.mem_append]
  constructor
  · rintro (inside | waiting | outside)
    · exact Or.inr (Or.inl inside)
    · exact Or.inl waiting
    · exact Or.inr (Or.inr outside)
  · rintro (waiting | inside | outside)
    · exact Or.inr (Or.inl waiting)
    · exact Or.inl inside
    · exact Or.inr (Or.inr outside)

/-- Rebuild certificates after full-prefix resumption using the retained
recipes and a finite check at the actual recomposed context. No successor
forest certificate or arbitrary context-weakening premise is assumed. -/
theorem resume_rechecked
    (saved : SourceDependencyCapture.Realizes tables families capturedScope capture)
    (waiting : SourceDependencyCapture.Realizes tables families frontScope front)
    (outside : SourceDependencyCapture.Realizes tables families tailScope tail)
    (recipes : ∀ handler ∈ handlers (front.append (.live owner input answer capture savedCaller tail)),
      DeclarationRecipes outward handler.clauses (families handler) (required handler))
    (checked : checkForest required (capture.append (front.append (.spent owner answer caller tail)))
      (capturedScope.append (frontScope.append (.spent owner tailScope))) outer = true) :
    SourceContextualForest.Forest outward tables families
      (capture.append (front.append (.spent owner answer caller tail)))
      (capturedScope.append (frontScope.append (.spent owner tailScope))) outer :=
  recheck_forest (saved.append (waiting.append (.spent outside)))
    (fun handler member => recipes handler ((resume_handlers handler).mp member)) checked

/-- Scheduled cleanup frames contain callback code but introduce no already
installed handler. Admission of handlers later installed by that code remains
a source obligation. -/
theorem handlers_close_control (plan : List CloseEntry) : handlers (closeControl caller plan) = [] := by
  induction plan with
  | nil => rfl
  | cons entry rest ih => cases entry <;> simp only [closeControl, handlers, CloseEntry.frame, frameHandlers, ih, List.nil_append]

theorem dispose_handlers {front captured tail : Stack} (plan : List CloseEntry) :
    handlers ((closeControl caller plan).append
      (.push (.closing closeId caller) (front.append (.spent owner answer returnScope tail)))) ⊆
      handlers (front.append (.live owner input answer captured savedCaller tail)) := by
  intro handler member
  simp only [handlers_append, handlers_close_control, handlers, frameHandlers, List.nil_append, List.mem_append] at member ⊢
  exact member.elim Or.inl (fun outside => Or.inr (Or.inr outside))

/-- Disposal reuses all remaining handler recipes and rebuilds their
certificates at the concrete cleanup/caller stack after a finite scope check. -/
theorem dispose_rechecked
    (scheduled : SourceDependencyCapture.Realizes tables families closingScope (closeControl caller plan))
    (waiting : SourceDependencyCapture.Realizes tables families frontScope front)
    (outside : SourceDependencyCapture.Realizes tables families tailScope tail)
    (recipes : ∀ handler ∈ handlers (front.append (.live owner input answer captured savedCaller tail)),
      DeclarationRecipes outward handler.clauses (families handler) (required handler))
    (checked : checkForest required
      ((closeControl caller plan).append (.push (.closing closeId caller) (front.append (.spent owner answer caller tail))))
      (closingScope.append (.running (frontScope.append (.spent owner tailScope)))) outer = true) :
    SourceContextualForest.Forest outward tables families
      ((closeControl caller plan).append (.push (.closing closeId caller) (front.append (.spent owner answer caller tail))))
      (closingScope.append (.running (frontScope.append (.spent owner tailScope)))) outer :=
  recheck_forest (scheduled.append (.push .closing (waiting.append (.spent outside))))
    (fun handler member => recipes handler (dispose_handlers plan member)) checked

namespace Examples
open SourceContextualForest.Examples (inner outer)

def callerHandler : HandlerData := ⟨13, .user 103 [], .nil, .none, .unit, rfl⟩
def tables : CallableProtectionFrames.Tables := fun handler =>
  if handler.activation = 13 then [] else SourceContextualForest.Examples.tables handler
def families : SourceDependencyCapture.Families := fun handler =>
  if handler.activation = 13 then [] else SourceContextualForest.Examples.families handler
def required : Required := fun handler =>
  if handler.activation = 11 then [(SourceDependencyHandlerGap.effect, 0)] else []
def captured : Stack := .push (.handler inner) .nil
def front : Stack := .push (.handler callerHandler) .nil
def tail : Stack := .push (.handler outer) .nil
def capturedScope : Receiving := .handler SourceDependencyHandlerGap.effect
  SourceDependencyHandlerGap.table SourceDependencyHandlerGap.dependencies .nil
def frontScope : Receiving := .handler (.user 103 []) [] [] .nil

theorem retained_recipes : ∀ handler ∈ handlers
    (front.append (.live 19 .unit .unit captured .none tail)),
    DeclarationRecipes outward handler.clauses (families handler) (required handler) := by
  intro handler member
  simp only [handlers_append, handlers, frameHandlers, front, captured, tail,
    List.append_nil, List.mem_append, List.mem_singleton] at member
  rcases member with rfl | rfl | rfl
  · exact .nil
  · exact SourceContextualRequirements.Examples.declaration_recipes
  · exact SourceContextualRequirements.Examples.resume_declarations

/-- The general resumption theorem admits an actual nonempty caller stack.
The saved handler still delegates to F through the caller's unrelated handler.
This checks the stored component, not reachability of a full runtime state. -/
theorem nonempty_caller_rechecked : SourceContextualForest.Forest outward tables families
    (captured.append (front.append (.spent 19 .unit .none tail)))
    (capturedScope.append (frontScope.append (.spent 19 SourceDependencyHandlerGap.outside))) .nil :=
  resume_rechecked (required := required)
    (.push (@SourceDependencyCapture.Frame.handler tables families inner) .nil)
    (.push (@SourceDependencyCapture.Frame.handler tables families callerHandler) .nil)
    (.push (@SourceDependencyCapture.Frame.handler tables families outer) .nil)
    retained_recipes (by decide)

end Examples

end Ash.OneShot.SourceContextualRechecking

#print axioms Ash.OneShot.SourceContextualRechecking.handlers_append
#print axioms Ash.OneShot.SourceContextualRechecking.check_forest_push
#print axioms Ash.OneShot.SourceContextualRechecking.recheck_frame
#print axioms Ash.OneShot.SourceContextualRechecking.recheck_forest
#print axioms Ash.OneShot.SourceContextualRechecking.resume_handlers
#print axioms Ash.OneShot.SourceContextualRechecking.resume_rechecked
#print axioms Ash.OneShot.SourceContextualRechecking.handlers_close_control
#print axioms Ash.OneShot.SourceContextualRechecking.dispose_handlers
#print axioms Ash.OneShot.SourceContextualRechecking.dispose_rechecked
#print axioms Ash.OneShot.SourceContextualRechecking.Examples.retained_recipes
#print axioms Ash.OneShot.SourceContextualRechecking.Examples.nonempty_caller_rechecked

namespace Ash.OneShot.SourceContextualRechecking.Lexical
open ScopedExpressions ScopedExecution
open SourceContextualRequirements (DeclarationRecipes checkRequirements)
theorem recheck_frame
    (recipes : ∀ handler ∈ frameHandlers entry,
      DeclarationRecipes outward handler.clauses (families handler) (required handler))
    (checked : checkFrame required entry outside = true) :
    SourceContextualForest.Lexical.Frame outward families outside entry := by
  cases entry with
  | handler data => exact .handler (SourceContextualRequirements.Lexical.recheck_declarations (recipes data List.mem_cons_self) checked)
  | plain => exact .plain
  | cell => exact .cell
  | armed => exact .armed
  | running => exact .running
  | unwinding => exact .unwinding
  | closing => exact .closing
  | retiring => exact .retiring

/-- The only supplied proof per handler is its structural source recipe.
The executable test supplies current interpretation capabilities at every
actual suffix, including suffixes inside dormant captures. -/
theorem recheck_forest
    (realized : SourceDependencyCapture.Realizes tables families scope stack)
    (recipes : ∀ handler ∈ handlers stack,
      DeclarationRecipes outward handler.clauses (families handler) (required handler))
    (checked : checkForest required stack scope outside = true) :
    SourceContextualForest.Lexical.Forest outward tables families stack scope outside := by
  induction realized generalizing outside with
  | nil => exact .nil
  | push frame tail ih =>
      rw [check_forest_push frame, Bool.and_eq_true] at checked
      exact .push frame
        (recheck_frame (fun handler member => recipes handler (List.mem_append_left _ member)) checked.1)
        (ih (fun handler member => recipes handler (List.mem_append_right _ member)) checked.2)
  | live saved tail ihSaved ihTail =>
      rw [checkForest, Bool.and_eq_true] at checked
      exact .live
        (ihSaved (fun handler member => recipes handler (List.mem_append_left _ member)) checked.1)
        (ihTail (fun handler member => recipes handler (List.mem_append_right _ member)) checked.2)
  | spent tail ih => exact .spent (ih recipes checked)

/-- Rebuild certificates after full-prefix resumption using the retained
recipes and a finite check at the actual recomposed context. No successor
forest certificate or arbitrary context-weakening premise is assumed. -/
theorem resume_rechecked
    (saved : SourceDependencyCapture.Realizes tables families capturedScope capture)
    (waiting : SourceDependencyCapture.Realizes tables families frontScope front)
    (outside : SourceDependencyCapture.Realizes tables families tailScope tail)
    (recipes : ∀ handler ∈ handlers (front.append (.live owner input answer capture savedCaller tail)),
      DeclarationRecipes outward handler.clauses (families handler) (required handler))
    (checked : checkForest required (capture.append (front.append (.spent owner answer caller tail)))
      (capturedScope.append (frontScope.append (.spent owner tailScope))) outer = true) :
    SourceContextualForest.Lexical.Forest outward tables families
      (capture.append (front.append (.spent owner answer caller tail)))
      (capturedScope.append (frontScope.append (.spent owner tailScope))) outer :=
  recheck_forest (saved.append (waiting.append (.spent outside)))
    (fun handler member => recipes handler ((resume_handlers handler).mp member)) checked

/-- Lexical disposal retains the captured handler occurrences until their
scopes unwind. The closing delimiter introduces no handler. -/
theorem discard_handlers {capture front tail : Stack} (handler : HandlerData) :
    handler ∈ handlers (capture.append (.push (.closing closeId caller)
      (front.append (.spent owner answer caller tail)))) ↔
      handler ∈ handlers (front.append (.live owner input answer capture savedCaller tail)) := by
  simpa only [handlers_append, handlers, frameHandlers, List.nil_append] using
    (resume_handlers (capture := capture) (front := front) (tail := tail)
      (owner := owner) (answer := answer) (caller := caller) (input := input)
      (savedCaller := savedCaller) handler)

/-- Reconstruct the retained handler certificates at the actual lexical
unwind stack. This needs an executable receiving-scope check, not a close plan
or an assumed successor forest. -/
theorem discard_rechecked
    (saved : SourceDependencyCapture.Realizes tables families capturedScope capture)
    (waiting : SourceDependencyCapture.Realizes tables families frontScope front)
    (outside : SourceDependencyCapture.Realizes tables families tailScope tail)
    (recipes : ∀ handler ∈ handlers (front.append (.live owner input answer capture savedCaller tail)),
      DeclarationRecipes outward handler.clauses (families handler) (required handler))
    (checked : checkForest required
      (capture.append (.push (.closing closeId caller) (front.append (.spent owner answer caller tail))))
      (capturedScope.append (.running (frontScope.append (.spent owner tailScope)))) outer = true) :
    SourceContextualForest.Lexical.Forest outward tables families
      (capture.append (.push (.closing closeId caller) (front.append (.spent owner answer caller tail))))
      (capturedScope.append (.running (frontScope.append (.spent owner tailScope)))) outer :=
  recheck_forest (saved.append (.push .closing (waiting.append (.spent outside))))
    (fun handler member => recipes handler ((discard_handlers handler).mp member)) checked

namespace Examples
open Ash.OneShot.SourceContextualRechecking.Examples
open SourceContextualForest.Examples (inner outer)

/-- Nonempty caller scopes and outer delegation survive lexical resumption. -/
theorem nonempty_caller_rechecked : SourceContextualForest.Lexical.Forest outward tables families
    (captured.append (front.append (.spent 19 .unit .none tail)))
    (capturedScope.append (frontScope.append (.spent 19 SourceDependencyHandlerGap.outside))) .nil :=
  resume_rechecked (required := required)
    (.push (@SourceDependencyCapture.Frame.handler tables families inner) .nil)
    (.push (@SourceDependencyCapture.Frame.handler tables families callerHandler) .nil)
    (.push (@SourceDependencyCapture.Frame.handler tables families outer) .nil)
    retained_recipes (by decide)

/-- Disposal retains the inner delegating handler above the closing marker
and the nonempty caller below it. This checks certificates, not reachability. -/
theorem nonempty_caller_discard_rechecked : SourceContextualForest.Lexical.Forest outward tables families
    (captured.append (.push (.closing 29 .none) (front.append (.spent 19 .unit .none tail))))
    (capturedScope.append (.running (frontScope.append (.spent 19 SourceDependencyHandlerGap.outside)))) .nil :=
  discard_rechecked (required := required)
    (.push (@SourceDependencyCapture.Frame.handler tables families inner) .nil)
    (.push (@SourceDependencyCapture.Frame.handler tables families callerHandler) .nil)
    (.push (@SourceDependencyCapture.Frame.handler tables families outer) .nil)
    retained_recipes (by decide)
end Examples
end Ash.OneShot.SourceContextualRechecking.Lexical

#print axioms Ash.OneShot.SourceContextualRechecking.Lexical.recheck_frame
#print axioms Ash.OneShot.SourceContextualRechecking.Lexical.recheck_forest
#print axioms Ash.OneShot.SourceContextualRechecking.Lexical.resume_rechecked
#print axioms Ash.OneShot.SourceContextualRechecking.Lexical.discard_handlers
#print axioms Ash.OneShot.SourceContextualRechecking.Lexical.discard_rechecked
#print axioms Ash.OneShot.SourceContextualRechecking.Lexical.Examples.nonempty_caller_rechecked
#print axioms Ash.OneShot.SourceContextualRechecking.Lexical.Examples.nonempty_caller_discard_rechecked

namespace Ash.OneShot.SourceContextualRechecking.Lexical
open ScopedExpressions ScopedExecution
open SourceContextualHints (checkCapability checkRequirements)

private theorem capability_prefix_congr
    (same : ∀ effect operation, checkCapability before effect operation = checkCapability after effect operation)
    (front : SourceDependencyCapture.Scope) :
    ∀ effect operation, checkCapability (front.append before) effect operation =
      checkCapability (front.append after) effect operation := by
  intro effect operation
  simp only [SourceHandlerRequirements.capability_append, same]

/-- Receiving scopes with identical operation capabilities give identical
finite handler checks, including in dormant captured branches. This does not
claim that arbitrary contextual declaration judgments are interchangeable. -/
theorem check_forest_outside
    (realized : SourceDependencyCapture.Realizes tables families scope stack)
    (same : ∀ effect operation, checkCapability before effect operation = checkCapability after effect operation) :
    checkForest required stack scope before = checkForest required stack scope after := by
  induction realized generalizing before after with
  | nil => rfl
  | push frame tail ih =>
      rw [check_forest_push frame, check_forest_push frame, ih same]
      congr 1
      cases frame <;> try rfl
      simp only [checkFrame, checkRequirements, capability_prefix_congr same]
  | live saved tail ihSaved ihTail =>
      simp only [checkForest, ihSaved (capability_prefix_congr same _), ihTail same]
  | spent tail ih => exact ih same

/-- Factor the existing finite checker at a physical stack append. -/
theorem check_forest_append
    (first : SourceDependencyCapture.Realizes tables families firstScope firstStack)
    (_second : SourceDependencyCapture.Realizes tables families secondScope secondStack) :
    checkForest required (firstStack.append secondStack) (firstScope.append secondScope) outside =
      (checkForest required firstStack firstScope (secondScope.append outside) &&
        checkForest required secondStack secondScope outside) := by
  induction first generalizing outside with
  | nil => rfl
  | push frame tail ih =>
      rw [Stack.append, frame.append, check_forest_push frame, check_forest_push frame, ih]
      simp only [SourceDependencyChecks.scope_append_assoc, Bool.and_assoc]
  | live saved tail ihSaved ihTail =>
      simp only [Stack.append, SourceDependencyCapture.Scope.append, checkForest, ihTail,
        SourceDependencyChecks.scope_append_assoc, Bool.and_assoc]
  | spent tail ih => exact ih

/-- Every local unwind step retains only existing declarations. Live-owner
retirement keeps the captured scopes before the new retirement marker. -/
theorem advance_handlers (step : LexicalUnwind.Advance before after discharged) :
    handlers after ⊆ handlers before := by
  cases step <;> simp only [handlers, frameHandlers, handlers_append, List.nil_append]
  all_goals intro handler member
  all_goals first | exact member | exact List.mem_cons_of_mem _ member

/-- All six administrative unwind steps preserve the finite handler checks.
The live-owner case reuses capability lookup through the retirement delimiter;
no checked successor is supplied. -/
theorem advance_checked
    (step : LexicalUnwind.Advance before after discharged)
    (realized : SourceDependencyCapture.Realizes tables families scope before)
    (checked : checkForest required before scope outside = true) :
    ∃ nextScope, SourceDependencyCapture.Realizes tables families nextScope after ∧
      checkForest required after nextScope outside = true := by
  cases step with
  | plain => cases realized with | push frame tail => cases frame with
      | plain => exact ⟨_, tail, checked⟩
  | handler => cases realized with | push frame tail => cases frame with
      | handler =>
          rw [checkForest, Bool.and_eq_true] at checked
          exact ⟨_, tail, checked.2⟩
  | cell => cases realized with | push frame tail => cases frame with
      | cell => exact ⟨_, tail, checked⟩
  | spent => cases realized with | spent tail => exact ⟨_, tail, checked⟩
  | retire => cases realized with | push frame tail => cases frame with
      | retiring => exact ⟨_, tail, checked⟩
  | live => cases realized with
      | @live capturedScope captured restScope rest owner input answer caller saved tail =>
          rw [checkForest, Bool.and_eq_true] at checked
          obtain ⟨savedCheck, tailCheck⟩ := checked
          refine ⟨_, saved.append (.push .retiring tail), ?_⟩
          rw [check_forest_append saved (.push .retiring tail), Bool.and_eq_true]
          refine ⟨?_, tailCheck⟩
          have same : ∀ effect operation,
              checkCapability (restScope.append outside) effect operation =
                checkCapability ((SourceDependencyCapture.Scope.running restScope).append outside) effect operation := by
            intro effect operation
            exact (SourceHandlerRequirements.capability_prepend (first := .running (restScope.append outside))
              (second := restScope.append outside) (layer := .running) rfl).symm
          exact (check_forest_outside saved same) ▸ savedCheck

/-- Retained structural recipes and current finite checks reconstruct lexical
handler certificates after every administrative unwind transition. -/
theorem advance_rechecked
    (step : LexicalUnwind.Advance before after discharged)
    (realized : SourceDependencyCapture.Realizes tables families scope before)
    (recipes : ∀ handler ∈ handlers before,
      SourceContextualRequirements.DeclarationRecipes outward handler.clauses (families handler) (required handler))
    (checked : checkForest required before scope outside = true) :
    ∃ nextScope, checkForest required after nextScope outside = true ∧
      SourceContextualForest.Lexical.Forest outward tables families after nextScope outside := by
  obtain ⟨nextScope, next, nextCheck⟩ := advance_checked step realized checked
  exact ⟨nextScope, nextCheck, recheck_forest next
    (fun handler member => recipes handler (advance_handlers step member)) nextCheck⟩

end Ash.OneShot.SourceContextualRechecking.Lexical
#print axioms Ash.OneShot.SourceContextualRechecking.Lexical.check_forest_outside
#print axioms Ash.OneShot.SourceContextualRechecking.Lexical.check_forest_append
#print axioms Ash.OneShot.SourceContextualRechecking.Lexical.advance_handlers
#print axioms Ash.OneShot.SourceContextualRechecking.Lexical.advance_checked
#print axioms Ash.OneShot.SourceContextualRechecking.Lexical.advance_rechecked

namespace Ash.OneShot.SourceContextualRechecking.Lexical
open ScopedExpressions ScopedExecution
open SourceContextualHints (checkCapability)
/-- Keep callback checks and finite handler checks at the same actual source
scope. Stack realization alone does not identify callback annotations. -/
theorem advance_unwind_checked
    (step : LexicalUnwind.Advance before after discharged)
    (realized : SourceDependencyCapture.Realizes tables families scope before)
    (checked : checkForest required before scope outside = true)
    (callbacks : SourceDependencyChecks.Lexical.Unwind outward actions phases world scope outside) :
    SourceDependencyCapture.Realizes tables families scope.afterUnwind after ∧
      checkForest required after scope.afterUnwind outside = true ∧
      SourceDependencyChecks.Lexical.Unwind outward actions phases world scope.afterUnwind outside := by
  cases step with
  | plain => cases realized with | push frame tail => cases frame with
      | plain => cases callbacks with | plain rest => exact ⟨tail, checked, rest⟩
  | handler => cases realized with | push frame tail => cases frame with
      | handler =>
          rw [checkForest, Bool.and_eq_true] at checked
          cases callbacks with | handler rest => exact ⟨tail, checked.2, rest⟩
  | cell => cases realized with | push frame tail => cases frame with
      | cell => cases callbacks with | cell rest => exact ⟨tail, checked, rest⟩
  | spent => cases realized with | spent tail => cases callbacks with | spent rest => exact ⟨tail, checked, rest⟩
  | retire => cases realized with | push frame tail => cases frame with
      | retiring => cases callbacks with | running rest => exact ⟨tail, checked, rest⟩
  | live => cases realized with
      | @live capturedScope captured restScope rest owner input answer caller saved tail =>
          rw [checkForest, Bool.and_eq_true] at checked
          obtain ⟨savedCheck, tailCheck⟩ := checked
          have nextCallbacks : SourceDependencyChecks.Lexical.Unwind outward actions phases world
              (capturedScope.append (.running restScope)) outside := by
            cases callbacks with
            | live inside rest =>
                apply SourceDependencyChecks.Lexical.Unwind.of_traversal
                exact SourceDependencyChecks.UnwindPending.append_iff.mpr ⟨inside.traversal, .running rest.traversal⟩
          refine ⟨saved.append (.push .retiring tail), ?_, nextCallbacks⟩
          dsimp only [SourceDependencyCapture.Scope.afterUnwind]
          rw [check_forest_append saved (.push .retiring tail), Bool.and_eq_true]
          refine ⟨?_, tailCheck⟩
          have same : ∀ effect operation,
              checkCapability (restScope.append outside) effect operation =
                checkCapability ((SourceDependencyCapture.Scope.running restScope).append outside) effect operation := by
            intro effect operation
            exact (SourceHandlerRequirements.capability_prepend (first := .running (restScope.append outside))
              (second := restScope.append outside) (layer := .running) rfl).symm
          exact (check_forest_outside saved same) ▸ savedCheck

end Ash.OneShot.SourceContextualRechecking.Lexical
#print axioms Ash.OneShot.SourceContextualRechecking.Lexical.advance_unwind_checked
