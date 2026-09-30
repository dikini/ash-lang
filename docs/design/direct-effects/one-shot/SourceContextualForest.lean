import SourceContextualClauses

/-! Contextual declaration certificates attached to actual execution frames.
Every handler is checked at its exact annotated suffix and outside scope.
Dormant captures retain that context recursively. This is the stored-certificate
component; it does not assert source typing or the full runtime invariant. -/
namespace Ash.OneShot.SourceContextualForest
open ScopedExpressions ScopedExecution
open SourceContextualClauses (FamilyAt ModeAt DeclarationsAt)
abbrev Receiving := SourceDependencyCapture.Scope

theorem ModeAt.project_tail (scheme : ModeAt outward rights tail family)
    (same : SourceDependencyProjection.project tail = SourceDependencyProjection.project nextTail) :
    ModeAt outward rights nextTail family := by
  cases scheme with
  | unavailable => exact .unavailable
  | available checked => exact .available (checked.project_tail same)

theorem DeclarationsAt.project_tail (schemes : DeclarationsAt outward tail clauses families)
    (same : SourceDependencyProjection.project tail = SourceDependencyProjection.project nextTail) :
    DeclarationsAt outward nextTail clauses families := by
  induction schemes with
  | nil => exact .nil
  | cons ordinary protectedMode rest ih => exact .cons (ModeAt.project_tail ordinary same) (ModeAt.project_tail protectedMode same) ih

inductive Frame (outward : List Instance) (families : SourceDependencyCapture.Families)
    (outside : Receiving) : ExecFrame → Prop where
  | plain : Frame outward families outside (.plain data)
  | handler (declarations : DeclarationsAt outward outside data.clauses (families data)) :
      Frame outward families outside (.handler data)
  | cell : Frame outward families outside (.cell identity payload scope answer)
  | armed : Frame outward families outside (.armed data)
  | running : Frame outward families outside (.running data saved closed)
  | unwinding : Frame outward families outside (.unwinding data)
  | closing : Frame outward families outside (.closing identity scope)
  | retiring : Frame outward families outside (.retiring owner)

inductive Forest (outward : List Instance) (tables : CallableProtectionFrames.Tables)
    (families : SourceDependencyCapture.Families) : Stack → Receiving → Receiving → Prop where
  | nil : Forest outward tables families .nil .nil outside
  | push (realized : SourceDependencyCapture.Frame tables families layer entry)
      (frame : Frame outward families (restScope.append outside) entry)
      (tail : Forest outward tables families rest restScope outside) :
      Forest outward tables families (.push entry rest) (layer restScope) outside
  | live (saved : Forest outward tables families captured capturedScope (restScope.append outside))
      (tail : Forest outward tables families rest restScope outside) :
      Forest outward tables families (.live owner input answer captured caller rest) (.live owner capturedScope restScope) outside
  | spent (tail : Forest outward tables families rest restScope outside) :
      Forest outward tables families (.spent owner answer caller rest) (.spent owner restScope) outside

theorem Forest.realizes (source : Forest outward tables families stack scope outside) :
    SourceDependencyCapture.Realizes tables families scope stack := by
  induction source with
  | nil => exact .nil
  | push realized frame tail ih => exact .push realized ih
  | live saved tail ihSaved ihTail => exact .live ihSaved ihTail
  | spent tail ih => exact .spent ih

theorem Frame.of_uniform (source : SourceDependencySchemes.Stored.Frame outward families entry) :
    Frame outward families outside entry := by
  cases source with
  | plain => exact .plain
  | handler declarations => exact .handler (.of_uniform declarations)
  | cell => exact .cell
  | armed => exact .armed
  | running => exact .running
  | closing => exact .closing
  | retiring => exact .retiring

theorem Frame.project_tail (source : Frame outward families outside entry)
    (same : SourceDependencyProjection.project outside = SourceDependencyProjection.project nextOutside) :
    Frame outward families nextOutside entry := by
  cases source with
  | plain => exact .plain
  | handler declarations => exact .handler (DeclarationsAt.project_tail declarations same)
  | cell => exact .cell
  | armed => exact .armed
  | running => exact .running
  | unwinding => exact .unwinding
  | closing => exact .closing
  | retiring => exact .retiring

/-- Equal projected outside scopes preserve every stored certificate,
including certificates in dormant branches. Stack and owner data are unchanged. -/
theorem Forest.project_outside (source : Forest outward tables families stack scope outside)
    (same : SourceDependencyProjection.project outside = SourceDependencyProjection.project nextOutside) :
    Forest outward tables families stack scope nextOutside := by
  induction source generalizing nextOutside with
  | nil => exact .nil
  | push realized frame tail ih =>
      exact .push realized (frame.project_tail (by simp only [SourceDependencyProjection.project_append, same])) (ih same)
  | live saved tail ihSaved ihTail =>
      exact .live (ihSaved (by simp only [SourceDependencyProjection.project_append, same])) (ihTail same)
  | spent tail ih => exact .spent (ih same)

/-- The old runtime certificates embed at every correctly realized scope.
No handler typing, usage or ownership proof needs to be duplicated. -/
theorem Forest.of_uniform (source : SourceDependencySchemes.Stored.Forest outward families stack)
    (realized : SourceDependencyCapture.Realizes tables families scope stack) :
    Forest outward tables families stack scope outside := by
  induction realized generalizing outside with
  | nil => exact .nil
  | push frame tail ih => cases source with
      | push stored rest => exact .push frame (.of_uniform stored) (ih rest)
  | live saved tail ihSaved ihTail => cases source with
      | live stored rest => exact .live (ihSaved stored) (ihTail rest)
  | spent tail ih => cases source with | spent rest => exact .spent (ih rest)

/-- Recomposition changes only where the same ordered suffix is grouped.
Certificates inside dormant branches see the same complete receiving scope. -/
theorem Forest.append
    (first : Forest outward tables families a firstScope (secondScope.append outside))
    (second : Forest outward tables families b secondScope outside) :
    Forest outward tables families (a.append b) (firstScope.append secondScope) outside := by
  induction a generalizing firstScope with
  | nil => cases first; exact second
  | push entry rest ih => cases first with
      | push realized frame tail =>
          rw [Stack.append, realized.append]
          exact .push realized
            (by simpa only [SourceDependencyChecks.scope_append_assoc] using frame)
            (ih tail)
  | live owner input answer captured caller rest ihCaptured ihRest => cases first with
      | live saved tail =>
          exact .live (by simpa only [SourceDependencyChecks.scope_append_assoc] using saved) (ihRest tail)
  | spent owner answer caller rest ih => cases first with | spent tail => exact .spent (ih tail)

/-- The exact actual handler cut supplies both contextual subforests and
the selected declaration certificate at the remaining receiving scope. -/
theorem Forest.cut
    (cut : HandlerCut requested whole captured tail handler)
    (source : Forest outward tables families whole scope outside) :
    ∃ capturedScope tailScope,
      Forest outward tables families captured capturedScope (tailScope.append outside) ∧
      Forest outward tables families tail tailScope outside ∧
      scope = capturedScope.append tailScope ∧
      DeclarationsAt outward (tailScope.append outside) handler.clauses (families handler) ∧
      ∀ operation, SourceDependencyCapture.select requested operation scope =
        SourceDependencyCapture.chosen operation (tables handler) (families handler) capturedScope tailScope := by
  induction cut generalizing scope with
  | hit handler tail same => cases source with
      | push realized frame rest => cases realized with
          | handler => cases frame with
              | handler declarations =>
                  refine ⟨_, _, .push .handler (.handler declarations) .nil, rest, rfl, declarations, ?_⟩
                  intro operation
                  simp only [SourceDependencyCapture.select, if_pos same.symm, SourceDependencyCapture.chosen]
                  rfl
  | push entry rest captured tail handler miss next ih => cases source with
      | push realized frame rest =>
          obtain ⟨capturedScope, tailScope, inside, remaining, recomposed, declarations, selected⟩ := ih rest
          refine ⟨_, _, .push realized ?_ inside, remaining, ?_, declarations, ?_⟩
          · simpa only [recomposed, SourceDependencyChecks.scope_append_assoc] using frame
          · rw [realized.append, ← recomposed]
          · intro operation
            rw [realized.select_miss miss, selected operation, SourceDependencyCapture.chosen_prepend]
  | live owner input answer saved caller rest captured tail handler next ih => cases source with
      | live inside rest =>
          rename_i savedScope restScope
          obtain ⟨capturedScope, tailScope, captured, remaining, recomposed, declarations, selected⟩ := ih rest
          refine ⟨.live owner savedScope capturedScope, tailScope, .live ?_ captured, remaining, ?_, declarations, ?_⟩
          · simpa only [recomposed, SourceDependencyChecks.scope_append_assoc] using inside
          · simp only [SourceDependencyCapture.Scope.append, ← recomposed]
          · intro operation
            rw [SourceDependencyCapture.select, selected operation, SourceDependencyCapture.chosen_prepend]
  | spent owner answer caller rest captured tail handler next ih => cases source with
      | spent rest =>
          obtain ⟨capturedScope, tailScope, captured, remaining, recomposed, declarations, selected⟩ := ih rest
          refine ⟨_, _, .spent captured, remaining, by simp only [SourceDependencyCapture.Scope.append, ← recomposed], declarations, ?_⟩
          intro operation
          rw [SourceDependencyCapture.select, selected operation, SourceDependencyCapture.chosen_prepend]

/-- Capture stores the contextual forests at exactly the same tail used by
the selected clause certificate. No certificate is moved to a new context. -/
theorem Forest.capture
    (cut : HandlerCut requested whole captured tail handler)
    (source : Forest outward tables families whole scope outside) :
    ∃ capturedScope tailScope,
      Forest outward tables families (.live owner input answer captured caller tail)
        (.live owner capturedScope tailScope) outside ∧
      scope = capturedScope.append tailScope ∧
      DeclarationsAt outward (tailScope.append outside) handler.clauses (families handler) := by
  obtain ⟨capturedScope, tailScope, saved, waiting, recomposed, declarations, selected⟩ := source.cut cut
  exact ⟨capturedScope, tailScope, .live saved waiting, recomposed, declarations⟩

/-- Align the stored split with another authenticated annotation of the same
cut. Successful exact selection identifies both scopes; no uniqueness of
arbitrary source annotations is assumed. -/
theorem Forest.cut_aligned
    (cut : HandlerCut requested whole captured tail handler)
    (source : Forest outward tables families whole wholeScope outside)
    (selection : SourceDependencyCapture.select requested operation wholeScope =
      SourceDependencyCapture.chosen operation (tables handler) (families handler) capturedScope tailScope)
    (known : ProtectionContracts.lookup operation (tables handler) = some offered)
    (checked : SourceDependencyCapture.checkCapture outward wholeScope requested operation = true) :
    Forest outward tables families captured capturedScope (tailScope.append outside) ∧
    Forest outward tables families tail tailScope outside ∧
    DeclarationsAt outward (tailScope.append outside) handler.clauses (families handler) := by
  obtain ⟨actualCapture, actualTail, saved, waiting, recomposed, declarations, actualSelection⟩ := source.cut cut
  cases located : SourceDependencyCapture.lookupDependencies operation (families handler) with
  | none =>
      have absent : SourceDependencyCapture.select requested operation wholeScope = none := by
        simpa only [SourceDependencyCapture.chosen, known, located] using selection
      simp only [SourceDependencyCapture.checkCapture, absent] at checked
      cases checked
  | some modes =>
      have identical := selection.symm.trans (actualSelection operation)
      simp only [SourceDependencyCapture.chosen, known, located] at identical
      cases Option.some.inj identical
      exact ⟨saved, waiting, declarations⟩

/-- Resumption at the captured owner's boundary uses only the proved spent
projection and ordered recomposition. A nonempty caller prefix needs its own
context-transport evidence and is not covered by this boundary case. -/
theorem Forest.resume_boundary
    (source : Forest outward tables families (.live owner input answer captured savedCaller tail)
      (.live owner capturedScope tailScope) outside) :
    Forest outward tables families (captured.append (.spent owner answer caller tail))
      (capturedScope.append (.spent owner tailScope)) outside := by
  cases source with
  | live saved waiting =>
      apply Forest.append (second := Forest.spent waiting)
      exact saved.project_outside (by
        simp only [SourceDependencyCapture.Scope.append, SourceDependencyProjection.project])

namespace Examples
open SourceDependencyHandlerGap (effect)

def inner : HandlerData := ⟨11, effect, SourceDependencyHandlerGap.clauses, .none, .unit, rfl⟩
def outer : HandlerData := ⟨12, effect, SourceDependencySchemes.Examples.resumeClauses, .none, .unit, rfl⟩
def tables : CallableProtectionFrames.Tables := fun handler =>
  if handler.activation = 11 then SourceDependencyHandlerGap.table else SourceDependencyCapture.Examples.resumeTable
def families : SourceDependencyCapture.Families := fun handler =>
  if handler.activation = 11 then SourceDependencyHandlerGap.dependencies else SourceDependencyCapture.Examples.resumeDependencies
def stack : Stack := .push (.handler inner) (.push (.handler outer) .nil)
def scope : Receiving := .handler effect SourceDependencyHandlerGap.table SourceDependencyHandlerGap.dependencies
  SourceDependencyHandlerGap.outside

/-- The formerly excluded declaration now resides in an actual handler
frame with its required outer interpretation. This checks the stored component,
not a reachable full runtime state. -/
theorem stored_composition : Forest outward tables families stack scope .nil :=
  .push (@SourceDependencyCapture.Frame.handler tables families inner)
    (.handler SourceContextualClauses.Examples.contextual_declarations)
    (.push (@SourceDependencyCapture.Frame.handler tables families outer)
      (.handler (.of_uniform SourceDependencySchemes.Examples.resume_declarations)) .nil)

theorem old_stored_rejected : ¬ SourceDependencySchemes.Stored.Forest outward families stack := by
  intro source
  cases source with
  | push frame rest => cases frame with
      | handler declarations => exact SourceDependencyHandlerGap.no_uniform_declarations outward declarations

end Examples

end Ash.OneShot.SourceContextualForest

#print axioms Ash.OneShot.SourceContextualForest.ModeAt.project_tail
#print axioms Ash.OneShot.SourceContextualForest.DeclarationsAt.project_tail
#print axioms Ash.OneShot.SourceContextualForest.Forest.realizes
#print axioms Ash.OneShot.SourceContextualForest.Frame.of_uniform
#print axioms Ash.OneShot.SourceContextualForest.Frame.project_tail
#print axioms Ash.OneShot.SourceContextualForest.Forest.project_outside
#print axioms Ash.OneShot.SourceContextualForest.Forest.of_uniform
#print axioms Ash.OneShot.SourceContextualForest.Forest.append
#print axioms Ash.OneShot.SourceContextualForest.Forest.cut
#print axioms Ash.OneShot.SourceContextualForest.Forest.capture
#print axioms Ash.OneShot.SourceContextualForest.Forest.cut_aligned
#print axioms Ash.OneShot.SourceContextualForest.Forest.resume_boundary
#print axioms Ash.OneShot.SourceContextualForest.Examples.stored_composition
#print axioms Ash.OneShot.SourceContextualForest.Examples.old_stored_rejected


namespace Ash.OneShot.SourceContextualForest
open ScopedExpressions ScopedExecution

/-- Cleanup changes only its return marker. The suffix's handler declarations
    retain exactly the enclosing scopes at which they were checked. Callback
    expression typing is supplied separately by the lexical source segment. -/
theorem Forest.start_cleanup
    (source : Forest outward tables families (.push (.armed action) rest)
      (.cleanup action.requests dependencies restScope) outside) :
    Forest outward tables families (.push (.unwinding action) rest) (.running restScope) outside := by
  generalize same : SourceDependencyCapture.Scope.cleanup action.requests dependencies restScope = checkedScope at source
  cases source with
  | push realized frame tail => cases realized with
      | cleanup => cases same; exact .push .unwinding .unwinding tail

theorem Forest.finish_cleanup
    (source : Forest outward tables families (.push (.unwinding action) rest) (.running restScope) outside) :
    Forest outward tables families rest restScope outside := by
  generalize same : SourceDependencyCapture.Scope.running restScope = checkedScope at source
  cases source with
  | push realized frame tail => cases realized with
      | unwinding => cases same; exact tail

#print axioms Ash.OneShot.SourceContextualForest.Forest.start_cleanup
#print axioms Ash.OneShot.SourceContextualForest.Forest.finish_cleanup
end Ash.OneShot.SourceContextualForest


namespace Ash.OneShot.SourceContextualForest.Lexical
open ScopedExpressions ScopedExecution
open SourceContextualClauses.Lexical (DeclarationsAt)
abbrev Receiving := SourceDependencyCapture.Scope
inductive Frame (outward : List Instance) (families : SourceDependencyCapture.Families)
    (outside : Receiving) : ExecFrame → Prop where
  | plain : Frame outward families outside (.plain data)
  | handler (declarations : DeclarationsAt outward outside data.clauses (families data)) :
      Frame outward families outside (.handler data)
  | cell : Frame outward families outside (.cell identity payload scope answer)
  | armed : Frame outward families outside (.armed data)
  | running : Frame outward families outside (.running data saved closed)
  | unwinding : Frame outward families outside (.unwinding data)
  | closing : Frame outward families outside (.closing identity scope)
  | retiring : Frame outward families outside (.retiring owner)

inductive Forest (outward : List Instance) (tables : CallableProtectionFrames.Tables)
    (families : SourceDependencyCapture.Families) : Stack → Receiving → Receiving → Prop where
  | nil : Forest outward tables families .nil .nil outside
  | push (realized : SourceDependencyCapture.Frame tables families layer entry)
      (frame : Frame outward families (restScope.append outside) entry)
      (tail : Forest outward tables families rest restScope outside) :
      Forest outward tables families (.push entry rest) (layer restScope) outside
  | live (saved : Forest outward tables families captured capturedScope (restScope.append outside))
      (tail : Forest outward tables families rest restScope outside) :
      Forest outward tables families (.live owner input answer captured caller rest) (.live owner capturedScope restScope) outside
  | spent (tail : Forest outward tables families rest restScope outside) :
      Forest outward tables families (.spent owner answer caller rest) (.spent owner restScope) outside

theorem Forest.realizes (source : Forest outward tables families stack scope outside) :
    SourceDependencyCapture.Realizes tables families scope stack := by
  induction source with
  | nil => exact .nil
  | push realized frame tail ih => exact .push realized ih
  | live saved tail ihSaved ihTail => exact .live ihSaved ihTail
  | spent tail ih => exact .spent ih

/-- The exact actual handler cut supplies both contextual subforests and
the selected declaration certificate at the remaining receiving scope. -/
theorem Forest.cut
    (cut : HandlerCut requested whole captured tail handler)
    (source : Forest outward tables families whole scope outside) :
    ∃ capturedScope tailScope,
      Forest outward tables families captured capturedScope (tailScope.append outside) ∧
      Forest outward tables families tail tailScope outside ∧
      scope = capturedScope.append tailScope ∧
      DeclarationsAt outward (tailScope.append outside) handler.clauses (families handler) ∧
      ∀ operation, SourceDependencyCapture.select requested operation scope =
        SourceDependencyCapture.chosen operation (tables handler) (families handler) capturedScope tailScope := by
  induction cut generalizing scope with
  | hit handler tail same => cases source with
      | push realized frame rest => cases realized with
          | handler => cases frame with
              | handler declarations =>
                  refine ⟨_, _, .push .handler (.handler declarations) .nil, rest, rfl, declarations, ?_⟩
                  intro operation
                  simp only [SourceDependencyCapture.select, if_pos same.symm, SourceDependencyCapture.chosen]
                  rfl
  | push entry rest captured tail handler miss next ih => cases source with
      | push realized frame rest =>
          obtain ⟨capturedScope, tailScope, inside, remaining, recomposed, declarations, selected⟩ := ih rest
          refine ⟨_, _, .push realized ?_ inside, remaining, ?_, declarations, ?_⟩
          · simpa only [recomposed, SourceDependencyChecks.scope_append_assoc] using frame
          · rw [realized.append, ← recomposed]
          · intro operation
            rw [realized.select_miss miss, selected operation, SourceDependencyCapture.chosen_prepend]
  | live owner input answer saved caller rest captured tail handler next ih => cases source with
      | live inside rest =>
          rename_i savedScope restScope
          obtain ⟨capturedScope, tailScope, captured, remaining, recomposed, declarations, selected⟩ := ih rest
          refine ⟨.live owner savedScope capturedScope, tailScope, .live ?_ captured, remaining, ?_, declarations, ?_⟩
          · simpa only [recomposed, SourceDependencyChecks.scope_append_assoc] using inside
          · simp only [SourceDependencyCapture.Scope.append, ← recomposed]
          · intro operation
            rw [SourceDependencyCapture.select, selected operation, SourceDependencyCapture.chosen_prepend]
  | spent owner answer caller rest captured tail handler next ih => cases source with
      | spent rest =>
          obtain ⟨capturedScope, tailScope, captured, remaining, recomposed, declarations, selected⟩ := ih rest
          refine ⟨_, _, .spent captured, remaining, by simp only [SourceDependencyCapture.Scope.append, ← recomposed], declarations, ?_⟩
          intro operation
          rw [SourceDependencyCapture.select, selected operation, SourceDependencyCapture.chosen_prepend]

/-- Capture stores the contextual forests at exactly the same tail used by
the selected clause certificate. No certificate is moved to a new context. -/
theorem Forest.capture
    (cut : HandlerCut requested whole captured tail handler)
    (source : Forest outward tables families whole scope outside) :
    ∃ capturedScope tailScope,
      Forest outward tables families (.live owner input answer captured caller tail)
        (.live owner capturedScope tailScope) outside ∧
      scope = capturedScope.append tailScope ∧
      DeclarationsAt outward (tailScope.append outside) handler.clauses (families handler) := by
  obtain ⟨capturedScope, tailScope, saved, waiting, recomposed, declarations, selected⟩ := source.cut cut
  exact ⟨capturedScope, tailScope, .live saved waiting, recomposed, declarations⟩

/-- Align the stored split with another authenticated annotation of the same
cut. Successful exact selection identifies both scopes; no uniqueness of
arbitrary source annotations is assumed. -/
theorem Forest.cut_aligned
    (cut : HandlerCut requested whole captured tail handler)
    (source : Forest outward tables families whole wholeScope outside)
    (selection : SourceDependencyCapture.select requested operation wholeScope =
      SourceDependencyCapture.chosen operation (tables handler) (families handler) capturedScope tailScope)
    (known : ProtectionContracts.lookup operation (tables handler) = some offered)
    (checked : SourceDependencyChecks.Lexical.Capture wholeScope requested operation) :
    Forest outward tables families captured capturedScope (tailScope.append outside) ∧
    Forest outward tables families tail tailScope outside ∧
    DeclarationsAt outward (tailScope.append outside) handler.clauses (families handler) := by
  obtain ⟨actualCapture, actualTail, saved, waiting, recomposed, declarations, actualSelection⟩ := source.cut cut
  cases located : SourceDependencyCapture.lookupDependencies operation (families handler) with
  | none =>
      have absent : SourceDependencyCapture.select requested operation wholeScope = none := by
        simpa only [SourceDependencyCapture.chosen, known, located] using selection
      cases checked with
      | builtin found | handler found => rw [absent] at found; cases found
  | some modes =>
      have identical := selection.symm.trans (actualSelection operation)
      simp only [SourceDependencyCapture.chosen, known, located] at identical
      cases Option.some.inj identical
      exact ⟨saved, waiting, declarations⟩


end Ash.OneShot.SourceContextualForest.Lexical

#print axioms Ash.OneShot.SourceContextualForest.Lexical.Forest.realizes
#print axioms Ash.OneShot.SourceContextualForest.Lexical.Forest.cut
#print axioms Ash.OneShot.SourceContextualForest.Lexical.Forest.capture
#print axioms Ash.OneShot.SourceContextualForest.Lexical.Forest.cut_aligned

namespace Ash.OneShot.SourceContextualForest.Lexical
open ScopedExpressions ScopedExecution
/-- Recomposition changes only where the same ordered suffix is grouped.
Certificates inside dormant branches see the same complete receiving scope. -/
theorem Forest.append
    (first : Forest outward tables families a firstScope (secondScope.append outside))
    (second : Forest outward tables families b secondScope outside) :
    Forest outward tables families (a.append b) (firstScope.append secondScope) outside := by
  induction a generalizing firstScope with
  | nil => cases first; exact second
  | push entry rest ih => cases first with
      | push realized frame tail =>
          rw [Stack.append, realized.append]
          exact .push realized
            (by simpa only [SourceDependencyChecks.scope_append_assoc] using frame)
            (ih tail)
  | live owner input answer captured caller rest ihCaptured ihRest => cases first with
      | live saved tail =>
          exact .live (by simpa only [SourceDependencyChecks.scope_append_assoc] using saved) (ihRest tail)
  | spent owner answer caller rest ih => cases first with | spent tail => exact .spent (ih tail)

/-- Cleanup changes only its return marker. The suffix's handler declarations
    retain exactly the enclosing scopes at which they were checked. Callback
    expression typing is supplied separately by the lexical source segment. -/
theorem Forest.start_cleanup
    (source : Forest outward tables families (.push (.armed action) rest)
      (.cleanup action.requests dependencies restScope) outside) :
    Forest outward tables families (.push (.unwinding action) rest) (.running restScope) outside := by
  generalize same : SourceDependencyCapture.Scope.cleanup action.requests dependencies restScope = checkedScope at source
  cases source with
  | push realized frame tail => cases realized with
      | cleanup => cases same; exact .push .unwinding .unwinding tail

theorem Forest.finish_cleanup
    (source : Forest outward tables families (.push (.unwinding action) rest) (.running restScope) outside) :
    Forest outward tables families rest restScope outside := by
  generalize same : SourceDependencyCapture.Scope.running restScope = checkedScope at source
  cases source with
  | push realized frame tail => cases realized with
      | unwinding => cases same; exact tail


end Ash.OneShot.SourceContextualForest.Lexical

#print axioms Ash.OneShot.SourceContextualForest.Lexical.Forest.append
#print axioms Ash.OneShot.SourceContextualForest.Lexical.Forest.start_cleanup
#print axioms Ash.OneShot.SourceContextualForest.Lexical.Forest.finish_cleanup
