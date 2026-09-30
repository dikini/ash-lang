import SourceDependencyFrames

/-! Structural continuation lookup, resumption and disposal for dependency scopes.
Only active live boundaries supply invocation access. The checker uses the
existing independent permission and owner-phase checks; it does not yet check
all requests made by the restored source under its receiving caller. -/
namespace Ash.OneShot.SourceDependencyCapture
open ScopedExpressions ScopedExecution ProtectionContracts
open OwnerPhaseTransitions (Phases spend)

structure OwnerSelection where
  front : Scope
  captured : Scope
  tail : Scope

def OwnerSelection.prepend (layer : Scope → Scope) (selected : OwnerSelection) : OwnerSelection :=
  { selected with front := layer selected.front }

def findOwner (owner : Nat) : Scope → Option OwnerSelection
  | .nil => none
  | .plain dependencies rest => (findOwner owner rest).map (OwnerSelection.prepend (.plain dependencies))
  | .handler effect table families rest => (findOwner owner rest).map (OwnerSelection.prepend (.handler effect table families))
  | .cell identity rest => (findOwner owner rest).map (OwnerSelection.prepend (.cell identity))
  | .cleanup needs body rest => (findOwner owner rest).map (OwnerSelection.prepend (.cleanup needs body))
  | .running rest => (findOwner owner rest).map (OwnerSelection.prepend .running)
  | .live other captured rest =>
      if owner = other then some ⟨.nil, captured, rest⟩
      else (findOwner owner rest).map (OwnerSelection.prepend (.live other captured))
  | .spent other rest => (findOwner owner rest).map (OwnerSelection.prepend (.spent other))

/-- Lookup walks only the active spine. In particular, the live-miss rule
retains the dormant branch and does not search it. -/
inductive OwnerCut (owner : Nat) : Scope → OwnerSelection → Prop where
  | hit : OwnerCut owner (.live owner captured rest) ⟨.nil, captured, rest⟩
  | plain (next : OwnerCut owner rest selected) :
      OwnerCut owner (.plain dependencies rest) (selected.prepend (.plain dependencies))
  | handler (next : OwnerCut owner rest selected) :
      OwnerCut owner (.handler effect table families rest) (selected.prepend (.handler effect table families))
  | cell (next : OwnerCut owner rest selected) :
      OwnerCut owner (.cell identity rest) (selected.prepend (.cell identity))
  | cleanup (next : OwnerCut owner rest selected) :
      OwnerCut owner (.cleanup needs body rest) (selected.prepend (.cleanup needs body))
  | running (next : OwnerCut owner rest selected) :
      OwnerCut owner (.running rest) (selected.prepend .running)
  | live (different : owner ≠ other) (next : OwnerCut owner rest selected) :
      OwnerCut owner (.live other captured rest) (selected.prepend (.live other captured))
  | spent (next : OwnerCut owner rest selected) :
      OwnerCut owner (.spent other rest) (selected.prepend (.spent other))

theorem OwnerCut.lookup (cut : OwnerCut owner scope selected) : findOwner owner scope = some selected := by
  induction cut with
  | hit => simp [findOwner]
  | live different next ih => simp only [findOwner, if_neg different, ih, Option.map_some]
  | plain next ih | handler next ih | cell next ih | cleanup next ih | running next ih | spent next ih =>
      simp only [findOwner, ih, Option.map_some]

theorem find_owner_sound (found : findOwner owner scope = some selected) : OwnerCut owner scope selected := by
  induction scope generalizing selected with
  | nil => cases found
  | live other captured rest ihCaptured ihRest =>
      by_cases same : owner = other
      · subst other
        simp only [findOwner, ↓reduceIte, Option.some.injEq] at found
        exact found ▸ .hit
      · simp only [findOwner, if_neg same, Option.map_eq_some_iff] at found
        obtain ⟨inside, looked, sameSelection⟩ := found
        exact sameSelection ▸ .live same (ihRest looked)
  | plain dependencies rest ih =>
      simp only [findOwner, Option.map_eq_some_iff] at found
      obtain ⟨inside, looked, sameSelection⟩ := found
      exact sameSelection ▸ .plain (ih looked)
  | handler effect table families rest ih =>
      simp only [findOwner, Option.map_eq_some_iff] at found
      obtain ⟨inside, looked, sameSelection⟩ := found
      exact sameSelection ▸ .handler (ih looked)
  | cell identity rest ih =>
      simp only [findOwner, Option.map_eq_some_iff] at found
      obtain ⟨inside, looked, sameSelection⟩ := found
      exact sameSelection ▸ .cell (ih looked)
  | cleanup needs body rest ih =>
      simp only [findOwner, Option.map_eq_some_iff] at found
      obtain ⟨inside, looked, sameSelection⟩ := found
      exact sameSelection ▸ .cleanup (ih looked)
  | running rest ih =>
      simp only [findOwner, Option.map_eq_some_iff] at found
      obtain ⟨inside, looked, sameSelection⟩ := found
      exact sameSelection ▸ .running (ih looked)
  | spent other rest ih =>
      simp only [findOwner, Option.map_eq_some_iff] at found
      obtain ⟨inside, looked, sameSelection⟩ := found
      exact sameSelection ▸ .spent (ih looked)

theorem find_owner_iff : findOwner owner scope = some selected ↔ OwnerCut owner scope selected :=
  ⟨find_owner_sound, OwnerCut.lookup⟩

theorem OwnerCut.reconstruct (cut : OwnerCut owner scope selected) :
    scope = selected.front.append (.live owner selected.captured selected.tail) := by
  induction cut with
  | hit => rfl
  | plain next ih => simp only [OwnerSelection.prepend, Scope.append, ← ih]
  | handler next ih => simp only [OwnerSelection.prepend, Scope.append, ← ih]
  | cell next ih => simp only [OwnerSelection.prepend, Scope.append, ← ih]
  | cleanup next ih => simp only [OwnerSelection.prepend, Scope.append, ← ih]
  | running next ih => simp only [OwnerSelection.prepend, Scope.append, ← ih]
  | live different next ih => simp only [OwnerSelection.prepend, Scope.append, ← ih]
  | spent next ih => simp only [OwnerSelection.prepend, Scope.append, ← ih]

def OwnerSelection.resumed (owner : Nat) (selected : OwnerSelection) : Scope :=
  selected.captured.append (selected.front.append (.spent owner selected.tail))

/-- Capability permission, available ownership and structural access are
independent premises. No effect invocation counter occurs here. -/
inductive ResumeChecked (actions : Syntax.UsageTickets) (phases : Phases) (owner : Nat) (scope : Scope) : Scope → Prop where
  | checked (located : OwnerCut owner scope selected) (known : actions owner = some rights)
      (permission : rights.resume = true) (available : phases owner = .available) :
      ResumeChecked actions phases owner scope (selected.resumed owner)

def checkResume (actions : Syntax.UsageTickets) (phases : Phases) (owner : Nat) (scope : Scope) : Option Scope :=
  match actions owner, findOwner owner scope with
  | some rights, some selected =>
      if rights.resume && decide (phases owner = .available) then some (selected.resumed owner) else none
  | _, _ => none

theorem check_resume_iff : checkResume actions phases owner scope = some after ↔ ResumeChecked actions phases owner scope after := by
  constructor
  · intro checked
    unfold checkResume at checked
    cases known : actions owner with
    | none => simp [known] at checked
    | some rights => cases located : findOwner owner scope with
      | none => simp [located] at checked
      | some selected =>
          simp only [known, located] at checked
          split at checked
          next permitted =>
            have facts : rights.resume = true ∧ decide (phases owner = .available) = true := by
              simpa only [Bool.and_eq_true] using permitted
            cases Option.some.inj checked
            exact .checked (find_owner_sound located) known facts.1 (of_decide_eq_true facts.2)
          next => cases checked
  · intro checked
    cases checked with
    | checked located known permission available =>
        simp only [checkResume, known, located.lookup, permission, available, decide_true, Bool.true_and, if_true]

theorem consumed_resume_rejected : checkResume actions (spend phases owner) owner scope = none := by
  unfold checkResume
  cases known : actions owner <;> cases located : findOwner owner scope <;>
    simp [OwnerPhaseTransitions.spend_self]

/-- Actual frames add exactly one pending layer; none supply a continuation. -/
theorem Frame.find_owner (frame : Frame tables families layer entry) :
    findOwner owner (layer rest) = (findOwner owner rest).map (OwnerSelection.prepend layer) := by
  cases frame <;> rfl

/-- Source lookup identifies the same actual live boundary and saved stack.
No independently chosen runtime continuation is supplied. -/
theorem Realizes.find_owner (realized : Realizes tables families scope stack)
    (found : findOwner owner scope = some selected) :
    ∃ front captured tail input answer caller,
      stack = front.append (.live owner input answer captured caller tail) ∧
      Realizes tables families selected.front front ∧
      Realizes tables families selected.captured captured ∧
      Realizes tables families selected.tail tail := by
  induction realized generalizing selected with
  | nil => cases found
  | push frame rest ih =>
      rw [frame.find_owner, Option.map_eq_some_iff] at found
      obtain ⟨inside, located, same⟩ := found
      subst selected
      obtain ⟨front, captured, tail, input, answer, caller, shape, frontSource, saved, outside⟩ := ih located
      exact ⟨.push _ front, captured, tail, input, answer, caller, by rw [shape]; rfl, .push frame frontSource, saved, outside⟩
  | @live captured savedScope rest stack other input answer caller inside outside ihInside ihOutside =>
      by_cases same : owner = other
      · subst other
        simp only [findOwner, ↓reduceIte, Option.some.injEq] at found
        subst selected
        exact ⟨.nil, savedScope, stack, input, answer, caller, rfl, .nil, inside, outside⟩
      · simp only [findOwner, if_neg same, Option.map_eq_some_iff] at found
        obtain ⟨selectedTail, located, selectionSame⟩ := found
        subst selected
        obtain ⟨front, capturedStack, tail, inputType, answerType, callerScope, shape, frontSource, saved, remaining⟩ := ihOutside located
        exact ⟨.live other input answer savedScope caller front, capturedStack, tail, inputType, answerType, callerScope,
          by rw [shape]; rfl, .live inside frontSource, saved, remaining⟩
  | spent rest ih =>
      simp only [findOwner, Option.map_eq_some_iff] at found
      obtain ⟨inside, located, same⟩ := found
      subst selected
      obtain ⟨front, captured, tail, input, answer, caller, shape, frontSource, saved, outside⟩ := ih located
      exact ⟨.spent _ _ _ front, captured, tail, input, answer, caller, by rw [shape]; rfl, .spent frontSource, saved, outside⟩

/-- The structural check produces the existing resume transition and the
annotation of its actual target stack. Lexical resolution and the value premise
are reused from that transition. This is not guard preservation for later code. -/
theorem checked_resume_step
    (realized : Realizes tables families dependencyScope stack)
    (checked : checkResume actions phases owner dependencyScope = some afterScope)
    (resolved : caller.resolve binder = some owner) (closed : ClosedValue value) :
    ∃ afterStack,
      RawStep ⟨.resume binder value, caller, stack⟩ ⟨value, caller, afterStack⟩ [] [.ticket owner] ∧
      Realizes tables families afterScope afterStack := by
  cases check_resume_iff.mp checked with
  | checked located known permission available =>
      obtain ⟨front, captured, tail, input, answer, scope, shape, frontSource, saved, outside⟩ := realized.find_owner located.lookup
      subst stack
      exact ⟨_, RawStep.resume binder owner caller scope input answer front captured tail value closed resolved,
        saved.append (frontSource.append (.spent outside))⟩


/-- Dependency annotations on the scheduled closing work. Dropped source
handlers and pending expressions do not execute. A scheduled retirement is a
protected frame. Use of this transformation requires an unprotected input. -/
def Scope.forClosing : Scope → Scope
  | .nil => .nil
  | .plain _ rest | .handler _ _ _ rest | .spent _ rest => rest.forClosing
  | .cell identity rest => .cell identity rest.forClosing
  | .cleanup needs body rest => .cleanup needs body rest.forClosing
  | .running rest => .running rest.forClosing
  | .live _ captured rest => captured.forClosing.append (.running rest.forClosing)

private theorem close_control_append (caller : Execution.Scope) (first second : List CloseEntry) :
    closeControl caller (first ++ second) = (closeControl caller first).append (closeControl caller second) := by
  induction first with
  | nil => rfl
  | cons entry rest ih => simp only [List.cons_append, closeControl, ih, Stack.append]

/-- Derive both the existing closing plan and the dependencies of its actual
scheduled callbacks. Owner accounting remains the old plan theorem. -/
theorem Realizes.forClosing (realized : Realizes tables families scope stack)
    (unprotected : scope.held = false) :
    ∃ plan, SourceRecursiveRoutes.Realizes scope.shape stack plan ∧
      Realizes tables families scope.forClosing (closeControl caller plan) := by
  induction realized with
  | nil => exact ⟨[], .nil, .nil⟩
  | push frame rest ih =>
      rw [frame.held, Bool.or_eq_false_iff] at unprotected
      obtain ⟨plan, shape, next⟩ := ih unprotected.2
      cases frame with
      | plain => exact ⟨plan, .plain shape, next⟩
      | handler => exact ⟨plan, .handler shape, next⟩
      | cell =>
          refine ⟨_, .cell shape, ?_⟩
          simp only [Scope.forClosing, closeControl, CloseEntry.frame]
          exact .push .cell next
      | @cleanup dependencies action =>
          refine ⟨_, .cleanup shape, ?_⟩
          simp only [Scope.forClosing, closeControl, CloseEntry.frame]
          exact .push (Frame.cleanup (action := { action with scope := caller, answer := .unit }) (dependencies := dependencies)) next
      | running | unwinding | closing | retiring => cases unprotected.1
  | live inside outside ihInside ihOutside =>
      simp only [Scope.held, Bool.or_eq_false_iff] at unprotected
      obtain ⟨first, firstShape, firstSource⟩ := ihInside unprotected.1
      obtain ⟨second, secondShape, secondSource⟩ := ihOutside unprotected.2
      refine ⟨_, .live firstShape secondShape, ?_⟩
      simpa only [Scope.forClosing, close_control_append, closeControl, CloseEntry.frame] using
        firstSource.append (.push .retiring secondSource)
  | spent rest ih =>
      obtain ⟨plan, shape, next⟩ := ih unprotected
      exact ⟨plan, .spent shape, next⟩

def OwnerSelection.disposed (owner : Nat) (selected : OwnerSelection) : Scope :=
  selected.captured.forClosing.append (.running (selected.front.append (.spent owner selected.tail)))

inductive DisposeChecked (outward : List Instance) (actions : Syntax.UsageTickets) (phases : Phases)
    (owner : Nat) (scope : Scope) : Scope → Prop where
  | checked (located : OwnerCut owner scope selected) (known : actions owner = some rights)
      (permission : rights.dispose = true) (available : phases owner = .available)
      (unprotected : selected.captured.held = false)
      (closing : SourceRecursiveRoutes.Closing outward selected.captured.shape [] []) :
      DisposeChecked outward actions phases owner scope (selected.disposed owner)

def checkDispose (outward : List Instance) (actions : Syntax.UsageTickets) (phases : Phases)
    (owner : Nat) (scope : Scope) : Option Scope :=
  match actions owner, findOwner owner scope with
  | some rights, some selected =>
      if rights.dispose && decide (phases owner = .available) && !selected.captured.held &&
          checkClosing outward selected.captured.shape [] [] then some (selected.disposed owner) else none
  | _, _ => none

theorem check_dispose_iff : checkDispose outward actions phases owner scope = some after ↔
    DisposeChecked outward actions phases owner scope after := by
  constructor
  · intro checked
    unfold checkDispose at checked
    cases known : actions owner with
    | none => simp [known] at checked
    | some rights => cases located : findOwner owner scope with
      | none => simp [located] at checked
      | some selected =>
          simp only [known, located] at checked
          split at checked
          next permitted =>
            have facts : ((rights.dispose = true ∧ phases owner = .available) ∧ selected.captured.held = false) ∧
                checkClosing outward selected.captured.shape [] [] = true := by simpa using permitted
            cases Option.some.inj checked
            exact .checked (find_owner_sound located) known facts.1.1.1 facts.1.1.2 facts.1.2 (check_closing_iff.mp facts.2)
          next => cases checked
  · intro checked
    cases checked with
    | checked located known permission available unprotected closing =>
        simp only [checkDispose, known, located.lookup, permission, available, unprotected,
          check_closing_iff.mpr closing, decide_true, Bool.not_false, Bool.true_and, if_true]

theorem consumed_dispose_rejected : checkDispose outward actions (spend phases owner) owner scope = none := by
  unfold checkDispose
  cases known : actions owner <;> cases located : findOwner owner scope <;>
    simp [OwnerPhaseTransitions.spend_self]

/-- Checked disposal produces the actual existing transition, preserves the
scheduled callback dependencies, and accounts for every captured owner. The
complete access/source invariant is a separate integration obligation. -/
theorem checked_dispose_step
    (realized : Realizes tables families dependencyScope stack)
    (checked : checkDispose outward actions phases owner dependencyScope = some afterScope)
    (resolved : caller.resolve binder = some owner) :
    ∃ afterStack captured plan,
      RawStep ⟨.discard binder, caller, stack⟩ ⟨.unit, caller, afterStack⟩ [.close closeId] [.ticket owner] ∧
      Realizes tables families afterScope afterStack ∧
      makePlan captured = some plan ∧ (planOwners (plan.map CloseEntry.erase)).Perm captured.erase.owners := by
  cases check_dispose_iff.mp checked with
  | checked located known permission available unprotected closing =>
      obtain ⟨front, captured, tail, input, answer, scope, shape, frontSource, saved, outside⟩ := realized.find_owner located.lookup
      obtain ⟨plan, realizedPlan, scheduled⟩ := saved.forClosing (caller := caller) unprotected
      subst stack
      exact ⟨_, captured, plan,
        RawStep.discard binder owner closeId caller scope input answer front captured tail plan resolved realizedPlan.built,
        scheduled.append (.push .closing (frontSource.append (.spent outside))), realizedPlan.built, realizedPlan.owner_accounting⟩

namespace InvocationExamples
open SourceDependencyAnnotations (Dependencies)

def nested : Scope := .live 8 (.live 6 .nil .nil) .nil

theorem dormant_owner_inaccessible : findOwner 6 nested = none := by decide

theorem enclosing_owner_accessible : findOwner 8 nested = some ⟨.nil, .live 6 .nil .nil, .nil⟩ := rfl

def actions : Syntax.UsageTickets := fun owner => if owner = 8 then some ⟨true, false⟩ else none

theorem resume_exposes_saved_owner :
    checkResume actions (OwnerPhaseTransitions.available [8, 6]) 8 nested = some (.live 6 .nil (.spent 8 .nil)) := rfl

theorem spent_owner_inaccessible : findOwner 8 (.live 6 .nil (.spent 8 .nil)) = none := by decide

theorem permission_is_independent : checkResume (fun _ => some ⟨false, true⟩)
    (OwnerPhaseTransitions.available [8, 6]) 8 nested = none := by decide


/-- Closing retains the callback dependency tree even inside a dormant
capture, and schedules its owner's retirement before the remaining cell. -/
theorem closing_retains_nested_callback :
    Examples.nested.forClosing = .cleanup [.cell 4] (.request (.cell 4) 0) (.running (.cell 4 .nil)) := rfl

theorem protected_disposal_rejected : checkDispose [] (fun _ => some ⟨true, true⟩)
    (OwnerPhaseTransitions.available [8]) 8 (.live 8 (.running .nil) .nil) = none := by decide

theorem removed_callback_handler_disposal_rejected : checkDispose [Examples.effectF]
    (fun _ => some ⟨true, true⟩) (OwnerPhaseTransitions.available [8]) 8 (.live 8 Examples.bad .nil) = none := by decide

def effectG : Instance := .user 93 []
def handlerG : Scope → Scope := .handler effectG Examples.disposeTable Examples.disposeDependencies
def savedCallback : Scope := .cleanup [Examples.effectF] Examples.callback (Examples.handlerE .nil)
def originalCaller : Scope := handlerG (Examples.handlerF .nil)
def interleavedCaller : Scope := Examples.handlerF (.live 8 savedCallback originalCaller)

theorem original_callback_route_accepted :
    checkCapture [Examples.effectF] (savedCallback.append originalCaller) effectG 0 = true := by decide

/-- Resumption itself is permitted, but its caller changes a later capture's
closing route. A complete source check must recheck exported requests at the
receiving caller; successful invocation access alone is insufficient. -/
theorem interleaved_resume_requires_rechecking :
    checkResume actions (OwnerPhaseTransitions.available [8]) 8 interleavedCaller =
      some (savedCallback.append (Examples.handlerF (.spent 8 originalCaller))) ∧
    checkCapture [Examples.effectF] (savedCallback.append (Examples.handlerF (.spent 8 originalCaller))) effectG 0 = false :=
  ⟨rfl, by decide⟩

end InvocationExamples
end Ash.OneShot.SourceDependencyCapture

#print axioms Ash.OneShot.SourceDependencyCapture.OwnerCut.lookup
#print axioms Ash.OneShot.SourceDependencyCapture.find_owner_sound
#print axioms Ash.OneShot.SourceDependencyCapture.find_owner_iff
#print axioms Ash.OneShot.SourceDependencyCapture.OwnerCut.reconstruct
#print axioms Ash.OneShot.SourceDependencyCapture.check_resume_iff
#print axioms Ash.OneShot.SourceDependencyCapture.consumed_resume_rejected
#print axioms Ash.OneShot.SourceDependencyCapture.Frame.find_owner
#print axioms Ash.OneShot.SourceDependencyCapture.Realizes.find_owner
#print axioms Ash.OneShot.SourceDependencyCapture.checked_resume_step
#print axioms Ash.OneShot.SourceDependencyCapture.InvocationExamples.dormant_owner_inaccessible
#print axioms Ash.OneShot.SourceDependencyCapture.InvocationExamples.enclosing_owner_accessible
#print axioms Ash.OneShot.SourceDependencyCapture.InvocationExamples.resume_exposes_saved_owner
#print axioms Ash.OneShot.SourceDependencyCapture.InvocationExamples.spent_owner_inaccessible
#print axioms Ash.OneShot.SourceDependencyCapture.InvocationExamples.permission_is_independent

#print axioms Ash.OneShot.SourceDependencyCapture.Realizes.forClosing

#print axioms Ash.OneShot.SourceDependencyCapture.check_dispose_iff

#print axioms Ash.OneShot.SourceDependencyCapture.consumed_dispose_rejected

#print axioms Ash.OneShot.SourceDependencyCapture.checked_dispose_step

#print axioms Ash.OneShot.SourceDependencyCapture.InvocationExamples.closing_retains_nested_callback

#print axioms Ash.OneShot.SourceDependencyCapture.InvocationExamples.protected_disposal_rejected

#print axioms Ash.OneShot.SourceDependencyCapture.InvocationExamples.removed_callback_handler_disposal_rejected

#print axioms Ash.OneShot.SourceDependencyCapture.InvocationExamples.original_callback_route_accepted

#print axioms Ash.OneShot.SourceDependencyCapture.InvocationExamples.interleaved_resume_requires_rechecking
