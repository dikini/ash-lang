import CoreValueRelation
import SourceResourceRoutes

/-! Appending an unchanged suffix preserves successful source transitions and
existing target transitions. Success already witnesses selection in the original
prefix; this does not prove dispatch into an appended cleanup tail. -/
set_option linter.unusedSimpArgs false

namespace Ash.OneShot.CoreSuffixSplice
open ScopedExpressions ScopedExecution CoreValueRelation
open CoreMachine

def appendFrames (state : CoreMachine.State) (suffix : List CoreMachine.Frame) : CoreMachine.State :=
  {state with frames := state.frames ++ suffix}

def appendInterpreter (cut : InterpreterCut) (suffix : List CoreMachine.Frame) : InterpreterCut :=
  match cut with
  | .cell cut => .cell {cut with outside := cut.outside ++ suffix}
  | .handler inside node environment occurrence outside => .handler inside node environment occurrence (outside ++ suffix)

/-- Successful nearest selection remains in the prefix. Only its outside grows. -/
theorem interpreter_append (known : findInterpreter graph effect frames = .ok cut) (suffix : List CoreMachine.Frame) :
    findInterpreter graph effect (frames ++ suffix) = .ok (appendInterpreter cut suffix) := by
  induction frames generalizing cut with
  | nil => cases known
  | cons frame rest ih =>
    cases frame with
    | resourceBoundary node key payload =>
      simp only [findInterpreter,List.cons_append] at known ⊢
      split at known <;> rename_i matching
      · cases known; simp [matching,appendInterpreter,Pure.pure,Except.pure]
      · cases found : findInterpreter graph effect rest with
        | error error => simp [found,Bind.bind,Except.bind] at known
        | ok selected =>
          have extended := ih found
          cases selected <;> simp only [found,Bind.bind,Except.bind,Pure.pure,Except.pure,Except.ok.injEq] at known <;> cases known <;> simp_all [appendInterpreter,Bind.bind,Except.bind,Pure.pure,Except.pure]
    | handlerBoundary node environment occurrence =>
      simp only [findInterpreter,List.cons_append] at known ⊢
      cases declarationEq : graph.node node with
      | none => simp [declarationEq,Bind.bind,Except.bind,Pure.pure,Except.pure] at known
      | some declared =>
        cases declaredKind : declared.kind <;> simp [declarationEq,declaredKind] at known ⊢
        rename_i handler handled body clauses
        split at known <;> rename_i matching
        · cases known; simp [matching,appendInterpreter,Pure.pure,Except.pure]
        · cases found : findInterpreter graph effect rest with
          | error error => simp [found,Bind.bind,Except.bind] at known
          | ok selected =>
            have extended := ih found
            cases selected <;> simp only [found,Bind.bind,Except.bind,Pure.pure,Except.pure,Except.ok.injEq] at known <;> cases known <;> simp_all [appendInterpreter,Bind.bind,Except.bind,Pure.pure,Except.pure]
    | bind binder body environment | applyFunction argument environment | applyArgument function
      | tupleLeft right environment | tupleRight left | matchCases arms environment
      | resourceInitializer site identity handle body environment | request requestedEffect operation environment
      | resume resumedHandler resumedOwner | clauseBoundary handler owner occurrence ticket saved
      | cleanupBoundary action environment identity | cleanupCompletion identity value | closeCompletion identity =>
      simp only [findInterpreter,List.cons_append] at known ⊢
      cases found : findInterpreter graph effect rest with
      | error error => simp [found,Bind.bind,Except.bind] at known
      | ok selected =>
        have extended := ih found
        cases selected <;> simp only [found,Bind.bind,Except.bind,Pure.pure,Except.pure,Except.ok.injEq] at known <;> cases known <;> simp_all [appendInterpreter,Bind.bind,Except.bind,Pure.pure,Except.pure]

theorem owner_append (known : findOwner handler owner frames = .ok cut) (suffix : List CoreMachine.Frame) :
    findOwner handler owner (frames ++ suffix) = .ok {cut with outside := cut.outside ++ suffix} := by
  induction frames generalizing cut with
  | nil => cases known
  | cons frame rest ih =>
    cases frame with
    | clauseBoundary candidate selected occurrence ticket saved =>
      simp only [findOwner,List.cons_append] at known ⊢
      split at known <;> rename_i matching
      · cases saved with
        | none => cases known
        | some capture => cases known; simp [matching,Pure.pure,Except.pure]
      · cases found : findOwner handler owner rest with
        | error error => simp [found,Bind.bind,Except.bind] at known
        | ok selected =>
          have extended := ih found
          simp only [found,Bind.bind,Except.bind,Pure.pure,Except.pure,Except.ok.injEq] at known
          cases known
          simp_all [Bind.bind,Except.bind,Pure.pure,Except.pure]
    | bind binder body environment | applyFunction argument environment | applyArgument function
      | tupleLeft right environment | tupleRight left | matchCases arms environment
      | resourceInitializer site identity handle body environment | request requestedEffect operation environment
      | resume resumedHandler resumedOwner | resourceBoundary node key payload | handlerBoundary node environment occurrence
      | cleanupBoundary action environment identity | cleanupCompletion identity value | closeCompletion identity =>
      simp only [findOwner,List.cons_append] at known ⊢
      cases found : findOwner handler owner rest with
      | error error => simp [found,Bind.bind,Except.bind] at known
      | ok selected =>
          have extended := ih found
          simp only [found,Bind.bind,Except.bind,Pure.pure,Except.pure,Except.ok.injEq] at known
          cases known
          simp_all [Bind.bind,Except.bind,Pure.pure,Except.pure]

theorem cell_success_append
    (step : interpretCell before cut operation value = .stepped after) (suffix : List CoreMachine.Frame) :
    interpretCell (appendFrames before suffix) {cut with outside := cut.outside ++ suffix} operation value =
      .stepped (appendFrames after suffix) := by
  unfold interpretCell at step ⊢
  simp only [appendFrames] at ⊢
  cases decoded : cellOperand before.heap operation value with
  | error error => simp [decoded] at step
  | ok decodedValue =>
    rcases decodedValue with ⟨handle,written⟩
    simp only [decoded] at step ⊢
    split at step <;> rename_i matching
    · cases step
    · cases written <;> cases step <;> simp [matching,appendFrames,List.append_assoc]

theorem resume_success_append
    (step : returnResume before handler owner value = .stepped after) (suffix : List CoreMachine.Frame) :
    returnResume (appendFrames before suffix) handler owner value = .stepped (appendFrames after suffix) := by
  unfold returnResume at step ⊢
  cases found : findOwner handler owner before.frames with
  | error error => simp [found] at step
  | ok cut =>
    simp only [found] at step
    cases step
    rw [show (appendFrames before suffix).frames = before.frames ++ suffix from rfl, owner_append found]
    simp [appendFrames,List.append_assoc]

theorem discard_success_append
    (step : discardOwner before handler owner = .stepped after) (suffix : List CoreMachine.Frame) :
    discardOwner (appendFrames before suffix) handler owner = .stepped (appendFrames after suffix) := by
  unfold discardOwner at step ⊢
  cases found : findOwner handler owner before.frames with
  | error error => simp [found] at step
  | ok cut =>
    simp only [found] at step
    rw [show (appendFrames before suffix).frames = before.frames ++ suffix from rfl, owner_append found]
    cases projection : closeFuel (framesMass cut.capture + 1) cut.capture with
    | error error => simp [projection] at step
    | ok result =>
      rcases result with ⟨closing,consumed⟩
      simp only [projection] at step ⊢
      split at step <;> rename_i empty <;> cases step <;> simp [empty,appendFrames,List.append_assoc]

theorem request_success_append
    (step : request graph before effect operation environment value = .stepped after) (suffix : List CoreMachine.Frame) :
    request graph (appendFrames before suffix) effect operation environment value = .stepped (appendFrames after suffix) := by
  unfold request at step ⊢
  cases requestedEq : effect.instantiate environment.instantiation with
  | user name arguments =>
    simp only [requestedEq] at step ⊢
    cases found : findInterpreter graph (.user name arguments) before.frames with
    | error error => cases error <;> simp [found] at step
    | ok cut =>
      rw [show (appendFrames before suffix).frames = before.frames ++ suffix from rfl,interpreter_append found]
      cases cut with
      | cell cut =>
        simp only [found,appendInterpreter] at step ⊢
        exact cell_success_append step suffix
      | handler inside node saved occurrence outside =>
        simp only [found,appendInterpreter] at step ⊢
        cases declarationEq : graph.node node with
        | none => simp [declarationEq] at step
        | some declaredNode =>
          cases declaredNode with
          | mk original type effects source nodeKind =>
            cases nodeKind <;> simp [declarationEq] at step ⊢
            rename_i handler handled body clauses
            cases selected : clauses.find? (fun clause => clause.operation == operation) with
            | none => simp [selected] at step
            | some clause =>
              cases argument : clause.argument <;> simp [selected,argument] at step ⊢
              cases step
              simp [appendFrames]
  | cell name =>
    cases name with
    | bound name => simp [requestedEq] at step
    | activation key =>
      simp only [requestedEq] at step ⊢
      cases found : findInterpreter graph (.cell (.activation key)) before.frames with
      | error error => cases error <;> simp [found] at step
      | ok cut =>
        rw [show (appendFrames before suffix).frames = before.frames ++ suffix from rfl,interpreter_append found]
        cases cut with
        | cell cut =>
          simp only [found,appendInterpreter] at step ⊢
          exact cell_success_append step suffix
        | handler inside node saved occurrence outside =>
          simp only [found,appendInterpreter] at step ⊢
          cases declarationEq : graph.node node with
          | none => simp [declarationEq] at step
          | some declaredNode =>
            cases declaredNode with
            | mk original type effects source nodeKind =>
              cases nodeKind <;> simp [declarationEq] at step ⊢
              rename_i handler handled body clauses
              cases selected : clauses.find? (fun clause => clause.operation == operation) with
              | none => simp [selected] at step
              | some clause =>
                cases argument : clause.argument <;> simp [selected,argument] at step ⊢
                cases step
                simp [appendFrames]

/-- This is success-only: terminal or rejected outcomes can change when a
suffix supplies another frame or interpreter. -/
theorem next_append (step : CoreMachine.next graph before = .stepped after) (suffix : List CoreMachine.Frame) :
    CoreMachine.next graph (appendFrames before suffix) = .stepped (appendFrames after suffix) := by
  cases control : before.control with
  | discard handler owner =>
    simp only [CoreMachine.next,control] at step
    simpa only [CoreMachine.next,appendFrames,control] using discard_success_append step suffix
  | evaluate index environment =>
    simp only [CoreMachine.next,appendFrames,control] at step ⊢
    cases found : graph.node index with
    | none => simp [found] at step
    | some node =>
      cases node with
      | mk original type effects source kind =>
        cases kind <;> simp only [found] at step ⊢
        all_goals repeat' (split at step)
        all_goals cases step <;> simp_all [appendFrames]
  | returned value =>
    simp only [CoreMachine.next,appendFrames,control] at step ⊢
    cases frames : before.frames with
    | nil => simp [frames] at step
    | cons frame rest =>
      cases frame <;> simp only [frames] at step ⊢
      case request effect operation environment =>
        simpa only [appendFrames,List.cons_append] using request_success_append step suffix
      case resume handler owner =>
        simpa only [appendFrames,List.cons_append] using resume_success_append step suffix
      all_goals repeat' (split at step)
      all_goals cases step <;> simp_all [appendFrames]

private theorem cell_heap_kept (step : interpretCell before cut operation value = .stepped after) :
    after.heap = before.heap := by
  unfold interpretCell at step
  cases decoded : cellOperand before.heap operation value with
  | error error => simp [decoded] at step
  | ok decodedValue =>
    rcases decodedValue with ⟨handle,written⟩
    simp only [decoded] at step
    split at step
    · cases step
    · cases written <;> cases step <;> rfl

private theorem resume_heap_kept (step : returnResume before handler owner value = .stepped after) :
    after.heap = before.heap := by
  unfold returnResume at step
  cases found : findOwner handler owner before.frames with
  | error error => simp [found] at step
  | ok cut => simp only [found] at step; cases step; rfl

private theorem discard_heap_kept (step : discardOwner before handler owner = .stepped after) :
    after.heap = before.heap := by
  unfold discardOwner at step
  cases found : findOwner handler owner before.frames with
  | error error => simp [found] at step
  | ok cut =>
    simp only [found] at step
    cases projection : closeFuel (framesMass cut.capture + 1) cut.capture with
    | error error => simp [projection] at step
    | ok result =>
      rcases result with ⟨closing,consumed⟩
      simp only [projection] at step
      split at step <;> cases step <;> rfl

private theorem request_heap_kept
    (step : request graph before effect operation environment value = .stepped after) :
    after.heap = before.heap := by
  unfold request at step
  cases requestedEq : effect.instantiate environment.instantiation with
  | user name arguments =>
    simp only [requestedEq] at step
    cases found : findInterpreter graph (.user name arguments) before.frames with
    | error error => cases error <;> simp [found] at step
    | ok cut =>
      cases cut with
      | cell cut =>
        simp only [found,appendInterpreter] at step
        exact cell_heap_kept step
      | handler inside node saved occurrence outside =>
        simp only [found,appendInterpreter] at step
        cases declarationEq : graph.node node with
        | none => simp [declarationEq] at step
        | some declaredNode =>
          cases declaredNode with
          | mk original type effects source nodeKind =>
            cases nodeKind <;> simp [declarationEq] at step
            rename_i handler handled body clauses
            cases selected : clauses.find? (fun clause => clause.operation == operation) with
            | none => simp [selected] at step
            | some clause =>
              cases argument : clause.argument <;> simp [selected,argument] at step
              cases step
              rfl
  | cell name =>
    cases name with
    | bound name => simp [requestedEq] at step
    | activation key =>
      simp only [requestedEq] at step
      cases found : findInterpreter graph (.cell (.activation key)) before.frames with
      | error error => cases error <;> simp [found] at step
      | ok cut =>
        cases cut with
        | cell cut =>
          simp only [found,appendInterpreter] at step
          exact cell_heap_kept step
        | handler inside node saved occurrence outside =>
          simp only [found,appendInterpreter] at step
          cases declarationEq : graph.node node with
          | none => simp [declarationEq] at step
          | some declaredNode =>
            cases declaredNode with
            | mk original type effects source nodeKind =>
              cases nodeKind <;> simp [declarationEq] at step
              rename_i handler handled body clauses
              cases selected : clauses.find? (fun clause => clause.operation == operation) with
              | none => simp [selected] at step
              | some clause =>
                cases argument : clause.argument <;> simp [selected,argument] at step
                cases step
                rfl

/-- The actual successful evaluator either keeps the heap or appends its
new tuple; no invariant about a desired successor is an input. -/
theorem next_heap_extends (step : CoreMachine.next graph before = .stepped after) :
    HeapExtends before.heap after.heap := by
  cases control : before.control with
  | discard handler owner =>
    simp only [CoreMachine.next,control] at step
    rw [discard_heap_kept step]
    exact fun _ _ known => known
  | evaluate index environment =>
    simp only [CoreMachine.next,control] at step
    cases found : graph.node index with
    | none => simp [found] at step
    | some node =>
      cases node with
      | mk original type effects source kind =>
        cases kind <;> simp only [found] at step
        all_goals repeat' (split at step)
        all_goals cases step <;> exact fun _ _ known => known
  | returned value =>
    simp only [CoreMachine.next,control] at step
    cases frames : before.frames with
    | nil => simp [frames] at step
    | cons frame rest =>
      cases frame <;> simp only [frames] at step
      case request effect operation environment =>
        rw [request_heap_kept step]
        exact fun _ _ known => known
      case resume handler owner =>
        rw [resume_heap_kept step]
        exact fun _ _ known => known
      all_goals repeat' (split at step)
      all_goals cases step
      all_goals first | exact fun _ _ known => known | exact heap_append _ _

theorem handler_cut_append (cut : HandlerCut requested whole captured outside data) (suffix : Stack) :
    HandlerCut requested (whole.append suffix) captured (outside.append suffix) data := by
  induction cut with
  | hit data outside matching => exact .hit data (outside.append suffix) matching
  | push frame rest captured outside data miss next ih => exact .push frame _ _ _ data miss ih
  | live ticket input answer saved scope rest captured outside data next ih => exact .live ticket input answer saved scope _ _ _ data ih
  | spent ticket answer scope rest captured outside data next ih => exact .spent ticket answer scope _ _ _ data ih

theorem cell_update_append (cut : CellUpdate identity old new before after) (suffix : Stack) :
    CellUpdate identity old new (before.append suffix) (after.append suffix) := by
  induction cut with
  | hit => exact .hit
  | push miss next ih => exact .push miss ih
  | live next ih => exact .live ih
  | spent next ih => exact .spent ih

def appendStack (configuration : Configuration) (suffix : Stack) : Configuration :=
  {configuration with stack := configuration.stack.append suffix}

/-- Exact event lists survive suffix extension. The obsolete discard rule is
structurally extendible too; current-machine lifting still requires ordinary. -/
theorem raw_step_append (step : RawStep before after created discharged) (suffix : Stack) :
    RawStep (appendStack before suffix) (appendStack after suffix) created discharged := by
  cases step with
  | focus plain focus tail => exact .focus plain focus (tail.append suffix)
  | plug plain value closed scope tail => exact .plug plain value closed scope (tail.append suffix)
  | bind parameter value body scope tail closed ready => exact .bind parameter value body scope (tail.append suffix) closed ready
  | beta parameter body value scope tail closed ready => exact .beta parameter body value scope (tail.append suffix) closed ready
  | ifTrue yes no scope tail => exact .ifTrue yes no scope (tail.append suffix)
  | ifFalse yes no scope tail => exact .ifFalse yes no scope (tail.append suffix)
  | enterHandler handler body tail => exact .enterHandler handler body (tail.append suffix)
  | leaveHandler handler value closed scope tail => exact .leaveHandler handler value closed scope (tail.append suffix)
  | enterCell binder identity payload body scope answer tail ready => exact .enterCell binder identity payload body scope answer (tail.append suffix) ready
  | leaveCell identity payload answer saved scope value closed tail => exact .leaveCell identity payload answer saved scope value closed (tail.append suffix)
  | enterCleanup action body tail => exact .enterCleanup action body (tail.append suffix)
  | startCleanup action saved closed scope tail => exact .startCleanup action saved closed scope (tail.append suffix)
  | finishCleanup action saved closed scope tail => exact .finishCleanup action saved closed scope (tail.append suffix)
  | capture requested operation parameter binder ticket operand body scope whole captured tail handler result selected clause closed ready =>
    exact .capture requested operation parameter binder ticket operand body scope (whole.append suffix) captured (tail.append suffix) handler result
      (handler_cut_append selected suffix) clause closed ready
  | resume binder ticket scope caller input answer front captured tail value closed resolve =>
    simpa [appendStack,Stack.append,stack_append_assoc] using
      RawStep.resume binder ticket scope caller input answer front captured (tail.append suffix) value closed resolve
  | discard binder ticket identity scope caller input answer front captured tail plan resolve build =>
    simpa [appendStack,Stack.append,stack_append_assoc] using
      RawStep.discard binder ticket identity scope caller input answer front captured (tail.append suffix) plan resolve build
  | leaveClause ticket answer value closed scope caller tail => exact .leaveClause ticket answer value closed scope caller (tail.append suffix)
  | finishClose identity scope caller tail => exact .finishClose identity scope caller (tail.append suffix)
  | retire ticket scope tail => exact .retire ticket scope (tail.append suffix)
  | readCell identity payload scope before after selected => exact .readCell identity payload scope _ _ (cell_update_append selected suffix)
  | writeCell identity old new scope before after selected => exact .writeCell identity old new scope _ _ (cell_update_append selected suffix)

theorem raw_trace_append (trace : RawTrace before after created discharged) (suffix : Stack) :
    RawTrace (appendStack before suffix) (appendStack after suffix) created discharged := by
  induction trace with
  | refl => exact .refl _
  | next step rest ih => exact .next (raw_step_append step suffix) ih

theorem ordinary_append (allowed : LexicalUnwind.ordinary before.expression) (suffix : Stack) :
    LexicalUnwind.ordinary (appendStack before suffix).expression := allowed

#print axioms interpreter_append
#print axioms owner_append
#print axioms request_success_append
#print axioms cell_success_append
#print axioms resume_success_append
#print axioms discard_success_append
#print axioms next_append
#print axioms next_heap_extends
#print axioms handler_cut_append
#print axioms cell_update_append
#print axioms raw_step_append
#print axioms raw_trace_append
#print axioms ordinary_append
end Ash.OneShot.CoreSuffixSplice
