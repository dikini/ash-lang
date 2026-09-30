import CoreUnwindRelation

/-! Normal cleanup saves an arbitrary current return value. Start interprets the
stored action through the same CleanupRel; finish requires the actual Unit
return, restores the saved value and scope, and discharges exactly its cleanup.
These are redex correspondence lemmas, not callback termination or safety. -/
namespace Ash.OneShot.CoreNormalCleanupSteps
open ScopedExpressions ScopedExecution CoreValueRelation CoreStrictStack
  CoreCleanupFrames CoreCleanupRunFrames CoreUnwindRelation

private theorem closed_ordinary (closed : ClosedValue code) : LexicalUnwind.ordinary code := by
  cases code <;> simp [LexicalUnwind.ordinary]
  simpa [Code.IsValue] using closed.1

/-- Extract the delayed action interpretation from its single saved carrier. -/
theorem delayed_action
    (delayed : CleanupRel graph owners heap (.cleanupBoundary action environment data.identity) data) :
    ∃ callback, CoreTranslation.translateFuel graph 3 owners action =
      .ok (.app (.variable callback) .unit) ∧
      EnvCloses graph owners heap environment (.app (.variable callback) .unit) (.app data.action .unit) := by
  generalize frameEq : CoreMachine.Frame.cleanupBoundary action environment data.identity = frame at delayed
  generalize dataEq : data = targetData at delayed
  cases delayed with
  | armed known kind shape translated saved lookup value =>
      cases dataEq
      obtain ⟨rfl,rfl,_⟩ := CoreMachine.Frame.cleanupBoundary.inj frameEq
      exact ⟨_,translated,saved⟩

def startBefore (base : CoreMachine.State) (action : CoreSyntax.NodeRef)
    (environment : CoreMachine.Environment) (identity : Nat) (savedValue : CoreMachine.Value)
    (outside : List MappedFrame) : CoreMachine.State :=
  { base with
    control := .returned savedValue,
    frames := .cleanupBoundary action environment identity :: framesOf outside }

def startAfter (base : CoreMachine.State) (action : CoreSyntax.NodeRef)
    (environment : CoreMachine.Environment) (identity : Nat) (savedValue : CoreMachine.Value)
    (outside : List MappedFrame) : CoreMachine.State :=
  { base with
    control := .evaluate action environment,
    frames := .cleanupCompletion identity savedValue :: framesOf outside,
    observations := base.observations ++ [.cleanupStarted identity] }

/-- Actual normal start: all interpretations are constructed from current
saved witnesses, including arbitrary saved values and supplied annotations. -/
theorem normal_start
    (delayed : CleanupRel graph cleanupOwners base.heap (.cleanupBoundary action environment data.identity) data)
    (saved : ValueRel graph callerOwners base.heap savedValue savedCode)
    (outside : PushedWithMaps graph base.heap outsideMaps outsideTarget)
    (scope : Scope) :
    ComponentMapped graph callerOwners
      ((cleanupOwners,.cleanupBoundary action environment data.identity)::outsideMaps)
      (startBefore base action environment data.identity savedValue outsideMaps)
      ⟨savedCode,scope,.push (.armed data) outsideTarget⟩ ∧
    CoreMachine.next graph (startBefore base action environment data.identity savedValue outsideMaps) =
      .stepped (startAfter base action environment data.identity savedValue outsideMaps) ∧
    LexicalUnwind.Transition
      (.eval ⟨savedCode,scope,.push (.armed data) outsideTarget⟩)
      (.eval ⟨.app data.action .unit,.none,.push (.running data savedCode saved.closed) outsideTarget⟩) [] [] ∧
    Related graph ⟨startAfter base action environment data.identity savedValue outsideMaps,
      .eval ⟨.app data.action .unit,.none,.push (.running data savedCode saved.closed) outsideTarget⟩,
      cleanupOwners,[]⟩ := by
  obtain ⟨callback,translated,closed⟩ := delayed_action delayed
  have component : ComponentMapped graph cleanupOwners []
      (isolate (startAfter base action environment data.identity savedValue outsideMaps) [])
      ⟨.app data.action .unit,.none,.nil⟩ :=
    ⟨rfl,_,.none,.evaluate translated closed,pushed_mapped .nil⟩
  exact ⟨⟨rfl,_,scope,.returned saved,pushed_mapped (.cleanup delayed outside)⟩,
    rfl,.evaluate (.startCleanup data savedCode saved.closed scope outsideTarget) (closed_ordinary saved.closed),
    .runningCleanup (state := startAfter base action environment data.identity savedValue outsideMaps)
      (.normal delayed saved outside) component rfl⟩

def finishBefore (base : CoreMachine.State) (identity : Nat) (savedValue : CoreMachine.Value)
    (outside : List MappedFrame) : CoreMachine.State :=
  { base with
    control := .returned .unit,
    frames := .cleanupCompletion identity savedValue :: framesOf outside }

def finishAfter (base : CoreMachine.State) (identity : Nat) (savedValue : CoreMachine.Value)
    (outside : List MappedFrame) : CoreMachine.State :=
  { base with
    control := .returned savedValue, frames := framesOf outside,
    observations := base.observations ++ [.cleanupFinished identity] }

/-- Actual Unit completion restores the saved return value and ActionData scope.
No evaluation or future-success premise is supplied for the callback. -/
theorem normal_finish
    (delayed : CleanupRel graph cleanupOwners base.heap (.cleanupBoundary action environment data.identity) data)
    (saved : ValueRel graph callerOwners base.heap savedValue savedCode)
    (outside : PushedWithMaps graph base.heap outsideMaps outsideTarget)
    (activeOwners : CoreTranslation.OwnerMap) (scope : Scope) :
    Related graph ⟨finishBefore base data.identity savedValue outsideMaps,
      .eval ⟨.unit,scope,.push (.running data savedCode saved.closed) outsideTarget⟩,activeOwners,[]⟩ ∧
    CoreMachine.next graph (finishBefore base data.identity savedValue outsideMaps) =
      .stepped (finishAfter base data.identity savedValue outsideMaps) ∧
    LexicalUnwind.Transition
      (.eval ⟨.unit,scope,.push (.running data savedCode saved.closed) outsideTarget⟩)
      (.eval ⟨savedCode,data.scope,outsideTarget⟩) [] [.cleanup data.identity] ∧
    ComponentMapped graph callerOwners outsideMaps
      (finishAfter base data.identity savedValue outsideMaps) ⟨savedCode,data.scope,outsideTarget⟩ := by
  have component : ComponentMapped graph activeOwners []
      (isolate (finishBefore base data.identity savedValue outsideMaps) []) ⟨.unit,scope,.nil⟩ :=
    ⟨rfl,.unit,scope,.returned .unit,pushed_mapped .nil⟩
  exact ⟨.runningCleanup (state := finishBefore base data.identity savedValue outsideMaps)
      (.normal delayed saved outside) component rfl,rfl,
    .evaluate (.finishCleanup data savedCode saved.closed scope outsideTarget) (by trivial),
    ⟨rfl,_,data.scope,.returned saved,pushed_mapped outside⟩⟩

/-- A non-Unit callback result is an error, never normal cleanup progress. -/
theorem nonunit_rejected {base : CoreMachine.State} (notUnit : value ≠ CoreMachine.Value.unit) :
    CoreMachine.next graph { base with
      control := .returned value,
      frames := .cleanupCompletion identity savedValue :: framesOf outsideMaps } =
      .rejected .cleanupResult := by
  cases value <;> first | exact False.elim (notUnit rfl) | rfl

theorem nonunit_not_step {base : CoreMachine.State} (notUnit : value ≠ CoreMachine.Value.unit) (after : CoreMachine.State) :
    ¬ CoreMachine.Step graph { base with
      control := .returned value,
      frames := .cleanupCompletion identity savedValue :: framesOf outsideMaps } after :=
  CoreMachine.rejected_not_step graph _ .cleanupResult (nonunit_rejected notUnit) after

#print axioms delayed_action
#print axioms normal_start
#print axioms normal_finish
#print axioms nonunit_rejected
#print axioms nonunit_not_step
end Ash.OneShot.CoreNormalCleanupSteps
