import CoreCellWriteFrames

/-! Actual builtin cell completion from one saved request carrier and current
operand relation. The mapped nearest cut constructs both endpoints. Supplied
scope/row annotations, target-world authentication and general projected cleanup
dispatch remain separate obligations. -/
namespace Ash.OneShot.CoreCellSteps
open ScopedExpressions ScopedExecution Instantiation CoreValueRelation CoreStrictStack
  CoreRequestFrames CoreCellWriteFrames CoreCleanupRunFrames CoreCleanupFrames CoreUnwindRelation

/-- The dynamic effect comes from the request's existing closing derivation. -/
theorem request_effect
    (request : RequestRel graph owners heap (.request effect operation environment) plain)
    (context : plain.context = .perform (freezeEffect (.cell identity)) operation) :
    effect.instantiate environment.instantiation = .cell (.activation identity) := by
  cases request with
  | operand carrier actual =>
      have same := Context.perform.inj (actual.symm.trans context)
      have header := perform_components_at carrier _ _ _ _ _ rfl rfl
      exact header.1.trans same.1

/-- Decode a related scalar without assuming an independent operand equation. -/
theorem handle_operand (related : ValueRel graph owners heap value (.resourceRef (.activation identity))) :
    value = .handle identity := by
  cases value with
  | closure parameter body environment =>
      obtain ⟨result,same⟩ := related.closure_shape
      cases same
  | unit | boolean _ | integer _ | location _ => cases related
  | handle key => cases related; rfl

theorem integer_operand (related : ValueRel graph owners heap value (.integer written)) :
    value = .integer written := by
  cases value with
  | closure parameter body environment =>
      obtain ⟨result,same⟩ := related.closure_shape
      cases same
  | unit | boolean _ | handle _ | location _ => cases related
  | integer number => cases related; rfl

/-- Related write pairs expose the actual heap cell used by cellOperand. -/
theorem write_operand
    (related : ValueRel graph owners heap value (.pair (.resourceRef (.activation identity)) (.integer written))) :
    ∃ index, value = .location index ∧ heap[index]? = some (.pair (.handle identity) (.integer written)) := by
  cases value with
  | closure parameter body environment =>
      obtain ⟨result,same⟩ := related.closure_shape
      cases same
  | unit | boolean _ | integer _ | handle _ => cases related
  | location index =>
      cases related with
      | location known left right =>
          rw [handle_operand left,integer_operand right] at known
          exact ⟨index,rfl,known⟩

def requestBefore (base : CoreMachine.State) (effect : Effect) (operation : Nat)
    (environment : CoreMachine.Environment) (value : CoreMachine.Value) (maps : List MappedFrame) : CoreMachine.State :=
  { base with
    control := .returned value,
    frames := .request effect operation environment :: framesOf maps }

def readAfter (base : CoreMachine.State) (identity : Nat) (payload : Int) (maps : List MappedFrame) : CoreMachine.State :=
  { base with
    control := .returned (.integer payload), frames := framesOf maps,
    observations := base.observations ++ [.read identity payload] }

def writeAfter (base : CoreMachine.State) (identity : Nat) (written : Int) (maps : List MappedFrame) : CoreMachine.State :=
  { base with
    control := .returned .unit, frames := framesOf maps,
    observations := base.observations ++ [.written identity written] }

/-- Generic read derives the full actual successor and both interpretations. -/
theorem read_complete
    (request : RequestRel graph requestOwners base.heap (.request effect 0 environment) plain)
    (context : plain.context = .perform (freezeEffect (.cell identity)) 0)
    (operand : ValueRel graph owners base.heap value (.resourceRef (.activation identity)))
    (cut : WriteCut graph base.heap identity payload payload maps target changedMaps changedTarget)
    (runtimeScope : Scope) :
    ComponentMapped graph owners ((requestOwners,.request effect 0 environment)::maps)
      (requestBefore base effect 0 environment value maps)
      ⟨.perform (freezeEffect (.cell identity)) 0 (.resourceRef (.activation identity)),plain.scope,target⟩ ∧
    CoreMachine.next graph (requestBefore base effect 0 environment value maps) =
      .stepped (readAfter base identity payload maps) ∧
    LexicalUnwind.Transition
      (.eval ⟨.perform (freezeEffect (.cell identity)) 0 (.resourceRef (.activation identity)),plain.scope,target⟩)
      (.eval ⟨.integer payload,plain.scope,target⟩) [] [] ∧
    ComponentMapped graph owners maps (readAfter base identity payload maps)
      ⟨.integer payload,plain.scope,target⟩ := by
  obtain ⟨rfl,rfl⟩ := cut.unchanged
  obtain ⟨inside,site,outside,beforeEq,afterEq,selector⟩ := cut.realizes
  have stack := prepend_request request operand.closed (pushed_mapped cut.components.1) runtimeScope
  rw [context] at stack
  have actual := request_effect request context
  have decoded := handle_operand operand
  refine ⟨⟨rfl,_,runtimeScope,.returned operand,stack⟩,?_,
    .evaluate (.readCell identity payload plain.scope target target cut.components.2.2) (by trivial),
    ⟨rfl,_,plain.scope,.returned .integer,pushed_mapped cut.components.1⟩⟩
  simp [requestBefore,readAfter,CoreMachine.next,CoreMachine.request,actual,selector,
    CoreMachine.interpretCell,CoreMachine.cellOperand,decoded]

/-- Generic write derives operand decoding and nearest selection from the same
current relations; only the selected cell changes, with one write observation. -/
theorem write_complete
    (request : RequestRel graph requestOwners base.heap (.request effect 1 environment) plain)
    (context : plain.context = .perform (freezeEffect (.cell identity)) 1)
    (operand : ValueRel graph owners base.heap value (.pair (.resourceRef (.activation identity)) (.integer written)))
    (cut : WriteCut graph base.heap identity old written maps target changedMaps changedTarget)
    (runtimeScope : Scope) :
    ComponentMapped graph owners ((requestOwners,.request effect 1 environment)::maps)
      (requestBefore base effect 1 environment value maps)
      ⟨.perform (freezeEffect (.cell identity)) 1 (.pair (.resourceRef (.activation identity)) (.integer written)),plain.scope,target⟩ ∧
    CoreMachine.next graph (requestBefore base effect 1 environment value maps) =
      .stepped (writeAfter base identity written changedMaps) ∧
    LexicalUnwind.Transition
      (.eval ⟨.perform (freezeEffect (.cell identity)) 1 (.pair (.resourceRef (.activation identity)) (.integer written)),plain.scope,target⟩)
      (.eval ⟨.unit,plain.scope,changedTarget⟩) [] [] ∧
    ComponentMapped graph owners changedMaps (writeAfter base identity written changedMaps)
      ⟨.unit,plain.scope,changedTarget⟩ := by
  obtain ⟨inside,site,outside,beforeEq,afterEq,selector⟩ := cut.realizes
  obtain ⟨index,rfl,known⟩ := write_operand operand
  have stack := prepend_request request operand.closed (pushed_mapped cut.components.1) runtimeScope
  rw [context] at stack
  have actual := request_effect request context
  refine ⟨⟨rfl,_,runtimeScope,.returned operand,stack⟩,?_,
    .evaluate (.writeCell identity old written plain.scope target changedTarget cut.components.2.2) (by trivial),
    ⟨rfl,_,plain.scope,.returned .unit,pushed_mapped cut.components.2.1⟩⟩
  simp [requestBefore,writeAfter,CoreMachine.next,CoreMachine.request,actual,selector,
    CoreMachine.interpretCell,CoreMachine.cellOperand,known,afterEq]

def normalBefore (base : CoreMachine.State) (effect : Effect) (operation : Nat)
    (environment : CoreMachine.Environment) (value : CoreMachine.Value)
    (cleanup : Nat) (saved : CoreMachine.Value) (maps : List MappedFrame) : CoreMachine.State :=
  { base with
    control := .returned value,
    frames := .request effect operation environment :: .cleanupCompletion cleanup saved :: framesOf maps }

def normalReadAfter (base : CoreMachine.State) (identity cleanup : Nat) (payload : Int)
    (saved : CoreMachine.Value) (maps : List MappedFrame) : CoreMachine.State :=
  { readAfter base identity payload maps with frames := .cleanupCompletion cleanup saved :: framesOf maps }

def normalWriteAfter (base : CoreMachine.State) (identity cleanup : Nat) (written : Int)
    (saved : CoreMachine.Value) (maps : List MappedFrame) : CoreMachine.State :=
  { writeAfter base identity written maps with frames := .cleanupCompletion cleanup saved :: framesOf maps }

/-- Immediate normal cleanup requests retain the same delayed action, arbitrary
saved return value, and outside stack. There is no opaque physical suffix. -/
theorem normal_request_current
    (request : RequestRel graph requestOwners base.heap (.request effect operation environment) plain)
    (context : plain.context = .perform (freezeEffect (.cell identity)) operation)
    (operand : ValueRel graph owners base.heap value operandCode)
    (delayed : CleanupRel graph cleanupOwners base.heap (.cleanupBoundary action savedEnvironment data.identity) data)
    (saved : ValueRel graph callerOwners base.heap savedValue savedCode)
    (outside : PushedWithMaps graph base.heap maps target)
    (runtimeScope : Scope) :
    Related graph ⟨normalBefore base effect operation environment value data.identity savedValue maps,
      .eval ⟨.perform (freezeEffect (.cell identity)) operation operandCode,plain.scope,
        .push (.running data savedCode saved.closed) target⟩,
      owners,[(requestOwners,.request effect operation environment)]⟩ := by
  have stack := prepend_request request operand.closed (pushed_mapped (PushedWithMaps.nil (graph := graph) (heap := base.heap))) runtimeScope
  rw [context] at stack
  have component : ComponentMapped graph owners [(requestOwners,.request effect operation environment)]
      (isolate (normalBefore base effect operation environment value data.identity savedValue maps)
        [(requestOwners,.request effect operation environment)])
      ⟨.perform (freezeEffect (.cell identity)) operation operandCode,plain.scope,.nil⟩ :=
    ⟨rfl,operandCode,runtimeScope,.returned operand,stack⟩
  exact .runningCleanup (state := normalBefore base effect operation environment value data.identity savedValue maps)
    (.normal delayed saved outside) component rfl

/-- Read immediately above normal cleanup preserves its arbitrary saved value. -/
theorem normal_read_complete
    (request : RequestRel graph requestOwners base.heap (.request effect 0 environment) plain)
    (context : plain.context = .perform (freezeEffect (.cell identity)) 0)
    (operand : ValueRel graph owners base.heap value (.resourceRef (.activation identity)))
    (delayed : CleanupRel graph cleanupOwners base.heap (.cleanupBoundary action savedEnvironment data.identity) data)
    (saved : ValueRel graph callerOwners base.heap savedValue savedCode)
    (cut : WriteCut graph base.heap identity payload payload maps target changedMaps changedTarget)
    (runtimeScope : Scope) :
    Related graph ⟨normalBefore base effect 0 environment value data.identity savedValue maps,
      .eval ⟨.perform (freezeEffect (.cell identity)) 0 (.resourceRef (.activation identity)),plain.scope,
        .push (.running data savedCode saved.closed) target⟩,
      owners,[(requestOwners,.request effect 0 environment)]⟩ ∧
    CoreMachine.next graph (normalBefore base effect 0 environment value data.identity savedValue maps) =
      .stepped (normalReadAfter base identity data.identity payload savedValue maps) ∧
    LexicalUnwind.Transition
      (.eval ⟨.perform (freezeEffect (.cell identity)) 0 (.resourceRef (.activation identity)),plain.scope,
        .push (.running data savedCode saved.closed) target⟩)
      (.eval ⟨.integer payload,plain.scope,.push (.running data savedCode saved.closed) target⟩) [] [] ∧
    Related graph ⟨normalReadAfter base identity data.identity payload savedValue maps,
      .eval ⟨.integer payload,plain.scope,.push (.running data savedCode saved.closed) target⟩,owners,[]⟩ := by
  obtain ⟨rfl,rfl⟩ := cut.unchanged
  obtain ⟨inside,site,outside,beforeEq,afterEq,selector⟩ := cut.realizes
  have actual := request_effect request context
  have decoded := handle_operand operand
  have selected : CellUpdate identity payload payload
      (.push (.running data savedCode saved.closed) target)
      (.push (.running data savedCode saved.closed) target) :=
    .push (by simp [ExecFrame.erase,Frame.target]) cut.components.2.2
  have component : ComponentMapped graph owners []
      (isolate (normalReadAfter base identity data.identity payload savedValue maps) [])
      ⟨.integer payload,plain.scope,.nil⟩ := ⟨rfl,_,plain.scope,.returned .integer,pushed_mapped .nil⟩
  refine ⟨normal_request_current request context operand delayed saved cut.components.1 runtimeScope,?_,
    .evaluate (.readCell identity payload plain.scope _ _ selected) (by trivial),
    .runningCleanup (state := normalReadAfter base identity data.identity payload savedValue maps)
      (.normal delayed saved cut.components.1) component rfl⟩
  simp [normalBefore,normalReadAfter,readAfter,CoreMachine.next,CoreMachine.request,actual,selector,
    CoreMachine.findInterpreter,CoreMachine.interpretCell,CoreMachine.cellOperand,decoded,
    Bind.bind,Except.bind,Pure.pure,Except.pure]

/-- Write immediately above normal cleanup updates only the outside selected
cell, preserving saved value/action and supplying the actual successor carrier. -/
theorem normal_write_complete
    (request : RequestRel graph requestOwners base.heap (.request effect 1 environment) plain)
    (context : plain.context = .perform (freezeEffect (.cell identity)) 1)
    (operand : ValueRel graph owners base.heap value (.pair (.resourceRef (.activation identity)) (.integer written)))
    (delayed : CleanupRel graph cleanupOwners base.heap (.cleanupBoundary action savedEnvironment data.identity) data)
    (saved : ValueRel graph callerOwners base.heap savedValue savedCode)
    (cut : WriteCut graph base.heap identity old written maps target changedMaps changedTarget)
    (runtimeScope : Scope) :
    Related graph ⟨normalBefore base effect 1 environment value data.identity savedValue maps,
      .eval ⟨.perform (freezeEffect (.cell identity)) 1 (.pair (.resourceRef (.activation identity)) (.integer written)),plain.scope,
        .push (.running data savedCode saved.closed) target⟩,
      owners,[(requestOwners,.request effect 1 environment)]⟩ ∧
    CoreMachine.next graph (normalBefore base effect 1 environment value data.identity savedValue maps) =
      .stepped (normalWriteAfter base identity data.identity written savedValue changedMaps) ∧
    LexicalUnwind.Transition
      (.eval ⟨.perform (freezeEffect (.cell identity)) 1 (.pair (.resourceRef (.activation identity)) (.integer written)),plain.scope,
        .push (.running data savedCode saved.closed) target⟩)
      (.eval ⟨.unit,plain.scope,.push (.running data savedCode saved.closed) changedTarget⟩) [] [] ∧
    Related graph ⟨normalWriteAfter base identity data.identity written savedValue changedMaps,
      .eval ⟨.unit,plain.scope,.push (.running data savedCode saved.closed) changedTarget⟩,owners,[]⟩ := by
  obtain ⟨inside,site,outside,beforeEq,afterEq,selector⟩ := cut.realizes
  obtain ⟨index,rfl,known⟩ := write_operand operand
  have actual := request_effect request context
  have selected : CellUpdate identity old written
      (.push (.running data savedCode saved.closed) target)
      (.push (.running data savedCode saved.closed) changedTarget) :=
    .push (by simp [ExecFrame.erase,Frame.target]) cut.components.2.2
  have component : ComponentMapped graph owners []
      (isolate (normalWriteAfter base identity data.identity written savedValue changedMaps) [])
      ⟨.unit,plain.scope,.nil⟩ := ⟨rfl,_,plain.scope,.returned .unit,pushed_mapped .nil⟩
  refine ⟨normal_request_current request context operand delayed saved cut.components.1 runtimeScope,?_,
    .evaluate (.writeCell identity old written plain.scope _ _ selected) (by trivial),
    .runningCleanup (state := normalWriteAfter base identity data.identity written savedValue changedMaps)
      (.normal delayed saved cut.components.2.1) component rfl⟩
  simp [normalBefore,normalWriteAfter,writeAfter,CoreMachine.next,CoreMachine.request,actual,selector,
    CoreMachine.findInterpreter,CoreMachine.interpretCell,CoreMachine.cellOperand,known,afterEq,
    Bind.bind,Except.bind,Pure.pure,Except.pure]

#print axioms request_effect
#print axioms handle_operand
#print axioms integer_operand
#print axioms write_operand
#print axioms read_complete
#print axioms write_complete
#print axioms normal_request_current
#print axioms normal_read_complete
#print axioms normal_write_complete
end Ash.OneShot.CoreCellSteps
