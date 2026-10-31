import NetworkLedgerCoreValues

/- The restricted increment is the actual saved-context query followed by a
   RegionBuffer IntegerArithmetic Add. Its immediate and allocated return paths
   are modeled separately. Mathematical Int is the existing integer-value
   abstraction; the Rust integer and Region implementations supply its reviewed
   representation and allocation correspondence. This model issues no fact. -/
namespace Ash.NetworkLedger.CoreIncrement

open Ash.NetworkLedger.CoreEval
open Ash.NetworkLedger.CoreRegion
open Ash.NetworkLedger.CoreValues

/-- The checked RegionBuffer operation is addition, not another primitive. -/
inductive BufferOperation where
  | add | multiply
  deriving DecidableEq

structure RegionBuffer where
  api : Nat
  context : NodeId
  left : NodeId
  right : NodeId
  operation : BufferOperation
  deriving DecidableEq

abbrev Buffers := NodeId → Option RegionBuffer

/-- Exact linked coordinates; API and binder encodings preserve full identity. -/
structure CheckedIncrement (program : Program) (buffers : Buffers) where
  root : NodeId
  queryNode : NodeId
  unitNode : NodeId
  bufferNode : NodeId
  contextNode : NodeId
  leftNode : NodeId
  rightNode : NodeId
  contextBinder : Binder
  counterBinder : Binder
  api : Nat
  rootShape : program root = some (.bind contextBinder queryNode bufferNode)
  queryShape : program queryNode = some (.query unitNode)
  unitShape : program unitNode = some .unit
  bufferShape : buffers bufferNode = some ⟨api, contextNode, leftNode, rightNode, .add⟩
  evalShape : program bufferNode = some (.integerAdd api contextNode leftNode rightNode)
  contextShape : program contextNode = some (.variable contextBinder)
  leftShape : program leftNode = some (.variable counterBinder)
  rightShape : program rightNode = some (.integer 1)
  counterFresh : counterBinder ≠ contextBinder

/-- A normal run uses the exact checked query, context and strict operand order. -/
structure IncrementRun (program : Program) (buffers : Buffers) (checked : CheckedIncrement program buffers)
    (env : Environment) (start finish : Store) (result : Value)
    (workAvailable storageAvailable : Bool) where
  queried : Store
  afterContext : Store
  afterLeft : Store
  afterRight : Store
  leftValue : Value
  rightValue : Value
  queryEval : Eval program env checked.queryNode start .context queried
  contextEval : Eval program (extend env checked.contextBinder .context) checked.contextNode queried .context afterContext
  leftEval : Eval program (extend env checked.contextBinder .context) checked.leftNode afterContext leftValue afterLeft
  rightEval : Eval program (extend env checked.contextBinder .context) checked.rightNode afterLeft rightValue afterRight
  returned : BufferReturn leftValue rightValue workAvailable storageAvailable afterRight result finish

/-- Either successful storage path preserves the caller's existing heap cells. -/
theorem buffer_return_frame (left right : Value) (workAvailable storageAvailable : Bool)
    (start finish : Store) (result : Value) (bounded : BoundedLocations start)
    (returned : BufferReturn left right workAvailable storageAvailable start result finish) :
    finish.aliases = start.aliases ∧ BoundedLocations finish ∧
      (∀ address old, readCell start address = some old → readCell finish address = some old) := by
  cases returned with
  | immediate => exact ⟨rfl, bounded, fun _ _ read => read⟩
  | backed left right state afterAlloc out location bytes notFits nonempty allocated initialized =>
    obtain ⟨_, _, _, aliases, finalBound, retained⟩ := host_allocation_retains bounded allocated initialized
    exact ⟨aliases, finalBound, retained⟩

/-- Work refusal and unavailable storage on the large path cannot return normally. -/
theorem buffer_work_refusal (left right : Value) (storageAvailable : Bool)
    (start finish : Store) (result : Value) :
    ¬ BufferReturn left right false storageAvailable start result finish := by
  intro returned
  cases returned

theorem buffer_storage_refusal (left right : Int) (start finish : Store) (result : Value)
    (notFits : ¬ Immediate (left + right)) :
    ¬ BufferReturn (.integer left) (.integer right) true false start result finish := by
  intro returned
  cases returned <;> simp_all

theorem integer_one_inversion {program : Program} {node : NodeId} {env : Environment}
    {start finish : Store} {value : Value} (shape : program node = some (.integer 1))
    (evaluation : Eval program env node start value finish) :
    value = .integer 1 ∧ finish = start := by
  cases evaluation <;> simp_all

theorem buffer_returns_sum (left right : Int) (workAvailable storageAvailable : Bool)
    (start finish : Store) (result : Value)
    (returned : BufferReturn (.integer left) (.integer right) workAvailable storageAvailable start result finish) :
    result = .integer (left + right) := by
  cases returned <;> rfl

/-- Checked execution returns the mathematical successor and preserves the frame. -/
theorem checked_increment_normal_return (program : Program) (buffers : Buffers)
    (checked : CheckedIncrement program buffers) (env : Environment) (start finish : Store)
    (result : Value) (workAvailable storageAvailable : Bool) (counter : Int)
    (binding : CoreEval.lookup env checked.counterBinder = some (.integer counter))
    (nonnegative : 0 ≤ counter) (bounded : BoundedLocations start)
    (run : IncrementRun program buffers checked env start finish result workAvailable storageAvailable) :
    result = .integer (counter + 1) ∧ counter < counter + 1 ∧ 0 ≤ counter + 1 ∧
      finish.aliases = start.aliases ∧ BoundedLocations finish ∧
      (∀ address old, readCell start address = some old → readCell finish address = some old) := by
  obtain ⟨_, afterOperand, chosen, operandEval, queryStep⟩ := query_inversion checked.queryShape run.queryEval
  obtain ⟨_, operandState⟩ := unit_inversion checked.unitShape operandEval
  subst afterOperand
  have chosenHost := (query_projects start run.queried .hostDefault chosen queryStep).1
  subst chosen
  obtain ⟨_, contextState⟩ := variable_inversion checked.contextShape run.contextEval
  have extended : CoreEval.lookup (extend env checked.contextBinder .context) checked.counterBinder =
      some (.integer counter) := by
    rw [lookup_extended_other env checked.contextBinder checked.counterBinder checked.counterFresh]
    exact binding
  obtain ⟨leftBinding, leftState⟩ := variable_inversion checked.leftShape run.leftEval
  have leftEq : run.leftValue = .integer counter := by simpa [extended] using leftBinding.symm
  have rightEq := integer_one_inversion checked.rightShape run.rightEval
  have queriedBound := query_preserves_bounded start run.queried .hostDefault .hostDefault bounded queryStep
  have queryAliases : run.queried.aliases = start.aliases := by
    simp only [query, Option.some.injEq, Prod.mk.injEq] at queryStep
    rcases queryStep with ⟨_, stateEq⟩
    rw [← stateEq]
  have queryRetained : ∀ address old, readCell start address = some old → readCell run.queried address = some old := by
    intro address old read
    exact query_preserves_cell queryStep read
  have frame := buffer_return_frame _ _ workAvailable storageAvailable run.afterRight finish result
    (by simpa [contextState, leftState, rightEq.2] using queriedBound) run.returned
  have resultEq : result = .integer (counter + 1) := by
    have returned : BufferReturn (.integer counter) (.integer 1) workAvailable storageAvailable
        run.afterRight result finish := by simpa [leftEq, rightEq.1] using run.returned
    exact buffer_returns_sum counter 1 workAvailable storageAvailable run.afterRight finish result returned
  have rightAliases : run.afterRight.aliases = run.queried.aliases := by
    rw [rightEq.2, leftState, contextState]
  refine ⟨resultEq, by omega, by omega, ?_, frame.2.1, ?_⟩
  · exact frame.1.trans (rightAliases.trans queryAliases)
  · intro address old read
    apply frame.2.2 address old
    simpa [contextState, leftState, rightEq.2] using queryRetained address old read

/-- The actual checked Add evaluation supplies the existing strict increment run. -/
theorem checked_increment_from_eval (program : Program) (buffers : Buffers)
    (checked : CheckedIncrement program buffers) (env : Environment) (start finish : Store)
    (result : Value) (counter : Int)
    (binding : CoreEval.lookup env checked.counterBinder = some (.integer counter))
    (nonnegative : 0 ≤ counter) (bounded : BoundedLocations start)
    (evaluation : Eval program env checked.root start result finish) :
    result = .integer (counter + 1) ∧ counter < counter + 1 ∧ 0 ≤ counter + 1 ∧
      finish.aliases = start.aliases ∧ BoundedLocations finish ∧
      (∀ address old, readCell start address = some old → readCell finish address = some old) := by
  obtain ⟨queried, queryValue, queryEval, bufferEval⟩ := bind_inversion checked.rootShape evaluation
  have queryValueEq := (query_inversion checked.queryShape queryEval).1
  subst queryValue
  obtain ⟨afterContext, afterLeft, afterRight, leftValue, rightValue, workAvailable, storageAvailable,
    contextEval, leftEval, rightEval, returned⟩ := integer_add_inversion checked.evalShape bufferEval
  exact checked_increment_normal_return program buffers checked env start finish result workAvailable storageAvailable
    counter binding nonnegative bounded ⟨queried, afterContext, afterLeft, afterRight, leftValue, rightValue,
      queryEval, contextEval, leftEval, rightEval, returned⟩

end Ash.NetworkLedger.CoreIncrement
