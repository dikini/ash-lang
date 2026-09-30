import CoreStrictPotential

/-! Transport of the existing administrative value witnesses through mixed
ordinary stacks for TASK-0032. Every theorem shares one target configuration
and the actual current interpretation derivation. No determinism of unrelated
closing derivations, future validity, reachability or full simulation is used.
The existing ready guard excludes unsupported and effect traversal families.
Saved PlainData annotations remain explicit static authentication obligations. -/
namespace Ash.OneShot.CoreAdministrativeTransport
open ScopedExpressions ScopedExecution CoreValueRelation CoreStrictFrames CoreStrictStack
open CoreAdministrativeSteps CoreStrictPotential

/-- Prepend a ready inner frame to the existing flattened prefix, preserving
all remaining flattened and pushed frames and their saved lexical scopes. -/
theorem ordinary_prepend (frame : PlainFrameRel graph owners heap core plain)
    (ready : ClosedValue code)
    (tail : OrdinaryStackRel graph owners heap cores (plain.context.plug code) plain.scope
      result resultScope target) (runtimeScope : Scope) :
    OrdinaryStackRel graph owners heap (core :: cores) code runtimeScope result resultScope target := by
  obtain ⟨flatPrefix, suffix, split, flattened, pushed⟩ := tail
  exact ⟨core :: flatPrefix, suffix, by simp [split], .cons frame ready flattened, pushed⟩

/-- Exact allowed-family guard and strict common potential preclude generic
unchanged-target progress. Both interpretations share the same configuration. -/
structure TransportWitness (graph : CoreSyntax.Graph) (owners : CoreTranslation.OwnerMap)
    (before after : CoreMachine.State) (target : Configuration) : Prop where
  permitted : CoreAdministrativeSteps.ready graph before = true
  core : CoreMachine.next graph before = .stepped after
  decreasing : potential graph after < potential graph before
  current : ComponentRel graph owners before target
  successor : ComponentRel graph owners after target

/-- Value-node entry preserves heap and frames by its actual permitted next
transition. These equalities are conclusions, not successor-state premises. -/
theorem value_entry_fields
    (witness : ValueWitness graph owners before after code)
    (evaluating : before.control = .evaluate index environment) :
    after.heap = before.heap ∧ after.frames = before.frames := by
  have permitted := witness.permitted
  have next := witness.core
  cases known : graph.node index with
  | none => simp [CoreAdministrativeSteps.ready, evaluating, known] at permitted
  | some node =>
    have supported : valueKind node.kind = true := by
      simpa [CoreAdministrativeSteps.ready, evaluating, known] using permitted
    cases kind : node.kind <;> simp only [kind, valueKind, Bool.false_eq_true] at supported
    all_goals try contradiction
    all_goals simp only [CoreMachine.next, evaluating, known, kind] at next
    all_goals try (cases next; exact ⟨rfl, rfl⟩)
    case «variable» name =>
      cases lookup : environment.lookup name with
      | none => simp only [lookup] at next; cases next
      | some value => simp only [lookup] at next; cases next; exact ⟨rfl, rfl⟩

/-- Reuse the exact current evaluate interpretation carried by the witness,
then reuse its actual returned value. The arbitrary mixed stack is unchanged. -/
theorem value_entry
    (witness : ValueWitness graph owners before after code)
    (evaluating : before.control = .evaluate index environment)
    (stack : OrdinaryStackRel graph owners before.heap before.frames code scope result resultScope target) :
    TransportWitness graph owners before after ⟨result, resultScope, target⟩ := by
  obtain ⟨heap, frames⟩ := value_entry_fields witness evaluating
  have current : ControlRel graph owners before.heap before.control code := by
    cases witness.current with
    | evaluate control translated saved closed => rw [control]; exact .evaluate translated saved
    | tuple control frames left right => rw [evaluating] at control; cases control
  obtain ⟨value, returned, related⟩ := witness.returned
  have successorStack : OrdinaryStackRel graph owners after.heap after.frames code scope result resultScope target := by
    rw [heap, frames]; exact stack
  exact ⟨witness.permitted, witness.core, administrative_potential witness,
    ⟨code, scope, current, stack⟩,
    ⟨code, scope, by rw [returned]; exact .returned related, successorStack⟩⟩

/-- Tuple allocation consumes one ready flattened frame and transports the
remaining mixed stack through append-only heap extension. Further ready pair
frames may remain flattened; the exact input operand relations build both the
allocation witness and the before-side interpretation. -/
theorem tuple_allocation {base : CoreMachine.State}
    (left : ValueRel graph owners base.heap leftValue leftCode)
    (right : ValueRel graph owners base.heap rightValue rightCode)
    (plain : PlainData) (context : plain.context = .pairRight leftCode)
    (stack : OrdinaryStackRel graph owners base.heap cores (.pair leftCode rightCode) plain.scope
      result resultScope target) (runtimeScope : Scope) :
    TransportWitness graph owners
      { base with control := .returned rightValue, frames := .tupleRight leftValue :: cores }
      { base with control := .returned (.location base.heap.length), frames := cores, heap := base.heap ++ [.pair leftValue rightValue] }
      ⟨result, resultScope, target⟩ := by
  obtain ⟨witness, extension, values, environments⟩ := CoreAdministrativeSteps.tuple_allocate left right cores
  have frame : PlainFrameRel graph owners base.heap (.tupleRight leftValue) plain := by
    change FrameRel graph owners base.heap _ plain.context
    rw [context]; exact .tupleRight left
  have tail : OrdinaryStackRel graph owners base.heap cores (plain.context.plug rightCode) plain.scope
      result resultScope target := by
    simpa only [context, Context.plug] using stack
  have beforeStack := ordinary_prepend frame right.closed tail runtimeScope
  obtain ⟨value, control, related⟩ := witness.returned
  have afterStack := stack.heap_weaken extension
  exact ⟨witness.permitted, witness.core, administrative_potential witness,
    ⟨rightCode, runtimeScope, .returned right, beforeStack⟩,
    ⟨.pair leftCode rightCode, plain.scope, by rw [control]; exact .returned related, afterStack⟩⟩

theorem unchanged_transport_rejected (graph : CoreSyntax.Graph) (owners : CoreTranslation.OwnerMap)
    (state : CoreMachine.State) (target : Configuration) :
    ¬ TransportWitness graph owners state state target := by
  intro witness
  exact unchanged_potential_rejected graph state witness.decreasing

namespace Examples
open CoreMachineExamples
private def base : CoreMachine.State := { control := .returned .unit }
private def caller : MEnv := .binding 1 (.integer 99) .empty
private def lexicalPlain : PlainData := ⟨.bind 4 (.integer 99), .none, .unit, .unit, [], rfl⟩
private def outerPairPlain : PlainData := ⟨.pairRight (.integer 99), .none, .unit, .unit, [], rfl⟩
private def innerPairPlain : PlainData := ⟨.pairRight (.integer 17), .none, .unit, .unit, [], rfl⟩
private def innerPair : Code := .pair (.integer 17) .unit
private def nestedPair : Code := .pair (.integer 99) innerPair
private def lexicalFrames : List CoreMachine.Frame := [.bind 4 1 caller]
private def outerFrames : List CoreMachine.Frame := .tupleRight (.integer 99) :: lexicalFrames
private def allFrames : List CoreMachine.Frame := .tupleRight (.integer 17) :: outerFrames
private def targetStack : Stack := .push (.plain lexicalPlain) .nil
private def target : Configuration := ⟨nestedPair, .none, targetStack⟩
private def evaluating : CoreMachine.State := { base with control := .evaluate 4 caller, frames := allFrames }
private def returned : CoreMachine.State := { base with control := .returned .unit, frames := allFrames, observations := [.entered 4] }
private def allocated : CoreMachine.State := { returned with control := .returned (.location 0), frames := outerFrames, heap := [.pair (.integer 17) .unit] }
private def nestedAllocated : CoreMachine.State := { allocated with control := .returned (.location 1), frames := lexicalFrames, heap := [.pair (.integer 17) .unit, .pair (.integer 99) (.location 0)] }

private theorem lexical_tail : PushedRel lexicalClosure [] [] lexicalFrames targetStack := by
  apply PushedRel.cons (plain := lexicalPlain)
  · change FrameRel lexicalClosure [] [] (.bind 4 1 caller) (.bind 4 (.integer 99))
    apply FrameRel.bind (fuel := 1) (raw := .variable 1) rfl
    · exact .binding .integer (by simpa [Code.subst] using
        (EnvCloses.empty (graph := lexicalClosure) (owners := []) (heap := [])
          (code := .lambda 4 (.integer 99))))
    · simp [ClosedExcept, Code.dependencies]
  · exact .nil

private theorem outer_stack : OrdinaryStackRel lexicalClosure [] [] outerFrames innerPair .none
    nestedPair .none targetStack := by
  have related : PlainFrameRel lexicalClosure [] [] (.tupleRight (.integer 99)) outerPairPlain :=
    FrameRel.tupleRight ValueRel.integer
  have closed : ClosedValue innerPair :=
    (ValueRel.location (graph := lexicalClosure) (owners := [])
      (heap := [.pair (.integer 17) .unit]) (index := 0) rfl ValueRel.integer ValueRel.unit).closed
  exact ordinary_prepend related closed (pushed_only lexical_tail) Execution.Scope.none

private theorem all_stack : OrdinaryStackRel lexicalClosure [] [] allFrames .unit .none
    nestedPair .none targetStack :=
  ordinary_prepend (plain := innerPairPlain) (FrameRel.tupleRight ValueRel.integer)
    (ValueRel.unit (graph := lexicalClosure) (owners := []) (heap := [])).closed
    outer_stack Execution.Scope.none

/-- The supplied state has two ready flattened tuple frames and a pushed bind
whose suffix closes under saved caller 99. Actual Unit entry preserves the
entire identical nested-pair target through the mixed stack. -/
theorem nested_value_entry : TransportWitness lexicalClosure [] evaluating returned target := by
  obtain ⟨witness, translated⟩ := CoreAdministrativeSteps.unit_evaluate
    (base := base) (graph := lexicalClosure) (owners := []) (index := 4)
    (node := ⟨4, .unit, [], none, .unit⟩) rfl rfl
    (EnvCloses.binding ValueRel.integer EnvCloses.empty) allFrames
  exact value_entry witness rfl all_stack

/-- First allocation consumes only the inner tuple frame; the outer tuple
frame stays flattened, with the same pushed lexical continuation. -/
theorem nested_first_allocation : TransportWitness lexicalClosure [] returned allocated target :=
  tuple_allocation (base := returned) ValueRel.integer ValueRel.unit
    innerPairPlain rfl outer_stack Execution.Scope.none

/-- The location actually produced by the first allocation is the right
operand of the second. Heap weakening retains the saved lexical continuation. -/
theorem nested_second_allocation : TransportWitness lexicalClosure [] allocated nestedAllocated target := by
  have right : ValueRel lexicalClosure [] allocated.heap (.location 0) innerPair :=
    .location rfl .integer .unit
  have tail := lexical_tail.heap_weaken (heap_append [] [.pair (.integer 17) .unit])
  exact tuple_allocation (base := allocated) ValueRel.integer right
    outerPairPlain rfl (pushed_only tail) Execution.Scope.none

end Examples

#print axioms Examples.nested_value_entry
#print axioms Examples.nested_first_allocation
#print axioms Examples.nested_second_allocation

#print axioms ordinary_prepend
#print axioms value_entry_fields
#print axioms value_entry
#print axioms tuple_allocation
#print axioms unchanged_transport_rejected
end Ash.OneShot.CoreAdministrativeTransport
