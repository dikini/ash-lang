import CoreStrictFrames

/-! Bounded ordinary-stack components for TASK-0032.
Only a contiguous inner prefix may be flattened. Each flattened hole must be
closed and value-ready; plugging app/bind/branch produces a non-value, so such
a frame terminates that prefix. This is not generic reachable-stack coverage.
Pushed frames carry explicit PlainData scopes and annotations. Authentication
against Core validation remains a static obligation. Effects, owners, cleanup,
and discard have no relation constructors; no opaque suffix is called related.
No full simulation theorem or future configuration validity is assumed. -/
namespace Ash.OneShot.CoreStrictStack
open ScopedExpressions ScopedExecution CoreValueRelation CoreStrictFrames

inductive PushedRel (graph : CoreSyntax.Graph) (owners : CoreTranslation.OwnerMap)
    (heap : Heap) : List CoreMachine.Frame → Stack → Prop where
  | nil : PushedRel graph owners heap [] .nil
  | cons (frame : PlainFrameRel graph owners heap core plain)
      (tail : PushedRel graph owners heap cores target) :
      PushedRel graph owners heap (core :: cores) (.push (.plain plain) target)

inductive FlattenedRel (graph : CoreSyntax.Graph) (owners : CoreTranslation.OwnerMap)
    (heap : Heap) : List CoreMachine.Frame → Code → Scope → Code → Scope → Prop where
  | nil : FlattenedRel graph owners heap [] code scope code scope
  | cons (frame : PlainFrameRel graph owners heap core plain)
      (ready : ClosedValue code)
      (tail : FlattenedRel graph owners heap cores (plain.context.plug code) plain.scope result resultScope) :
      FlattenedRel graph owners heap (core :: cores) code scope result resultScope

def OrdinaryStackRel (graph : CoreSyntax.Graph) (owners : CoreTranslation.OwnerMap)
    (heap : Heap) (cores : List CoreMachine.Frame) (code : Code) (scope : Scope)
    (result : Code) (resultScope : Scope) (target : Stack) : Prop :=
  ∃ flatPrefix suffix, cores = flatPrefix ++ suffix ∧
    FlattenedRel graph owners heap flatPrefix code scope result resultScope ∧
    PushedRel graph owners heap suffix target

inductive ControlRel (graph : CoreSyntax.Graph) (owners : CoreTranslation.OwnerMap)
    (heap : Heap) : CoreMachine.Control → Code → Prop where
  | evaluate (translated : CoreTranslation.translateFuel graph fuel owners index = .ok raw)
      (saved : EnvCloses graph owners heap environment raw code) :
      ControlRel graph owners heap (.evaluate index environment) code
  | returned (value : ValueRel graph owners heap core code) :
      ControlRel graph owners heap (.returned core) code

/-- Structural expression/ordinary-stack interpretation only. It does not
assert target Valid, source reachability or annotation authentication. -/
def ComponentWithMaps (graph : CoreSyntax.Graph)
    (codeOwners frameOwners : CoreTranslation.OwnerMap)
    (state : CoreMachine.State) (target : Configuration) : Prop :=
  ∃ code scope, ControlRel graph codeOwners state.heap state.control code ∧
    OrdinaryStackRel graph frameOwners state.heap state.frames code scope
      target.expression target.scope target.stack

/-- The earlier component is the diagonal case. Different saved-frame maps
remain open; this factor records only the callable/current-code boundary. -/
abbrev ComponentRel (graph : CoreSyntax.Graph) (owners : CoreTranslation.OwnerMap)
    (state : CoreMachine.State) (target : Configuration) : Prop :=
  ComponentWithMaps graph owners owners state target

theorem PushedRel.heap_weaken (related : PushedRel graph owners heap cores target)
    (extension : HeapExtends heap larger) : PushedRel graph owners larger cores target := by
  induction related with
  | nil => exact .nil
  | cons frame tail ih => exact .cons (PlainFrameRel.heap_weaken frame extension) ih

theorem FlattenedRel.heap_weaken (related : FlattenedRel graph owners heap cores code scope result resultScope)
    (extension : HeapExtends heap larger) : FlattenedRel graph owners larger cores code scope result resultScope := by
  induction related with
  | nil => exact .nil
  | cons frame ready tail ih => exact .cons (PlainFrameRel.heap_weaken frame extension) ready ih

theorem OrdinaryStackRel.heap_weaken
    (related : OrdinaryStackRel graph owners heap cores code scope result resultScope target)
    (extension : HeapExtends heap larger) :
    OrdinaryStackRel graph owners larger cores code scope result resultScope target := by
  obtain ⟨flatPrefix, suffix, split, flattened, pushed⟩ := related
  exact ⟨flatPrefix, suffix, split, flattened.heap_weaken extension, pushed.heap_weaken extension⟩

theorem pushed_only (related : PushedRel graph owners heap cores target) :
    OrdinaryStackRel graph owners heap cores code scope code scope target :=
  ⟨[], cores, rfl, .nil, related⟩

/-- Flattening is structural reconstruction of one positive plug transition,
not a zero-step execution rule. The runtime scope is explicit. -/
theorem flatten_one (frame : PlainFrameRel graph owners heap core plain)
    (value : ValueRel graph owners heap coreValue code)
    (tail : PushedRel graph owners heap cores target) (scope : Scope) :
    OrdinaryStackRel graph owners heap (core :: cores) code scope
      (plain.context.plug code) plain.scope target ∧
    RawStep ⟨code, scope, .push (.plain plain) target⟩
      ⟨plain.context.plug code, plain.scope, target⟩ [] [] :=
  ⟨⟨[core], cores, rfl, .cons frame value.closed .nil, tail⟩,
    .plug plain code value.closed scope target⟩

/-- A unit entry has one and the same whole target interpretation on both
sides. Its actual ValueWitness supplies permission, current interpretation,
actual next and strict administrative-rank decrease. -/
theorem unit_entry {base : CoreMachine.State}
    (known : graph.node index = some node) (kind : node.kind = .unit)
    (saved : EnvCloses graph owners base.heap environment .unit .unit)
    (stack : OrdinaryStackRel graph owners base.heap cores .unit scope result resultScope target) :
    CoreAdministrativeSteps.ValueWitness graph owners
      { base with control := .evaluate index environment, frames := cores }
      { base with control := .returned .unit, frames := cores, observations := base.observations ++ [.entered index] } .unit ∧
    ComponentRel graph owners { base with control := .evaluate index environment, frames := cores }
      ⟨result, resultScope, target⟩ ∧
    ComponentRel graph owners { base with control := .returned .unit, frames := cores, observations := base.observations ++ [.entered index] }
      ⟨result, resultScope, target⟩ := by
  obtain ⟨witness, translated⟩ := CoreAdministrativeSteps.unit_evaluate known kind saved cores
  exact ⟨witness, ⟨.unit, scope, .evaluate translated saved, stack⟩,
    ⟨.unit, scope, .returned .unit, stack⟩⟩

/-- Completed beta consumes the flattened ready argument frame. Arbitrary
remaining ordinary pushed frames persist; beta resets the current scope to
none, exactly as the existing RawStep does. -/
theorem beta_complete {base : CoreMachine.State}
    (function : ValueRel graph owners base.heap (.closure parameter body saved) (.lambda parameter result))
    (argument : ValueRel graph owners base.heap value argumentCode)
    (plain : PlainData) (context : plain.context = .appArgument (.lambda parameter result))
    (tail : PushedRel graph owners base.heap cores target) (runtimeScope : Scope) :
    ComponentRel graph owners { base with control := .returned value, frames := .applyArgument (.closure parameter body saved) :: cores }
      ⟨.app (.lambda parameter result) argumentCode, plain.scope, target⟩ ∧
    CoreMachine.next graph { base with control := .returned value, frames := .applyArgument (.closure parameter body saved) :: cores } =
      .stepped { base with control := .evaluate body (.binding parameter value saved), frames := cores } ∧
    RawStep ⟨.app (.lambda parameter result) argumentCode, plain.scope, target⟩
      ⟨result.subst parameter argumentCode, .none, target⟩ [] [] ∧
    ComponentWithMaps graph [] owners { base with control := .evaluate body (.binding parameter value saved), frames := cores }
      ⟨result.subst parameter argumentCode, .none, target⟩ := by
  obtain ⟨fuel, raw, translated, next, step, closed, originalArgument⟩ :=
    CoreStrictSteps.application_complete function argument cores plain.scope target
  have frame : PlainFrameRel graph owners base.heap (.applyArgument (.closure parameter body saved)) plain := by
    change FrameRel graph owners base.heap _ plain.context
    rw [context]; exact .applyArgument function
  have stack := (flatten_one frame argument tail runtimeScope).1
  simp only [context, Context.plug] at stack
  exact ⟨⟨argumentCode, runtimeScope, .returned argument, stack⟩, next, step,
    ⟨_, .none, .evaluate translated closed, pushed_only tail⟩⟩

/-- No rank can license an unchanged source state. There is no unrestricted
zero-step constructor in the stack relation or administrative witness. -/
theorem unchanged_rank_rejected (graph : CoreSyntax.Graph) (state : CoreMachine.State) :
    ¬ CoreAdministrativeSteps.rank graph state < CoreAdministrativeSteps.rank graph state :=
  Nat.lt_irrefl _

theorem unchanged_admin_rejected (graph : CoreSyntax.Graph) (owners : CoreTranslation.OwnerMap)
    (state : CoreMachine.State) (code : Code) :
    ¬ CoreAdministrativeSteps.ValueWitness graph owners state state code := by
  intro witness
  exact unchanged_rank_rejected graph state witness.decreasing

/-- An application frame's plugged expression is not a value. Thus no second
frame, including another application or bind, can extend the flattened prefix.
This exact exclusion is a representation discipline. Reachable-state phase
lemmas must establish it; it does not demonstrate a source coverage failure. -/
theorem application_flattening_barrier :
    ¬ FlattenedRel graph owners heap (.applyArgument function :: outer :: rest)
      argument scope result resultScope := by
  intro related
  cases related with
  | cons frame ready tail =>
    rename_i plain
    have notValue : ¬ (plain.context.plug argument).IsValue := by
      change FrameRel graph owners heap (.applyArgument function) plain.context at frame
      generalize contextEq : plain.context = context at frame
      cases frame with
      | applyArgument value => simp [Context.plug, Code.IsValue]
    cases tail with
    | cons nextFrame nextReady remaining => exact notValue nextReady.1


namespace Examples
open CoreMachineExamples
private def base : CoreMachine.State := { control := .returned .unit }
private def caller : MEnv := .binding 1 (.integer 99) .empty
private def closure : MValue := .closure 2 1 (.binding 1 (.integer 17) .empty)
private def outer : PlainData := ⟨.bind 4 (.integer 99), .none, .unit, .unit, [], rfl⟩
private def inner : PlainData := ⟨.appArgument (.lambda 2 (.integer 17)), .none, .unit, .unit, [], rfl⟩
private def cores : List CoreMachine.Frame := [.bind 4 1 caller]
private def targets : Stack := .push (.plain outer) .nil
private def whole : Configuration := ⟨.app (.lambda 2 (.integer 17)) .unit, .none, targets⟩
private def successor : Configuration := ⟨.integer 17, .none, targets⟩
private def before : CoreMachine.State := { base with control := .evaluate 4 caller, frames := .applyArgument closure :: cores }
private def returned : CoreMachine.State := { base with control := .returned .unit, frames := .applyArgument closure :: cores, observations := [.entered 4] }
private def enteredBody : CoreMachine.State := { returned with control := .evaluate 1 (.binding 2 .unit (.binding 1 (.integer 17) .empty)), frames := cores }

private theorem outer_related : PushedRel lexicalClosure [] [] cores targets := by
  apply PushedRel.cons (plain := outer)
  · change FrameRel lexicalClosure [] [] (.bind 4 1 caller) (.bind 4 (.integer 99))
    apply FrameRel.bind (fuel := 1) (raw := .variable 1) rfl
    · exact .binding .integer (by simpa [Code.subst] using
        (EnvCloses.empty (graph := lexicalClosure) (owners := []) (heap := [])
          (code := .lambda 4 (.integer 99))))
    · simp [ClosedExcept, Code.dependencies]
  · exact .nil

/-- Unit entry from the supplied state over the original lexical graph has a flattened application
frame and a pushed outer bind saved under caller 99. Its whole target stays
identical while the administrative rank strictly decreases. -/
theorem lexical_ranked_entry :
    CoreAdministrativeSteps.ValueWitness lexicalClosure [] before returned .unit ∧
    ComponentRel lexicalClosure [] before whole ∧ ComponentRel lexicalClosure [] returned whole := by
  have frame : PlainFrameRel lexicalClosure [] [] (.applyArgument closure) inner :=
    FrameRel.applyArgument CoreValueRelation.Examples.lexical_closure
  have stack := (flatten_one frame (ValueRel.unit (graph := lexicalClosure) (owners := []) (heap := []))
    outer_related Execution.Scope.none).1
  exact unit_entry (base := base) (graph := lexicalClosure) (owners := [])
    (index := 4) (node := ⟨4, .unit, [], none, .unit⟩) rfl rfl
    (EnvCloses.binding ValueRel.integer EnvCloses.empty) stack

/-- The following actual Core completion from the supplied state enters captured 17, restores none
through beta, and preserves the pushed outer frame saved under caller 99. -/
theorem lexical_completed_beta :
    ComponentRel lexicalClosure [] returned whole ∧
    CoreMachine.next lexicalClosure returned = .stepped enteredBody ∧
    RawStep whole successor [] [] ∧ ComponentRel lexicalClosure [] enteredBody successor := by
  exact beta_complete (base := returned) CoreValueRelation.Examples.lexical_closure
    ValueRel.unit inner rfl outer_related Execution.Scope.none

end Examples

#print axioms Examples.lexical_ranked_entry
#print axioms Examples.lexical_completed_beta

#print axioms OrdinaryStackRel.heap_weaken
#print axioms flatten_one
#print axioms unit_entry
#print axioms beta_complete
#print axioms unchanged_admin_rejected
#print axioms application_flattening_barrier
end Ash.OneShot.CoreStrictStack
