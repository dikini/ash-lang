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
  exact ⟨(owners, core) :: flatPrefix, suffix, by simpa [uniformFrames] using congrArg ((owners, core) :: ·) split, .cons frame ready flattened, pushed⟩

/-- Exact allowed-family guard and strict common potential preclude generic
unchanged-target progress. Both interpretations share the same configuration. -/
structure TransportMapped (graph : CoreSyntax.Graph)
    (beforeOwners afterOwners : CoreTranslation.OwnerMap) (beforeMaps afterMaps : List MappedFrame)
    (before after : CoreMachine.State) (target : Configuration) : Prop where
  permitted : CoreAdministrativeSteps.ready graph before = true
  core : CoreMachine.next graph before = .stepped after
  decreasing : potential graph after < potential graph before
  current : ComponentMapped graph beforeOwners beforeMaps before target
  successor : ComponentMapped graph afterOwners afterMaps after target

abbrev TransportWitness (graph : CoreSyntax.Graph) (owners : CoreTranslation.OwnerMap)
    (before after : CoreMachine.State) (target : Configuration) : Prop :=
  TransportMapped graph owners owners (uniformFrames owners before.frames)
    (uniformFrames owners after.frames) before after target

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
    component_uniform ⟨code, scope, current, stack⟩,
    component_uniform ⟨code, scope, by rw [returned]; exact .returned related, successorStack⟩⟩

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
    component_uniform ⟨rightCode, runtimeScope, .returned right, beforeStack⟩,
    component_uniform ⟨.pair leftCode rightCode, plain.scope, by rw [control]; exact .returned related, afterStack⟩⟩

/-- Same current witness, arbitrary explicit frame annotations, and no future
interpretation input. The current code map and every saved frame map persist. -/
theorem value_entry_mapped
    (witness : ValueWitness graph owners before after code)
    (evaluating : before.control = .evaluate index environment)
    (shape : before.frames = framesOf annotations)
    (stack : OrdinaryWithMaps graph before.heap annotations code scope result resultScope target) :
    TransportMapped graph owners owners annotations annotations before after ⟨result, resultScope, target⟩ := by
  obtain ⟨heap, frames⟩ := value_entry_fields witness evaluating
  have current : ControlRel graph owners before.heap before.control code := by
    cases witness.current with
    | evaluate control translated saved closed => rw [control]; exact .evaluate translated saved
    | tuple control frames left right => rw [evaluating] at control; cases control
  obtain ⟨value, returned, related⟩ := witness.returned
  have afterStack : OrdinaryWithMaps graph after.heap annotations code scope result resultScope target := by
    rw [heap]; exact stack
  exact ⟨witness.permitted, witness.core, administrative_potential witness,
    ⟨shape, code, scope, current, stack⟩,
    ⟨frames.trans shape, code, scope, by rw [returned]; exact .returned related, afterStack⟩⟩

theorem tuple_allocation_mapped {base : CoreMachine.State}
    (left : ValueRel graph owners base.heap leftValue leftCode)
    (right : ValueRel graph owners base.heap rightValue rightCode)
    (plain : PlainData) (context : plain.context = .pairRight leftCode)
    (stack : OrdinaryWithMaps graph base.heap annotations (.pair leftCode rightCode) plain.scope
      result resultScope target) (runtimeScope : Scope) (frameOwners : CoreTranslation.OwnerMap) :
    TransportMapped graph owners owners ((frameOwners, .tupleRight leftValue) :: annotations) annotations
      { base with control := .returned rightValue, frames := .tupleRight leftValue :: framesOf annotations }
      { base with control := .returned (.location base.heap.length), frames := framesOf annotations, heap := base.heap ++ [.pair leftValue rightValue] }
      ⟨result, resultScope, target⟩ := by
  obtain ⟨witness, extension, values, environments⟩ := CoreAdministrativeSteps.tuple_allocate left right (framesOf annotations)
  have frame : PlainFrameRel graph frameOwners base.heap (.tupleRight leftValue) plain := by
    change FrameRel graph frameOwners base.heap _ plain.context
    rw [context]; exact .tupleRight (left.owner_transport frameOwners)
  have tail : OrdinaryWithMaps graph base.heap annotations (plain.context.plug rightCode) plain.scope
      result resultScope target := by simpa only [context, Context.plug] using stack
  have beforeStack := prepend_mapped frame right.closed tail runtimeScope
  obtain ⟨value, control, related⟩ := witness.returned
  exact ⟨witness.permitted, witness.core, administrative_potential witness,
    ⟨rfl, rightCode, runtimeScope, .returned right, beforeStack⟩,
    ⟨rfl, .pair leftCode rightCode, plain.scope, by rw [control]; exact .returned related, stack.heap_weaken extension⟩⟩

/-- A connected ordinary path. Beta enters the callable empty-map boundary;
its actual integer entry shares the identical target, then the caller bind
restores its explicitly saved map and supplied scope. Older annotations persist.
This is a component path, not a reachable-state or PlainData authentication claim. -/
theorem beta_admin_caller_bind {base : CoreMachine.State}
    (function : ValueRel graph codeOwners base.heap (.closure parameter body captured)
      (.lambda parameter (.integer integer)))
    (argument : ValueRel graph codeOwners base.heap value argumentCode)
    (known : graph.node body = some node) (kind : node.kind = .integer integer)
    (translated : CoreTranslation.translateFuel graph fuel savedOwners continuation = .ok rawSuffix)
    (saved : EnvCloses graph savedOwners base.heap caller
      (.lambda binder rawSuffix) (.lambda binder suffix))
    (ready : ClosedExcept binder suffix)
    (applyPlain bindPlain : PlainData)
    (applyContext : applyPlain.context = .appArgument (.lambda parameter (.integer integer)))
    (bindContext : bindPlain.context = .bind binder suffix)
    (older : PushedWithMaps graph base.heap annotations target)
    (runtimeScope : Scope) (applyOwners : CoreTranslation.OwnerMap) :
    let callerMaps := (savedOwners, CoreMachine.Frame.bind binder continuation caller) :: annotations
    let entered := { base with control := .evaluate body (.binding parameter value captured), frames := framesOf callerMaps }
    let returned := { entered with control := .returned (.integer integer), observations := base.observations ++ [.entered body] }
    let finished := { returned with control := .evaluate continuation (.binding binder (.integer integer) caller), frames := framesOf annotations }
    let bodyTarget : Configuration := ⟨.integer integer, .none, .push (.plain bindPlain) target⟩
    ComponentMapped graph codeOwners ((applyOwners, .applyArgument (.closure parameter body captured)) :: callerMaps)
      { base with control := .returned value, frames := .applyArgument (.closure parameter body captured) :: framesOf callerMaps }
      ⟨.app (.lambda parameter (.integer integer)) argumentCode, applyPlain.scope, bodyTarget.stack⟩ ∧
    CoreMachine.next graph { base with control := .returned value, frames := .applyArgument (.closure parameter body captured) :: framesOf callerMaps } = .stepped entered ∧
    RawStep ⟨.app (.lambda parameter (.integer integer)) argumentCode, applyPlain.scope, bodyTarget.stack⟩ bodyTarget [] [] ∧
    TransportMapped graph [] [] callerMaps callerMaps entered returned bodyTarget ∧
    CoreMachine.next graph returned = .stepped finished ∧
    RawStep bodyTarget ⟨.bind binder (.integer integer) suffix, bindPlain.scope, target⟩ [] [] ∧
    RawStep ⟨.bind binder (.integer integer) suffix, bindPlain.scope, target⟩
      ⟨suffix.subst binder (.integer integer), bindPlain.scope, target⟩ [] [] ∧
    ComponentMapped graph savedOwners annotations finished
      ⟨suffix.subst binder (.integer integer), bindPlain.scope, target⟩ := by
  dsimp only
  have callerFrame : PlainFrameRel graph savedOwners base.heap (.bind binder continuation caller) bindPlain := by
    change FrameRel graph savedOwners base.heap _ bindPlain.context
    rw [bindContext]; exact .bind translated saved ready
  have callerTail := PushedWithMaps.cons callerFrame older
  obtain ⟨before, betaNext, betaStep, betaAfter⟩ := beta_complete_mapped function argument
    applyPlain applyContext callerTail runtimeScope applyOwners
  obtain ⟨bodyFuel, rawBody, bodyTranslation, next, step, bodyClosed, original⟩ :=
    CoreStrictSteps.application_complete function argument
      (framesOf ((savedOwners, .bind binder continuation caller) :: annotations))
      applyPlain.scope (.push (.plain bindPlain) target)
  have rawEq : rawBody = .integer integer := by
    cases bodyFuel with
    | zero => simp [CoreTranslation.translateFuel] at bodyTranslation
    | succ remaining =>
      cases node with
      | mk original type effects source nodeKind =>
        cases kind
        simp only [CoreTranslation.translateFuel, CoreTranslation.requireNode, known] at bodyTranslation
        cases bodyTranslation; rfl
  have exactClosed : EnvCloses graph [] base.heap (.binding parameter value captured)
      (.integer integer) (.integer integer) := by
    simpa only [rawEq, Code.subst] using bodyClosed
  obtain ⟨entry, entryTranslation⟩ := CoreAdministrativeSteps.integer_evaluate
    (base := { base with control := .evaluate body (.binding parameter value captured), frames := framesOf ((savedOwners, .bind binder continuation caller) :: annotations) })
    known kind exactClosed (framesOf ((savedOwners, .bind binder continuation caller) :: annotations))
  have transport := value_entry_mapped entry rfl rfl (pushed_mapped (scope := Execution.Scope.none) callerTail)
  obtain ⟨returnBefore, returnNext, plug, bind, returnAfter⟩ := bind_return_mapped
    (base := { base with control := .returned (.integer integer), frames := framesOf ((savedOwners, .bind binder continuation caller) :: annotations), observations := base.observations ++ [.entered body] })
    translated saved ready (ValueRel.integer (owners := [])) bindPlain bindContext older Execution.Scope.none
  exact ⟨before, betaNext, by simpa only [Code.subst] using betaStep,
    transport, returnNext, plug, bind, returnAfter⟩

#print axioms beta_admin_caller_bind

#print axioms value_entry_mapped
#print axioms tuple_allocation_mapped

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
