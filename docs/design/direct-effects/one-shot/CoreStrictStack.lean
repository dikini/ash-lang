import CoreStrictFrames
import CoreEffectFrames
import CoreCleanupFrames

/-! Bounded ordinary-stack components for TASK-0032.
Only a contiguous inner prefix may be flattened. Each flattened hole must be
closed and value-ready; plugging app/bind/branch produces a non-value, so such
a frame terminates that prefix. This is not generic reachable-stack coverage.
Pushed frames carry explicit PlainData scopes and annotations. Authentication
against Core validation remains a static obligation. Captured owners, running cleanup,
and discard have no relation constructors; exact armed cleanup, handler/cell boundaries and
resource initializers are explicit constructors, never opaque related suffixes.
No full simulation theorem or future configuration validity is assumed. -/
namespace Ash.OneShot.CoreStrictStack
open ScopedExpressions ScopedExecution CoreValueRelation CoreStrictFrames CoreEffectFrames CoreCleanupFrames

abbrev MappedFrame := CoreTranslation.OwnerMap × CoreMachine.Frame

def uniformFrames (owners : CoreTranslation.OwnerMap) (frames : List CoreMachine.Frame) : List MappedFrame :=
  frames.map (fun frame => (owners, frame))
def framesOf (frames : List MappedFrame) : List CoreMachine.Frame := frames.map Prod.snd

@[simp] theorem framesOf_uniform (owners : CoreTranslation.OwnerMap) (frames : List CoreMachine.Frame) :
    framesOf (uniformFrames owners frames) = frames := by
  simp [framesOf, uniformFrames, List.map_map, Function.comp_def]
@[simp] theorem framesOf_cons (map : CoreTranslation.OwnerMap) (frame : CoreMachine.Frame) (tail : List MappedFrame) :
    framesOf ((map, frame) :: tail) = frame :: framesOf tail := rfl

inductive PushedWithMaps (graph : CoreSyntax.Graph) (heap : Heap) : List MappedFrame → Stack → Prop where
  | nil : PushedWithMaps graph heap [] .nil
  | cons (frame : PlainFrameRel graph owners heap core plain)
      (tail : PushedWithMaps graph heap cores target) :
      PushedWithMaps graph heap ((owners, core) :: cores) (.push (.plain plain) target)
  | initializer (frame : InitializerRel graph owners heap core plain)
      (tail : PushedWithMaps graph heap cores target) :
      PushedWithMaps graph heap ((owners, core) :: cores) (.push (.plain plain) target)
  | boundary (frame : BoundaryRel graph owners heap core effectFrame)
      (tail : PushedWithMaps graph heap cores target) :
      PushedWithMaps graph heap ((owners, core) :: cores) (.push effectFrame target)
  | cleanup (frame : CleanupRel graph owners heap core data)
      (tail : PushedWithMaps graph heap cores target) :
      PushedWithMaps graph heap ((owners, core) :: cores) (.push (.armed data) target)

inductive FlattenedWithMaps (graph : CoreSyntax.Graph) (heap : Heap) :
    List MappedFrame → Code → Scope → Code → Scope → Prop where
  | nil : FlattenedWithMaps graph heap [] code scope code scope
  | cons (frame : PlainFrameRel graph owners heap core plain)
      (ready : ClosedValue code)
      (tail : FlattenedWithMaps graph heap cores (plain.context.plug code) plain.scope result resultScope) :
      FlattenedWithMaps graph heap ((owners, core) :: cores) code scope result resultScope
  | initializer (frame : InitializerRel graph owners heap core plain)
      (ready : ClosedValue code)
      (tail : FlattenedWithMaps graph heap cores (plain.context.plug code) plain.scope result resultScope) :
      FlattenedWithMaps graph heap ((owners, core) :: cores) code scope result resultScope

abbrev PushedRel (graph : CoreSyntax.Graph) (owners : CoreTranslation.OwnerMap) (heap : Heap)
    (cores : List CoreMachine.Frame) (target : Stack) : Prop :=
  PushedWithMaps graph heap (uniformFrames owners cores) target
abbrev FlattenedRel (graph : CoreSyntax.Graph) (owners : CoreTranslation.OwnerMap) (heap : Heap)
    (cores : List CoreMachine.Frame) (code : Code) (scope : Scope) (result : Code) (resultScope : Scope) : Prop :=
  FlattenedWithMaps graph heap (uniformFrames owners cores) code scope result resultScope

theorem PushedRel.nil : PushedRel graph owners heap [] .nil := PushedWithMaps.nil

theorem PushedRel.cons (frame : PlainFrameRel graph owners heap core plain)
    (tail : PushedRel graph owners heap cores target) :
    PushedRel graph owners heap (core :: cores) (.push (.plain plain) target) :=
  PushedWithMaps.cons frame tail

def OrdinaryWithMaps (graph : CoreSyntax.Graph) (heap : Heap) (cores : List MappedFrame)
    (code : Code) (scope : Scope) (result : Code) (resultScope : Scope) (target : Stack) : Prop :=
  ∃ flatPrefix suffix, cores = flatPrefix ++ suffix ∧
    FlattenedWithMaps graph heap flatPrefix code scope result resultScope ∧
    PushedWithMaps graph heap suffix target

abbrev OrdinaryStackRel (graph : CoreSyntax.Graph) (owners : CoreTranslation.OwnerMap)
    (heap : Heap) (cores : List CoreMachine.Frame) (code : Code) (scope : Scope)
    (result : Code) (resultScope : Scope) (target : Stack) : Prop :=
  OrdinaryWithMaps graph heap (uniformFrames owners cores) code scope result resultScope target

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

/-- The earlier component is the uniform diagonal case. ComponentMapped below
records supplied individual frame maps; reachable-map authentication stays open. -/
abbrev ComponentRel (graph : CoreSyntax.Graph) (owners : CoreTranslation.OwnerMap)
    (state : CoreMachine.State) (target : Configuration) : Prop :=
  ComponentWithMaps graph owners owners state target

theorem PushedWithMaps.heap_weaken (related : PushedWithMaps graph heap cores target)
    (extension : HeapExtends heap larger) : PushedWithMaps graph larger cores target := by
  induction related with
  | nil => exact .nil
  | cons frame tail ih => exact .cons (PlainFrameRel.heap_weaken frame extension) ih
  | initializer frame tail ih => exact .initializer (InitializerRel.heap_weaken frame extension) ih
  | boundary frame tail ih => exact .boundary (BoundaryRel.heap_weaken frame extension) ih
  | cleanup frame tail ih => exact .cleanup (CleanupRel.heap_weaken frame extension) ih

theorem FlattenedWithMaps.heap_weaken
    (related : FlattenedWithMaps graph heap cores code scope result resultScope)
    (extension : HeapExtends heap larger) : FlattenedWithMaps graph larger cores code scope result resultScope := by
  induction related with
  | nil => exact .nil
  | cons frame ready tail ih => exact .cons (PlainFrameRel.heap_weaken frame extension) ready ih
  | initializer frame ready tail ih => exact .initializer (InitializerRel.heap_weaken frame extension) ready ih

theorem PushedRel.heap_weaken (related : PushedRel graph owners heap cores target)
    (extension : HeapExtends heap larger) : PushedRel graph owners larger cores target :=
  PushedWithMaps.heap_weaken related extension

theorem FlattenedRel.heap_weaken (related : FlattenedRel graph owners heap cores code scope result resultScope)
    (extension : HeapExtends heap larger) : FlattenedRel graph owners larger cores code scope result resultScope :=
  FlattenedWithMaps.heap_weaken related extension

theorem OrdinaryStackRel.heap_weaken
    (related : OrdinaryStackRel graph owners heap cores code scope result resultScope target)
    (extension : HeapExtends heap larger) :
    OrdinaryStackRel graph owners larger cores code scope result resultScope target := by
  obtain ⟨flatPrefix, suffix, split, flattened, pushed⟩ := related
  exact ⟨flatPrefix, suffix, split, flattened.heap_weaken extension, pushed.heap_weaken extension⟩

theorem pushed_only (related : PushedRel graph owners heap cores target) :
    OrdinaryStackRel graph owners heap cores code scope code scope target :=
  ⟨[], uniformFrames owners cores, rfl, .nil, related⟩

/-- Flattening is structural reconstruction of one positive plug transition,
not a zero-step execution rule. The runtime scope is explicit. -/
theorem flatten_one (frame : PlainFrameRel graph owners heap core plain)
    (value : ValueRel graph owners heap coreValue code)
    (tail : PushedRel graph owners heap cores target) (scope : Scope) :
    OrdinaryStackRel graph owners heap (core :: cores) code scope
      (plain.context.plug code) plain.scope target ∧
    RawStep ⟨code, scope, .push (.plain plain) target⟩
      ⟨plain.context.plug code, plain.scope, target⟩ [] [] :=
  ⟨⟨[(owners, core)], uniformFrames owners cores, rfl, .cons frame value.closed .nil, tail⟩,
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

/-- Explicit supplied per-frame annotations. Full reachable-site authentication
is separate; no maps are chosen existentially by this component predicate. -/
def ComponentMapped (graph : CoreSyntax.Graph) (codeOwners : CoreTranslation.OwnerMap)
    (annotations : List MappedFrame) (state : CoreMachine.State) (target : Configuration) : Prop :=
  state.frames = framesOf annotations ∧ ∃ code scope,
    ControlRel graph codeOwners state.heap state.control code ∧
    OrdinaryWithMaps graph state.heap annotations code scope target.expression target.scope target.stack

theorem OrdinaryWithMaps.heap_weaken
    (related : OrdinaryWithMaps graph heap cores code scope result resultScope target)
    (extension : HeapExtends heap larger) : OrdinaryWithMaps graph larger cores code scope result resultScope target := by
  obtain ⟨flatPrefix, suffix, split, flattened, pushed⟩ := related
  exact ⟨flatPrefix, suffix, split, flattened.heap_weaken extension, pushed.heap_weaken extension⟩

theorem ordinary_uniform
    (related : OrdinaryStackRel graph owners heap cores code scope result resultScope target) :
    OrdinaryWithMaps graph heap (uniformFrames owners cores) code scope result resultScope target := related

theorem component_uniform (related : ComponentWithMaps graph codeOwners frameOwners state target) :
    ComponentMapped graph codeOwners (uniformFrames frameOwners state.frames) state target := by
  obtain ⟨code, scope, control, stack⟩ := related
  exact ⟨by simp, code, scope, control, ordinary_uniform stack⟩

theorem pushed_mapped (tail : PushedWithMaps graph heap cores target) :
    OrdinaryWithMaps graph heap cores code scope code scope target := ⟨[], cores, rfl, .nil, tail⟩

theorem prepend_mapped (frame : PlainFrameRel graph owners heap core plain)
    (ready : ClosedValue code)
    (tail : OrdinaryWithMaps graph heap cores (plain.context.plug code) plain.scope result resultScope target)
    (scope : Scope) :
    OrdinaryWithMaps graph heap ((owners, core) :: cores) code scope result resultScope target := by
  obtain ⟨flatPrefix, suffix, split, flattened, pushed⟩ := tail
  exact ⟨(owners, core) :: flatPrefix, suffix, by simp [split], .cons frame ready flattened, pushed⟩

/-- Prepend the exact resource initializer to the same mixed reconstruction;
closed readiness permits only this named flattened resource family. -/
theorem prepend_initializer (frame : InitializerRel graph owners heap core plain)
    (ready : ClosedValue code)
    (tail : OrdinaryWithMaps graph heap annotations (plain.context.plug code) plain.scope result resultScope target)
    (runtimeScope : Scope) :
    OrdinaryWithMaps graph heap ((owners, core) :: annotations) code runtimeScope result resultScope target := by
  obtain ⟨flatPrefix, suffix, split, flattened, pushed⟩ := tail
  exact ⟨(owners, core) :: flatPrefix, suffix, congrArg ((owners, core) :: ·) split,
    .initializer frame ready flattened, pushed⟩

#print axioms prepend_initializer

theorem beta_complete_mapped {base : CoreMachine.State}
    (function : ValueRel graph codeOwners base.heap (.closure parameter body saved) (.lambda parameter result))
    (argument : ValueRel graph codeOwners base.heap value argumentCode)
    (plain : PlainData) (context : plain.context = .appArgument (.lambda parameter result))
    (tail : PushedWithMaps graph base.heap annotations target) (runtimeScope : Scope)
    (frameOwners : CoreTranslation.OwnerMap) :
    ComponentMapped graph codeOwners ((frameOwners, .applyArgument (.closure parameter body saved)) :: annotations)
      { base with control := .returned value, frames := .applyArgument (.closure parameter body saved) :: framesOf annotations }
      ⟨.app (.lambda parameter result) argumentCode, plain.scope, target⟩ ∧
    CoreMachine.next graph { base with control := .returned value, frames := .applyArgument (.closure parameter body saved) :: framesOf annotations } =
      .stepped { base with control := .evaluate body (.binding parameter value saved), frames := framesOf annotations } ∧
    RawStep ⟨.app (.lambda parameter result) argumentCode, plain.scope, target⟩
      ⟨result.subst parameter argumentCode, .none, target⟩ [] [] ∧
    ComponentMapped graph [] annotations
      { base with control := .evaluate body (.binding parameter value saved), frames := framesOf annotations }
      ⟨result.subst parameter argumentCode, .none, target⟩ := by
  obtain ⟨fuel, raw, translated, next, step, closed, original⟩ :=
    CoreStrictSteps.application_complete function argument (framesOf annotations) plain.scope target
  have frame : PlainFrameRel graph frameOwners base.heap (.applyArgument (.closure parameter body saved)) plain := by
    change FrameRel graph frameOwners base.heap _ plain.context
    rw [context]; exact .applyArgument (function.owner_transport frameOwners)
  have stack := prepend_mapped frame argument.closed (pushed_mapped tail) runtimeScope
  simp only [context, Context.plug] at stack
  exact ⟨⟨rfl, argumentCode, runtimeScope, .returned argument, stack⟩, next, step,
    ⟨rfl, _, .none, .evaluate translated closed, pushed_mapped tail⟩⟩

/-- Completed caller bind restores that frame's saved lexical map and scope,
with two actual positive target transitions and unchanged older annotations. -/
theorem bind_return_mapped {base : CoreMachine.State}
    (translated : CoreTranslation.translateFuel graph fuel savedOwners body = .ok rawBody)
    (saved : EnvCloses graph savedOwners base.heap environment (.lambda parameter rawBody) (.lambda parameter suffix))
    (ready : ClosedExcept parameter suffix)
    (argument : ValueRel graph codeOwners base.heap value argumentCode)
    (plain : PlainData) (context : plain.context = .bind parameter suffix)
    (tail : PushedWithMaps graph base.heap annotations target) (runtimeScope : Scope) :
    ComponentMapped graph codeOwners ((savedOwners, .bind parameter body environment) :: annotations)
      { base with control := .returned value, frames := .bind parameter body environment :: framesOf annotations }
      ⟨argumentCode, runtimeScope, .push (.plain plain) target⟩ ∧
    CoreMachine.next graph { base with control := .returned value, frames := .bind parameter body environment :: framesOf annotations } =
      .stepped { base with control := .evaluate body (.binding parameter value environment), frames := framesOf annotations } ∧
    RawStep ⟨argumentCode, runtimeScope, .push (.plain plain) target⟩
      ⟨.bind parameter argumentCode suffix, plain.scope, target⟩ [] [] ∧
    RawStep ⟨.bind parameter argumentCode suffix, plain.scope, target⟩
      ⟨suffix.subst parameter argumentCode, plain.scope, target⟩ [] [] ∧
    ComponentMapped graph savedOwners annotations
      { base with control := .evaluate body (.binding parameter value environment), frames := framesOf annotations }
      ⟨suffix.subst parameter argumentCode, plain.scope, target⟩ := by
  obtain ⟨next, bind, closed, sourceTranslated⟩ := CoreStrictSteps.bind_complete translated saved
    (argument.owner_transport savedOwners) ready (framesOf annotations) plain.scope target
  have frame : PlainFrameRel graph savedOwners base.heap (.bind parameter body environment) plain := by
    change FrameRel graph savedOwners base.heap _ plain.context
    rw [context]; exact .bind translated saved ready
  have plug := RawStep.plug plain argumentCode argument.closed runtimeScope target
  simp only [context, Context.plug] at plug
  exact ⟨⟨rfl, argumentCode, runtimeScope, .returned argument, pushed_mapped (.cons frame tail)⟩,
    next, plug, bind, ⟨rfl, _, plain.scope, .evaluate translated closed, pushed_mapped tail⟩⟩

#print axioms bind_return_mapped

#print axioms component_uniform
#print axioms beta_complete_mapped

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
  | initializer frame ready tail => cases frame
  | cons frame ready tail =>
    rename_i plain
    have notValue : ¬ (plain.context.plug argument).IsValue := by
      change FrameRel graph owners heap (.applyArgument function) plain.context at frame
      generalize contextEq : plain.context = context at frame
      cases frame with
      | applyArgument value => simp [Context.plug, Code.IsValue]
    cases tail with
    | cons nextFrame nextReady remaining => exact notValue nextReady.1
    | initializer nextFrame nextReady remaining => exact notValue nextReady.1


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
