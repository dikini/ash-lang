import CoreValueRelation

/-! Bounded administrative value and tuple-allocation components for TASK-0032.
Only literal, lexical variable (including cell-handle variable), lambda entry
and completed binary tuple allocation may keep the target value unchanged.
Every such Core step strictly decreases the explicit local rank below.
Unsupported nodes and malformed lookups have no successful witness.

These are redex components, not a whole configuration simulation. Tails remain
explicit and unchanged. Initial translation/closedness, reachable heap and
resource freshness evidence remain separate static/runtime obligations. Ghost
Core node entries do not assert equality with Rust's effect trace. -/
namespace Ash.OneShot.CoreAdministrativeSteps
open ScopedExpressions CoreValueRelation

/-- Exactly the evaluated node families whose target is already a value. -/
def valueKind : CoreSyntax.Kind → Bool
  | .unit | .boolean _ | .integer _ | .variable _ | .function _ _ => true
  | _ => false

/-- Tuple allocation is included separately from evaluation of value nodes. -/
def ready (graph : CoreSyntax.Graph) (state : CoreMachine.State) : Bool :=
  match state.control with
  | .evaluate index _ => match graph.node index with
      | some node => valueKind node.kind
      | none => false
  | .returned _ => match state.frames with
      | .tupleRight _ :: _ => true
      | _ => false
  | .discard _ _ => false

/-- A value-node entry removes one evaluation bonus. Tuple allocation removes
    one frame. Other transitions have no permission to use this measure as an
    unrestricted zero-step match. -/
def rank (graph : CoreSyntax.Graph) (state : CoreMachine.State) : Nat :=
  state.frames.length + match state.control with
    | .evaluate index _ => match graph.node index with
        | some node => if valueKind node.kind then 1 else 0
        | none => 0
    | _ => 0

/-- Current value interpretation, independently of any future Core step.
    Tuple completion represents the pending pair from its actual two operands. -/
inductive BeforeValue (graph : CoreSyntax.Graph) (owners : CoreTranslation.OwnerMap)
    (before : CoreMachine.State) : Code → Prop where
  | evaluate (control : before.control = .evaluate index saved)
      (translated : CoreTranslation.translateFuel graph fuel owners index = .ok raw)
      (environment : EnvCloses graph owners before.heap saved raw target)
      (closed : ClosedValue target) : BeforeValue graph owners before target
  | tuple (control : before.control = .returned right)
      (frames : before.frames = .tupleRight left :: tail)
      (leftRelated : ValueRel graph owners before.heap left leftCode)
      (rightRelated : ValueRel graph owners before.heap right rightCode) :
      BeforeValue graph owners before (.pair leftCode rightCode)

/-- The target value is the same parameter before and after this administrative
    component. A concrete source step, family check and decrease are required. -/
structure ValueWitness (graph : CoreSyntax.Graph) (owners : CoreTranslation.OwnerMap)
    (before after : CoreMachine.State) (target : Code) : Prop where
  core : CoreMachine.next graph before = .stepped after
  permitted : ready graph before = true
  current : BeforeValue graph owners before target
  returned : ∃ value, after.control = .returned value ∧ ValueRel graph owners after.heap value target
  decreasing : rank graph after < rank graph before

private theorem entry_ready
    (known : graph.node index = some node) (kind : valueKind node.kind = true)
    (base : CoreMachine.State) (saved : MEnv) (tail : List CoreMachine.Frame) :
    ready graph { base with control := .evaluate index saved, frames := tail } = true := by
  simp [ready, known, kind]

private theorem entry_decreases
    (known : graph.node index = some node) (kind : valueKind node.kind = true)
    (base : CoreMachine.State) (saved : MEnv) (value : MValue) (tail : List CoreMachine.Frame) :
    rank graph { base with control := .returned value, frames := tail, observations := base.observations ++ [.entered index] } <
      rank graph { base with control := .evaluate index saved, frames := tail } := by
  simp [rank, known, kind]

/-- Unit interpretation closes to Unit under every related lexical environment. -/
theorem unit_evaluate {base : CoreMachine.State}
    (known : graph.node index = some node) (kind : node.kind = .unit)
    (environment : EnvCloses graph owners base.heap saved .unit target)
    (tail : List CoreMachine.Frame) :
    ValueWitness graph owners
      { base with control := .evaluate index saved, frames := tail }
      { base with control := .returned .unit, frames := tail, observations := base.observations ++ [.entered index] } target ∧
    CoreTranslation.translateFuel graph 1 owners index = .ok .unit := by
  have closed : ClosedValue Code.unit := (ValueRel.unit (graph := graph) (owners := owners) (heap := base.heap)).closed
  have equal := environment.closed_identity closed
  have translation : CoreTranslation.translateFuel graph 1 owners index = .ok Code.unit := by
    cases node with
    | mk original type effects source nodeKind =>
        cases kind
        simp only [CoreTranslation.translateFuel, CoreTranslation.requireNode, known]
        rfl
  refine ⟨⟨?_, entry_ready known (by simp [kind, valueKind]) base saved tail, .evaluate rfl translation environment (equal ▸ closed),
    ⟨.unit, rfl, equal ▸ ValueRel.unit⟩,
    entry_decreases known (by simp [kind, valueKind]) base saved .unit tail⟩, translation⟩
  · simp [CoreMachine.next, known, kind]

theorem boolean_evaluate {base : CoreMachine.State}
    (known : graph.node index = some node) (kind : node.kind = .boolean flag)
    (environment : EnvCloses graph owners base.heap saved (.boolean flag) target)
    (tail : List CoreMachine.Frame) :
    ValueWitness graph owners
      { base with control := .evaluate index saved, frames := tail }
      { base with control := .returned (.boolean flag), frames := tail, observations := base.observations ++ [.entered index] } target ∧
    CoreTranslation.translateFuel graph 1 owners index = .ok (.boolean flag) := by
  have closed : ClosedValue (Code.boolean flag) := (ValueRel.boolean (graph := graph)
    (owners := owners) (heap := base.heap) (value := flag)).closed
  have equal := environment.closed_identity closed
  have translation : CoreTranslation.translateFuel graph 1 owners index = .ok (Code.boolean flag) := by
    cases node with
    | mk original type effects source nodeKind =>
        cases kind
        simp only [CoreTranslation.translateFuel, CoreTranslation.requireNode, known]
        rfl
  refine ⟨⟨?_, entry_ready known (by simp [kind, valueKind]) base saved tail, .evaluate rfl translation environment (equal ▸ closed),
    ⟨.boolean flag, rfl, equal ▸ ValueRel.boolean⟩,
    entry_decreases known (by simp [kind, valueKind]) base saved (.boolean flag) tail⟩, translation⟩
  · simp [CoreMachine.next, known, kind]

theorem integer_evaluate {base : CoreMachine.State}
    (known : graph.node index = some node) (kind : node.kind = .integer integer)
    (environment : EnvCloses graph owners base.heap saved (.integer integer) target)
    (tail : List CoreMachine.Frame) :
    ValueWitness graph owners
      { base with control := .evaluate index saved, frames := tail }
      { base with control := .returned (.integer integer), frames := tail, observations := base.observations ++ [.entered index] } target ∧
    CoreTranslation.translateFuel graph 1 owners index = .ok (.integer integer) := by
  have closed : ClosedValue (Code.integer integer) := (ValueRel.integer (graph := graph)
    (owners := owners) (heap := base.heap) (value := integer)).closed
  have equal := environment.closed_identity closed
  have translation : CoreTranslation.translateFuel graph 1 owners index = .ok (Code.integer integer) := by
    cases node with
    | mk original type effects source nodeKind =>
        cases kind
        simp only [CoreTranslation.translateFuel, CoreTranslation.requireNode, known]
        rfl
  refine ⟨⟨?_, entry_ready known (by simp [kind, valueKind]) base saved tail, .evaluate rfl translation environment (equal ▸ closed),
    ⟨.integer integer, rfl, equal ▸ ValueRel.integer⟩,
    entry_decreases known (by simp [kind, valueKind]) base saved (.integer integer) tail⟩, translation⟩
  · simp [CoreMachine.next, known, kind]

/-- Closed lexical interpretation constructs the successful lookup. It does not
    assume that evaluation succeeded or that a future invariant will hold. -/
theorem variable_evaluate {base : CoreMachine.State}
    (known : graph.node index = some node) (kind : node.kind = .variable name)
    (environment : EnvCloses graph owners base.heap saved (.variable name) target)
    (closed : ClosedValue target) (tail : List CoreMachine.Frame) :
    ∃ value, saved.lookup name = some value ∧
      ValueWitness graph owners
        { base with control := .evaluate index saved, frames := tail }
        { base with control := .returned value, frames := tail, observations := base.observations ++ [.entered index] } target ∧
      CoreTranslation.translateFuel graph 1 owners index = .ok (.variable name) := by
  have translation : CoreTranslation.translateFuel graph 1 owners index = .ok (.variable name) := by
    cases node with
    | mk original type effects source nodeKind =>
        cases kind
        simp only [CoreTranslation.translateFuel, CoreTranslation.requireNode, known]
        rfl
  obtain ⟨value, lookup, related⟩ := environment.lookup closed
  refine ⟨value, lookup, ⟨?_, entry_ready known (by simp [kind, valueKind]) base saved tail, .evaluate rfl translation environment closed,
    ⟨value, rfl, related⟩,
    entry_decreases known (by simp [kind, valueKind]) base saved value tail⟩, translation⟩
  · simp [CoreMachine.next, known, kind, lookup]

/-- Lambda entry closes the translated body under its captured environment,
    rather than the later caller's environment. -/
theorem lambda_evaluate {base : CoreMachine.State}
    (known : graph.node index = some node) (kind : node.kind = .function parameter body)
    (translated : CoreTranslation.translateFuel graph fuel owners body = .ok rawBody)
    (callable : CallableCertificate graph parameter.id body rawBody)
    (environment : EnvCloses graph owners base.heap saved (.lambda parameter.id rawBody) target)
    (closed : ClosedValue target) (tail : List CoreMachine.Frame) :
    ValueWitness graph owners
      { base with control := .evaluate index saved, frames := tail }
      { base with control := .returned (.closure parameter.id body saved), frames := tail, observations := base.observations ++ [.entered index] } target ∧
    CoreTranslation.translateFuel graph (fuel + 1) owners index = .ok (.lambda parameter.id rawBody) := by
  have translation : CoreTranslation.translateFuel graph (fuel + 1) owners index =
      .ok (.lambda parameter.id rawBody) := by
    cases node with
    | mk original type effects source nodeKind =>
        cases kind
        simp only [CoreTranslation.translateFuel, CoreTranslation.requireNode, known]
        change (do pure (Code.lambda parameter.id (← CoreTranslation.translateFuel graph fuel owners body))) = _
        rw [translated]
        rfl
  obtain ⟨emptyFuel, emptyTranslation⟩ := callable.emptyTranslation
  refine ⟨⟨?_, entry_ready known (by simp [kind, valueKind]) base saved tail, .evaluate rfl translation environment closed,
    ⟨.closure parameter.id body saved, rfl, .closure emptyTranslation callable (environment.owner_transport []) closed⟩,
    entry_decreases known (by simp [kind, valueKind]) base saved (.closure parameter.id body saved) tail⟩, translation⟩
  · simp [CoreMachine.next, known, kind]

private theorem reference_value
    (related : ValueRel graph owners heap value (.resourceRef (.activation key))) : value = .handle key := by
  cases related with
  | handle => rfl
  | closure translated callable environment closed =>
      obtain ⟨result, impossible⟩ := environment.lambda_shape_at _ _ rfl
      cases impossible

/-- Core has no separate resource-reference graph node. This is the supported
    variable lookup path whose lexical binding is a cell activation handle. -/
theorem resource_reference_evaluate {base : CoreMachine.State}
    (known : graph.node index = some node) (kind : node.kind = .variable name)
    (environment : EnvCloses graph owners base.heap saved (.variable name) (.resourceRef (.activation key)))
    (tail : List CoreMachine.Frame) :
    saved.lookup name = some (.handle key) ∧
      ValueWitness graph owners
        { base with control := .evaluate index saved, frames := tail }
        { base with control := .returned (.handle key), frames := tail, observations := base.observations ++ [.entered index] } (.resourceRef (.activation key)) := by
  have closed := (ValueRel.handle (graph := graph) (owners := owners) (heap := base.heap) (key := key)).closed
  obtain ⟨value, lookup, witness, translated⟩ := variable_evaluate known kind environment closed tail
  obtain ⟨returned, same, related⟩ := witness.returned
  have returnedEqual : returned = value := by simpa using same.symm
  have valueEqual : value = .handle key := returnedEqual ▸ reference_value related
  rw [valueEqual] at lookup witness
  exact ⟨lookup, witness⟩

/-- Completed binary tuple allocation creates the actual fresh heap location.
    Existing related values and environments transport through heap extension. -/
theorem tuple_allocate {base : CoreMachine.State}
    (leftRelated : ValueRel graph owners base.heap left leftCode)
    (rightRelated : ValueRel graph owners base.heap right rightCode)
    (tail : List CoreMachine.Frame) :
    ValueWitness graph owners
      { base with control := .returned right, frames := .tupleRight left :: tail }
      { base with control := .returned (.location base.heap.length), frames := tail, heap := base.heap ++ [.pair left right] } (.pair leftCode rightCode) ∧
    HeapExtends base.heap (base.heap ++ [.pair left right]) ∧
    (∀ value code, ValueRel graph owners base.heap value code →
      ValueRel graph owners (base.heap ++ [.pair left right]) value code) ∧
    (∀ saved code output, EnvCloses graph owners base.heap saved code output →
      EnvCloses graph owners (base.heap ++ [.pair left right]) saved code output) := by
  have extension := heap_append base.heap [.pair left right]
  have atNew : (base.heap ++ [.pair left right])[base.heap.length]? = some (.pair left right) := by
    simp
  exact ⟨⟨rfl, rfl, .tuple rfl rfl leftRelated rightRelated, ⟨.location base.heap.length, rfl,
    .location atNew (leftRelated.heap_weaken extension) (rightRelated.heap_weaken extension)⟩,
    by simp [rank]⟩, extension,
    fun value code related => related.heap_weaken extension,
    fun saved code output related => related.heap_weaken extension⟩

/-- A rejected Core transition never becomes successful administrative progress. -/
theorem rejected_no_witness (rejected : CoreMachine.next graph before = .rejected error) :
    ¬ ValueWitness graph owners before after target := by
  intro witness
  exact CoreMachine.rejected_not_step graph before error rejected after witness.core

/-- Unsupported node kinds are excluded even before considering their failure. -/
theorem unsupported_no_witness
    (control : before.control = .evaluate index saved)
    (known : graph.node index = some node) (kind : node.kind = .unsupported unsupported) :
    ¬ ValueWitness graph owners before after target := by
  intro witness
  have impossible := witness.permitted
  simp [ready, control, known, kind, valueKind] at impossible

namespace Examples
open CoreMachineExamples

private def base : CoreMachine.State := { control := .returned .unit }

/-- The current lexical graph's variable 3 yields the closure capturing 17,
    even though the nearest caller binding for integer variable 1 is 99. -/
theorem lexical_variable (tail : List CoreMachine.Frame) : ∃ value,
    CoreMachine.Environment.lookup
      (.binding 1 (.integer 99) (.binding 3 (.closure 2 1 (.binding 1 (.integer 17) .empty))
        (.binding 1 (.integer 17) .empty))) 3 = some value ∧
    ValueWitness lexicalClosure []
      { base with control := .evaluate 3 (.binding 1 (.integer 99) (.binding 3 (.closure 2 1 (.binding 1 (.integer 17) .empty)) (.binding 1 (.integer 17) .empty))), frames := tail }
      { base with control := .returned value, frames := tail, observations := [.entered 3] }
      (.lambda 2 (.integer 17)) := by
  obtain ⟨value, lookup, witness, translated⟩ := variable_evaluate (base := base) (graph := lexicalClosure)
    (index := 3) (node := ⟨3, .function .unit .integer [], [], none, .variable 3⟩) rfl rfl
    CoreValueRelation.Examples.lexical_lookup CoreValueRelation.Examples.lexical_closure.closed tail
  exact ⟨value, lookup, witness⟩

/-- The completed tuple is related at its new location with an arbitrary tail. -/
theorem tuple_value (tail : List CoreMachine.Frame) :
    ValueWitness tupleGraph []
      { base with control := .returned (.boolean true), frames := .tupleRight (.integer 17) :: tail }
      { base with control := .returned (.location 0), frames := tail, heap := [.pair (.integer 17) (.boolean true)] } (.pair (.integer 17) (.boolean true)) :=
  (tuple_allocate (base := base) (graph := tupleGraph) (owners := []) .integer .boolean tail).1

/-- A malformed missing lexical binding is rejected, not counted as progress. -/
theorem missing_variable_rejected (tail : List CoreMachine.Frame) :
    ¬ ValueWitness lexicalClosure []
      { base with control := .evaluate 1 .empty, frames := tail } after target :=
  rejected_no_witness (error := .missingVariable 1) rfl

end Examples

#print axioms unit_evaluate
#print axioms boolean_evaluate
#print axioms integer_evaluate
#print axioms variable_evaluate
#print axioms lambda_evaluate
#print axioms resource_reference_evaluate
#print axioms tuple_allocate
#print axioms rejected_no_witness
#print axioms unsupported_no_witness
#print axioms Examples.lexical_variable
#print axioms Examples.tuple_value
#print axioms Examples.missing_variable_rejected

end Ash.OneShot.CoreAdministrativeSteps
