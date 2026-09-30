import CoreStrictStack
import CoreTranslationFuel

/-! Finite structural potential for the bounded ordinary administrative slice.
Postorder is static graph descent, not a bound on future execution. Only the
named actual ordinary traversal transitions may use this potential for
unchanged-target progress. No effect transition is authorized by its weight.
Translation, lexical interpretation, closed readiness and PlainData annotation
obligations remain explicit current inputs. No whole simulation is claimed. -/
namespace Ash.OneShot.CoreStrictPotential
open ScopedExpressions ScopedExecution CoreValueRelation CoreStrictFrames CoreStrictStack CoreRequestFrames CoreResumeFrames

/-- Reuse the frozen static postorder condition and checker extraction. -/
abbrev Postorder := CoreTranslationFuel.Postorder

/-- Total even on malformed graphs; static postorder removes every fallback.
The recursion uses a node index, independently of translation/evaluation fuel. -/
def nodeCost (graph : CoreSyntax.Graph) (index : Nat) : Nat :=
  3 + match graph.node index with
    | none => 0
    | some node => (node.kind.children.map fun child =>
        if _lower : child < index then nodeCost graph child else 0).sum
termination_by index

theorem cost_recurrence (ordered : Postorder graph)
    (known : graph.node index = some node) :
    nodeCost graph index = 3 + (node.kind.children.map (nodeCost graph)).sum := by
  rw [nodeCost, known]
  simp only
  congr 2
  apply List.map_congr_left
  intro child member
  simp only [dif_pos (ordered index node known child member)]

def frameWeight (graph : CoreSyntax.Graph) : CoreMachine.Frame → Nat
  | .applyFunction argument _ | .tupleLeft argument _ => nodeCost graph argument + 2
  | .applyArgument _ | .tupleRight _ | .request _ _ _ | .resume _ _ => 1
  | .bind _ body _ | .resourceInitializer _ _ _ body _ => nodeCost graph body + 1
  | .matchCases arms _ => (arms.map fun arm => nodeCost graph arm.body).sum + 1
  | _ => 0

def potential (graph : CoreSyntax.Graph) (state : CoreMachine.State) : Nat :=
  (match state.control with | .evaluate index _ => nodeCost graph index | _ => 0) +
    (state.frames.map (frameWeight graph)).sum

theorem application_entry_decreases {base : CoreMachine.State}
    (ordered : Postorder graph) (known : graph.node site = some node)
    (kind : node.kind = .apply function argument) (tail : List CoreMachine.Frame) :
    CoreMachine.next graph { base with control := .evaluate site environment, frames := tail } =
      .stepped { base with control := .evaluate function environment, frames := .applyFunction argument environment :: tail, observations := base.observations ++ [.entered site] } ∧
    potential graph { base with control := .evaluate function environment, frames := .applyFunction argument environment :: tail, observations := base.observations ++ [.entered site] } <
      potential graph { base with control := .evaluate site environment, frames := tail } := by
  have cost := cost_recurrence ordered known
  simp only [kind, CoreSyntax.Kind.children, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at cost
  refine ⟨?_, ?_⟩
  · cases node with
    | mk original type effects source nodeKind => cases kind; simp only [CoreMachine.next, known]
  · simp only [potential, List.map_cons, List.sum_cons, frameWeight]
    omega

theorem application_argument_decreases (base : CoreMachine.State)
    (tail : List CoreMachine.Frame) :
    CoreMachine.next graph { base with control := .returned function, frames := .applyFunction argument environment :: tail } =
      .stepped { base with control := .evaluate argument environment, frames := .applyArgument function :: tail } ∧
    potential graph { base with control := .evaluate argument environment, frames := .applyArgument function :: tail } <
      potential graph { base with control := .returned function, frames := .applyFunction argument environment :: tail } := by
  refine ⟨rfl, ?_⟩
  simp [potential, frameWeight]
  omega

theorem tuple_entry_decreases {base : CoreMachine.State}
    (ordered : Postorder graph) (known : graph.node site = some node)
    (kind : node.kind = .tuple [left, right]) (tail : List CoreMachine.Frame) :
    CoreMachine.next graph { base with control := .evaluate site environment, frames := tail } =
      .stepped { base with control := .evaluate left environment, frames := .tupleLeft right environment :: tail, observations := base.observations ++ [.entered site] } ∧
    potential graph { base with control := .evaluate left environment, frames := .tupleLeft right environment :: tail, observations := base.observations ++ [.entered site] } <
      potential graph { base with control := .evaluate site environment, frames := tail } := by
  have cost := cost_recurrence ordered known
  simp only [kind, CoreSyntax.Kind.children, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at cost
  refine ⟨?_, ?_⟩
  · cases node with
    | mk original type effects source nodeKind => cases kind; simp only [CoreMachine.next, known]
  · simp only [potential, List.map_cons, List.sum_cons, frameWeight]
    omega

theorem tuple_right_decreases (base : CoreMachine.State) (tail : List CoreMachine.Frame) :
    CoreMachine.next graph { base with control := .returned left, frames := .tupleLeft right environment :: tail } =
      .stepped { base with control := .evaluate right environment, frames := .tupleRight left :: tail } ∧
    potential graph { base with control := .evaluate right environment, frames := .tupleRight left :: tail } <
      potential graph { base with control := .returned left, frames := .tupleLeft right environment :: tail } := by
  refine ⟨rfl, ?_⟩
  simp [potential, frameWeight]
  omega

/-- Only this actual resource entry may use the common potential. The saved
initializer weight retains the pending source body cost. -/
theorem resource_entry_decreases {base : CoreMachine.State}
    (ordered : Postorder graph) (known : graph.node site = some node)
    (kind : node.kind = .resource identity handle initializer body) (tail : List CoreMachine.Frame) :
    CoreMachine.next graph { base with control := .evaluate site environment, frames := tail } =
      .stepped { base with control := .evaluate initializer environment, frames := .resourceInitializer site identity handle body environment :: tail, observations := base.observations ++ [.entered site] } ∧
    potential graph { base with control := .evaluate initializer environment, frames := .resourceInitializer site identity handle body environment :: tail, observations := base.observations ++ [.entered site] } <
      potential graph { base with control := .evaluate site environment, frames := tail } := by
  have cost := cost_recurrence ordered known
  simp only [kind, CoreSyntax.Kind.children, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at cost
  refine ⟨?_, ?_⟩
  · simp [CoreMachine.next, known, kind]
  · simp only [potential, List.map_cons, List.sum_cons, frameWeight]; omega

#print axioms resource_entry_decreases

theorem nodeCost_positive (graph : CoreSyntax.Graph) (index : Nat) : 0 < nodeCost graph index := by
  rw [nodeCost]
  omega

/-- The same potential also decreases for every previously permitted value
entry and tuple allocation; zero-step families need no competing rank choice. -/
theorem administrative_potential
    (witness : CoreAdministrativeSteps.ValueWitness graph owners before after code) :
    potential graph after < potential graph before := by
  have permitted := witness.permitted
  have next := witness.core
  cases control : before.control with
  | discard handler owner => simp [CoreAdministrativeSteps.ready, control] at permitted
  | evaluate index environment =>
    cases known : graph.node index with
    | none => simp [CoreAdministrativeSteps.ready, control, known] at permitted
    | some node =>
      have supported : CoreAdministrativeSteps.valueKind node.kind = true := by
        simpa [CoreAdministrativeSteps.ready, control, known] using permitted
      have positive := nodeCost_positive graph index
      cases kind : node.kind <;> simp only [kind, CoreAdministrativeSteps.valueKind, Bool.false_eq_true] at supported
      all_goals try contradiction
      all_goals simp only [CoreMachine.next, control, known, kind] at next
      all_goals try (cases next; simp only [potential, control]; omega)
      case «variable» name =>
        cases lookup : environment.lookup name with
        | none => simp only [lookup] at next; cases next
        | some value => simp only [lookup] at next; cases next; simp only [potential, control]; omega
  | returned value =>
    cases frames : before.frames with
    | nil => simp [CoreAdministrativeSteps.ready, control, frames] at permitted
    | cons frame tail =>
      cases frame <;> simp only [CoreAdministrativeSteps.ready, control, frames, Bool.false_eq_true] at permitted
      all_goals try contradiction
      case tupleRight left =>
        simp only [CoreMachine.next, control, frames] at next
        cases next
        simp [potential, control, frames, frameWeight]

theorem unchanged_potential_rejected (graph : CoreSyntax.Graph) (state : CoreMachine.State) :
    ¬ potential graph state < potential graph state := Nat.lt_irrefl _

#print axioms administrative_potential
#print axioms unchanged_potential_rejected

/-- Exactly the new administrative traversal families proved in this file. -/
def traversalReady (graph : CoreSyntax.Graph) (state : CoreMachine.State) : Bool :=
  match state.control with
  | .evaluate index _ => match graph.node index with
    | some node => match node.kind with
      | .apply _ _ | .tuple [_, _] | .bind _ _ _ | .resource _ _ _ _ | .request _ _ _ | .resume _ _ _ _
        | .matchCases _ [⟨.unit, _⟩]
        | .matchCases _ [⟨.boolean true, _⟩, ⟨.boolean false, _⟩]
        | .matchCases _ [⟨.boolean false, _⟩, ⟨.boolean true, _⟩] => true
      | _ => false
    | none => false
  | .returned _ => match state.frames with
    | .applyFunction _ _ :: _ | .tupleLeft _ _ :: _ => true
    | _ => false
  | .discard _ _ => false

/-- Named administrative witnesses are the only users of unchanged-target
progress here; both interpretations share one exact target configuration. -/
structure SilentMapped (graph : CoreSyntax.Graph)
    (beforeOwners afterOwners : CoreTranslation.OwnerMap) (beforeMaps afterMaps : List MappedFrame)
    (before after : CoreMachine.State) (target : Configuration) : Prop where
  core : CoreMachine.next graph before = .stepped after
  decreasing : potential graph after < potential graph before
  permitted : traversalReady graph before = true
  current : ComponentMapped graph beforeOwners beforeMaps before target
  successor : ComponentMapped graph afterOwners afterMaps after target

abbrev SilentWitness (graph : CoreSyntax.Graph) (owners : CoreTranslation.OwnerMap)
    (before after : CoreMachine.State) (target : Configuration) : Prop :=
  SilentMapped graph owners owners (uniformFrames owners before.frames)
    (uniformFrames owners after.frames) before after target

theorem unchanged_silent_rejected (graph : CoreSyntax.Graph) (owners : CoreTranslation.OwnerMap)
    (state : CoreMachine.State) (target : Configuration) :
    ¬ SilentWitness graph owners state state target := by
  intro witness
  exact unchanged_potential_rejected graph state witness.decreasing

theorem discard_not_traversal (graph : CoreSyntax.Graph) (base : CoreMachine.State)
    (handler owner : Nat) :
    traversalReady graph { base with control := .discard handler owner } = false := rfl

#print axioms unchanged_silent_rejected
#print axioms discard_not_traversal

private theorem single_flattened (frame : PlainFrameRel graph owners heap core plain)
    (ready : ClosedValue code) (tail : PushedRel graph owners heap cores target) (scope : Scope) :
    OrdinaryStackRel graph owners heap (core :: cores) code scope
      (plain.context.plug code) plain.scope target :=
  ⟨[(owners, core)], uniformFrames owners cores, rfl, .cons frame ready .nil, tail⟩

theorem application_entry_same_target {base : CoreMachine.State}
    (ordered : Postorder graph) (known : graph.node site = some node)
    (kind : node.kind = .apply function argument)
    (ft : CoreTranslation.translateFuel graph fuel owners function = .ok rawFunction)
    (argTranslated : CoreTranslation.translateFuel graph fuel owners argument = .ok rawArgument)
    (saved : EnvCloses graph owners base.heap environment
      (.app rawFunction rawArgument) (.app functionCode argumentCode))
    (ready : ClosedValue functionCode)
    (plain : PlainData) (context : plain.context = .appFunction argumentCode)
    (tail : PushedRel graph owners base.heap cores target) :
    SilentWitness graph owners
      { base with control := .evaluate site environment, frames := cores }
      { base with control := .evaluate function environment, frames := .applyFunction argument environment :: cores, observations := base.observations ++ [.entered site] }
      ⟨.app functionCode argumentCode, plain.scope, target⟩ := by
  obtain ⟨next, decrease⟩ := application_entry_decreases (base := base) ordered known kind cores
  obtain ⟨fs, ars⟩ := saved.app_components
  have translated : CoreTranslation.translateFuel graph (fuel + 1) owners site =
      .ok (.app rawFunction rawArgument) := by
    cases node with
    | mk original type effects source nodeKind =>
      cases kind
      simp only [CoreTranslation.translateFuel, CoreTranslation.requireNode, known]
      change (do pure (Code.app (← CoreTranslation.translateFuel graph fuel owners function)
        (← CoreTranslation.translateFuel graph fuel owners argument))) = _
      rw [ft, argTranslated]; rfl
  have frame : PlainFrameRel graph owners base.heap (.applyFunction argument environment) plain := by
    change FrameRel graph owners base.heap _ plain.context
    rw [context]; exact .applyFunction argTranslated ars
  have stack := single_flattened frame ready tail plain.scope
  simp only [context, Context.plug] at stack
  exact ⟨next, decrease, (by simp [traversalReady, known, kind]),
    component_uniform ⟨_, plain.scope, .evaluate translated saved, pushed_only tail⟩,
    component_uniform ⟨_, plain.scope, .evaluate ft fs, stack⟩⟩

theorem application_argument_same_target {base : CoreMachine.State}
    (translated : CoreTranslation.translateFuel graph fuel owners argument = .ok rawArgument)
    (saved : EnvCloses graph owners base.heap environment rawArgument argumentCode)
    (function : ValueRel graph owners base.heap functionValue functionCode)
    (ready : ClosedValue argumentCode)
    (before after : PlainData)
    (bc : before.context = .appFunction argumentCode)
    (ac : after.context = .appArgument functionCode) (scope : after.scope = before.scope)
    (tail : PushedRel graph owners base.heap cores target) (runtimeScope : Scope) :
    SilentWitness graph owners
      { base with control := .returned functionValue, frames := .applyFunction argument environment :: cores }
      { base with control := .evaluate argument environment, frames := .applyArgument functionValue :: cores }
      ⟨.app functionCode argumentCode, before.scope, target⟩ := by
  obtain ⟨next, decrease⟩ := application_argument_decreases (graph := graph) base cores
  have bf : PlainFrameRel graph owners base.heap (.applyFunction argument environment) before := by
    change FrameRel graph owners base.heap _ before.context
    rw [bc]; exact .applyFunction translated saved
  have af : PlainFrameRel graph owners base.heap (.applyArgument functionValue) after := by
    change FrameRel graph owners base.heap _ after.context
    rw [ac]; exact .applyArgument function
  have bs := single_flattened bf function.closed tail runtimeScope
  have ats := single_flattened af ready tail after.scope
  simp only [bc, Context.plug] at bs
  simp only [ac, Context.plug, scope] at ats
  exact ⟨next, decrease, rfl, component_uniform ⟨_, runtimeScope, .returned function, bs⟩,
    component_uniform ⟨_, before.scope, .evaluate translated saved, ats⟩⟩

theorem tuple_entry_same_target {base : CoreMachine.State}
    (ordered : Postorder graph) (known : graph.node site = some node)
    (kind : node.kind = .tuple [left, right])
    (lt : CoreTranslation.translateFuel graph fuel owners left = .ok rawLeft)
    (rt : CoreTranslation.translateFuel graph fuel owners right = .ok rawRight)
    (wholeSaved : EnvCloses graph owners base.heap environment
      (.pair rawLeft rawRight) (.pair leftCode rightCode))
    (leftSaved : EnvCloses graph owners base.heap environment rawLeft leftCode)
    (rightSaved : EnvCloses graph owners base.heap environment rawRight rightCode)
    (ready : ClosedValue leftCode)
    (plain : PlainData) (context : plain.context = .pairLeft rightCode)
    (tail : PushedRel graph owners base.heap cores target) :
    SilentWitness graph owners
      { base with control := .evaluate site environment, frames := cores }
      { base with control := .evaluate left environment, frames := .tupleLeft right environment :: cores, observations := base.observations ++ [.entered site] }
      ⟨.pair leftCode rightCode, plain.scope, target⟩ := by
  obtain ⟨next, decrease⟩ := tuple_entry_decreases (base := base) ordered known kind cores
  have translated : CoreTranslation.translateFuel graph (fuel + 1) owners site =
      .ok (.pair rawLeft rawRight) := by
    cases node with
    | mk original type effects source nodeKind =>
      cases kind
      simp only [CoreTranslation.translateFuel, CoreTranslation.requireNode, known]
      change (do pure (Code.pair (← CoreTranslation.translateFuel graph fuel owners left)
        (← CoreTranslation.translateFuel graph fuel owners right))) = _
      rw [lt, rt]; rfl
  have frame : PlainFrameRel graph owners base.heap (.tupleLeft right environment) plain := by
    change FrameRel graph owners base.heap _ plain.context
    rw [context]; exact .tupleLeft rt rightSaved
  have stack := single_flattened frame ready tail plain.scope
  simp only [context, Context.plug] at stack
  exact ⟨next, decrease, (by simp [traversalReady, known, kind]),
    component_uniform ⟨_, plain.scope, .evaluate translated wholeSaved, pushed_only tail⟩,
    component_uniform ⟨_, plain.scope, .evaluate lt leftSaved, stack⟩⟩

theorem tuple_right_same_target {base : CoreMachine.State}
    (translated : CoreTranslation.translateFuel graph fuel owners right = .ok rawRight)
    (saved : EnvCloses graph owners base.heap environment rawRight rightCode)
    (left : ValueRel graph owners base.heap leftValue leftCode)
    (ready : ClosedValue rightCode)
    (before after : PlainData)
    (bc : before.context = .pairLeft rightCode)
    (ac : after.context = .pairRight leftCode) (scope : after.scope = before.scope)
    (tail : PushedRel graph owners base.heap cores target) (runtimeScope : Scope) :
    SilentWitness graph owners
      { base with control := .returned leftValue, frames := .tupleLeft right environment :: cores }
      { base with control := .evaluate right environment, frames := .tupleRight leftValue :: cores }
      ⟨.pair leftCode rightCode, before.scope, target⟩ := by
  obtain ⟨next, decrease⟩ := tuple_right_decreases (graph := graph) base cores
  have bf : PlainFrameRel graph owners base.heap (.tupleLeft right environment) before := by
    change FrameRel graph owners base.heap _ before.context
    rw [bc]; exact .tupleLeft translated saved
  have af : PlainFrameRel graph owners base.heap (.tupleRight leftValue) after := by
    change FrameRel graph owners base.heap _ after.context
    rw [ac]; exact .tupleRight left
  have bs := single_flattened bf left.closed tail runtimeScope
  have ats := single_flattened af ready tail after.scope
  simp only [bc, Context.plug] at bs
  simp only [ac, Context.plug, scope] at ats
  exact ⟨next, decrease, rfl, component_uniform ⟨_, runtimeScope, .returned left, bs⟩,
    component_uniform ⟨_, before.scope, .evaluate translated saved, ats⟩⟩

theorem application_entry_same_target_mapped {base : CoreMachine.State}
    (ordered : Postorder graph) (known : graph.node site = some node)
    (kind : node.kind = .apply function argument)
    (ft : CoreTranslation.translateFuel graph fuel owners function = .ok rawFunction)
    (argTranslated : CoreTranslation.translateFuel graph fuel owners argument = .ok rawArgument)
    (saved : EnvCloses graph owners base.heap environment
      (.app rawFunction rawArgument) (.app functionCode argumentCode))
    (ready : ClosedValue functionCode)
    (plain : PlainData) (context : plain.context = .appFunction argumentCode)
    (tail : PushedWithMaps graph base.heap annotations target) :
    SilentMapped graph owners owners annotations ((owners, .applyFunction argument environment) :: annotations)
      { base with control := .evaluate site environment, frames := (framesOf annotations) }
      { base with control := .evaluate function environment, frames := .applyFunction argument environment :: (framesOf annotations), observations := base.observations ++ [.entered site] }
      ⟨.app functionCode argumentCode, plain.scope, target⟩ := by
  obtain ⟨next, decrease⟩ := application_entry_decreases (base := base) ordered known kind (framesOf annotations)
  obtain ⟨fs, ars⟩ := saved.app_components
  have translated : CoreTranslation.translateFuel graph (fuel + 1) owners site =
      .ok (.app rawFunction rawArgument) := by
    cases node with
    | mk original type effects source nodeKind =>
      cases kind
      simp only [CoreTranslation.translateFuel, CoreTranslation.requireNode, known]
      change (do pure (Code.app (← CoreTranslation.translateFuel graph fuel owners function)
        (← CoreTranslation.translateFuel graph fuel owners argument))) = _
      rw [ft, argTranslated]; rfl
  have frame : PlainFrameRel graph owners base.heap (.applyFunction argument environment) plain := by
    change FrameRel graph owners base.heap _ plain.context
    rw [context]; exact .applyFunction argTranslated ars
  have stack := prepend_mapped frame ready (pushed_mapped tail) plain.scope
  simp only [context, Context.plug] at stack
  exact ⟨next, decrease, (by simp [traversalReady, known, kind]),
    ⟨rfl, _, plain.scope, .evaluate translated saved, pushed_mapped tail⟩,
    ⟨rfl, _, plain.scope, .evaluate ft fs, stack⟩⟩

theorem application_argument_same_target_mapped {base : CoreMachine.State}
    (translated : CoreTranslation.translateFuel graph fuel savedOwners argument = .ok rawArgument)
    (saved : EnvCloses graph savedOwners base.heap environment rawArgument argumentCode)
    (function : ValueRel graph owners base.heap functionValue functionCode)
    (ready : ClosedValue argumentCode)
    (before after : PlainData)
    (bc : before.context = .appFunction argumentCode)
    (ac : after.context = .appArgument functionCode) (scope : after.scope = before.scope)
    (tail : PushedWithMaps graph base.heap annotations target) (runtimeScope : Scope) :
    SilentMapped graph owners savedOwners ((savedOwners, .applyFunction argument environment) :: annotations) ((savedOwners, .applyArgument functionValue) :: annotations)
      { base with control := .returned functionValue, frames := .applyFunction argument environment :: (framesOf annotations) }
      { base with control := .evaluate argument environment, frames := .applyArgument functionValue :: (framesOf annotations) }
      ⟨.app functionCode argumentCode, before.scope, target⟩ := by
  obtain ⟨next, decrease⟩ := application_argument_decreases (graph := graph) base (framesOf annotations)
  have bf : PlainFrameRel graph savedOwners base.heap (.applyFunction argument environment) before := by
    change FrameRel graph savedOwners base.heap _ before.context
    rw [bc]; exact .applyFunction translated saved
  have af : PlainFrameRel graph savedOwners base.heap (.applyArgument functionValue) after := by
    change FrameRel graph savedOwners base.heap _ after.context
    rw [ac]; exact .applyArgument (function.owner_transport savedOwners)
  have bs := prepend_mapped bf function.closed (pushed_mapped tail) runtimeScope
  have ats := prepend_mapped af ready (pushed_mapped tail) after.scope
  simp only [bc, Context.plug] at bs
  simp only [ac, Context.plug, scope] at ats
  exact ⟨next, decrease, rfl, ⟨rfl, _, runtimeScope, .returned function, bs⟩,
    ⟨rfl, _, before.scope, .evaluate translated saved, ats⟩⟩

theorem tuple_entry_same_target_mapped {base : CoreMachine.State}
    (ordered : Postorder graph) (known : graph.node site = some node)
    (kind : node.kind = .tuple [left, right])
    (lt : CoreTranslation.translateFuel graph fuel owners left = .ok rawLeft)
    (rt : CoreTranslation.translateFuel graph fuel owners right = .ok rawRight)
    (wholeSaved : EnvCloses graph owners base.heap environment
      (.pair rawLeft rawRight) (.pair leftCode rightCode))
    (leftSaved : EnvCloses graph owners base.heap environment rawLeft leftCode)
    (rightSaved : EnvCloses graph owners base.heap environment rawRight rightCode)
    (ready : ClosedValue leftCode)
    (plain : PlainData) (context : plain.context = .pairLeft rightCode)
    (tail : PushedWithMaps graph base.heap annotations target) :
    SilentMapped graph owners owners annotations ((owners, .tupleLeft right environment) :: annotations)
      { base with control := .evaluate site environment, frames := (framesOf annotations) }
      { base with control := .evaluate left environment, frames := .tupleLeft right environment :: (framesOf annotations), observations := base.observations ++ [.entered site] }
      ⟨.pair leftCode rightCode, plain.scope, target⟩ := by
  obtain ⟨next, decrease⟩ := tuple_entry_decreases (base := base) ordered known kind (framesOf annotations)
  have translated : CoreTranslation.translateFuel graph (fuel + 1) owners site =
      .ok (.pair rawLeft rawRight) := by
    cases node with
    | mk original type effects source nodeKind =>
      cases kind
      simp only [CoreTranslation.translateFuel, CoreTranslation.requireNode, known]
      change (do pure (Code.pair (← CoreTranslation.translateFuel graph fuel owners left)
        (← CoreTranslation.translateFuel graph fuel owners right))) = _
      rw [lt, rt]; rfl
  have frame : PlainFrameRel graph owners base.heap (.tupleLeft right environment) plain := by
    change FrameRel graph owners base.heap _ plain.context
    rw [context]; exact .tupleLeft rt rightSaved
  have stack := prepend_mapped frame ready (pushed_mapped tail) plain.scope
  simp only [context, Context.plug] at stack
  exact ⟨next, decrease, (by simp [traversalReady, known, kind]),
    ⟨rfl, _, plain.scope, .evaluate translated wholeSaved, pushed_mapped tail⟩,
    ⟨rfl, _, plain.scope, .evaluate lt leftSaved, stack⟩⟩

theorem tuple_right_same_target_mapped {base : CoreMachine.State}
    (translated : CoreTranslation.translateFuel graph fuel savedOwners right = .ok rawRight)
    (saved : EnvCloses graph savedOwners base.heap environment rawRight rightCode)
    (left : ValueRel graph owners base.heap leftValue leftCode)
    (ready : ClosedValue rightCode)
    (before after : PlainData)
    (bc : before.context = .pairLeft rightCode)
    (ac : after.context = .pairRight leftCode) (scope : after.scope = before.scope)
    (tail : PushedWithMaps graph base.heap annotations target) (runtimeScope : Scope) :
    SilentMapped graph owners savedOwners ((savedOwners, .tupleLeft right environment) :: annotations) ((savedOwners, .tupleRight leftValue) :: annotations)
      { base with control := .returned leftValue, frames := .tupleLeft right environment :: (framesOf annotations) }
      { base with control := .evaluate right environment, frames := .tupleRight leftValue :: (framesOf annotations) }
      ⟨.pair leftCode rightCode, before.scope, target⟩ := by
  obtain ⟨next, decrease⟩ := tuple_right_decreases (graph := graph) base (framesOf annotations)
  have bf : PlainFrameRel graph savedOwners base.heap (.tupleLeft right environment) before := by
    change FrameRel graph savedOwners base.heap _ before.context
    rw [bc]; exact .tupleLeft translated saved
  have af : PlainFrameRel graph savedOwners base.heap (.tupleRight leftValue) after := by
    change FrameRel graph savedOwners base.heap _ after.context
    rw [ac]; exact .tupleRight (left.owner_transport savedOwners)
  have bs := prepend_mapped bf left.closed (pushed_mapped tail) runtimeScope
  have ats := prepend_mapped af ready (pushed_mapped tail) after.scope
  simp only [bc, Context.plug] at bs
  simp only [ac, Context.plug, scope] at ats
  exact ⟨next, decrease, rfl, ⟨rfl, _, runtimeScope, .returned left, bs⟩,
    ⟨rfl, _, before.scope, .evaluate translated saved, ats⟩⟩

#print axioms application_entry_same_target_mapped
#print axioms application_argument_same_target_mapped
#print axioms tuple_entry_same_target_mapped
#print axioms tuple_right_same_target_mapped

/-- Exact value-ready request operand traversal shares the common potential.
Capture itself is positive and cannot use this witness. -/
theorem request_entry_decreases {base : CoreMachine.State}
    (ordered : Postorder graph) (known : graph.node site = some node)
    (kind : node.kind = .request effect operation operand) (tail : List CoreMachine.Frame) :
    CoreMachine.next graph { base with control := .evaluate site environment, frames := tail } =
      .stepped { base with control := .evaluate operand environment, frames := .request effect operation environment :: tail, observations := base.observations ++ [.entered site] } ∧
    potential graph { base with control := .evaluate operand environment, frames := .request effect operation environment :: tail, observations := base.observations ++ [.entered site] } <
      potential graph { base with control := .evaluate site environment, frames := tail } := by
  have cost := cost_recurrence ordered known
  simp only [kind, CoreSyntax.Kind.children, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at cost
  refine ⟨?_, ?_⟩
  · cases node with
    | mk original type effects source nodeKind => cases kind; simp only [CoreMachine.next, known]
  · simp only [potential, List.map_cons, List.sum_cons, frameWeight]
    omega

theorem request_entry_same_target_mapped {base : CoreMachine.State}
    (ordered : Postorder graph) (known : graph.node site = some node)
    (kind : node.kind = .request effect operation operand)
    (translated : CoreTranslation.translateFuel graph fuel owners operand = .ok raw)
    (saved : EnvCloses graph owners base.heap environment
      (.perform effect operation raw) (.perform (Instantiation.freezeEffect requested) operation code))
    (ready : ClosedValue code) (plain : PlainData)
    (context : plain.context = .perform (Instantiation.freezeEffect requested) operation)
    (tail : PushedWithMaps graph base.heap annotations target) :
    SilentMapped graph owners owners annotations ((owners, .request effect operation environment) :: annotations)
      { base with control := .evaluate site environment, frames := framesOf annotations }
      { base with control := .evaluate operand environment, frames := .request effect operation environment :: framesOf annotations, observations := base.observations ++ [.entered site] }
      ⟨.perform (Instantiation.freezeEffect requested) operation code, plain.scope, target⟩ := by
  obtain ⟨next, decrease⟩ := request_entry_decreases (base := base) ordered known kind (framesOf annotations)
  have siteTranslated : CoreTranslation.translateFuel graph (fuel + 1) owners site =
      .ok (.perform effect operation raw) := by
    rw [CoreTranslation.request_equation graph owners fuel site node effect operation operand known kind, translated]; rfl
  obtain ⟨effectEq, operandSaved⟩ := perform_components saved
  have carrier := perform_header_at saved _ _ _ _ _ rfl rfl
  have frame : RequestRel graph owners base.heap (.request effect operation environment) plain := .operand carrier context
  have stack := prepend_request frame ready (pushed_mapped tail) plain.scope
  simp only [context, Context.plug] at stack
  exact ⟨next, decrease, by simp [traversalReady, known, kind],
    ⟨rfl, _, plain.scope, .evaluate siteTranslated saved, pushed_mapped tail⟩,
    ⟨rfl, _, plain.scope, .evaluate translated operandSaved, stack⟩⟩

#print axioms request_entry_decreases
#print axioms request_entry_same_target_mapped

/-- Resume operand traversal is administrative; completion remains one
positive consuming rule and cannot use this measure as an escape. -/
theorem resume_entry_decreases {base : CoreMachine.State}
    (ordered : Postorder graph) (known : graph.node site = some node)
    (kind : node.kind = .resume handler owner post operand) (tail : List CoreMachine.Frame) :
    CoreMachine.next graph { base with control := .evaluate site environment, frames := tail } =
      .stepped { base with control := .evaluate operand environment, frames := .resume handler owner :: tail, observations := base.observations ++ [.entered site] } ∧
    potential graph { base with control := .evaluate operand environment, frames := .resume handler owner :: tail, observations := base.observations ++ [.entered site] } <
      potential graph { base with control := .evaluate site environment, frames := tail } := by
  have cost := cost_recurrence ordered known
  simp only [kind,CoreSyntax.Kind.children,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at cost
  refine ⟨?_,?_⟩
  · cases node with
    | mk original type effects source nodeKind => cases kind; simp only [CoreMachine.next,known]
  · simp only [potential,List.map_cons,List.sum_cons,frameWeight]
    omega

theorem resume_entry_same_target_mapped {base : CoreMachine.State}
    (ordered : Postorder graph) (known : graph.node site = some node)
    (kind : node.kind = .resume handler owner post operand)
    (translated : CoreTranslation.translateFuel graph fuel owners site = .ok (.resume binder raw))
    (current : EnvCloses graph owners base.heap environment (.resume binder raw) (.resume binder code))
    (ready : ClosedValue code) (plain : PlainData) (context : plain.context = .resume binder)
    (older : PushedWithMaps graph base.heap annotations target) :
    SilentMapped graph owners owners annotations ((owners,.resume handler owner) :: annotations)
      { base with control := .evaluate site environment, frames := framesOf annotations }
      { base with control := .evaluate operand environment, frames := .resume handler owner :: framesOf annotations, observations := base.observations ++ [.entered site] }
      ⟨.resume binder code,plain.scope,target⟩ := by
  obtain ⟨operandFuel,resolved,childTranslated⟩ := resume_translation_parts known kind translated
  obtain ⟨_,child,marker⟩ := resume_components current
  have frame : ResumeRel graph owners base.heap (.resume handler owner) plain :=
    .operand known kind translated resolved marker context
  have stack := prepend_resume frame ready (pushed_mapped older) plain.scope
  simp only [context,Context.plug] at stack
  obtain ⟨next,decrease⟩ := resume_entry_decreases (base := base) ordered known kind (framesOf annotations)
  exact ⟨next,decrease,by simp [traversalReady,known,kind],
    ⟨rfl,_,plain.scope,.evaluate translated current,pushed_mapped older⟩,
    ⟨rfl,_,plain.scope,.evaluate childTranslated child,stack⟩⟩

#print axioms resume_entry_decreases
#print axioms resume_entry_same_target_mapped

namespace Examples
open CoreMachineExamples
private def base : CoreMachine.State := { control := .returned .unit }
private def closure : MValue := .closure 2 1 (.binding 1 (.integer 17) .empty)
private def caller : MEnv := .binding 3 closure (.binding 1 (.integer 99) .empty)
private def functionPlain : PlainData := ⟨.appFunction .unit, .none, .unit, .unit, [], rfl⟩
private def argumentPlain : PlainData := ⟨.appArgument (.lambda 2 (.integer 17)), .none, .unit, .unit, [], rfl⟩
private def appBefore : CoreMachine.State := { base with control := .evaluate 5 caller }
private def appFocused : CoreMachine.State := { base with control := .evaluate 3 caller, frames := [.applyFunction 4 caller], observations := [.entered 5] }
private def functionReturned : CoreMachine.State := { base with control := .returned closure, frames := [.applyFunction 4 caller] }
private def argumentEntered : CoreMachine.State := { base with control := .evaluate 4 caller, frames := [.applyArgument closure] }
private def appTarget : Configuration := ⟨.app (.lambda 2 (.integer 17)) .unit, .none, .nil⟩

/-- Already-value lexical function interpretation permits unchanged-target
entry even though actual Core must still evaluate its variable node. -/
theorem lexical_application_entry : SilentWitness lexicalClosure [] appBefore appFocused appTarget := by
  have saved : EnvCloses lexicalClosure [] [] caller
      (.app (.variable 3) .unit) (.app (.lambda 2 (.integer 17)) .unit) :=
    .binding CoreValueRelation.Examples.lexical_closure (.binding .integer .empty)
  exact application_entry_same_target (base := base)
    (CoreTranslationFuel.checkShape_postorder lexicalClosure rfl)
    (site := 5) (node := ⟨5, .integer, [], none, .apply 3 4⟩) rfl rfl
    (fuel := 1) rfl rfl saved CoreValueRelation.Examples.lexical_closure.closed
    functionPlain rfl PushedRel.nil

/-- The closed Unit argument remains pending in Core; its entry precedes beta. -/
theorem lexical_argument_entry : SilentWitness lexicalClosure [] functionReturned argumentEntered appTarget := by
  have saved : EnvCloses lexicalClosure [] [] caller .unit .unit :=
    .binding CoreValueRelation.Examples.lexical_closure (.binding .integer .empty)
  exact application_argument_same_target (base := base) (argument := 4) (fuel := 1) rfl saved
    CoreValueRelation.Examples.lexical_closure (ValueRel.unit (graph := lexicalClosure) (owners := []) (heap := [])).closed
    functionPlain argumentPlain rfl rfl rfl PushedRel.nil Execution.Scope.none

/-- The previous local rank cannot license either ready-child traversal. -/
theorem old_rank_entry_rejected :
    ¬ CoreAdministrativeSteps.rank lexicalClosure appFocused < CoreAdministrativeSteps.rank lexicalClosure appBefore := by decide

theorem old_rank_argument_rejected :
    ¬ CoreAdministrativeSteps.rank lexicalClosure argumentEntered < CoreAdministrativeSteps.rank lexicalClosure functionReturned := by decide

private def pairLeft : PlainData := ⟨.pairLeft (.boolean true), .none, .integer, .unit, [], rfl⟩
private def pairRight : PlainData := ⟨.pairRight (.integer 17), .none, .boolean, .unit, [], rfl⟩
private def pairTarget : Configuration := ⟨.pair (.integer 17) (.boolean true), .none, .nil⟩

theorem tuple_ready_entry : SilentWitness tupleGraph []
    { base with control := .evaluate 2 .empty }
    { base with control := .evaluate 0 .empty, frames := [.tupleLeft 1 .empty], observations := [.entered 2] }
    pairTarget := by
  exact tuple_entry_same_target (base := base)
    (CoreTranslationFuel.checkShape_postorder tupleGraph rfl)
    (site := 2) (node := ⟨2, .product .integer .boolean, [], none, .tuple [0, 1]⟩) rfl rfl
    (fuel := 1) rfl rfl EnvCloses.empty EnvCloses.empty EnvCloses.empty
    (ValueRel.integer (graph := tupleGraph) (owners := []) (heap := []) (value := 17)).closed pairLeft rfl PushedRel.nil

theorem tuple_ready_right : SilentWitness tupleGraph []
    { base with control := .returned (.integer 17), frames := [.tupleLeft 1 .empty] }
    { base with control := .evaluate 1 .empty, frames := [.tupleRight (.integer 17)] }
    pairTarget := by
  exact tuple_right_same_target (base := base) (right := 1) (fuel := 1) rfl EnvCloses.empty
    ValueRel.integer (ValueRel.boolean (graph := tupleGraph) (owners := []) (heap := []) (value := true)).closed pairLeft pairRight rfl rfl rfl PushedRel.nil Execution.Scope.none

end Examples

#print axioms Examples.lexical_application_entry
#print axioms Examples.lexical_argument_entry
#print axioms Examples.old_rank_entry_rejected
#print axioms Examples.old_rank_argument_rejected
#print axioms Examples.tuple_ready_entry
#print axioms Examples.tuple_ready_right

#print axioms application_entry_same_target
#print axioms application_argument_same_target
#print axioms tuple_entry_same_target
#print axioms tuple_right_same_target

#print axioms cost_recurrence
#print axioms application_entry_decreases
#print axioms application_argument_decreases
#print axioms tuple_entry_decreases
#print axioms tuple_right_decreases
end Ash.OneShot.CoreStrictPotential
