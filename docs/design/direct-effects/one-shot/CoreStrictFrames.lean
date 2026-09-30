import CoreStrictSteps
import CoreAdministrativeSteps

/-! Ordinary saved-frame components for TASK-0032. PlainData carries explicit
scope/type/pending annotations; their authentication against Core validation is
still a current static obligation. These components assert no whole-stack or
configuration invariant. Value-ready Core frames may retain a whole target
expression rather than push a target frame: focus requires a non-value child.
No effect, capture, cleanup, discard, or unrestricted stuttering is included. -/
namespace Ash.OneShot.CoreStrictFrames
open ScopedExpressions ScopedExecution CoreValueRelation

inductive FrameRel (graph : CoreSyntax.Graph) (owners : CoreTranslation.OwnerMap)
    (heap : Heap) : CoreMachine.Frame → Context → Prop where
  | bind (translated : CoreTranslation.translateFuel graph fuel owners body = .ok raw)
      (saved : EnvCloses graph owners heap environment (.lambda binder raw) (.lambda binder suffix))
      (ready : ClosedExcept binder suffix) :
      FrameRel graph owners heap (.bind binder body environment) (.bind binder suffix)
  | applyFunction (translated : CoreTranslation.translateFuel graph fuel owners argument = .ok raw)
      (saved : EnvCloses graph owners heap environment raw code) :
      FrameRel graph owners heap (.applyFunction argument environment) (.appFunction code)
  | applyArgument (related : ValueRel graph owners heap function code) :
      FrameRel graph owners heap (.applyArgument function) (.appArgument code)
  | tupleLeft (translated : CoreTranslation.translateFuel graph fuel owners right = .ok raw)
      (saved : EnvCloses graph owners heap environment raw code) :
      FrameRel graph owners heap (.tupleLeft right environment) (.pairLeft code)
  | tupleRight (related : ValueRel graph owners heap left code) :
      FrameRel graph owners heap (.tupleRight left) (.pairRight code)
  | booleanMatch
      (yesTranslated : CoreTranslation.translateFuel graph yesFuel owners yes = .ok rawYes)
      (noTranslated : CoreTranslation.translateFuel graph noFuel owners no = .ok rawNo)
      (yesSaved : EnvCloses graph owners heap environment rawYes yesCode)
      (noSaved : EnvCloses graph owners heap environment rawNo noCode) :
      FrameRel graph owners heap (.matchCases (CoreStrictSteps.booleanArms yes no reversed) environment)
        (.branch yesCode noCode)
  | unitMatch (known : graph.node site = some node)
      (kind : node.kind = .matchCases scrutinee [⟨.unit, body⟩])
      (translated : CoreTranslation.translateFuel graph fuel owners body = .ok raw)
      (saved : EnvCloses graph owners heap environment raw suffix)
      (absent : Syntax.Dependency.variable (CoreTranslation.dummy graph site) ∉ suffix.dependencies)
      (ready : ClosedExcept (CoreTranslation.dummy graph site) suffix) :
      FrameRel graph owners heap (.matchCases [⟨.unit, body⟩] environment)
        (.bind (CoreTranslation.dummy graph site) suffix)

/-- The supplied PlainData's annotations and translation certificate remain
explicit; this relation authenticates only its expression context. -/
def PlainFrameRel (graph : CoreSyntax.Graph) (owners : CoreTranslation.OwnerMap)
    (heap : Heap) (frame : CoreMachine.Frame) (plain : PlainData) : Prop :=
  FrameRel graph owners heap frame plain.context

theorem FrameRel.heap_weaken (related : FrameRel graph owners heap frame context)
    (extension : HeapExtends heap larger) : FrameRel graph owners larger frame context := by
  cases related with
  | bind translated saved ready => exact .bind translated (saved.heap_weaken extension) ready
  | applyFunction translated saved => exact .applyFunction translated (saved.heap_weaken extension)
  | applyArgument related => exact .applyArgument (related.heap_weaken extension)
  | tupleLeft translated saved => exact .tupleLeft translated (saved.heap_weaken extension)
  | tupleRight related => exact .tupleRight (related.heap_weaken extension)
  | booleanMatch yt nt ys ns => exact .booleanMatch yt nt (ys.heap_weaken extension) (ns.heap_weaken extension)
  | unitMatch known kind translated saved absent ready =>
      exact .unitMatch known kind translated (saved.heap_weaken extension) absent ready

theorem PlainFrameRel.heap_weaken (related : PlainFrameRel graph owners heap frame plain)
    (extension : HeapExtends heap larger) : PlainFrameRel graph owners larger frame plain :=
  FrameRel.heap_weaken related extension

/-- Plug is an actual positive transition for a related current value. The
saved context's expression interpretation is supplied by FrameRel itself. -/
theorem plug_related_value (frame : PlainFrameRel graph owners heap coreFrame plain)
    (value : ValueRel graph owners heap coreValue code) (scope : Scope) (tail : Stack) :
    FrameRel graph owners heap coreFrame plain.context ∧
    RawStep ⟨code, scope, .push (.plain plain) tail⟩
      ⟨plain.context.plug code, plain.scope, tail⟩ [] [] :=
  ⟨frame, .plug plain code value.closed scope tail⟩

theorem focus_plug_agreement (related : PlainFrameRel graph owners heap coreFrame plain)
    (focus : Focus whole child plain.context) :
    FrameRel graph owners heap coreFrame plain.context ∧ plain.context.plug child = whole :=
  ⟨related, focus_reconstructs focus⟩

/-- A source apply node focuses its non-value function and saves the translated
argument. Both lexical children come from the same whole-app interpretation. -/
theorem application_focus {base : CoreMachine.State}
    (known : graph.node site = some node) (kind : node.kind = .apply function argument)
    (functionTranslated : CoreTranslation.translateFuel graph fuel owners function = .ok rawFunction)
    (argumentTranslated : CoreTranslation.translateFuel graph fuel owners argument = .ok rawArgument)
    (current : EnvCloses graph owners base.heap environment
      (.app rawFunction rawArgument) (.app functionCode argumentCode))
    (notValue : ¬ functionCode.IsValue)
    (plain : PlainData) (context : plain.context = .appFunction argumentCode)
    (coreTail : List CoreMachine.Frame) (targetTail : Stack) :
    CoreMachine.next graph { base with control := .evaluate site environment, frames := coreTail } =
      .stepped { base with control := .evaluate function environment, frames := .applyFunction argument environment :: coreTail, observations := base.observations ++ [.entered site] } ∧
    RawStep ⟨.app functionCode argumentCode, plain.scope, targetTail⟩
      ⟨functionCode, plain.scope, .push (.plain plain) targetTail⟩ [] [] ∧
    CoreTranslation.translateFuel graph fuel owners function = .ok rawFunction ∧
    EnvCloses graph owners base.heap environment rawFunction functionCode ∧
    PlainFrameRel graph owners base.heap (.applyFunction argument environment) plain := by
  obtain ⟨functionSaved, argumentSaved⟩ := current.app_components
  refine ⟨?_, ?_, functionTranslated, functionSaved, ?_⟩
  · cases node with
    | mk original type effects source nodeKind =>
      cases kind
      simp only [CoreMachine.next, known]
  · exact .focus plain (by rw [context]; exact .appFunction notValue) targetTail
  · change FrameRel graph owners base.heap _ plain.context
    rw [context]
    exact .applyFunction argumentTranslated argumentSaved

/-- Return the function, reconstruct the application, then focus the saved
non-value argument. The intermediate whole application prevents early beta. -/
theorem application_return_function {base : CoreMachine.State}
    (translated : CoreTranslation.translateFuel graph fuel owners argument = .ok rawArgument)
    (saved : EnvCloses graph owners base.heap environment rawArgument argumentCode)
    (function : ValueRel graph owners base.heap functionValue functionCode)
    (notValue : ¬ argumentCode.IsValue)
    (before after : PlainData)
    (beforeContext : before.context = .appFunction argumentCode)
    (afterContext : after.context = .appArgument functionCode)
    (sameScope : after.scope = before.scope)
    (runtimeScope : Scope) (coreTail : List CoreMachine.Frame) (targetTail : Stack) :
    CoreMachine.next graph { base with control := .returned functionValue, frames := .applyFunction argument environment :: coreTail } =
      .stepped { base with control := .evaluate argument environment, frames := .applyArgument functionValue :: coreTail } ∧
    RawStep ⟨functionCode, runtimeScope, .push (.plain before) targetTail⟩
      ⟨.app functionCode argumentCode, before.scope, targetTail⟩ [] [] ∧
    RawStep ⟨.app functionCode argumentCode, before.scope, targetTail⟩
      ⟨argumentCode, after.scope, .push (.plain after) targetTail⟩ [] [] ∧
    PlainFrameRel graph owners base.heap (.applyArgument functionValue) after ∧
    EnvCloses graph owners base.heap environment rawArgument argumentCode ∧
    PlainFrameRel graph owners base.heap (.applyFunction argument environment) before := by
  refine ⟨rfl, ?_, ?_, ?_, saved, ?_⟩
  · have step := RawStep.plug before functionCode function.closed runtimeScope targetTail
    simpa only [beforeContext, Context.plug] using step
  · rw [← sameScope]
    exact .focus after (by rw [afterContext]; exact .appArgument function.closed.1 notValue) targetTail
  · change FrameRel graph owners base.heap _ after.context
    rw [afterContext]; exact .applyArgument function
  · change FrameRel graph owners base.heap _ before.context
    rw [beforeContext]; exact .applyFunction translated saved

/-- With a value-ready argument only reconstruction happens here. Core still
enters that argument; administrative entry and completed beta are separate. -/
theorem application_value_ready_boundary
    (function : ValueRel graph owners heap value functionCode)
    (plain : PlainData) (context : plain.context = .appFunction argumentCode)
    (scope : Scope) (tail : Stack) :
    RawStep ⟨functionCode, scope, .push (.plain plain) tail⟩
      ⟨.app functionCode argumentCode, plain.scope, tail⟩ [] [] := by
  simpa only [context, Context.plug] using RawStep.plug plain functionCode function.closed scope tail

namespace Examples
open CoreMachineExamples

/-- The actual saved lexical closure remains 17 through a frame, independent
of the caller's 99. The main wrapper retains its finite template suffix. -/
theorem lexical_frame : FrameRel lexicalClosure [] []
    (.applyArgument (.closure 2 1 (.binding 1 (.integer 17) .empty)))
    (.appArgument (.lambda 2 (.integer 17))) :=
  .applyArgument CoreValueRelation.Examples.lexical_closure

theorem main_frame : FrameRel entryWrapper [] []
    (.applyArgument (.closure 8 0 (.functionTemplate 5 8 0 .empty)))
    (.appArgument (.lambda 8 (.integer 17))) :=
  .applyArgument CoreValueRelation.Examples.main_lookup_value

private def node (identity : Nat) (kind : CoreSyntax.Kind) : CoreSyntax.Node :=
  ⟨identity, .unit, [], none, kind⟩
private def graph : CoreSyntax.Graph := ⟨[
  node 0 .unit,
  node 1 (.bind ⟨4, .unit⟩ 0 0),
  node 2 (.apply 1 0),
  ⟨3, .function .unit .unit [], [], none, .function ⟨2, .unit⟩ 0⟩], 2⟩
private def base : CoreMachine.State := { control := .returned .unit }
private def argumentPlain : PlainData :=
  ⟨.appFunction (.bind 4 .unit .unit), .none, .unit, .unit, [], rfl⟩
private def functionPlain : PlainData :=
  ⟨.appArgument (.lambda 2 .unit), .none, .unit, .unit, [], rfl⟩
private def focusPlain : PlainData :=
  ⟨.appFunction .unit, .none, .unit, .unit, [], rfl⟩

/-- Saved pending expressions may be non-values; this genuinely takes two
positive transitions through the reconstructed whole application. -/
theorem return_nonvalue_argument (coreTail : List CoreMachine.Frame) (targetTail : Stack) :
    ∃ middle : Configuration,
      RawStep ⟨.lambda 2 .unit, .none, .push (.plain argumentPlain) targetTail⟩ middle [] [] ∧
      RawStep middle ⟨.bind 4 .unit .unit, .none, .push (.plain functionPlain) targetTail⟩ [] [] := by
  have closure : ValueRel graph [] base.heap (.closure 2 0 .empty) (.lambda 2 .unit) := by
    have callable : CallableCertificate graph 2 0 .unit := by
      refine ⟨⟨3, ⟨2, .unit⟩, _, rfl, rfl, rfl⟩, ⟨1, rfl⟩, ?_⟩
      intro ticket; simp [Code.dependencies, Syntax.without]
    exact .closure (fuel := 1) rfl callable .empty (by
      simp [ClosedValue, Code.IsValue, Code.ResourceClosed, Code.freeNames, Code.dependencies])
  obtain ⟨_, plug, focus, _⟩ := application_return_function
    (graph := graph) (owners := []) (base := base) (argument := 1)
    (fuel := 2) (rawArgument := .bind 4 .unit .unit) rfl EnvCloses.empty
    closure (by simp [Code.IsValue]) argumentPlain functionPlain rfl rfl rfl
    .none coreTail targetTail
  exact ⟨_, plug, focus⟩

/-- A genuine non-value function focus creates the actual saved argument
frame, with arbitrary untouched tails on both machines. -/
theorem focus_nonvalue_function (coreTail : List CoreMachine.Frame) (targetTail : Stack) :
    CoreMachine.next graph { base with control := .evaluate 2 .empty, frames := coreTail } =
      .stepped { base with control := .evaluate 1 .empty, frames := .applyFunction 0 .empty :: coreTail, observations := [.entered 2] } ∧
    RawStep ⟨.app (.bind 4 .unit .unit) .unit, .none, targetTail⟩
      ⟨.bind 4 .unit .unit, .none, .push (.plain focusPlain) targetTail⟩ [] [] := by
  have witness := application_focus (graph := graph) (owners := []) (base := base)
    (site := 2) (node := node 2 (.apply 1 0)) (function := 1) (argument := 0)
    (fuel := 2) (rawFunction := .bind 4 .unit .unit) (rawArgument := .unit)
    (environment := .empty) rfl rfl rfl rfl EnvCloses.empty
    (by simp [Code.IsValue]) focusPlain rfl coreTail targetTail
  exact ⟨witness.1, witness.2.1⟩

/-- The argument focus side condition prevents premature beta/focus in the
value-ready application boundary. -/
theorem value_argument_not_focus :
    ¬ Focus (.app (.lambda 2 .unit) .unit) .unit (.appArgument (.lambda 2 .unit)) := by
  intro focus
  cases focus with
  | appArgument _ notValue => exact notValue trivial

end Examples

#print axioms Examples.lexical_frame
#print axioms Examples.main_frame
#print axioms Examples.return_nonvalue_argument
#print axioms Examples.focus_nonvalue_function
#print axioms Examples.value_argument_not_focus

#print axioms FrameRel.heap_weaken
#print axioms plug_related_value
#print axioms focus_plug_agreement
#print axioms application_focus
#print axioms application_return_function
#print axioms application_value_ready_boundary
end Ash.OneShot.CoreStrictFrames
