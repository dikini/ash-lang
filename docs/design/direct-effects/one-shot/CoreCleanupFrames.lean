import CoreEffectFrames

/-! Exact delayed cleanup action interpretation. Registration saves the actual
Core action and environment; no action execution or future validity is assumed. -/
namespace Ash.OneShot.CoreCleanupFrames
open ScopedExpressions ScopedExecution CoreValueRelation CoreEffectFrames
open Syntax (Dependency)

theorem cleanup_components_at
    (related : EnvCloses graph owners heap environment source target) :
    ∀ rawFunction rawArgument function argument,
      source = .cleanup rawFunction rawArgument → target = .cleanup function argument →
      EnvCloses graph owners heap environment rawFunction function ∧
      EnvCloses graph owners heap environment rawArgument argument := by
  induction related using EnvCloses.rec (motive_1 := fun _ _ _ _ _ => True) with
  | unit | boolean | integer | handle | location | closure => trivial
  | empty =>
      intro rf ra f a sourceEq targetEq
      have same : rf = f ∧ ra = a := by simpa [sourceEq] using targetEq
      rcases same with ⟨rfl, rfl⟩
      exact ⟨.empty, .empty⟩
  | @binding owners heap value valueCode rest output binder code replacement tail ihReplacement ihTail =>
      intro rf ra f a sourceEq targetEq
      obtain ⟨left, right⟩ := ihTail (rf.subst binder valueCode) (ra.subst binder valueCode) f a
        (by simp only [sourceEq, Code.subst]) targetEq
      exact ⟨.binding replacement left, .binding replacement right⟩
  | @resource owners heap rest output binder key code tail ihTail =>
      intro rf ra f a sourceEq targetEq
      obtain ⟨left, right⟩ := ihTail
        (rf.instantiate (Instantiation.Environment.empty.bind binder key))
        (ra.instantiate (Instantiation.Environment.empty.bind binder key)) f a
        (by simp only [sourceEq, Code.instantiate]) targetEq
      exact ⟨.resource left, .resource right⟩
  | @templateUnused binder owners heap rest code output parameter body absent tail ihTail =>
      intro rf ra f a sourceEq targetEq
      obtain ⟨left, right⟩ := ihTail rf ra f a sourceEq targetEq
      have absentLeft : Dependency.variable binder ∉ rf.dependencies := by
        intro member; apply absent
        simpa only [sourceEq, Code.dependencies] using List.mem_append_left ra.dependencies member
      have absentRight : Dependency.variable binder ∉ ra.dependencies := by
        intro member; apply absent
        simpa only [sourceEq, Code.dependencies] using List.mem_append_right rf.dependencies member
      exact ⟨.templateUnused absentLeft left, .templateUnused absentRight right⟩
  | @templateExpand fuel body bodyCode parameter binder heap rest valueCode owners output code translated callable nonrecursive replacement closed tail ihReplacement ihTail =>
      intro rf ra f a sourceEq targetEq
      obtain ⟨left, right⟩ := ihTail (rf.subst binder valueCode) (ra.subst binder valueCode) f a
        (by simp only [sourceEq, Code.subst]) targetEq
      exact ⟨.templateExpand translated callable nonrecursive replacement closed left,
        .templateExpand translated callable nonrecursive replacement closed right⟩

theorem cleanup_components
    (related : EnvCloses graph owners heap environment (.cleanup rawFunction rawArgument) (.cleanup function argument)) :
    EnvCloses graph owners heap environment rawFunction function ∧
      EnvCloses graph owners heap environment rawArgument argument :=
  cleanup_components_at related _ _ _ _ rfl rfl

/-- Add the delayed Unit operand through the same finite environment derivation. -/
theorem app_unit (related : EnvCloses graph owners heap environment source target) :
    EnvCloses graph owners heap environment (.app source .unit) (.app target .unit) := by
  induction related using EnvCloses.rec (motive_1 := fun _ _ _ _ _ => True) with
  | unit | boolean | integer | handle | location | closure => trivial
  | empty => exact .empty
  | binding replacement tail ihReplacement ihTail => exact .binding replacement ihTail
  | resource tail ihTail => exact .resource ihTail
  | templateUnused absent tail ihTail =>
      exact .templateUnused (by simpa [Code.dependencies] using absent) ihTail
  | templateExpand translated callable nonrecursive replacement closed tail ihReplacement ihTail =>
      exact .templateExpand translated callable nonrecursive replacement closed ihTail

set_option linter.unusedSimpArgs false in
/-- The translator's finite cleanup check authenticates the actual stored
ordinary invocation, independently of registration and callback execution. -/
theorem checked_action_translation
    (checked : CoreTranslation.checkCleanup graph site callback action = .ok ()) :
    CoreTranslation.translateFuel graph 3 owners action = .ok (.app (.variable callback.id) .unit) := by
  cases actionFound : graph.node action with
  | none => simp [CoreTranslation.checkCleanup,CoreTranslation.requireNode,Bind.bind,Pure.pure,Except.bind,Except.pure,actionFound] at checked
  | some actionNode =>
      cases actionKind : actionNode.kind <;>
        simp [CoreTranslation.checkCleanup,CoreTranslation.requireNode,Bind.bind,Pure.pure,Except.bind,Except.pure,actionFound,actionKind] at checked
      rename_i function argument
      cases functionFound : graph.node function with
      | none => simp [Bind.bind,Pure.pure,Except.bind,Except.pure,functionFound] at checked
      | some functionNode =>
          cases argumentFound : graph.node argument with
          | none => simp [Bind.bind,Pure.pure,Except.bind,Except.pure,functionFound,argumentFound] at checked
          | some argumentNode =>
              cases functionKind : functionNode.kind <;> cases argumentKind : argumentNode.kind <;>
                simp [Bind.bind,Pure.pure,Except.bind,Except.pure,functionFound,argumentFound,functionKind,argumentKind] at checked
              simp [CoreTranslation.translateFuel,CoreTranslation.requireNode,Bind.bind,Pure.pure,Except.bind,Except.pure,actionFound,actionKind,
                functionFound,argumentFound,functionKind,argumentKind,checked]

/-- Actual cleanup boundary and its armed target action. Supplied ActionData
scope/answer/request annotations are not authenticated by this relation. -/
inductive CleanupRel (graph : CoreSyntax.Graph) (owners : CoreTranslation.OwnerMap) (heap : Heap) :
    CoreMachine.Frame → ActionData → Prop where
  | armed (known : graph.node site = some node)
      (kind : node.kind = .cleanup callback action body)
      (shape : CoreTranslation.checkCleanup graph site callback action = .ok ())
      (delayed : CoreTranslation.translateFuel graph 3 owners action = .ok (.app (.variable callback.id) .unit))
      (saved : EnvCloses graph owners heap environment (.app (.variable callback.id) .unit) (.app data.action .unit))
      (lookup : environment.lookup callback.id = some (.closure parameter functionBody captured))
      (value : ValueRel graph owners heap (.closure parameter functionBody captured) data.action) :
      CleanupRel graph owners heap (.cleanupBoundary action environment data.identity) data

theorem CleanupRel.heap_weaken (related : CleanupRel graph owners heap core data)
    (extension : HeapExtends heap larger) : CleanupRel graph owners larger core data := by
  cases related with
  | armed known kind shape delayed saved lookup value =>
      exact .armed known kind shape delayed (saved.heap_weaken extension) lookup (value.heap_weaken extension)

#print axioms cleanup_components
#print axioms app_unit
#print axioms checked_action_translation
#print axioms CleanupRel.heap_weaken
end Ash.OneShot.CoreCleanupFrames
