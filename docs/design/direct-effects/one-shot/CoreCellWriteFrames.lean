import CoreCleanupRunFrames
import CoreCaptureEntry
import CoreUnwindRelation

/-! Current cell-write components above an authenticated running cleanup tail.
Only the selected cell is updated; retained lexical handlers are not erased.
Annotations and target-world freshness remain separate obligations. -/
namespace Ash.OneShot.CoreCellWriteFrames
open ScopedExpressions
open Syntax (Dependency)
open ScopedExecution CoreValueRelation CoreStrictFrames CoreStrictStack CoreEffectFrames
  CoreCleanupRunFrames CoreCaptureEntry

theorem pair_components_at
    (related : EnvCloses graph owners heap environment source target) :
    ∀ rawFunction rawArgument function argument,
      source = .pair rawFunction rawArgument → target = .pair function argument →
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

theorem pair_components
    (related : EnvCloses graph owners heap environment (.pair rawFunction rawArgument) (.pair function argument)) :
    EnvCloses graph owners heap environment rawFunction function ∧
      EnvCloses graph owners heap environment rawArgument argument :=
  pair_components_at related _ _ _ _ rfl rfl


/-- Empty mapped ordinary components expose their current control interpretation. -/
theorem empty_component (component : ComponentMapped graph owners [] state target) :
    ControlRel graph owners state.heap state.control target.expression ∧ target.stack = .nil := by
  cases target with
  | mk expression targetScope targetStack =>
    obtain ⟨_,code,scope,control,front,suffix,split,flat,pushed⟩ := component
    have empty := List.append_eq_nil_iff.mp split.symm
    rcases empty with ⟨rfl,rfl⟩
    cases flat
    cases pushed
    exact ⟨control,rfl⟩
/-- Extract one reached empty ordinary prefix; retain its exact running carrier. -/
theorem running_empty_parts (related : CoreUnwindRelation.Related graph point)
    (maps : point.annotations = [])
    (control : point.state.control = .evaluate index environment)
    (machine : point.machine = .eval target)
    (nonempty : point.state.frames ≠ []) :
    ∃ physical lexical focus,
      RunningTail graph point.state.heap physical lexical ∧ point.state.frames = physical ∧
      target = attach focus lexical ∧ focus.stack = .nil ∧
      ControlRel graph point.owners point.state.heap point.state.control focus.expression := by
  cases related with
  | eval component =>
      simp only at maps machine nonempty
      rw [maps] at component
      exact False.elim (nonempty component.1)
  | discard carrier actual frames stack =>
      simp only at control
      rw [actual] at control
      cases control
  | projected captured outside projection nonemptyClosing actual frames counter =>
      simp only at control
      rw [actual] at control
      cases control
  | awaitingClose actual frames tail =>
      simp only at control
      rw [actual] at control
      cases control
  | runningCleanup carrier component frames =>
      simp only at maps machine nonempty ⊢
      rw [maps] at component frames
      have parts := empty_component component
      have same := LexicalUnwind.Machine.eval.inj machine
      exact ⟨_,_,_,carrier,by simpa [framesOf] using frames,same.symm,parts.2,parts.1⟩

/-- A selected target cell update over current Core frame interpretations.
The new stack is constructed from those same interpretations. Actual Core
nearest selection is checked separately for the concrete callback below. -/
inductive WriteCut (graph : CoreSyntax.Graph) (heap : Heap) (identity : Nat) (old new : Int) :
    List MappedFrame → Stack → List MappedFrame → Stack → Prop where
  | hit (known : graph.node site = some node)
      (kind : node.kind = .resource resource binder initializer body)
      (tail : PushedWithMaps graph heap maps target) :
      WriteCut graph heap identity old new ((owners,.resourceBoundary site identity old)::maps)
        (.push (.cell identity old scope answer) target)
        ((owners,.resourceBoundary site identity new)::maps) (.push (.cell identity new scope answer) target)
  | push (frame : PushCarrier graph owners heap core targetFrame)
      (miss : targetFrame.erase.target ≠ some (.cell identity))
      (next : WriteCut graph heap identity old new before beforeTarget after afterTarget) :
      WriteCut graph heap identity old new ((owners,core)::before) (.push targetFrame beforeTarget)
        ((owners,core)::after) (.push targetFrame afterTarget)
  | spent (header : CoreRequestFrames.OwnerHeader graph owners heap handler owner occurrence data)
      (next : WriteCut graph heap identity old new before beforeTarget after afterTarget) :
      WriteCut graph heap identity old new ((owners,.clauseBoundary handler owner occurrence ticket none)::before)
        (.spent ticket data.answer data.scope beforeTarget)
        ((owners,.clauseBoundary handler owner occurrence ticket none)::after) (.spent ticket data.answer data.scope afterTarget)

theorem WriteCut.components (cut : WriteCut graph heap identity old new before beforeTarget after afterTarget) :
    PushedWithMaps graph heap before beforeTarget ∧ PushedWithMaps graph heap after afterTarget ∧
      CellUpdate identity old new beforeTarget afterTarget := by
  induction cut with
  | hit known kind tail => exact ⟨.boundary (.cell known kind) tail,.boundary (.cell known kind) tail,.hit⟩
  | push frame miss next ih => exact ⟨frame.prepend ih.1,frame.prepend ih.2.1,.push miss ih.2.2⟩
  | spent header next ih => exact ⟨.spent header ih.1,.spent header ih.2.1,.spent ih.2.2⟩

theorem WriteCut.heap_weaken (cut : WriteCut graph heap identity old new before beforeTarget after afterTarget)
    (extension : HeapExtends heap larger) : WriteCut graph larger identity old new before beforeTarget after afterTarget := by
  induction cut with
  | hit known kind tail => exact .hit known kind (tail.heap_weaken extension)
  | @push owners core targetFrame before beforeTarget after afterTarget frame miss next ih =>
      have largerFrame : PushCarrier graph owners larger core targetFrame := by
        cases frame with
        | ordinary frame => exact .ordinary (frame.heap_weaken extension)
        | initializer frame => exact .initializer (frame.heap_weaken extension)
        | request frame => exact .request (frame.heap_weaken extension)
        | resume frame => exact .resume (frame.heap_weaken extension)
        | cleanup frame => exact .cleanup (frame.heap_weaken extension)
        | boundary frame => exact .boundary (frame.heap_weaken extension)
      exact .push largerFrame miss ih
  | spent header next ih => exact .spent (header.heap_weaken extension) ih

/-- Preserve the same captured cleanup, delayed lexical environment, projection
and retained handlers while updating only its current outside cell. -/
theorem running_write
    (captured : PushedWithMaps graph heap
      ((pendingOwners,pending)::(savedOwners,.cleanupBoundary action environment data.identity)::retainedMaps)
      (.push (.plain pendingPlain) (.push (.armed data) retainedTarget)))
    (delayed : CoreCleanupFrames.CleanupRel graph savedOwners heap (.cleanupBoundary action environment data.identity) data)
    (retained : PushedWithMaps graph heap retainedMaps retainedTarget)
    (outside : WriteCut graph heap identity old new before beforeTarget after afterTarget)
    (projection : CoreMachine.closeFuel
      (CoreMachine.framesMass (pending::.cleanupBoundary action environment data.identity::framesOf retainedMaps)+1)
      (pending::.cleanupBoundary action environment data.identity::framesOf retainedMaps) =
      .ok (.cleanupBoundary action environment data.identity::closing,[]))
    (retainedMiss : ∀ tail changed, CellUpdate identity old new tail changed →
      CellUpdate identity old new (retainedTarget.append tail) (retainedTarget.append changed)) :
    RunningTail graph heap
      (.cleanupCompletion data.identity .unit::closing ++ .closeCompletion closeIdentity::framesOf after)
      (.push (.unwinding data) (retainedTarget.append (.push (.closing closeIdentity closeScope) afterTarget))) ∧
    CellUpdate identity old new
      (.push (.unwinding data) (retainedTarget.append (.push (.closing closeIdentity closeScope) beforeTarget)))
      (.push (.unwinding data) (retainedTarget.append (.push (.closing closeIdentity closeScope) afterTarget))) := by
  exact ⟨.projected captured delayed retained outside.components.2.1 projection,
    .push (by simp [ExecFrame.erase,Frame.target])
      (retainedMiss _ _ (.push (by simp [ExecFrame.erase,Frame.target,closeFrame]) outside.components.2.2))⟩

#print axioms WriteCut.components
#print axioms WriteCut.heap_weaken
#print axioms running_write
#print axioms pair_components
#print axioms empty_component
#print axioms running_empty_parts
end Ash.OneShot.CoreCellWriteFrames
