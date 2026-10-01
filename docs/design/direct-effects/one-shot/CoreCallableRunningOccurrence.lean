import CoreCallableCallerBarriers
namespace Ash.OneShot.CoreCallableRunningOccurrence
open CoreSyntax CoreTranslation CoreMachine CoreValueRelation CoreStrictFrames CoreStrictStack
open ScopedExpressions ScopedExecution CoreGeneralStack CoreGeneralCaptureResume CoreGeneralRestoration
open CoreCallableReachableResume CoreCallableCleanupOrigins CoreCallableCleanupReachableTransport
open CoreCallableGeneralHistory CoreCallableCallerBarriers CoreCallableSiteLineage

/-- Immutable actual cleanup start, with original full suffix and exact receipt. -/
structure RunningStartPast (graph : Graph) (cleanupOwners : OwnerMap)
    (action : Nat) (environment : CoreMachine.Environment) (data : ActionData)
    (savedValue : CoreMachine.Value) (savedCode : Code)
    (originalPhysical : List CoreMachine.Frame) (originalTarget : Stack) where
  predecessor : CoreMachine.State
  callerOwners : OwnerMap
  scope : Execution.Scope
  installed : SavedCleanupOrigin graph cleanupOwners predecessor.heap action environment data originalPhysical
  saved : ValueRel graph callerOwners predecessor.heap savedValue savedCode
  originalHistory : GeneralHistory graph predecessor.heap originalPhysical originalTarget
  running : RunningReceipt graph cleanupOwners predecessor.heap action environment data savedValue savedCode originalPhysical
  sameInstalled : running.installed = installed
  actual : GeneralStepWitness graph
    ⟨returnedState predecessor savedValue (.cleanupBoundary action environment data.identity :: originalPhysical),
      .eval ⟨savedCode,scope,.push (.armed data) originalTarget⟩,callerOwners,[]⟩
    ⟨startedState predecessor action environment data.identity savedValue originalPhysical,
      .eval ⟨.app data.action .unit,.none,.push (.running data savedCode saved.closed) originalTarget⟩,cleanupOwners,[]⟩ [] []

/-- Structural occurrence of this SAME produced start. The current tail is
separate from the immutable original suffix; no current saved-scope invariant is
stored. Chronological transport through capture/resume remains separate. -/
structure RunningOccurrence
    (start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode originalPhysical originalTarget)
    (heap : CoreMachine.Heap) (physical : List CoreMachine.Frame) (target : Stack) where
  extension : HeapExtends start.predecessor.heap heap
  front : List CoreMachine.Frame
  frontTarget : Stack
  frontHistory : GeneralHistory graph heap front frontTarget
  tail : List CoreMachine.Frame
  tailTarget : Stack
  tailHistory : GeneralHistory graph heap tail tailTarget
  physicalSame : physical = front ++ .cleanupCompletion data.identity savedValue :: tail
  targetSame : target = frontTarget.append (.push (.running data savedCode start.running.value.closed) tailTarget)

noncomputable def RunningOccurrence.history
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode originalPhysical originalTarget}
    (occurrence : RunningOccurrence start heap physical target) : GeneralHistory graph heap physical target := by
  have built := occurrence.frontHistory.append
    ((GeneralHistory.running (start.running.heap_weaken occurrence.extension)).append occurrence.tailHistory)
  simpa only [← occurrence.targetSame,Stack.append,List.singleton_append,← occurrence.physicalSame] using built

private theorem retained_refl (history : RetainedHistory graph heap physical target)
    (extension : HeapExtends heap heap) : history.heap_weaken extension = history := by
  induction history <;> simp_all [RetainedHistory.heap_weaken]

private theorem history_refl (history : GeneralHistory graph heap physical target)
    (extension : HeapExtends heap heap) : history.heap_weaken extension = history := by
  induction history <;> simp_all [GeneralHistory.heap_weaken,retained_refl]

/-- The only initial occurrence factory consumes actual start inputs and emits
its actual start witness together with this exact receipt occurrence. -/
theorem normal_start {base : CoreMachine.State}
    (receipt : SavedCleanupOrigin graph cleanupOwners base.heap action environment data originalPhysical)
    (saved : ValueRel graph callerOwners base.heap savedValue savedCode)
    (outside : GeneralHistory graph base.heap originalPhysical originalTarget)
    (bounded : TicketBound base (.push (.armed data) originalTarget)) (scope : Execution.Scope) :
    ∃ start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode originalPhysical originalTarget,
      start.predecessor = base ∧ start.callerOwners = callerOwners ∧ start.scope = scope ∧
      HEq start.installed receipt ∧ HEq start.originalHistory outside ∧
      ∃ occurrence : RunningOccurrence start base.heap
        (.cleanupCompletion data.identity savedValue :: originalPhysical)
        (.push (.running data savedCode saved.closed) originalTarget),
        occurrence.front = [] ∧ occurrence.frontTarget = .nil ∧ occurrence.tail = originalPhysical ∧ occurrence.tailTarget = originalTarget := by
  obtain ⟨actual,_,running,installed,_⟩ := normal_start_history receipt saved outside bounded scope
  let start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode originalPhysical originalTarget :=
    ⟨base,callerOwners,scope,receipt,saved,outside,running,installed,actual⟩
  let occurrence : RunningOccurrence start base.heap
      (.cleanupCompletion data.identity savedValue :: originalPhysical)
      (.push (.running data savedCode saved.closed) originalTarget) :=
    ⟨(by intro i v h; exact h),[],.nil,.nil,originalPhysical,originalTarget,outside,rfl,rfl⟩
  exact ⟨start,rfl,rfl,rfl,HEq.rfl,HEq.rfl,occurrence,rfl,rfl,rfl,rfl⟩

/-- Actual bind installation is attached to this occurrence's SAME whole suffix,
not independently paired with a running receipt. -/
theorem bind_enter {base : CoreMachine.State}
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode originalPhysical originalTarget}
    (occurrence : RunningOccurrence start base.heap physical target)
    (origin : CurrentScopeOrigin graph owners plain.scope physical)
    (postorder : CoreTranslationFuel.Postorder graph)
    (lineage : SiteLineage graph owners plain.scope site)
    (known : graph.node site = some node) (kind : node.kind = .bind binder initializer body)
    (it : translateFuel graph fuel owners initializer = .ok rawInitializer)
    (bt : translateFuel graph fuel owners body = .ok rawBody)
    (current : EnvCloses graph owners base.heap savedEnvironment
      (.bind binder.id rawInitializer rawBody) (.bind binder.id initializerCode suffix))
    (notValue : ¬ initializerCode.IsValue) (ready : ClosedExcept binder.id suffix)
    (context : plain.context = .bind binder.id suffix) :
    ∃ past : CallerBindPast graph owners binder body savedEnvironment plain physical target,
      past.predecessor = base ∧ past.site = site ∧
      HEq past.originalHistory occurrence.history ∧
      ∃ extension : HeapExtends past.predecessor.heap base.heap,
      HEq (past.originalHistory.heap_weaken extension) occurrence.history ∧
      ∃ next : RunningOccurrence start base.heap
          (.bind binder.id body savedEnvironment :: physical) (.push (.plain plain) target),
        next.front = .bind binder.id body savedEnvironment :: occurrence.front ∧
        next.tail = occurrence.tail ∧ next.tailTarget = occurrence.tailTarget := by
  obtain ⟨past,baseSame,siteSame,_,_,_,historySame⟩ := CoreCallableCallerBarriers.bind_enter occurrence.history
    origin postorder lineage known kind it bt current notValue ready context
  have carrier : CoreCaptureEntry.PushCarrier graph owners base.heap (.bind binder.id body savedEnvironment) (.plain plain) :=
    .ordinary (by simpa only [baseSame] using past.saved.saved.related)
  let next : RunningOccurrence start base.heap
      (.bind binder.id body savedEnvironment :: physical) (.push (.plain plain) target) := {
    extension := occurrence.extension
    front := .bind binder.id body savedEnvironment :: occurrence.front
    frontTarget := .push (.plain plain) occurrence.frontTarget
    frontHistory := .push carrier (by trivial) occurrence.frontHistory
    tail := occurrence.tail, tailTarget := occurrence.tailTarget, tailHistory := occurrence.tailHistory
    physicalSame := by simp only [occurrence.physicalSame,List.cons_append]
    targetSame := by simp only [occurrence.targetSame,Stack.append] }
  have extension : HeapExtends past.predecessor.heap base.heap := by rw [baseSame]; intro i v h; exact h
  have currentCoupled : HEq (past.originalHistory.heap_weaken extension) occurrence.history := by
    have same : HEq (past.originalHistory.heap_weaken extension) past.originalHistory := by
      cases baseSame
      exact heq_of_eq (history_refl _ extension)
    exact same.trans historySame
  exact ⟨past,baseSame,siteSame,historySame,extension,currentCoupled,next,rfl,rfl,rfl⟩

/-- Actual beta over the SAME bind produced for this exact occurrence. The
active application component is outside the preserved general suffix. No new
independent prefix is admitted to manufacture a marker-bearing occurrence. -/
theorem beta_enter {base : CoreMachine.State}
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode originalPhysical originalTarget}
    (occurrence : RunningOccurrence start base.heap physical target)
    (past : CallerBindPast graph bindOwners binder body savedEnvironment plain physical target)
    (extension : HeapExtends past.predecessor.heap base.heap)
    (coupled : HEq (past.originalHistory.heap_weaken extension) occurrence.history)
    (function : ValueRel graph callOwners base.heap (.closure parameter calleeBody closureSaved) (.lambda parameter result))
    (argument : ValueRel graph callOwners base.heap value argumentCode) (callScope : Execution.Scope) :
    ∃ reset : BetaBindPast graph bindOwners binder body savedEnvironment plain physical target past base [] .nil
        callOwners parameter calleeBody closureSaved value argumentCode result callScope,
      reset.frontHistory = .nil ∧ HEq (past.originalHistory.heap_weaken extension) occurrence.history ∧
      ∃ next : RunningOccurrence start base.heap
          (.bind binder.id body savedEnvironment :: physical) (.push (.plain plain) target),
        next.front = .bind binder.id body savedEnvironment :: occurrence.front ∧
        next.tail = occurrence.tail ∧ next.tailTarget = occurrence.tailTarget ∧
        SiteLineage graph [] .none calleeBody := by
  obtain ⟨reset,frontSame,_⟩ := CoreCallableCallerBarriers.beta_enter past extension .nil function argument callScope
  have carrier : CoreCaptureEntry.PushCarrier graph bindOwners base.heap (.bind binder.id body savedEnvironment) (.plain plain) :=
    .ordinary (past.saved.saved.related.heap_weaken extension)
  let next : RunningOccurrence start base.heap
      (.bind binder.id body savedEnvironment :: physical) (.push (.plain plain) target) := {
    extension := occurrence.extension
    front := .bind binder.id body savedEnvironment :: occurrence.front
    frontTarget := .push (.plain plain) occurrence.frontTarget
    frontHistory := .push carrier (by trivial) occurrence.frontHistory
    tail := occurrence.tail, tailTarget := occurrence.tailTarget, tailHistory := occurrence.tailHistory
    physicalSame := by simp only [occurrence.physicalSame,List.cons_append]
    targetSame := by simp only [occurrence.targetSame,Stack.append] }
  exact ⟨reset,frontSame,coupled,next,rfl,rfl,rfl,reset.resetSite⟩

#print axioms RunningOccurrence.history
#print axioms normal_start
#print axioms bind_enter
#print axioms beta_enter
end Ash.OneShot.CoreCallableRunningOccurrence
