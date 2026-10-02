import CoreCallableGeneratedChronology
import CoreSuffixSplice

/-! Original cleanup registration sites produced by SAME actual entry.
The current caller-site receipt is consumed at registration, not invented from
CleanupRel. Full physical history is retained into actual normal start. Later
capture/resume saved-anchor transport remains separate. -/
namespace Ash.OneShot.CoreCallableGeneratedCleanupRegistration
open CoreSyntax CoreTranslation CoreTranslationFuel CoreMachine CoreValueRelation
open ScopedExpressions ScopedExecution CoreStrictStack CoreStrictFrames
open CoreGeneralStack CoreGeneralRestoration CoreCallableReachableResume
open CoreCallableCleanupOrigins CoreCallableSiteLineage CoreCallableGeneralHistory
open CoreCallableFrameInstallations CoreCallableRunningOccurrence CoreCallableGeneratedChronology

/-- This computed endpoint is the exact existing cleanup entry successor. -/
def registeredState (base : CoreMachine.State) (site body action : Nat)
    (environment : CoreMachine.Environment) (data : ActionData) (physical : List CoreMachine.Frame) : CoreMachine.State :=
  {base with control := .evaluate body environment, frames := .cleanupBoundary action environment data.identity :: physical, nextCleanup := base.nextCleanup+1, observations := base.observations ++ [.entered site,.cleanupArmed data.identity]}

/-- Actual past output, indexed by original node, action, scope and suffix. -/
structure RegisteredCleanupPast (graph : Graph) (owners : OwnerMap) (base : CoreMachine.State)
    (site : Nat) (callback : Binder) (action body : Nat) (environment : CoreMachine.Environment)
    (data : ActionData) (physical : List CoreMachine.Frame) (target : Stack) where
  node : CoreSyntax.Node
  known : graph.node site = some node
  kind : node.kind = .cleanup callback action body
  postorder : Postorder graph
  lineage : SiteLineage graph owners data.scope site
  identity : data.identity = base.nextCleanup
  installed : SavedCleanupOrigin graph owners base.heap action environment data physical
  history : GeneralHistory graph base.heap physical target
  actual : CoreMachine.next graph {base with control := .evaluate site environment,frames := physical} =
    .stepped (registeredState base site body action environment data physical)

/-- Caller-site input is current independently produced lineage. Body/action
lineage and SAME registered receipt are outputs of this concrete entry. -/
theorem register_with_sites
    (postorder : Postorder graph) (lineage : SiteLineage graph owners data.scope site)
    (known : graph.node site = some node) (kind : node.kind = .cleanup callback action body)
    (shape : checkCleanup graph site callback action = .ok ())
    (translated : translateFuel graph fuel owners body = .ok rawBody)
    (current : EnvCloses graph owners base.heap environment (.cleanup (.variable callback.id) rawBody)
      (.cleanup data.action bodyCode))
    (callable : data.action = .lambda parameter lambdaBody)
    (identity : data.identity = base.nextCleanup)
    (ownership : CurrentOwnership graph owners {base with frames := framesOf annotations} data.scope target)
    (older : MappedHistory graph base.heap annotations target) :
    ∃ _past : RegisteredCleanupPast graph owners base site callback action body environment data (framesOf annotations) target,
      SiteLineage graph owners data.scope body ∧ SiteLineage graph owners data.scope action ∧
      RawStep ⟨.cleanup data.action bodyCode,data.scope,target⟩
        ⟨bodyCode,data.scope,.push (.armed data) target⟩ [.cleanup data.identity] [] ∧
      CurrentOwnership graph owners (registeredState base site body action environment data (framesOf annotations))
        data.scope (.push (.armed data) target) := by
  obtain ⟨_before,step,raw,_after,installed,owned⟩ :=
    cleanup_enter_owned known kind shape translated current callable identity ownership older.related
  let past : RegisteredCleanupPast graph owners base site callback action body environment data (framesOf annotations) target :=
    ⟨node,known,kind,postorder,lineage,identity,installed,GeneralHistory.of_mapped older,step⟩
  exact ⟨past,lineage.child postorder known (by simp [kind,Kind.children]),
    lineage.child postorder known (by simp [kind,Kind.children]),raw,owned⟩

/-- No independently supplied child lineage is needed by this actual consumer. -/
theorem RegisteredCleanupPast.body_site
    (past : RegisteredCleanupPast graph owners base site callback action body environment data physical target) :
    SiteLineage graph owners data.scope body :=
  past.lineage.child past.postorder past.known (by simp [past.kind,Kind.children])

theorem RegisteredCleanupPast.action_site
    (past : RegisteredCleanupPast graph owners base site callback action body environment data physical target) :
    SiteLineage graph owners data.scope action :=
  past.lineage.child past.postorder past.known (by simp [past.kind,Kind.children])

/-- An immediate literal body handler cannot reinstall the original active
caller's SAME handler. This is local registration ancestry, not a global
activation separation theorem. -/
theorem RegisteredCleanupPast.body_not_caller_reentry
    (past : RegisteredCleanupPast graph (⟨handler,owner,ticket graph owner⟩::owners)
      base site callback action body environment data physical target)
    (unique : UniqueHandlerSites graph)
    (scope : data.scope = .ticket (ticket graph owner) dynamicTicket)
    {handlerNode : CoreSyntax.Node}
    (known : graph.node body = some handlerNode)
    (kind : handlerNode.kind = .handler handler effect handlerBody clauses) : False := by
  have lineage := past.body_site
  rw [scope] at lineage
  exact lineage.not_own_handler unique known kind

/-- Actual successful body steps supply heap extension, rather than an
independently selected later heap. -/
theorem steps_heap_extends (steps : CoreAllocationHistory.Steps graph count before after) :
    HeapExtends before.heap after.heap := by
  induction steps with
  | refl => exact fun _ _ h => h
  | snoc earlier step ih =>
    have next := CoreSuffixSplice.next_heap_extends step
    exact fun i v known => next i v (ih i v known)

/-- Registration-to-start relation records the SAME actual body execution.
No unrelated start, replacement receipt or desired successor is accepted. -/
structure StartedFrom
    (registration : RegisteredCleanupPast graph owners base site callback action body environment data physical target)
    (start : RunningStartPast graph owners action environment data savedValue savedCode physical target)
    (bodyCount : Nat) : Prop where
  bodySteps : CoreAllocationHistory.Steps graph bodyCount
    (registeredState base site body action environment data physical) start.predecessor
  returned : start.predecessor.control = .returned savedValue
  physicalSame : start.predecessor.frames = .cleanupBoundary action environment data.identity :: physical
  extension : HeapExtends base.heap start.predecessor.heap
  installedSame : HEq start.installed (registration.installed.heap_weaken extension)
  historySame : HEq start.originalHistory (registration.history.heap_weaken extension)

/-- The original registered history is weakened using actual body steps and
passed to SAME normal_start_history factory. Body completion and TicketBound
are current execution outputs; general body progress is not manufactured. -/
theorem start_registered
    (registration : RegisteredCleanupPast graph owners base site callback action body environment data physical target)
    (bodySteps : CoreAllocationHistory.Steps graph count
      (registeredState base site body action environment data physical) bodyEnd)
    (returned : bodyEnd.control = .returned savedValue)
    (physicalSame : bodyEnd.frames = .cleanupBoundary action environment data.identity :: physical)
    (saved : ValueRel graph callerOwners bodyEnd.heap savedValue savedCode)
    (bounded : TicketBound bodyEnd (.push (.armed data) target)) :
    ∃ start : RunningStartPast graph owners action environment data savedValue savedCode physical target,
      StartedFrom registration start count ∧
      CoreMachine.next graph bodyEnd = .stepped (started start).state ∧
      Nonempty (Generated start (started start) 0 [] []) ∧
      SiteLineage graph owners .none action := by
  have extension : HeapExtends base.heap bodyEnd.heap := by
    have produced := steps_heap_extends bodySteps
    exact produced
  let installed := registration.installed.heap_weaken extension
  let history := registration.history.heap_weaken extension
  obtain ⟨actual,_ownership,running,sameInstalled,_history⟩ :=
    normal_start_history installed saved history bounded data.scope
  let start : RunningStartPast graph owners action environment data savedValue savedCode physical target :=
    ⟨bodyEnd,callerOwners,data.scope,installed,saved,history,running,sameInstalled,actual⟩
  have same : returnedState bodyEnd savedValue (.cleanupBoundary action environment data.identity :: physical) = bodyEnd := by
    simp only [returnedState]
    rw [← returned,← physicalSame]
  have core := actual.core
  rw [same] at core
  exact ⟨start,⟨bodySteps,returned,physicalSame,extension,HEq.rfl,HEq.rfl⟩,
    core,⟨.initial⟩,.inactive (CoreCallableCleanupOrigins.CurrentScopeOrigin.canonical registration.installed.origin)⟩

/-- Active original caller ancestry survives start, while current callback
invocation uses the inactive scope at SAME Generated.initial endpoint. -/
theorem StartedFrom.original_and_current_sites
    (registration : RegisteredCleanupPast graph owners base site callback action body environment data physical target)
    (start : RunningStartPast graph owners action environment data savedValue savedCode physical target)
    (linked : StartedFrom registration start count) :
    start.installed.origin = registration.installed.origin ∧
    SiteLineage graph owners data.scope body ∧
    SiteLineage graph owners data.scope action ∧
    (started start).state.control = .evaluate action environment ∧
    (started start).focus.scope = .none ∧
    SiteLineage graph owners .none action := by
  have installedEq := eq_of_heq linked.installedSame
  exact ⟨congrArg SavedCleanupOrigin.origin installedEq,registration.body_site,registration.action_site,rfl,rfl,
    .inactive (CoreCallableCleanupOrigins.CurrentScopeOrigin.canonical registration.installed.origin)⟩

/-- Prefix composition follows actual body steps; no saved registration state
can be attached to an unrelated current callback invocation. -/
theorem steps_prepend_one (first : CoreMachine.Step graph before middle)
    (steps : CoreAllocationHistory.Steps graph count middle after) :
    CoreAllocationHistory.Steps graph (count+1) before after := by
  induction steps with
  | refl => exact .snoc (.refl _) first
  | snoc earlier step ih => exact .snoc (ih first) step

theorem StartedFrom.registration_to_invocation
    (registration : RegisteredCleanupPast graph owners base site callback action body environment data physical target)
    (start : RunningStartPast graph owners action environment data savedValue savedCode physical target)
    (linked : StartedFrom registration start count) :
    CoreAllocationHistory.Steps graph (count+2)
      {base with control := .evaluate site environment,frames := physical} (started start).state := by
  have recordedSteps := steps_prepend_one registration.actual linked.bodySteps
  have actual := start.actual.core
  have same : returnedState start.predecessor savedValue
      (.cleanupBoundary action environment data.identity :: physical) = start.predecessor := by
    simp only [returnedState]
    rw [← linked.returned,← linked.physicalSame]
  rw [same] at actual
  exact .snoc recordedSteps actual

#print axioms register_with_sites
#print axioms RegisteredCleanupPast.body_site
#print axioms RegisteredCleanupPast.action_site
#print axioms RegisteredCleanupPast.body_not_caller_reentry
#print axioms steps_heap_extends
#print axioms start_registered
#print axioms StartedFrom.original_and_current_sites
#print axioms steps_prepend_one
#print axioms StartedFrom.registration_to_invocation
end Ash.OneShot.CoreCallableGeneratedCleanupRegistration
