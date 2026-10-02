import CoreCallableRunningClauseOccurrence
namespace Ash.OneShot.CoreCallableRunningLocalHandler
open CoreSyntax CoreTranslation CoreMachine CoreValueRelation CoreStrictFrames CoreStrictStack
open ScopedExpressions ScopedExecution CoreGeneralStack CoreGeneralCaptureResume CoreGeneralRestoration
open CoreCallableReachableResume CoreCallableCleanupOrigins CoreCallableCleanupReachableTransport
open CoreCallableGeneralHistory CoreCallableCallerBarriers CoreCallableSiteLineage
open CoreCallableRunningOccurrence CoreCallableRunningCapture CoreCallableRunningClauseOccurrence
open CoreCaptureEntry CoreRequestFrames CoreEffectFrames

/-- A local installation retains the SAME produced clause occurrence suffix. -/
structure LocalHandlerEntry
    {start : RunningStartPast graph cleanupOwners action environment actionData savedValue savedCode originalPhysical originalTarget}
    {original : RunningOccurrence start originalHeap originalFrames originalStack}
    {index : Fin (handler_locations original.tailHistory).length}
    {captured : CapturedOccurrence original index selectedClause dynamicTicket}
    (current : ClauseOccurrence captured result heap)
    (owners : OwnerMap) (site : Nat) (environment : Environment) (data : HandlerData) where
  installation : GeneralHandlerPast graph owners site environment data
  extension : HeapExtends installation.predecessor.heap heap
  sameSuffix : installation.originalSuffix = current.physical
  boundary : BoundaryRel graph owners heap (.handlerBoundary site environment data.activation) (.handler data)
  sameBoundary : boundary = installation.header.heap_weaken extension

section
variable {start : RunningStartPast graph cleanupOwners action originalEnvironment actionData savedValue savedCode originalPhysical originalTarget}
variable {original : RunningOccurrence start originalHeap originalFrames originalStack}
variable {index : Fin (handler_locations original.tailHistory).length}
variable {captured : CapturedOccurrence original index originalSelectedClause dynamicTicket}

noncomputable def LocalHandlerEntry.history
    {current : ClauseOccurrence (graph := graph) captured result heap}
    (entry : LocalHandlerEntry (graph := graph) (heap := heap) current owners site environment data) :
    GeneralHistory graph heap (.handlerBoundary site environment data.activation :: current.physical)
      (.push (.handler data) current.target) :=
  .handler entry.installation entry.boundary current.history

theorem handler_enter {base : CoreMachine.State}
    (current : ClauseOccurrence (graph := graph) captured result base.heap)
    (postorder : CoreTranslationFuel.Postorder graph)
    (lineage : SiteLineage graph owners data.scope site)
    (origin : CurrentScopeOrigin graph owners data.scope current.physical)
    (known : graph.node site = some node) (kind : node.kind = .handler literalHandler effect body clauses)
    (translated : translateFuel graph fuel owners site = .ok (.handle effect rawBody rawClauses))
    (bodyTranslated : translateFuel graph bodyFuel owners body = .ok rawBody)
    (lexical : EnvCloses graph owners base.heap environment (.handle effect rawBody rawClauses)
      (.handle (Instantiation.freezeEffect data.effectInst) bodyCode data.clauses))
    (activation : data.activation = base.nextHandler) :
    ∃ entry : LocalHandlerEntry (graph := graph) (heap := base.heap) current owners site environment data,
      entry.installation.predecessor = base ∧ entry.installation.originalMaps = none ∧
      CoreMachine.next graph {base with control := .evaluate site environment,frames := current.physical} =
        .stepped {base with control := .evaluate body environment, frames := .handlerBoundary site environment data.activation :: current.physical, nextHandler := base.nextHandler + 1, observations := base.observations ++ [.entered site,.handlerEntered site data.activation]} ∧
      RawStep ⟨.handle (Instantiation.freezeEffect data.effectInst) bodyCode data.clauses,data.scope,current.target⟩
        ⟨bodyCode,data.scope,.push (.handler data) current.target⟩ [] [] ∧
      SiteLineage graph owners data.scope body := by
  obtain ⟨installation,pred,suffix,maps,_,actual,raw,bodySite⟩ := handler_enter_history
    postorder lineage origin current.history known kind translated bodyTranslated lexical activation
  have sameHeap := congrArg CoreMachine.State.heap pred
  have boundary : BoundaryRel graph owners base.heap
      (.handlerBoundary site environment data.activation) (.handler data) := by
    simpa only [sameHeap] using installation.header
  have extension : HeapExtends installation.predecessor.heap base.heap := by
    intro i cell found
    simpa only [sameHeap] using found
  have sameBoundary : boundary = installation.header.heap_weaken extension := Subsingleton.elim _ _
  exact ⟨⟨installation,extension,suffix,boundary,sameBoundary⟩,pred,maps,actual,raw,bodySite⟩

noncomputable def LocalHandlerEntry.heap_weaken
    {current : ClauseOccurrence (graph := graph) captured result heap}
    (entry : LocalHandlerEntry (graph := graph) (heap := heap) current owners site environment data)
    (extension : HeapExtends heap largerHeap) :
    LocalHandlerEntry (graph := graph) (heap := largerHeap) (current.heap_weaken extension) owners site environment data := {
  installation := entry.installation
  extension := fun index cell found => extension index cell (entry.extension index cell found)
  sameSuffix := entry.sameSuffix
  boundary := entry.boundary.heap_weaken extension
  sameBoundary := Subsingleton.elim _ _ }

/-- Normal local return restores the SAME actual installed boundary suffix. -/
theorem LocalHandlerEntry.handler_return {base : CoreMachine.State}
    {current : ClauseOccurrence (graph := graph) captured result base.heap}
    (entry : LocalHandlerEntry (graph := graph) (heap := base.heap) current owners site environment data)
    (value : ValueRel graph codeOwners base.heap coreValue code) (runtimeScope : Execution.Scope) :
    CoreMachine.next graph {base with control := .returned coreValue, frames := .handlerBoundary site environment data.activation :: current.physical} =
      .stepped {base with control := .returned coreValue,frames := current.physical} ∧
    RawStep ⟨code,runtimeScope,.push (.handler data) current.target⟩
      ⟨code,data.scope,current.target⟩ [] [] ∧
    ValueRel graph owners base.heap coreValue code ∧
    CurrentScopeOrigin graph owners data.scope current.physical ∧
    Nonempty (GeneralHistory graph base.heap current.physical current.target) := by
  obtain ⟨actual,raw,saved⟩ := CoreEffectEntry.handler_leave entry.boundary value runtimeScope current.physical current.target
  exact ⟨actual,raw,saved,entry.sameSuffix ▸ entry.installation.origin,⟨current.history⟩⟩

noncomputable def LocalHandlerEntry.head_index
    {current : ClauseOccurrence (graph := graph) captured result heap}
    (entry : LocalHandlerEntry (graph := graph) (heap := heap) current owners site environment data) :
    Fin (handler_locations entry.history).length :=
  ⟨0,by simp [LocalHandlerEntry.history,handler_locations]⟩

/-- All complete local selection data and the outside history are projected
from the SAME installed head, not from an independently chosen cut. -/
theorem LocalHandlerEntry.location_data
    {current : ClauseOccurrence (graph := graph) captured result heap}
    (entry : LocalHandlerEntry (graph := graph) (heap := heap) current owners site environment data) :
    let location := (handler_locations entry.history)[entry.head_index]
    location.inside = [] ∧ location.front = .nil ∧ location.site = site ∧
    location.environment = environment ∧ location.data = data ∧
    location.installation = entry.installation ∧ location.header = entry.boundary ∧
    location.outside = current.physical ∧ location.tail = current.target ∧
    HEq location.after current.history := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,HEq.rfl⟩

theorem LocalHandlerEntry.capture {base : CoreMachine.State}
    {current : ClauseOccurrence (graph := graph) captured result base.heap}
    (entry : LocalHandlerEntry (graph := graph) (heap := base.heap) current owners site environment data) :
    let location := (handler_locations entry.history)[entry.head_index]
    ∀ (same : location.data.effectInst = requested)
      (prefixScope : SourceRecursiveRoutes.Scope context location.front.erase)
      (route : SourceResourceRoutes.Route outward context requested none)
      (lookup : CoreMachine.findInterpreter graph (Instantiation.freezeEffect requested)
        (.handlerBoundary site environment data.activation :: current.physical) =
        .ok (.handler location.inside location.site location.environment location.data.activation location.outside))
      (selected : location.installation.clauses.find? (fun clause => clause.operation == operation) = some selectedClause)
      (operand : ValueRel graph operandOwners base.heap value operandCode)
      (requestCarrier : EnvCloses graph operandOwners base.heap requestEnvironment
        (.perform effect operation .unit) (.perform (Instantiation.freezeEffect requested) operation .unit))
      (plain : PlainData) (context : plain.context = .perform (Instantiation.freezeEffect requested) operation)
      (ready : ∀ parameter binder body, ClauseAt operation location.data.clauses parameter binder body → ClosedExcept parameter body)
      (operationResult : Ty) (runtimeScope : Execution.Scope),
    ∃ (fuel : Nat) (argument : Binder) (rawBody body : Code),
      selectedClause.argument = .binder argument ∧
      ClauseAt operation location.data.clauses argument.id (CoreTranslation.ticket graph selectedClause.owner) body ∧
      translateFuel graph fuel
        (⟨location.installation.handler,selectedClause.owner,CoreTranslation.ticket graph selectedClause.owner⟩ :: location.owners)
        selectedClause.body = .ok rawBody ∧
      EnvCloses graph
        (⟨location.installation.handler,selectedClause.owner,CoreTranslation.ticket graph selectedClause.owner⟩ :: location.owners)
        base.heap (.binding argument.id value location.environment) rawBody (body.subst argument.id operandCode) ∧
      GeneralStepWitness graph
        ⟨captureBefore base value effect operation requestEnvironment (.handlerBoundary site environment data.activation :: current.physical),
          .eval ⟨.perform (Instantiation.freezeEffect requested) operation operandCode,plain.scope,.push (.handler data) current.target⟩,
          operandOwners,[(operandOwners,.request effect operation requestEnvironment)]⟩
        ⟨captureAfter base selectedClause argument.id value location.installation.handler location.data.activation
          location.site location.environment location.inside location.outside,
          .eval ⟨body.subst argument.id operandCode,.ticket (CoreTranslation.ticket graph selectedClause.owner) base.nextOwner,
            .live base.nextOwner operationResult location.data.answer
              (location.front.append (.push (.handler location.data) .nil)) location.data.scope location.tail⟩,
          ⟨location.installation.handler,selectedClause.owner,CoreTranslation.ticket graph selectedClause.owner⟩ :: location.owners,[]⟩
          [.ticket base.nextOwner] [] ∧
      ∃ (installation : GeneralClausePast graph location.owners location.installation.handler selectedClause.owner
            location.data.activation base.nextOwner
            (location.inside ++ [.handlerBoundary location.site location.environment location.data.activation]) location.data)
        (header : OwnerHeader graph location.owners base.heap location.installation.handler selectedClause.owner location.data.activation location.data)
        (successor : GeneralHistory graph base.heap
          (.clauseBoundary location.installation.handler selectedClause.owner location.data.activation base.nextOwner
            (some (location.inside ++ [.handlerBoundary location.site location.environment location.data.activation])) :: location.outside)
          (.live base.nextOwner operationResult location.data.answer
            (location.front.append (.push (.handler location.data) .nil)) location.data.scope location.tail)),
        installation.site = location.site ∧ installation.environment = location.environment ∧
        HEq installation.installation location.installation ∧ installation.selected = selectedClause ∧
        installation.originalInside = location.inside ∧ installation.originalOutside = location.outside ∧
        successor = .live installation header
          (.append location.before (.handler location.installation location.header .nil)) location.after := by
  exact capture_history entry.history entry.head_index

#print axioms LocalHandlerEntry.history
#print axioms handler_enter
#print axioms LocalHandlerEntry.heap_weaken
#print axioms LocalHandlerEntry.handler_return
#print axioms LocalHandlerEntry.head_index
#print axioms LocalHandlerEntry.location_data
#print axioms LocalHandlerEntry.capture

end
end Ash.OneShot.CoreCallableRunningLocalHandler
