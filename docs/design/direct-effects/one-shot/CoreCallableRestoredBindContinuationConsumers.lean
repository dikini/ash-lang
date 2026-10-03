import CoreCallableRestoredBindContinuationOrigins
namespace Ash.OneShot.CoreCallableRestoredBindContinuationConsumers
open CoreSyntax CoreMachine CoreTranslation CoreValueRelation CoreStrictFrames CoreStrictStack
open ScopedExpressions ScopedExecution CoreCallableGeneralHistory CoreCallableGeneratedChronology
open CoreCallableReachableResume CoreCallableSiteLineage CoreCallableCallerBarriers
open CoreCallableRestoredBindContinuationOrigins CoreGeneralCaptureResume CoreResumeFrames

/-- Internal consumer of a live occurrence produced from original capture and
transport. Current control/maps/operand remain actual shape guards. The
selected full location and successor are computed, never supplied. -/
noncomputable def resume_live_result {graph : Graph} {current : Endpoint graph}
    (path : OwnerPath handler owner occurrence dynamicTicket (some saved) current.physical front outside)
    (plain : PlainData) (frameOwners : OwnerMap)
    (frame : ResumeRel graph frameOwners current.state.heap (.resume handler owner) plain)
    (context : plain.context = .resume (ticket graph owner))
    (scope : plain.scope = .ticket (ticket graph owner) dynamicTicket)
    (operand : ValueRel graph current.owners current.state.heap value code)
    (control : current.state.control = .returned value)
    (maps : current.maps = [(frameOwners,.resume handler owner)])
    (focus : current.focus = ⟨.resume (ticket graph owner) code,plain.scope,.nil⟩) :
    Result current [] [.ticket dynamicTicket] := by
  let selected := owner_from_live_path current.history path
  have sameTicket : selected.dynamicTicket = dynamicTicket := owner_from_live_path_ticket current.history path
  let after : Endpoint graph := {
    state := resumeAfter current.state handler owner selected.occurrence selected.dynamicTicket value
      selected.captured selected.front selected.outside
    focus := ⟨code,plain.scope,.nil⟩,owners := current.owners,maps := []
    physical := selected.captured ++ (selected.front ++
      .clauseBoundary handler owner selected.occurrence selected.dynamicTicket none :: selected.outside)
    lexical := selected.capturedTarget.append (selected.frontTarget.append
      (.spent selected.dynamicTicket selected.data.answer selected.data.scope selected.tail))
    history := selected.restored_history
    frames := by simp [resumeAfter,List.append_assoc,framesOf] }
  have resolve : plain.scope.resolve (ticket graph owner) = some selected.dynamicTicket := by
    rw [scope,sameTicket]; simp [Execution.Scope.resolve]
  have actual := resume_general selected.cut frame context operand resolve plain.scope
  have frames : current.state.frames = .resume handler owner :: current.physical := by
    simpa [maps,framesOf] using current.frames
  have beforeSame : resumeBefore current.state handler owner value current.physical = current.state := by
    simp only [resumeBefore]; rw [← frames,← control]
  refine ⟨after,?_,.positive ?_⟩
  · simpa only [beforeSame] using actual.core
  · simpa only [Endpoint.point,focus,CoreCleanupRunFrames.attach,Stack.append,after,sameTicket] using actual.target

/-- Return through a handler chosen from the actual structural inventory.
Only current empty prefix and returned-control guards are inputs. The full
handler installation, header and tail are outputs of the inventory. -/
noncomputable def handler_inventory_result {graph : Graph} {current : Endpoint graph}
    (index : Fin (handler_locations current.history).length)
    (inside : (location current index).inside = [])
    (front : (location current index).front = .nil)
    (operand : ValueRel graph current.owners current.state.heap value code)
    (control : current.state.control = .returned value)
    (empty : EmptyFocus current code scope) : Result current [] [] := by
  let selected := location current index
  let after : Endpoint graph := {
    state := {current.state with frames := selected.outside}
    focus := ⟨code,selected.data.scope,.nil⟩,owners := selected.owners,maps := []
    physical := selected.outside,lexical := selected.tail,history := selected.after,frames := rfl }
  have physical : current.physical = .handlerBoundary selected.site selected.environment selected.data.activation :: selected.outside := by
    simpa only [selected,inside,List.nil_append] using selected.physicalSame
  have lexical : current.lexical = .push (.handler selected.data) selected.tail := by
    simpa only [selected,front,Stack.append] using selected.targetSame
  have actual := CoreEffectEntry.handler_leave selected.header operand scope selected.outside selected.tail
  have frames : current.state.frames = current.physical := by simpa only [empty.maps,framesOf,List.map_nil,List.nil_append] using current.frames
  have beforeSame : { current.state with
      control := .returned value
      frames := .handlerBoundary selected.site selected.environment selected.data.activation :: selected.outside} = current.state := by
    rw [← physical,← frames,← control]
  refine ⟨after,?_,.positive ?_⟩
  · have core := actual.1
    rw [beforeSame] at core
    simpa only [after,← control] using core
  · have before : current.point.machine = .eval ⟨code,scope,current.lexical⟩ := by
      simp only [Endpoint.point,empty.focus,CoreCleanupRunFrames.attach,Stack.append]
    rw [before,lexical]
    exact .one (.evaluate actual.2.1 (by
      have value := operand.closed.1
      cases code <;> simp_all [LexicalUnwind.ordinary,Code.IsValue]))

/-- The spent receipt is computed from the actual history and static physical
head. No independently selected original metadata or successor is an input. -/
noncomputable def spent_physical_result {graph : Graph} {current : Endpoint graph}
    (physical : current.physical = .clauseBoundary handler owner occurrence dynamicTicket none :: rest)
    (emptyLeading : (spent_position current.history physical).prefixTarget = .nil)
    (operand : ValueRel graph current.owners current.state.heap value code)
    (control : current.state.control = .returned value)
    (empty : EmptyFocus current code scope) : Result current [] [] := by
  let selected := spent_position current.history physical
  let after : Endpoint graph := {
    state := CoreGeneralRestoration.observedState current.state value selected.tailPhysical (.clauseReturned dynamicTicket)
    focus := ⟨code,selected.data.scope,.nil⟩,owners := selected.owners,maps := []
    physical := selected.tailPhysical,lexical := selected.tailTarget,history := selected.tail,frames := rfl }
  have lexical : current.lexical = .spent dynamicTicket selected.data.answer selected.data.scope selected.tailTarget := by
    simpa only [selected,emptyLeading,Stack.append] using selected.targetSame
  have actual := CoreGeneralRestoration.leave_clause (base := current.state) selected.header operand selected.tail.related dynamicTicket scope
  have frames : current.state.frames = current.physical := by simpa only [empty.maps,framesOf,List.map_nil,List.nil_append] using current.frames
  have beforeSame : CoreGeneralRestoration.returnedState current.state value
      (.clauseBoundary handler owner occurrence dynamicTicket none :: selected.tailPhysical) = current.state := by
    simp only [CoreGeneralRestoration.returnedState]
    rw [← selected.physicalSame,← frames,← control]
  refine ⟨after,by simpa only [beforeSame] using actual.core,.positive ?_⟩
  have before : current.point.machine = .eval ⟨code,scope,current.lexical⟩ := by
    simp only [Endpoint.point,empty.focus,CoreCleanupRunFrames.attach,Stack.append]
  rw [before,lexical]
  exact actual.target


/-- Finish the same original running action after its actual outside suffix has
been restored. Immutable start authority and heap growth produce the current
receipt and outside history; current shape and bound guards name no successor. -/
noncomputable def finish_original_result {graph : Graph} {current : Endpoint graph}
    (start : CoreCallableRunningOccurrence.RunningStartPast graph cleanupOwners action environment data
      savedValue savedCode originalPhysical originalTarget)
    (extension : HeapExtends start.predecessor.heap current.state.heap)
    (physical : current.physical = .cleanupCompletion data.identity savedValue :: originalPhysical)
    (lexical : current.lexical = .push (.running data savedCode start.running.value.closed) originalTarget)
    (bounded : TicketBound current.state current.lexical)
    (control : current.state.control = .returned .unit)
    (empty : EmptyFocus current .unit scope) : Result current [] [.cleanup data.identity] := by
  let receipt := start.running.heap_weaken extension
  let outside := start.originalHistory.heap_weaken extension
  let after : Endpoint graph := {
    state := CoreGeneralRestoration.observedState current.state savedValue originalPhysical (.cleanupFinished data.identity)
    focus := ⟨savedCode,data.scope,.nil⟩,owners := cleanupOwners,maps := []
    physical := originalPhysical,lexical := originalTarget,history := outside,frames := rfl }
  have bound : TicketBound current.state (.push (.running data savedCode receipt.value.closed) originalTarget) := by
    simpa only [lexical] using bounded
  have actual := CoreCallableGeneralHistory.normal_finish_history (base := current.state)
    receipt outside bound current.owners scope
  have frames : current.state.frames = current.physical := by
    simpa only [empty.maps,framesOf,List.map_nil,List.nil_append] using current.frames
  have beforeSame : CoreGeneralRestoration.returnedState current.state .unit
      (.cleanupCompletion data.identity savedValue :: originalPhysical) = current.state := by
    simp only [CoreGeneralRestoration.returnedState]
    rw [← physical,← frames,← control]
  refine ⟨after,by simpa only [beforeSame] using actual.1.core,.positive ?_⟩
  simpa only [Endpoint.point,empty.focus,CoreCleanupRunFrames.attach,Stack.append,lexical,after] using actual.1.target

#print axioms finish_original_result

#print axioms spent_physical_result

#print axioms handler_inventory_result

#print axioms resume_live_result
end Ash.OneShot.CoreCallableRestoredBindContinuationConsumers
