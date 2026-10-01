import ScopedNames
import CoreCallableRestoredResume
import CoreResumeReadiness

namespace Ash.OneShot.CoreCallableResumeCorrespondence
open ScopedExpressions ScopedExecution
variable {front nextFront saved nextSaved tail nextTail : Stack}
variable {owner : Nat} {input nextInput answer nextAnswer : Ty}
variable {caller nextCaller : Execution.Scope}

private theorem front_excludes_ticket
    (names : (front.append (.live owner input answer saved caller tail)).erase.ticketNames.Nodup) :
    owner ∉ front.erase.ticketNames := by
  have disjoint := (List.nodup_append.mp (by
    simpa only [erase_append, ticketNames_append, Stack.erase, Control.ticketNames] using names)).2.2
  intro member
  exact disjoint owner member owner (by simp) rfl

/-- A unique current dynamic ticket fixes the full active cut, including dormant
saved continuation and lexical caller metadata. -/
theorem live_cut_unique
    (names : (front.append (.live owner input answer saved caller tail)).erase.ticketNames.Nodup)
    (same : front.append (.live owner input answer saved caller tail) =
      nextFront.append (.live owner nextInput nextAnswer nextSaved nextCaller nextTail)) :
    front = nextFront ∧ input = nextInput ∧ answer = nextAnswer ∧
      saved = nextSaved ∧ caller = nextCaller ∧ tail = nextTail := by
  have absent := front_excludes_ticket names
  have nextNames : (nextFront.append (.live owner nextInput nextAnswer nextSaved nextCaller nextTail)).erase.ticketNames.Nodup := by rw [← same]; exact names
  have nextAbsent := front_excludes_ticket nextNames
  clear names nextNames
  induction front generalizing nextFront with
  | nil =>
    cases nextFront with
    | nil => simpa only [Stack.append, Stack.live.injEq, true_and] using same
    | push frame rest => cases same
    | live ticket q a cap scope rest =>
      have ticketSame : owner = ticket := by injection same
      exact False.elim (nextAbsent (by simp [Stack.erase, Control.ticketNames, ticketSame]))
    | spent ticket a scope rest => cases same
  | push frame rest ih =>
    cases nextFront with
    | nil => cases same
    | push nextFrame nextRest =>
      have eqs : frame = nextFrame ∧ rest.append (.live owner input answer saved caller tail) = nextRest.append (.live owner nextInput nextAnswer nextSaved nextCaller nextTail) := by simpa only [Stack.append, Stack.push.injEq] using same
      have oldAbsent : owner ∉ rest.erase.ticketNames := by intro mem; exact absent (by simp [Stack.erase, Control.ticketNames, mem])
      have newAbsent : owner ∉ nextRest.erase.ticketNames := by intro mem; exact nextAbsent (by simp [Stack.erase, Control.ticketNames, mem])
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := ih eqs.2 oldAbsent newAbsent
      exact ⟨by rw [eqs.1], rfl, rfl, rfl, rfl, rfl⟩
    | live ticket q a cap scope rest => cases same
    | spent ticket a scope rest => cases same
  | live ticket q a cap scope rest _ihSaved ih =>
    cases nextFront with
    | nil =>
      have ticketSame : ticket = owner := by injection same
      exact False.elim (absent (by simp [Stack.erase, Control.ticketNames, ticketSame]))
    | push nextFrame nextRest => cases same
    | live nextTicket nextQ nextA nextCap nextScope nextRest =>
      have eqs := Stack.live.inj same
      have oldAbsent : owner ∉ rest.erase.ticketNames := by intro mem; exact absent (by simp [Stack.erase, Control.ticketNames, mem])
      have newAbsent : owner ∉ nextRest.erase.ticketNames := by intro mem; exact nextAbsent (by simp [Stack.erase, Control.ticketNames, mem])
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := ih eqs.2.2.2.2.2 oldAbsent newAbsent
      exact ⟨by simp_all, rfl, rfl, rfl, rfl, rfl⟩
    | spent ticket a scope rest => cases same
  | spent ticket a scope rest ih =>
    cases nextFront with
    | nil => cases same
    | push nextFrame nextRest => cases same
    | live nextTicket nextQ nextA nextCap nextScope nextRest => cases same
    | spent nextTicket nextA nextScope nextRest =>
      have eqs := Stack.spent.inj same
      have oldAbsent : owner ∉ rest.erase.ticketNames := by intro mem; exact absent (by simp [Stack.erase, Control.ticketNames, mem])
      have newAbsent : owner ∉ nextRest.erase.ticketNames := by intro mem; exact nextAbsent (by simp [Stack.erase, Control.ticketNames, mem])
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := ih eqs.2.2.2 oldAbsent newAbsent
      exact ⟨by simp_all, rfl, rfl, rfl, rfl, rfl⟩

/-- Resume endpoints are unique at a currently named stack. This compares two
actual steps and does not postulate either successor configuration. -/
theorem resume_step_unique {operand : Code} {binder : Nat} {scope : Execution.Scope}
    {stack : Stack} {after otherAfter : Configuration} {owner otherOwner : Nat}
    (names : stack.erase.ticketNames.Nodup)
    (left : RawStep ⟨.resume binder operand, scope, stack⟩ after [] [.ticket owner])
    (right : RawStep ⟨.resume binder operand, scope, stack⟩ otherAfter [] [.ticket otherOwner]) :
    after = otherAfter ∧ owner = otherOwner := by
  cases left with
  | resume _ _ _ caller q a front cap tail _ closed resolved =>
    generalize currentSame : (⟨.resume binder operand, scope, front.append (.live owner q a cap caller tail)⟩ : Configuration) = current at right
    cases right with
    | resume _ _ _ nextCaller nextQ nextA nextFront nextCap nextTail _ nextClosed nextResolved =>
      have currentEq := Configuration.mk.inj currentSame
      obtain ⟨codeSame, scopeSame, stackSame⟩ := currentEq
      obtain ⟨binderSame, operandSame⟩ := Code.resume.inj codeSame
      subst_vars
      have ownerSame : owner = otherOwner := Option.some.inj (resolved.symm.trans nextResolved)
      subst otherOwner
      have cutSame := live_cut_unique names stackSame
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := cutSame
      exact ⟨rfl, rfl⟩
    | retire => cases currentSame

open CoreCallableContractExecution CoreCallableContractAdmission CoreCallableContractRegistries
open CoreGeneralCaptureResume CoreGeneralStack CoreResumeFrames CoreValueRelation CoreUnwindRelation
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourcePlannedChecks

section
variable [DeclarationPolicy]

/-- Current callable admission and actual Core lookup select the same full raw
resume successor at a named stack. The dynamic scope equation is current
Core/Source ownership consistency, not a successor assumption. -/
theorem Site.resume_core_cut
    {receiving : SourceDependencyCapture.Scope}
    {hints : SourceDependencyChecks.Lexical.ReturnHints receiving} {context : Context hints}
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.resume binder operand) plain.scope stack result final context root)
    (names : stack.erase.ticketNames.Nodup)
    (segment : GeneralSegment graph base.heap whole stack)
    (found : CoreMachine.findOwner handler staticOwner whole = .ok ⟨coreFront, handler, staticOwner, occurrence, ticket, captured, outside⟩)
    (frame : ResumeRel graph frameOwners base.heap (.resume handler staticOwner) plain)
    (contextSame : plain.context = .resume binder)
    (value : ValueRel graph owners base.heap coreValue operand)
    (resolve : plain.scope.resolve binder = some ticket) (runtimeScope : Execution.Scope) :
    CoreResumeReadiness.HandlersReady graph captured ∧
    ∃ frontTarget savedOwners data operationResult capturedTarget outsideTarget,
      GeneralOwnerCut graph base.heap handler staticOwner whole stack coreFront frontTarget savedOwners
        occurrence ticket data operationResult captured capturedTarget outside outsideTarget ∧
      GeneralStepWitness graph
        ⟨resumeBefore base handler staticOwner coreValue whole,
          .eval ⟨.resume binder operand, plain.scope, stack⟩, owners, [(frameOwners, .resume handler staticOwner)]⟩
        ⟨resumeAfter base handler staticOwner occurrence ticket coreValue captured coreFront outside,
          .eval ⟨operand, plain.scope, capturedTarget.append (frontTarget.append (.spent ticket data.answer data.scope outsideTarget))⟩,
          owners, []⟩ [] [.ticket ticket] ∧
      RawStep ⟨.resume binder operand, plain.scope, stack⟩
        ⟨operand, plain.scope, capturedTarget.append (frontTarget.append (.spent ticket data.answer data.scope outsideTarget))⟩
        [] [.ticket ticket] := by
  obtain ⟨ready, frontTarget, savedOwners, data, operationResult, capturedTarget, outsideTarget, cut, step⟩ :=
    CoreResumeReadiness.resume_ready_from_lookup segment found frame contextSame value resolve runtimeScope
  obtain ⟨owner, contract, sourceFront, sourceCaptured, sourceTail, input, answer, caller,
    _known, sourceResolved, _answer, sourceShape, _input, _output, raw⟩ := site.resume_raw value.closed
  have ownerSame : owner = ticket := Option.some.inj (sourceResolved.symm.trans resolve)
  subst owner
  have coreShape := cut.realizes.2.1
  have namedSource : (sourceFront.append (.live ticket input answer sourceCaptured caller sourceTail)).erase.ticketNames.Nodup := by rw [← sourceShape]; exact names
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := live_cut_unique namedSource (sourceShape.symm.trans coreShape)
  exact ⟨ready, _, _, _, _, _, _, cut, step, raw⟩
/-- One current admitted resume yields the actual Core step and the same rich
Source successor, with root consumption and the spent-owner phase fixed. -/
theorem Site.resume_correspondence
    {receiving : SourceDependencyCapture.Scope}
    {hints : SourceDependencyChecks.Lexical.ReturnHints receiving} {context : Context hints}
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.resume binder operand) plain.scope stack result final context
      (root : RecursiveRequirements.Requirements rootDemand))
    (names : stack.erase.ticketNames.Nodup)
    (segment : GeneralSegment graph base.heap whole stack)
    (found : CoreMachine.findOwner handler staticOwner whole = .ok ⟨coreFront, handler, staticOwner, occurrence, ticket, captured, outside⟩)
    (frame : ResumeRel graph frameOwners base.heap (.resume handler staticOwner) plain)
    (contextSame : plain.context = .resume binder)
    (value : ValueRel graph owners base.heap coreValue operand)
    (resolve : plain.scope.resolve binder = some ticket) (runtimeScope : Execution.Scope) :
    CoreResumeReadiness.HandlersReady graph captured ∧
    ∃ frontTarget savedOwners data operationResult capturedTarget outsideTarget,
      GeneralOwnerCut graph base.heap handler staticOwner whole stack coreFront frontTarget savedOwners
        occurrence ticket data operationResult captured capturedTarget outside outsideTarget ∧
      GeneralStepWitness graph
        ⟨resumeBefore base handler staticOwner coreValue whole,
          .eval ⟨.resume binder operand, plain.scope, stack⟩, owners, [(frameOwners, .resume handler staticOwner)]⟩
        ⟨resumeAfter base handler staticOwner occurrence ticket coreValue captured coreFront outside,
          .eval ⟨operand, plain.scope, capturedTarget.append (frontTarget.append (.spent ticket data.answer data.scope outsideTarget))⟩,
          owners, []⟩ [] [.ticket ticket] ∧
      RawStep ⟨.resume binder operand, plain.scope, stack⟩
        ⟨operand, plain.scope, capturedTarget.append (frontTarget.append (.spent ticket data.answer data.scope outsideTarget))⟩
        [] [.ticket ticket] ∧
    ∃ contract : OwnerContract,
      globals.owners ticket = some contract ∧ result = contract.answer ∧
      ScopedPorts.eraseType operationResult = contract.input.port ∧
      ScopedPorts.eraseType data.answer = contract.answer.port ∧
    ∃ nextDemand, ∃ nextRoot : RecursiveRequirements.Requirements nextDemand,
      rootDemand = ticket :: nextDemand ∧
    ∃ nextAllowed, ∃ restored : Packed,
    ∃ _successor : Site globals outward world nextAllowed actions
        (OwnerPhaseTransitions.spend phases ticket) budget ambient installations operand plain.scope
        (capturedTarget.append (frontTarget.append (.spent ticket data.answer data.scope outsideTarget)))
        contract.input final restored.context nextRoot,
      (resumeAfter base handler staticOwner occurrence ticket coreValue captured coreFront outside).observations =
        base.observations ++ [.resumed ticket] ∧
      stack.erase.owners.Perm
        ((capturedTarget.append (frontTarget.append (.spent ticket data.answer data.scope outsideTarget))).erase.owners ++ [.ticket ticket]) := by
  obtain ⟨ready, frontTarget, savedOwners, data, operationResult, capturedTarget, outsideTarget,
    cut, step, coreRaw⟩ := Site.resume_core_cut site names segment found frame contextSame value resolve runtimeScope
  obtain ⟨sourceOwner, contract, sourceFront, sourceCaptured, sourceTail, input, answer, caller,
    known, sourceResolved, resultAnswer, sourceShape, inputPort, answerPort,
    nextDemand, nextRoot, rootSame, nextAllowed, restored, successor, sourceRaw⟩ := site.resume value.closed
  have endpoints := resume_step_unique names sourceRaw coreRaw
  have ownerSame := endpoints.2
  subst sourceOwner
  have coreShape := cut.realizes.2.1
  have namedSource : (sourceFront.append (.live ticket input answer sourceCaptured caller sourceTail)).erase.ticketNames.Nodup := by rw [← sourceShape]; exact names
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := live_cut_unique namedSource (sourceShape.symm.trans coreShape)
  refine ⟨ready, _, _, _, _, _, _, cut, step, coreRaw, contract, known, resultAnswer,
    inputPort, answerPort, nextDemand, nextRoot, rootSame, nextAllowed, restored, successor, rfl, ?_⟩
  simpa [LexicalUnwind.Machine.stack] using step.accounting
end

#print axioms live_cut_unique
#print axioms resume_step_unique
#print axioms Site.resume_core_cut
#print axioms Site.resume_correspondence
end Ash.OneShot.CoreCallableResumeCorrespondence
