import SourceScheduledInstallationMachine
namespace Ash.OneShot.SourceDependencyCapture
open ScopedExpressions ScopedExecution ProtectionContracts

private theorem selection_prepend_handler
    (found : selected.map (Selection.prepend layer) = some (.handler captured tail contract modes)) :
    ∃ first, selected = some (.handler first tail contract modes) ∧ captured = layer first := by
  cases selected with
  | none => cases found
  | some selected => cases selected with
    | builtin => cases found
    | handler first rest offered families =>
      cases found
      exact ⟨first, rfl, rfl⟩

/-- A successful lexical selection recovers its actual runtime handler cut.
The selected capture and suffix keep exactly the same source-scope indices. -/
theorem Realizes.selected_handler_cut
    (source : Realizes tables families scope whole)
    (selected : select effect operation scope = some (.handler capturedScope tailScope contract modes)) :
    ∃ captured tail handler,
      HandlerCut effect whole captured tail handler ∧
      Realizes tables families capturedScope captured ∧
      Realizes tables families tailScope tail := by
  induction source generalizing capturedScope tailScope with
  | nil => cases selected
  | @push layer entry rest stack frame source ih =>
    by_cases hit : entry.erase.target = some effect
    · cases frame with
      | @handler data =>
        simp only [ExecFrame.erase, HandlerData.erase, Ash.OneShot.Frame.target, Option.some.injEq] at hit
        subst effect
        cases offered : lookup operation (tables data) <;>
          cases dependencies : lookupDependencies operation (families data) <;>
          simp [select, offered, dependencies] at selected
        rcases selected with ⟨rfl, rfl, rfl, rfl⟩
        exact ⟨_, _, _, .hit _ _ rfl, .push .handler .nil, source⟩
      | cell =>
        simp only [ExecFrame.erase, Ash.OneShot.Frame.target, Option.some.injEq] at hit
        subst effect
        simp [select] at selected
      | plain | cleanup | running | unwinding | closing | retiring => cases hit
    · rw [frame.select_miss hit] at selected
      obtain ⟨first, found, rfl⟩ := selection_prepend_handler selected
      obtain ⟨captured, tail, handler, cut, inside, outside⟩ := ih found
      exact ⟨_, _, handler, .push _ _ _ _ _ hit cut, .push frame inside, outside⟩
  | live saved rest ihSaved ihRest =>
    obtain ⟨first, found, rfl⟩ := selection_prepend_handler selected
    obtain ⟨captured, tail, handler, cut, inside, outside⟩ := ihRest found
    exact ⟨_, _, handler, .live _ _ _ _ _ _ _ _ _ cut, .live saved inside, outside⟩
  | spent rest ih =>
    obtain ⟨first, found, rfl⟩ := selection_prepend_handler selected
    obtain ⟨captured, tail, handler, cut, inside, outside⟩ := ih found
    exact ⟨_, _, handler, .spent _ _ _ _ _ _ _ cut, .spent inside, outside⟩

end Ash.OneShot.SourceDependencyCapture
#print axioms Ash.OneShot.SourceDependencyCapture.Realizes.selected_handler_cut


namespace Ash.OneShot.ScopedExecution
open ScopedExpressions

private theorem append_handler_ne_nil (front : Stack) (handler : HandlerData) :
    front.append (.push (.handler handler) .nil) ≠ .nil := by
  cases front <;> simp [Stack.append]

private theorem HandlerCut.capture_ne_nil
    (cut : HandlerCut requested whole captured tail handler) : captured ≠ .nil := by
  cases cut <;> intro impossible <;> cases impossible

/-- The cut's terminal physical handler agrees with any explicit decomposition
of that same captured stack ending in one handler frame. -/
theorem HandlerCut.terminal_handler_eq
    {front : Stack} {handler : HandlerData}
    (cut : HandlerCut requested whole captured tail actual)
    (same : captured = front.append (.push (.handler handler) .nil)) : actual = handler := by
  induction cut generalizing front with
  | hit selected rest effectSame =>
    cases front with
    | nil => cases same; rfl
    | push frame rest =>
      have impossible := (Stack.push.inj same).2.symm
      exact False.elim (append_handler_ne_nil rest handler impossible)
    | live | spent => cases same
  | push frame rest captured tail actual miss cut ih =>
    cases front with
    | nil => exact False.elim (cut.capture_ne_nil (Stack.push.inj same).2)
    | push entry next => exact ih (Stack.push.inj same).2
    | live | spent => cases same
  | live owner input answer saved caller rest captured tail actual cut ih =>
    cases front with
    | live ticket q a dormant scope next => exact ih (Stack.live.inj same).2.2.2.2.2
    | nil | push | spent => cases same
  | spent owner answer caller rest captured tail actual cut ih =>
    cases front with
    | spent ticket a scope next => exact ih (Stack.spent.inj same).2.2.2
    | nil | push | live => cases same

end Ash.OneShot.ScopedExecution
#print axioms Ash.OneShot.ScopedExecution.HandlerCut.terminal_handler_eq


namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyChecks.Lexical (ReturnHints)

/-- The selected source cut is the physical cut of the same retained split and
terminal handler. No runtime cut or future transition is assumed. -/
theorem CaptureSourceAt.handler_cut
    {site : ExecutionSite ambient operations policy contracts tables families required outward actions phases world installations
      resumes budget ports owners emptyRows output outputRows}
    {captureHints : ReturnHints captureScope} {tailHints : ReturnHints tailScope}
    {captured : Context captureHints} {tail : Context tailHints}
    {front : Stack} {handler : HandlerData}
    (split : CaptureSourceAt site captured tail)
    (cut : Cut effect operation site.context captured tail contract modes)
    (terminal : split.capturedStack = front.append (.push (.handler handler) .nil)) :
    HandlerCut effect site.stack split.capturedStack split.tailStack handler := by
  obtain ⟨actualCaptured, actualTail, actualHandler, physical, saved, waiting⟩ :=
    site.pending.realizes.selected_handler_cut cut.select_sound
  obtain ⟨sameCaptured, sameTail⟩ := realized_append_stacks_unique saved split.savedSource.realizes
    ((handler_cut_reconstructs physical).symm.trans split.stackSplit)
  rw [sameCaptured, sameTail] at physical
  exact (physical.terminal_handler_eq terminal) ▸ physical

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.CaptureSourceAt.handler_cut

namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Contract)
open SourcePlanSignatures (Signature)
open SourceDependencyAnnotations (Dependencies)
open SourceDependencyChecks.Lexical (ReturnHints)
open RecursiveRequirements (Requirements Checked)
open SourceDependencySchemes.Closing (Bound)
open OwnerPhaseTransitions (available introduce)

private theorem ModeRowsValue.Answer.capture_returns
    {answerRows : ValueRows answer} {boundaryRows : ModeRowsValue boundary}
    (aligned : ModeRowsValue.Answer answerRows boundaryRows) :
    boundary = .value answer ∨ boundary = .unwind := by
  cases aligned <;> simp

private theorem ExecutableState.capture_at_site
    {site : ExecutionSite ambient operations policy contracts tables families required outward actions phases world installations
      resumes budget ports owners emptyRows output outputRows}
    {captureHints : ReturnHints captureScope} {tailHints : ReturnHints tailScope}
    {captured : Context captureHints} {tail : Context tailHints}
    {family : Nat → Dependencies} {bodies : ∀ owner, Signature (family owner)}
    {bodyRows : ∀ owner, Rows (bodies owner)}
    (split : CaptureSourceAt site captured tail)
    (selected : CapturedClauseRows effect operation captureScope.held captured bodyRows)
    (expression : site.expression = .perform (Instantiation.freezeEffect effect) operation operand)
    (closed : ClosedValue operand)
    (owner : Nat)
    (cut : Cut effect operation site.context captured tail selectedContract modes)
    (resumeRow : Footprint) (closeRow : Option Footprint)
    (rooted : ExecutionRoot operations policy contracts tables families required outward actions phases world installations
      resumes budget ports owners emptyRows output outputRows site (root : Requirements demand))
    (phaseAgreement : phases = available site.context.owned)
    (checked : Checked (annotateDisposalStore annotatedStore) [] phases (annotateDisposals root) budgetRow)
    (bounded : budgetRow ⊆ budget)
    (bound : Bound annotations site.receiving)
    (state : ExecutableState operations policy contracts tables families required outward annotations world ambient installations
      resumes disposals annotatedStore budget ports owners emptyRows output outputRows
      ⟨⟨.eval ⟨site.expression, site.runtimeScope, site.stack⟩, issued, completed⟩, actions⟩)
    (fresh : (issued ++ [Owner.ticket owner]).Nodup)
    (support : Supported (ParameterSensitiveBoundary.stackView operations site.stack) ambient) :
    ∃ frontStack : Stack, ∃ handler : HandlerData, ∃ answer residual parameter binder code offered row,
    ∃ answerRows : ValueRows answer, ∃ resumeEffects closeEffects,
    let allocated : Contract :=
      ⟨site.result, answer, captureScope.held, split.savedDemand, resumeRow,
        split.savedDemand, closeRow, resumeEffects, closeEffects⟩
    ∃ next : ExecutionSite ambient operations policy (contracts.insert owner allocated) tables families required outward
      (actions.insert owner code.requiredActions) (OwnerPhaseTransitions.introduce phases owner) world installations
      ((⟨owner, .resume⟩, ⟨split.savedDemand, split.savedRequirements⟩) :: resumes)
      budget ports (owners.insert owner site.resultRows answerRows) emptyRows output outputRows,
      split.capturedStack = frontStack.append (.push (.handler handler) .nil) ∧
      handler.effectInst = effect ∧
      ModeRowsValue.Answer answerRows split.boundaryRows ∧
      ClauseAt operation handler.clauses parameter binder code ∧
      ClosedExcept parameter code ∧
      lookup operation (tables handler) = some offered ∧ offered.row captureScope.held = some row ∧
      (code.requiredActions.resume = true → resumeEffects = residual) ∧
      (code.requiredActions.dispose = true → closeEffects = residual) ∧
      next.expression = code.subst parameter operand ∧ next.runtimeScope = .ticket binder owner ∧
      next.stack = .live owner (ScopedPorts.embedPort site.result.erase.erase.port) handler.answer
        split.capturedStack handler.scope split.tailStack ∧
      next.result = answer ∧ next.allowed = residual ∧
      next.context.pack = (Context.live (owner := owner) (resumeDemand := split.savedDemand) captured tail).pack ∧
      next.dependencies = family owner ∧
      HEq (SourcePlanSignatures.signature next.plan) (bodies owner) ∧
      HEq next.rows (bodyRows owner) ∧
      LexicalUnwind.Event
        ⟨.eval ⟨site.expression, site.runtimeScope, site.stack⟩, issued, completed⟩
        ⟨.eval ⟨next.expression, next.runtimeScope, next.stack⟩, issued ++ [.ticket owner], completed⟩ ∧
      ExecutableState operations policy (contracts.insert owner allocated) tables families required outward
        (fun other => if other = owner then some captureScope else annotations other) world ambient installations
        ((⟨owner, .resume⟩, ⟨split.savedDemand, split.savedRequirements⟩) :: resumes) disposals
        ((⟨owner, .resume⟩, ⟨split.savedDemand, split.savedRequirements⟩) :: annotatedStore)
        budget ports (owners.insert owner site.resultRows answerRows) emptyRows output outputRows
        ⟨⟨.eval ⟨next.expression, next.runtimeScope, next.stack⟩, issued ++ [.ticket owner], completed⟩,
          actions.insert owner code.requiredActions⟩ := by
  have freshIssued : Owner.ticket owner ∉ issued := by
    intro member
    exact (List.nodup_append.mp fresh).2.2 _ member _ List.mem_cons_self rfl
  have freshActions : actions owner = none := by
    cases same : actions owner with
    | none => rfl
    | some rights => exact False.elim (freshIssued ((state.registry owner).mp ⟨rights, same⟩))
  have freshContract := (state.captureMetadata.allocated_fresh fresh).1
  have absent := state.allocated_context_ticket_absent site.coherent.forget.source fresh
  have unique : site.context.owned.Nodup :=
    site.coherent.forget.source.owned_permutation.symm.nodup (owned_tickets_unique (ledger_unique_live state.ledger))
  obtain ⟨frontStack, handler, answer, residual, parameter, binder, code, offered, row,
    answerRows, resumeEffects, closeEffects, next,
    stackEq, effectEq, answerMode, located, ready, found, offeredRow, resumeInterface, closeInterface,
    expressionEq, runtimeScopeEq, nextStackEq, resultEq, allowedEq, contextEq,
    dependenciesEq, signatureEq, rowsEq, nextDemand, nextRoot, rootedNext, checkedNext, demandEq⟩ :=
    split.successor_root (nextStore := annotateDisposalStore
      ((⟨owner, .resume⟩, ⟨split.savedDemand, split.savedRequirements⟩) :: annotatedStore))
      (nextReceiving := []) selected expression closed owner freshContract cut freshActions absent resumeRow closeRow
      rooted phaseAgreement unique checked
  let allocated : Contract :=
    ⟨site.result, answer, captureScope.held, split.savedDemand, resumeRow,
      split.savedDemand, closeRow, resumeEffects, closeEffects⟩
  have physical := split.handler_cut cut stackEq
  have returns : split.boundary = .value answer ∨ split.boundary = .unwind :=
    ModeRowsValue.Answer.capture_returns answerMode
  have scopeSame : site.receiving = captureScope.append tailScope := congrArg Packed.scope cut.decomposition
  obtain ⟨nextBound, nextMetadata, nextResumes, nextDisposals, nextAnnotation, _agreement⟩ :=
    capture_record_package (contract := allocated)
      (input := ScopedPorts.embedPort site.result.erase.erase.port) (answer := handler.answer) (caller := handler.scope)
      physical split.savedSource returns scopeSame bound state.captureMetadata fresh freshActions
      state.resumeRecords state.unwindRecords state.storeAnnotation code.requiredActions
  have physicalPhase : phases = available (ownedTickets site.stack) :=
    phaseAgreement.trans (OwnerPhaseTransitions.available_permutation site.coherent.forget.source.owned_permutation)
  have nextPhase : introduce phases owner = available (ownedTickets next.stack) := by
    rw [nextStackEq]
    exact (congrArg (fun p => introduce p owner) physicalPhase).trans
      (OwnerPhaseTransitions.capture_map physical).symm
  have ledger := state.ledger
  rw [expression] at ledger
  have history := state.ticketHistory
  rw [expression] at history
  obtain ⟨event, nextLedger, nextRegistry, nextTicketHistory⟩ :=
    LexicalUnwind.capture_lifetime
      (operationResult := ScopedPorts.embedPort site.result.erase.erase.port)
      physical located closed ready ledger state.registry history fresh code.requiredActions
  have actualEvent : LexicalUnwind.Event
      ⟨.eval ⟨site.expression, site.runtimeScope, site.stack⟩, issued, completed⟩
      ⟨.eval ⟨next.expression, next.runtimeScope, next.stack⟩, issued ++ [.ticket owner], completed⟩ := by
    simpa only [expression, expressionEq, runtimeScopeEq, nextStackEq] using event
  have access : LexicalUnwind.MachineAccess ambient (.eval ⟨next.expression, next.runtimeScope, next.stack⟩) := by
    obtain ⟨requested, argument, known, payload, effectSame, payloadAuth, _resultRows⟩ :=
      site.current.previous.authenticated.request_payload expression closed
    have same : requested = effect := by
      have realization : Instantiation.EffectRealizes Instantiation.Environment.empty
          (Instantiation.freezeEffect effect) requested := by
        rw [effectSame]
        exact Instantiation.frozen_effect_realizes _ _
      exact Instantiation.frozen_effect_cannot_change realization
    subst requested
    cases state.resources with
    | eval current =>
      apply LexicalUnwind.MachineAccess.eval
      simpa only [expressionEq, runtimeScopeEq, nextStackEq] using
        (ParameterSensitiveBoundary.capture_access_from_view (owner := owner)
          (result := ScopedPorts.embedPort site.result.erase.erase.port)
          payloadAuth known closed physical located support current.control)
  have actualBound : Bound
      (fun other => if other = owner then some captureScope else annotations other) next.receiving := by
    have same : next.receiving = .live owner captureScope tailScope := congrArg Packed.scope contextEq
    exact same.symm ▸ nextBound
  have nextState : ExecutableState operations policy (contracts.insert owner allocated) tables families required outward
      (fun other => if other = owner then some captureScope else annotations other) world ambient installations
      ((⟨owner, .resume⟩, ⟨split.savedDemand, split.savedRequirements⟩) :: resumes) disposals
      ((⟨owner, .resume⟩, ⟨split.savedDemand, split.savedRequirements⟩) :: annotatedStore)
      budget ports (owners.insert owner site.resultRows answerRows) emptyRows output outputRows
      ⟨⟨.eval ⟨next.expression, next.runtimeScope, next.stack⟩, issued ++ [.ticket owner], completed⟩,
        actions.insert owner code.requiredActions⟩ := by
    refine ⟨.eval next nextPhase rootedNext actualBound .original checkedNext bounded,
      ?_, ?_, nextAnnotation, ?_, ?_, access, ?_, ?_, ?_, nextMetadata⟩
    · simpa only [LexicalUnwind.Machine.stack, nextStackEq] using nextResumes
    · simpa only [LexicalUnwind.Machine.stack, nextStackEq] using nextDisposals
    · simpa only [expressionEq, runtimeScopeEq, nextStackEq] using nextLedger
    · exact nextRegistry
    · change next.stack.erase.activations ⊆ installations
      rw [nextStackEq]
      intro activation member
      apply state.activations
      change activation ∈ site.stack.erase.activations
      rw [handler_cut_reconstructs physical]
      simpa only [erase_append, Stack.erase, activations_append, Control.activations] using member
    · change ScopedTyping.resourceWorld (issued ++ [.ticket owner]) ⊆ world
      rw [ScopedTyping.resource_world_append]
      simpa only [ScopedTyping.resourceWorld, List.filterMap_cons, List.filterMap_nil, List.append_nil]
        using state.issuedResources
    · simpa only [expressionEq, runtimeScopeEq, nextStackEq] using nextTicketHistory
  exact ⟨frontStack, handler, answer, residual, parameter, binder, code, offered, row,
    answerRows, resumeEffects, closeEffects, next,
    stackEq, effectEq, answerMode, located, ready, found, offeredRow, resumeInterface, closeInterface,
    expressionEq, runtimeScopeEq, nextStackEq, resultEq, allowedEq, contextEq,
    dependenciesEq, signatureEq, rowsEq, actualEvent, nextState⟩

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual

namespace Ash.OneShot.SourceDependencyCapture
open ScopedExpressions ScopedExecution ProtectionContracts

/-- A physical handler selection cannot simultaneously name a builtin cell. -/
theorem Realizes.handler_not_builtin
    (realized : Realizes tables families scope whole)
    (physical : HandlerCut effect whole captured tail handler)
    (found : select effect operation scope = some (.builtin identity)) : False := by
  obtain ⟨_, _, _, _, _, chosenEq⟩ := realized.cut physical
  rw [chosenEq operation] at found
  unfold chosen at found
  cases tableEq : lookup operation (tables handler) <;>
    cases familyEq : lookupDependencies operation (families handler) <;> simp [tableEq, familyEq] at found

end Ash.OneShot.SourceDependencyCapture

namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Contract)
open RecursiveRequirements (Requirements)

/-- Capture constructs its complete successor from the actual predecessor.
The physical cut, operand readiness and fresh ticket are operational premises;
source decomposition, clause checks and installed support are derived. -/
theorem InstallationState.capture_successor_metadata
    (state : InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows output outputRows
      ⟨⟨.eval ⟨.perform (Instantiation.freezeEffect effect) operation operand, runtimeScope, stack⟩,
        issued, completed⟩, actions⟩)
    (physical : HandlerCut effect stack capturedStack tailStack handler)
    (closed : ClosedValue operand)
    (owner : Nat) (fresh : (issued ++ [Owner.ticket owner]).Nodup)
    (resumeRow : Footprint) (closeRow : Option Footprint) :
    ∃ allocated : Contract, ∃ inputRows : ValueRows allocated.input, ∃ answerRows : ValueRows allocated.answer,
    ∃ captureScope : SourceDependencyCapture.Scope,
    ∃ savedRequirements : Requirements allocated.resumeDemand,
    ∃ rights : Syntax.OneShotRights, ∃ next : Configuration,
    ∃ selectedHandler : HandlerData, ∃ selectedCaptured selectedTail : Stack,
    ∃ parameter binder : Nat, ∃ code : Code,
      allocated.resumeRow = resumeRow ∧ allocated.closeRow = closeRow ∧
      HandlerCut effect stack selectedCaptured selectedTail selectedHandler ∧
      ClauseAt operation selectedHandler.clauses parameter binder code ∧
      ClosedExcept parameter code ∧ rights = code.requiredActions ∧
      next.expression = code.subst parameter operand ∧
      next.scope = .ticket binder owner ∧
      next.stack = .live owner (ScopedPorts.embedPort allocated.input.erase.erase.port)
        selectedHandler.answer selectedCaptured selectedHandler.scope selectedTail ∧
      LexicalUnwind.Event
        ⟨.eval ⟨.perform (Instantiation.freezeEffect effect) operation operand, runtimeScope, stack⟩, issued, completed⟩
        ⟨.eval next, issued ++ [.ticket owner], completed⟩ ∧
      InstallationState operations policy (contracts.insert owner allocated) tables families required outward
        (fun other => if other = owner then some captureScope else annotations other) world ambient history
        ((⟨owner, .resume⟩, ⟨allocated.resumeDemand, savedRequirements⟩) :: resumes) disposals
        ((⟨owner, .resume⟩, ⟨allocated.resumeDemand, savedRequirements⟩) :: annotatedStore)
        budget ports (owners.insert owner inputRows answerRows) emptyRows output outputRows
        ⟨⟨.eval next, issued ++ [.ticket owner], completed⟩, actions.insert owner rights⟩ := by
  have source := state.source
  dsimp only at source
  generalize machineEq : LexicalUnwind.Machine.eval
    ⟨.perform (Instantiation.freezeEffect effect) operation operand, runtimeScope, stack⟩ = machine at source
  cases source with
  | eval site phaseAgreement rooted bound annotation checked bounded =>
    obtain ⟨expressionEq, runtimeEq, stackEq⟩ := Configuration.mk.inj (LexicalUnwind.Machine.eval.inj machineEq)
    have currentState : InstallationState operations policy contracts tables families required outward annotations world ambient history
        resumes disposals annotatedStore budget ports owners emptyRows output outputRows
        ⟨⟨.eval ⟨site.expression, site.runtimeScope, site.stack⟩, issued, completed⟩, actions⟩ := by
      simpa only [← expressionEq, ← runtimeEq, ← stackEq] using state
    obtain ⟨requested, input, known, effectEq, _resultRows, primitive, _resource⟩ :=
      checked_request_origin site.current.previous.authenticated expressionEq.symm site.currentResource
    have same := freeze_effect_injective effectEq
    subst requested
    cases primitive with
    | builtin found =>
      have erased := (select_sound effect operation site.context).symm.trans
        (congrArg (Option.map Selection.erase) found)
      exact False.elim (site.pending.realizes.handler_not_builtin (stackEq ▸ physical) erased)
    | request cut guarded callbacks ownerBound cleanupBudget selected terminal rights retained body =>
      rename_i capturedScope tailScope selectedContract modes declarationFamilies activation requiredRights
        capturedHints tailHints captured tail family bodies bodyRows declarations declarationRows
      obtain ⟨split⟩ := site.capture_source cut
      obtain ⟨rootRow, rootCheck, within⟩ := (disposal_annotation_map annotation).checked checked
      have sourcePhase := phaseAgreement.trans
        (OwnerPhaseTransitions.available_permutation site.coherent.forget.source.owned_permutation).symm
      obtain ⟨frontStack, actualHandler, answer, residual, parameter, binder, code, offered, row,
        answerRows, resumeEffects, closeEffects, next,
        stackSplit, effectSame, answerMode, located, ready, found, offeredRow, resumeInterface, closeInterface,
        expressionSame, scopeSame, nextStack, resultSame, allowedSame, contextSame,
        dependenciesSame, signatureSame, rowsSame, event, nextState⟩ :=
        ExecutableState.capture_at_site split selected expressionEq.symm closed owner cut resumeRow closeRow
          rooted sourcePhase rootCheck (within.trans bounded) bound currentState.toExecutableState fresh currentState.installedSupport
      let allocated : Contract := ⟨site.result, answer, capturedScope.held, split.savedDemand, resumeRow,
        split.savedDemand, closeRow, resumeEffects, closeEffects⟩
      have selectedPhysical := split.handler_cut cut stackSplit
      refine ⟨allocated, site.resultRows, answerRows, capturedScope, split.savedRequirements, code.requiredActions,
        ⟨next.expression, next.runtimeScope, next.stack⟩, actualHandler, split.capturedStack, split.tailStack,
        parameter, binder, code, rfl, rfl, ?_, located, ready, rfl, expressionSame, scopeSame,
        nextStack, ?_, nextState, currentState.event_support event⟩
      · simpa only [← stackEq] using selectedPhysical
      · simpa only [← expressionEq, ← runtimeEq, ← stackEq] using event
  | unwind => cases machineEq


/-- The original endpoint projects preservation from the metadata-exposing endpoint. -/
theorem InstallationState.capture_successor
    (state : InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows output outputRows
      ⟨⟨.eval ⟨.perform (Instantiation.freezeEffect effect) operation operand, runtimeScope, stack⟩,
        issued, completed⟩, actions⟩)
    (physical : HandlerCut effect stack capturedStack tailStack handler)
    (closed : ClosedValue operand)
    (owner : Nat) (fresh : (issued ++ [Owner.ticket owner]).Nodup)
    (resumeRow : Footprint) (closeRow : Option Footprint) :
    ∃ allocated : Contract, ∃ inputRows : ValueRows allocated.input, ∃ answerRows : ValueRows allocated.answer,
    ∃ captureScope : SourceDependencyCapture.Scope,
    ∃ savedRequirements : Requirements allocated.resumeDemand,
    ∃ rights : Syntax.OneShotRights, ∃ next : Configuration,
      LexicalUnwind.Event
        ⟨.eval ⟨.perform (Instantiation.freezeEffect effect) operation operand, runtimeScope, stack⟩, issued, completed⟩
        ⟨.eval next, issued ++ [.ticket owner], completed⟩ ∧
      InstallationState operations policy (contracts.insert owner allocated) tables families required outward
        (fun other => if other = owner then some captureScope else annotations other) world ambient history
        ((⟨owner, .resume⟩, ⟨allocated.resumeDemand, savedRequirements⟩) :: resumes) disposals
        ((⟨owner, .resume⟩, ⟨allocated.resumeDemand, savedRequirements⟩) :: annotatedStore)
        budget ports (owners.insert owner inputRows answerRows) emptyRows output outputRows
        ⟨⟨.eval next, issued ++ [.ticket owner], completed⟩, actions.insert owner rights⟩ := by
  obtain ⟨allocated, inputRows, answerRows, captureScope, savedRequirements, rights, next,
    selectedHandler, selectedCaptured, selectedTail, parameter, binder, code,
    _resumeRow, _closeRow, _physical, _located, _ready, _rights, _expression, _scope, _stack,
    event, nextState⟩ := state.capture_successor_metadata physical closed owner fresh resumeRow closeRow
  exact ⟨allocated, inputRows, answerRows, captureScope, savedRequirements, rights, next, event, nextState⟩

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport
#print axioms Ash.OneShot.SourceDependencyCapture.Realizes.handler_not_builtin
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.InstallationState.capture_successor

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.InstallationState.capture_successor_metadata
