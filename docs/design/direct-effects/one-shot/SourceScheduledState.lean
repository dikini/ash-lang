import SourceScheduledAllocation
import SourcePlannedSourceReduction

/-! A shared execution state retains the actual source plan and scheduling
forest together with their typing, ownership and effect checks. The forest is
an index so capture obligations refer to the same saved computations. This
state does not assume preservation or successful future execution. -/
namespace Ash.OneShot.SourceScheduledState
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Operations Contracts Value)
open SourcePlannedSources (Expression)
open SourceDependencyCapture (lookupDependencies)
open SourceDependencyAnnotations (Dependencies)
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceRetainedPlans (Forest)
open SourceScheduledSavedPlans (Annotations)
open SourcePlannedFrames (DeclarationEvidence recipeEvidence)
open RecursiveRequirements (Requirements)

section

variable [admission : SourceScheduledChecks.DeclarationPolicy] [certification : SourcePlannedChecks.DeclarationPolicy]

inductive State [admission : SourceScheduledChecks.DeclarationPolicy] [certification : SourcePlannedChecks.DeclarationPolicy] (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (families : SourceDependencyFrames.Families)
    (required : SourceContextualRechecking.Required) (actions : Syntax.UsageTickets) (annotations : Annotations)
    (world : List Nat) (outward : List Instance) (outside : ProtectionContracts.Context)
    (scope : Execution.Scope) (code : Code) (stack : Stack)
    {receiving : SourceDependencyCapture.Scope} {hints : SourceContextualHints.Hints receiving} (forest : Forest hints)
    (output : Value) (demand : List Nat) (row : Footprint)
    (evidence : DeclarationEvidence := recipeEvidence) : Prop where
  | checked {plan : Plan dependencies}
      (current : Expression operations policy contracts world allowed scope (fun _ => none)
        code input currentDemand currentRequirements (signature plan))
      (scopeTyped : ScopedPorts.EffectScope contracts.erase.erase.ports scope ticket)
      (pending : SourceScheduledFrames.Segment (evidence := evidence) operations policy contracts tables families required actions outward
        (OwnerPhaseTransitions.available (ownedTickets stack)) world
        stack input output pendingDemand pendingRequirements resumes forest .nil allowed [])
      (closing : DeclaredSourceClosing.Records operations.erase.erase policy contracts.erase.erase tables world stack disposals)
      (templates : SourceScheduledClosingRecords.Records operations policy contracts tables annotations world stack disposals)
      (matched : SourceScheduledSavedPlans.Matches annotations forest)
      (contextual : SourceScheduledChecks.Local outward actions (OwnerPhaseTransitions.available (ownedTickets stack)) world plan forest)
      (unique : (ownedTickets stack).Nodup)
      (evaluated : RecursiveRequirements.Checked (resumes ++ disposals) [] (OwnerPhaseTransitions.available (ownedTickets stack))
        (.sequence (currentRequirements.prepend (OwnerPhases.ofStack tables stack)) pendingRequirements) row)
      (accepted : checkFootprint outside row = true)
      (accounting : demand = currentDemand ++ pendingDemand) :
      State operations policy contracts tables families required actions annotations world outward outside scope code stack forest output demand row evidence

/-- Forgetting plans recovers the established shared source invariant without
adding a separately assumed source derivation. -/
theorem State.erase [SourceScheduledChecks.DeclarationProjection admission certification]
    (state : State operations policy contracts tables families required actions annotations world outward outside
      scope code stack forest output demand row evidence) :
    DeclaredConnectedSources.State operations.erase.erase policy contracts.erase.erase tables actions world outside
      scope code stack output.erase.erase demand row := by
  cases state with
  | checked current scope pending closing templates matched contextual unique evaluated accepted accounting =>
      exact .checked (SourceDependencyAnnotations.expression_erase (SourcePlannedSources.expression_erase current))
        scope pending.source.source.erase.erase closing unique evaluated accepted accounting

/-- Initial programs have no saved continuations or stored closing templates.
Their current source and capability checks are still explicit admission data. -/
theorem initial {plan : Plan dependencies}
    (current : Expression operations policy contracts world [] .none (fun _ => none) code output demand requirements (signature plan))
    (empty : demand = [])
    (contextual : SourceScheduledChecks.Local outward actions (OwnerPhaseTransitions.available []) world plan .nil)
    (evaluated : RecursiveRequirements.Checked [] [] (OwnerPhaseTransitions.available []) requirements row)
    (accepted : checkFootprint outside row = true) :
    State operations policy contracts tables families required actions annotations world outward outside
      .none code .nil .nil output demand row evidence := by
  subst demand
  have currentCheck := RecursiveRequirements.checked_prepend_iff.mpr
    (show RecursiveRequirements.Checked [] ([] ++ []) (OwnerPhaseTransitions.available []) requirements row from evaluated)
  have pendingCheck : RecursiveRequirements.Checked [] [] (OwnerPhaseTransitions.available []) (Requirements.request [] []) [] := .request rfl
  simpa only [List.append_nil] using
    (State.checked (evidence := evidence) (tables := tables) current .none (.nil (List.Subset.refl [])) .nil .nil .nil
      contextual (by decide) (RecursiveRequirements.Checked.sequence currentCheck pendingCheck)
      (by simpa only [List.append_nil] using accepted) rfl)

/-- Source replacement keeps the exact pending source, stores and annotations.
Only present expression typing, contextual checking and evaluation are needed. -/
theorem replace_current
    {requirements : Requirements currentDemand} {plan : Plan dependencies}
    (current : Expression operations policy contracts world allowed nextScope (fun _ => none)
      next input currentDemand reduced (signature plan))
    (scopeTyped : ScopedPorts.EffectScope contracts.erase.erase.ports nextScope ticket)
    (pending : SourceScheduledFrames.Segment (evidence := evidence) operations policy contracts tables families required actions outward
      (OwnerPhaseTransitions.available (ownedTickets stack)) world
      stack input output pendingDemand pendingRequirements resumes forest .nil allowed [])
    (closing : DeclaredSourceClosing.Records operations.erase.erase policy contracts.erase.erase tables world stack disposals)
    (templates : SourceScheduledClosingRecords.Records operations policy contracts tables annotations world stack disposals)
    (matched : SourceScheduledSavedPlans.Matches annotations forest)
    (contextual : SourceScheduledChecks.Local outward actions (OwnerPhaseTransitions.available (ownedTickets stack)) world plan forest)
    (unique : (ownedTickets stack).Nodup)
    (evaluated : RecursiveRequirements.Checked (resumes ++ disposals) [] (OwnerPhaseTransitions.available (ownedTickets stack))
      (.sequence (requirements.prepend (OwnerPhases.ofStack tables stack)) pendingRequirements) row)
    (accepted : checkFootprint outside row = true)
    (accounting : demand = currentDemand ++ pendingDemand)
    (same : ∀ store receiving before, RecursiveRequirements.evaluate store receiving before reduced =
      RecursiveRequirements.evaluate store receiving before requirements) :
    State operations policy contracts tables families required actions annotations world outward outside nextScope next stack forest output demand row evidence := by
  apply State.checked current scopeTyped pending closing templates matched contextual unique _ accepted accounting
  apply RecursiveRequirements.evaluate_sound
  have original := RecursiveRequirements.checked_complete evaluated
  simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend] at original ⊢
  rw [same]
  exact original

/-- Bind reduction keeps the same body plan, pending source and saved map.
The existing source substitution and requirement-evaluation lemmas do the work. -/
theorem bind_preserves
    (state : State operations policy contracts tables families required actions annotations world outward outside scope
      (.bind parameter value body) stack forest output demand row evidence)
    (closed : ClosedValue value) :
    State operations policy contracts tables families required actions annotations world outward outside scope
      (body.subst parameter value) stack forest output demand row evidence := by
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting =>
    rename_i dependencies allowed input currentDemand currentRequirements ticket pendingDemand pendingRequirements resumes disposals plan
    have originalCurrent := current
    generalize sameSignature : signature plan = currentSignature at current
    cases current with
    | bind initializer body =>
      cases plan with
      | sequence initialPlan bodyPlan =>
        obtain ⟨reduced, replacement, same⟩ := SourcePlannedSources.bind_expression originalCurrent closed
        cases contextual with
        | sequence first second =>
          exact replace_current replacement scopeTyped pending closing templates matched second unique evaluated accepted accounting same

/-- Beta reduction reuses the actual latent body plan and its check. Its empty
lexical ticket scope is derived by the existing source substitution theorem. -/
theorem beta_preserves
    (state : State operations policy contracts tables families required actions annotations world outward outside scope
      (.app (.lambda parameter body) value) stack forest output demand row evidence)
    (closed : ClosedValue value) :
    State operations policy contracts tables families required actions annotations world outward outside .none
      (body.subst parameter value) stack forest output demand row evidence := by
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting =>
    rename_i dependencies allowed input currentDemand currentRequirements ticket pendingDemand pendingRequirements resumes disposals plan
    have originalCurrent := current
    generalize sameSignature : signature plan = currentSignature at current
    cases current with
    | app function argument admitted =>
      cases plan with
      | sequence functionPlan rest => cases rest with
        | sequence argumentPlan bodyPlan =>
          obtain ⟨reduced, replacement, same⟩ := SourcePlannedSources.beta_expression originalCurrent closed
          cases contextual with
          | sequence first rest => cases rest with
            | sequence argument body =>
              exact replace_current replacement .none pending closing templates matched body unique evaluated accepted accounting same

end

/-- Capture without a closing plan preserves the shared state. The selected
clause's contextual obligations remain an explicit premise; ownership balance
and the successor's combined effect check are derived from existing proofs. -/
theorem capture_without_closing
    (state : State operations policy contracts tables families required actions annotations world outward outside scope
      (.perform (Instantiation.freezeEffect requested) operation operand) whole forest output demand row evidence)
    (cut : HandlerCut requested whole capture tail handler)
    (isValue : operand.IsValue)
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler) = some offered)
    (freshContract : contracts owner = none) (freshAction : actions owner = none)
    (freshAnnotation : annotations owner = none)
    (unavailable : makePlan capture = none ∨ ¬ InternalUses capture.erase.liveTickets capture.erase.pending)
    (requirementsAtCapture : ∀ {plans : SourceDeclarationPlans.ClausePlans handler.clauses (families handler)},
      evidence (required handler) plans →
      ∀ {modes}, lookupDependencies operation (families handler) = some modes →
      ∀ {capturedScope tailScope} {savedHints : SourceContextualHints.Hints capturedScope}
        {waitingHints : SourceContextualHints.Hints tailScope},
      (saved : Forest savedHints) → (waiting : Forest waitingHints) →
      SourceScheduledNeutral.Cut requested operation offered modes forest saved waiting →
      ∀ {family : Nat → Dependencies} {bodies : ∀ owner, SourceDeclarationPlans.Plan (family owner)},
      SourcePlannedRecipeDeclarations.Selected operation capturedScope.held plans parameter binder code bodies →
      SourceScheduledRequirements.Satisfied outward (actions.insert owner code.requiredActions)
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole)) owner) world
        (bodies owner) (.live (owner := owner) saved waiting)) :
    ∃ (contract : SourcePlannedTyping.Contract) (captured waiting : SourceScheduledSavedPlans.Saved)
      (after : Configuration) (nextDemand : List Nat) (nextRow : Footprint),
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩ after [.ticket owner] [] ∧
      State operations policy (contracts.insert owner contract) tables families required (actions.insert owner code.requiredActions)
        (annotations.insert owner captured) world outward outside after.scope after.expression after.stack
        (.live (owner := owner) captured.forest waiting.forest) output nextDemand nextRow evidence ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack = owner :: ownedTickets whole ∧
      offered.dispose = false ∧ code.requiredActions.dispose = false ∧
      after = ⟨code.subst parameter operand, .ticket binder owner,
        .live owner (ScopedPorts.embedPort contract.input.erase.erase.port) handler.answer capture handler.scope tail⟩ ∧
      ∃ argument, operations requested operation = some (argument, contract.input) := by
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting =>
    rename_i dependencies allowed input currentDemand currentRequirements ticket pendingDemand pendingRequirements resumes disposals plan
    have originalCurrent := current
    generalize encoded : Instantiation.freezeEffect requested = syntaxEffect at current
    generalize signatureSame : signature plan = currentSignature at current
    cases current with
    | perform operationKnown admitted operandSource formed =>
      cases freeze_effect_injective encoded
      cases plan with
      | sequence operandPlan requestPlan =>
        cases requestPlan
        have payload := SourcePlannedSources.Values.summary operandSource isValue
        have empty := SourceTemplates.expression_value_demand
          (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase
            (SourcePlannedSources.expression_erase operandSource))) isValue
        cases empty
        have closed := ScopedPorts.typed_value_closed
          ((DeclaredSourceValues.erase (SourceDependencyFrames.value_erase
            (SourcePlannedSources.expression_erase payload))).ports .none) isValue
        have requestContextual := by
          cases contextual with
          | sequence operandCheck requestCheck => exact requestCheck
        obtain ⟨requestRow, pendingRow, currentCheck, pendingCheck, sameRow⟩ :=
          RecursiveRequirements.checked_sequence_parts evaluated
        have requestExport := RecursiveRequirements.checked_complete
          (RecursiveRequirements.checked_prepend_iff.mp currentCheck)
        rw [RecursiveDispatch.request_evaluation
          (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase
            (SourcePlannedSources.expression_erase originalCurrent))) isValue] at requestExport
        have requestCheck : RecursiveRequirements.Checked (resumes ++ disposals) (OwnerPhases.ofStack tables whole)
            (OwnerPhaseTransitions.available (ownedTickets whole))
            (.request [] [⟨requested, operation, false⟩]) requestRow :=
          RecursiveRequirements.evaluate_sound (by
            simpa only [RecursiveContexts.evaluate_request, List.nil_append, List.append_nil] using requestExport)
        obtain ⟨actualOffer, offeredRow, actualFound, mode, rowKnown, exported⟩ :=
          RecursiveDispatch.cut_residual cut (by
            simpa only [List.append_nil, OwnerSource.exportAt, OwnerPhaseTransitions.project_actual] using requestExport)
        cases Option.some.inj (actualFound.symm.trans found)
        simp only [Bool.false_or] at rowKnown
        have capabilities : ClausesUse policy handler.clauses := by
          obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords,
            capScope, tailScope, annotation, frame, saved, waiting, rest⟩ :=
            SourceDependencyFrames.capture_segments cut pending.source.source.erase
          cases frame with
          | handler scope annotation clauses coverage unique declarations capabilities modes => exact capabilities
        obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capScope, tailScope,
          resumeEffects, closeEffects, family, captureRow, tailRow, noDispose, codeNoDispose,
          raw, owned, nextUnique, demandSame, pendingRowSame, refinedAnswer, bodies,
          savedHints, waitingHints, saved, waiting, answerSame, exactErasure,
          nextMatched, nextLocal, nextPending, nextTemplates, nextLayout,
          savedAfter, tailAfter, resumeCheck, clauseDemand, clauseRequirements, clauseRow, expression, clauseCheck, covered⟩ :=
          SourceScheduledAllocation.allocate_without_closing operations contracts _ _ cut pending matched requestContextual
            selected found rowKnown operationKnown payload closed freshContract freshAction closing templates freshAnnotation
            unavailable (by simpa only [OwnerPhaseTransitions.spendAll] using pendingCheck) unique requestCheck requirementsAtCapture
            (caller := scope)
        let allocated : SourceDependencyAnnotations.Contract :=
          ⟨input.erase, answer, capScope.held, capDemand, captureRow, capDemand, none, resumeEffects, closeEffects⟩
        let contract := SourcePlannedSources.refineContract allocated input refinedAnswer
        have known : (contracts.insert owner contract) owner = some contract := by simp [SourcePlannedTyping.Contracts.insert]
        have erasedKnown := SourceDependencyAnnotations.contract_erase_known (SourcePlannedSources.contract_erase_known known)
        have payloadUsage := SourceOwnerClosure.expression_usage
          (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase
            (SourcePlannedSources.expression_erase payload))) rfl
        have clauseUsage := ScopedExpressions.usage_substitution
          (selected_clause_usage selected capabilities) closed.1 payloadUsage parameter
        have erasedCurrent := DeclaredSources.expression_erase
          (SourceDependencyAnnotations.expression_erase (SourcePlannedSources.expression_erase expression))
        have completed := RecursiveClauseUsage.consuming_usage_completed erasedCurrent clauseUsage clauseCheck
        have balanced : contract.erase.erase.closeDemand.Perm contract.erase.erase.resumeDemand := by
          change capDemand.Perm capDemand
          exact List.Perm.refl _
        have sameDemand := RecursiveClauseOwnership.consuming_clause_balance erasedCurrent erasedKnown clauseCheck
          (by simp [OwnerPhaseTransitions.available, ownedTickets]) completed balanced
        change clauseDemand.Perm (owner :: capDemand) at sameDemand
        have freshErased : contracts.erase.erase owner = none := by
          simp [SourcePlannedTyping.Contracts.erase, SourceDependencyAnnotations.Contracts.erase, freshContract]
        have phaseSame := RecursiveCapture.capture_phase_consumed (input := ScopedPorts.embedPort input.erase.erase.port)
          cut (RecursiveCapture.fresh_unowned pending.source.source.erase.erase.source.erase freshErased)
        have consumed := phaseSame ▸ OwnerPhaseTransitions.spend_self
          (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.erase.port)
            handler.answer capture handler.scope tail))) owner
        have afterOwner := OwnerPhaseTransitions.trace_monotone (RecursiveRequirements.checked_trace savedAfter) consumed
        have pendingReady : RecursiveRequirements.Checked
            (((⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: resumes) ++ disposals) []
            (OwnerPhaseTransitions.spendAll (OwnerPhaseTransitions.available
              (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail))) clauseDemand)
            (.sequence (.spent owner) tailReq) tailRow := by
          rw [PhaseRechecking.spendAll_permutation sameDemand]
          simpa only [OwnerPhaseTransitions.spendAll, phaseSame, List.nil_append] using
            (RecursiveRequirements.Checked.sequence (RecursiveRequirements.Checked.spent (receiving := []) afterOwner) tailAfter)
        have included : clauseRow ++ tailRow ⊆ row := by
          rw [sameRow, pendingRowSame, ← List.append_assoc]
          exact ScopedExpressions.append_subset covered (List.Subset.refl _)
        refine ⟨contract, ⟨capScope, savedHints, saved⟩, ⟨tailScope, waitingHints, waiting⟩, _,
          clauseDemand ++ tailDemand, clauseRow ++ tailRow, raw, ?_, ?_, included, owned, noDispose, codeNoDispose, rfl, _, operationKnown⟩
        · have phases : OwnerPhaseTransitions.available (ownedTickets
              (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail)) =
              OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole)) owner := by
            exact OwnerPhaseTransitions.capture_map cut
          apply State.checked expression (.bound (CoherentSourceTypes.Owners.ports_lookup erasedKnown))
            (phases.symm ▸ nextPending) nextLayout nextTemplates nextMatched (phases.symm ▸ nextLocal) nextUnique
            (RecursiveRequirements.Checked.sequence
              (RecursiveRequirements.checked_prepend_iff.mpr (by simpa only [List.append_nil] using clauseCheck)) pendingReady)
            (checked_footprint_subset accepted included) rfl
        · simpa only [accounting, List.nil_append, demandSame, List.cons_append] using sameDemand.append_right tailDemand

/-- A constructed closing plan is retained in the shared successor. With an
empty outward guard, support justifies its budget whenever disposal is allowed;
resume-only offers require no closing budget even when a plan exists. -/
theorem capture_with_closing
    (state : State operations policy contracts tables families required actions annotations world [] outside scope
      (.perform (Instantiation.freezeEffect requested) operation operand) whole forest output demand row evidence)
    (cut : HandlerCut requested whole capture tail handler)
    (isValue : operand.IsValue)
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler) = some offered)
    (freshContract : contracts owner = none) (freshAction : actions owner = none)
    (freshAnnotation : annotations owner = none)
    (supported : Supported capture.erase (Admission.outsideResources capture.erase))
    (built : makePlan capture = some closingPlan)
    (internal : InternalUses capture.erase.liveTickets capture.erase.pending)
    (requirementsAtCapture : ∀ {plans : SourceDeclarationPlans.ClausePlans handler.clauses (families handler)},
      evidence (required handler) plans →
      ∀ {modes}, lookupDependencies operation (families handler) = some modes →
      ∀ {capturedScope tailScope} {savedHints : SourceContextualHints.Hints capturedScope}
        {waitingHints : SourceContextualHints.Hints tailScope},
      (saved : Forest savedHints) → (waiting : Forest waitingHints) →
      SourceScheduledNeutral.Cut requested operation offered modes forest saved waiting →
      ∀ {family : Nat → Dependencies} {bodies : ∀ owner, SourceDeclarationPlans.Plan (family owner)},
      SourcePlannedRecipeDeclarations.Selected operation capturedScope.held plans parameter binder code bodies →
      SourceScheduledRequirements.Satisfied [] (actions.insert owner code.requiredActions)
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole)) owner) world
        (bodies owner) (.live (owner := owner) saved waiting)) :
    ∃ (contract : SourcePlannedTyping.Contract) (captured waiting : SourceScheduledSavedPlans.Saved)
      (after : Configuration) (nextDemand : List Nat) (nextRow : Footprint),
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩ after [.ticket owner] [] ∧
      State operations policy (contracts.insert owner contract) tables families required (actions.insert owner code.requiredActions)
        (annotations.insert owner captured) world [] outside after.scope after.expression after.stack
        (.live (owner := owner) captured.forest waiting.forest) output nextDemand nextRow evidence ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack = owner :: ownedTickets whole ∧
      after = ⟨code.subst parameter operand, .ticket binder owner,
        .live owner (ScopedPorts.embedPort contract.input.erase.erase.port) handler.answer capture handler.scope tail⟩ ∧
      ∃ argument, operations requested operation = some (argument, contract.input) := by
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting =>
    rename_i dependencies allowed input currentDemand currentRequirements ticket pendingDemand pendingRequirements resumes disposals plan
    have originalCurrent := current
    generalize encoded : Instantiation.freezeEffect requested = syntaxEffect at current
    generalize signatureSame : signature plan = currentSignature at current
    cases current with
    | perform operationKnown admitted operandSource formed =>
      cases freeze_effect_injective encoded
      cases plan with
      | sequence operandPlan requestPlan =>
        cases requestPlan
        have payload := SourcePlannedSources.Values.summary operandSource isValue
        have empty := SourceTemplates.expression_value_demand
          (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase
            (SourcePlannedSources.expression_erase operandSource))) isValue
        cases empty
        have closed := ScopedPorts.typed_value_closed
          ((DeclaredSourceValues.erase (SourceDependencyFrames.value_erase
            (SourcePlannedSources.expression_erase payload))).ports .none) isValue
        have requestContextual := by
          cases contextual with
          | sequence operandCheck requestCheck => exact requestCheck
        obtain ⟨requestRow, pendingRow, currentCheck, pendingCheck, sameRow⟩ :=
          RecursiveRequirements.checked_sequence_parts evaluated
        have requestExport := RecursiveRequirements.checked_complete
          (RecursiveRequirements.checked_prepend_iff.mp currentCheck)
        rw [RecursiveDispatch.request_evaluation
          (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase
            (SourcePlannedSources.expression_erase originalCurrent))) isValue] at requestExport
        have requestCheck : RecursiveRequirements.Checked (resumes ++ disposals) (OwnerPhases.ofStack tables whole)
            (OwnerPhaseTransitions.available (ownedTickets whole))
            (.request [] [⟨requested, operation, false⟩]) requestRow :=
          RecursiveRequirements.evaluate_sound (by
            simpa only [RecursiveContexts.evaluate_request, List.nil_append, List.append_nil] using requestExport)
        obtain ⟨actualOffer, offeredRow, actualFound, mode, rowKnown, exported⟩ :=
          RecursiveDispatch.cut_residual cut (by
            simpa only [List.append_nil, OwnerSource.exportAt, OwnerPhaseTransitions.project_actual] using requestExport)
        cases Option.some.inj (actualFound.symm.trans found)
        simp only [Bool.false_or] at rowKnown
        have capabilities : ClausesUse policy handler.clauses := by
          obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords,
            capScope, tailScope, annotation, frame, saved, waiting, rest⟩ :=
            SourceDependencyFrames.capture_segments cut pending.source.source.erase
          cases frame with
          | handler scope annotation clauses coverage unique declarations capabilities modes => exact capabilities
        obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capScope, tailScope,
          resumeEffects, closeEffects, family, captureRow, tailRow, closingRaw, closeReq,
          raw, owned, nextUnique, scopeSame, demandSame, clauseContextual, nextRetained, kept, certificate,
          pendingRowSame, savedCheck, tailCheck, balance, parts⟩ :=
          SourceScheduledAllocation.allocate operations contracts _ _ cut pending matched requestContextual
            selected found rowKnown operationKnown payload closed freshContract freshAction closing templates freshAnnotation
            built internal (by simpa only [OwnerPhaseTransitions.spendAll] using pendingCheck) unique requestCheck requirementsAtCapture
            (outside := outside) (caller := scope)
        dsimp only at parts
        obtain ⟨⟨refinedAnswer, bodies, savedHints, waitingHints, saved, waiting, answerSame, exactErasure,
          nextMatched, nextLocal, body, nextPending, exactTemplate, legacyTemplate, nextTemplates⟩,
          oldBody, oldPending, nextBound, nextTemplate, nextLayout, oldTemplates,
          savedAfter, tailAfter, resumeCheck, disposeCheck, clauseReady⟩ := parts
        let allocated : SourceDependencyAnnotations.Contract :=
          ⟨input.erase, answer, capScope.held, capDemand, captureRow, OwnerClosingSource.retirements closingPlan,
            RecursiveRequirements.evaluate [] (OwnerPhases.ofStack tables tail)
              (OwnerPhaseTransitions.available (ownedTickets whole)) closeReq, resumeEffects, closeEffects⟩
        let contract := SourcePlannedSources.refineContract allocated input refinedAnswer
        have capHeld : capScope.held = ProtectionContexts.protectedMode capture.erase := by
          cases kept with
          | checked annotation scopeKnown saved waiting records resume close typed kept savedMatched waitingMatched =>
              exact saved.source.source.matches.realizes.held
        have freshErased : contracts.erase.erase owner = none := by
          simp [SourcePlannedTyping.Contracts.erase, SourceDependencyAnnotations.Contracts.erase, freshContract]
        have phaseSame := RecursiveCapture.capture_phase_consumed (input := ScopedPorts.embedPort input.erase.erase.port)
          cut (RecursiveCapture.fresh_unowned pending.source.source.erase.erase.source.erase freshErased)
        have closingFacts : offered.dispose = true → ∃ closingRow,
            allocated.closeRow = some closingRow ∧ EffectBounds.Covers (requestRow ++ captureRow) closingRow := by
          intro disposes
          obtain ⟨actualPlan, actualReq, actualScope, actualBuilt, typedPlan, template, budget, owners⟩ :=
            SourceDependencySchemes.closed_capture_budget cut pending.source.source.erase requestContextual.erase.erase
              found disposes supported (outside := outside) (budget := row)
          cases Option.some.inj (actualBuilt.symm.trans built)
          obtain ⟨actualClosingRow, closingEvaluated, closingAllowed, closingCovered, callbackAllowed⟩ :=
            DeclaredCallbackAdmission.checked_template nextTemplate.erase built nextUnique
              (nextTemplate.closed_budget typedPlan (budget := requestRow ++ captureRow) (outside := outside)) (store := [])
          exact ⟨actualClosingRow, by simpa only [phaseSame] using closingEvaluated, closingCovered⟩
        let afterPhases := OwnerPhaseTransitions.available (ownedTickets
          (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail))
        have callerReady : ∀ other ∈ activeTickets tail, afterPhases other = .available := by
          intro other member
          apply if_pos
          exact List.mem_cons.mpr (Or.inr (List.mem_append_right _ (active_tickets_owned tail member)))
        have exportAfter : OwnerSource.exportAt (OwnerPhases.ofStack tables tail) afterPhases offeredRow = some requestRow :=
          (RecursivePlanAdmission.caller_export callerReady).trans exported
        have interface : ClauseRowAdmission.Interface owner allocated.erase offered.dispose
            (((⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: resumes) ++
              ((⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements closingPlan, closeReq⟩) :: disposals))
            (OwnerPhases.ofStack tables tail) afterPhases requestRow := by
          refine ⟨?_, ?_, ?_, ?_, OwnerPhaseTransitions.capture_tail_fresh cut (RecursiveCapture.fresh_unowned pending.source.source.erase.erase.source.erase freshErased)⟩
          · simpa only [afterPhases, OwnerPhases.ofStack, allocated, SourceDependencyAnnotations.Contract.erase, capHeld] using resumeCheck
          · intro _ closingRow same
            simpa only [afterPhases, OwnerPhases.ofStack, allocated, SourceDependencyAnnotations.Contract.erase, capHeld] using disposeCheck closingRow same
          · intro disposes
            obtain ⟨closingRow, same, covered⟩ := closingFacts disposes
            exact ⟨closingRow, same⟩
          · intro disposes closingRow same
            obtain ⟨actualClosingRow, closeSame, closingCovered⟩ := closingFacts disposes
            cases Option.some.inj (closeSame.symm.trans same)
            exact closingCovered
        cases body with
        | typed expression rows closingRows =>
          rename_i clauseDemand clauseRequirements
          obtain ⟨clauseRow, checkedClause, covered⟩ := rows.instantiate interface exportAfter
              (ClauseRowAdmission.SourceStore.of_source oldPending.erase.source.erase
                (DeclaredSourceClosing.records_erase nextLayout)
                (by simp [SourceDependencyAnnotations.Contracts.erase, SourceDependencyAnnotations.Contracts.insert]))
          have clauseCheck := checkedClause
          simp only [SourceDependencyAnnotations.Contract.erase, capHeld] at clauseCheck
          have known : (contracts.insert owner contract) owner = some contract := by simp [SourcePlannedTyping.Contracts.insert]
          have erasedKnown := SourceDependencyAnnotations.contract_erase_known (SourcePlannedSources.contract_erase_known known)
          have payloadUsage := SourceOwnerClosure.expression_usage
            (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase
              (SourcePlannedSources.expression_erase payload))) rfl
          have clauseUsage := ScopedExpressions.usage_substitution
            (selected_clause_usage selected capabilities) closed.1 payloadUsage parameter
          have erasedCurrent := DeclaredSources.expression_erase
            (SourceDependencyAnnotations.expression_erase (SourcePlannedSources.expression_erase expression))
          have completed := RecursiveClauseUsage.consuming_usage_completed erasedCurrent clauseUsage clauseCheck
          have balanced : contract.erase.erase.closeDemand.Perm contract.erase.erase.resumeDemand := balance
          have sameDemand := RecursiveClauseOwnership.consuming_clause_balance erasedCurrent erasedKnown clauseCheck
            (by simp [afterPhases, OwnerPhaseTransitions.available, ownedTickets]) completed balanced
          change clauseDemand.Perm (owner :: capDemand) at sameDemand
          have consumed := phaseSame ▸ OwnerPhaseTransitions.spend_self
            (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.erase.port)
              handler.answer capture handler.scope tail))) owner
          have afterOwner := OwnerPhaseTransitions.trace_monotone (RecursiveRequirements.checked_trace savedAfter) consumed
          have pendingReady : RecursiveRequirements.Checked
              (((⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: resumes) ++
                ((⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements closingPlan, closeReq⟩) :: disposals)) []
              (OwnerPhaseTransitions.spendAll (OwnerPhaseTransitions.available
                (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail))) clauseDemand)
              (.sequence (.spent owner) tailReq) tailRow := by
            rw [PhaseRechecking.spendAll_permutation sameDemand]
            simpa only [OwnerPhaseTransitions.spendAll, phaseSame, List.nil_append] using
              (RecursiveRequirements.Checked.sequence (RecursiveRequirements.Checked.spent (receiving := []) afterOwner) tailAfter)
          have included : clauseRow ++ tailRow ⊆ row := by
            rw [sameRow, pendingRowSame, ← List.append_assoc]
            exact ScopedExpressions.append_subset covered (List.Subset.refl _)
          refine ⟨contract, ⟨capScope, savedHints, saved⟩, ⟨tailScope, waitingHints, waiting⟩, _,
            clauseDemand ++ tailDemand, clauseRow ++ tailRow, raw, ?_, ?_, included, owned, rfl, _, operationKnown⟩
          · have phases : OwnerPhaseTransitions.available (ownedTickets
                (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail)) =
                OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole)) owner := by
              exact OwnerPhaseTransitions.capture_map cut
            apply State.checked expression (.bound (CoherentSourceTypes.Owners.ports_lookup erasedKnown))
              (phases.symm ▸ nextPending)
                (by simpa only [SourcePlannedTyping.contracts_erase_insert, exactErasure] using nextLayout) nextTemplates nextMatched (phases.symm ▸ nextLocal) nextUnique
              (RecursiveRequirements.Checked.sequence
                (RecursiveRequirements.checked_prepend_iff.mpr (by simpa only [List.append_nil, afterPhases, OwnerPhases.ofStack] using clauseCheck)) pendingReady)
              (checked_footprint_subset accepted included) rfl
          · simpa only [accounting, List.nil_append, demandSame, List.cons_append] using sameDemand.append_right tailDemand

/-- All physical one-shot captures preserve the same scheduled state. The
source supplies offer availability and payload closure; classification of the
actual captured stack selects closing allocation or derives disposal denial.
Contextual clause requirements and resource support remain explicit premises. -/
theorem capture_preserves
    (state : State operations policy contracts tables families required actions annotations world [] outside scope
      (.perform (Instantiation.freezeEffect requested) operation operand) whole forest output demand row evidence)
    (cut : HandlerCut requested whole capture tail handler)
    (isValue : operand.IsValue)
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler) = some offered)
    (freshContract : contracts owner = none) (freshAction : actions owner = none)
    (freshAnnotation : annotations owner = none)
    (supported : Supported capture.erase (Admission.outsideResources capture.erase))
    (requirementsAtCapture : ∀ {plans : SourceDeclarationPlans.ClausePlans handler.clauses (families handler)},
      evidence (required handler) plans →
      ∀ {modes}, lookupDependencies operation (families handler) = some modes →
      ∀ {capturedScope tailScope} {savedHints : SourceContextualHints.Hints capturedScope}
        {waitingHints : SourceContextualHints.Hints tailScope},
      (saved : Forest savedHints) → (waiting : Forest waitingHints) →
      SourceScheduledNeutral.Cut requested operation offered modes forest saved waiting →
      ∀ {family : Nat → Dependencies} {bodies : ∀ owner, SourceDeclarationPlans.Plan (family owner)},
      SourcePlannedRecipeDeclarations.Selected operation capturedScope.held plans parameter binder code bodies →
      SourceScheduledRequirements.Satisfied [] (actions.insert owner code.requiredActions)
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole)) owner) world
        (bodies owner) (.live (owner := owner) saved waiting)) :
    ∃ (contract : SourcePlannedTyping.Contract) (captured waiting : SourceScheduledSavedPlans.Saved)
      (after : Configuration) (nextDemand : List Nat) (nextRow : Footprint),
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩ after [.ticket owner] [] ∧
      State operations policy (contracts.insert owner contract) tables families required (actions.insert owner code.requiredActions)
        (annotations.insert owner captured) world [] outside after.scope after.expression after.stack
        (.live (owner := owner) captured.forest waiting.forest) output nextDemand nextRow evidence ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack = owner :: ownedTickets whole ∧
      after = ⟨code.subst parameter operand, .ticket binder owner,
        .live owner (ScopedPorts.embedPort contract.input.erase.erase.port) handler.answer capture handler.scope tail⟩ ∧
      ∃ argument, operations requested operation = some (argument, contract.input) := by
  classical
  have withoutClosing (unavailable : makePlan capture = none ∨ ¬ InternalUses capture.erase.liveTickets capture.erase.pending) :=
    capture_without_closing state cut isValue selected found freshContract freshAction freshAnnotation unavailable requirementsAtCapture
  cases built : makePlan capture with
  | none =>
      obtain ⟨contract, captured, waiting, after, nextDemand, nextRow, step, next, balanced, bounded, owned, _, _, same, sourceInput⟩ :=
        withoutClosing (Or.inl built)
      exact ⟨contract, captured, waiting, after, nextDemand, nextRow, step, next, balanced, bounded, owned, same, sourceInput⟩
  | some plan =>
      by_cases internal : InternalUses capture.erase.liveTickets capture.erase.pending
      · exact capture_with_closing state cut isValue selected found freshContract freshAction freshAnnotation
          supported built internal requirementsAtCapture
      · obtain ⟨contract, captured, waiting, after, nextDemand, nextRow, step, next, balanced, bounded, owned, _, _, same, sourceInput⟩ :=
          withoutClosing (Or.inr internal)
        exact ⟨contract, captured, waiting, after, nextDemand, nextRow, step, next, balanced, bounded, owned, same, sourceInput⟩

end Ash.OneShot.SourceScheduledState

#print axioms Ash.OneShot.SourceScheduledState.State.erase
#print axioms Ash.OneShot.SourceScheduledState.initial

#print axioms Ash.OneShot.SourceScheduledState.capture_without_closing

#print axioms Ash.OneShot.SourceScheduledState.capture_with_closing

#print axioms Ash.OneShot.SourceScheduledState.capture_preserves

#print axioms Ash.OneShot.SourceScheduledState.replace_current
#print axioms Ash.OneShot.SourceScheduledState.bind_preserves
#print axioms Ash.OneShot.SourceScheduledState.beta_preserves
