import SourceAnnotatedAllocation

/-! Both physical capture branches preserve the annotated scheduled state,
including the same stored callback certificates. Ownership and effect accounting
reuse existing allocation, completion and row-instantiation proofs. -/
namespace Ash.OneShot.SourceAnnotatedRuntimeState
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Operations Contracts Value)
open SourceDependencyCapture (lookupDependencies)
open SourceDependencyAnnotations (Dependencies)
open SourcePlanSignatures (signature)
open SourceRetainedPlans (Forest)
open SourceAnnotatedAllocationData (ClauseEvidence noClauseEvidence)

variable {whole capture tail : SourceAnnotatedRuntime.Stack}
variable {handler : SourceAnnotatedRuntime.Handler} {code operand : SourceAnnotatedCode.Term}

/-- Capture without a closing plan preserves the shared state. The selected
clause's contextual obligations remain an explicit premise; ownership balance
and the successor's combined effect check are derived from existing proofs. -/
theorem capture_without_closing_retaining (currentEvidence : ClauseEvidence)
    (state : State operations policy contracts tables families required actions annotations world outward outside scope
      (.perform hint (Instantiation.freezeEffect requested) operation operand) whole forest output demand row evidence)
    (cut : SourceAnnotatedRuntime.HandlerCut requested whole capture tail handler)
    (isValue : operand.erase.IsValue)
    (selected : SourceAnnotatedRuntime.ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler.erase) = some offered)
    (freshContract : contracts owner = none) (freshAction : actions owner = none)
    (freshAnnotation : annotations owner = none)
    (unavailable : makePlan capture.erase = none ∨ ¬ InternalUses capture.erase.erase.liveTickets capture.erase.erase.pending)
    (requirementsAtCapture : ∀ {plans : SourceDeclarationPlans.ClausePlans handler.clauses.erase (families handler.erase)},
      evidence (required handler.erase) plans →
      ∀ {modes}, lookupDependencies operation (families handler.erase) = some modes →
      ∀ {capturedScope tailScope} {savedHints : SourceContextualHints.Hints capturedScope}
        {waitingHints : SourceContextualHints.Hints tailScope},
      (saved : Forest savedHints) → (waiting : Forest waitingHints) →
      SourceScheduledNeutral.Cut requested operation offered modes forest saved waiting →
      ∀ {family : Nat → Dependencies} {bodies : ∀ owner, SourceDeclarationPlans.Plan (family owner)},
      SourcePlannedRecipeDeclarations.Selected operation capturedScope.held plans parameter binder code.erase bodies →
      SourceScheduledRequirements.Satisfied outward (actions.insert owner code.erase.requiredActions)
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner) world
        (bodies owner) (.live (owner := owner) saved waiting) ∧
        currentEvidence (bodies owner) (.live (owner := owner) saved waiting)) :
    ∃ (contract : SourcePlannedTyping.Contract) (captured waiting : SourceScheduledSavedPlans.Saved)
      (after : SourceAnnotatedRuntime.Configuration) (nextDemand : List Nat) (nextRow : Footprint),
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand.erase, scope, whole.erase⟩ after.erase [.ticket owner] [] ∧
      (∃ dependencies, ∃ nextPlan : SourceDeclarationPlans.Plan dependencies,
      AtPlan operations policy (contracts.insert owner contract) tables families required (actions.insert owner code.erase.requiredActions)
        (annotations.insert owner captured) world outward outside after.scope after.expression after.stack nextPlan
        (.live (owner := owner) captured.forest waiting.forest) output nextDemand nextRow evidence ∧
      currentEvidence nextPlan (.live (owner := owner) captured.forest waiting.forest)) ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack.erase = owner :: ownedTickets whole.erase ∧
      offered.dispose = false ∧ code.erase.requiredActions.dispose = false ∧
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
    | checked checkedHint metadata node => cases node with
      | perform operationKnown admitted operandSource formed =>
        cases freeze_effect_injective encoded
        cases plan with
        | sequence operandPlan requestPlan =>
          cases requestPlan
          have payload := SourceAnnotatedSources.Values.summary operandSource isValue
          have empty := SourceTemplates.expression_value_demand
            (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase
              (SourcePlannedSources.expression_erase operandSource.erase))) isValue
          cases empty
          have closed := ScopedPorts.typed_value_closed
            ((DeclaredSourceValues.erase (SourceDependencyFrames.value_erase
              (SourcePlannedSources.expression_erase payload.erase))).ports .none) isValue
          have requestContextual := by
            cases contextual with
            | sequence operandCheck requestCheck => exact requestCheck
          obtain ⟨requestRow, pendingRow, currentCheck, pendingCheck, sameRow⟩ :=
            RecursiveRequirements.checked_sequence_parts evaluated
          have requestExport := RecursiveRequirements.checked_complete
            (RecursiveRequirements.checked_prepend_iff.mp currentCheck)
          rw [RecursiveDispatch.request_evaluation
            (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase
              (SourcePlannedSources.expression_erase originalCurrent.erase))) isValue] at requestExport
          have requestCheck : RecursiveRequirements.Checked (resumes ++ disposals) (OwnerPhases.ofStack tables whole.erase)
              (OwnerPhaseTransitions.available (ownedTickets whole.erase))
              (.request [] [⟨requested, operation, false⟩]) requestRow :=
            RecursiveRequirements.evaluate_sound (by
              simpa only [SourceAnnotatedRuntime.Handler.erase, SourceAnnotatedRuntime.Stack.erase, RecursiveContexts.evaluate_request, List.nil_append, List.append_nil] using requestExport)
          obtain ⟨actualOffer, offeredRow, actualFound, mode, rowKnown, exported⟩ :=
            RecursiveDispatch.cut_residual cut.erase (by
              simpa only [SourceAnnotatedRuntime.Handler.erase, SourceAnnotatedRuntime.Stack.erase, List.append_nil, OwnerSource.exportAt, OwnerPhaseTransitions.project_actual] using requestExport)
          cases Option.some.inj (actualFound.symm.trans found)
          simp only [Bool.false_or] at rowKnown
          have capabilities : ClausesUse policy handler.erase.clauses := by
            obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords,
              capScope, tailScope, annotation, frame, saved, waiting, rest⟩ :=
              SourceDependencyFrames.capture_segments cut.erase pending.erase.source.source.erase
            cases frame with
            | handler scope annotation clauses coverage unique declarations capabilities modes => exact capabilities
          obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capScope, tailScope,
            resumeEffects, closeEffects, family, captureRow, tailRow, noDispose, codeNoDispose,
            raw, owned, nextUnique, demandSame, pendingRowSame, refinedAnswer, bodies,
            savedHints, waitingHints, saved, waiting, answerSame, exactErasure,
            nextMatched, nextLocal, nextPending, nextTemplates, nextLayout,
            savedAfter, tailAfter, resumeCheck, clauseDemand, clauseRequirements, clauseRow, expression, clauseCheck, covered, clauseKept⟩ :=
            SourceAnnotatedAllocation.allocate_without_closing_retaining currentEvidence operations contracts _ _ cut pending matched requestContextual
              selected found rowKnown operationKnown payload closed freshContract freshAction closing templates freshAnnotation
              unavailable (by simpa only [SourceAnnotatedRuntime.Handler.erase, SourceAnnotatedRuntime.Stack.erase, OwnerPhaseTransitions.spendAll] using pendingCheck) unique requestCheck requirementsAtCapture
              (caller := scope)
          let allocated : SourceDependencyAnnotations.Contract :=
            ⟨input.erase, answer, capScope.held, capDemand, captureRow, capDemand, none, resumeEffects, closeEffects⟩
          let contract := SourcePlannedSources.refineContract allocated input refinedAnswer
          have known : (contracts.insert owner contract) owner = some contract := by simp [SourcePlannedTyping.Contracts.insert]
          have erasedKnown := SourceDependencyAnnotations.contract_erase_known (SourcePlannedSources.contract_erase_known known)
          have payloadUsage := SourceOwnerClosure.expression_usage
            (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase
              (SourcePlannedSources.expression_erase payload.erase))) rfl
          have clauseUsage := ScopedExpressions.usage_substitution
            (selected_clause_usage selected.erase capabilities) closed.1 payloadUsage parameter
          have erasedCurrent := DeclaredSources.expression_erase
            (SourceDependencyAnnotations.expression_erase (SourcePlannedSources.expression_erase expression.erase))
          simp only [SourceAnnotatedCode.Term.erase_subst] at erasedCurrent
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
            cut.erase (RecursiveCapture.fresh_unowned pending.erase.source.source.erase.erase.source.erase freshErased)
          simp only [SourceAnnotatedRuntime.Handler.erase] at phaseSame
          have consumed := phaseSame ▸ OwnerPhaseTransitions.spend_self
            (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.erase.port)
              handler.erase.answer capture.erase handler.erase.scope tail.erase))) owner
          have afterOwner := OwnerPhaseTransitions.trace_monotone (RecursiveRequirements.checked_trace savedAfter) consumed
          have pendingReady : RecursiveRequirements.Checked
              (((⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: resumes) ++ disposals) []
              (OwnerPhaseTransitions.spendAll (OwnerPhaseTransitions.available
                (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.erase.answer capture.erase handler.erase.scope tail.erase))) clauseDemand)
              (.sequence (.spent owner) tailReq) tailRow := by
            rw [PhaseRechecking.spendAll_permutation sameDemand]
            simpa only [SourceAnnotatedRuntime.Handler.erase, SourceAnnotatedRuntime.Stack.erase, OwnerPhaseTransitions.spendAll, phaseSame, List.nil_append] using
              (RecursiveRequirements.Checked.sequence (RecursiveRequirements.Checked.spent (receiving := []) afterOwner) tailAfter)
          have included : clauseRow ++ tailRow ⊆ row := by
            rw [sameRow, pendingRowSame, ← List.append_assoc]
            exact ScopedExpressions.append_subset covered (List.Subset.refl _)
          refine ⟨contract, ⟨capScope, savedHints, saved⟩, ⟨tailScope, waitingHints, waiting⟩,
            ⟨code.subst parameter operand, .ticket binder owner,
              .live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail⟩,
            clauseDemand ++ tailDemand, clauseRow ++ tailRow,
            (by simpa only [SourceAnnotatedRuntime.Handler.erase, SourceAnnotatedRuntime.Stack.erase, SourceAnnotatedRuntime.Configuration.erase,
              SourceAnnotatedCode.Term.erase_subst] using raw), ⟨_, bodies owner, ?_, clauseKept⟩, ?_, included, owned, noDispose, codeNoDispose, rfl, _, operationKnown⟩
          · have phases : OwnerPhaseTransitions.available (ownedTickets
                (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.erase.answer capture.erase handler.erase.scope tail.erase)) =
                OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner := by
              exact OwnerPhaseTransitions.capture_map cut.erase
            apply AtPlan.checked (stack := .live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail) expression (.bound (CoherentSourceTypes.Owners.ports_lookup erasedKnown))
              (phases.symm ▸ nextPending) nextLayout nextTemplates nextMatched (phases.symm ▸ nextLocal) nextUnique
              (RecursiveRequirements.Checked.sequence
                (RecursiveRequirements.checked_prepend_iff.mpr (by simpa only [SourceAnnotatedRuntime.Handler.erase, SourceAnnotatedRuntime.Stack.erase, List.append_nil] using clauseCheck)) pendingReady)
              (checked_footprint_subset accepted included) rfl
          · simpa only [SourceAnnotatedRuntime.Handler.erase, SourceAnnotatedRuntime.Stack.erase, accounting, List.nil_append, demandSame, List.cons_append] using sameDemand.append_right tailDemand

theorem capture_without_closing
    (state : State operations policy contracts tables families required actions annotations world outward outside scope
      (.perform hint (Instantiation.freezeEffect requested) operation operand) whole forest output demand row evidence)
    (cut : SourceAnnotatedRuntime.HandlerCut requested whole capture tail handler)
    (isValue : operand.erase.IsValue)
    (selected : SourceAnnotatedRuntime.ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler.erase) = some offered)
    (freshContract : contracts owner = none) (freshAction : actions owner = none)
    (freshAnnotation : annotations owner = none)
    (unavailable : makePlan capture.erase = none ∨ ¬ InternalUses capture.erase.erase.liveTickets capture.erase.erase.pending)
    (requirementsAtCapture : ∀ {plans : SourceDeclarationPlans.ClausePlans handler.clauses.erase (families handler.erase)},
      evidence (required handler.erase) plans →
      ∀ {modes}, lookupDependencies operation (families handler.erase) = some modes →
      ∀ {capturedScope tailScope} {savedHints : SourceContextualHints.Hints capturedScope}
        {waitingHints : SourceContextualHints.Hints tailScope},
      (saved : Forest savedHints) → (waiting : Forest waitingHints) →
      SourceScheduledNeutral.Cut requested operation offered modes forest saved waiting →
      ∀ {family : Nat → Dependencies} {bodies : ∀ owner, SourceDeclarationPlans.Plan (family owner)},
      SourcePlannedRecipeDeclarations.Selected operation capturedScope.held plans parameter binder code.erase bodies →
      SourceScheduledRequirements.Satisfied outward (actions.insert owner code.erase.requiredActions)
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner) world
        (bodies owner) (.live (owner := owner) saved waiting)) :
    ∃ (contract : SourcePlannedTyping.Contract) (captured waiting : SourceScheduledSavedPlans.Saved)
      (after : SourceAnnotatedRuntime.Configuration) (nextDemand : List Nat) (nextRow : Footprint),
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand.erase, scope, whole.erase⟩ after.erase [.ticket owner] [] ∧
      State operations policy (contracts.insert owner contract) tables families required (actions.insert owner code.erase.requiredActions)
        (annotations.insert owner captured) world outward outside after.scope after.expression after.stack
        (.live (owner := owner) captured.forest waiting.forest) output nextDemand nextRow evidence ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack.erase = owner :: ownedTickets whole.erase ∧
      offered.dispose = false ∧ code.erase.requiredActions.dispose = false ∧
      after = ⟨code.subst parameter operand, .ticket binder owner,
        .live owner (ScopedPorts.embedPort contract.input.erase.erase.port) handler.answer capture handler.scope tail⟩ ∧
      ∃ argument, operations requested operation = some (argument, contract.input) := by
  obtain ⟨contract, captured, waiting, after, nextDemand, nextRow, step, ⟨dependencies, nextPlan, next, _⟩,
    balanced, bounded, owned, noDispose, codeNoDispose, same, sourceInput⟩ :=
    capture_without_closing_retaining noClauseEvidence state cut isValue selected found freshContract freshAction freshAnnotation unavailable (by
      intro plans recipes modes declared capturedScope tailScope savedHints waitingHints saved waiting cut family bodies chosen
      exact ⟨requirementsAtCapture recipes declared saved waiting cut chosen, trivial⟩)
  exact ⟨contract, captured, waiting, after, nextDemand, nextRow, step, next.state,
    balanced, bounded, owned, noDispose, codeNoDispose, same, sourceInput⟩

/-- A constructed closing plan is retained in the shared successor. With an
empty outward guard, support justifies its budget whenever disposal is allowed;
resume-only offers require no closing budget even when a plan exists. -/
theorem capture_with_closing_retaining (currentEvidence : ClauseEvidence)
    (state : State operations policy contracts tables families required actions annotations world [] outside scope
      (.perform hint (Instantiation.freezeEffect requested) operation operand) whole forest output demand row evidence)
    (cut : SourceAnnotatedRuntime.HandlerCut requested whole capture tail handler)
    (isValue : operand.erase.IsValue)
    (selected : SourceAnnotatedRuntime.ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler.erase) = some offered)
    (freshContract : contracts owner = none) (freshAction : actions owner = none)
    (freshAnnotation : annotations owner = none)
    (supported : Supported capture.erase.erase (Admission.outsideResources capture.erase.erase))
    (built : makePlan capture.erase = some closingPlan)
    (internal : InternalUses capture.erase.erase.liveTickets capture.erase.erase.pending)
    (requirementsAtCapture : ∀ {plans : SourceDeclarationPlans.ClausePlans handler.clauses.erase (families handler.erase)},
      evidence (required handler.erase) plans →
      ∀ {modes}, lookupDependencies operation (families handler.erase) = some modes →
      ∀ {capturedScope tailScope} {savedHints : SourceContextualHints.Hints capturedScope}
        {waitingHints : SourceContextualHints.Hints tailScope},
      (saved : Forest savedHints) → (waiting : Forest waitingHints) →
      SourceScheduledNeutral.Cut requested operation offered modes forest saved waiting →
      ∀ {family : Nat → Dependencies} {bodies : ∀ owner, SourceDeclarationPlans.Plan (family owner)},
      SourcePlannedRecipeDeclarations.Selected operation capturedScope.held plans parameter binder code.erase bodies →
      SourceScheduledRequirements.Satisfied [] (actions.insert owner code.erase.requiredActions)
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner) world
        (bodies owner) (.live (owner := owner) saved waiting) ∧
        currentEvidence (bodies owner) (.live (owner := owner) saved waiting)) :
    ∃ (contract : SourcePlannedTyping.Contract) (captured waiting : SourceScheduledSavedPlans.Saved)
      (after : SourceAnnotatedRuntime.Configuration) (nextDemand : List Nat) (nextRow : Footprint),
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand.erase, scope, whole.erase⟩ after.erase [.ticket owner] [] ∧
      (∃ dependencies, ∃ nextPlan : SourceDeclarationPlans.Plan dependencies,
      AtPlan operations policy (contracts.insert owner contract) tables families required (actions.insert owner code.erase.requiredActions)
        (annotations.insert owner captured) world [] outside after.scope after.expression after.stack nextPlan
        (.live (owner := owner) captured.forest waiting.forest) output nextDemand nextRow evidence ∧
      currentEvidence nextPlan (.live (owner := owner) captured.forest waiting.forest)) ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack.erase = owner :: ownedTickets whole.erase ∧
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
    | checked checkedHint metadata node => cases node with
      | perform operationKnown admitted operandSource formed =>
        cases freeze_effect_injective encoded
        cases plan with
        | sequence operandPlan requestPlan =>
          cases requestPlan
          have payload := SourceAnnotatedSources.Values.summary operandSource isValue
          have empty := SourceTemplates.expression_value_demand
            (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase
              (SourcePlannedSources.expression_erase operandSource.erase))) isValue
          cases empty
          have closed := ScopedPorts.typed_value_closed
            ((DeclaredSourceValues.erase (SourceDependencyFrames.value_erase
              (SourcePlannedSources.expression_erase payload.erase))).ports .none) isValue
          have requestContextual := by
            cases contextual with
            | sequence operandCheck requestCheck => exact requestCheck
          obtain ⟨requestRow, pendingRow, currentCheck, pendingCheck, sameRow⟩ :=
            RecursiveRequirements.checked_sequence_parts evaluated
          have requestExport := RecursiveRequirements.checked_complete
            (RecursiveRequirements.checked_prepend_iff.mp currentCheck)
          rw [RecursiveDispatch.request_evaluation
            (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase
              (SourcePlannedSources.expression_erase originalCurrent.erase))) isValue] at requestExport
          have requestCheck : RecursiveRequirements.Checked (resumes ++ disposals) (OwnerPhases.ofStack tables whole.erase)
              (OwnerPhaseTransitions.available (ownedTickets whole.erase))
              (.request [] [⟨requested, operation, false⟩]) requestRow :=
            RecursiveRequirements.evaluate_sound (by
              simpa only [SourceAnnotatedRuntime.Handler.erase, SourceAnnotatedRuntime.Stack.erase, RecursiveContexts.evaluate_request, List.nil_append, List.append_nil] using requestExport)
          obtain ⟨actualOffer, offeredRow, actualFound, mode, rowKnown, exported⟩ :=
            RecursiveDispatch.cut_residual cut.erase (by
              simpa only [SourceAnnotatedRuntime.Handler.erase, SourceAnnotatedRuntime.Stack.erase, List.append_nil, OwnerSource.exportAt, OwnerPhaseTransitions.project_actual] using requestExport)
          cases Option.some.inj (actualFound.symm.trans found)
          simp only [Bool.false_or] at rowKnown
          have capabilities : ClausesUse policy handler.erase.clauses := by
            obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords,
              capScope, tailScope, annotation, frame, saved, waiting, rest⟩ :=
              SourceDependencyFrames.capture_segments cut.erase pending.erase.source.source.erase
            cases frame with
            | handler scope annotation clauses coverage unique declarations capabilities modes => exact capabilities
          obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capScope, tailScope,
            resumeEffects, closeEffects, family, captureRow, tailRow, closingRaw, closeReq,
            raw, owned, nextUnique, scopeSame, demandSame, clauseContextual, nextRetained, kept, certificate,
            pendingRowSame, savedCheck, tailCheck, balance, parts⟩ :=
            SourceAnnotatedAllocation.allocate_retaining currentEvidence operations contracts _ _ cut pending matched requestContextual
              selected found rowKnown operationKnown payload closed freshContract freshAction closing templates freshAnnotation
              built internal (by simpa only [SourceAnnotatedRuntime.Handler.erase, SourceAnnotatedRuntime.Stack.erase, OwnerPhaseTransitions.spendAll] using pendingCheck) unique requestCheck requirementsAtCapture
              (outside := outside) (caller := scope)
          dsimp only at parts
          obtain ⟨⟨refinedAnswer, bodies, savedHints, waitingHints, saved, waiting, answerSame, exactErasure,
            nextMatched, nextLocal, body, nextPending, exactTemplate, legacyTemplate, nextTemplates, clauseKept⟩,
            oldBody, oldPending, nextBound, nextTemplate, nextLayout, oldTemplates,
            savedAfter, tailAfter, resumeCheck, disposeCheck, clauseReady⟩ := parts
          let allocated : SourceDependencyAnnotations.Contract :=
            ⟨input.erase, answer, capScope.held, capDemand, captureRow, OwnerClosingSource.retirements closingPlan,
              RecursiveRequirements.evaluate [] (OwnerPhases.ofStack tables tail.erase)
                (OwnerPhaseTransitions.available (ownedTickets whole.erase)) closeReq, resumeEffects, closeEffects⟩
          let contract := SourcePlannedSources.refineContract allocated input refinedAnswer
          have capHeld : capScope.held = ProtectionContexts.protectedMode capture.erase.erase := by
            cases kept with
            | checked annotation scopeKnown saved waiting records resume close typed kept savedMatched waitingMatched clauseKept =>
                exact saved.erase.source.source.matches.realizes.held
          have freshErased : contracts.erase.erase owner = none := by
            simp [SourcePlannedTyping.Contracts.erase, SourceDependencyAnnotations.Contracts.erase, freshContract]
          have phaseSame := RecursiveCapture.capture_phase_consumed (input := ScopedPorts.embedPort input.erase.erase.port)
            cut.erase (RecursiveCapture.fresh_unowned pending.erase.source.source.erase.erase.source.erase freshErased)
          simp only [SourceAnnotatedRuntime.Handler.erase] at phaseSame
          have closingFacts : offered.dispose = true → ∃ closingRow,
              allocated.closeRow = some closingRow ∧ EffectBounds.Covers (requestRow ++ captureRow) closingRow := by
            intro disposes
            obtain ⟨actualPlan, actualReq, actualScope, actualBuilt, typedPlan, template, budget, owners⟩ :=
              SourceDependencySchemes.closed_capture_budget cut.erase pending.erase.source.source.erase requestContextual.erase.erase
                found disposes supported (outside := outside) (budget := row)
            cases Option.some.inj (actualBuilt.symm.trans built)
            obtain ⟨actualClosingRow, closingEvaluated, closingAllowed, closingCovered, callbackAllowed⟩ :=
              DeclaredCallbackAdmission.checked_template nextTemplate.erase built nextUnique
                (nextTemplate.closed_budget typedPlan (budget := requestRow ++ captureRow) (outside := outside)) (store := [])
            exact ⟨actualClosingRow, by simpa only [SourceAnnotatedRuntime.Handler.erase, SourceAnnotatedRuntime.Stack.erase, phaseSame] using closingEvaluated, closingCovered⟩
          let afterPhases := OwnerPhaseTransitions.available (ownedTickets
            (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.erase.answer capture.erase handler.erase.scope tail.erase))
          have callerReady : ∀ other ∈ activeTickets tail.erase, afterPhases other = .available := by
            intro other member
            apply if_pos
            exact List.mem_cons.mpr (Or.inr (List.mem_append_right _ (active_tickets_owned tail.erase member)))
          have exportAfter : OwnerSource.exportAt (OwnerPhases.ofStack tables tail.erase) afterPhases offeredRow = some requestRow :=
            (RecursivePlanAdmission.caller_export callerReady).trans exported
          have interface : ClauseRowAdmission.Interface owner allocated.erase offered.dispose
              (((⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: resumes) ++
                ((⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements closingPlan, closeReq⟩) :: disposals))
              (OwnerPhases.ofStack tables tail.erase) afterPhases requestRow := by
            refine ⟨?_, ?_, ?_, ?_, OwnerPhaseTransitions.capture_tail_fresh cut.erase (RecursiveCapture.fresh_unowned pending.erase.source.source.erase.erase.source.erase freshErased), ?_⟩
            · simpa only [SourceAnnotatedRuntime.Handler.erase, SourceAnnotatedRuntime.Stack.erase, afterPhases, OwnerPhases.ofStack, allocated, SourceDependencyAnnotations.Contract.erase, capHeld] using resumeCheck
            · intro _ closingRow same
              simpa only [SourceAnnotatedRuntime.Handler.erase, SourceAnnotatedRuntime.Stack.erase, afterPhases, OwnerPhases.ofStack, allocated, SourceDependencyAnnotations.Contract.erase, capHeld] using disposeCheck closingRow same
            · intro disposes
              obtain ⟨closingRow, same, covered⟩ := closingFacts disposes
              exact ⟨closingRow, same⟩
            · intro disposes closingRow same
              obtain ⟨actualClosingRow, closeSame, closingCovered⟩ := closingFacts disposes
              cases Option.some.inj (closeSame.symm.trans same)
              exact closingCovered
            · intro _
              change ∀ other ∈ OwnerClosingSource.retirements closingPlan, other ∉ OwnerPhaseTransitions.liveNames (OwnerPhases.ofStack tables tail.erase)
              exact OwnerPhaseTransitions.owned_closing_demand_separate_at_live
                (OwnerClosingSource.retirements_capture built) nextUnique
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
                (SourcePlannedSources.expression_erase payload.erase))) rfl
            have clauseUsage := ScopedExpressions.usage_substitution
              (selected_clause_usage selected.erase capabilities) closed.1 payloadUsage parameter
            have erasedCurrent := DeclaredSources.expression_erase
              (SourceDependencyAnnotations.expression_erase (SourcePlannedSources.expression_erase expression.erase))
            simp only [SourceAnnotatedCode.Term.erase_subst] at erasedCurrent
            have completed := RecursiveClauseUsage.consuming_usage_completed erasedCurrent clauseUsage clauseCheck
            have balanced : contract.erase.erase.closeDemand.Perm contract.erase.erase.resumeDemand := balance
            have sameDemand := RecursiveClauseOwnership.consuming_clause_balance erasedCurrent erasedKnown clauseCheck
              (by simp [afterPhases, OwnerPhaseTransitions.available, ownedTickets]) completed balanced
            change clauseDemand.Perm (owner :: capDemand) at sameDemand
            have consumed := phaseSame ▸ OwnerPhaseTransitions.spend_self
              (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.erase.port)
                handler.erase.answer capture.erase handler.erase.scope tail.erase))) owner
            have afterOwner := OwnerPhaseTransitions.trace_monotone (RecursiveRequirements.checked_trace savedAfter) consumed
            have pendingReady : RecursiveRequirements.Checked
                (((⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: resumes) ++
                  ((⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements closingPlan, closeReq⟩) :: disposals)) []
                (OwnerPhaseTransitions.spendAll (OwnerPhaseTransitions.available
                  (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.erase.answer capture.erase handler.erase.scope tail.erase))) clauseDemand)
                (.sequence (.spent owner) tailReq) tailRow := by
              rw [PhaseRechecking.spendAll_permutation sameDemand]
              simpa only [SourceAnnotatedRuntime.Handler.erase, SourceAnnotatedRuntime.Stack.erase, OwnerPhaseTransitions.spendAll, phaseSame, List.nil_append] using
                (RecursiveRequirements.Checked.sequence (RecursiveRequirements.Checked.spent (receiving := []) afterOwner) tailAfter)
            have included : clauseRow ++ tailRow ⊆ row := by
              rw [sameRow, pendingRowSame, ← List.append_assoc]
              exact ScopedExpressions.append_subset covered (List.Subset.refl _)
            refine ⟨contract, ⟨capScope, savedHints, saved⟩, ⟨tailScope, waitingHints, waiting⟩,
              ⟨code.subst parameter operand, .ticket binder owner,
                .live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail⟩,
              clauseDemand ++ tailDemand, clauseRow ++ tailRow,
              (by simpa only [SourceAnnotatedRuntime.Handler.erase, SourceAnnotatedRuntime.Stack.erase, SourceAnnotatedRuntime.Configuration.erase,
              SourceAnnotatedCode.Term.erase_subst] using raw), ⟨_, bodies owner, ?_, clauseKept⟩, ?_, included, owned, rfl, _, operationKnown⟩
            · have phases : OwnerPhaseTransitions.available (ownedTickets
                  (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.erase.answer capture.erase handler.erase.scope tail.erase)) =
                  OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner := by
                exact OwnerPhaseTransitions.capture_map cut.erase
              apply AtPlan.checked (stack := .live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail) expression (.bound (CoherentSourceTypes.Owners.ports_lookup erasedKnown))
                (phases.symm ▸ nextPending)
                  (by simpa only [SourceAnnotatedRuntime.Handler.erase, SourceAnnotatedRuntime.Stack.erase, SourcePlannedTyping.contracts_erase_insert, exactErasure] using nextLayout) nextTemplates nextMatched (phases.symm ▸ nextLocal) nextUnique
                (RecursiveRequirements.Checked.sequence
                  (RecursiveRequirements.checked_prepend_iff.mpr (by simpa only [SourceAnnotatedRuntime.Handler.erase, SourceAnnotatedRuntime.Stack.erase, List.append_nil, afterPhases, OwnerPhases.ofStack] using clauseCheck)) pendingReady)
                (checked_footprint_subset accepted included) rfl
            · simpa only [SourceAnnotatedRuntime.Handler.erase, SourceAnnotatedRuntime.Stack.erase, accounting, List.nil_append, demandSame, List.cons_append] using sameDemand.append_right tailDemand

theorem capture_with_closing
    (state : State operations policy contracts tables families required actions annotations world [] outside scope
      (.perform hint (Instantiation.freezeEffect requested) operation operand) whole forest output demand row evidence)
    (cut : SourceAnnotatedRuntime.HandlerCut requested whole capture tail handler)
    (isValue : operand.erase.IsValue)
    (selected : SourceAnnotatedRuntime.ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler.erase) = some offered)
    (freshContract : contracts owner = none) (freshAction : actions owner = none)
    (freshAnnotation : annotations owner = none)
    (supported : Supported capture.erase.erase (Admission.outsideResources capture.erase.erase))
    (built : makePlan capture.erase = some closingPlan)
    (internal : InternalUses capture.erase.erase.liveTickets capture.erase.erase.pending)
    (requirementsAtCapture : ∀ {plans : SourceDeclarationPlans.ClausePlans handler.clauses.erase (families handler.erase)},
      evidence (required handler.erase) plans →
      ∀ {modes}, lookupDependencies operation (families handler.erase) = some modes →
      ∀ {capturedScope tailScope} {savedHints : SourceContextualHints.Hints capturedScope}
        {waitingHints : SourceContextualHints.Hints tailScope},
      (saved : Forest savedHints) → (waiting : Forest waitingHints) →
      SourceScheduledNeutral.Cut requested operation offered modes forest saved waiting →
      ∀ {family : Nat → Dependencies} {bodies : ∀ owner, SourceDeclarationPlans.Plan (family owner)},
      SourcePlannedRecipeDeclarations.Selected operation capturedScope.held plans parameter binder code.erase bodies →
      SourceScheduledRequirements.Satisfied [] (actions.insert owner code.erase.requiredActions)
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner) world
        (bodies owner) (.live (owner := owner) saved waiting)) :
    ∃ (contract : SourcePlannedTyping.Contract) (captured waiting : SourceScheduledSavedPlans.Saved)
      (after : SourceAnnotatedRuntime.Configuration) (nextDemand : List Nat) (nextRow : Footprint),
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand.erase, scope, whole.erase⟩ after.erase [.ticket owner] [] ∧
      State operations policy (contracts.insert owner contract) tables families required (actions.insert owner code.erase.requiredActions)
        (annotations.insert owner captured) world [] outside after.scope after.expression after.stack
        (.live (owner := owner) captured.forest waiting.forest) output nextDemand nextRow evidence ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack.erase = owner :: ownedTickets whole.erase ∧
      after = ⟨code.subst parameter operand, .ticket binder owner,
        .live owner (ScopedPorts.embedPort contract.input.erase.erase.port) handler.answer capture handler.scope tail⟩ ∧
      ∃ argument, operations requested operation = some (argument, contract.input) := by
  obtain ⟨contract, captured, waiting, after, nextDemand, nextRow, step, ⟨dependencies, nextPlan, next, _⟩,
    balanced, bounded, owned, same, sourceInput⟩ :=
    capture_with_closing_retaining noClauseEvidence state cut isValue selected found freshContract freshAction freshAnnotation supported built internal (by
      intro plans recipes modes declared capturedScope tailScope savedHints waitingHints saved waiting cut family bodies chosen
      exact ⟨requirementsAtCapture recipes declared saved waiting cut chosen, trivial⟩)
  exact ⟨contract, captured, waiting, after, nextDemand, nextRow, step, next.state,
    balanced, bounded, owned, same, sourceInput⟩

/-- All physical one-shot captures preserve the same scheduled state. The
source supplies offer availability and payload closure; classification of the
actual captured stack selects closing allocation or derives disposal denial.
Contextual clause requirements and resource support remain explicit premises. -/
theorem capture_preserves_retaining (currentEvidence : ClauseEvidence)
    (state : State operations policy contracts tables families required actions annotations world [] outside scope
      (.perform hint (Instantiation.freezeEffect requested) operation operand) whole forest output demand row evidence)
    (cut : SourceAnnotatedRuntime.HandlerCut requested whole capture tail handler)
    (isValue : operand.erase.IsValue)
    (selected : SourceAnnotatedRuntime.ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler.erase) = some offered)
    (freshContract : contracts owner = none) (freshAction : actions owner = none)
    (freshAnnotation : annotations owner = none)
    (supported : Supported capture.erase.erase (Admission.outsideResources capture.erase.erase))
    (requirementsAtCapture : ∀ {plans : SourceDeclarationPlans.ClausePlans handler.clauses.erase (families handler.erase)},
      evidence (required handler.erase) plans →
      ∀ {modes}, lookupDependencies operation (families handler.erase) = some modes →
      ∀ {capturedScope tailScope} {savedHints : SourceContextualHints.Hints capturedScope}
        {waitingHints : SourceContextualHints.Hints tailScope},
      (saved : Forest savedHints) → (waiting : Forest waitingHints) →
      SourceScheduledNeutral.Cut requested operation offered modes forest saved waiting →
      ∀ {family : Nat → Dependencies} {bodies : ∀ owner, SourceDeclarationPlans.Plan (family owner)},
      SourcePlannedRecipeDeclarations.Selected operation capturedScope.held plans parameter binder code.erase bodies →
      SourceScheduledRequirements.Satisfied [] (actions.insert owner code.erase.requiredActions)
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner) world
        (bodies owner) (.live (owner := owner) saved waiting) ∧
        currentEvidence (bodies owner) (.live (owner := owner) saved waiting)) :
    ∃ (contract : SourcePlannedTyping.Contract) (captured waiting : SourceScheduledSavedPlans.Saved)
      (after : SourceAnnotatedRuntime.Configuration) (nextDemand : List Nat) (nextRow : Footprint),
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand.erase, scope, whole.erase⟩ after.erase [.ticket owner] [] ∧
      (∃ dependencies, ∃ nextPlan : SourceDeclarationPlans.Plan dependencies,
      AtPlan operations policy (contracts.insert owner contract) tables families required (actions.insert owner code.erase.requiredActions)
        (annotations.insert owner captured) world [] outside after.scope after.expression after.stack nextPlan
        (.live (owner := owner) captured.forest waiting.forest) output nextDemand nextRow evidence ∧
      currentEvidence nextPlan (.live (owner := owner) captured.forest waiting.forest)) ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack.erase = owner :: ownedTickets whole.erase ∧
      after = ⟨code.subst parameter operand, .ticket binder owner,
        .live owner (ScopedPorts.embedPort contract.input.erase.erase.port) handler.answer capture handler.scope tail⟩ ∧
      ∃ argument, operations requested operation = some (argument, contract.input) := by
  classical
  have withoutClosing (unavailable : makePlan capture.erase = none ∨ ¬ InternalUses capture.erase.erase.liveTickets capture.erase.erase.pending) :=
    capture_without_closing_retaining currentEvidence state cut isValue selected found freshContract freshAction freshAnnotation unavailable requirementsAtCapture
  cases built : makePlan capture.erase with
  | none =>
      obtain ⟨contract, captured, waiting, after, nextDemand, nextRow, step, next, balanced, bounded, owned, _, _, same, sourceInput⟩ :=
        withoutClosing (Or.inl built)
      exact ⟨contract, captured, waiting, after, nextDemand, nextRow, step, next, balanced, bounded, owned, same, sourceInput⟩
  | some plan =>
      by_cases internal : InternalUses capture.erase.erase.liveTickets capture.erase.erase.pending
      · exact capture_with_closing_retaining currentEvidence state cut isValue selected found freshContract freshAction freshAnnotation
          supported built internal requirementsAtCapture
      · obtain ⟨contract, captured, waiting, after, nextDemand, nextRow, step, next, balanced, bounded, owned, _, _, same, sourceInput⟩ :=
          withoutClosing (Or.inr internal)
        exact ⟨contract, captured, waiting, after, nextDemand, nextRow, step, next, balanced, bounded, owned, same, sourceInput⟩

theorem capture_preserves
    (state : State operations policy contracts tables families required actions annotations world [] outside scope
      (.perform hint (Instantiation.freezeEffect requested) operation operand) whole forest output demand row evidence)
    (cut : SourceAnnotatedRuntime.HandlerCut requested whole capture tail handler)
    (isValue : operand.erase.IsValue)
    (selected : SourceAnnotatedRuntime.ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler.erase) = some offered)
    (freshContract : contracts owner = none) (freshAction : actions owner = none)
    (freshAnnotation : annotations owner = none)
    (supported : Supported capture.erase.erase (Admission.outsideResources capture.erase.erase))
    (requirementsAtCapture : ∀ {plans : SourceDeclarationPlans.ClausePlans handler.clauses.erase (families handler.erase)},
      evidence (required handler.erase) plans →
      ∀ {modes}, lookupDependencies operation (families handler.erase) = some modes →
      ∀ {capturedScope tailScope} {savedHints : SourceContextualHints.Hints capturedScope}
        {waitingHints : SourceContextualHints.Hints tailScope},
      (saved : Forest savedHints) → (waiting : Forest waitingHints) →
      SourceScheduledNeutral.Cut requested operation offered modes forest saved waiting →
      ∀ {family : Nat → Dependencies} {bodies : ∀ owner, SourceDeclarationPlans.Plan (family owner)},
      SourcePlannedRecipeDeclarations.Selected operation capturedScope.held plans parameter binder code.erase bodies →
      SourceScheduledRequirements.Satisfied [] (actions.insert owner code.erase.requiredActions)
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner) world
        (bodies owner) (.live (owner := owner) saved waiting)) :
    ∃ (contract : SourcePlannedTyping.Contract) (captured waiting : SourceScheduledSavedPlans.Saved)
      (after : SourceAnnotatedRuntime.Configuration) (nextDemand : List Nat) (nextRow : Footprint),
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand.erase, scope, whole.erase⟩ after.erase [.ticket owner] [] ∧
      State operations policy (contracts.insert owner contract) tables families required (actions.insert owner code.erase.requiredActions)
        (annotations.insert owner captured) world [] outside after.scope after.expression after.stack
        (.live (owner := owner) captured.forest waiting.forest) output nextDemand nextRow evidence ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack.erase = owner :: ownedTickets whole.erase ∧
      after = ⟨code.subst parameter operand, .ticket binder owner,
        .live owner (ScopedPorts.embedPort contract.input.erase.erase.port) handler.answer capture handler.scope tail⟩ ∧
      ∃ argument, operations requested operation = some (argument, contract.input) := by
  obtain ⟨contract, captured, waiting, after, nextDemand, nextRow, step, ⟨dependencies, nextPlan, next, _⟩,
    balanced, bounded, owned, same, sourceInput⟩ :=
    capture_preserves_retaining noClauseEvidence state cut isValue selected found freshContract freshAction freshAnnotation
      supported (by
        intro plans recipes modes declared capturedScope tailScope savedHints waitingHints saved waiting cut family bodies chosen
        exact ⟨requirementsAtCapture recipes declared saved waiting cut chosen, trivial⟩)
  exact ⟨contract, captured, waiting, after, nextDemand, nextRow, step, next.state,
    balanced, bounded, owned, same, sourceInput⟩

end Ash.OneShot.SourceAnnotatedRuntimeState

#print axioms Ash.OneShot.SourceAnnotatedRuntimeState.capture_without_closing
#print axioms Ash.OneShot.SourceAnnotatedRuntimeState.capture_with_closing
#print axioms Ash.OneShot.SourceAnnotatedRuntimeState.capture_preserves

#print axioms Ash.OneShot.SourceAnnotatedRuntimeState.capture_without_closing_retaining
#print axioms Ash.OneShot.SourceAnnotatedRuntimeState.capture_with_closing_retaining
#print axioms Ash.OneShot.SourceAnnotatedRuntimeState.capture_preserves_retaining
