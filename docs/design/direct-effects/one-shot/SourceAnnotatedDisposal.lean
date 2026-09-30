import SourceAnnotatedRuntimeResumption
import SourceBoundDisposal
import SourceAnnotatedClosingData

/-! Disposal retains the selected stored closing template and the exact caller
plans. Structural invocation checks supply the closing and waiting schedules;
existing consumption lemmas account for removed owner records. -/
namespace Ash.OneShot.SourceAnnotatedDisposal

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceAnnotatedRuntimeTyping (Segment)
open SourceScheduledChecks (Local Pending)
open SourceScheduledSavedPlans (Saved Matches)
open SourceRetainedPlans (Forest closingForest)
open SourceAnnotatedClosingData (Certificate)
open SourceDependencyOwners (owners)
open RecursiveRequirements (Requirements Store Checked evaluate)
open OwnerPhaseTransitions (available spend spendAll Trace)
open OwnerClosingSource (retirements)
variable {front capture tail : SourceAnnotatedRuntime.Stack}

/-- Extract the actual stored closing template, rebuild the caller from its
scheduled check, and retain the original record and evaluation identities. -/
theorem disposal_parts
    (source : Segment (evidence := evidence) operations policy contracts tables families required actions outward
      (available (ownedTickets (front.erase.append (.live owner inputType answerType capture.erase savedCaller tail.erase)))) world
      (front.append (.live owner inputType answerType capture savedCaller tail)) input output
      demand requirements records forest .nil incoming outgoing)
    (templates : SourceAnnotatedClosingRecords.Records operations policy contracts tables annotations world
      (front.append (.live owner inputType answerType capture savedCaller tail)) disposals)
    (matched : Matches annotations forest)
    (known : contracts owner = some contract)
    (unique : (ownedTickets (front.erase.append (.live owner inputType answerType capture.erase savedCaller tail.erase))).Nodup)
    (scheduled : Local outward actions
      (available (ownedTickets (front.erase.append (.live owner inputType answerType capture.erase savedCaller tail.erase)))) world
      (.invoke (key := ⟨owner, .dispose⟩)) forest)
    (invocation : Checked (records ++ disposals)
      (OwnerPhases.ofStack tables (front.erase.append (.live owner inputType answerType capture.erase savedCaller tail.erase)))
      (available (ownedTickets (front.erase.append (.live owner inputType answerType capture.erase savedCaller tail.erase))))
      (.invoke ⟨owner, .dispose⟩ closingDemand []) closingRow)
    (built : makePlan capture.erase = some plan) :
    ∃ (capturedReq : Requirements contract.resumeDemand) (capturedRecords : Store)
      (waitingReq : Requirements demand) (waitingRecords : Store) (saved waiting : Saved)
      (raw : Footprint) (closeReq : Requirements (retirements plan)),
      closingDemand = retirements plan ∧
      Certificate operations policy contracts tables world capture plan saved.forest raw closeReq ∧
      Pending outward actions
        (spend (available (ownedTickets (front.erase.append (.live owner inputType answerType capture.erase savedCaller tail.erase)))) owner)
        world saved.forest.forClosing (.running waiting.forest) ∧
      Segment (evidence := evidence) operations policy contracts tables families required actions outward
        (spend (available (ownedTickets (front.erase.append (.live owner inputType answerType capture.erase savedCaller tail.erase)))) owner) world
        (front.append (.spent owner answerType savedCaller tail)) input output demand waitingReq waitingRecords
        waiting.forest .nil incoming outgoing ∧
      SourceBoundSnapshots.DiscardForest owner forest (saved.forest.forClosing.append (.running waiting.forest)) ∧
      records.Perm ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedReq⟩) :: (capturedRecords ++ waitingRecords)) ∧
      (∀ key body, (key, body) ∈ capturedRecords → key.owner ∈ ownedTickets capture.erase) ∧
      Matches annotations (saved.forest.forClosing.append (.running waiting.forest)) ∧
      Checked (records ++ disposals)
        (OwnerPhases.ofStack tables (front.erase.append (.spent owner answerType savedCaller tail.erase)))
        (spend (available (ownedTickets (front.erase.append (.live owner inputType answerType capture.erase savedCaller tail.erase)))) owner)
        closeReq closingRow ∧
      ∀ store receiving before, before owner = .consumed →
        evaluate store receiving before waitingReq = evaluate store receiving before requirements := by
  obtain ⟨middle, boundary, firstDemand, secondDemand, firstReq, secondReq, firstRecords, secondRecords,
    firstScope, secondScope, firstHints, secondHints, firstForest, secondForest,
    first, second, sameScope, sameHints, sameForest, sameDemand, sameRecords, evaluation⟩ :=
    SourceAnnotatedRuntimeTyping.segment_split source
  cases sameScope
  cases sameHints
  cases sameForest
  cases second with
  | live actual actionKnown inputAnnotation answerAnnotation scope held saved savedBound rest resume close bound =>
    cases Option.some.inj (actual.symm.trans known)
    rename_i rights capturedRecords savedScope savedHints savedForest savedBoundary remainingRecords tailScope tailHints tailForest tailBoundary tailReq capturedReq
    have absent : owner ∉ owners firstScope := by
      intro member
      have owned := recursive_live_tickets_owned front.erase
        (by simpa only [SourceDependencyOwners.realized_owners first.erase.source.source.matches.realizes] using member)
      have separated := (List.nodup_append.mp (by simpa only [owned_tickets_append] using unique)).2.2
      exact separated owner owned owner List.mem_cons_self rfl
    obtain ⟨access, closingCheck, firstCheck, tailCheck⟩ :=
      (SourceScheduledScopedInvocations.dispose_iff (SourceScheduledResumption.owner_cut_append firstForest absent)).mp scheduled
    obtain ⟨body, selectedContext, looked, ready, selection, bodyChecked⟩ := RecursiveRequirements.checked_invocation invocation
    obtain ⟨actualPlan, raw, closeReq, actualBuilt, bodySame, certificate⟩ :=
      SourceAnnotatedClosingRecords.selected_template source templates matched
        (SourceScheduledResumption.owner_cut_append firstForest absent) looked
        (by simpa only [SourceAnnotatedRuntime.Stack.erase_append, SourceAnnotatedRuntime.Stack.erase] using unique)
        (SourceAnnotatedRuntime.located_below front .here)
    cases Option.some.inj (actualBuilt.symm.trans built)
    have sameClosingDemand := congrArg Sigma.fst bodySame
    change closingDemand = retirements plan at sameClosingDemand
    have sameBody := (Sigma.mk.inj bodySame).2
    subst closingDemand
    cases eq_of_heq sameBody
    simp only [SourceAnnotatedRuntime.Stack.erase] at evaluation
    have firstNext := first.recheck firstCheck
    have boundaryNext := Segment.spent known answerAnnotation scope (rest.recheck tailCheck) bound
    obtain ⟨waitingReq, waitingSource, waitingEvaluation⟩ := SourceAnnotatedRuntimeTyping.segment_append firstNext boundaryNext
      (SourceDependencyProjection.scope_append_nil _).symm (SourcePlannedRecomposition.hints_append_nil _).symm
      (SourceScheduledRecomposition.forest_append_nil _).symm
    simp only [SourceAnnotatedRuntime.Stack.erase] at waitingEvaluation
    have contexts := RecursiveRecomposition.normalize_replaced (front := front.erase) (capture := capture.erase) (tail := tail.erase)
      (input := inputType) (answer := answerType) (caller := savedCaller) (tables := tables) (receiving := [])
      (OwnerPhaseTransitions.spend_self
        (available (ownedTickets (front.erase.append (.live owner inputType answerType capture.erase savedCaller tail.erase)))) owner)
    simp only [List.append_nil] at contexts
    have checkedTemplate := RecursiveTransport.checked_transport bodyChecked (fun _ _ => rfl) contexts
    subst demand
    subst records
    refine ⟨capturedReq, capturedRecords, waitingReq, _, ⟨savedScope, savedHints, savedForest⟩, ⟨_, _, _⟩, raw, closeReq, rfl, certificate,
      closingCheck, waitingSource, .cut firstForest _ _, ?_, ?_, matched.dispose, checkedTemplate, ?_⟩
    · simpa only [List.append_assoc] using RecursiveRecomposition.move_records
        (prefixRecords := firstRecords) (List.Perm.refl _)
    · intro key body member
      exact (RecursiveTransport.record_owners_sublist saved.erase.source.source.erase.erase.source.erase).subset
        (RecursiveTransport.record_owner_member member)
    · intro store receiving before consumed
      rw [waitingEvaluation, evaluation]
      congr 1
      apply RecursiveTransport.evaluate_transport (fun _ _ => rfl)
      simpa only [Stack.append] using
        (RecursiveRecomposition.normalize_replaced (front := .nil) (capture := capture.erase) (tail := tail.erase)
          (input := inputType) (answer := answerType) (caller := savedCaller) (tables := tables) (receiving := receiving) consumed).symm


/-- Disposal preserves the exact scheduled source, closing certificates and
one-shot accounting. Plan typing is the remaining external interface premise
at this source-state layer. -/
theorem discard_segments
    (source : Segment (evidence := evidence) operations policy contracts tables families required actions outward
      (available (ownedTickets (front.erase.append (.live owner inputType answerType capture.erase savedCaller tail.erase)))) world
      (front.append (.live owner inputType answerType capture savedCaller tail)) .unit output
      demand requirements records forest .nil incoming outgoing)
    (templates : SourceAnnotatedClosingRecords.Records operations policy contracts tables annotations world
      (front.append (.live owner inputType answerType capture savedCaller tail)) disposals)
    (matched : Matches annotations forest)
    (layout : DeclaredSourceClosing.Records operations.erase.erase policy contracts.erase.erase tables world
      (front.erase.append (.live owner inputType answerType capture.erase savedCaller tail.erase)) disposals)
    (known : contracts owner = some contract)
    (unique : (ownedTickets (front.erase.append (.live owner inputType answerType capture.erase savedCaller tail.erase))).Nodup)
    (scheduled : Local outward actions
      (available (ownedTickets (front.erase.append (.live owner inputType answerType capture.erase savedCaller tail.erase)))) world
      (.invoke (key := ⟨owner, .dispose⟩)) forest)
    (invocation : Checked (records ++ disposals)
      (OwnerPhases.ofStack tables (front.erase.append (.live owner inputType answerType capture.erase savedCaller tail.erase)))
      (available (ownedTickets (front.erase.append (.live owner inputType answerType capture.erase savedCaller tail.erase))))
      (.invoke ⟨owner, .dispose⟩ closingDemand []) closingRow)
    (pending : Checked (records ++ disposals) []
      (spendAll (available (ownedTickets (front.erase.append (.live owner inputType answerType capture.erase savedCaller tail.erase))))
        (owner :: closingDemand)) requirements pendingRow)
    (built : makePlan capture.erase = some plan)
    (typed : ScopedPorts.PlanTyped operations.erase.erase.ports world contract.closeEffects plan)
    (admitted : contract.closeEffects ⊆ incoming)
    (scope : ScopedPorts.EffectScopeKnown contracts.erase.erase.ports caller) :
    let rawRestored := (closeControl caller plan).append
      (.push (.closing closeId caller) (front.erase.append (.spent owner answerType savedCaller tail.erase)))
    ∃ restored : SourceAnnotatedRuntime.Stack, restored.erase = rawRestored ∧
    (∃ annotated, SourceAnnotatedRuntime.makePlan capture = some annotated ∧
      restored = (SourceAnnotatedRuntime.closeControl caller annotated).append
        (.push (.closing closeId caller) (front.append (.spent owner answerType savedCaller tail)))) ∧
    ∃ (combined : Requirements (retirements plan ++ demand)) (remaining remainingDisposals : Store) (nextForest : Saved),
      closingDemand = retirements plan ∧
      Segment (evidence := evidence) operations policy contracts tables families required actions outward
        (available (ownedTickets restored.erase)) world restored .unit output (retirements plan ++ demand)
        combined remaining nextForest.forest .nil [] outgoing ∧
      DeclaredSourceClosing.Records operations.erase.erase policy contracts.erase.erase tables world restored.erase remainingDisposals ∧
      SourceAnnotatedClosingRecords.Records operations policy contracts tables annotations world restored remainingDisposals ∧
      Matches annotations nextForest.forest ∧
      (ownedTickets restored.erase).Nodup ∧
      Trace (available (ownedTickets (front.erase.append (.live owner inputType answerType capture.erase savedCaller tail.erase)))) [owner]
        (available (ownedTickets restored.erase)) ∧
      Checked (remaining ++ remainingDisposals) [] (available (ownedTickets restored.erase)) combined (closingRow ++ pendingRow) ∧
      SourceBoundSnapshots.DiscardForest owner forest nextForest.forest := by
  have sourceErased := source.erase.source.source.erase.erase.source.erase
  simp only [SourceAnnotatedRuntime.Stack.erase_append, SourceAnnotatedRuntime.Stack.erase] at sourceErased
  obtain ⟨capReq, capRecords, waitingReq, waitingRecords, savedForest, waitingForest, raw, closeReq,
    sameDemand, certificate, closingCheck, waiting, shape, permutation, capturedOwners, matchedAfter, selectedCheck, waitingEvaluation⟩ :=
    disposal_parts source templates matched known unique scheduled invocation built
  subst closingDemand
  obtain ⟨closingStack, closingErasure, closingSource, annotatedPlan, actualBuilt, closingSame⟩ := certificate.materialize
    (evidence := evidence) (families := families) (required := required) closingCheck typed scope
  obtain ⟨plans, selectedTemplate, retained⟩ := certificate.erase
  have template := selectedTemplate.scope (second := caller)
  have fixedSource := Segment.push (SourceAnnotatedRuntimeTyping.Frame.closing
    (identity := closeId) (ScopedPorts.effect_scope_known_has_types scope) (ScopedPorts.EffectFrame.closing scope))
    waiting (List.Subset.refl incoming)
  have ready := (closingSource.input_weaken (List.nil_subset _)).output_weaken admitted
  obtain ⟨combined, restoredSource, evaluation⟩ := SourceAnnotatedRuntimeTyping.segment_append ready fixedSource
    (SourceDependencyProjection.scope_append_nil _).symm (SourcePlannedRecomposition.hints_append_nil _).symm
    (SourceScheduledRecomposition.forest_append_nil _).symm
  let restored : SourceAnnotatedRuntime.Stack := closingStack.append
    (.push (.closing closeId caller) (front.append (.spent owner answerType savedCaller tail)))
  have eraseRestored : restored.erase = (closeControl caller plan).append
      (.push (.closing closeId caller) (front.erase.append (.spent owner answerType savedCaller tail.erase))) := by
    simp only [restored, SourceAnnotatedRuntime.Stack.erase_append, SourceAnnotatedRuntime.Stack.erase,
      SourceAnnotatedRuntime.Frame.erase, closingErasure]
  simp only [SourceAnnotatedRuntime.Stack.erase_append, SourceAnnotatedRuntime.Stack.erase,
    SourceAnnotatedRuntime.Frame.erase] at evaluation
  have accounting := OwnerClosingSource.discard_owned_permutation (front := front.erase) (owner := owner)
    (inputType := inputType) (answerType := answerType) (caller := savedCaller) (tail := tail.erase)
    (scope := caller) (closeId := closeId) built
  obtain ⟨selectedDisposals, capturedDisposals, waitingDisposals, savedLayout, waitingLayout, disposalPermutation, selectedNames⟩ :=
    DeclaredSourceClosing.split_live layout
  let initial := available (ownedTickets (front.erase.append (.live owner inputType answerType capture.erase savedCaller tail.erase)))
  let afterPlan := spendAll initial (owner :: retirements plan)
  have captureConsumed : ∀ other ∈ ownedTickets capture.erase, afterPlan other = .consumed := by
    intro other member
    have scheduled := (OwnerClosingSource.retirements_capture built).mem_iff.mpr member
    simp only [afterPlan, OwnerPhaseTransitions.spendAll_at]
    exact if_pos (List.mem_cons_of_mem owner scheduled)
  have outerConsumed : afterPlan owner = .consumed := by
    simp only [afterPlan, OwnerPhaseTransitions.spendAll_at, List.mem_cons_self, if_true]
  have storePermutation := RecursiveConsumption.discard_store_permutation permutation disposalPermutation
  have removedConsumed : ∀ key body,
      (key, body) ∈ ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capReq⟩) :: (capRecords ++ selectedDisposals ++ capturedDisposals)) →
      afterPlan key.owner = .consumed := by
    intro key body member
    rcases List.mem_cons.mp member with same | rest
    · cases same; exact outerConsumed
    · rcases List.mem_append.mp rest with first | last
      · rcases List.mem_append.mp first with captured | selected
        · exact captureConsumed key.owner (capturedOwners key body captured)
        · rw [selectedNames key body selected]; exact outerConsumed
      · exact captureConsumed key.owner ((DeclaredSourceClosing.owners_sublist savedLayout).subset
          (RecursiveTransport.record_owner_member last))
  have stores : ∀ key : RecursiveRequirements.Key, afterPlan key.owner = .available →
      RecursiveRequirements.lookup key (records ++ disposals) = RecursiveRequirements.lookup key (waitingRecords ++ waitingDisposals) := by
    intro key ready
    exact (RecursiveTransport.lookup_permuted
      (RecursiveRecords.combined_unique sourceErased (DeclaredSourceClosing.records_erase layout) unique)
      storePermutation).trans (RecursiveConsumption.lookup_drop_consumed removedConsumed ready)
  have nextLayout := DeclaredSourceClosing.records_append
    (DeclaredSourceClosing.plan_records (operations := operations.erase.erase) (contracts := contracts.erase.erase) (tables := tables)
      (world := world) (scope := caller) plan)
    (DeclaredSourceClosing.Records.push (frame := .closing closeId caller) waitingLayout)
  have combinedEvaluation : ∀ store outside phases, phases owner = .consumed →
      evaluate store outside phases combined =
        ProtectionResiduals.merge
          (evaluate store
            (OwnerPhases.ofStack tables (Stack.push (.closing closeId caller) (front.erase.append (.spent owner answerType savedCaller tail.erase))) ++ outside)
            phases closeReq)
          (evaluate store outside (spendAll phases (retirements plan)) requirements) := by
    intro store outside phases consumed
    rw [evaluation]
    simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
      RecursiveRecomposition.evaluate_empty, RecursiveRecomposition.merge_empty_left, spendAll]
    rw [waitingEvaluation store outside _ (RecursiveTransport.phases_spendAll_later owner consumed)]
  have transition := OwnerClosingSource.discard_phase_trace (front := front.erase) (owner := owner)
    (inputType := inputType) (answerType := answerType) (caller := savedCaller) (tail := tail.erase)
    (scope := caller) (closeId := closeId) built unique
  have retainedIncluded : waitingDisposals ⊆ disposals := by
    intro entry member
    exact disposalPermutation.mem_iff.mpr (List.mem_append_right _ member)
  have richNext := templates.after_step (nextRoot := restored)
    (by simpa only [eraseRestored] using nextLayout)
    (by simpa only [List.nil_append] using retainedIncluded)
    (fun _ _ located => by
      simp only [restored, closingSame] at located
      exact SourceAnnotatedRuntime.discard_capture_origin located)
    (by simpa only [SourceAnnotatedRuntime.Stack.erase_append, SourceAnnotatedRuntime.Stack.erase] using unique)
  have phases := OwnerPhaseTransitions.trace_result transition
  change available (ownedTickets ((closeControl caller plan).append
    (.push (.closing closeId caller) (front.erase.append (.spent owner answerType savedCaller tail.erase))))) = spend initial owner at phases
  change Segment _ _ _ _ _ _ _ _ (spend initial owner) _ _ _ _ _ _ _ _ _ _ _ _ at restoredSource
  have nextPhases : available (ownedTickets restored.erase) = spend initial owner := by
    rw [eraseRestored]
    exact phases
  rw [← nextPhases] at restoredSource
  refine ⟨restored, eraseRestored, ⟨annotatedPlan, actualBuilt, by simp only [restored, closingSame]⟩, combined, waitingRecords, waitingDisposals, ⟨_, _, _⟩, rfl,
    by simpa only [List.nil_append] using restoredSource,
    by simpa only [eraseRestored, List.nil_append] using nextLayout,
    by simpa only [List.nil_append] using richNext,
    matchedAfter,
    by rw [eraseRestored]; exact (List.nodup_cons.mp (accounting.nodup unique)).2,
    by rw [eraseRestored]; exact transition, ?_, shape⟩
  · have pendingCollected := RecursiveTransport.checked_transport pending stores rfl
    apply RecursiveRequirements.evaluate_sound
    rw [nextPhases, combinedEvaluation _ [] _ (OwnerPhaseTransitions.spend_self _ owner), List.append_nil,
      RecursiveConsumption.template_guard (DeclaredSourceClosing.template_erase template.erase.erase),
      ← RecursiveConsumption.template_store (first := records ++ disposals)
        (DeclaredSourceClosing.template_erase template.erase.erase), RecursiveRequirements.checked_complete selectedCheck]
    simp only [spendAll] at pendingCollected
    rw [RecursiveRequirements.checked_complete pendingCollected]
    rfl


/-- Ready disposal preserves the complete scheduled state when its actual
closing plan has the advertised effect interface. Scheduling and stored-template
identity follow from the state; they are not supplied for the successor. -/
theorem discard_cut_preserves_snapshot
    (snapshot : SourceBoundSnapshots.Snapshot world)
    (state : SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
      caller (.discard hint binder) (front.append (.live owner inputType answerType capture savedCaller tail))
      snapshot.plan snapshot.forest output demand row evidence)
    (known : contracts owner = some contract) (resolved : caller.resolve binder = some owner)
    (built : makePlan capture.erase = some plan)
    (typed : ScopedPorts.PlanTyped operations.erase.erase.ports world contract.closeEffects plan) :
    ∃ restored : SourceAnnotatedRuntime.Stack, ∃ remaining, ∃ nextSnapshot : SourceBoundSnapshots.Snapshot world,
      restored.erase = (closeControl caller plan).append
        (.push (.closing closeId caller) (front.erase.append (.spent owner answerType savedCaller tail.erase))) ∧
      RawStep ⟨.discard binder, caller, front.erase.append (.live owner inputType answerType capture.erase savedCaller tail.erase)⟩
        ⟨.unit, caller, restored.erase⟩ [.close closeId] [.ticket owner] ∧
      SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
        caller (.unit .unit) restored nextSnapshot.plan nextSnapshot.forest output remaining row evidence ∧
      demand = owner :: remaining ∧
      (ownedTickets (front.erase.append (.live owner inputType answerType capture.erase savedCaller tail.erase))).Perm
        (owner :: ownedTickets restored.erase) ∧
      Trace (available (ownedTickets (front.erase.append (.live owner inputType answerType capture.erase savedCaller tail.erase)))) [owner]
        (available (ownedTickets restored.erase)) ∧
      (∃ annotated, SourceAnnotatedRuntime.makePlan capture = some annotated ∧
        restored = (SourceAnnotatedRuntime.closeControl caller annotated).append
          (.push (.closing closeId caller) (front.append (.spent owner answerType savedCaller tail)))) ∧
      SourceBoundSnapshots.Discarded owner snapshot nextSnapshot := by
  rcases snapshot with ⟨dependencies, sourcePlan, bounds, receiving, hints, forest, pendingBounds⟩
  cases state with
  | checked current scopeTyped pendingSource closing templates matched contextual unique evaluated accepted accounting =>
    rename_i allowed input currentDemand currentRequirements ticket pendingDemand pendingRequirements resumes disposals
    simp only [SourceAnnotatedRuntime.Stack.erase_append, SourceAnnotatedRuntime.Stack.erase] at pendingSource closing templates contextual unique evaluated
    subst demand
    generalize signatureSame : SourcePlanSignatures.signature sourcePlan = currentSignature at current
    cases current with
    | checked checkedHint metadata node => cases node with
      | discard actualKnown sourceResolved permission unprotected admitted =>
        cases Option.some.inj (sourceResolved.symm.trans resolved)
        cases Option.some.inj (actualKnown.symm.trans known)
        cases sourcePlan
        obtain ⟨closingRow, pendingRow, currentChecked, pendingChecked, rows⟩ :=
          RecursiveRequirements.checked_sequence_parts evaluated
        have invocation := RecursiveRequirements.checked_prepend_iff.mp currentChecked
        simp only [List.append_nil] at invocation
        obtain ⟨restored, erasedRestored, provenance, combined, nextResumes, nextDisposals, nextForest, sameDemand, combinedSource, nextClosing,
          nextTemplates, nextMatches, afterUnique, transition, combinedCheck, shape⟩ :=
          discard_segments pendingSource templates matched closing known unique contextual invocation pendingChecked
            built typed admitted ⟨_, scopeTyped⟩ (closeId := closeId)
        have acceptedAfter : checkFootprint outside (closingRow ++ pendingRow) = true := by simpa only [rows] using accepted
        have summary : SourceAnnotatedSources.ValueSummary operations policy contracts world (fun _ => none) []
            (.unit .unit) .unit := .checked rfl rfl .unit
        have afterValid := SourceAnnotatedRuntimeReturns.value_configuration_atPlan summary trivial scopeTyped combinedSource nextClosing
          nextTemplates nextMatches afterUnique combinedCheck acceptedAfter
        rw [← rows] at afterValid
        obtain ⟨nextPending, moved⟩ := shape.snapshot
          (before := ⟨_, _, bounds, _, _, forest, pendingBounds⟩)
        exact ⟨restored, _, SourceBoundSnapshots.Snapshot.value nextPending, erasedRestored,
          by rw [erasedRestored]; exact RawStep.discard binder owner closeId caller savedCaller inputType answerType front.erase capture.erase tail.erase plan resolved built,
          afterValid, by simp only [sameDemand, List.cons_append],
          by rw [erasedRestored]; exact OwnerClosingSource.discard_owned_permutation built, transition, provenance, moved⟩

theorem discard_cut_preserves
    (state : SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
      caller (.discard hint binder) (front.append (.live owner inputType answerType capture savedCaller tail))
      forest output demand row evidence)
    (known : contracts owner = some contract) (resolved : caller.resolve binder = some owner)
    (built : makePlan capture.erase = some plan)
    (typed : ScopedPorts.PlanTyped operations.erase.erase.ports world contract.closeEffects plan) :
    ∃ restored : SourceAnnotatedRuntime.Stack, ∃ remaining, ∃ nextForest : Saved,
      restored.erase = (closeControl caller plan).append
        (.push (.closing closeId caller) (front.erase.append (.spent owner answerType savedCaller tail.erase))) ∧
      RawStep ⟨.discard binder, caller, front.erase.append (.live owner inputType answerType capture.erase savedCaller tail.erase)⟩
        ⟨.unit, caller, restored.erase⟩ [.close closeId] [.ticket owner] ∧
      SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
        caller (.unit .unit) restored nextForest.forest output remaining row evidence ∧
      demand = owner :: remaining ∧
      (ownedTickets (front.erase.append (.live owner inputType answerType capture.erase savedCaller tail.erase))).Perm
        (owner :: ownedTickets restored.erase) ∧
      Trace (available (ownedTickets (front.erase.append (.live owner inputType answerType capture.erase savedCaller tail.erase)))) [owner]
        (available (ownedTickets restored.erase)) ∧
      (∃ annotated, SourceAnnotatedRuntime.makePlan capture = some annotated ∧
        restored = (SourceAnnotatedRuntime.closeControl caller annotated).append
          (.push (.closing closeId caller) (front.append (.spent owner answerType savedCaller tail)))) := by
  obtain ⟨dependencies, sourcePlan, indexed⟩ := state.atPlan
  let snapshot : SourceBoundSnapshots.Snapshot world :=
    ⟨dependencies, sourcePlan, .absent, _, _, forest, SourceBoundSnapshots.Retained.absent forest⟩
  obtain ⟨restored, remaining, nextSnapshot, erased, raw, next, accounting, owners, trace, provenance, _⟩ :=
    discard_cut_preserves_snapshot snapshot indexed known resolved built typed (closeId := closeId)
  exact ⟨restored, remaining, ⟨_, _, nextSnapshot.forest⟩, erased, raw, next.state, accounting, owners, trace, provenance⟩

end Ash.OneShot.SourceAnnotatedDisposal

#print axioms Ash.OneShot.SourceAnnotatedDisposal.disposal_parts

#print axioms Ash.OneShot.SourceAnnotatedDisposal.discard_segments

#print axioms Ash.OneShot.SourceAnnotatedDisposal.discard_cut_preserves

#print axioms Ash.OneShot.SourceAnnotatedDisposal.discard_cut_preserves_snapshot
