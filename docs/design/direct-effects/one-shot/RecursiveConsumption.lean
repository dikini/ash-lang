import RecursiveRecords

/-!
Consumption preserves the recursive state with authenticated resume and disposal
records. The physical waiting caller and actual owner map determine checking;
removing a consumed owner removes both modes from the store.
-/

namespace Ash.OneShot.RecursiveConsumption
open ScopedExpressions ScopedExecution CoherentSourceTypes ProtectionContracts ProtectionResiduals
open SourceTemplates (Segment Expression)
open RecursiveRecords (Records CheckedState)
open RecursiveRequirements (Requirements Store Key Checked evaluate)
open OwnerPhaseTransitions (Phases Trace available spend spendAll)

variable {front capture tail : Stack}

theorem remove_owner_append (owner : Nat) (first second : Store) :
    RecursiveTransport.removeOwner owner (first ++ second) =
      RecursiveTransport.removeOwner owner first ++ RecursiveTransport.removeOwner owner second := by
  simp only [RecursiveRecomposition.remove_owner_filter, List.filter_append]

theorem resume_segments
    (source : Segment operations policy contracts tables world
      (front.append (.live owner inputType answerType capture caller tail)) contract.answer output pendingDemand pendingRequirements resumes)
    (closing : Records operations policy contracts tables world
      (front.append (.live owner inputType answerType capture caller tail)) disposals)
    (known : contracts owner = some contract)
    (unique : (ownedTickets (front.append (.live owner inputType answerType capture caller tail))).Nodup)
    (invocation : Checked (resumes ++ disposals)
      (OwnerPhases.ofStack tables (front.append (.live owner inputType answerType capture caller tail)))
      (available (ownedTickets (front.append (.live owner inputType answerType capture caller tail))))
      (.invoke ⟨owner, .resume⟩ contract.resumeDemand []) resumeRow)
    (pending : Checked (resumes ++ disposals) []
      (spendAll (available (ownedTickets (front.append (.live owner inputType answerType capture caller tail))))
        (owner :: contract.resumeDemand)) pendingRequirements pendingRow) :
    ∃ (combined : Requirements (contract.resumeDemand ++ pendingDemand)) (nextResumes nextDisposals : Store),
      Segment operations policy contracts tables world (capture.append (front.append (.spent owner answerType caller tail)))
        contract.input output (contract.resumeDemand ++ pendingDemand) combined nextResumes ∧
      Records operations policy contracts tables world (capture.append (front.append (.spent owner answerType caller tail))) nextDisposals ∧
      Checked (nextResumes ++ nextDisposals) []
        (available (ownedTickets (capture.append (front.append (.spent owner answerType caller tail)))))
        combined (resumeRow ++ pendingRow) ∧
      (RecursiveTransport.removeOwner owner (resumes ++ disposals)).Perm (nextResumes ++ nextDisposals) ∧
      (ownedTickets (capture.append (front.append (.spent owner answerType caller tail)))).Nodup ∧
      Trace (available (ownedTickets (front.append (.live owner inputType answerType capture caller tail)))) [owner]
        (available (ownedTickets (capture.append (front.append (.spent owner answerType caller tail))))) := by
  obtain ⟨capturedReq, capturedRecords, waitingReq, waitingRecords, saved, waiting, permutation, waitingEvaluation⟩ :=
    RecursiveRecomposition.replace_live source known
  obtain ⟨nextDisposals, nextClosing, disposalPermutation⟩ := RecursiveRecords.resume_records closing unique
  have resumeUnique := RecursiveTransport.source_records_unique source unique
  have ownersUnique := (RecursiveTransport.record_owners_sublist source).nodup unique
  have resumePermutation := RecursiveRecomposition.removed_records ownersUnique permutation
  have erasedPermutation : (RecursiveTransport.removeOwner owner (resumes ++ disposals)).Perm
      ((capturedRecords ++ waitingRecords) ++ nextDisposals) := by
    rw [remove_owner_append]
    exact resumePermutation.append disposalPermutation
  have keysUnique := RecursiveRecords.combined_unique source closing unique
  have erasedUnique := RecursiveTransport.remove_owner_unique (owner := owner) keysUnique
  have capturedKnown := RecursiveRecords.lookup_append (second := disposals)
    (RecursiveTransport.lookup_of_member resumeUnique (permutation.mem_iff.mpr List.mem_cons_self))
  obtain ⟨body, selectedContext, actual, ready, selection, bodyChecked⟩ := RecursiveRequirements.checked_invocation invocation
  have sameTemplate := Option.some.inj (actual.symm.trans capturedKnown)
  have sameBody := eq_of_heq (Sigma.mk.inj sameTemplate).2
  subst body
  let initial := available (ownedTickets (front.append (.live owner inputType answerType capture caller tail)))
  have consumed : spend initial owner owner = .consumed := OwnerPhaseTransitions.spend_self initial owner
  have contexts : RecursiveTransport.normalize (spend initial owner)
      (OwnerPhases.ofStack tables (front.append (.live owner inputType answerType capture caller tail))) =
      RecursiveTransport.normalize (spend initial owner)
        (OwnerPhases.ofStack tables (front.append (.spent owner answerType caller tail))) := by
    simpa only [List.append_nil] using (RecursiveRecomposition.normalize_replaced (front := front) (capture := capture) (tail := tail)
      (input := inputType) (answer := answerType) (caller := caller) (tables := tables) (receiving := []) consumed)
  have bodyWaiting := RecursiveTransport.checked_transport bodyChecked
    (RecursiveTransport.remove_consumed_agrees consumed) contexts
  have bodyCollected := RecursiveTransport.checked_permuted bodyWaiting erasedUnique erasedPermutation
  have consumedAfter : spendAll initial (owner :: contract.resumeDemand) owner = .consumed := by
    rw [OwnerPhaseTransitions.spendAll_at, if_pos List.mem_cons_self]
  have pendingWaiting : Checked (resumes ++ disposals) []
      (spendAll initial (owner :: contract.resumeDemand)) waitingReq pendingRow := by
    apply RecursiveRequirements.evaluate_sound
    rw [waitingEvaluation (resumes ++ disposals) [] _ consumedAfter]
    exact RecursiveRequirements.checked_complete pending
  have pendingErased := RecursiveTransport.checked_remove_consumed pendingWaiting consumedAfter
  have pendingCollected := RecursiveTransport.checked_permuted pendingErased erasedUnique erasedPermutation
  obtain ⟨combined, combinedSource, combinedCheck⟩ := RecursiveRecomposition.segment_append_checked saved waiting
    (receiving := []) (by simpa only [List.append_nil] using bodyCollected) pendingCollected
  have trace := OwnerPhaseTransitions.resume_phase_trace unique
  have actualPhases := OwnerPhaseTransitions.trace_result trace
  change available (ownedTickets (capture.append (front.append (.spent owner answerType caller tail)))) =
    spend initial owner at actualPhases
  rw [← actualPhases] at combinedCheck
  have afterUnique := (List.nodup_cons.mp (OwnerPhaseTransitions.resume_owned_permutation.nodup unique)).2
  exact ⟨combined, _, nextDisposals, combinedSource, nextClosing, combinedCheck, erasedPermutation, afterUnique, trace⟩

theorem resume_cut_preserves
    (source : CheckedState operations policy contracts tables world outside scope (.resume binder value)
      (front.append (.live owner inputType answerType capture caller tail)) output demand row)
    (resolved : scope.resolve binder = some owner) (closed : ClosedValue value) :
    ∃ remaining, CheckedState operations policy contracts tables world outside scope value
      (capture.append (front.append (.spent owner answerType caller tail))) output remaining row ∧
      demand = owner :: remaining ∧
      Trace (available (ownedTickets (front.append (.live owner inputType answerType capture caller tail)))) [owner]
        (available (ownedTickets (capture.append (front.append (.spent owner answerType caller tail))))) := by
  cases source with
  | checked source closing unique evaluated accepted => cases source with
      | checked current scopeTyped pendingSource => cases current with
          | stable summary => cases summary
          | callable summary => cases summary
          | resume known sourceResolved permission operand admitted formed =>
              rename_i actualOwner contract operandDemand operandRequirements
              have sameOwner := Option.some.inj (sourceResolved.symm.trans resolved)
              subst actualOwner
              have noDemand := SourceTemplates.expression_value_demand operand closed.1
              obtain ⟨currentRow, pendingRow, currentChecked, pendingChecked, rows⟩ :=
                RecursiveRequirements.checked_sequence_parts evaluated
              have currentAt := RecursiveRequirements.checked_prepend_iff.mp currentChecked
              simp only [List.append_nil] at currentAt
              obtain ⟨operandRow, resumeRow, operandChecked, resumeChecked, currentRows⟩ :=
                RecursiveRequirements.checked_sequence_parts currentAt
              have operandEmpty := Option.some.inj ((RecursiveRequirements.checked_complete operandChecked).symm.trans
                (RecursiveRecomposition.value_evaluation operand closed.1))
              subst operandRow
              simp only [List.nil_append] at currentRows
              subst currentRow
              simp only [noDemand, List.nil_append, spendAll] at resumeChecked pendingChecked
              obtain ⟨combined, nextResumes, nextDisposals, combinedSource, nextClosing, combinedCheck, permutation, afterUnique, trace⟩ :=
                resume_segments pendingSource closing known unique resumeChecked pendingChecked
              let restored := capture.append (front.append (.spent owner answerType caller tail))
              have valueChecked : Checked (nextResumes ++ nextDisposals) [] (available (ownedTickets restored))
                  (.request (OwnerPhases.ofStack tables restored) []) [] := .request (by simp [OwnerSource.exportAt, residual_empty])
              have afterSource := SourceTemplates.Configuration.checked
                ((RecursiveRecomposition.value_summary operand closed.1).expression _) scopeTyped combinedSource
              have acceptedAfter : checkFootprint outside (resumeRow ++ pendingRow) = true := by simpa only [rows] using accepted
              have afterValid := CheckedState.checked afterSource nextClosing afterUnique
                (Checked.sequence valueChecked combinedCheck) acceptedAfter
              rw [← rows] at afterValid
              refine ⟨_, afterValid, ?_, trace⟩
              simp only [noDemand, List.nil_append, List.cons_append]

theorem resume_step_preserves
    (source : CheckedState operations policy contracts tables world outside scope (.resume binder value) stack output demand row)
    (closed : ClosedValue value) (step : RawStep ⟨.resume binder value, scope, stack⟩ next created completed) :
    ∃ owner remaining, next.expression = value ∧ next.scope = scope ∧
      CheckedState operations policy contracts tables world outside next.scope next.expression next.stack output remaining row ∧
      demand = owner :: remaining ∧ created = [] ∧ completed = [.ticket owner] ∧
      Trace (available (ownedTickets stack)) [owner] (available (ownedTickets next.stack)) := by
  cases step with
  | focus plain focus tail => exact False.elim (RecursiveRecomposition.focus_resume_not_value focus closed.1)
  | plug plain value impossible scope tail => cases impossible.1
  | leaveHandler handler value impossible scope tail => cases impossible.1
  | leaveCell identity payload answer savedScope scope value impossible tail => cases impossible.1
  | startCleanup action saved impossible scope tail => cases impossible.1
  | leaveClause ticket answer value impossible scope caller tail => cases impossible.1
  | resume binder owner scope caller inputType answerType front capture tail value ready resolved =>
      obtain ⟨remaining, checked, demand, trace⟩ := resume_cut_preserves source resolved closed
      exact ⟨owner, remaining, rfl, rfl, checked, demand, rfl, rfl, trace⟩

theorem resume_progress
    (source : CheckedState operations policy contracts tables world outside scope (.resume binder value) stack output demand row)
    (closed : ClosedValue value) :
    ∃ owner restored, RawStep ⟨.resume binder value, scope, stack⟩ ⟨value, scope, restored⟩ [] [.ticket owner] := by
  cases source with
  | checked source closing unique evaluated accepted => cases source with
      | checked current scopeTyped pending => cases current with
          | stable summary => cases summary
          | callable summary => cases summary
          | resume known resolved permission operand admitted formed =>
              have noDemand := SourceTemplates.expression_value_demand operand closed.1
              obtain ⟨currentRow, pendingRow, currentChecked, pendingChecked, rows⟩ := RecursiveRequirements.checked_sequence_parts evaluated
              have currentAt := RecursiveRequirements.checked_prepend_iff.mp currentChecked
              simp only [List.append_nil] at currentAt
              obtain ⟨operandRow, resumeRow, operandChecked, resumeChecked, currentRows⟩ := RecursiveRequirements.checked_sequence_parts currentAt
              rw [noDemand] at resumeChecked
              obtain ⟨body, waiting, looked, ready, selection, bodyCheck⟩ := RecursiveRequirements.checked_invocation resumeChecked
              obtain ⟨capture, active⟩ := SourceTemplates.consume_active_capture (OwnerPhases.consumes_sound selection)
              obtain ⟨front, inputType, answerType, caller, tail, same⟩ := SourceTemplates.active_capture_decompose active
              rw [same]
              exact ⟨_, _, .resume _ _ _ _ _ _ _ _ _ _ closed resolved⟩

theorem resume_preserves
    (source : CheckedState operations policy contracts tables world outside scope (.resume binder value) stack output demand row)
    (closed : ClosedValue value) :
    ∃ owner restored remaining,
      RawStep ⟨.resume binder value, scope, stack⟩ ⟨value, scope, restored⟩ [] [.ticket owner] ∧
      CheckedState operations policy contracts tables world outside scope value restored output remaining row ∧
      demand = owner :: remaining ∧ Trace (available (ownedTickets stack)) [owner] (available (ownedTickets restored)) := by
  obtain ⟨owner, restored, step⟩ := resume_progress source closed
  obtain ⟨actual, remaining, valueSame, scopeSame, checked, demand, created, completed, transition⟩ := resume_step_preserves source closed step
  have sameOwner : owner = actual := Owner.ticket.inj (List.cons.inj completed).1
  subst actual
  exact ⟨owner, restored, remaining, step, checked, demand, transition⟩

theorem template_store
    (template : RecursiveClosing.PlanTemplate operations policy contracts tables world scope plan raw requirements) :
    evaluate first receiving before requirements = evaluate second receiving before requirements := by
  induction template generalizing before with
  | nil => simp only [OwnerClosingSource.retirements, RecursiveRecomposition.evaluate_empty]
  | release rest ih =>
      simp only [OwnerClosingSource.retirements, RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
        RecursiveRecomposition.evaluate_empty, spendAll, ih]
  | retire known rest ih =>
      simp only [OwnerClosingSource.retirements, RecursiveRequirements.evaluate_sequence, RecursiveClosing.evaluate_retire, spendAll, ih]
  | invoke callback rest ih =>
      simp only [OwnerClosingSource.retirements, RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
        RecursiveContexts.evaluate_request, spendAll, ih]

theorem guarded_export (fixed : Stack) (identity : Nat) (scope : Execution.Scope) :
    OwnerSource.exportAt (OwnerPhases.ofStack tables (.push (.closing identity scope) fixed)) before (qualify true raw) =
      OwnerSource.exportAt (OwnerPhases.ofStack tables fixed) before (qualify true raw) := by
  simp only [OwnerSource.exportAt, OwnerPhases.ofStack, OwnerPhases.frameEntry, ExecFrame.erase, closeFrame,
    ProtectionContexts.frameProtected, OwnerPhaseTransitions.project, residualize, DisposalProtection.through_barrier,
    qualify_composes, Bool.or_true]

/-- The closing guard adds no new obligation to a plan: every callback demand
    is already protected, and the intervening plan contains only builtins and
    barriers. This does not require an assumption about caller name absence. -/
theorem template_guard
    (template : RecursiveClosing.PlanTemplate operations policy contracts tables world planScope plan raw requirements) :
    evaluate store (OwnerPhases.ofStack tables (.push (.closing identity scope) fixed)) before requirements =
      evaluate store (OwnerPhases.ofStack tables fixed) before requirements := by
  induction template generalizing before with
  | nil => simp only [OwnerClosingSource.retirements, RecursiveRecomposition.evaluate_empty]
  | release rest ih =>
      simp only [OwnerClosingSource.retirements, RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
        RecursiveRecomposition.evaluate_empty, spendAll, ih]
  | retire known rest ih =>
      simp only [OwnerClosingSource.retirements, RecursiveRequirements.evaluate_sequence, RecursiveClosing.evaluate_retire, spendAll, ih]
  | invoke callback rest ih =>
      simp only [OwnerClosingSource.retirements, RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
        RecursiveContexts.evaluate_request, spendAll, RecursiveClosing.callback_evaluation,
        DisposalProtection.callbackResidual, guarded_export, ih]

theorem plan_records (plan : List CloseEntry) :
    Records operations policy contracts tables world (closeControl scope plan) [] := by
  induction plan with
  | nil => exact .nil
  | cons entry rest ih => exact .push ih

theorem discard_store_permutation {entry : Key × RecursiveRequirements.Template}
    {resumes disposals capturedResumes waitingResumes selectedDisposals capturedDisposals waitingDisposals : Store}
    (first : resumes.Perm (entry :: (capturedResumes ++ waitingResumes)))
    (second : disposals.Perm (selectedDisposals ++ capturedDisposals ++ waitingDisposals)) :
    (resumes ++ disposals).Perm
      ((entry :: (capturedResumes ++ selectedDisposals ++ capturedDisposals)) ++ (waitingResumes ++ waitingDisposals)) := by
  have joined := first.append second
  have moved := ((List.perm_append_comm (l₁ := waitingResumes) (l₂ := selectedDisposals ++ capturedDisposals)).append_left
    (entry :: capturedResumes)).append_right waitingDisposals
  exact joined.trans (by simpa only [List.cons_append, List.append_assoc] using moved)

theorem lookup_drop_consumed {before : Phases}
    (consumed : ∀ key body, (key, body) ∈ discarded → before key.owner = .consumed)
    (ready : before key.owner = .available) :
    RecursiveRequirements.lookup key (discarded ++ retained) = RecursiveRequirements.lookup key retained := by
  induction discarded with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨candidate, body⟩ := entry
      have different : key ≠ candidate := by
        intro same
        have spent := consumed candidate body List.mem_cons_self
        rw [← same, ready] at spent
        cases spent
      simp only [List.cons_append, RecursiveRequirements.lookup, different, if_false]
      exact ih (fun key body member => consumed key body (List.mem_cons_of_mem _ member))

theorem certified_plan_at
    (certificate : RecursiveRecords.Certified operations policy contracts tables world stack key body)
    (unique : (ownedTickets stack).Nodup) (located : SourceTemplates.CapturedIn key.owner capture stack) :
    ∃ (plan : List CloseEntry) (raw : Footprint) (requirements : Requirements (OwnerClosingSource.retirements plan)),
      makePlan capture = some plan ∧ body = ⟨OwnerClosingSource.retirements plan, requirements⟩ ∧
      RecursiveClosing.PlanTemplate operations policy contracts tables world .none plan raw requirements := by
  cases certificate with
  | dispose saved built internal template =>
      have same := SourceTemplates.captured_in_unique unique saved located
      cases same
      exact ⟨_, _, _, built, rfl, template⟩

theorem discard_segments
    (source : Segment operations policy contracts tables world
      (front.append (.live owner inputType answerType capture caller tail)) .unit output pendingDemand pendingRequirements resumes)
    (closing : Records operations policy contracts tables world
      (front.append (.live owner inputType answerType capture caller tail)) disposals)
    (known : contracts owner = some contract)
    (unique : (ownedTickets (front.append (.live owner inputType answerType capture caller tail))).Nodup)
    (invocation : Checked (resumes ++ disposals)
      (OwnerPhases.ofStack tables (front.append (.live owner inputType answerType capture caller tail)))
      (available (ownedTickets (front.append (.live owner inputType answerType capture caller tail))))
      (.invoke ⟨owner, .dispose⟩ closingDemand []) closingRow)
    (pending : Checked (resumes ++ disposals) []
      (spendAll (available (ownedTickets (front.append (.live owner inputType answerType capture caller tail))))
        (owner :: closingDemand)) pendingRequirements pendingRow)
    (built : makePlan capture = some plan)
    (scopeKnown : ScopedPorts.ScopeKnown contracts.ports.types scope) (identity : Nat) :
    ∃ (combined : Requirements (OwnerClosingSource.retirements plan ++ pendingDemand)) (nextResumes nextDisposals : Store),
      closingDemand = OwnerClosingSource.retirements plan ∧
      Segment operations policy contracts tables world
        ((closeControl scope plan).append (.push (.closing identity scope) (front.append (.spent owner answerType caller tail))))
        .unit output (OwnerClosingSource.retirements plan ++ pendingDemand) combined nextResumes ∧
      Records operations policy contracts tables world
        ((closeControl scope plan).append (.push (.closing identity scope) (front.append (.spent owner answerType caller tail)))) nextDisposals ∧
      Checked (nextResumes ++ nextDisposals) []
        (available (ownedTickets ((closeControl scope plan).append (.push (.closing identity scope) (front.append (.spent owner answerType caller tail))))))
        combined (closingRow ++ pendingRow) ∧
      (ownedTickets ((closeControl scope plan).append (.push (.closing identity scope) (front.append (.spent owner answerType caller tail))))).Nodup ∧
      Trace (available (ownedTickets (front.append (.live owner inputType answerType capture caller tail)))) [owner]
        (available (ownedTickets ((closeControl scope plan).append (.push (.closing identity scope) (front.append (.spent owner answerType caller tail)))))) := by
  obtain ⟨capturedReq, capturedResumes, waitingReq, waitingResumes, saved, waiting, resumePermutation, waitingEvaluation⟩ :=
    RecursiveRecomposition.replace_live source known
  obtain ⟨selectedDisposals, capturedDisposals, waitingDisposals, savedClosing, waitingClosing, disposalPermutation, selectedNames⟩ :=
    RecursiveRecords.split_live closing
  obtain ⟨body, selectedContext, looked, ready, selection, bodyChecked⟩ := RecursiveRequirements.checked_invocation invocation
  obtain ⟨actualPlan, raw, planReq, actualBuilt, sameTemplate, template⟩ := certified_plan_at
    (RecursiveRecords.lookup_certified source closing looked) unique (RecursiveRecords.located_below front .here)
  have samePlan := Option.some.inj (actualBuilt.symm.trans built)
  subst actualPlan
  have sameDemand := congrArg Sigma.fst sameTemplate
  change closingDemand = OwnerClosingSource.retirements plan at sameDemand
  have sameBody := (Sigma.mk.inj sameTemplate).2
  subst closingDemand
  cases eq_of_heq sameBody
  let initial := available (ownedTickets (front.append (.live owner inputType answerType capture caller tail)))
  let fixed := Stack.push (.closing identity scope) (front.append (.spent owner answerType caller tail))
  let restored := (closeControl scope plan).append fixed
  let afterPlan := spendAll initial (owner :: OwnerClosingSource.retirements plan)
  have ownerConsumed : spend initial owner owner = .consumed := OwnerPhaseTransitions.spend_self initial owner
  have contexts : RecursiveTransport.normalize (spend initial owner)
      (OwnerPhases.ofStack tables (front.append (.live owner inputType answerType capture caller tail))) =
      RecursiveTransport.normalize (spend initial owner)
        (OwnerPhases.ofStack tables (front.append (.spent owner answerType caller tail))) := by
    simpa only [List.append_nil] using (RecursiveRecomposition.normalize_replaced (front := front) (capture := capture) (tail := tail)
      (input := inputType) (answer := answerType) (caller := caller) (tables := tables) (receiving := []) ownerConsumed)
  have bodyWaiting := RecursiveTransport.checked_transport bodyChecked (fun _ _ => rfl) contexts
  have planCheck : Checked (waitingResumes ++ waitingDisposals) (OwnerPhases.ofStack tables fixed)
      (spend initial owner) planReq closingRow := by
    apply RecursiveRequirements.evaluate_sound
    rw [template_guard template, ← template_store (first := resumes ++ disposals) template]
    exact RecursiveRequirements.checked_complete bodyWaiting
  have captureConsumed : ∀ other ∈ ownedTickets capture, afterPlan other = .consumed := by
    intro other member
    have scheduled := (OwnerClosingSource.retirements_capture built).mem_iff.mpr member
    exact OwnerPhaseTransitions.trace_consumed (RecursiveRequirements.checked_trace invocation) (List.mem_cons_of_mem owner scheduled)
  have outerConsumed : afterPlan owner = .consumed := by
    exact OwnerPhaseTransitions.trace_consumed (RecursiveRequirements.checked_trace invocation) List.mem_cons_self
  have permutation := discard_store_permutation resumePermutation disposalPermutation
  have removedConsumed : ∀ key body,
      (key, body) ∈ ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedReq⟩) :: (capturedResumes ++ selectedDisposals ++ capturedDisposals)) →
      afterPlan key.owner = .consumed := by
    intro key body member
    rcases List.mem_cons.mp member with same | rest
    · cases same; exact outerConsumed
    · rcases List.mem_append.mp rest with first | last
      · rcases List.mem_append.mp first with captured | selected
        · exact captureConsumed key.owner ((RecursiveTransport.record_owners_sublist saved).subset (RecursiveTransport.record_owner_member captured))
        · rw [selectedNames key body selected]; exact outerConsumed
      · exact captureConsumed key.owner ((RecursiveRecords.owners_sublist savedClosing).subset (RecursiveTransport.record_owner_member last))
  have stores : ∀ key : Key, afterPlan key.owner = .available →
      RecursiveRequirements.lookup key (resumes ++ disposals) = RecursiveRequirements.lookup key (waitingResumes ++ waitingDisposals) := by
    intro key ready
    exact (RecursiveTransport.lookup_permuted (RecursiveRecords.combined_unique source closing unique) permutation).trans
      (lookup_drop_consumed removedConsumed ready)
  have pendingWaiting : Checked (resumes ++ disposals) [] afterPlan waitingReq pendingRow := by
    apply RecursiveRequirements.evaluate_sound
    rw [waitingEvaluation (resumes ++ disposals) [] afterPlan outerConsumed]
    exact RecursiveRequirements.checked_complete pending
  have pendingCollected := RecursiveTransport.checked_transport pendingWaiting stores rfl
  have fixedSource := Segment.push (SourceTemplates.Frame.closing (identity := identity) scopeKnown) waiting
  have fixedCheck : Checked (waitingResumes ++ waitingDisposals) [] afterPlan
      (.sequence ((Requirements.request [] []).prepend (OwnerPhases.ofStack tables (front.append (.spent owner answerType caller tail)))) waitingReq) pendingRow := by
    have first : Checked (waitingResumes ++ waitingDisposals) [] afterPlan
        ((Requirements.request [] []).prepend (OwnerPhases.ofStack tables (front.append (.spent owner answerType caller tail)))) [] :=
      .request (by simp [OwnerSource.exportAt, residual_empty])
    simpa only [List.nil_append] using Checked.sequence first pendingCollected
  have planSource := RecursiveClosing.template_source (policy := policy) (RecursiveRecords.template_scope (second := scope) template) scopeKnown
  obtain ⟨combined, combinedSource, combinedCheck⟩ := RecursiveRecomposition.segment_append_checked planSource fixedSource
    (receiving := []) (by simpa only [List.append_nil] using planCheck) fixedCheck
  have nextClosing := RecursiveRecords.records_append (plan_records (operations := operations) (contracts := contracts) (tables := tables)
    (world := world) (scope := scope) plan) (Records.push (frame := .closing identity scope) waitingClosing)
  have afterUnique := (List.nodup_cons.mp ((OwnerClosingSource.discard_owned_permutation (scope := scope) (closeId := identity) built).nodup unique)).2
  have transition := OwnerClosingSource.discard_phase_trace (scope := scope) (closeId := identity) built unique
  have phases := OwnerPhaseTransitions.trace_result transition
  change available (ownedTickets restored) = spend initial owner at phases
  rw [← phases] at combinedCheck
  exact ⟨combined, waitingResumes, waitingDisposals, rfl,
    by simpa only [List.nil_append] using combinedSource,
    by simpa only [List.nil_append] using nextClosing, combinedCheck, afterUnique, transition⟩

theorem discard_cut_preserves
    (source : CheckedState operations policy contracts tables world outside scope (.discard binder)
      (front.append (.live owner inputType answerType capture caller tail)) output demand row)
    (resolved : scope.resolve binder = some owner) (built : makePlan capture = some plan) (identity : Nat) :
    ∃ remaining, CheckedState operations policy contracts tables world outside scope .unit
      ((closeControl scope plan).append (.push (.closing identity scope) (front.append (.spent owner answerType caller tail)))) output remaining row ∧
      demand = owner :: remaining ∧
      Trace (available (ownedTickets (front.append (.live owner inputType answerType capture caller tail)))) [owner]
        (available (ownedTickets ((closeControl scope plan).append (.push (.closing identity scope) (front.append (.spent owner answerType caller tail)))))) := by
  cases source with
  | checked source closing unique evaluated accepted => cases source with
      | checked current scopeTyped pendingSource => cases current with
          | stable summary => cases summary
          | callable summary => cases summary
          | discard known sourceResolved permission unprotected admitted =>
              rename_i actualOwner contract
              have sameOwner := Option.some.inj (sourceResolved.symm.trans resolved)
              subst actualOwner
              obtain ⟨closingRow, pendingRow, currentChecked, pendingChecked, rows⟩ := RecursiveRequirements.checked_sequence_parts evaluated
              have invocation := RecursiveRequirements.checked_prepend_iff.mp currentChecked
              simp only [List.append_nil] at invocation
              obtain ⟨combined, nextResumes, nextDisposals, sameDemand, combinedSource, nextClosing, combinedCheck, afterUnique, transition⟩ :=
                discard_segments pendingSource closing known unique invocation pendingChecked built
                  ⟨_, ScopedPorts.effect_scope_has_types scopeTyped⟩ identity
              let restored := (closeControl scope plan).append (.push (.closing identity scope) (front.append (.spent owner answerType caller tail)))
              have valueChecked : Checked (nextResumes ++ nextDisposals) [] (available (ownedTickets restored))
                  (.request (OwnerPhases.ofStack tables restored) []) [] := .request (by simp [OwnerSource.exportAt, residual_empty])
              have afterSource := SourceTemplates.Configuration.checked (currentDemand := [])
                (pendingDemand := OwnerClosingSource.retirements plan ++ _) (Expression.stable (allowed := []) .unit) scopeTyped combinedSource
              have acceptedAfter : checkFootprint outside (closingRow ++ pendingRow) = true := by simpa only [rows] using accepted
              have afterValid := CheckedState.checked afterSource nextClosing afterUnique
                (Checked.sequence valueChecked combinedCheck) acceptedAfter
              rw [← rows] at afterValid
              exact ⟨_, afterValid, by simp only [sameDemand, List.cons_append, List.nil_append], transition⟩

theorem discard_step_preserves
    (source : CheckedState operations policy contracts tables world outside scope (.discard binder) stack output demand row)
    (step : RawStep ⟨.discard binder, scope, stack⟩ next created completed) :
    ∃ owner identity remaining, next.expression = .unit ∧ next.scope = scope ∧
      CheckedState operations policy contracts tables world outside next.scope next.expression next.stack output remaining row ∧
      demand = owner :: remaining ∧ created = [.close identity] ∧ completed = [.ticket owner] ∧
      Trace (available (ownedTickets stack)) [owner] (available (ownedTickets next.stack)) := by
  cases step with
  | focus plain focus tail => cases focus
  | plug plain value impossible scope tail => cases impossible.1
  | leaveHandler handler value impossible scope tail => cases impossible.1
  | leaveCell identity payload answer savedScope scope value impossible tail => cases impossible.1
  | startCleanup action saved impossible scope tail => cases impossible.1
  | leaveClause ticket answer value impossible scope caller tail => cases impossible.1
  | discard binder owner identity scope caller inputType answerType front capture tail plan resolved built =>
      obtain ⟨remaining, checked, demand, transition⟩ := discard_cut_preserves source resolved built identity
      exact ⟨owner, identity, remaining, rfl, rfl, checked, demand, rfl, rfl, transition⟩

theorem discard_preserves
    (source : CheckedState operations policy contracts tables world outside scope (.discard binder) stack output demand row)
    (identity : Nat) :
    ∃ next owner remaining,
      RawStep ⟨.discard binder, scope, stack⟩ next [.close identity] [.ticket owner] ∧
      CheckedState operations policy contracts tables world outside next.scope next.expression next.stack output remaining row ∧
      demand = owner :: remaining ∧ Trace (available (ownedTickets stack)) [owner] (available (ownedTickets next.stack)) := by
  obtain ⟨next, owner, step⟩ := RecursiveRecords.discard_progress source identity
  obtain ⟨actualOwner, actualIdentity, remaining, unitSame, scopeSame, checked, demand, created, completed, transition⟩ :=
    discard_step_preserves source step
  have sameOwner : owner = actualOwner := Owner.ticket.inj (List.cons.inj completed).1
  have sameIdentity : identity = actualIdentity := Owner.close.inj (List.cons.inj created).1
  subst actualOwner
  subst actualIdentity
  exact ⟨next, owner, remaining, step, checked, demand, transition⟩

namespace Examples

open RecursiveRecords.Examples (operations policy tables inner)

def outer : Owners.Contract := { inner with resumeDemand := [19], closeDemand := [19] }
def contracts : Owners.Contracts := fun owner => if owner = 19 then some inner else if owner = 23 then some outer else none

theorem inner_known : contracts 19 = some inner := rfl
theorem outer_known : contracts 23 = some outer := rfl

def emptyRequirements : Requirements [] := .request [] []
def innerRequirements : Requirements [] := .sequence (.spent 19) emptyRequirements
def outerRequirements : Requirements [] := .sequence (.spent 23) emptyRequirements
def closingRequirements : Requirements [19] := .sequence (.retire 19) emptyRequirements
def binding : PlainData := ⟨.bind 99 (.discard 0), .ticket 0 19, .unit, .unit, [19], rfl⟩
def innerBoundary : Stack := .live 19 .unit .unit .nil .none .nil
def captured : Stack := .push (.plain binding) innerBoundary
def whole : Stack := .live 23 .unit .unit captured .none .nil
def capturedRequirements : Requirements [19] := .sequence
  ((Requirements.invoke ⟨19, .dispose⟩ [] []).prepend (OwnerPhases.ofStack tables innerBoundary)) innerRequirements
def innerResumes : Store := [(⟨19, .resume⟩, ⟨[], emptyRequirements⟩)]
def innerDisposals : Store := [(⟨19, .dispose⟩, ⟨[], emptyRequirements⟩)]
def resumes : Store := (⟨23, .resume⟩, ⟨[19], capturedRequirements⟩) :: innerResumes
def disposals : Store := (⟨23, .dispose⟩, ⟨[19], closingRequirements⟩) :: innerDisposals

theorem inner_source : Segment operations policy contracts tables [] innerBoundary .unit .unit [] innerRequirements innerResumes :=
  .live inner_known rfl rfl ⟨.none, .none⟩ rfl .nil .nil

theorem captured_source : Segment operations policy contracts tables [] captured .unit .unit [19] capturedRequirements innerResumes := by
  have body : Expression operations policy contracts [] [] binding.scope (Environment.empty.extend 99 .unit)
      (.discard 0) .unit [19] (.invoke ⟨19, .dispose⟩ [] []) :=
    .discard inner_known rfl rfl rfl (by simp [inner])
  exact .push (.plain (.bind body) (.bound (Owners.ports_lookup inner_known)) rfl rfl) inner_source

theorem whole_source : Segment operations policy contracts tables [] whole .unit .unit [] outerRequirements resumes :=
  .live outer_known rfl rfl ⟨.none, .none⟩ rfl captured_source .nil

theorem whole_closing : Records operations policy contracts tables [] whole disposals :=
  .close rfl (ClosingAdmission.check_internal_uses_iff.mp (by decide)) (.retire inner_known .nil)
    (.push (.close rfl .nil .nil .nil .nil)) .nil

theorem captured_checked : Checked (resumes ++ disposals) (OwnerPhases.ofStack tables whole)
    (spend (available [23, 19]) 23) capturedRequirements [] := by
  have nested : Checked (resumes ++ disposals) (OwnerPhases.ofStack tables whole) (spend (available [23, 19]) 23)
      ((Requirements.invoke ⟨19, .dispose⟩ [] []).prepend (OwnerPhases.ofStack tables innerBoundary)) [] := by
    apply Checked.invoke (body := emptyRequirements) rfl (by decide) (by exact OwnerPhases.Consumes.hit)
    exact .request (by simp [OwnerSource.exportAt, residual_empty])
  have remaining : Checked (resumes ++ disposals) (OwnerPhases.ofStack tables whole)
      (spendAll (spend (available [23, 19]) 23) [19]) innerRequirements [] :=
    .sequence (.spent (by decide)) (.request (by simp [OwnerSource.exportAt, residual_empty]))
  exact Checked.sequence nested remaining

theorem outer_resume_checked : Checked (resumes ++ disposals) (OwnerPhases.ofStack tables whole)
    (available [23, 19]) (.invoke ⟨23, .resume⟩ [19] []) [] :=
  .invoke rfl (by decide) (by exact OwnerPhases.Consumes.hit) captured_checked

theorem mixed_source_checked : CheckedState operations policy contracts tables [] [] (.ticket 1 23)
    (.resume 1 .unit) whole .unit [23, 19] [] := by
  have current : Expression operations policy contracts [] [] (.ticket 1 23) Environment.empty
      (.resume 1 .unit) .unit [23, 19] (.sequence emptyRequirements (.invoke ⟨23, .resume⟩ [19] [])) :=
    .resume outer_known rfl rfl (.stable .unit) (by simp [outer, inner]) (by simp [outer, inner, ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])
  have empty : Checked (resumes ++ disposals) (OwnerPhases.ofStack tables whole) (available [23, 19]) emptyRequirements [] :=
    .request (by simp [OwnerSource.exportAt, residual_empty])
  have sequence := Checked.sequence empty outer_resume_checked
  have currentCheck : Checked (resumes ++ disposals) [] (available (ownedTickets whole))
      ((Requirements.sequence emptyRequirements (.invoke ⟨23, .resume⟩ [19] [])).prepend (OwnerPhases.ofStack tables whole)) [] :=
    RecursiveRequirements.checked_prepend_iff.mpr (by
      simpa only [List.append_nil, whole, captured, innerBoundary, ownedTickets] using sequence)
  have pending : Checked (resumes ++ disposals) [] (spendAll (available (ownedTickets whole)) [23, 19]) outerRequirements [] :=
    .sequence (.spent (by decide)) (.request (by simp [OwnerSource.exportAt, residual_empty]))
  exact .checked (.checked (currentDemand := [23, 19]) (pendingDemand := []) current
    (.bound (Owners.ports_lookup outer_known)) whole_source) whole_closing (by decide)
    (Checked.sequence currentCheck pending) (by decide)

theorem mixed_resume_preserved : CheckedState operations policy contracts tables [] [] (.ticket 1 23) .unit
    (captured.append (.spent 23 .unit .none .nil)) .unit [19] [] := by
  obtain ⟨remaining, checked, same, transition⟩ := resume_cut_preserves (front := .nil) mixed_source_checked rfl
    CallableProtection.Examples.unit_closed
  have remainder : remaining = [19] := (List.cons.inj same).2.symm
  exact remainder ▸ checked

theorem mixed_actual_resume :
    RawStep ⟨.resume 1 .unit, .ticket 1 23, whole⟩ ⟨.unit, .ticket 1 23, captured.append (.spent 23 .unit .none .nil)⟩ [] [.ticket 23] ∧
    CheckedState operations policy contracts tables [] [] (.ticket 1 23) .unit
      (captured.append (.spent 23 .unit .none .nil)) .unit [19] [] :=
  ⟨.resume 1 23 (.ticket 1 23) .none .unit .unit .nil captured .nil .unit CallableProtection.Examples.unit_closed rfl,
    mixed_resume_preserved⟩

end Examples

namespace DisposalExamples
open RecursiveRecords.Examples (operations policy contracts tables stack)

def restored : Stack := (closeControl (.ticket 0 23) [.retire 19]).append
  (.push (.closing 41 (.ticket 0 23)) (.spent 23 .unit .none .nil))

theorem disposal_preserved : CheckedState operations policy contracts tables [] [] (.ticket 0 23) .unit restored .unit [19] [] := by
  obtain ⟨remaining, checked, same, transition⟩ := discard_cut_preserves (front := .nil)
    RecursiveRecords.Examples.admitted_discard rfl (by rfl) 41
  have remainder : remaining = [19] := (List.cons.inj same).2.symm
  exact remainder ▸ checked

theorem actual_disposal :
    RawStep ⟨.discard 0, .ticket 0 23, stack⟩ ⟨.unit, .ticket 0 23, restored⟩ [.close 41] [.ticket 23] ∧
    CheckedState operations policy contracts tables [] [] (.ticket 0 23) .unit restored .unit [19] [] :=
  ⟨.discard 0 23 41 (.ticket 0 23) .none .unit .unit .nil RecursiveRecords.Examples.capture .nil [.retire 19] rfl rfl,
    disposal_preserved⟩

end DisposalExamples

end Ash.OneShot.RecursiveConsumption

#print axioms Ash.OneShot.RecursiveConsumption.remove_owner_append
#print axioms Ash.OneShot.RecursiveConsumption.resume_segments
#print axioms Ash.OneShot.RecursiveConsumption.resume_cut_preserves
#print axioms Ash.OneShot.RecursiveConsumption.resume_step_preserves
#print axioms Ash.OneShot.RecursiveConsumption.resume_progress
#print axioms Ash.OneShot.RecursiveConsumption.resume_preserves
#print axioms Ash.OneShot.RecursiveConsumption.template_store
#print axioms Ash.OneShot.RecursiveConsumption.guarded_export
#print axioms Ash.OneShot.RecursiveConsumption.template_guard
#print axioms Ash.OneShot.RecursiveConsumption.plan_records
#print axioms Ash.OneShot.RecursiveConsumption.discard_store_permutation
#print axioms Ash.OneShot.RecursiveConsumption.lookup_drop_consumed
#print axioms Ash.OneShot.RecursiveConsumption.certified_plan_at
#print axioms Ash.OneShot.RecursiveConsumption.discard_segments
#print axioms Ash.OneShot.RecursiveConsumption.discard_cut_preserves
#print axioms Ash.OneShot.RecursiveConsumption.discard_step_preserves
#print axioms Ash.OneShot.RecursiveConsumption.discard_preserves
#print axioms Ash.OneShot.RecursiveConsumption.Examples.inner_known
#print axioms Ash.OneShot.RecursiveConsumption.Examples.outer_known
#print axioms Ash.OneShot.RecursiveConsumption.Examples.inner_source
#print axioms Ash.OneShot.RecursiveConsumption.Examples.captured_source
#print axioms Ash.OneShot.RecursiveConsumption.Examples.whole_source
#print axioms Ash.OneShot.RecursiveConsumption.Examples.whole_closing
#print axioms Ash.OneShot.RecursiveConsumption.Examples.captured_checked
#print axioms Ash.OneShot.RecursiveConsumption.Examples.outer_resume_checked
#print axioms Ash.OneShot.RecursiveConsumption.Examples.mixed_source_checked
#print axioms Ash.OneShot.RecursiveConsumption.Examples.mixed_resume_preserved
#print axioms Ash.OneShot.RecursiveConsumption.Examples.mixed_actual_resume
#print axioms Ash.OneShot.RecursiveConsumption.DisposalExamples.disposal_preserved
#print axioms Ash.OneShot.RecursiveConsumption.DisposalExamples.actual_disposal
