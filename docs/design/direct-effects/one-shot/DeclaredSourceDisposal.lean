import DeclaredSourceClosing
import DeclaredSourceStates
import AnnotatedRecomposition

/-! Disposal recomposition retains exact hereditary closing-template evidence.
The existing authenticated lookup, consumed-record transport, plan guarding
and one-shot ownership permutation proofs supply the checking argument. -/
namespace Ash.OneShot.DeclaredSourceDisposal
open ScopedExpressions ScopedExecution CoherentSourceTypes ProtectionContracts ProtectionResiduals
open DeclaredSourceFrames (Segment)
open DeclaredSources (Expression)
open DeclaredSourceStates (CheckedState)
open DeclaredSourceClosing (Records certified_plan_at plan_records)
open RecursiveRequirements (Requirements Store Key Checked evaluate)
open OwnerPhaseTransitions (Phases Trace available spend spendAll)
open RecursiveConsumption (template_guard template_store discard_store_permutation lookup_drop_consumed)
variable {front capture tail : Stack}

/-- The current invocation selects an actual hereditary closing template and
checks it in the surviving caller. This is evidence already used by disposal
recomposition, exposed before any next stack is assembled. -/
theorem checked_disposal_plan
    (source : Segment operations policy contracts tables world
      (front.append (.live owner inputType answerType capture caller tail)) input output pendingDemand pendingRequirements resumes)
    (closing : Records operations policy contracts tables world
      (front.append (.live owner inputType answerType capture caller tail)) disposals)
    (unique : (ownedTickets (front.append (.live owner inputType answerType capture caller tail))).Nodup)
    (invocation : Checked (resumes ++ disposals)
      (OwnerPhases.ofStack tables (front.append (.live owner inputType answerType capture caller tail)))
      (available (ownedTickets (front.append (.live owner inputType answerType capture caller tail))))
      (.invoke ⟨owner, .dispose⟩ closingDemand []) closingRow) :
    ∃ (plan : List CloseEntry) (raw : Footprint) (requirements : Requirements (OwnerClosingSource.retirements plan)),
      makePlan capture = some plan ∧
      DeclaredSourceClosing.PlanTemplate operations policy contracts tables world .none plan raw requirements ∧
      closingDemand = OwnerClosingSource.retirements plan ∧
      Checked (resumes ++ disposals)
        (OwnerPhases.ofStack tables (front.append (.spent owner answerType caller tail)))
        (spend (available (ownedTickets (front.append (.live owner inputType answerType capture caller tail)))) owner)
        requirements closingRow := by
  obtain ⟨body, selectedContext, looked, ready, selection, bodyChecked⟩ :=
    RecursiveRequirements.checked_invocation invocation
  obtain ⟨plan, raw, requirements, built, sameTemplate, template⟩ := certified_plan_at
    (DeclaredSourceClosing.lookup_certified source closing looked) unique (RecursiveRecords.located_below front .here)
  have sameDemand := congrArg Sigma.fst sameTemplate
  change closingDemand = OwnerClosingSource.retirements plan at sameDemand
  have sameBody := (Sigma.mk.inj sameTemplate).2
  subst closingDemand
  cases eq_of_heq sameBody
  have contexts : RecursiveTransport.normalize
      (spend (available (ownedTickets (front.append (.live owner inputType answerType capture caller tail)))) owner)
      (OwnerPhases.ofStack tables (front.append (.live owner inputType answerType capture caller tail))) =
    RecursiveTransport.normalize
      (spend (available (ownedTickets (front.append (.live owner inputType answerType capture caller tail)))) owner)
      (OwnerPhases.ofStack tables (front.append (.spent owner answerType caller tail))) := by
    simpa only [List.append_nil] using
      (RecursiveRecomposition.normalize_replaced (front := front) (capture := capture) (tail := tail)
        (input := inputType) (answer := answerType) (caller := caller) (tables := tables) (receiving := [])
        (OwnerPhaseTransitions.spend_self _ owner))
  exact ⟨plan, raw, requirements, built, template, rfl,
    RecursiveTransport.checked_transport bodyChecked (fun _ _ => rfl) contexts⟩

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
    AnnotatedRecomposition.replace_live source known
  obtain ⟨selectedDisposals, capturedDisposals, waitingDisposals, savedClosing, waitingClosing, disposalPermutation, selectedNames⟩ :=
    DeclaredSourceClosing.split_live closing
  obtain ⟨actualPlan, raw, planReq, actualBuilt, template, sameDemand, planWaiting⟩ :=
    checked_disposal_plan source closing unique invocation
  have samePlan := Option.some.inj (actualBuilt.symm.trans built)
  subst actualPlan
  subst closingDemand
  let initial := available (ownedTickets (front.append (.live owner inputType answerType capture caller tail)))
  let fixed := Stack.push (.closing identity scope) (front.append (.spent owner answerType caller tail))
  let restored := (closeControl scope plan).append fixed
  let afterPlan := spendAll initial (owner :: OwnerClosingSource.retirements plan)
  have planCheck : Checked (waitingResumes ++ waitingDisposals) (OwnerPhases.ofStack tables fixed)
      (spend initial owner) planReq closingRow := by
    apply RecursiveRequirements.evaluate_sound
    rw [template_guard (DeclaredSourceClosing.template_erase template), ← template_store (first := resumes ++ disposals) (DeclaredSourceClosing.template_erase template)]
    exact RecursiveRequirements.checked_complete planWaiting
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
        · exact captureConsumed key.owner ((RecursiveTransport.record_owners_sublist saved.erase).subset (RecursiveTransport.record_owner_member captured))
        · rw [selectedNames key body selected]; exact outerConsumed
      · exact captureConsumed key.owner ((DeclaredSourceClosing.owners_sublist savedClosing).subset (RecursiveTransport.record_owner_member last))
  have stores : ∀ key : Key, afterPlan key.owner = .available →
      RecursiveRequirements.lookup key (resumes ++ disposals) = RecursiveRequirements.lookup key (waitingResumes ++ waitingDisposals) := by
    intro key ready
    exact (RecursiveTransport.lookup_permuted (RecursiveRecords.combined_unique source.erase (DeclaredSourceClosing.records_erase closing) unique) permutation).trans
      (lookup_drop_consumed removedConsumed ready)
  have pendingWaiting : Checked (resumes ++ disposals) [] afterPlan waitingReq pendingRow := by
    apply RecursiveRequirements.evaluate_sound
    rw [waitingEvaluation (resumes ++ disposals) [] afterPlan outerConsumed]
    exact RecursiveRequirements.checked_complete pending
  have pendingCollected := RecursiveTransport.checked_transport pendingWaiting stores rfl
  have fixedSource := DeclaredSourceFrames.push (DeclaredSourceFrames.Frame.closing (identity := identity) scopeKnown) waiting
  have fixedCheck : Checked (waitingResumes ++ waitingDisposals) [] afterPlan
      (.sequence ((Requirements.request [] []).prepend (OwnerPhases.ofStack tables (front.append (.spent owner answerType caller tail)))) waitingReq) pendingRow := by
    have first : Checked (waitingResumes ++ waitingDisposals) [] afterPlan
        ((Requirements.request [] []).prepend (OwnerPhases.ofStack tables (front.append (.spent owner answerType caller tail)))) [] :=
      .request (by simp [OwnerSource.exportAt, residual_empty])
    simpa only [List.nil_append] using Checked.sequence first pendingCollected
  have planSource := DeclaredSourceClosing.template_source (policy := policy) (DeclaredSourceClosing.template_scope (second := scope) template) scopeKnown
  obtain ⟨combined, combinedSource, combinedCheck⟩ := AnnotatedRecomposition.segment_append_checked planSource fixedSource
    (receiving := []) (by simpa only [List.append_nil] using planCheck) fixedCheck
  have nextClosing := DeclaredSourceClosing.records_append (plan_records (operations := operations) (contracts := contracts) (tables := tables)
    (world := world) (scope := scope) plan) (Records.push (frame := .closing identity scope) waitingClosing)
  have afterUnique := (List.nodup_cons.mp ((OwnerClosingSource.discard_owned_permutation (scope := scope) (closeId := identity) built).nodup unique)).2
  have transition := OwnerClosingSource.discard_phase_trace (scope := scope) (closeId := identity) built unique
  have phases := OwnerPhaseTransitions.trace_result transition
  change available (ownedTickets restored) = spend initial owner at phases
  rw [← phases] at combinedCheck
  exact ⟨combined, waitingResumes, waitingDisposals, rfl,
    by simpa only [List.nil_append] using combinedSource,
    by simpa only [List.nil_append] using nextClosing, combinedCheck, afterUnique, transition⟩


/-- A checked current discard supplies the selected plan, its exact source
template and its admitted residual. No plan or successful closing check is
assumed separately. -/
theorem current_disposal_plan
    (source : CheckedState operations policy contracts tables world outside scope (.discard binder)
      (front.append (.live owner inputType answerType capture caller tail)) output demand row)
    (resolved : scope.resolve binder = some owner) :
    ∃ (plan : List CloseEntry) (raw : Footprint)
      (requirements : Requirements (OwnerClosingSource.retirements plan)) (store : Store) (closingRow : Footprint),
      makePlan capture = some plan ∧
      DeclaredSourceClosing.PlanTemplate operations policy contracts tables world .none plan raw requirements ∧
      Checked store (OwnerPhases.ofStack tables (front.append (.spent owner answerType caller tail)))
        (spend (available (ownedTickets (front.append (.live owner inputType answerType capture caller tail)))) owner)
        requirements closingRow ∧
      closingRow ⊆ row ∧ checkFootprint outside closingRow = true := by
  cases source with
  | checked source closing unique evaluated accepted => cases source with
      | checked current scopeTyped pendingSource => cases current with
          | stable summary => cases summary
          | callable summary => cases summary
          | discard known sourceResolved permission unprotected admitted =>
              rename_i contract actualOwner
              have sameOwner := Option.some.inj (sourceResolved.symm.trans resolved)
              subst actualOwner
              obtain ⟨closingRow, pendingRow, currentChecked, pendingChecked, rows⟩ :=
                RecursiveRequirements.checked_sequence_parts evaluated
              have invocation := RecursiveRequirements.checked_prepend_iff.mp currentChecked
              simp only [List.append_nil] at invocation
              obtain ⟨plan, raw, requirements, built, template, sameDemand, checked⟩ :=
                checked_disposal_plan pendingSource closing unique invocation
              rw [rows, check_footprint_append, Bool.and_eq_true] at accepted
              refine ⟨plan, raw, requirements, _, closingRow, built, template, checked, ?_, accepted.1⟩
              rw [rows]
              exact List.subset_append_left _ _

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
              rename_i contract actualOwner
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
              have afterSource := DeclaredSourceStates.Configuration.checked (currentDemand := [])
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
  obtain ⟨next, owner, step⟩ := RecursiveRecords.discard_progress (DeclaredSourceStates.checked_state_erase source) identity
  obtain ⟨actualOwner, actualIdentity, remaining, unitSame, scopeSame, checked, demand, created, completed, transition⟩ :=
    discard_step_preserves source step
  have sameOwner : owner = actualOwner := Owner.ticket.inj (List.cons.inj completed).1
  have sameIdentity : identity = actualIdentity := Owner.close.inj (List.cons.inj created).1
  subst actualOwner
  subst actualIdentity
  exact ⟨next, owner, remaining, step, checked, demand, transition⟩


end Ash.OneShot.DeclaredSourceDisposal

#print axioms Ash.OneShot.DeclaredSourceDisposal.discard_segments
#print axioms Ash.OneShot.DeclaredSourceDisposal.discard_cut_preserves
#print axioms Ash.OneShot.DeclaredSourceDisposal.discard_step_preserves
#print axioms Ash.OneShot.DeclaredSourceDisposal.discard_preserves

#print axioms Ash.OneShot.DeclaredSourceDisposal.checked_disposal_plan
#print axioms Ash.OneShot.DeclaredSourceDisposal.current_disposal_plan
