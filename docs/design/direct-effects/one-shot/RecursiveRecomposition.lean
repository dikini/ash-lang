import RecursiveTransport

/-!
Recomposition of source-derived segments and their recursive checks. Segment
append retains the exact collected store and interpretation order. Resumption
uses the physical waiting caller and the actual successor ownership map.
-/

namespace Ash.OneShot.RecursiveRecomposition
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open CoherentSourceTypes
open SourceTemplates (Segment Frame Expression)
open RecursiveRequirements (Requirements Store Key Checked evaluate)
open OwnerPhaseTransitions (Phases spend spendAll)

variable {before phases : Phases} {front capture tail : Stack}

theorem evaluate_empty : evaluate store receiving before (.request nearer []) = some [] := by
  simp only [evaluate, RecursiveRequirements.evaluateFuel, OwnerSource.exportAt, residual_empty]

theorem evaluate_spent : evaluate store receiving before (.spent owner) =
    if before owner = .consumed then some [] else none := by
  simp only [evaluate, RecursiveRequirements.evaluateFuel]

theorem merge_empty_left (row : Option Footprint) : merge (some []) row = row := by cases row <;> rfl

theorem merge_empty_right (row : Option Footprint) : merge row (some []) = row := by cases row <;> simp [merge]

theorem segment_append
    (first : Segment operations policy contracts tables world front input middle firstDemand firstRequirements firstRecords)
    (second : Segment operations policy contracts tables world tail middle output secondDemand secondRequirements secondRecords) :
    ∃ combined : Requirements (firstDemand ++ secondDemand),
      Segment operations policy contracts tables world (front.append tail) input output
        (firstDemand ++ secondDemand) combined (firstRecords ++ secondRecords) ∧
      ∀ store receiving phases,
        evaluate store receiving phases combined =
          merge (evaluate store (OwnerPhases.ofStack tables tail ++ receiving) phases firstRequirements)
            (evaluate store receiving (spendAll phases firstDemand) secondRequirements) := by
  induction first generalizing output secondDemand secondRequirements secondRecords tail with
  | nil =>
      refine ⟨secondRequirements, second, ?_⟩
      intro store receiving phases
      simp only [evaluate_empty, spendAll, merge_empty_left]
  | push head rest ih =>
      obtain ⟨combined, source, evaluation⟩ := ih second
      rw [List.append_assoc]
      refine ⟨_, .push head source, ?_⟩
      intro store receiving phases
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
        OwnerPhases.stack_append, List.append_assoc, evaluation, PhaseRechecking.spendAll_append, merge_assoc]
  | @live owner contract inputType answerType caller capture body nested rest middle demand requirements remaining
      known inputAnnotation answerAnnotation scopeKnown held saved restSource ihSaved ihRest =>
      obtain ⟨combined, source, evaluation⟩ := ihRest second
      refine ⟨@Requirements.sequence [] (demand ++ secondDemand) (.spent owner) combined, ?_, ?_⟩
      · simpa only [List.cons_append, List.append_assoc, Stack.append] using Segment.live known inputAnnotation answerAnnotation scopeKnown held saved source
      · intro store receiving phases
        simp only [RecursiveRequirements.evaluate_sequence, evaluate_spent, evaluation, spendAll, merge_assoc]
  | spent known answerAnnotation scopeKnown rest ih =>
      obtain ⟨combined, source, evaluation⟩ := ih second
      refine ⟨_, .spent known answerAnnotation scopeKnown source, ?_⟩
      intro store receiving phases
      simp only [RecursiveRequirements.evaluate_sequence, evaluate_spent, evaluation, spendAll, merge_assoc]

theorem segment_append_checked
    (first : Segment operations policy contracts tables world front input middle firstDemand firstRequirements firstRecords)
    (second : Segment operations policy contracts tables world tail middle output secondDemand secondRequirements secondRecords)
    (firstChecked : Checked store (OwnerPhases.ofStack tables tail ++ receiving) before firstRequirements firstRow)
    (secondChecked : Checked store receiving (spendAll before firstDemand) secondRequirements secondRow) :
    ∃ combined : Requirements (firstDemand ++ secondDemand),
      Segment operations policy contracts tables world (front.append tail) input output
        (firstDemand ++ secondDemand) combined (firstRecords ++ secondRecords) ∧
      Checked store receiving before combined (firstRow ++ secondRow) := by
  obtain ⟨combined, source, evaluation⟩ := segment_append first second
  refine ⟨combined, source, RecursiveRequirements.evaluate_sound ?_⟩
  rw [evaluation, RecursiveRequirements.checked_complete firstChecked, RecursiveRequirements.checked_complete secondChecked]
  rfl

theorem move_records {prefixRecords old captured remaining : Store} {entry : Key × RecursiveRequirements.Template}
    (permutation : old.Perm (entry :: (captured ++ remaining))) :
    (prefixRecords ++ old).Perm (entry :: (captured ++ (prefixRecords ++ remaining))) := by
  have moved := (List.perm_append_comm (l₁ := prefixRecords) (l₂ := entry :: captured)).append_right remaining
  have joined := permutation.append_left prefixRecords
  exact joined.trans (by simpa only [List.append_assoc, List.cons_append] using moved)

theorem normalize_replaced (consumed : phases owner = .consumed) :
    RecursiveTransport.normalize phases (OwnerPhases.ofStack tables (front.append (.live owner input answer capture caller tail)) ++ receiving) =
      RecursiveTransport.normalize phases (OwnerPhases.ofStack tables (front.append (.spent owner answer caller tail)) ++ receiving) := by
  simp only [OwnerPhases.stack_append, OwnerPhases.ofStack, List.append_assoc, List.cons_append,
    RecursiveTransport.normalize_append, RecursiveTransport.normalize, consumed, if_true]

theorem replace_live
    (source : Segment operations policy contracts tables world
      (front.append (.live owner inputType answerType capture caller tail)) input output demand requirements records)
    (known : contracts owner = some contract) :
    ∃ (capturedRequirements : Requirements contract.resumeDemand) (capturedRecords : Store)
      (waitingRequirements : Requirements demand) (waitingRecords : Store),
      Segment operations policy contracts tables world capture contract.input contract.answer
        contract.resumeDemand capturedRequirements capturedRecords ∧
      Segment operations policy contracts tables world (front.append (.spent owner answerType caller tail)) input output
        demand waitingRequirements waitingRecords ∧
      records.Perm ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (capturedRecords ++ waitingRecords)) ∧
      ∀ store receiving phases, phases owner = .consumed →
        evaluate store receiving phases waitingRequirements = evaluate store receiving phases requirements := by
  induction front generalizing input demand requirements records with
  | nil => cases source with
      | live actual inputAnnotation answerAnnotation scopeKnown held saved rest =>
          have same := Option.some.inj (actual.symm.trans known)
          cases same
          refine ⟨_, _, _, _, saved, .spent known answerAnnotation scopeKnown rest, .refl _, ?_⟩
          intros; rfl
  | push frame front ih => cases source with
      | push head rest =>
          rename_i middle headDemand headReq tailDemand tailReq
          obtain ⟨capturedReq, capturedRecords, waitingReq, waitingRecords, saved, waiting, permutation, evaluation⟩ := ih rest
          refine ⟨capturedReq, capturedRecords, _, waitingRecords, saved, .push head waiting, permutation, ?_⟩
          intro store receiving phases consumed
          rw [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_sequence,
            RecursiveRequirements.evaluate_prepend, RecursiveRequirements.evaluate_prepend]
          have headSame := RecursiveTransport.evaluate_transport (requirements := headReq) (store := store) (nextStore := store)
            (fun _ _ => rfl) (normalize_replaced (front := front) (capture := capture) (tail := tail)
              (input := inputType) (answer := answerType) (caller := caller) (tables := tables) (receiving := receiving) consumed)
          rw [← headSame, evaluation store receiving _ (RecursiveTransport.phases_spendAll_later owner consumed)]
  | live other otherInput otherAnswer savedFront savedScope front ihSaved ihFront => cases source with
      | @live other otherContract otherInput otherAnswer savedScope savedFront body nested restStack output demand requirements remaining
          actual inputAnnotation answerAnnotation scopeKnown held savedOther rest =>
          obtain ⟨capturedReq, capturedRecords, waitingReq, waitingRecords, saved, waiting, permutation, evaluation⟩ := ihFront rest
          have rebuilt := Segment.live actual inputAnnotation answerAnnotation scopeKnown held savedOther waiting
          refine ⟨capturedReq, capturedRecords, _, _, saved, rebuilt, ?_, ?_⟩
          · simpa only [List.cons_append, List.append_assoc] using
              move_records (prefixRecords := (⟨other, .resume⟩, ⟨otherContract.resumeDemand, body⟩) :: nested) permutation
          · intro store receiving phases consumed
            simp only [RecursiveRequirements.evaluate_sequence, spendAll, evaluation store receiving phases consumed, evaluate_spent]
  | spent other answer savedScope front ih => cases source with
      | spent actual answerAnnotation scopeKnown rest =>
          obtain ⟨capturedReq, capturedRecords, waitingReq, waitingRecords, saved, waiting, permutation, evaluation⟩ := ih rest
          refine ⟨capturedReq, capturedRecords, _, waitingRecords, saved, .spent actual answerAnnotation scopeKnown waiting, permutation, ?_⟩
          intro store receiving phases consumed
          simp only [RecursiveRequirements.evaluate_sequence, spendAll, evaluation store receiving phases consumed, evaluate_spent]

theorem remove_owner_filter : RecursiveTransport.removeOwner owner records =
    records.filter (fun entry => entry.1.owner != owner) := by
  induction records with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨key, body⟩ := entry
      by_cases same : key.owner = owner <;> simp [RecursiveTransport.removeOwner, same, ih]

theorem remove_owner_permutation (permutation : first.Perm second) :
    (RecursiveTransport.removeOwner owner first).Perm (RecursiveTransport.removeOwner owner second) := by
  rw [remove_owner_filter, remove_owner_filter]
  exact permutation.filter _

theorem remove_owner_absent (absent : owner ∉ RecursiveTransport.recordOwners records) :
    RecursiveTransport.removeOwner owner records = records := by
  induction records with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨key, body⟩ := entry
      have different : key.owner ≠ owner := by intro same; exact absent (by simp [RecursiveTransport.recordOwners, same])
      have restAbsent : owner ∉ RecursiveTransport.recordOwners rest := fun member => absent (List.mem_cons_of_mem _ member)
      simp only [RecursiveTransport.removeOwner, different, if_false, ih restAbsent]

theorem removed_records (unique : (RecursiveTransport.recordOwners records).Nodup)
    (permutation : records.Perm ((⟨owner, .resume⟩, template) :: remaining)) :
    (RecursiveTransport.removeOwner owner records).Perm remaining := by
  have reorderedUnique := (permutation.map (fun (entry : Key × RecursiveRequirements.Template) => entry.1.owner)).nodup unique
  have absent := (List.nodup_cons.mp reorderedUnique).1
  have same := remove_owner_absent absent
  have erased := remove_owner_permutation (owner := owner) permutation
  simpa [RecursiveTransport.removeOwner, same] using erased

theorem resume_segments
    (source : Segment operations policy contracts tables world
      (front.append (.live owner inputType answerType capture caller tail)) contract.answer output pendingDemand pendingRequirements records)
    (known : contracts owner = some contract)
    (unique : (ownedTickets (front.append (.live owner inputType answerType capture caller tail))).Nodup)
    (invocation : Checked records (OwnerPhases.ofStack tables (front.append (.live owner inputType answerType capture caller tail)))
      (OwnerPhaseTransitions.available (ownedTickets (front.append (.live owner inputType answerType capture caller tail))))
      (.invoke ⟨owner, .resume⟩ contract.resumeDemand []) resumeRow)
    (pending : Checked records []
      (spendAll (OwnerPhaseTransitions.available (ownedTickets (front.append (.live owner inputType answerType capture caller tail))))
        (owner :: contract.resumeDemand)) pendingRequirements pendingRow) :
    ∃ (combined : Requirements (contract.resumeDemand ++ pendingDemand)) (collected : Store),
      Segment operations policy contracts tables world (capture.append (front.append (.spent owner answerType caller tail)))
        contract.input output (contract.resumeDemand ++ pendingDemand) combined collected ∧
      Checked collected []
        (OwnerPhaseTransitions.available (ownedTickets (capture.append (front.append (.spent owner answerType caller tail)))))
        combined (resumeRow ++ pendingRow) ∧
      (RecursiveTransport.removeOwner owner records).Perm collected ∧
      (ownedTickets (capture.append (front.append (.spent owner answerType caller tail)))).Nodup ∧
      OwnerPhaseTransitions.Trace
        (OwnerPhaseTransitions.available (ownedTickets (front.append (.live owner inputType answerType capture caller tail)))) [owner]
        (OwnerPhaseTransitions.available (ownedTickets (capture.append (front.append (.spent owner answerType caller tail))))) := by
  obtain ⟨capturedReq, capturedRecords, waitingReq, waitingRecords, saved, waiting, permutation, waitingEvaluation⟩ :=
    replace_live source known
  have keysUnique := RecursiveTransport.source_records_unique source unique
  have ownersUnique := (RecursiveTransport.record_owners_sublist source).nodup unique
  have erasedPermutation := removed_records ownersUnique permutation
  have erasedUnique := RecursiveTransport.remove_owner_unique (owner := owner) keysUnique
  have capturedKnown := RecursiveTransport.lookup_of_member keysUnique (permutation.mem_iff.mpr List.mem_cons_self)
  obtain ⟨body, selectedContext, actual, ready, selection, bodyChecked⟩ := RecursiveRequirements.checked_invocation invocation
  have sameTemplate := Option.some.inj (actual.symm.trans capturedKnown)
  have sameBody := eq_of_heq (Sigma.mk.inj sameTemplate).2
  subst body
  let initial := OwnerPhaseTransitions.available (ownedTickets (front.append (.live owner inputType answerType capture caller tail)))
  have consumed : spend initial owner owner = .consumed := OwnerPhaseTransitions.spend_self initial owner
  have contexts : RecursiveTransport.normalize (spend initial owner)
      (OwnerPhases.ofStack tables (front.append (.live owner inputType answerType capture caller tail))) =
      RecursiveTransport.normalize (spend initial owner)
        (OwnerPhases.ofStack tables (front.append (.spent owner answerType caller tail))) := by
    simpa only [List.append_nil] using (normalize_replaced (front := front) (capture := capture) (tail := tail)
      (input := inputType) (answer := answerType) (caller := caller) (tables := tables) (receiving := []) consumed)
  have bodyWaiting := RecursiveTransport.checked_transport bodyChecked
    (RecursiveTransport.remove_consumed_agrees consumed) contexts
  have bodyCollected := RecursiveTransport.checked_permuted bodyWaiting erasedUnique erasedPermutation
  have consumedAfter : spendAll initial (owner :: contract.resumeDemand) owner = .consumed := by
    rw [OwnerPhaseTransitions.spendAll_at, if_pos List.mem_cons_self]
  have pendingWaiting : Checked records [] (spendAll initial (owner :: contract.resumeDemand)) waitingReq pendingRow := by
    apply RecursiveRequirements.evaluate_sound
    rw [waitingEvaluation records [] _ consumedAfter]
    exact RecursiveRequirements.checked_complete pending
  have pendingErased := RecursiveTransport.checked_remove_consumed pendingWaiting consumedAfter
  have pendingCollected := RecursiveTransport.checked_permuted pendingErased erasedUnique erasedPermutation
  obtain ⟨combined, combinedSource, combinedCheck⟩ := segment_append_checked saved waiting
    (receiving := []) (by simpa only [List.append_nil] using bodyCollected) pendingCollected
  have trace := OwnerPhaseTransitions.resume_phase_trace unique
  have actualPhases := OwnerPhaseTransitions.trace_result trace
  change OwnerPhaseTransitions.available (ownedTickets (capture.append (front.append (.spent owner answerType caller tail)))) =
    spend initial owner at actualPhases
  rw [← actualPhases] at combinedCheck
  have afterUnique := (List.nodup_cons.mp (OwnerPhaseTransitions.resume_owned_permutation.nodup unique)).2
  exact ⟨combined, _, combinedSource, combinedCheck, erasedPermutation, afterUnique, trace⟩

theorem value_summary
    (source : Expression operations policy contracts world allowed scope environment code result demand requirements)
    (isValue : code.IsValue) : SourceTemplates.ValueSummary operations policy contracts world environment allowed code result :=
  SourceTemplates.value_summary source isValue

theorem value_evaluation
    (source : Expression operations policy contracts world allowed scope environment code result demand requirements)
    (isValue : code.IsValue) : evaluate store receiving before requirements = some [] := by
  induction source using SourceTemplates.Expression.rec (motive_2 := fun _ _ _ _ _ _ _ => True) generalizing before receiving with
  | stable summary => simp only [CoherentSourceTypes.value_row summary isValue, evaluate_empty]
  | callable summary ih => simp only [CallableSources.value_row summary isValue, evaluate_empty]
  | lambda body outward formed ih => exact evaluate_empty
  | purePair left right ihLeft ihRight => exact evaluate_empty
  | pair left right ihLeft ihRight =>
      rw [RecursiveRequirements.evaluate_sequence, ihLeft isValue.1, ihRight isValue.2]
      rfl
  | app | bind | branch | perform | handler | resource | scopedResource | resume | discard | cleanup => cases isValue

  | _ => intros; trivial

/-- Preservation for every actual resume cut, independently of the cut
    constructed by the progress theorem. These are the raw rule's premises. -/

theorem resume_cut_preserves
    (source : SourceTemplates.CheckedConfiguration operations policy contracts tables world outside scope
      (.resume binder value) (front.append (.live owner inputType answerType capture caller tail)) output demand row)
    (resolved : scope.resolve binder = some owner) (closed : ClosedValue value) :
    ∃ remaining : List Nat,
      SourceTemplates.CheckedConfiguration operations policy contracts tables world outside scope value
        (capture.append (front.append (.spent owner answerType caller tail))) output remaining row ∧
      demand = owner :: remaining ∧
      OwnerPhaseTransitions.Trace
        (OwnerPhaseTransitions.available (ownedTickets (front.append (.live owner inputType answerType capture caller tail)))) [owner]
        (OwnerPhaseTransitions.available (ownedTickets (capture.append (front.append (.spent owner answerType caller tail))))) := by
  cases source with
  | checked source unique evaluated accepted => cases source with
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
                (value_evaluation operand closed.1))
              subst operandRow
              simp only [List.nil_append] at currentRows
              subst currentRow
              simp only [noDemand, List.nil_append, spendAll] at resumeChecked pendingChecked
              obtain ⟨combined, collected, combinedSource, combinedCheck, permutation, afterUnique, trace⟩ :=
                resume_segments pendingSource known unique resumeChecked pendingChecked
              let restored := capture.append (front.append (.spent owner answerType caller tail))
              have valueChecked : Checked collected [] (OwnerPhaseTransitions.available (ownedTickets restored))
                  (.request (OwnerPhases.ofStack tables restored) []) [] := .request (by
                    simp only [OwnerSource.exportAt, residual_empty])
              have afterSource := SourceTemplates.Configuration.checked ((value_summary operand closed.1).expression _)
                scopeTyped combinedSource
              have wholeCheck := Checked.sequence valueChecked combinedCheck
              have acceptedAfter : checkFootprint outside (resumeRow ++ pendingRow) = true := by
                simpa only [rows] using accepted
              have afterValid := SourceTemplates.CheckedConfiguration.checked afterSource afterUnique wholeCheck acceptedAfter
              rw [← rows] at afterValid
              refine ⟨_, afterValid, ?_, trace⟩
              simp only [noDemand, List.nil_append, List.cons_append]

theorem focus_resume_not_value (focus : Focus (.resume binder value) child position) : ¬ value.IsValue := by
  cases focus with
  | resume notValue => exact notValue

/-- Every raw step of a ready resume preserves checking. Focus and value
    completion rules cannot apply to this expression with a value operand. -/
theorem resume_step_preserves
    (source : SourceTemplates.CheckedConfiguration operations policy contracts tables world outside scope
      (.resume binder value) stack output demand row)
    (closed : ClosedValue value)
    (step : RawStep ⟨.resume binder value, scope, stack⟩ next created completed) :
    ∃ (owner : Nat) (remaining : List Nat),
      next.expression = value ∧ next.scope = scope ∧
      SourceTemplates.CheckedConfiguration operations policy contracts tables world outside
        next.scope next.expression next.stack output remaining row ∧
      demand = owner :: remaining ∧ created = [] ∧ completed = [.ticket owner] ∧
      OwnerPhaseTransitions.Trace (OwnerPhaseTransitions.available (ownedTickets stack)) [owner]
        (OwnerPhaseTransitions.available (ownedTickets next.stack)) := by
  cases step with
  | focus plain focus tail => exact False.elim (focus_resume_not_value focus closed.1)
  | plug plain value impossible scope tail => cases impossible.1
  | leaveHandler handler value impossible scope tail => cases impossible.1
  | leaveCell identity payload answer savedScope scope value impossible tail => cases impossible.1
  | startCleanup action saved impossible scope tail => cases impossible.1
  | leaveClause ticket answer value impossible scope caller tail => cases impossible.1
  | resume binder owner scope caller inputType answerType front capture tail value ready resolved =>
      obtain ⟨remaining, checked, demand, trace⟩ := resume_cut_preserves source resolved closed
      exact ⟨owner, remaining, rfl, rfl, checked, demand, rfl, rfl, trace⟩

/-- Resumption preserves the complete source-derived checking judgment at every
    stack depth, including the actual reconstructed template store. -/
theorem resume_preserves
    (source : SourceTemplates.CheckedConfiguration operations policy contracts tables world outside scope
      (.resume binder value) stack output demand row)
    (closed : ClosedValue value) :
    ∃ (owner : Nat) (restored : Stack) (remaining : List Nat),
      RawStep ⟨.resume binder value, scope, stack⟩ ⟨value, scope, restored⟩ [] [.ticket owner] ∧
      SourceTemplates.CheckedConfiguration operations policy contracts tables world outside scope value restored output remaining row ∧
      demand = owner :: remaining ∧
      OwnerPhaseTransitions.Trace (OwnerPhaseTransitions.available (ownedTickets stack)) [owner]
        (OwnerPhaseTransitions.available (ownedTickets restored)) := by
  obtain ⟨owner, next, resolved, step, trace⟩ := SourceTemplates.checked_configuration_resume_progress source closed
  obtain ⟨actualOwner, remaining, valueSame, scopeSame, checked, demand, created, completed, actualTrace⟩ :=
    resume_step_preserves source closed step
  have sameOwner : owner = actualOwner := Owner.ticket.inj (List.cons.inj completed).1
  subst actualOwner
  cases next with
  | mk expression nextScope nextStack =>
      change expression = value at valueSame
      change nextScope = scope at scopeSame
      subst expression
      subst nextScope
      exact ⟨owner, nextStack, remaining, step, checked, demand, actualTrace⟩

namespace Examples
open OwnerPhaseTransitions (available)
open SharedResumption.NestedExamples (contracts inner_known outer_known innerBoundary outerBoundary outerCapture)
open SharedResumption.Examples (raw effect operations policy tables outside operation_known)
open SourceTemplates.Examples
  (records innerRequirements inner_lookup outer_lookup outerRequirements outerBoundaryRequirements currentRequirements
    current_source outer_boundary_source inner_checked empty_checked boundary_checked)

theorem nested_general_preservation : ∃ restored : Stack,
    RawStep ⟨.resume 7 .unit, .ticket 7 19, outerBoundary⟩ ⟨.unit, .ticket 7 19, restored⟩ [] [.ticket 19] ∧
    SourceTemplates.CheckedConfiguration operations policy contracts tables [] outside (.ticket 7 19)
      .unit restored .unit [29] raw := by
  obtain ⟨owner, restored, remaining, step, checked, demand, trace⟩ :=
    resume_preserves SourceTemplates.Examples.checked_configuration CallableProtection.Examples.unit_closed
  obtain ⟨sameOwner, sameRemaining⟩ := List.cons.inj demand
  subst owner
  subst remaining
  exact ⟨restored, step, checked⟩

def bindPlain : PlainData :=
  ⟨.bind 99 (.perform (Instantiation.freezeEffect effect) 0 .unit), .none, .unit, .unit, [], rfl⟩

def bindRequirements : Requirements [] := .emitAfter (.request [] []) [] raw

def prefixed : Stack := .push (.plain bindPlain) outerBoundary

def pendingRequirements : Requirements [] :=
  .sequence (bindRequirements.prepend (OwnerPhases.ofStack tables outerBoundary)) outerBoundaryRequirements

def prefixedRequirements : Requirements [19, 29] :=
  .sequence (currentRequirements.prepend (OwnerPhases.ofStack tables prefixed)) pendingRequirements

theorem bind_frame : SourceTemplates.Frame operations policy contracts [] (.plain bindPlain) .unit .unit [] bindRequirements := by
  have suffix : Expression operations policy contracts [] [effect] .none (Environment.empty.extend 99 .unit)
      (.perform (Instantiation.freezeEffect effect) 0 .unit) .unit [] bindRequirements :=
    .perform operation_known List.mem_cons_self (.stable .unit)
      (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])
  exact .plain (.bind suffix) .none rfl rfl

theorem prefixed_source : SourceTemplates.Configuration operations policy contracts tables [] (.ticket 7 19)
    (.resume 7 .unit) prefixed .unit [19, 29] prefixedRequirements records :=
  .checked current_source (.bound (Owners.ports_lookup outer_known)) (.push bind_frame outer_boundary_source)

theorem prefixed_check : Checked records [] (available (ownedTickets prefixed)) prefixedRequirements (raw ++ raw) := by
  let initial := available (ownedTickets prefixed)
  let context := OwnerPhases.ofStack tables prefixed
  let afterOwner := spend initial 19
  let afterAll := spendAll initial [19, 29]
  have innerBody : Checked records (OwnerPhases.ofStack tables innerBoundary ++ context) (spend afterOwner 29) innerRequirements raw :=
    inner_checked (by decide)
  have innerCall : Checked records context afterOwner (.invoke ⟨29, .resume⟩ [] (OwnerPhases.ofStack tables innerBoundary)) raw :=
    .invoke inner_lookup (by decide) (OwnerPhases.consumes_complete rfl) innerBody
  have innerTail : Checked records context (spendAll afterOwner [29]) SourceTemplates.Examples.innerBoundaryRequirements [] :=
    boundary_checked (by decide)
  have outerBody : Checked records context afterOwner outerRequirements raw := by
    simpa only [outerRequirements, List.append_nil] using Checked.sequence innerCall innerTail
  have outerCall : Checked records context initial (.invoke ⟨19, .resume⟩ [29] []) raw :=
    .invoke outer_lookup (by decide) (OwnerPhases.consumes_complete rfl) outerBody
  have current : Checked records context initial currentRequirements raw := .sequence empty_checked outerCall
  have currentPrefixed : Checked records [] initial (currentRequirements.prepend context) raw :=
    RecursiveRequirements.checked_prepend_iff.mpr (by simpa only [List.append_nil] using current)
  have bind : Checked records (OwnerPhases.ofStack tables outerBoundary) afterAll bindRequirements raw :=
    .emitAfter empty_checked (by decide)
  have bindPrefixed : Checked records [] afterAll (bindRequirements.prepend (OwnerPhases.ofStack tables outerBoundary)) raw :=
    RecursiveRequirements.checked_prepend_iff.mpr (by simpa only [List.append_nil] using bind)
  have tail : Checked records [] (spendAll afterAll []) outerBoundaryRequirements [] := boundary_checked (by decide)
  have pending : Checked records [] afterAll pendingRequirements raw := by
    simpa only [pendingRequirements, List.append_nil] using Checked.sequence bindPrefixed tail
  exact .sequence currentPrefixed pending

theorem prefixed_checked : SourceTemplates.CheckedConfiguration operations policy contracts tables [] outside (.ticket 7 19)
    (.resume 7 .unit) prefixed .unit [19, 29] (raw ++ raw) :=
  .checked prefixed_source (by decide) prefixed_check (by decide)

theorem effectful_bind_prefix_preserved : ∃ restored : Stack,
    RawStep ⟨.resume 7 .unit, .ticket 7 19, prefixed⟩ ⟨.unit, .ticket 7 19, restored⟩ [] [.ticket 19] ∧
    SourceTemplates.CheckedConfiguration operations policy contracts tables [] outside (.ticket 7 19)
      .unit restored .unit [29] (raw ++ raw) := by
  obtain ⟨owner, restored, remaining, step, checked, demand, trace⟩ :=
    resume_preserves prefixed_checked CallableProtection.Examples.unit_closed
  obtain ⟨sameOwner, sameRemaining⟩ := List.cons.inj demand
  subst owner
  subst remaining
  exact ⟨restored, step, checked⟩

theorem actual_nested_step_preserved :
    SourceTemplates.CheckedConfiguration operations policy contracts tables [] outside (.ticket 7 19)
      .unit RecursiveTransport.Examples.afterStack .unit [29] raw := by
  obtain ⟨owner, remaining, valueSame, scopeSame, checked, demand, created, completed, trace⟩ :=
    resume_step_preserves SourceTemplates.Examples.checked_configuration CallableProtection.Examples.unit_closed
      RecursiveTransport.Examples.actual_resume
  obtain ⟨sameOwner, sameRemaining⟩ := List.cons.inj demand
  subst owner
  subst remaining
  exact checked

def prefixRestored : Stack := outerCapture.append (.push (.plain bindPlain) (.spent 19 .unit .none .nil))

theorem prefixed_raw_step : RawStep ⟨.resume 7 .unit, .ticket 7 19, prefixed⟩
    ⟨.unit, .ticket 7 19, prefixRestored⟩ [] [.ticket 19] :=
  .resume 7 19 (.ticket 7 19) .none .unit .unit (.push (.plain bindPlain) .nil) outerCapture .nil .unit
    CallableProtection.Examples.unit_closed rfl

theorem effectful_bind_step_preserved :
    SourceTemplates.CheckedConfiguration operations policy contracts tables [] outside (.ticket 7 19)
      .unit prefixRestored .unit [29] (raw ++ raw) := by
  obtain ⟨owner, remaining, valueSame, scopeSame, checked, demand, created, completed, trace⟩ :=
    resume_step_preserves prefixed_checked CallableProtection.Examples.unit_closed prefixed_raw_step
  obtain ⟨sameOwner, sameRemaining⟩ := List.cons.inj demand
  subst owner
  subst remaining
  exact checked

end Examples

end Ash.OneShot.RecursiveRecomposition

#print axioms Ash.OneShot.RecursiveRecomposition.evaluate_empty
#print axioms Ash.OneShot.RecursiveRecomposition.evaluate_spent
#print axioms Ash.OneShot.RecursiveRecomposition.merge_empty_left
#print axioms Ash.OneShot.RecursiveRecomposition.merge_empty_right
#print axioms Ash.OneShot.RecursiveRecomposition.segment_append
#print axioms Ash.OneShot.RecursiveRecomposition.segment_append_checked
#print axioms Ash.OneShot.RecursiveRecomposition.move_records
#print axioms Ash.OneShot.RecursiveRecomposition.normalize_replaced
#print axioms Ash.OneShot.RecursiveRecomposition.replace_live
#print axioms Ash.OneShot.RecursiveRecomposition.remove_owner_filter
#print axioms Ash.OneShot.RecursiveRecomposition.remove_owner_permutation
#print axioms Ash.OneShot.RecursiveRecomposition.remove_owner_absent
#print axioms Ash.OneShot.RecursiveRecomposition.removed_records
#print axioms Ash.OneShot.RecursiveRecomposition.resume_segments
#print axioms Ash.OneShot.RecursiveRecomposition.value_summary
#print axioms Ash.OneShot.RecursiveRecomposition.value_evaluation
#print axioms Ash.OneShot.RecursiveRecomposition.resume_cut_preserves
#print axioms Ash.OneShot.RecursiveRecomposition.focus_resume_not_value
#print axioms Ash.OneShot.RecursiveRecomposition.resume_step_preserves
#print axioms Ash.OneShot.RecursiveRecomposition.resume_preserves
#print axioms Ash.OneShot.RecursiveRecomposition.Examples.nested_general_preservation
#print axioms Ash.OneShot.RecursiveRecomposition.Examples.bind_frame
#print axioms Ash.OneShot.RecursiveRecomposition.Examples.prefixed_source
#print axioms Ash.OneShot.RecursiveRecomposition.Examples.prefixed_check
#print axioms Ash.OneShot.RecursiveRecomposition.Examples.prefixed_checked
#print axioms Ash.OneShot.RecursiveRecomposition.Examples.effectful_bind_prefix_preserved
#print axioms Ash.OneShot.RecursiveRecomposition.Examples.actual_nested_step_preserved
#print axioms Ash.OneShot.RecursiveRecomposition.Examples.prefixed_raw_step
#print axioms Ash.OneShot.RecursiveRecomposition.Examples.effectful_bind_step_preserved
