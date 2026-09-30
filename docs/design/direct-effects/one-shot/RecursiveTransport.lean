import SourceTemplates

/-!
Transport recursive checking through consumed owner boundaries and removal of
spent continuation templates. These operations preserve interpretation order;
no effect or computation conversion is introduced.
-/

namespace Ash.OneShot.RecursiveTransport
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open OwnerPhaseTransitions (Phases spend spendAll)
open RecursiveRequirements (Requirements Store Key Checked)

variable {before after phases : Phases}

/-- Consumed boundaries have no remaining selection or protection role.
    A spent boundary whose owner is still marked available remains visible so
    that inconsistent duplicate names cannot bypass the selection check. -/
def normalize (phases : Phases) : OwnerPhases.Context → OwnerPhases.Context
  | [] => []
  | .ordinary layer :: rest => .ordinary layer :: normalize phases rest
  | .live owner held :: rest =>
      if phases owner = .consumed then normalize phases rest
      else .live owner held :: normalize phases rest
  | .spent owner :: rest =>
      if phases owner = .consumed then normalize phases rest
      else .spent owner :: normalize phases rest

theorem normalize_append (phases : Phases) (first second : OwnerPhases.Context) :
    normalize phases (first ++ second) = normalize phases first ++ normalize phases second := by
  induction first with
  | nil => rfl
  | cons entry rest ih => cases entry <;> simp only [List.cons_append, normalize] <;> (try split) <;> simp_all

theorem normalize_project :
    OwnerPhases.project (normalize phases context) = OwnerPhaseTransitions.project context phases := by
  induction context with
  | nil => rfl
  | cons entry rest ih => cases entry with
      | ordinary layer => simp only [normalize, OwnerPhases.project, OwnerPhaseTransitions.project, ih]
      | spent owner => simp only [normalize, OwnerPhaseTransitions.project]; split <;> simp_all [OwnerPhases.project]
      | live owner held => cases phase : phases owner <;>
          simp [normalize, OwnerPhases.project, OwnerPhaseTransitions.project, phase, ih]

theorem normalize_later (later : ∀ owner, before owner = .consumed → after owner = .consumed) :
    normalize after (normalize before context) = normalize after context := by
  induction context with
  | nil => rfl
  | cons entry rest ih => cases entry with
      | ordinary layer => simp only [normalize, ih]
      | live owner held | spent owner =>
          by_cases consumed : before owner = .consumed
          · simp [normalize, consumed, later owner consumed, ih]
          · simp only [normalize, consumed, if_false]; split <;> simp_all

theorem phases_spend_later : ∀ other, before other = .consumed → spend before owner other = .consumed := by
  intro other consumed
  simp only [spend]
  split <;> simp_all

theorem phases_spendAll_later : ∀ other, before other = .consumed → spendAll before owners other = .consumed := by
  intro other consumed
  rw [OwnerPhaseTransitions.spendAll_at]
  split <;> simp_all

theorem normalized_later (same : normalize before first = normalize before second)
    (later : ∀ owner, before owner = .consumed → after owner = .consumed) :
    normalize after first = normalize after second := by
  rw [← normalize_later (context := first) later, same, normalize_later later]

theorem normalized_prefix (same : normalize phases first = normalize phases second) :
    normalize phases (prefixContext ++ first) = normalize phases (prefixContext ++ second) := by
  simp only [normalize_append, same]

theorem export_normalized (same : normalize phases first = normalize phases second) :
    OwnerSource.exportAt first phases raw = OwnerSource.exportAt second phases raw := by
  simp only [OwnerSource.exportAt, ← normalize_project, same]

theorem consume_normalized (ready : phases owner = .available) :
    (OwnerPhases.consume owner (normalize phases context)).isSome = (OwnerPhases.consume owner context).isSome := by
  induction context with
  | nil => rfl
  | cons entry rest ih => cases entry with
      | ordinary layer => simp only [normalize, OwnerPhases.consume, Option.isSome_map, ih]
      | live other held | spent other =>
          by_cases consumed : phases other = .consumed
          · have different : owner ≠ other := by intro same; subst other; rw [ready] at consumed; cases consumed
            simp [normalize, consumed, OwnerPhases.consume, different, ih]
          · simp only [normalize, consumed, if_false, OwnerPhases.consume]
            split <;> simp_all

theorem selection_transport (same : normalize phases first = normalize phases second)
    (ready : phases owner = .available) (selection : OwnerPhases.Consumes owner first waiting) :
    ∃ next, OwnerPhases.Consumes owner second next := by
  have existsFirst : (OwnerPhases.consume owner first).isSome = true := by
    rw [OwnerPhases.consumes_sound selection]; rfl
  have existsSecond : (OwnerPhases.consume owner second).isSome = true := by
    rw [← consume_normalized ready, ← same, consume_normalized ready, existsFirst]
  cases found : OwnerPhases.consume owner second with
  | none => simp [found] at existsSecond
  | some next => exact ⟨next, OwnerPhases.consumes_complete found⟩

theorem consumed_normalized (selection : OwnerPhases.Consumes owner first second)
    (consumed : phases owner = .consumed) : normalize phases first = normalize phases second := by
  induction selection with
  | hit => simp [normalize, consumed]
  | ordinary selection ih => simp only [normalize, ih]
  | live different selection ih | spent different selection ih => simp only [normalize]; split <;> simp_all

theorem available_earlier (later : ∀ owner, before owner = .consumed → after owner = .consumed)
    (ready : after owner = .available) : before owner = .available := by
  cases phase : before owner with
  | available => rfl
  | consumed => have impossible := later owner phase; rw [ready] at impossible; cases impossible

/-- Only available owners can cause template lookup to contribute a row.
    Both source contexts and stores may change as long as those observations
    agree. The induction includes every recursively checked captured body. -/
theorem checked_transport
    (checked : Checked store receiving before requirements row)
    (stores : ∀ key : Key, before key.owner = .available →
      RecursiveRequirements.lookup key store = RecursiveRequirements.lookup key nextStore)
    (contexts : normalize before receiving = normalize before otherContext) :
    Checked nextStore otherContext before requirements row := by
  induction checked generalizing nextStore otherContext with
  | request exported => exact .request ((export_normalized (normalized_prefix contexts)).symm.trans exported)
  | retire ready => exact .retire ready
  | spent consumed => exact .spent consumed
  | invoke known ready selection next ih =>
      have ownerReady := OwnerPhaseTransitions.trace_available (PhaseRechecking.check_owners_iff.mp ready) _ List.mem_cons_self
      obtain ⟨waiting, selected⟩ := selection_transport (normalized_prefix contexts) ownerReady selection
      exact .invoke ((stores _ ownerReady).symm.trans known) ready selected
        (ih (fun key available => stores key (available_earlier phases_spend_later available))
          (normalized_later (normalized_prefix contexts) phases_spend_later))
  | sequence first second ihFirst ihSecond =>
      exact .sequence (ihFirst stores contexts)
        (ihSecond (fun key available => stores key (available_earlier phases_spendAll_later available))
          (normalized_later contexts phases_spendAll_later))
  | emitAfter body exported ih =>
      exact .emitAfter (ih stores contexts)
        ((export_normalized (normalized_prefix (normalized_later contexts phases_spendAll_later))).symm.trans exported)
  | choice first second ihFirst ihSecond => exact .choice (ihFirst stores contexts) (ihSecond stores contexts)

theorem checked_transport_iff
    (stores : ∀ key : Key, before key.owner = .available →
      RecursiveRequirements.lookup key store = RecursiveRequirements.lookup key nextStore)
    (contexts : normalize before receiving = normalize before otherContext) :
    Checked store receiving before requirements row ↔ Checked nextStore otherContext before requirements row :=
  ⟨fun checked => checked_transport checked stores contexts,
    fun checked => checked_transport checked (fun key ready => (stores key ready).symm) contexts.symm⟩

theorem evaluate_transport
    (stores : ∀ key : Key, before key.owner = .available →
      RecursiveRequirements.lookup key store = RecursiveRequirements.lookup key nextStore)
    (contexts : normalize before receiving = normalize before otherContext) :
    RecursiveRequirements.evaluate store receiving before requirements =
      RecursiveRequirements.evaluate nextStore otherContext before requirements := by
  cases original : RecursiveRequirements.evaluate store receiving before requirements with
  | some row => exact (RecursiveRequirements.checked_complete
      (checked_transport (RecursiveRequirements.evaluate_sound original) stores contexts)).symm
  | none =>
      cases changed : RecursiveRequirements.evaluate nextStore otherContext before requirements with
      | none => rfl
      | some row =>
          have impossible := RecursiveRequirements.checked_complete
            (checked_transport (RecursiveRequirements.evaluate_sound changed)
              (fun key ready => (stores key ready).symm) contexts.symm)
          rw [original] at impossible
          cases impossible

def removeOwner (owner : Nat) : Store → Store
  | [] => []
  | (key, body) :: rest =>
      if key.owner = owner then removeOwner owner rest else (key, body) :: removeOwner owner rest

theorem lookup_remove_other (different : key.owner ≠ owner) :
    RecursiveRequirements.lookup key (removeOwner owner store) = RecursiveRequirements.lookup key store := by
  induction store with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨candidate, body⟩ := entry
      by_cases removed : candidate.owner = owner
      · have distinct : key ≠ candidate := fun same => different (same ▸ removed)
        simp [removeOwner, removed, RecursiveRequirements.lookup, distinct, ih]
      · simp only [removeOwner, removed, if_false, RecursiveRequirements.lookup]
        split <;> simp_all

theorem lookup_remove_self : RecursiveRequirements.lookup ⟨owner, mode⟩ (removeOwner owner store) = none := by
  induction store with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨candidate, body⟩ := entry
      by_cases removed : candidate.owner = owner
      · simp only [removeOwner, removed, if_true, ih]
      · have distinct : (⟨owner, mode⟩ : Key) ≠ candidate := by
          intro same
          have ownerSame := congrArg Key.owner same
          exact removed ownerSame.symm
        simp only [removeOwner, removed, if_false, RecursiveRequirements.lookup, distinct, ih]

theorem remove_consumed_agrees (consumed : before owner = .consumed) :
    ∀ key : Key, before key.owner = .available →
      RecursiveRequirements.lookup key store = RecursiveRequirements.lookup key (removeOwner owner store) := by
  intro key ready
  symm
  apply lookup_remove_other
  intro same
  rw [same, consumed] at ready
  cases ready

theorem checked_remove_consumed (checked : Checked store receiving before requirements row)
    (consumed : before owner = .consumed) :
    Checked (removeOwner owner store) receiving before requirements row :=
  checked_transport checked (remove_consumed_agrees consumed) rfl

/-- The body checked under the phase-updated caller remains checked under the
    actual live-to-spent caller, with both modes of the consumed owner removed
    from the template store. -/
theorem resume_caller_transport
    (selection : OwnerPhases.Consumes owner receiving waiting)
    (checked : Checked store receiving (spend before owner) requirements row) :
    Checked (removeOwner owner store) waiting (spend before owner) requirements row :=
  checked_transport checked (remove_consumed_agrees (OwnerPhaseTransitions.spend_self before owner))
    (consumed_normalized selection (OwnerPhaseTransitions.spend_self before owner))

def recordOwners (store : Store) : List Nat := store.map (fun (entry : Key × RecursiveRequirements.Template) => entry.1.owner)

def recordKeys (store : Store) : List Key := store.map Prod.fst

theorem record_key_member (member : (key, template) ∈ store) : key ∈ recordKeys store :=
  List.mem_map.mpr ⟨(key, template), member, rfl⟩

theorem record_owner_member (member : (key, template) ∈ store) : key.owner ∈ recordOwners store :=
  List.mem_map.mpr ⟨(key, template), member, rfl⟩

theorem lookup_of_member (unique : (recordKeys store).Nodup) (member : (key, template) ∈ store) :
    RecursiveRequirements.lookup key store = some template := by
  induction store with
  | nil => cases member
  | cons entry rest ih =>
      obtain ⟨candidate, body⟩ := entry
      have absent := (List.nodup_cons.mp unique).1
      have restUnique := (List.nodup_cons.mp unique).2
      rcases List.mem_cons.mp member with same | remaining
      · cases same; simp [RecursiveRequirements.lookup]
      · have different : key ≠ candidate := by
          intro same
          have present := record_key_member remaining
          rw [same] at present
          exact absent present
        simp only [RecursiveRequirements.lookup, different, if_false]
        exact ih restUnique remaining

theorem lookup_permuted (unique : (recordKeys store).Nodup) (permutation : store.Perm reordered) :
    RecursiveRequirements.lookup key store = RecursiveRequirements.lookup key reordered := by
  have otherUnique : (recordKeys reordered).Nodup := (permutation.map Prod.fst).nodup unique
  cases original : RecursiveRequirements.lookup key store with
  | some template => exact (lookup_of_member otherUnique
      (permutation.mem_iff.mp (SourceTemplates.lookup_member original))).symm
  | none => cases changed : RecursiveRequirements.lookup key reordered with
      | none => rfl
      | some template =>
          have impossible := lookup_of_member unique (permutation.mem_iff.mpr (SourceTemplates.lookup_member changed))
          rw [original] at impossible
          cases impossible

theorem record_owners_sublist
    (source : SourceTemplates.Segment operations policy contracts tables world stack input output demand requirements records) :
    (recordOwners records).Sublist (ownedTickets stack) := by
  induction source with
  | nil => exact .slnil
  | @push entry input middle headDemand first rest output tailDemand second records head tail ih =>
      cases entry <;> first | exact ih | exact .cons _ ih
  | live known inputAnnotation answerAnnotation scopeKnown held saved tail ihSaved ihTail =>
      simpa only [recordOwners, List.map_cons, List.map_append, ownedTickets] using List.Sublist.cons_cons _ (ihSaved.append ihTail)
  | spent known answerAnnotation scopeKnown tail ih => exact ih

theorem record_keys_unique (unique : (recordOwners store).Nodup) : (recordKeys store).Nodup := by
  induction store with
  | nil => exact List.nodup_nil
  | cons entry rest ih =>
      obtain ⟨key, body⟩ := entry
      have absent := (List.nodup_cons.mp unique).1
      have restUnique := (List.nodup_cons.mp unique).2
      refine List.nodup_cons.mpr ⟨?_, ih restUnique⟩
      intro present
      obtain ⟨⟨candidate, template⟩, member, same⟩ := List.mem_map.mp present
      have ownerPresent := record_owner_member member
      change candidate = key at same
      rw [same] at ownerPresent
      exact absent ownerPresent

theorem source_records_unique
    (source : SourceTemplates.Segment operations policy contracts tables world stack input output demand requirements records)
    (unique : (ownedTickets stack).Nodup) : (recordKeys records).Nodup :=
  record_keys_unique ((record_owners_sublist source).nodup unique)

theorem remove_owner_sublist : (removeOwner owner store).Sublist store := by
  induction store with
  | nil => exact .slnil
  | cons entry rest ih =>
      obtain ⟨key, body⟩ := entry
      simp only [removeOwner]
      split
      · exact .cons _ ih
      · exact .cons_cons _ ih

theorem remove_owner_unique (unique : (recordKeys store).Nodup) : (recordKeys (removeOwner owner store)).Nodup :=
  (remove_owner_sublist.map Prod.fst).nodup unique

theorem checked_permuted (checked : Checked store receiving before requirements row)
    (unique : (recordKeys store).Nodup) (permutation : store.Perm reordered) :
    Checked reordered receiving before requirements row :=
  checked_transport checked (fun _ _ => lookup_permuted unique permutation) rfl

theorem selected_caller (selected : SourceTemplates.ActiveCapture owner capture stack) :
    ∃ (front : Stack) (input answer : Ty) (caller : Execution.Scope) (tail : Stack),
      stack = front.append (.live owner input answer capture caller tail) ∧
      OwnerPhases.Consumes owner (OwnerPhases.ofStack tables stack)
        (OwnerPhases.ofStack tables (front.append (.spent owner answer caller tail))) := by
  induction selected with
  | here => exact ⟨.nil, _, _, _, _, rfl, .hit⟩
  | @push rest frame selected ih =>
      obtain ⟨front, input, answer, caller, tail, same, consumed⟩ := ih
      refine ⟨.push frame front, input, answer, caller, tail, by simp only [Stack.append, same], ?_⟩
      cases frame <;> exact .ordinary consumed
  | @live other rest input answer saved caller different selected ih =>
      obtain ⟨front, targetInput, targetAnswer, targetCaller, tail, same, consumed⟩ := ih
      exact ⟨.live other input answer saved caller front, targetInput, targetAnswer, targetCaller, tail,
        by simp only [Stack.append, same], .live different consumed⟩
  | @spent other rest answer caller different selected ih =>
      obtain ⟨front, targetInput, targetAnswer, targetCaller, tail, same, consumed⟩ := ih
      exact ⟨.spent other answer caller front, targetInput, targetAnswer, targetCaller, tail,
        by simp only [Stack.append, same], .spent different consumed⟩

/-- The actual resumed body retains its recursive check at the physical waiting
    caller and actual successor owner map, after deleting the spent owner from
    the template store. The shared historical contract registry is retained. -/
theorem checked_resume_body
    (source : SourceTemplates.Segment operations policy contracts tables world stack input output pendingDemand pending records)
    (unique : (ownedTickets stack).Nodup)
    (checked : Checked records (OwnerPhases.ofStack tables stack) (OwnerPhaseTransitions.available (ownedTickets stack))
      (.invoke ⟨owner, .resume⟩ demand []) row)
    (resolved : scope.resolve binder = some owner) (closed : ClosedValue value) :
    ∃ (capture front : Stack) (inputType answerType : Ty) (caller : Execution.Scope) (tail : Stack)
      (contract : CoherentSourceTypes.Owners.Contract) (requirements : Requirements contract.resumeDemand) (nested : Store),
      stack = front.append (.live owner inputType answerType capture caller tail) ∧
      contracts owner = some contract ∧ demand = contract.resumeDemand ∧
      SourceTemplates.Segment operations policy contracts tables world capture contract.input contract.answer
        contract.resumeDemand requirements nested ∧
      Checked (removeOwner owner records) (OwnerPhases.ofStack tables (front.append (.spent owner answerType caller tail)))
        (OwnerPhaseTransitions.available (ownedTickets (capture.append (front.append (.spent owner answerType caller tail)))))
        requirements row ∧
      RawStep ⟨.resume binder value, scope, stack⟩
        ⟨value, scope, capture.append (front.append (.spent owner answerType caller tail))⟩ [] [.ticket owner] := by
  obtain ⟨body, waiting, known, ready, selection, bodyChecked⟩ := RecursiveRequirements.checked_invocation checked
  obtain ⟨capture, active⟩ := SourceTemplates.consume_active_capture (OwnerPhases.consumes_sound selection)
  obtain ⟨contract, requirements, nested, contractKnown, sameTemplate, saved⟩ :=
    SourceTemplates.certified_selected (SourceTemplates.lookup_certified source known) unique active
  have sameDemand := congrArg Sigma.fst sameTemplate
  change demand = contract.resumeDemand at sameDemand
  have sameBody := (Sigma.mk.inj sameTemplate).2
  subst demand
  cases eq_of_heq sameBody
  obtain ⟨front, inputType, answerType, caller, tail, sameStack, selected⟩ := selected_caller (tables := tables) active
  have transported := resume_caller_transport selected bodyChecked
  have trace := OwnerPhaseTransitions.resume_phase_trace (by simpa only [sameStack] using unique)
  have actualPhases := OwnerPhaseTransitions.trace_result trace
  change OwnerPhaseTransitions.available (ownedTickets (capture.append (front.append (.spent owner answerType caller tail)))) =
    spend (OwnerPhaseTransitions.available (ownedTickets (front.append (.live owner inputType answerType capture caller tail)))) owner at actualPhases
  rw [← sameStack] at actualPhases
  rw [← actualPhases] at transported
  refine ⟨capture, front, inputType, answerType, caller, tail, contract, requirements, nested,
    sameStack, contractKnown, rfl, saved, transported, ?_⟩
  rw [sameStack]
  exact .resume binder owner scope caller inputType answerType front capture tail value closed resolved

namespace Examples
open OwnerPhaseTransitions (available)
open CoherentSourceTypes
open SharedResumption.NestedExamples
  (contracts inner_known outer_known innerCapture innerBoundary outerCapture outerBoundary outerWaiting resumePlain)
open SharedResumption.Examples (raw effect operations policy tables outside)
open SourceTemplates.Examples
  (records innerRecords innerRequirements innerBoundaryRequirements outerRequirements outerBoundaryRequirements
    inner_source inner_lookup empty_checked inner_checked boundary_checked)

def afterStack : Stack := outerCapture.append outerWaiting

def afterPhases : Phases := spend (available (ownedTickets outerBoundary)) 19

def afterInnerRequirements : Requirements [] := .sequence (.spent 29) outerBoundaryRequirements

def afterPendingRequirements : Requirements [29] :=
  .sequence (.invoke ⟨29, .resume⟩ [] (OwnerPhases.ofStack tables (innerBoundary.append outerWaiting))) afterInnerRequirements

def afterRequirements : Requirements [29] :=
  .sequence (.request (OwnerPhases.ofStack tables afterStack) []) afterPendingRequirements

theorem waiting_source : SourceTemplates.Segment operations policy contracts tables [] outerWaiting
    .unit .unit [] outerBoundaryRequirements [] :=
  .spent outer_known rfl ⟨.none, .none⟩ .nil

theorem inner_waiting_source : SourceTemplates.Segment operations policy contracts tables [] (innerBoundary.append outerWaiting)
    .unit .unit [] afterInnerRequirements innerRecords :=
  .live inner_known rfl rfl ⟨.none, .none⟩ rfl inner_source waiting_source

theorem after_pending_source : SourceTemplates.Segment operations policy contracts tables [] afterStack
    .unit .unit [29] afterPendingRequirements innerRecords := by
  have context : SourceTemplates.Context operations policy contracts [] Environment.empty [effect] (.ticket 8 29) (.resume 8)
      .unit .unit [29] (.invoke ⟨29, .resume⟩ [] []) :=
    .resume inner_known rfl rfl (fun _ member => member)
      (by simp [SharedResumption.NestedExamples.inner, SharedResumption.Examples.contract,
        ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])
  exact .push (.plain (plain := resumePlain) context (.bound (Owners.ports_lookup inner_known)) rfl rfl) inner_waiting_source

theorem outer_body_checked : Checked records (OwnerPhases.ofStack tables outerBoundary) afterPhases outerRequirements raw := by
  have body : Checked records (OwnerPhases.ofStack tables innerBoundary ++ OwnerPhases.ofStack tables outerBoundary)
      (spend afterPhases 29) innerRequirements raw := inner_checked (by decide)
  have invocation : Checked records (OwnerPhases.ofStack tables outerBoundary) afterPhases
      (.invoke ⟨29, .resume⟩ [] (OwnerPhases.ofStack tables innerBoundary)) raw :=
    .invoke inner_lookup (by decide) (OwnerPhases.consumes_complete rfl) body
  have rest : Checked records (OwnerPhases.ofStack tables outerBoundary) (spendAll afterPhases [29]) innerBoundaryRequirements [] :=
    boundary_checked (by decide)
  simpa only [outerRequirements, List.append_nil] using Checked.sequence invocation rest

theorem after_store : removeOwner 19 records = innerRecords := rfl

theorem transported_body : Checked innerRecords (OwnerPhases.ofStack tables outerWaiting) afterPhases outerRequirements raw := by
  have result := resume_caller_transport (owner := 19) (before := available (ownedTickets outerBoundary))
    (waiting := OwnerPhases.ofStack tables outerWaiting) OwnerPhases.Consumes.hit outer_body_checked
  simpa only [after_store, afterPhases] using result

theorem actual_phases : available (ownedTickets afterStack) = afterPhases :=
  OwnerPhaseTransitions.trace_result (OwnerPhaseTransitions.resume_phase_trace
    (front := Stack.nil) (capture := outerCapture) (tail := Stack.nil)
    (owner := 19) (input := Ty.unit) (answer := Ty.unit) (caller := Execution.Scope.none) (by decide))

theorem after_pending_checked : Checked innerRecords [] afterPhases afterPendingRequirements raw := by
  obtain ⟨callRow, tailRow, invocation, rest, combined⟩ := RecursiveRequirements.checked_sequence_parts transported_body
  have tailEvaluation : RecursiveRequirements.evaluate innerRecords (OwnerPhases.ofStack tables outerWaiting)
      (spendAll afterPhases [29]) innerBoundaryRequirements = some [] := by
    rw [innerBoundaryRequirements, RecursiveRequirements.evaluate_sequence]
    simp only [RecursiveRequirements.evaluate, RecursiveRequirements.evaluateFuel]
    decide
  have tailEmpty := Option.some.inj ((RecursiveRequirements.checked_complete rest).symm.trans tailEvaluation)
  subst tailRow
  simp only [List.append_nil] at combined
  subst callRow
  have prefixed : Checked innerRecords [] afterPhases
      ((Requirements.invoke ⟨29, .resume⟩ [] (OwnerPhases.ofStack tables innerBoundary)).prepend
        (OwnerPhases.ofStack tables outerWaiting)) raw :=
    RecursiveRequirements.checked_prepend_iff.mpr (by simpa only [List.append_nil] using invocation)
  have finish : Checked innerRecords [] (spendAll afterPhases [29]) afterInnerRequirements [] :=
    .sequence (.spent (by decide)) (.sequence (.spent (by decide)) (.request (by simp [OwnerSource.exportAt, residual_empty])))
  have combined := Checked.sequence prefixed finish
  simpa only [afterPendingRequirements, Requirements.prepend, OwnerPhases.stack_append, List.append_nil] using combined

theorem after_configuration_source : SourceTemplates.Configuration operations policy contracts tables [] (.ticket 7 19) .unit
    afterStack .unit [29] afterRequirements innerRecords :=
  .checked (.stable (allowed := [effect]) .unit) (.bound (Owners.ports_lookup outer_known)) after_pending_source

theorem after_recursive_check : Checked innerRecords [] (available (ownedTickets afterStack)) afterRequirements raw := by
  rw [actual_phases]
  have value : Checked innerRecords [] afterPhases (.request (OwnerPhases.ofStack tables afterStack) []) [] :=
    .request (by simp [OwnerSource.exportAt, residual_empty])
  exact .sequence value after_pending_checked

theorem after_configuration_checked : SourceTemplates.CheckedConfiguration operations policy contracts tables [] outside
    (.ticket 7 19) .unit afterStack .unit [29] raw :=
  .checked after_configuration_source (by decide) after_recursive_check (by decide)

theorem actual_resume : RawStep ⟨.resume 7 .unit, .ticket 7 19, outerBoundary⟩
    ⟨.unit, .ticket 7 19, afterStack⟩ [] [.ticket 19] :=
  .resume 7 19 (.ticket 7 19) .none .unit .unit .nil outerCapture .nil .unit CallableProtection.Examples.unit_closed rfl

theorem nested_resume_preserved :
    SourceTemplates.CheckedConfiguration operations policy contracts tables [] outside (.ticket 7 19)
      (.resume 7 .unit) outerBoundary .unit [19, 29] raw ∧
    RawStep ⟨.resume 7 .unit, .ticket 7 19, outerBoundary⟩ ⟨.unit, .ticket 7 19, afterStack⟩ [] [.ticket 19] ∧
    SourceTemplates.CheckedConfiguration operations policy contracts tables [] outside (.ticket 7 19)
      .unit afterStack .unit [29] raw :=
  ⟨SourceTemplates.Examples.checked_configuration, actual_resume, after_configuration_checked⟩

theorem after_ports : ScopedPorts.ConfigurationTyped operations.ports contracts.ports.types []
    ⟨.unit, .ticket 7 19, afterStack⟩ .unit := SourceTemplates.checked_configuration_ports after_configuration_checked

theorem available_spent_still_blocks :
    OwnerPhases.consume 19 (normalize (available [19]) [.spent 19, .live 19 false]) = none := by decide

theorem reordered_store_checked : Checked
    ([(⟨29, .resume⟩, ⟨[], innerRequirements⟩), (⟨19, .resume⟩, ⟨[29], outerRequirements⟩)] : Store)
    [] (available (ownedTickets outerBoundary)) SourceTemplates.Examples.requirements raw :=
  checked_permuted SourceTemplates.Examples.recursive_check (by decide) (List.Perm.swap _ _ [])

def mixedModes : Store := [(⟨19, .resume⟩, ⟨[], .request [] raw⟩), (⟨19, .dispose⟩, ⟨[], .request [] []⟩)]

theorem mixed_modes_have_unique_keys : (recordKeys mixedModes).Nodup := by decide

theorem mixed_modes_share_owner : ¬ (recordOwners mixedModes).Nodup := by decide

theorem mixed_modes_reorder :
    RecursiveRequirements.lookup key mixedModes =
      RecursiveRequirements.lookup key ([(⟨19, .dispose⟩, ⟨[], .request [] []⟩), (⟨19, .resume⟩, ⟨[], .request [] raw⟩)] : Store) :=
  lookup_permuted mixed_modes_have_unique_keys (List.Perm.swap _ _ [])

theorem mixed_modes_removed : removeOwner 19 mixedModes = [] := rfl

end Examples

end Ash.OneShot.RecursiveTransport

#print axioms Ash.OneShot.RecursiveTransport.normalize_append
#print axioms Ash.OneShot.RecursiveTransport.normalize_project
#print axioms Ash.OneShot.RecursiveTransport.normalize_later
#print axioms Ash.OneShot.RecursiveTransport.phases_spend_later
#print axioms Ash.OneShot.RecursiveTransport.phases_spendAll_later
#print axioms Ash.OneShot.RecursiveTransport.normalized_later
#print axioms Ash.OneShot.RecursiveTransport.normalized_prefix
#print axioms Ash.OneShot.RecursiveTransport.export_normalized
#print axioms Ash.OneShot.RecursiveTransport.consume_normalized
#print axioms Ash.OneShot.RecursiveTransport.selection_transport
#print axioms Ash.OneShot.RecursiveTransport.consumed_normalized
#print axioms Ash.OneShot.RecursiveTransport.available_earlier
#print axioms Ash.OneShot.RecursiveTransport.checked_transport
#print axioms Ash.OneShot.RecursiveTransport.checked_transport_iff
#print axioms Ash.OneShot.RecursiveTransport.evaluate_transport
#print axioms Ash.OneShot.RecursiveTransport.lookup_remove_other
#print axioms Ash.OneShot.RecursiveTransport.lookup_remove_self
#print axioms Ash.OneShot.RecursiveTransport.remove_consumed_agrees
#print axioms Ash.OneShot.RecursiveTransport.checked_remove_consumed
#print axioms Ash.OneShot.RecursiveTransport.resume_caller_transport
#print axioms Ash.OneShot.RecursiveTransport.record_key_member
#print axioms Ash.OneShot.RecursiveTransport.record_owner_member
#print axioms Ash.OneShot.RecursiveTransport.lookup_of_member
#print axioms Ash.OneShot.RecursiveTransport.lookup_permuted
#print axioms Ash.OneShot.RecursiveTransport.record_owners_sublist
#print axioms Ash.OneShot.RecursiveTransport.record_keys_unique
#print axioms Ash.OneShot.RecursiveTransport.source_records_unique
#print axioms Ash.OneShot.RecursiveTransport.remove_owner_sublist
#print axioms Ash.OneShot.RecursiveTransport.remove_owner_unique
#print axioms Ash.OneShot.RecursiveTransport.checked_permuted
#print axioms Ash.OneShot.RecursiveTransport.selected_caller
#print axioms Ash.OneShot.RecursiveTransport.checked_resume_body
#print axioms Ash.OneShot.RecursiveTransport.Examples.waiting_source
#print axioms Ash.OneShot.RecursiveTransport.Examples.inner_waiting_source
#print axioms Ash.OneShot.RecursiveTransport.Examples.after_pending_source
#print axioms Ash.OneShot.RecursiveTransport.Examples.outer_body_checked
#print axioms Ash.OneShot.RecursiveTransport.Examples.after_store
#print axioms Ash.OneShot.RecursiveTransport.Examples.transported_body
#print axioms Ash.OneShot.RecursiveTransport.Examples.actual_phases
#print axioms Ash.OneShot.RecursiveTransport.Examples.after_pending_checked
#print axioms Ash.OneShot.RecursiveTransport.Examples.after_configuration_source
#print axioms Ash.OneShot.RecursiveTransport.Examples.after_recursive_check
#print axioms Ash.OneShot.RecursiveTransport.Examples.after_configuration_checked
#print axioms Ash.OneShot.RecursiveTransport.Examples.actual_resume
#print axioms Ash.OneShot.RecursiveTransport.Examples.nested_resume_preserved
#print axioms Ash.OneShot.RecursiveTransport.Examples.after_ports
#print axioms Ash.OneShot.RecursiveTransport.Examples.available_spent_still_blocks
#print axioms Ash.OneShot.RecursiveTransport.Examples.reordered_store_checked
#print axioms Ash.OneShot.RecursiveTransport.Examples.mixed_modes_have_unique_keys
#print axioms Ash.OneShot.RecursiveTransport.Examples.mixed_modes_share_owner
#print axioms Ash.OneShot.RecursiveTransport.Examples.mixed_modes_reorder
#print axioms Ash.OneShot.RecursiveTransport.Examples.mixed_modes_removed
