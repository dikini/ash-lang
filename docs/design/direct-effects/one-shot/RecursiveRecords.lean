import RecursiveCompletion

/-!
Closing records are collected from actual live captures. Each record follows
the executable closing plan and retains callback source, rather than trusting
the contract's declared closing demand. Resume and disposal use distinct keys
for the same owner in one recursive checking store.
-/

namespace Ash.OneShot.RecursiveRecords
open ScopedExpressions ScopedExecution CoherentSourceTypes ProtectionContracts ProtectionResiduals
open RecursiveRequirements (Requirements Store Key Checked evaluate)
open RecursiveClosing (PlanTemplate)
open SourceTemplates (Segment CapturedIn)
open OwnerClosingSource (retirements)
open OwnerPhaseTransitions (Phases available spend spendAll)


theorem plan_context_scope (tables : CallableProtectionFrames.Tables) (plan : List CloseEntry) :
    OwnerPhases.ofStack tables (closeControl first plan) = OwnerPhases.ofStack tables (closeControl second plan) := by
  induction plan with
  | nil => rfl
  | cons entry rest ih => cases entry <;>
      simp only [closeControl, CloseEntry.frame, OwnerPhases.ofStack, OwnerPhases.frameEntry,
        ExecFrame.erase, ActionData.erase, ProtectionContexts.frameProtected] <;> rw [ih]

theorem template_scope (template : PlanTemplate operations policy contracts tables world first plan raw requirements) :
    PlanTemplate operations policy contracts tables world second plan raw requirements := by
  induction template with
  | nil => exact .nil
  | release rest ih =>
      simpa only [plan_context_scope (first := first) (second := second)] using PlanTemplate.release ih
  | retire known rest ih => exact .retire known ih
  | invoke callback rest ih =>
      simpa only [plan_context_scope (first := first) (second := second)] using PlanTemplate.invoke callback ih

inductive Records (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Owners.Contracts)
    (tables : CallableProtectionFrames.Tables) (world : List Nat) : Stack → Store → Prop where
  | nil : Records operations policy contracts tables world .nil []
  | push (rest : Records operations policy contracts tables world tail records) :
      Records operations policy contracts tables world (.push frame tail) records
  | unclosable (blocked : makePlan capture = none)
      (saved : Records operations policy contracts tables world capture nested)
      (rest : Records operations policy contracts tables world tail remaining) :
      Records operations policy contracts tables world (.live owner input answer capture caller tail) (nested ++ remaining)
  | external (outside : ¬ InternalUses capture.erase.liveTickets capture.erase.pending)
      (saved : Records operations policy contracts tables world capture nested)
      (rest : Records operations policy contracts tables world tail remaining) :
      Records operations policy contracts tables world (.live owner input answer capture caller tail) (nested ++ remaining)
  | close (built : makePlan capture = some plan)
      (internal : InternalUses capture.erase.liveTickets capture.erase.pending)
      (template : PlanTemplate operations policy contracts tables world .none plan raw requirements)
      (saved : Records operations policy contracts tables world capture nested)
      (rest : Records operations policy contracts tables world tail remaining) :
      Records operations policy contracts tables world (.live owner input answer capture caller tail)
        ((⟨owner, .dispose⟩, ⟨retirements plan, requirements⟩) :: (nested ++ remaining))
  | spent (rest : Records operations policy contracts tables world tail records) :
      Records operations policy contracts tables world (.spent owner answer caller tail) records

theorem template_world_weaken
    (template : PlanTemplate operations policy contracts tables world scope plan raw requirements)
    (larger : world ⊆ next) : PlanTemplate operations policy contracts tables next scope plan raw requirements := by
  induction template with
  | nil => exact .nil
  | release rest ih => exact .release ih
  | retire known rest ih => exact .retire known ih
  | invoke callback rest ih => exact .invoke (callback.world_weaken larger) ih

/-- Acquisition preserves the existing disposal store, including every dormant
    capture. It creates no new continuation record. -/
theorem records_world_weaken
    (source : Records operations policy contracts tables world stack records)
    (larger : world ⊆ next) : Records operations policy contracts tables next stack records := by
  induction source with
  | nil => exact .nil
  | push rest ih => exact .push ih
  | unclosable blocked saved rest ihSaved ihRest => exact .unclosable blocked ihSaved ihRest
  | external outside saved rest ihSaved ihRest => exact .external outside ihSaved ihRest
  | close built internal template saved rest ihSaved ihRest =>
      exact .close built internal (template_world_weaken template larger) ihSaved ihRest
  | spent rest ih => exact .spent ih

theorem collect (source : Segment operations policy contracts tables world stack input output demand requirements resumes) :
    ∃ records, Records operations policy contracts tables world stack records := by
  induction source with
  | nil => exact ⟨[], .nil⟩
  | push head rest ih => obtain ⟨records, collected⟩ := ih; exact ⟨records, .push collected⟩
  | @live owner contract inputType answerType caller capture body nestedRecords restStack output demand requirements remainingRecords
      known inputAnnotation answerAnnotation scopeKnown held saved rest ihSaved ihRest =>
      obtain ⟨nested, captured⟩ := ihSaved
      obtain ⟨remaining, tail⟩ := ihRest
      cases built : makePlan capture with
      | none => exact ⟨_, .unclosable built captured tail⟩
      | some plan =>
          by_cases accepted : ClosingAdmission.checkInternalUses capture.erase.liveTickets capture.erase.pending = true
          · have internal := ClosingAdmission.check_internal_uses_iff.mp accepted
            obtain ⟨raw, rows⟩ := RecursiveClosing.plan_rows saved built
            obtain ⟨requirements, template⟩ := RecursiveClosing.rows_template (scope := Execution.Scope.none) (tables := tables) rows
            exact ⟨_, .close built internal template captured tail⟩
          · exact ⟨_, .external (fun internal => accepted (ClosingAdmission.check_internal_uses_iff.mpr internal)) captured tail⟩
  | spent known answerAnnotation scopeKnown rest ih => obtain ⟨records, collected⟩ := ih; exact ⟨records, .spent collected⟩

inductive Certified (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Owners.Contracts)
    (tables : CallableProtectionFrames.Tables) (world : List Nat) (root : Stack) : Key → RecursiveRequirements.Template → Prop where
  | dispose (located : CapturedIn owner capture root) (built : makePlan capture = some plan)
      (internal : InternalUses capture.erase.liveTickets capture.erase.pending)
      (template : PlanTemplate operations policy contracts tables world .none plan raw requirements) :
      Certified operations policy contracts tables world root ⟨owner, .dispose⟩ ⟨retirements plan, requirements⟩

theorem certified_transport (source : Certified operations policy contracts tables world first key body)
    (move : ∀ owner capture, CapturedIn owner capture first → CapturedIn owner capture second) :
    Certified operations policy contracts tables world second key body := by
  cases source with
  | dispose located built internal template => exact .dispose (move _ _ located) built internal template

theorem records_certified (source : Records operations policy contracts tables world stack records)
    (member : (key, body) ∈ records) : Certified operations policy contracts tables world stack key body := by
  induction source with
  | nil => cases member
  | push rest ih => exact certified_transport (ih member) (fun _ _ located => .push located)
  | unclosable blocked saved rest ihSaved ihRest =>
      rcases List.mem_append.mp member with nested | remaining
      · exact certified_transport (ihSaved nested) (fun _ _ located => .saved located)
      · exact certified_transport (ihRest remaining) (fun _ _ located => .tail located)
  | external blocked saved rest ihSaved ihRest =>
      rcases List.mem_append.mp member with nested | remaining
      · exact certified_transport (ihSaved nested) (fun _ _ located => .saved located)
      · exact certified_transport (ihRest remaining) (fun _ _ located => .tail located)
  | close built internal template saved rest ihSaved ihRest =>
      rcases List.mem_cons.mp member with same | later
      · cases same; exact .dispose .here built internal template
      · rcases List.mem_append.mp later with nested | remaining
        · exact certified_transport (ihSaved nested) (fun _ _ located => .saved located)
        · exact certified_transport (ihRest remaining) (fun _ _ located => .tail located)
  | spent rest ih => exact certified_transport (ih member) (fun _ _ located => .spent located)

theorem owners_sublist (source : Records operations policy contracts tables world stack records) :
    (RecursiveTransport.recordOwners records).Sublist (ownedTickets stack) := by
  induction source with
  | nil => exact .slnil
  | @push tail records frame rest ih => cases frame <;> first | exact ih | exact .cons _ ih
  | unclosable blocked saved rest ihSaved ihRest =>
      simpa only [RecursiveTransport.recordOwners, List.map_append, ownedTickets] using List.Sublist.cons _ (ihSaved.append ihRest)
  | external blocked saved rest ihSaved ihRest =>
      simpa only [RecursiveTransport.recordOwners, List.map_append, ownedTickets] using List.Sublist.cons _ (ihSaved.append ihRest)
  | close built internal template saved rest ihSaved ihRest =>
      simpa only [RecursiveTransport.recordOwners, List.map_cons, List.map_append, ownedTickets] using
        List.Sublist.cons_cons _ (ihSaved.append ihRest)
  | spent rest ih => exact ih

theorem record_mode (source : Records operations policy contracts tables world stack records)
    (member : (key, body) ∈ records) : key.mode = .dispose := by
  cases records_certified source member
  rfl

theorem resume_mode (source : Segment operations policy contracts tables world stack input output demand requirements records)
    (member : (key, body) ∈ records) : key.mode = .resume := by
  cases SourceTemplates.records_certified source member
  rfl

theorem combined_unique
    (source : Segment operations policy contracts tables world stack input output demand requirements resumes)
    (closing : Records operations policy contracts tables world stack disposals)
    (unique : (ownedTickets stack).Nodup) :
    (RecursiveTransport.recordKeys (resumes ++ disposals)).Nodup := by
  have first := RecursiveTransport.source_records_unique source unique
  have second := RecursiveTransport.record_keys_unique ((owners_sublist closing).nodup unique)
  simp only [RecursiveTransport.recordKeys, List.map_append]
  refine List.nodup_append.mpr ⟨first, second, ?_⟩
  intro key left other right same
  obtain ⟨⟨leftKey, leftBody⟩, leftMember, leftSame⟩ := List.mem_map.mp left
  obtain ⟨⟨rightKey, rightBody⟩, rightMember, rightSame⟩ := List.mem_map.mp right
  have modes := congrArg Key.mode (leftSame.trans (same.trans rightSame.symm))
  rw [resume_mode source leftMember, record_mode closing rightMember] at modes
  cases modes

theorem records_append (first : Records operations policy contracts tables world front a)
    (second : Records operations policy contracts tables world tail b) :
    Records operations policy contracts tables world (front.append tail) (a ++ b) := by
  induction first with
  | nil => exact second
  | push rest ih => exact .push ih
  | unclosable blocked saved rest ihSaved ihRest =>
      simpa only [Stack.append, List.append_assoc] using Records.unclosable blocked saved ihRest
  | external blocked saved rest ihSaved ihRest =>
      simpa only [Stack.append, List.append_assoc] using Records.external blocked saved ihRest
  | close built internal template saved rest ihSaved ihRest =>
      simpa only [Stack.append, List.cons_append, List.append_assoc] using Records.close built internal template saved ihRest
  | spent rest ih => exact .spent ih

theorem template_extension (template : PlanTemplate operations policy contracts tables world scope plan raw requirements)
    (extension : contracts.Extends larger) : PlanTemplate operations policy larger tables world scope plan raw requirements := by
  induction template with
  | nil => exact .nil
  | release rest ih => exact .release ih
  | retire known rest ih => exact .retire (extension _ _ known) ih
  | invoke callback rest ih => exact .invoke (callback.extension extension) ih

theorem records_extension (source : Records operations policy contracts tables world stack records)
    (extension : contracts.Extends larger) : Records operations policy larger tables world stack records := by
  induction source with
  | nil => exact .nil
  | push rest ih => exact .push ih
  | unclosable blocked saved rest ihSaved ihRest => exact .unclosable blocked ihSaved ihRest
  | external blocked saved rest ihSaved ihRest => exact .external blocked ihSaved ihRest
  | close built internal template saved rest ihSaved ihRest => exact .close built internal (template_extension template extension) ihSaved ihRest
  | spent rest ih => exact .spent ih

theorem split_append (source : Records operations policy contracts tables world (front.append tail) records) :
    ∃ a b, Records operations policy contracts tables world front a ∧
      Records operations policy contracts tables world tail b ∧ records = a ++ b := by
  induction front generalizing records with
  | nil => exact ⟨[], records, .nil, source, rfl⟩
  | push frame front ih => cases source with
      | push rest =>
          obtain ⟨a, b, first, second, same⟩ := ih rest
          exact ⟨a, b, .push first, second, same⟩
  | live owner input answer saved caller front ihSaved ihFront => cases source with
      | unclosable blocked nested rest =>
          obtain ⟨a, b, first, second, same⟩ := ihFront rest
          exact ⟨_, b, .unclosable blocked nested first, second, by simp only [same, List.append_assoc]⟩
      | external blocked nested rest =>
          obtain ⟨a, b, first, second, same⟩ := ihFront rest
          exact ⟨_, b, .external blocked nested first, second, by simp only [same, List.append_assoc]⟩
      | close built internal template nested rest =>
          obtain ⟨a, b, first, second, same⟩ := ihFront rest
          exact ⟨_, b, .close built internal template nested first, second, by simp only [same, List.cons_append, List.append_assoc]⟩
  | spent owner answer caller front ih => cases source with
      | spent rest =>
          obtain ⟨a, b, first, second, same⟩ := ih rest
          exact ⟨a, b, .spent first, second, same⟩

/-- Insert a chosen closing template before the fresh continuation contract
    is allocated. Existing nested and caller records are retained exactly. -/
theorem capture_records_with_template
    (cut : HandlerCut requested whole capture tail handler)
    (closing : Records operations policy contracts tables world whole records)
    (built : makePlan capture = some plan)
    (internal : InternalUses capture.erase.liveTickets capture.erase.pending)
    (template : PlanTemplate operations policy contracts tables world .none plan raw requirements) :
    Records operations policy contracts tables world
      (.live owner input answer capture caller tail)
      ((⟨owner, .dispose⟩, ⟨retirements plan, requirements⟩) :: records) := by
  obtain ⟨a, b, first, second, same⟩ := split_append (handler_cut_reconstructs cut ▸ closing)
  rw [same]
  exact .close built internal template first second

theorem capture_records
    (cut : HandlerCut requested whole capture tail handler)
    (source : Segment operations policy contracts tables world whole input output demand requirements resumes)
    (closing : Records operations policy contracts tables world whole records)
    (extension : contracts.Extends larger) :
    ∃ added, Records operations policy larger tables world
      (.live owner inputType answerType capture caller tail) (added ++ records) ∧
      ∀ key body, (key, body) ∈ added → key.owner = owner ∧ key.mode = .dispose := by
  obtain ⟨answer, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords,
    annotation, saved, outside, sameDemand, sameRecords, evaluation⟩ := RecursiveCapture.capture_segments cut source
  obtain ⟨a, b, first, second, same⟩ := split_append (handler_cut_reconstructs cut ▸ closing)
  have captured := records_extension first extension
  have remaining := records_extension second extension
  rw [same]
  cases built : makePlan capture with
  | none => exact ⟨[], by simpa only [List.nil_append] using Records.unclosable built captured remaining, by simp⟩
  | some plan =>
      by_cases accepted : ClosingAdmission.checkInternalUses capture.erase.liveTickets capture.erase.pending = true
      · have internal := ClosingAdmission.check_internal_uses_iff.mp accepted
        obtain ⟨raw, rows⟩ := RecursiveClosing.plan_rows (SourceTemplates.segment_extension saved extension) built
        obtain ⟨requirements, template⟩ := RecursiveClosing.rows_template (scope := Execution.Scope.none) (tables := tables) rows
        refine ⟨[(⟨owner, .dispose⟩, ⟨retirements plan, requirements⟩)], ?_, ?_⟩
        · simpa only [List.cons_append, List.nil_append] using Records.close (owner := owner)
            (input := inputType) (answer := answerType) (caller := caller) built internal template captured remaining
        · intro key body member
          have same := List.mem_singleton.mp member
          cases same
          exact ⟨rfl, rfl⟩
      · have omitted := Records.external (owner := owner) (input := inputType) (answer := answerType) (caller := caller)
          (fun internal => accepted (ClosingAdmission.check_internal_uses_iff.mpr internal)) captured remaining
        exact ⟨[], by simpa only [List.nil_append] using omitted, by simp⟩


theorem move_prefix {prefixRecords selected captured remaining old : Store}
    (permutation : old.Perm (selected ++ captured ++ remaining)) :
    (prefixRecords ++ old).Perm (selected ++ captured ++ (prefixRecords ++ remaining)) := by
  have joined := permutation.append_left prefixRecords
  have moved := (List.perm_append_comm (l₁ := prefixRecords) (l₂ := selected ++ captured)).append_right remaining
  exact joined.trans (by simpa only [List.append_assoc] using moved)

theorem split_live {front capture tail : Stack}
    (source : Records operations policy contracts tables world
      (front.append (.live owner input answer capture caller tail)) records) :
    ∃ selected captured waiting,
      Records operations policy contracts tables world capture captured ∧
      Records operations policy contracts tables world (front.append (.spent owner answer caller tail)) waiting ∧
      records.Perm (selected ++ captured ++ waiting) ∧
      ∀ key body, (key, body) ∈ selected → key.owner = owner := by
  induction front generalizing records with
  | nil => cases source with
      | unclosable blocked saved rest => exact ⟨[], _, _, saved, .spent rest, .refl _, by simp⟩
      | external blocked saved rest => exact ⟨[], _, _, saved, .spent rest, .refl _, by simp⟩
      | close built internal template saved rest =>
          refine ⟨[(_, _)], _, _, saved, .spent rest, .refl _, ?_⟩
          intro key body member
          have same := List.mem_singleton.mp member
          cases same
          rfl
  | push frame front ih => cases source with
      | push rest =>
          obtain ⟨selected, captured, waiting, saved, callerSource, permutation, names⟩ := ih rest
          exact ⟨selected, captured, waiting, saved, .push callerSource, permutation, names⟩
  | live other otherInput otherAnswer savedFront savedCaller front ihSaved ihFront => cases source with
      | unclosable blocked nested rest =>
          obtain ⟨selected, captured, waiting, saved, callerSource, permutation, names⟩ := ihFront rest
          exact ⟨selected, captured, _, saved, .unclosable blocked nested callerSource, move_prefix permutation, names⟩
      | external blocked nested rest =>
          obtain ⟨selected, captured, waiting, saved, callerSource, permutation, names⟩ := ihFront rest
          exact ⟨selected, captured, _, saved, .external blocked nested callerSource, move_prefix permutation, names⟩
      | close built internal template nested rest =>
          obtain ⟨selected, captured, waiting, saved, callerSource, permutation, names⟩ := ihFront rest
          refine ⟨selected, captured, _, saved, .close built internal template nested callerSource, ?_, names⟩
          simpa only [List.cons_append] using move_prefix
            (prefixRecords := (_, _) :: _) permutation
  | spent other otherAnswer savedCaller front ih => cases source with
      | spent rest =>
          obtain ⟨selected, captured, waiting, saved, callerSource, permutation, names⟩ := ih rest
          exact ⟨selected, captured, waiting, saved, .spent callerSource, permutation, names⟩

theorem remove_selected (names : ∀ key body, (key, body) ∈ records → key.owner = owner) :
    RecursiveTransport.removeOwner owner records = [] := by
  induction records with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨key, body⟩ := entry
      simp only [RecursiveTransport.removeOwner, names key body List.mem_cons_self, if_true]
      exact ih (fun key body member => names key body (List.mem_cons_of_mem _ member))

theorem resume_records {front capture tail : Stack}
    (source : Records operations policy contracts tables world
      (front.append (.live owner input answer capture caller tail)) records)
    (unique : (ownedTickets (front.append (.live owner input answer capture caller tail))).Nodup) :
    ∃ nextRecords, Records operations policy contracts tables world
      (capture.append (front.append (.spent owner answer caller tail))) nextRecords ∧
      (RecursiveTransport.removeOwner owner records).Perm nextRecords := by
  obtain ⟨selected, captured, waiting, saved, callerSource, permutation, names⟩ := split_live source
  have combined := records_append saved callerSource
  have absent := (List.nodup_cons.mp (OwnerPhaseTransitions.resume_owned_permutation.nodup unique)).1
  have recordAbsent : owner ∉ RecursiveTransport.recordOwners (captured ++ waiting) :=
    fun member => absent ((owners_sublist combined).subset member)
  have removed := RecursiveRecomposition.remove_owner_permutation (owner := owner) permutation
  have same : RecursiveTransport.removeOwner owner (selected ++ captured ++ waiting) = captured ++ waiting := by
    rw [List.append_assoc, RecursiveRecomposition.remove_owner_filter, List.filter_append,
      ← RecursiveRecomposition.remove_owner_filter, ← RecursiveRecomposition.remove_owner_filter,
      remove_selected names, RecursiveRecomposition.remove_owner_absent recordAbsent, List.nil_append]
  exact ⟨_, combined, same ▸ removed⟩

theorem lookup_certified
    (source : Segment operations policy contracts tables world stack input output demand requirements resumes)
    (closing : Records operations policy contracts tables world stack disposals)
    (known : RecursiveRequirements.lookup ⟨owner, .dispose⟩ (resumes ++ disposals) = some body) :
    Certified operations policy contracts tables world stack ⟨owner, .dispose⟩ body := by
  rcases List.mem_append.mp (SourceTemplates.lookup_member known) with original | added
  · have impossible := resume_mode source original
    cases impossible
  · exact records_certified closing added

theorem certified_selected (certificate : Certified operations policy contracts tables world stack key body)
    (unique : (ownedTickets stack).Nodup) (selected : SourceTemplates.ActiveCapture key.owner capture stack) :
    ∃ (plan : List CloseEntry) (raw : Footprint) (requirements : Requirements (retirements plan)),
      makePlan capture = some plan ∧ InternalUses capture.erase.liveTickets capture.erase.pending ∧ body = ⟨retirements plan, requirements⟩ ∧
      PlanTemplate operations policy contracts tables world .none plan raw requirements := by
  cases certificate with
  | dispose located built internal template =>
      have same := SourceTemplates.captured_in_unique unique located (SourceTemplates.active_capture_located selected)
      cases same
      exact ⟨_, _, _, built, internal, rfl, template⟩

/-- The checked disposal uses the actual active capture and its actual plan,
    including the structural abandoned-use check. Preservation of the complete
    successor and the combined usage invariant remain separate. -/
theorem checked_discard_step
    (source : Segment operations policy contracts tables world stack input output pendingDemand pending resumes)
    (closing : Records operations policy contracts tables world stack disposals)
    (unique : (ownedTickets stack).Nodup)
    (checked : Checked (resumes ++ disposals) (OwnerPhases.ofStack tables stack) before
      (.invoke ⟨owner, .dispose⟩ demand []) row)
    (resolved : scope.resolve binder = some owner) (identity : Nat) :
    ∃ (capture front : Stack) (inputType answerType : Ty) (caller : Execution.Scope) (tail : Stack)
      (plan : List CloseEntry) (raw : Footprint) (requirements : Requirements (retirements plan)),
      stack = front.append (.live owner inputType answerType capture caller tail) ∧
      makePlan capture = some plan ∧ InternalUses capture.erase.liveTickets capture.erase.pending ∧ demand = retirements plan ∧
      PlanTemplate operations policy contracts tables world .none plan raw requirements ∧
      Checked (resumes ++ disposals) (OwnerPhases.ofStack tables stack) (spend before owner) requirements row ∧
      RawStep ⟨.discard binder, scope, stack⟩
        ⟨.unit, scope, (closeControl scope plan).append (.push (.closing identity scope)
          (front.append (.spent owner answerType caller tail)))⟩ [.close identity] [.ticket owner] := by
  obtain ⟨body, waiting, known, ready, selection, bodyChecked⟩ := RecursiveRequirements.checked_invocation checked
  obtain ⟨capture, active⟩ := SourceTemplates.consume_active_capture (OwnerPhases.consumes_sound selection)
  obtain ⟨plan, raw, requirements, built, internal, sameTemplate, template⟩ :=
    certified_selected (lookup_certified source closing known) unique active
  have sameDemand := congrArg Sigma.fst sameTemplate
  change demand = retirements plan at sameDemand
  have sameBody := (Sigma.mk.inj sameTemplate).2
  subst demand
  cases eq_of_heq sameBody
  obtain ⟨front, inputType, answerType, caller, tail, sameStack⟩ := SourceTemplates.active_capture_decompose active
  refine ⟨capture, front, inputType, answerType, caller, tail, plan, raw, requirements,
    sameStack, built, internal, rfl, template, bodyChecked, ?_⟩
  rw [sameStack]
  exact .discard binder owner identity scope caller inputType answerType front capture tail plan resolved built

theorem lookup_append (known : RecursiveRequirements.lookup key first = some body) :
    RecursiveRequirements.lookup key (first ++ second) = some body := by
  induction first with
  | nil => cases known
  | cons entry rest ih =>
      obtain ⟨candidate, value⟩ := entry
      by_cases same : key = candidate
      · simpa only [RecursiveRequirements.lookup, same, if_true, List.cons_append] using known
      · simp only [RecursiveRequirements.lookup, same, if_false] at known
        simpa only [RecursiveRequirements.lookup, same, if_false, List.cons_append] using ih known

theorem checked_extension (checked : Checked store receiving before requirements row)
    (extension : ∀ key body, RecursiveRequirements.lookup key store = some body →
      RecursiveRequirements.lookup key larger = some body) :
    Checked larger receiving before requirements row := by
  induction checked with
  | request exported => exact .request exported
  | retire ready => exact .retire ready
  | spent consumed => exact .spent consumed
  | invoke known ready selection next ih => exact .invoke (extension _ _ known) ready selection ih
  | sequence first second ihFirst ihSecond => exact .sequence ihFirst ihSecond
  | emitAfter body exported ih => exact .emitAfter ih exported
  | choice first second ihFirst ihSecond => exact .choice ihFirst ihSecond

/-- The existing structural expression and segment judgments supply resume
    records; the actual captures additionally supply closing records. -/
inductive CheckedState (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Owners.Contracts)
    (tables : CallableProtectionFrames.Tables) (world : List Nat) (outside : ProtectionContracts.Context)
    (scope : Execution.Scope) (code : Code) (stack : Stack) (output : Value) (demand : List Nat) (row : Footprint) : Prop where
  | checked (source : SourceTemplates.Configuration operations policy contracts tables world scope code stack output demand requirements resumes)
      (closing : Records operations policy contracts tables world stack disposals)
      (unique : (ownedTickets stack).Nodup)
      (evaluated : Checked (resumes ++ disposals) [] (available (ownedTickets stack)) requirements row)
      (accepted : checkFootprint outside row = true) :
      CheckedState operations policy contracts tables world outside scope code stack output demand row

/-- The same recursive evaluation and ownership proof apply after extending the
    resource world; only source and callback typing need transport. -/
theorem checked_state_world_weaken
    (source : CheckedState operations policy contracts tables world outside scope code stack output demand row)
    (larger : world ⊆ next) :
    CheckedState operations policy contracts tables next outside scope code stack output demand row := by
  cases source with
  | checked source closing unique evaluated accepted =>
      exact .checked (SourceTemplates.configuration_world_weaken source larger)
        (records_world_weaken closing larger) unique evaluated accepted

theorem existing_state (source : SourceTemplates.CheckedConfiguration operations policy contracts tables world outside scope code stack output demand row) :
    CheckedState operations policy contracts tables world outside scope code stack output demand row := by
  cases source with
  | checked source unique evaluated accepted =>
      have closings : ∃ records, Records operations policy contracts tables world stack records := by
        cases source with
        | checked current scopeTyped pending => exact collect pending
      obtain ⟨records, closing⟩ := closings
      exact .checked source closing unique (checked_extension evaluated (fun _ _ known => lookup_append known)) accepted

theorem discard_progress
    (source : CheckedState operations policy contracts tables world outside scope (.discard binder) stack output demand row)
    (identity : Nat) :
    ∃ next owner, RawStep ⟨.discard binder, scope, stack⟩ next [.close identity] [.ticket owner] := by
  cases source with
  | checked source closing unique evaluated accepted => cases source with
      | checked current scopeTyped pending => cases current with
          | stable summary => cases summary
          | callable summary => cases summary
          | discard known resolved permission unprotected admitted =>
              obtain ⟨currentRow, pendingRow, currentCheck, pendingCheck, same⟩ := RecursiveRequirements.checked_sequence_parts evaluated
              have invocation := RecursiveRequirements.checked_prepend_iff.mp currentCheck
              simp only [List.append_nil] at invocation
              obtain ⟨capture, front, inputType, answerType, caller, tail, plan, raw, requirements,
                sameStack, built, internal, sameDemand, template, bodyCheck, step⟩ :=
                checked_discard_step pending closing unique invocation resolved identity
              exact ⟨_, _, step⟩

theorem located_below (front : Stack) (located : CapturedIn owner capture tail) :
    CapturedIn owner capture (front.append tail) := by
  induction front with
  | nil => exact located
  | push frame rest ih => exact .push ih
  | live other input answer saved caller rest ihSaved ihRest => exact .tail ihRest
  | spent other answer caller rest ih => exact .spent ih

theorem certified_internal (certificate : Certified operations policy contracts tables world stack key body)
    (unique : (ownedTickets stack).Nodup) (located : CapturedIn key.owner capture stack) :
    InternalUses capture.erase.liveTickets capture.erase.pending := by
  cases certificate with
  | dispose saved built internal template =>
      exact SourceTemplates.captured_in_unique unique saved located ▸ internal

/-- Every actual raw disposal cut obtains the abandoned-use condition from
    the checked state. The cut need not be the one constructed by progress. -/
theorem discard_internal {front capture tail : Stack}
    (source : CheckedState operations policy contracts tables world outside scope (.discard binder)
      (front.append (.live owner input answer capture caller tail)) output demand row)
    (resolved : scope.resolve binder = some owner) :
    InternalUses capture.erase.liveTickets capture.erase.pending := by
  cases source with
  | checked source closing unique evaluated accepted => cases source with
      | checked current scopeTyped pending => cases current with
          | stable summary => cases summary
          | callable summary => cases summary
          | discard known actualResolved permission unprotected admitted =>
              have sameOwner := Option.some.inj (actualResolved.symm.trans resolved)
              subst_vars
              obtain ⟨currentRow, pendingRow, currentCheck, pendingCheck, same⟩ := RecursiveRequirements.checked_sequence_parts evaluated
              have invocation := RecursiveRequirements.checked_prepend_iff.mp currentCheck
              simp only [List.append_nil] at invocation
              obtain ⟨body, waiting, looked, ready, selection, bodyCheck⟩ := RecursiveRequirements.checked_invocation invocation
              exact certified_internal (lookup_certified pending closing looked) unique (located_below front .here)

namespace Examples

def operations : Operations := fun _ _ => none
def policy : Syntax.TicketPolicy := fun _ => ⟨true, true⟩
def tables : CallableProtectionFrames.Tables := fun _ => []
def inner : Owners.Contract := ⟨.unit, .unit, false, [], [], [], some [], [], []⟩
def outer : Owners.Contract := { inner with closeDemand := [19] }
def contracts : Owners.Contracts := fun owner => if owner = 19 then some inner else if owner = 23 then some outer else none

theorem inner_known : contracts 19 = some inner := rfl
theorem outer_known : contracts 23 = some outer := rfl

def emptyRequirements : Requirements [] := .request [] []
def innerRequirements : Requirements [] := .sequence (.spent 19) emptyRequirements
def outerRequirements : Requirements [] := .sequence (.spent 23) emptyRequirements
def closingRequirements : Requirements [19] := .sequence (.retire 19) emptyRequirements
def capture : Stack := .live 19 .unit .unit .nil .none .nil
def stack : Stack := .live 23 .unit .unit capture .none .nil
def innerResumes : Store := [(⟨19, .resume⟩, ⟨[], emptyRequirements⟩)]
def innerDisposals : Store := [(⟨19, .dispose⟩, ⟨[], emptyRequirements⟩)]
def resumes : Store := (⟨23, .resume⟩, ⟨[], innerRequirements⟩) :: innerResumes
def disposals : Store := (⟨23, .dispose⟩, ⟨[19], closingRequirements⟩) :: innerDisposals

theorem inner_source : Segment operations policy contracts tables [] capture .unit .unit [] innerRequirements innerResumes :=
  .live inner_known rfl rfl ⟨.none, .none⟩ rfl .nil .nil

theorem outer_source : Segment operations policy contracts tables [] stack .unit .unit [] outerRequirements resumes :=
  .live outer_known rfl rfl ⟨.none, .none⟩ rfl inner_source .nil

theorem inner_closing : Records operations policy contracts tables [] capture innerDisposals :=
  .close rfl .nil .nil .nil .nil

theorem outer_closing : Records operations policy contracts tables [] stack disposals :=
  .close rfl .nil (.retire inner_known .nil) inner_closing .nil

theorem distinct_modes : (RecursiveTransport.recordKeys (resumes ++ disposals)).Nodup :=
  combined_unique outer_source outer_closing (by decide)

theorem inner_resume_checked : Checked (innerResumes ++ innerDisposals) (OwnerPhases.ofStack tables capture)
    (available [19]) (.invoke ⟨19, .resume⟩ [] []) [] := by
  apply Checked.invoke (body := emptyRequirements) rfl (by decide)
    (by exact OwnerPhases.Consumes.hit)
  apply Checked.request
  simp [OwnerSource.exportAt, residual_empty]

theorem inner_dispose_checked : Checked (innerResumes ++ innerDisposals) (OwnerPhases.ofStack tables capture)
    (available [19]) (.invoke ⟨19, .dispose⟩ [] []) [] := by
  apply Checked.invoke (body := emptyRequirements) rfl (by decide)
    (by exact OwnerPhases.Consumes.hit)
  apply Checked.request
  simp [OwnerSource.exportAt, residual_empty]

theorem outer_checked : Checked (resumes ++ disposals) (OwnerPhases.ofStack tables stack)
    (available [23, 19]) (.invoke ⟨23, .dispose⟩ [19] []) [] := by
  apply Checked.invoke (body := closingRequirements) rfl (by decide)
    (by exact OwnerPhases.Consumes.hit)
  exact Checked.sequence (.retire (by decide)) (.request (by simp [OwnerSource.exportAt, residual_empty]))

theorem incorrect_demand_rejected : ¬ Checked (resumes ++ disposals) (OwnerPhases.ofStack tables stack)
    (available [23, 19]) (.invoke ⟨23, .dispose⟩ [] []) row := by
  intro checked
  obtain ⟨body, waiting, known, ready, selection, bodyCheck⟩ := RecursiveRequirements.checked_invocation checked
  have actual : RecursiveRequirements.lookup ⟨23, .dispose⟩ (resumes ++ disposals) = some ⟨[19], closingRequirements⟩ := rfl
  have impossible := congrArg Sigma.fst (Option.some.inj (known.symm.trans actual))
  cases impossible

theorem admitted_discard : CheckedState operations policy contracts tables [] [] (.ticket 0 23) (.discard 0) stack .unit [23, 19] [] := by
  have expression : SourceTemplates.Expression operations policy contracts [] [] (.ticket 0 23) Environment.empty
      (.discard 0) .unit [23, 19] (.invoke ⟨23, .dispose⟩ [19] []) :=
    .discard outer_known rfl rfl rfl (by simp [outer, inner])
  have current : Checked (resumes ++ disposals) [] (available (ownedTickets stack))
      ((Requirements.invoke ⟨23, .dispose⟩ [19] []).prepend (OwnerPhases.ofStack tables stack)) [] :=
    RecursiveRequirements.checked_prepend_iff.mpr (by simpa only [List.append_nil, stack, capture, ownedTickets] using outer_checked)
  have pending : Checked (resumes ++ disposals) [] (spendAll (available (ownedTickets stack)) [23, 19]) outerRequirements [] :=
    Checked.sequence (.spent (by decide)) (.request (by simp [OwnerSource.exportAt, residual_empty]))
  exact .checked (.checked (currentDemand := [23, 19]) (pendingDemand := []) expression (.bound (Owners.ports_lookup outer_known)) outer_source)
    outer_closing (by decide) (Checked.sequence current pending) (by decide)

theorem disposal_progress : ∃ next owner,
    RawStep ⟨.discard 0, .ticket 0 23, stack⟩ next [.close 41] [.ticket owner] :=
  discard_progress admitted_discard 41

theorem nested_records_survive_resume : ∃ nextRecords,
    Records operations policy contracts tables [] (capture.append (.spent 23 .unit .none .nil)) nextRecords ∧
      (RecursiveTransport.removeOwner 23 disposals).Perm nextRecords :=
  resume_records (front := .nil) outer_closing (by decide)

theorem admitted_discard_internal : InternalUses capture.erase.liveTickets capture.erase.pending :=
  discard_internal (front := .nil) admitted_discard rfl

def outsideCapture : Stack := .push (.plain (ControlUsageExamples.waiting 0 29)) .nil

theorem outside_plan_exists : makePlan outsideCapture = some [] := rfl

theorem outside_use_rejected : ¬ InternalUses outsideCapture.erase.liveTickets outsideCapture.erase.pending := by
  intro internal
  have checked := ClosingAdmission.check_internal_uses_iff.mpr internal
  have rejected : ClosingAdmission.checkInternalUses outsideCapture.erase.liveTickets outsideCapture.erase.pending = false := by decide
  rw [rejected] at checked
  cases checked

theorem outside_disposal_omitted : Records operations policy contracts tables []
    (.live 19 .unit .unit outsideCapture .none .nil) [] :=
  .external outside_use_rejected (.push .nil) .nil

end Examples

end Ash.OneShot.RecursiveRecords

#print axioms Ash.OneShot.RecursiveRecords.plan_context_scope
#print axioms Ash.OneShot.RecursiveRecords.template_scope
#print axioms Ash.OneShot.RecursiveRecords.collect
#print axioms Ash.OneShot.RecursiveRecords.certified_transport
#print axioms Ash.OneShot.RecursiveRecords.records_certified
#print axioms Ash.OneShot.RecursiveRecords.owners_sublist
#print axioms Ash.OneShot.RecursiveRecords.record_mode
#print axioms Ash.OneShot.RecursiveRecords.resume_mode
#print axioms Ash.OneShot.RecursiveRecords.combined_unique
#print axioms Ash.OneShot.RecursiveRecords.records_append
#print axioms Ash.OneShot.RecursiveRecords.template_extension
#print axioms Ash.OneShot.RecursiveRecords.records_extension
#print axioms Ash.OneShot.RecursiveRecords.split_append
#print axioms Ash.OneShot.RecursiveRecords.capture_records
#print axioms Ash.OneShot.RecursiveRecords.move_prefix
#print axioms Ash.OneShot.RecursiveRecords.split_live
#print axioms Ash.OneShot.RecursiveRecords.remove_selected
#print axioms Ash.OneShot.RecursiveRecords.resume_records
#print axioms Ash.OneShot.RecursiveRecords.lookup_certified
#print axioms Ash.OneShot.RecursiveRecords.certified_selected
#print axioms Ash.OneShot.RecursiveRecords.checked_discard_step
#print axioms Ash.OneShot.RecursiveRecords.lookup_append
#print axioms Ash.OneShot.RecursiveRecords.checked_extension
#print axioms Ash.OneShot.RecursiveRecords.existing_state
#print axioms Ash.OneShot.RecursiveRecords.discard_progress
#print axioms Ash.OneShot.RecursiveRecords.located_below
#print axioms Ash.OneShot.RecursiveRecords.certified_internal
#print axioms Ash.OneShot.RecursiveRecords.discard_internal
#print axioms Ash.OneShot.RecursiveRecords.Examples.inner_known
#print axioms Ash.OneShot.RecursiveRecords.Examples.outer_known
#print axioms Ash.OneShot.RecursiveRecords.Examples.inner_source
#print axioms Ash.OneShot.RecursiveRecords.Examples.outer_source
#print axioms Ash.OneShot.RecursiveRecords.Examples.inner_closing
#print axioms Ash.OneShot.RecursiveRecords.Examples.outer_closing
#print axioms Ash.OneShot.RecursiveRecords.Examples.distinct_modes
#print axioms Ash.OneShot.RecursiveRecords.Examples.inner_resume_checked
#print axioms Ash.OneShot.RecursiveRecords.Examples.inner_dispose_checked
#print axioms Ash.OneShot.RecursiveRecords.Examples.outer_checked
#print axioms Ash.OneShot.RecursiveRecords.Examples.incorrect_demand_rejected
#print axioms Ash.OneShot.RecursiveRecords.Examples.admitted_discard
#print axioms Ash.OneShot.RecursiveRecords.Examples.disposal_progress
#print axioms Ash.OneShot.RecursiveRecords.Examples.nested_records_survive_resume
#print axioms Ash.OneShot.RecursiveRecords.Examples.admitted_discard_internal
#print axioms Ash.OneShot.RecursiveRecords.Examples.outside_plan_exists
#print axioms Ash.OneShot.RecursiveRecords.Examples.outside_use_rejected
#print axioms Ash.OneShot.RecursiveRecords.Examples.outside_disposal_omitted

#print axioms Ash.OneShot.RecursiveRecords.template_world_weaken
#print axioms Ash.OneShot.RecursiveRecords.records_world_weaken
#print axioms Ash.OneShot.RecursiveRecords.checked_state_world_weaken

#print axioms Ash.OneShot.RecursiveRecords.capture_records_with_template
