import DeclaredSourceClosing
import ProtectedClosingRows

/-! Recover effect budgets from the continuation records actually consulted by
the existing recursive check. Open derivations retain each invocation's exact
context and phase; source lookup authenticates its chosen closing template.
This does not assume that independently typed templates share annotations. -/
namespace Ash.OneShot.NestedClosingBudgets
open ScopedExpressions ScopedExecution ProtectionContracts CoherentSourceTypes
open RecursiveRequirements (Requirements Checked)
open ContextualClauseChecks (Invocation Derivation)
open OwnerPhaseTransitions (spend)
open RecursiveDisposalCapture (directRetirements)

/-- Successful closing construction excludes existing generated retirement
frames. Source retirement accounting remains the established ownership lemma. -/
theorem plan_no_scheduled (stack : Stack) (built : makePlan stack = some plan) :
    ScopedRetirement.scheduled stack = [] := by
  induction stack generalizing plan with
  | nil => rfl
  | push frame rest ih =>
      cases frame <;> cases next : makePlan rest <;> simp only [makePlan, next] at built
      all_goals first | cases built | skip
      all_goals exact ih next
  | live owner input answer saved scope rest ihSaved ihRest =>
      cases inside : makePlan saved <;> cases outside : makePlan rest <;>
        simp only [makePlan, inside, outside] at built
      all_goals first | cases built | skip
      simp only [ScopedRetirement.scheduled, ihSaved inside, ihRest outside, List.nil_append]
  | spent owner answer scope rest ih => exact ih built

theorem captured_no_retirements
    (source : DeclaredSourceFrames.Segment operations policy contracts tables world capture input output demand requirements records)
    (built : makePlan capture = some plan) :
    RecursiveDisposalCapture.directRetirements requirements = [] := by
  have accounted := RecursiveDisposalCapture.segment_retirements source.erase
  rw [plan_no_scheduled capture built] at accounted
  exact List.eq_nil_iff_forall_not_mem.mpr (fun _ member => List.not_mem_nil (accounted member))

theorem invocation_bound
    (source : Derivation receiving before requirements row calls)
    (member : call ∈ calls) : EffectBounds.Covers row call.row := by
  induction source with
  | request | retire | spent => cases member
  | invoke => cases List.mem_singleton.mp member; exact List.Subset.refl _
  | sequence first second ihFirst ihSecond
  | choice first second ihFirst ihSecond =>
      rcases List.mem_append.mp member with first | second
      · exact (ihFirst first).trans (List.subset_append_left _ _)
      · exact (ihSecond second).trans (List.subset_append_right _ _)
  | emitAfter body exported ih => exact (ih member).trans (List.subset_append_left _ _)

/-- The full invocation demand, including nested owners, belongs to the
enclosing requirement demand. The existing branch permutation is respected. -/
theorem invocation_demand
    (source : Derivation receiving before (owners := owners) requirements row calls)
    (member : call ∈ calls) : (call.key.owner :: call.demand) ⊆ owners := by
  induction source with
  | request | retire | spent => cases member
  | invoke => cases List.mem_singleton.mp member; exact List.Subset.refl _
  | sequence first second ihFirst ihSecond =>
      rcases List.mem_append.mp member with first | second
      · exact (ihFirst first).trans (List.subset_append_left _ _)
      · exact (ihSecond second).trans (List.subset_append_right _ _)
  | emitAfter body exported ih => exact ih member
  | @choice receiving before firstOwners first firstRow firstCalls secondOwners second secondRow secondCalls same left right ihLeft ihRight =>
      rcases List.mem_append.mp member with first | second
      · exact ihLeft first
      · exact fun _ present => same.mem_iff.mpr (ihRight second present)

/-- Recursive proof decomposition decreases the owner demand strictly at an
invocation edge. Existing one-shot uniqueness supplies the finite measure. -/
theorem invocation_body_smaller
    (source : Derivation receiving before (owners := owners) requirements row calls)
    (member : call ∈ calls) (checked : call.Check store) :
    call.demand.length < owners.length := by
  have unique := RecursiveRequirements.checked_once checked
  have bounded := unique.length_le_of_subset (invocation_demand source member)
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) bounded

/-- Choose one alternative at each branch while retaining every sequential
invocation. Their full demands concatenate to the enclosing demand exactly;
both alternatives' effect rows remain included in the enclosing budget. -/
theorem invocation_partition
    (source : Derivation receiving before (owners := owners) requirements row calls)
    (ordinary : directRetirements requirements = []) :
    ∃ selected, selected ⊆ calls ∧
      selected.flatMap (fun call => call.key.owner :: call.demand) = owners := by
  induction source with
  | request | spent => exact ⟨[], List.Subset.refl _, rfl⟩
  | retire => cases ordinary
  | invoke => exact ⟨_, List.Subset.refl _, by simp⟩
  | sequence first second ihFirst ihSecond =>
      simp only [directRetirements, List.append_eq_nil_iff] at ordinary
      obtain ⟨a, firstSubset, firstDemand⟩ := ihFirst ordinary.1
      obtain ⟨b, secondSubset, secondDemand⟩ := ihSecond ordinary.2
      refine ⟨a ++ b, ?_, ?_⟩
      · intro call member
        rcases List.mem_append.mp member with first | second
        · exact List.mem_append_left _ (firstSubset first)
        · exact List.mem_append_right _ (secondSubset second)
      · simp only [List.flatMap_append, firstDemand, secondDemand]
  | emitAfter body exported ih => exact ih ordinary
  | choice first second ihFirst ihSecond =>
      simp only [directRetirements, List.append_eq_nil_iff] at ordinary
      obtain ⟨selected, included, demands⟩ := ihFirst ordinary.1
      exact ⟨selected, included.trans (List.subset_append_left _ _), demands⟩

/-- Every demanded owner belongs to an explicit invocation or its nested
obligations. Reuse the partition instead of a second ownership induction. -/
theorem owner_invocation
    (source : Derivation receiving before (owners := owners) requirements row calls)
    (ordinary : directRetirements requirements = []) (present : owner ∈ owners) :
    ∃ call ∈ calls, owner ∈ call.key.owner :: call.demand := by
  obtain ⟨selected, included, demands⟩ := invocation_partition source ordinary
  rw [← demands] at present
  obtain ⟨call, member, demand⟩ := List.mem_flatMap.mp present
  exact ⟨call, included member, demand⟩

theorem source_owner_invocation
    (source : DeclaredSources.Expression operations policy contracts world allowed scope environment code result demand requirements)
    (opened : Derivation receiving before requirements row calls) (present : owner ∈ demand) :
    ∃ call ∈ calls, owner ∈ call.key.owner :: call.demand :=
  owner_invocation opened
    (RecursiveDisposalCapture.expression_no_retirements (DeclaredSources.expression_erase source)) present

theorem captured_owner_invocation
    (source : DeclaredSourceFrames.Segment operations policy contracts tables world capture input output demand requirements records)
    (built : makePlan capture = some plan)
    (opened : Derivation receiving before requirements row calls) (present : owner ∈ demand) :
    ∃ call ∈ calls, owner ∈ call.key.owner :: call.demand :=
  owner_invocation opened (captured_no_retirements source built) present

/-- A source-derived capture with a closing plan has a finite partition of its
actual checked owner obligations into authenticated invocation demands. The
result does not pretend that merely retaining a live boundary invokes it. -/
theorem captured_invocation_partition
    (source : DeclaredSourceFrames.Segment operations policy contracts tables world capture input output demand requirements records)
    (built : makePlan capture = some plan)
    (checked : Checked store receiving before requirements row) :
    ∃ calls selected,
      Derivation receiving before requirements row calls ∧ selected ⊆ calls ∧
      selected.flatMap (fun call => call.key.owner :: call.demand) = demand ∧
      (selected.flatMap (fun call => call.key.owner :: call.demand)).Nodup ∧
      (∀ call ∈ selected, call.Check store ∧ EffectBounds.Covers row call.row) := by
  obtain ⟨calls, opened, supplied⟩ := ContextualClauseChecks.open_checked checked
  have ordinary := captured_no_retirements source built
  obtain ⟨selected, included, demands⟩ := invocation_partition opened ordinary
  refine ⟨calls, selected, opened, included, demands, demands.symm ▸ RecursiveRequirements.checked_once checked, ?_⟩
  intro call member
  exact ⟨supplied call (included member), invocation_bound opened (included member)⟩

/-- Reuse the established ownership-tree balance theorem to identify the
partition with all owners of the actual captured region, including dormant
captures. Internal uses and entry availability retain their existing roles. -/
theorem captured_owned_partition
    (rootSource : DeclaredSourceFrames.Segment operations policy contracts tables world root input output rootDemand rootRequirements resumes)
    (closing : DeclaredSourceClosing.Records operations policy contracts tables world root disposals)
    (unique : (ownedTickets root).Nodup)
    (located : SourceTemplates.CapturedIn boundary capture root)
    (internal : InternalUses capture.erase.liveTickets capture.erase.pending)
    (saved : DeclaredSourceFrames.Segment operations policy contracts tables world capture argument answer demand requirements records)
    (built : makePlan capture = some plan)
    (checked : Checked (resumes ++ disposals) receiving before requirements row)
    (ready : ∀ owner ∈ ownedTickets capture, before owner = .available) :
    ∃ calls selected,
      Derivation receiving before requirements row calls ∧ selected ⊆ calls ∧
      (selected.flatMap (fun call => call.key.owner :: call.demand)).Perm (ownedTickets capture) ∧
      (selected.flatMap (fun call => call.key.owner :: call.demand)).Nodup ∧
      (∀ call ∈ selected, call.Check (resumes ++ disposals) ∧ EffectBounds.Covers row call.row) := by
  obtain ⟨calls, selected, opened, included, demands, distinct, supplied⟩ :=
    captured_invocation_partition saved built checked
  have balanced := RecursiveDisposalCapture.captured_segment_balance rootSource.erase
    (DeclaredSourceClosing.records_erase closing) unique located internal saved.erase checked ready
  exact ⟨calls, selected, opened, included, demands.symm ▸ balanced, distinct, supplied⟩

/-- Expanding a selected invocation reuses the existing lookup and open-check
lemmas. Every nested call inherits both an owner bound and an effect budget;
its own receiving interpretations and post-consumption phase remain exact. -/
theorem expand_invocation
    (source : Derivation receiving before (owners := owners) requirements row calls)
    (member : call ∈ calls) (checked : call.Check store) :
    ∃ (body : Requirements call.demand), ∃ waiting nested,
      RecursiveRequirements.lookup call.key store = some ⟨call.demand, body⟩ ∧
      OwnerPhases.Consumes call.key.owner call.receiving waiting ∧
      Derivation call.receiving (spend call.before call.key.owner) body call.row nested ∧
      (∀ next ∈ nested, next.Check store ∧ EffectBounds.Covers row next.row ∧
        (next.key.owner :: next.demand) ⊆ owners) := by
  obtain ⟨body, waiting, known, ready, selected, bodyCheck⟩ := RecursiveRequirements.checked_invocation checked
  obtain ⟨nested, opened, supplied⟩ := ContextualClauseChecks.open_checked bodyCheck
  refine ⟨body, waiting, nested, known, by simpa only [List.nil_append] using selected,
    by simpa only [List.nil_append] using opened, ?_⟩
  intro next present
  exact ⟨supplied next present, (invocation_bound opened present).trans (invocation_bound source member),
    (invocation_demand opened present).trans ((List.subset_cons_self _ _).trans (invocation_demand source member))⟩

/-- Lift the existing record-membership induction to the retained hereditary
frame judgment. This preserves the selected template's exact demand and body. -/
theorem resume_member_source
    (source : DeclaredSourceFrames.Segment operations policy contracts tables world stack input output demand requirements records)
    (member : (key, template) ∈ records) :
    ∃ capture, ∃ (contract : Owners.Contract) (body : Requirements contract.resumeDemand), ∃ nested,
      SourceTemplates.CapturedIn key.owner capture stack ∧ contracts key.owner = some contract ∧
      template = ⟨contract.resumeDemand, body⟩ ∧
      DeclaredSourceFrames.Segment operations policy contracts tables world capture contract.input contract.answer
        contract.resumeDemand body nested := by
  induction source with
  | nil => cases member
  | push current head tail ih =>
      obtain ⟨capture, contract, body, nested, located, known, same, saved⟩ := ih member
      exact ⟨capture, contract, body, nested, .push located, known, same, saved⟩
  | live known inputAnnotation answerAnnotation scopeKnown held saved tail ihSaved ihTail =>
      simp only [List.mem_cons, List.mem_append] at member
      rcases member with same | inside | outside
      · cases same; exact ⟨_, _, _, _, .here, known, rfl, saved⟩
      · obtain ⟨capture, contract, body, nested, located, known, same, source⟩ := ihSaved inside
        exact ⟨capture, contract, body, nested, .saved located, known, same, source⟩
      · obtain ⟨capture, contract, body, nested, located, known, same, source⟩ := ihTail outside
        exact ⟨capture, contract, body, nested, .tail located, known, same, source⟩
  | spent known answerAnnotation scopeKnown tail ih =>
      obtain ⟨capture, contract, body, nested, located, known, same, saved⟩ := ih member
      exact ⟨capture, contract, body, nested, .spent located, known, same, saved⟩

theorem selected_resumption
    (stackSource : DeclaredSourceFrames.Segment operations policy contracts tables world stack input output demand pending resumes)
    (closing : DeclaredSourceClosing.Records operations policy contracts tables world stack disposals)
    (source : Derivation receiving before requirements row calls)
    (member : call ∈ calls) (mode : call.key.mode = .resume)
    (checked : call.Check (resumes ++ disposals)) :
    ∃ capture, ∃ (contract : Owners.Contract) (body : Requirements contract.resumeDemand), ∃ nested,
      SourceTemplates.CapturedIn call.key.owner capture stack ∧ contracts call.key.owner = some contract ∧
      DeclaredSourceFrames.Segment operations policy contracts tables world capture contract.input contract.answer
        contract.resumeDemand body nested ∧
      Checked (resumes ++ disposals) call.receiving (spend call.before call.key.owner) body call.row ∧
      EffectBounds.Covers row call.row := by
  rcases call with ⟨⟨owner, callMode⟩, callDemand, callReceiving, callBefore, callRow⟩
  cases mode
  obtain ⟨body, waiting, known, ready, selected, bodyCheck⟩ := RecursiveRequirements.checked_invocation checked
  have inResumes : (⟨owner, .resume⟩, ⟨callDemand, body⟩) ∈ resumes := by
    rcases List.mem_append.mp (SourceTemplates.lookup_member known) with first | second
    · exact first
    · have impossible := RecursiveRecords.record_mode (DeclaredSourceClosing.records_erase closing) second
      cases impossible
  obtain ⟨capture, contract, actual, nested, located, registered, same, saved⟩ := resume_member_source stackSource inResumes
  cases same
  exact ⟨capture, contract, actual, nested, located, registered, saved,
    by simpa only [List.nil_append] using bodyCheck, invocation_bound source member⟩

/-- A selected disposal supplies the hereditary template from the actual
stored record, together with its checked row inside the enclosing budget.
No template is reconstructed with independently chosen callback annotations. -/
theorem selected_disposal
    (stackSource : DeclaredSourceFrames.Segment operations policy contracts tables world stack input output demand pending resumes)
    (closing : DeclaredSourceClosing.Records operations policy contracts tables world stack disposals)
    (source : Derivation receiving before requirements row calls)
    (member : call ∈ calls) (mode : call.key.mode = .dispose)
    (checked : call.Check (resumes ++ disposals)) :
    ∃ capture plan raw, ∃ (body : Requirements (OwnerClosingSource.retirements plan)),
      SourceTemplates.CapturedIn call.key.owner capture stack ∧
      makePlan capture = some plan ∧
      InternalUses capture.erase.liveTickets capture.erase.pending ∧
      DeclaredSourceClosing.PlanTemplate operations policy contracts tables world .none plan raw body ∧
      Checked (resumes ++ disposals) call.receiving (spend call.before call.key.owner) body call.row ∧
      EffectBounds.Covers row call.row := by
  rcases call with ⟨⟨owner, callMode⟩, callDemand, callReceiving, callBefore, callRow⟩
  cases mode
  obtain ⟨body, waiting, known, ready, selected, bodyCheck⟩ := RecursiveRequirements.checked_invocation checked
  have certified := DeclaredSourceClosing.lookup_certified stackSource closing known
  cases certified with
  | dispose located built internal template =>
      exact ⟨_, _, _, _, located, built, internal, template,
        by simpa only [List.nil_append] using bodyCheck, invocation_bound source member⟩

end Ash.OneShot.NestedClosingBudgets

#print axioms Ash.OneShot.NestedClosingBudgets.invocation_bound
#print axioms Ash.OneShot.NestedClosingBudgets.owner_invocation
#print axioms Ash.OneShot.NestedClosingBudgets.source_owner_invocation
#print axioms Ash.OneShot.NestedClosingBudgets.captured_owner_invocation
#print axioms Ash.OneShot.NestedClosingBudgets.invocation_demand
#print axioms Ash.OneShot.NestedClosingBudgets.invocation_body_smaller
#print axioms Ash.OneShot.NestedClosingBudgets.invocation_partition
#print axioms Ash.OneShot.NestedClosingBudgets.captured_invocation_partition
#print axioms Ash.OneShot.NestedClosingBudgets.captured_owned_partition
#print axioms Ash.OneShot.NestedClosingBudgets.expand_invocation
#print axioms Ash.OneShot.NestedClosingBudgets.resume_member_source
#print axioms Ash.OneShot.NestedClosingBudgets.selected_resumption
#print axioms Ash.OneShot.NestedClosingBudgets.selected_disposal

#print axioms Ash.OneShot.NestedClosingBudgets.plan_no_scheduled
#print axioms Ash.OneShot.NestedClosingBudgets.captured_no_retirements
