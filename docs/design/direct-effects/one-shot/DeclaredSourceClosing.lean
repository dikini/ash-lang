import DeclaredSourceFrames
import RecursiveCells

/-! Closing plans and records retaining hereditary callback declarations at
exact full callable types and checked requirement indices. Erasure recovers
the existing closing records and all their evaluation and ownership facts. -/
namespace Ash.OneShot.DeclaredSourceClosing
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals CoherentSourceTypes
open Owners (Contracts)
open DeclaredSourceFrames (Segment)
open SourceTemplates (CapturedIn)
open RecursiveRequirements (Requirements Store Key Checked evaluate)
open OwnerPhaseTransitions (Phases Trace spend spendAll)
open OwnerClosingSource (retirements)
open RecursiveRecords (plan_context_scope move_prefix remove_selected)
open RecursiveHandlerTables (closing_context_congr)

inductive Contents (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts) (world : List Nat) : List CloseEntry → Prop where
  | nil : Contents operations policy contracts world []
  | release (rest : Contents operations policy contracts world tail) : Contents operations policy contracts world (.release identity payload :: tail)
  | retire (known : contracts owner = some contract) (rest : Contents operations policy contracts world tail) :
      Contents operations policy contracts world (.retire owner :: tail)
  | invoke (callback : DeclaredSourceValues.ValueSummary operations policy contracts world Environment.empty [] action.action (.function .unit .unit action.requests latent))
      (rest : Contents operations policy contracts world tail) : Contents operations policy contracts world (.invoke action :: tail)

theorem contents_append (first : Contents operations policy contracts world before) (second : Contents operations policy contracts world after) :
    Contents operations policy contracts world (before ++ after) := by
  induction first with
  | nil => exact second
  | release rest ih => exact .release ih
  | retire known rest ih => exact .retire known ih
  | invoke callback rest ih => exact .invoke callback ih

theorem plan_contents
    (source : Segment operations policy contracts tables world capture input output demand requirements records)
    (built : makePlan capture = some plan) : Contents operations policy contracts world plan := by
  induction capture generalizing input output demand requirements records plan with
  | nil => cases built; exact .nil
  | push frame rest ih => cases source with
      | push head erasedHead tail => cases frame with
          | plain => exact ih tail built
          | handler => exact ih tail built
          | cell identity payload scope answer =>
              cases next : makePlan rest <;> simp [makePlan, next] at built
              case some suffix => subst plan; exact .release (ih tail next)
          | armed action => cases head with
              | armed scopeKnown callback annotation =>
                  cases next : makePlan rest <;> simp [makePlan, next] at built
                  case some suffix => subst plan; exact .invoke callback (ih tail next)
          | running | unwinding | closing | retiring => simp [makePlan] at built
  | live owner inputType answerType saved scope rest ihSaved ihRest => cases source with
      | live known inputAnnotation answerAnnotation scopeKnown held captured tail =>
          cases inside : makePlan saved <;> cases outside : makePlan rest <;> simp [makePlan, inside, outside] at built
          case some.some first second =>
            subst plan
            exact contents_append (ihSaved captured inside) (.retire known (ihRest tail outside))
  | spent owner answer scope rest ih => cases source with
      | spent known answerAnnotation scopeKnown tail => exact ih tail built

inductive PlanTemplate (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Owners.Contracts)
    (tables : CallableProtectionFrames.Tables) (world : List Nat) (scope : Scope) :
    (plan : List CloseEntry) → Footprint → Requirements (retirements plan) → Prop where
  | nil : PlanTemplate operations policy contracts tables world scope [] [] (.request [] [])
  | release (rest : PlanTemplate operations policy contracts tables world scope tail raw requirements) :
      PlanTemplate operations policy contracts tables world scope (.release identity payload :: tail) raw
        (.sequence ((Requirements.request [] []).prepend (OwnerPhases.ofStack tables (closeControl scope tail))) requirements)
  | retire (known : contracts owner = some contract)
      (rest : PlanTemplate operations policy contracts tables world scope tail raw requirements) :
      PlanTemplate operations policy contracts tables world scope (.retire owner :: tail) raw
        (.sequence (.retire owner) requirements)
  | invoke (callback : DeclaredSourceValues.ValueSummary operations policy contracts world Environment.empty [] action.action (.function .unit .unit action.requests latent))
      (rest : PlanTemplate operations policy contracts tables world scope tail raw requirements) :
      PlanTemplate operations policy contracts tables world scope (.invoke action :: tail)
        (DisposalProtection.callbackResidual tail latent ++ raw)
        (.sequence ((Requirements.request [] (qualify true latent)).prepend (OwnerPhases.ofStack tables (closeControl scope tail))) requirements)

theorem template_erase
    (source : PlanTemplate operations policy contracts tables world scope plan raw requirements) :
    RecursiveClosing.PlanTemplate operations policy contracts tables world scope plan raw requirements := by
  induction source with
  | nil => exact .nil
  | release rest ih => exact .release ih
  | retire known rest ih => exact .retire known ih
  | invoke callback rest ih => exact .invoke (DeclaredSourceValues.erase callback) ih

theorem contents_template (source : Contents operations policy contracts world plan) :
    ∃ raw, ∃ requirements : Requirements (retirements plan),
      PlanTemplate operations policy contracts tables world scope plan raw requirements := by
  induction source with
  | nil => exact ⟨[], _, .nil⟩
  | release rest ih => obtain ⟨raw, requirements, template⟩ := ih; exact ⟨raw, _, .release template⟩
  | retire known rest ih => obtain ⟨raw, requirements, template⟩ := ih; exact ⟨raw, _, .retire known template⟩
  | invoke callback rest ih => obtain ⟨raw, requirements, template⟩ := ih; exact ⟨_, _, .invoke callback template⟩

/-- Reuse the structural disposal checker to choose an executable plan and
its hereditary callback template from the actual captured source. Successful
checking preserves the original interpretation and pending-owner conditions;
no unrelated plan or callback source is selected afterward. -/
theorem checked_disposal_template
    (source : Segment operations policy contracts tables world capture input output demand requirements records)
    (accepted : ClosingAdmission.checkedDisposal capture.erase outer = some erasedPlan) :
    ∃ plan raw, ∃ closingRequirements : Requirements (retirements plan),
      makePlan capture = some plan ∧
      Discardable capture.erase outer (plan.map CloseEntry.erase) ∧
      InternalUses capture.erase.liveTickets capture.erase.pending ∧
      PlanTemplate operations policy contracts tables world scope plan raw closingRequirements ∧
      (retirements plan).Perm (ownedTickets capture) ∧
      ProtectionContexts.protectedMode capture.erase = false := by
  have disposal := ClosingAdmission.checked_disposal_iff.mp accepted
  have internal : InternalUses capture.erase.liveTickets capture.erase.pending := by
    cases disposal with | checked closing uses => exact uses
  have rawPlanBuilt : rawPlan capture.erase = some erasedPlan := by
    cases disposal with | checked closing uses => exact closes_constructs_raw_plan closing
  have erases := make_plan_erases capture
  cases built : makePlan capture with
  | none =>
      rw [built] at erases
      rw [← erases] at rawPlanBuilt
      cases rawPlanBuilt
  | some plan =>
      rw [built] at erases
      have same := Option.some.inj (erases.trans rawPlanBuilt)
      obtain ⟨raw, closingRequirements, template⟩ := contents_template (plan_contents source built)
      exact ⟨plan, raw, closingRequirements, rfl, by simpa only [same] using disposal,
        internal, template, OwnerClosingSource.retirements_capture built, RecursiveClosing.plan_unprotected built⟩

theorem template_source (template : PlanTemplate operations policy contracts tables world scope plan raw requirements)
    (scopeKnown : ScopedPorts.ScopeKnown contracts.ports.types scope) :
    Segment operations policy contracts tables world (closeControl scope plan) .unit .unit (retirements plan) requirements [] := by
  induction template with
  | nil => exact .nil
  | release rest ih => exact DeclaredSourceFrames.push (.cell scopeKnown (by simp [ScopedPorts.eraseType, ScopedPorts.Port.resources]) rfl) ih
  | retire known rest ih => exact DeclaredSourceFrames.push (.retiring known) ih
  | @invoke latent tail raw requirements action callback rest ih =>
      exact DeclaredSourceFrames.push (.armed (action := { action with scope := scope, answer := .unit }) scopeKnown callback rfl) ih

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
  | invoke callback rest ih => exact .invoke (DeclaredSourceValues.world_weaken callback larger) ih

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

theorem records_erase
    (source : Records operations policy contracts tables world stack records) :
    RecursiveRecords.Records operations policy contracts tables world stack records := by
  induction source with
  | nil => exact .nil
  | push rest ih => exact .push ih
  | unclosable blocked saved rest ihSaved ihRest => exact .unclosable blocked ihSaved ihRest
  | external blocked saved rest ihSaved ihRest => exact .external blocked ihSaved ihRest
  | close built internal template saved rest ihSaved ihRest =>
      exact .close built internal (template_erase template) ihSaved ihRest
  | spent rest ih => exact .spent ih

theorem collect (source : Segment operations policy contracts tables world stack input output demand requirements resumes) :
    ∃ records, Records operations policy contracts tables world stack records := by
  induction source with
  | nil => exact ⟨[], .nil⟩
  | push current head rest ih => obtain ⟨records, collected⟩ := ih; exact ⟨records, .push collected⟩
  | @live owner contract inputType answerType caller capture body nestedRecords restStack output demand requirements remainingRecords
      known inputAnnotation answerAnnotation scopeKnown held saved rest ihSaved ihRest =>
      obtain ⟨nested, captured⟩ := ihSaved
      obtain ⟨remaining, tail⟩ := ihRest
      cases built : makePlan capture with
      | none => exact ⟨_, .unclosable built captured tail⟩
      | some plan =>
          by_cases accepted : ClosingAdmission.checkInternalUses capture.erase.liveTickets capture.erase.pending = true
          · have internal := ClosingAdmission.check_internal_uses_iff.mp accepted
            obtain ⟨raw, requirements, template⟩ := contents_template (scope := Execution.Scope.none) (tables := tables) (plan_contents saved built)
            exact ⟨_, .close built internal template captured tail⟩
          · exact ⟨_, .external (fun internal => accepted (ClosingAdmission.check_internal_uses_iff.mpr internal)) captured tail⟩
  | spent known answerAnnotation scopeKnown rest ih => obtain ⟨records, collected⟩ := ih; exact ⟨records, .spent collected⟩

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
  | invoke callback rest ih => exact .invoke (DeclaredSourceValues.extension callback extension) ih

theorem records_extension (source : Records operations policy contracts tables world stack records)
    (extension : contracts.Extends larger) : Records operations policy larger tables world stack records := by
  induction source with
  | nil => exact .nil
  | push rest ih => exact .push ih
  | unclosable blocked saved rest ihSaved ihRest => exact .unclosable blocked ihSaved ihRest
  | external blocked saved rest ihSaved ihRest => exact .external blocked ihSaved ihRest
  | close built internal template saved rest ihSaved ihRest => exact .close built internal (template_extension template extension) ihSaved ihRest
  | spent rest ih => exact .spent ih


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
    (RecursiveTransport.recordOwners records).Sublist (ownedTickets stack) :=
  RecursiveRecords.owners_sublist (records_erase source)

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
  · have impossible := RecursiveRecords.resume_mode source.erase original
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

theorem template_congr
    (source : PlanTemplate operations policy contracts first world scope plan raw requirements) :
    PlanTemplate operations policy contracts second world scope plan raw requirements := by
  induction source with
  | nil => exact .nil
  | release rest ih => simpa only [closing_context_congr first second] using PlanTemplate.release ih
  | retire known rest ih => exact .retire known ih
  | invoke callback rest ih => simpa only [closing_context_congr first second] using PlanTemplate.invoke callback ih

theorem records_congr
    (source : Records operations policy contracts first world stack records) :
    Records operations policy contracts second world stack records := by
  induction source with
  | nil => exact .nil
  | push rest ih => exact .push ih
  | unclosable blocked saved rest ihSaved ihRest => exact .unclosable blocked ihSaved ihRest
  | external outside saved rest ihSaved ihRest => exact .external outside ihSaved ihRest
  | close built internal template saved rest ihSaved ihRest =>
      exact .close built internal (template_congr template) ihSaved ihRest
  | spent rest ih => exact .spent ih

theorem update_records
    (update : CellUpdate identity old new before after)
    (source : Records operations policy contracts tables world before records) :
    Records operations policy contracts tables world after records := by
  induction update generalizing records with
  | hit => cases source with
    | push rest => exact .push rest
  | push miss next ih => cases source with
    | push rest => exact .push (ih rest)
  | live next ih => cases source with
    | unclosable blocked saved rest => exact .unclosable blocked saved (ih rest)
    | external outside saved rest => exact .external outside saved (ih rest)
    | close built internal template saved rest => exact .close built internal template saved (ih rest)
  | spent next ih => cases source with
    | spent rest => exact .spent (ih rest)

theorem plan_records (plan : List CloseEntry) :
    Records operations policy contracts tables world (closeControl scope plan) [] := by
  induction plan with
  | nil => exact .nil
  | cons entry rest ih => exact .push ih

theorem certified_plan_at
    (certificate : Certified operations policy contracts tables world stack key body)
    (unique : (ownedTickets stack).Nodup) (located : SourceTemplates.CapturedIn key.owner capture stack) :
    ∃ (plan : List CloseEntry) (raw : Footprint) (requirements : Requirements (OwnerClosingSource.retirements plan)),
      makePlan capture = some plan ∧ body = ⟨OwnerClosingSource.retirements plan, requirements⟩ ∧
      PlanTemplate operations policy contracts tables world .none plan raw requirements := by
  cases certificate with
  | dispose saved built internal template =>
      have same := SourceTemplates.captured_in_unique unique saved located
      cases same
      exact ⟨_, _, _, built, rfl, template⟩


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


end Ash.OneShot.DeclaredSourceClosing

#print axioms Ash.OneShot.DeclaredSourceClosing.contents_append
#print axioms Ash.OneShot.DeclaredSourceClosing.plan_contents
#print axioms Ash.OneShot.DeclaredSourceClosing.template_erase
#print axioms Ash.OneShot.DeclaredSourceClosing.contents_template
#print axioms Ash.OneShot.DeclaredSourceClosing.checked_disposal_template
#print axioms Ash.OneShot.DeclaredSourceClosing.template_source
#print axioms Ash.OneShot.DeclaredSourceClosing.template_scope
#print axioms Ash.OneShot.DeclaredSourceClosing.template_world_weaken
#print axioms Ash.OneShot.DeclaredSourceClosing.records_world_weaken
#print axioms Ash.OneShot.DeclaredSourceClosing.records_erase
#print axioms Ash.OneShot.DeclaredSourceClosing.collect
#print axioms Ash.OneShot.DeclaredSourceClosing.records_append
#print axioms Ash.OneShot.DeclaredSourceClosing.template_extension
#print axioms Ash.OneShot.DeclaredSourceClosing.records_extension
#print axioms Ash.OneShot.DeclaredSourceClosing.certified_transport
#print axioms Ash.OneShot.DeclaredSourceClosing.records_certified
#print axioms Ash.OneShot.DeclaredSourceClosing.owners_sublist
#print axioms Ash.OneShot.DeclaredSourceClosing.split_live
#print axioms Ash.OneShot.DeclaredSourceClosing.resume_records
#print axioms Ash.OneShot.DeclaredSourceClosing.lookup_certified
#print axioms Ash.OneShot.DeclaredSourceClosing.certified_selected
#print axioms Ash.OneShot.DeclaredSourceClosing.template_congr
#print axioms Ash.OneShot.DeclaredSourceClosing.records_congr
#print axioms Ash.OneShot.DeclaredSourceClosing.update_records
#print axioms Ash.OneShot.DeclaredSourceClosing.plan_records
#print axioms Ash.OneShot.DeclaredSourceClosing.certified_plan_at
#print axioms Ash.OneShot.DeclaredSourceClosing.split_append
#print axioms Ash.OneShot.DeclaredSourceClosing.capture_records_with_template
