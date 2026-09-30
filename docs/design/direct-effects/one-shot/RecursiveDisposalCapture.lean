import RecursivePlanAdmission

/-!
Both one-shot clause modes use actual saved source and closing plans. Ownership
balance follows from the existing structural checks, including capture across
a surviving caller. Closing and clause admission remain separate obligations.
-/

namespace Ash.OneShot.RecursiveDisposalCapture
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals CoherentSourceTypes
open SourceTemplates (Expression Segment)
open RecursiveRecords (Records CheckedState)
open RecursiveRequirements (Requirements Store Checked evaluate)
open RecursiveClosing (PlanTemplate)
open CallableProtectionFrames (contextOf Tables)
open OwnerPhaseTransitions (Phases available spend spendAll)
open RecursiveClauses (resolved_owner available_unchanged compile fresh_resume_check)

def modeDemand (contract : Owners.Contract) : RecursiveRequirements.Mode → List Nat
  | .resume => contract.resumeDemand
  | .dispose => contract.closeDemand

/-- Owners completed by traversing the current spine. A live boundary's saved
    stack is accounted for separately, because it is entered only by resume. -/
def spineOwners : Stack → List Nat
  | .nil => []
  | .push (.retiring owner) rest => owner :: spineOwners rest
  | .push _ rest => spineOwners rest
  | .live owner _ _ _ _ rest => owner :: spineOwners rest
  | .spent _ _ _ rest => spineOwners rest

def dormantOwners : Stack → List Nat
  | .nil => []
  | .push _ rest => dormantOwners rest
  | .live _ _ _ saved _ rest => ownedTickets saved ++ dormantOwners rest
  | .spent _ _ _ rest => dormantOwners rest

theorem ownership_partition (stack : Stack) :
    (ownedTickets stack).Perm (spineOwners stack ++ dormantOwners stack) := by
  induction stack with
  | nil => exact .refl _
  | push frame rest ih => cases frame <;>
      simpa only [ownedTickets, spineOwners, dormantOwners, List.cons_append] using
        (by first | exact ih | exact ih.cons _)
  | live owner input answer saved caller rest ihSaved ihRest =>
      simp only [ownedTickets, spineOwners, dormantOwners, List.cons_append]
      apply List.Perm.cons
      exact (ihRest.append_left _).trans (by
        simpa only [List.append_assoc] using
          (List.perm_append_comm (l₁ := ownedTickets saved) (l₂ := spineOwners rest)).append_right (dormantOwners rest))
  | spent owner answer caller rest ih => exact ih

/-- Every boundary and scheduled retirement on a checked segment's current
    spine is consumed at its endpoint. The store and entry phases are arbitrary;
    recursive invocations are handled by the existing checked trace theorem. -/
theorem segment_spine_consumed
    (source : Segment operations policy contracts tables world stack input output demand requirements records)
    (checked : Checked store receiving before requirements row) :
    ∀ owner ∈ spineOwners stack, spendAll before demand owner = .consumed := by
  induction source generalizing before receiving row with
  | nil => simp [spineOwners]
  | @push entry input middle headDemand first rest output tailDemand second records head tail ih =>
      obtain ⟨firstRow, secondRow, firstCheck, secondCheck, same⟩ := RecursiveRequirements.checked_sequence_parts checked
      have later := ih secondCheck
      rw [PhaseRechecking.spendAll_append]
      cases head with
      | retiring known =>
          intro owner member
          rcases List.mem_cons.mp member with equal | member
          · subst owner
            exact RecursiveTransport.phases_spendAll_later _
              (OwnerPhaseTransitions.trace_consumed (RecursiveRequirements.checked_trace firstCheck) List.mem_cons_self)
          · exact later owner member
      | plain | handler | cell | armed | running | closing => exact later
  | @live owner contract inputType answerType caller capture body nested rest output demand requirements remaining
      known inputAnnotation answerAnnotation scopeKnown held saved tail ihSaved ihTail =>
      obtain ⟨firstRow, secondRow, firstCheck, secondCheck, same⟩ := RecursiveRequirements.checked_sequence_parts checked
      have consumed : before owner = .consumed := by
        have evaluated := RecursiveRequirements.checked_complete firstCheck
        rw [RecursiveRecomposition.evaluate_spent] at evaluated
        split at evaluated
        · assumption
        · cases evaluated
      intro other member
      rcases List.mem_cons.mp member with equal | member
      · subst other
        exact RecursiveTransport.phases_spendAll_later _ consumed
      · exact ihTail secondCheck other member
  | spent known answerAnnotation scopeKnown tail ih =>
      obtain ⟨firstRow, secondRow, firstCheck, secondCheck, same⟩ := RecursiveRequirements.checked_sequence_parts checked
      exact ih secondCheck

theorem checked_demand_owned
    {requirements : Requirements demand}
    (checked : Checked store receiving (available (ownedTickets stack)) requirements row) :
    demand ⊆ ownedTickets stack := by
  intro owner member
  have ready := OwnerPhaseTransitions.trace_available (RecursiveRequirements.checked_trace checked) owner member
  by_cases owned : owner ∈ ownedTickets stack
  · exact owned
  · simp [available, owned] at ready

theorem segment_spine_demand
    (source : Segment operations policy contracts tables world stack input output demand requirements records)
    (checked : Checked store receiving (available (ownedTickets stack)) requirements row) :
    spineOwners stack ⊆ demand := by
  intro owner member
  have owned : owner ∈ ownedTickets stack :=
    (ownership_partition stack).mem_iff.mpr (List.mem_append_left _ member)
  have consumed := segment_spine_consumed source checked owner member
  by_cases present : owner ∈ demand
  · exact present
  · simp only [OwnerPhaseTransitions.spendAll_at, present, if_false, available, owned, if_true] at consumed
    cases consumed

/-- Any gap between checked demand and actual ownership lies inside a dormant
    capture. This locates the remaining induction obligation; it does not admit
    such a gap as a valid completed source program. -/
theorem undemanded_owner_dormant
    (source : Segment operations policy contracts tables world stack input output demand requirements records)
    (checked : Checked store receiving (available (ownedTickets stack)) requirements row)
    (owned : owner ∈ ownedTickets stack) (absent : owner ∉ demand) :
    owner ∈ dormantOwners stack := by
  rcases List.mem_append.mp ((ownership_partition stack).mem_iff.mp owned) with spine | dormant
  · exact False.elim (absent (segment_spine_demand source checked spine))
  · exact dormant

/-- The base case for the ownership-tree argument. This is a derived theorem
    for stacks with no dormant owners, not a proposed source restriction. -/
theorem no_dormant_balance
    (source : Segment operations policy contracts tables world stack input output demand requirements records)
    (checked : Checked store receiving (available (ownedTickets stack)) requirements row)
    (unique : (ownedTickets stack).Nodup) (noDormant : dormantOwners stack = []) :
    demand.Perm (ownedTickets stack) := by
  apply (List.perm_ext_iff_of_nodup (RecursiveRequirements.checked_once checked) unique).mpr
  intro owner
  constructor
  · intro present
    exact checked_demand_owned checked present
  · intro owned
    by_cases present : owner ∈ demand
    · exact present
    · have hidden := undemanded_owner_dormant source checked owned present
      rw [noDormant] at hidden
      cases hidden

theorem no_dormant_mode_balance
    (source : Segment operations policy contracts tables world capture input output demand requirements records)
    (checked : Checked store receiving (available (ownedTickets capture)) requirements row)
    (unique : (ownedTickets capture).Nodup) (noDormant : dormantOwners capture = [])
    (built : makePlan capture = some plan) :
    (OwnerClosingSource.retirements plan).Perm demand :=
  (OwnerClosingSource.retirements_capture built).trans (no_dormant_balance source checked unique noDormant).symm

theorem captured_owned_sublist (located : SourceTemplates.CapturedIn owner capture root) :
    (ownedTickets capture).Sublist (ownedTickets root) := by
  induction located with
  | here => exact .cons _ (List.sublist_append_left _ _)
  | @push rest frame located ih => cases frame <;> first
      | exact ih
      | exact .cons _ ih
  | saved located ih => exact .cons _ (ih.trans (List.sublist_append_left _ _))
  | tail located ih => exact .cons _ (ih.trans (List.sublist_append_right _ _))
  | spent located ih => exact ih

theorem captured_owned_subset (located : SourceTemplates.CapturedIn owner capture root) :
    ownedTickets capture ⊆ ownedTickets root := (captured_owned_sublist located).subset

theorem captured_inside (outer : SourceTemplates.CapturedIn owner capture root)
    (inner : SourceTemplates.CapturedIn other saved capture) : SourceTemplates.CapturedIn other saved root := by
  induction outer with
  | here => exact .saved inner
  | push outer ih => exact .push ih
  | saved outer ih => exact .saved ih
  | tail outer ih => exact .tail ih
  | spent outer ih => exact .spent ih

theorem scheduled_owned (stack : Stack) : ScopedRetirement.scheduled stack ⊆ ownedTickets stack := by
  induction stack with
  | nil => exact List.nil_subset _
  | push frame rest ih => cases frame <;> first
      | exact ih
      | exact List.cons_subset_cons _ ih
  | live owner input answer saved caller rest ihSaved ihRest =>
      intro other member
      rcases List.mem_append.mp member with saved | rest
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ (ihSaved saved))
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ihRest rest))
  | spent owner answer caller rest ih => exact ih

theorem captured_scheduled_subset (located : SourceTemplates.CapturedIn owner capture root) :
    ScopedRetirement.scheduled capture ⊆ ScopedRetirement.scheduled root := by
  induction located with
  | here => exact List.subset_append_left _ _
  | @push rest frame located ih => cases frame <;> first
      | exact ih
      | exact fun _ member => List.mem_cons_of_mem _ (ih member)
  | saved located ih => exact fun _ member => List.mem_append_left _ (ih member)
  | tail located ih => exact fun _ member => List.mem_append_right _ (ih member)
  | spent located ih => exact ih

theorem scheduled_not_captured (unique : (ownedTickets root).Nodup)
    (located : SourceTemplates.CapturedIn owner capture root) : owner ∉ ScopedRetirement.scheduled root := by
  induction located with
  | @here input answer caller rest =>
      intro member
      apply (List.nodup_cons.mp unique).1
      rcases List.mem_append.mp member with saved | rest
      · exact List.mem_append_left _ (scheduled_owned _ saved)
      · exact List.mem_append_right _ (scheduled_owned _ rest)
  | @push rest frame located ih =>
      cases frame <;> first
        | exact ih unique
        | obtain ⟨absent, restUnique⟩ := List.nodup_cons.mp unique
          intro member
          rcases List.mem_cons.mp member with equal | member
          · exact absent (equal ▸ SourceTemplates.captured_in_owned located)
          · exact ih restUnique member
  | @saved nested other input answer caller rest located ih =>
      have parts := List.nodup_append.mp (List.nodup_cons.mp unique).2
      intro member
      rcases List.mem_append.mp member with saved | rest
      · exact ih parts.1 saved
      · exact parts.2.2 owner (SourceTemplates.captured_in_owned located) owner (scheduled_owned _ rest) rfl
  | @tail rest other input answer saved caller located ih =>
      have parts := List.nodup_append.mp (List.nodup_cons.mp unique).2
      intro member
      rcases List.mem_append.mp member with saved | rest
      · exact parts.2.2 owner (scheduled_owned _ saved) owner (SourceTemplates.captured_in_owned located) rfl
      · exact ih parts.2.1 rest
  | spent located ih => exact ih unique

theorem owned_origin (member : owner ∈ ownedTickets stack) :
    (∃ capture, SourceTemplates.CapturedIn owner capture stack) ∨ owner ∈ ScopedRetirement.scheduled stack := by
  induction stack with
  | nil => cases member
  | push frame rest ih =>
      cases frame <;> first
        | rcases ih member with ⟨capture, located⟩ | scheduled
          · exact Or.inl ⟨capture, .push located⟩
          · exact Or.inr scheduled
        | rcases List.mem_cons.mp member with equal | member
          · exact Or.inr (equal ▸ List.mem_cons_self)
          · rcases ih member with ⟨capture, located⟩ | scheduled
            · exact Or.inl ⟨capture, .push located⟩
            · exact Or.inr (List.mem_cons_of_mem _ scheduled)
  | live other input answer saved caller rest ihSaved ihRest =>
      rcases List.mem_cons.mp member with equal | member
      · subst owner; exact Or.inl ⟨saved, .here⟩
      · rcases List.mem_append.mp member with saved | rest
        · rcases ihSaved saved with ⟨capture, located⟩ | scheduled
          · exact Or.inl ⟨capture, .saved located⟩
          · exact Or.inr (List.mem_append_left _ scheduled)
        · rcases ihRest rest with ⟨capture, located⟩ | scheduled
          · exact Or.inl ⟨capture, .tail located⟩
          · exact Or.inr (List.mem_append_right _ scheduled)
  | spent other answer caller rest ih =>
      rcases ih member with ⟨capture, located⟩ | scheduled
      · exact Or.inl ⟨capture, .spent located⟩
      · exact Or.inr scheduled

theorem captured_in_region (unique : (ownedTickets root).Nodup)
    (outer : SourceTemplates.CapturedIn owner capture root)
    (inner : SourceTemplates.CapturedIn other saved root) (member : other ∈ ownedTickets capture) :
    SourceTemplates.CapturedIn other saved capture := by
  rcases owned_origin member with ⟨actual, located⟩ | scheduled
  · have same := SourceTemplates.captured_in_unique unique (captured_inside outer located) inner
    subst actual
    exact located
  · exact False.elim (scheduled_not_captured unique inner (captured_scheduled_subset outer scheduled))

theorem captured_ownership_closed (unique : (ownedTickets root).Nodup)
    (outer : SourceTemplates.CapturedIn owner capture root)
    (inner : SourceTemplates.CapturedIn other saved root) (member : other ∈ ownedTickets capture) :
    ownedTickets saved ⊆ ownedTickets capture :=
  captured_owned_subset (captured_in_region unique outer inner member)

theorem captured_pending_subset (located : SourceTemplates.CapturedIn owner capture root) :
    capture.erase.pending ⊆ root.erase.pending := by
  induction located with
  | here => exact List.subset_append_left _ _
  | push located ih | spent located ih => first
      | exact ih
      | exact fun _ member => List.mem_append_right _ (ih member)
  | saved located ih => exact fun _ member => List.mem_append_left _ (ih member)
  | tail located ih => exact fun _ member => List.mem_append_right _ (ih member)

/-- Direct retirements exclude bodies referenced by invocation keys. Their
    provenance is checked when the existing recursive derivation enters them. -/
def directRetirements : {demand : List Nat} → Requirements demand → List Nat
  | _, .request _ _ | _, .spent _ | _, .invoke _ _ _ => []
  | _, .retire owner => [owner]
  | _, .sequence first second | _, .choice first second _ => directRetirements first ++ directRetirements second
  | _, .emitAfter body _ _ => directRetirements body

theorem retirements_prepend (requirements : Requirements demand) :
    directRetirements (requirements.prepend nearer) = directRetirements requirements := by
  induction requirements <;> simp_all [Requirements.prepend, directRetirements]

theorem hidden_retirements (hidden : ResourceRequirements.Hides identity opened closed) :
    directRetirements opened = directRetirements closed := by
  induction hidden <;> simp_all [directRetirements]

theorem expression_no_retirements
    (source : Expression operations policy contracts world allowed scope environment code output demand requirements) :
    directRetirements requirements = [] := by
  induction source using Expression.rec (motive_2 := fun _ _ _ _ _ _ _ => True) with
  | handler body clauses capabilities coverage unique admitted table modes ih => simpa only [retirements_prepend] using ih
  | scopedResource initializer body formed effectsBound admitted hidden ihInit ihBody =>
      obtain ⟨identity, fresh⟩ := ScopedTyping.fresh_world_name _
      simp only [directRetirements, ihInit, List.nil_append]
      rw [← hidden_retirements (hidden identity fresh)]
      exact ihBody identity fresh
  | _ => intros; simp_all [directRetirements]

theorem context_no_retirements
    (source : SourceTemplates.Context operations policy contracts world environment allowed scope position input output demand requirements) :
    directRetirements requirements = [] := by
  cases source with
  | pairLeft source | appFunction source _ | bind source | cleanup source _ =>
      simpa only [directRetirements] using expression_no_retirements source
  | branch yes no same => simp only [directRetirements, expression_no_retirements yes, expression_no_retirements no, List.nil_append]
  | pairRight | appArgument | perform | resource | resume => rfl
  | scopedResource body formed effectsBound admitted hidden =>
      obtain ⟨identity, fresh⟩ := ScopedTyping.fresh_world_name _
      rw [← hidden_retirements (hidden identity fresh)]
      exact expression_no_retirements (body identity fresh)

theorem frame_retirements
    (source : SourceTemplates.Frame operations policy contracts world frame input output demand requirements) :
    directRetirements requirements ⊆ ScopedRetirement.scheduled (.push frame .nil) := by
  cases source with
  | plain source scopeTyped inputAnnotation outputAnnotation =>
      rw [context_no_retirements source]
      exact List.nil_subset _
  | handler | cell | armed | running | closing => exact List.nil_subset _
  | retiring => exact List.Subset.refl _

theorem scheduled_push (frame : ExecFrame) (rest : Stack) :
    ScopedRetirement.scheduled (.push frame rest) =
      ScopedRetirement.scheduled (.push frame .nil) ++ ScopedRetirement.scheduled rest := by
  cases frame <;> rfl

theorem segment_retirements
    (source : Segment operations policy contracts tables world stack input output demand requirements records) :
    directRetirements requirements ⊆ ScopedRetirement.scheduled stack := by
  induction source with
  | nil => exact List.nil_subset _
  | @push frame input middle headDemand first rest output tailDemand second records head tail ih =>
      have headBound := frame_retirements head
      rw [directRetirements, retirements_prepend, scheduled_push]
      intro owner member
      rcases List.mem_append.mp member with first | second
      · exact List.mem_append_left _ (headBound first)
      · exact List.mem_append_right _ (ih second)
  | live known inputAnnotation answerAnnotation scopeKnown held saved tail ihSaved ihTail =>
      exact fun _ member => List.mem_append_right _ (ihTail member)
  | spent known answerAnnotation scopeKnown tail ih => exact ih

/-- A completed checking derivation accounts for the immediate saved owners of
    every captured owner it consumes. Referenced bodies retain their actual
    source provenance; disposal accounts for its entire physical closing tree. -/
theorem checked_capture_spines
    (source : Segment operations policy contracts tables world root input output rootDemand rootRequirements resumes)
    (closing : Records operations policy contracts tables world root disposals)
    (unique : (ownedTickets root).Nodup)
    {requirements : Requirements demand}
    (checked : Checked (resumes ++ disposals) receiving before requirements row)
    (retirements : directRetirements requirements ⊆ ScopedRetirement.scheduled root) :
    ∀ owner capture, SourceTemplates.CapturedIn owner capture root → owner ∈ demand →
      ∀ nested ∈ spineOwners capture, spendAll before demand nested = .consumed := by
  induction checked with
  | request | spent => intro owner capture located member; cases member
  | retire ready =>
      intro owner capture located member
      exact False.elim (scheduled_not_captured unique located (retirements member))
  | @invoke key demand body before nearer receiving waiting row known ready selection next ih =>
      cases key with
      | mk called mode => cases mode with
        | resume =>
            have certificate : SourceTemplates.Certified operations policy contracts tables world root
                ⟨called, .resume⟩ ⟨demand, body⟩ := by
              rcases List.mem_append.mp (SourceTemplates.lookup_member known) with original | added
              · exact SourceTemplates.records_certified source original
              · have impossible := RecursiveRecords.record_mode closing added
                cases impossible
            cases certificate with
            | resume actual contractKnown saved =>
                have bodySafe := (segment_retirements saved).trans (captured_scheduled_subset actual)
                intro owner capture located member nested present
                rcases List.mem_cons.mp member with same | later
                · subst owner
                  have sameCapture := SourceTemplates.captured_in_unique unique actual located
                  subst capture
                  exact segment_spine_consumed saved next nested present
                · exact ih bodySafe owner capture located later nested present
        | dispose =>
            have certificate := RecursiveRecords.lookup_certified source closing known
            cases certificate with
            | dispose actual built internal template =>
                rename_i actualCapture actualPlan actualRaw actualRequirements
                intro owner capture located member nested present
                have inside : nested ∈ OwnerClosingSource.retirements actualPlan := by
                  apply (OwnerClosingSource.retirements_capture built).mem_iff.mpr
                  have captured : nested ∈ ownedTickets capture :=
                    (ownership_partition capture).mem_iff.mpr (List.mem_append_left _ present)
                  rcases List.mem_cons.mp member with same | later
                  · subst owner
                    have sameCapture := SourceTemplates.captured_in_unique unique actual located
                    simpa only [sameCapture] using captured
                  · exact captured_ownership_closed unique actual located
                      ((OwnerClosingSource.retirements_capture built).mem_iff.mp later) captured
                exact OwnerPhaseTransitions.trace_consumed (PhaseRechecking.check_owners_iff.mp ready)
                  (List.mem_cons_of_mem _ inside)
  | sequence first second ihFirst ihSecond =>
      intro owner capture located member nested present
      rw [PhaseRechecking.spendAll_append]
      rcases List.mem_append.mp member with earlier | later
      · exact RecursiveTransport.phases_spendAll_later _
          (ihFirst (fun _ member => retirements (List.mem_append_left _ member)) owner capture located earlier nested present)
      · exact ihSecond (fun _ member => retirements (List.mem_append_right _ member)) owner capture located later nested present
  | emitAfter body exported ih => exact ih retirements
  | choice first second ihFirst ihSecond =>
      exact ihFirst (fun _ member => retirements (List.mem_append_left _ member))

/-- Induction over the actual ownership tree turns completion of every saved
    spine into completion of every owner, at arbitrary finite nesting depth. -/
theorem ownership_tree_consumed (stack : Stack) (after : Phases)
    (spine : ∀ owner ∈ spineOwners stack, after owner = .consumed)
    (closed : ∀ owner capture, SourceTemplates.CapturedIn owner capture stack → after owner = .consumed →
      ∀ nested ∈ spineOwners capture, after nested = .consumed) :
    ∀ owner ∈ ownedTickets stack, after owner = .consumed := by
  induction stack with
  | nil => intro owner member; cases member
  | push frame rest ih =>
      have restSpine : ∀ owner ∈ spineOwners rest, after owner = .consumed := by
        cases frame <;> first
          | exact spine
          | exact fun owner member => spine owner (List.mem_cons_of_mem _ member)
      have restClosed := fun owner capture located => closed owner capture (.push located)
      have complete := ih restSpine restClosed
      cases frame <;> first
        | exact complete
        | intro owner member
          rcases List.mem_cons.mp member with same | later
          · exact spine owner (same ▸ List.mem_cons_self)
          · exact complete owner later
  | live owner input answer saved caller rest ihSaved ihRest =>
      have consumed := spine owner List.mem_cons_self
      have savedComplete := ihSaved (closed owner saved .here consumed)
        (fun other capture located => closed other capture (.saved located))
      have restComplete := ihRest (fun other member => spine other (List.mem_cons_of_mem _ member))
        (fun other capture located => closed other capture (.tail located))
      intro other member
      rcases List.mem_cons.mp member with same | later
      · simpa only [same] using consumed
      · rcases List.mem_append.mp later with saved | rest
        · exact savedComplete other saved
        · exact restComplete other rest
  | spent owner answer caller rest ih =>
      exact ih spine (fun other capture located => closed other capture (.spent located))

theorem checked_ownership_balance
    (source : Segment operations policy contracts tables world stack input output pendingDemand pending resumes)
    (closing : Records operations policy contracts tables world stack disposals)
    (unique : (ownedTickets stack).Nodup)
    {requirements : Requirements demand}
    (checked : Checked (resumes ++ disposals) receiving (available (ownedTickets stack)) requirements row)
    (retirements : directRetirements requirements ⊆ ScopedRetirement.scheduled stack)
    (spine : ∀ owner ∈ spineOwners stack, spendAll (available (ownedTickets stack)) demand owner = .consumed) :
    demand.Perm (ownedTickets stack) := by
  have transition := RecursiveRequirements.checked_trace checked
  have complete := ownership_tree_consumed stack _ spine (by
    intro owner capture located consumed
    have demanded := (OwnerSource.trace_member_iff_changes transition (owner := owner)).mpr (by
      rw [consumed]
      simp [available, SourceTemplates.captured_in_owned located])
    exact checked_capture_spines source closing unique checked retirements owner capture located demanded)
  have endpoint : spendAll (available (ownedTickets stack)) demand = OwnerPhaseTransitions.empty := by
    funext owner
    by_cases owned : owner ∈ ownedTickets stack
    · exact complete owner owned
    · exact RecursiveTransport.phases_spendAll_later _ (by simp [available, owned])
  rw [endpoint] at transition
  exact OwnerSource.trace_same_endpoints transition (OwnerPhaseTransitions.trace_all_owned (.refl _) unique)

theorem segment_ownership_balance
    (source : Segment operations policy contracts tables world stack input output demand requirements resumes)
    (closing : Records operations policy contracts tables world stack disposals)
    (unique : (ownedTickets stack).Nodup)
    (checked : Checked (resumes ++ disposals) receiving (available (ownedTickets stack)) requirements row) :
    demand.Perm (ownedTickets stack) :=
  checked_ownership_balance source closing unique checked (segment_retirements source)
    (segment_spine_consumed source checked)

theorem segment_all_owned_consumed
    (source : Segment operations policy contracts tables world stack input output demand requirements resumes)
    (closing : Records operations policy contracts tables world stack disposals)
    (unique : (ownedTickets stack).Nodup)
    (checked : Checked (resumes ++ disposals) receiving (available (ownedTickets stack)) requirements row) :
    ∀ owner ∈ ownedTickets stack, spendAll (available (ownedTickets stack)) demand owner = .consumed := by
  intro owner member
  have demanded := (segment_ownership_balance source closing unique checked).mem_iff.mpr member
  rw [OwnerPhaseTransitions.spendAll_at, if_pos demanded]

theorem segment_mode_balance
    (source : Segment operations policy contracts tables world capture input output demand requirements resumes)
    (closing : Records operations policy contracts tables world capture disposals)
    (unique : (ownedTickets capture).Nodup)
    (checked : Checked (resumes ++ disposals) receiving (available (ownedTickets capture)) requirements row)
    (built : makePlan capture = some plan) :
    (OwnerClosingSource.retirements plan).Perm demand :=
  (OwnerClosingSource.retirements_capture built).trans (segment_ownership_balance source closing unique checked).symm

/-- Whole-state ownership balance is derived from the current source, pending
    source, authenticated stores and existing check. It is not an extra premise
    added to CheckedState. This does not assert admission of every source form. -/
theorem checked_state_ownership_balance
    (source : CheckedState operations policy contracts tables world outside scope code stack output demand row) :
    demand.Perm (ownedTickets stack) := by
  cases source with
  | checked source closing unique evaluated accepted => cases source with
      | checked current scopeTyped pending =>
          apply checked_ownership_balance pending closing unique evaluated
          · simpa only [directRetirements, retirements_prepend, expression_no_retirements current, List.nil_append] using
              segment_retirements pending
          · obtain ⟨currentRow, pendingRow, currentCheck, pendingCheck, same⟩ := RecursiveRequirements.checked_sequence_parts evaluated
            simpa only [PhaseRechecking.spendAll_append] using segment_spine_consumed pending pendingCheck

theorem checked_state_consumes_all
    (source : CheckedState operations policy contracts tables world outside scope code stack output demand row) :
    OwnerPhaseTransitions.Trace (available (ownedTickets stack)) demand OwnerPhaseTransitions.empty := by
  have balanced := checked_state_ownership_balance source
  cases source with
  | checked source closing unique evaluated accepted => exact OwnerPhaseTransitions.trace_all_owned balanced unique

/-- Inspect direct invocation sites, leaving referenced bodies to the existing
    recursive check. This list is not an execution or a consumption demand. -/
def directCalls : {demand : List Nat} → Requirements demand → List Nat
  | _, .request _ _ | _, .retire _ | _, .spent _ => []
  | _, .invoke key _ _ => [key.owner]
  | _, .sequence first second | _, .choice first second _ => directCalls first ++ directCalls second
  | _, .emitAfter body _ _ => directCalls body

theorem calls_prepend (requirements : Requirements demand) :
    directCalls (requirements.prepend nearer) = directCalls requirements := by
  induction requirements <;> simp_all [Requirements.prepend, directCalls]

theorem hidden_calls (hidden : ResourceRequirements.Hides identity opened closed) :
    directCalls opened = directCalls closed := by
  induction hidden <;> simp_all [directCalls]

theorem expression_call_ticket
    (source : Expression operations policy contracts world allowed scope environment code output demand requirements)
    (member : owner ∈ directCalls requirements) :
    ∃ binder, binder ∈ Syntax.ticketDependencies code.dependencies ∧ scope.resolve binder = some owner := by
  induction source using Expression.rec (motive_2 := fun _ _ _ _ _ _ _ => True) with
  | stable | callable | lambda | purePair => cases member
  | pair left right ihLeft ihRight | app left right _ ihLeft ihRight | cleanup left right _ ihLeft ihRight =>
      rcases List.mem_append.mp member with first | second
      · obtain ⟨binder, member, resolved⟩ := ihLeft first
        exact ⟨binder, by simpa only [Code.dependencies, tickets_append] using List.mem_append_left _ member, resolved⟩
      · obtain ⟨binder, member, resolved⟩ := ihRight second
        exact ⟨binder, by simpa only [Code.dependencies, tickets_append] using List.mem_append_right _ member, resolved⟩
  | bind left right ihLeft ihRight =>
      rcases List.mem_append.mp member with first | second
      · obtain ⟨binder, member, resolved⟩ := ihLeft first
        exact ⟨binder, by simpa only [Code.dependencies, tickets_append, tickets_without_variable] using List.mem_append_left _ member, resolved⟩
      · obtain ⟨binder, member, resolved⟩ := ihRight second
        exact ⟨binder, by simpa only [Code.dependencies, tickets_append, tickets_without_variable] using List.mem_append_right _ member, resolved⟩
  | branch condition yes no same ihCondition ihYes ihNo =>
      rcases List.mem_append.mp member with first | second
      · obtain ⟨binder, member, resolved⟩ := ihCondition first
        exact ⟨binder, by simpa only [Code.dependencies, tickets_append] using
          List.mem_append_left _ (List.mem_append_left _ member), resolved⟩
      · rcases List.mem_append.mp second with second | third
        · obtain ⟨binder, member, resolved⟩ := ihYes second
          exact ⟨binder, by simpa only [Code.dependencies, tickets_append] using
            List.mem_append_left _ (List.mem_append_right _ member), resolved⟩
        · obtain ⟨binder, member, resolved⟩ := ihNo third
          exact ⟨binder, by simpa only [Code.dependencies, tickets_append] using List.mem_append_right _ member, resolved⟩
  | handler body clauses capabilities coverage unique admitted table modes ih =>
      obtain ⟨binder, present, resolved⟩ := ih (by simpa only [calls_prepend] using member)
      exact ⟨binder, by simpa only [Code.dependencies, tickets_append, tickets_resource_map, List.nil_append] using
        List.mem_append_left _ present, resolved⟩
  | perform known admitted operand formed ih =>
      obtain ⟨binder, member, resolved⟩ := ih member
      exact ⟨binder, by simpa only [Code.dependencies, tickets_append, tickets_resource_map, List.nil_append] using member, resolved⟩
  | resource initializer body formed effectsBound admitted outward ih ihBody =>
      obtain ⟨binder, member, resolved⟩ := ih member
      exact ⟨binder, by simpa only [Code.dependencies, tickets_append] using List.mem_append_left _ member, resolved⟩
  | scopedResource initializer body formed effectsBound admitted hidden ihInit ihBody =>
      rcases List.mem_append.mp member with first | second
      · obtain ⟨binder, present, resolved⟩ := ihInit first
        exact ⟨binder, by simpa only [Code.dependencies, tickets_append] using List.mem_append_left _ present, resolved⟩
      · obtain ⟨identity, fresh⟩ := ScopedTyping.fresh_world_name _
        rw [← hidden_calls (hidden identity fresh)] at second
        obtain ⟨binder, present, resolved⟩ := ihBody identity fresh second
        rw [ScopedExpressions.instantiation_preserves_ticket_dependencies] at present
        exact ⟨binder, by simpa only [Code.dependencies, tickets_append] using List.mem_append_right _ present, resolved⟩
  | resume known resolved permission operand admitted formed ih =>
      rcases List.mem_append.mp member with operand | called
      · obtain ⟨binder, member, resolution⟩ := ih operand
        exact ⟨binder, List.mem_cons_of_mem _ member, resolution⟩
      · have same := List.mem_singleton.mp called
        subst owner
        exact ⟨_, List.mem_cons_self, resolved⟩
  | discard known resolved permission unprotected admitted =>
      have same := List.mem_singleton.mp member
      subst owner
      exact ⟨_, List.mem_cons_self, resolved⟩
  | _ => intros; trivial

theorem context_call_ticket
    (source : SourceTemplates.Context operations policy contracts world environment allowed scope position input output demand requirements)
    (member : owner ∈ directCalls requirements) :
    ∃ binder, binder ∈ Syntax.ticketDependencies position.dependencies ∧ scope.resolve binder = some owner := by
  cases source with
  | pairLeft source | appFunction source _ | cleanup source _ =>
      simpa only [ScopedExecution.Context.dependencies, ScopedExecution.Context.plug, Code.dependencies,
        tickets_append, show Syntax.ticketDependencies [] = [] from rfl, List.nil_append] using
        expression_call_ticket source member
  | pairRight | appArgument | perform | resource => cases member
  | scopedResource body formed effectsBound admitted hidden =>
      obtain ⟨identity, fresh⟩ := ScopedTyping.fresh_world_name _
      rw [← hidden_calls (hidden identity fresh)] at member
      obtain ⟨binder, present, resolved⟩ := expression_call_ticket (body identity fresh) member
      rw [ScopedExpressions.instantiation_preserves_ticket_dependencies] at present
      exact ⟨binder, by simpa only [ScopedExecution.Context.dependencies, ScopedExecution.Context.plug,
        Code.dependencies, tickets_append, show Syntax.ticketDependencies [] = [] from rfl, List.nil_append] using present, resolved⟩
  | bind source =>
      simpa only [ScopedExecution.Context.dependencies, ScopedExecution.Context.plug, Code.dependencies,
        tickets_append, tickets_without_variable, show Syntax.ticketDependencies [] = [] from rfl, List.nil_append] using
        expression_call_ticket source member
  | branch yes no same =>
      rcases List.mem_append.mp member with first | second
      · obtain ⟨binder, member, resolved⟩ := expression_call_ticket yes first
        exact ⟨binder, by simpa only [ScopedExecution.Context.dependencies, ScopedExecution.Context.plug, Code.dependencies,
          tickets_append, show Syntax.ticketDependencies [] = [] from rfl, List.nil_append] using List.mem_append_left _ member, resolved⟩
      · obtain ⟨binder, member, resolved⟩ := expression_call_ticket no second
        exact ⟨binder, by simpa only [ScopedExecution.Context.dependencies, ScopedExecution.Context.plug, Code.dependencies,
          tickets_append, show Syntax.ticketDependencies [] = [] from rfl, List.nil_append] using List.mem_append_right _ member, resolved⟩
  | resume known resolved permission admitted formed =>
      have same := List.mem_singleton.mp member
      subst owner
      exact ⟨_, List.mem_cons_self, resolved⟩

theorem frame_call_pending
    (source : SourceTemplates.Frame operations policy contracts world frame input output demand requirements)
    (member : owner ∈ directCalls requirements) : owner ∈ frame.erase.pending := by
  cases source with
  | plain source scopeTyped inputAnnotation outputAnnotation =>
      rename_i allowed ticket plain
      obtain ⟨binder, member, resolved⟩ := context_call_ticket source member
      exact (Syntax.scope_translate_membership plain.translated owner).mpr
        ⟨binder, Syntax.mem_ticketDependencies.mp member, resolved⟩
  | handler | cell | armed | running | closing | retiring => cases member

theorem segment_call_pending
    (source : Segment operations policy contracts tables world stack input output demand requirements records)
    (member : owner ∈ directCalls requirements) : owner ∈ stack.erase.pending := by
  induction source with
  | nil => cases member
  | push head tail ih =>
      rw [directCalls, calls_prepend] at member
      rcases List.mem_append.mp member with first | second
      · exact List.mem_append_left _ (frame_call_pending head first)
      · exact List.mem_append_right _ (ih second)
  | live known inputAnnotation answerAnnotation scopeKnown held saved tail ihSaved ihTail =>
      exact List.mem_append_right _ (ihTail member)
  | spent known answerAnnotation scopeKnown tail ih => exact ih member

theorem checked_internal_demand
    (source : Segment operations policy contracts tables world root input output rootDemand rootRequirements resumes)
    (closing : Records operations policy contracts tables world root disposals)
    (unique : (ownedTickets root).Nodup)
    (outer : SourceTemplates.CapturedIn boundary region root)
    (internal : InternalUses region.erase.liveTickets region.erase.pending)
    {requirements : Requirements demand}
    (checked : Checked (resumes ++ disposals) receiving before requirements row)
    (calls : directCalls requirements ⊆ ownedTickets region)
    (retirements : directRetirements requirements ⊆ ownedTickets region) : demand ⊆ ownedTickets region := by
  induction checked with
  | request | spent => exact List.nil_subset _
  | retire ready => exact retirements
  | @invoke key demand body before nearer receiving waiting row known ready selection next ih =>
      have called := calls List.mem_cons_self
      cases key with
      | mk owner mode => cases mode with
        | resume =>
            have certificate : SourceTemplates.Certified operations policy contracts tables world root
                ⟨owner, .resume⟩ ⟨demand, body⟩ := by
              rcases List.mem_append.mp (SourceTemplates.lookup_member known) with original | added
              · exact SourceTemplates.records_certified source original
              · have impossible := RecursiveRecords.record_mode closing added
                cases impossible
            cases certificate with
            | resume actual knownContract saved =>
                rename_i actualCapture actualContract actualRequirements actualRecords
                have localCapture := captured_in_region unique outer actual called
                have bodyCalls : directCalls actualRequirements ⊆ ownedTickets region := by
                  intro nested member
                  exact recursive_live_tickets_owned region (internalUses_subset internal
                    (captured_pending_subset localCapture (segment_call_pending saved member)))
                have bodyRetirements := (segment_retirements saved).trans
                  ((scheduled_owned _).trans (captured_owned_subset localCapture))
                have inside := ih bodyCalls bodyRetirements
                intro nested member
                rcases List.mem_cons.mp member with same | later
                · simpa only [same] using called
                · exact inside later
        | dispose =>
            have certificate := RecursiveRecords.lookup_certified source closing known
            cases certificate with
            | dispose actual built internal template =>
                have included := captured_ownership_closed unique outer actual called
                intro nested member
                rcases List.mem_cons.mp member with same | later
                · simpa only [same] using called
                · exact included ((OwnerClosingSource.retirements_capture built).mem_iff.mp later)
  | sequence first second ihFirst ihSecond =>
      have left := ihFirst (fun _ member => calls (List.mem_append_left _ member))
        (fun _ member => retirements (List.mem_append_left _ member))
      have right := ihSecond (fun _ member => calls (List.mem_append_right _ member))
        (fun _ member => retirements (List.mem_append_right _ member))
      exact List.append_subset.mpr ⟨left, right⟩
  | emitAfter body exported ih => exact ih calls retirements
  | choice first second ihFirst ihSecond =>
      exact ihFirst (fun _ member => calls (List.mem_append_left _ member))
        (fun _ member => retirements (List.mem_append_left _ member))

theorem captured_segment_balance
    (source : Segment operations policy contracts tables world root input output rootDemand rootRequirements resumes)
    (closing : Records operations policy contracts tables world root disposals)
    (unique : (ownedTickets root).Nodup)
    (outer : SourceTemplates.CapturedIn boundary capture root)
    (internal : InternalUses capture.erase.liveTickets capture.erase.pending)
    (saved : Segment operations policy contracts tables world capture argument answer demand requirements records)
    (checked : Checked (resumes ++ disposals) receiving before requirements row)
    (ready : ∀ owner ∈ ownedTickets capture, before owner = .available) :
    demand.Perm (ownedTickets capture) := by
  have retirements := (segment_retirements saved).trans (scheduled_owned capture)
  have calls : directCalls requirements ⊆ ownedTickets capture := by
    intro owner member
    exact recursive_live_tickets_owned capture (internalUses_subset internal (segment_call_pending saved member))
  have inside := checked_internal_demand source closing unique outer internal checked calls retirements
  have transition := RecursiveRequirements.checked_trace checked
  have complete := ownership_tree_consumed capture _ (segment_spine_consumed saved checked) (by
    intro owner nested located consumed
    have demanded := (OwnerSource.trace_member_iff_changes transition (owner := owner)).mpr (by
      rw [ready owner (SourceTemplates.captured_in_owned located), consumed]
      decide)
    exact checked_capture_spines source closing unique checked
      ((segment_retirements saved).trans (captured_scheduled_subset outer))
      owner nested (captured_inside outer located) demanded)
  apply (List.perm_ext_iff_of_nodup (RecursiveRequirements.checked_once checked)
    ((captured_owned_sublist outer).nodup unique)).mpr
  intro owner
  constructor
  · intro member; exact inside member
  · intro owned
    apply (OwnerSource.trace_member_iff_changes transition).mpr
    rw [ready owner owned, complete owner owned]
    decide

theorem demand_shape
    (source : Owners.Derives operations policy contracts inside world environment allowed (.ticket binder owner)
      before code after result demand row)
    (known : contracts owner = some contract) :
    demand = [] ∨ ∃ mode, demand = owner :: modeDemand contract mode := by
  cases source with
  | stable summary exported => exact Or.inl rfl
  | pair left right | app left right _ _ | bind left right | cleanup left right _ _ =>
      rcases demand_shape left known with leftEmpty | ⟨leftMode, leftUse⟩
      · simpa only [leftEmpty, List.nil_append] using demand_shape right known
      · rcases demand_shape right known with rightEmpty | ⟨rightMode, rightUse⟩
        · exact Or.inr ⟨leftMode, by simp only [leftUse, rightEmpty, List.append_nil]⟩
        · have spent := OwnerPhaseTransitions.trace_consumed (Owners.source_trace left)
            (leftUse ▸ List.mem_cons_self)
          have ready := OwnerPhaseTransitions.trace_available (Owners.source_trace right) owner
            (rightUse ▸ List.mem_cons_self)
          rw [spent] at ready
          cases ready
  | branch condition yes no =>
      rcases demand_shape condition known with conditionEmpty | ⟨conditionMode, conditionUse⟩
      · simpa only [conditionEmpty, List.nil_append] using demand_shape yes known
      · rcases demand_shape yes known with yesEmpty | ⟨yesMode, yesUse⟩
        · exact Or.inr ⟨conditionMode, by simp only [conditionUse, yesEmpty, List.append_nil]⟩
        · have spent := OwnerPhaseTransitions.trace_consumed (Owners.source_trace condition)
            (conditionUse ▸ List.mem_cons_self)
          have ready := OwnerPhaseTransitions.trace_available (Owners.source_trace yes) owner
            (yesUse ▸ List.mem_cons_self)
          rw [spent] at ready
          cases ready
  | perform actual admitted operand formed exported => exact demand_shape operand known
  | resource initializer _ _ _ _ _ _ => exact demand_shape initializer known
  | resume actual resolved permission operand transition admitted formed =>
      have sameOwner := resolved_owner resolved
      subst_vars
      have sameContract := Option.some.inj (actual.symm.trans known)
      cases sameContract
      have empty := (available_unchanged operand
        (OwnerPhaseTransitions.trace_available transition _ List.mem_cons_self)).2
      exact Or.inr ⟨.resume, by simp only [empty, List.nil_append, modeDemand]⟩
  | discard actual resolved permission unprotected closable transition admitted =>
      have sameOwner := resolved_owner resolved
      subst_vars
      have sameContract := Option.some.inj (actual.symm.trans known)
      cases sameContract
      exact Or.inr ⟨.dispose, rfl⟩
termination_by code.nodes
decreasing_by all_goals subst_vars; all_goals simp only [Code.nodes]; all_goals omega

theorem consuming_demand
    (source : Owners.Derives operations policy contracts inside world environment allowed (.ticket binder owner)
      before code after result demand row)
    (known : contracts owner = some contract)
    (ready : before owner = .available) (consumed : after owner = .consumed) :
    ∃ mode, demand = owner :: modeDemand contract mode := by
  rcases demand_shape source known with empty | used
  · have endpoint := OwnerPhaseTransitions.trace_result (Owners.source_trace source)
    simp only [empty, spendAll] at endpoint
    rw [endpoint, ready] at consumed
    cases consumed
  · exact used

/-- This finite ownership law compares sets and multiplicities, not execution
    order. Each mode retains its own ordered demands and effect interpretation. -/
theorem consuming_balance
    (source : Owners.Derives operations policy contracts inside world environment allowed (.ticket binder owner)
      before code after result demand row)
    (known : contracts owner = some contract)
    (balance : contract.closeDemand.Perm contract.resumeDemand)
    (ready : before owner = .available) (consumed : after owner = .consumed) :
    demand.Perm (owner :: contract.resumeDemand) := by
  obtain ⟨mode, same⟩ := consuming_demand source known ready consumed
  rw [same]
  cases mode
  · exact .refl _
  · exact balance.cons owner

theorem lookup_after_resumes
    (modes : ∀ key body, (key, body) ∈ resumes → key.mode = .resume) :
    RecursiveRequirements.lookup ⟨owner, .dispose⟩ (resumes ++ disposals) =
      RecursiveRequirements.lookup ⟨owner, .dispose⟩ disposals := by
  induction resumes with
  | nil => rfl
  | cons entry rest ih =>
      have mode := modes entry.1 entry.2 List.mem_cons_self
      have different : (⟨owner, .dispose⟩ : RecursiveRequirements.Key) ≠ entry.1 := by
        intro same
        have impossible := congrArg RecursiveRequirements.Key.mode same
        rw [mode] at impossible
        cases impossible
      simp only [List.cons_append, RecursiveRequirements.lookup, if_neg different]
      exact ih (fun key body member => modes key body (List.mem_cons_of_mem _ member))

theorem closing_record
    (source : Segment operations policy contracts tables world
      (.live owner input answer capture caller tail) result output demand requirements resumes)
    (closing : Records operations policy contracts tables world
      (.live owner input answer capture caller tail) disposals)
    (built : makePlan capture = some plan)
    (internal : InternalUses capture.erase.liveTickets capture.erase.pending) :
    ∃ (raw : Footprint) (closingRequirements : Requirements (OwnerClosingSource.retirements plan)),
      PlanTemplate operations policy contracts tables world .none plan raw closingRequirements ∧
      RecursiveRequirements.lookup ⟨owner, .dispose⟩ (resumes ++ disposals) =
        some ⟨OwnerClosingSource.retirements plan, closingRequirements⟩ := by
  rw [lookup_after_resumes (fun key body member => RecursiveRecords.resume_mode source member)]
  cases closing with
  | unclosable blocked saved rest => rw [built] at blocked; cases blocked
  | external blocked saved rest => exact False.elim (blocked internal)
  | close actual allowed template saved rest =>
      have same := Option.some.inj (actual.symm.trans built)
      cases same
      exact ⟨_, _, template, by simp [RecursiveRequirements.lookup]⟩

/-- The actual closing template supplies the invocation body. Its finite
    evaluation at the surviving caller authenticates the advertised row. -/
theorem closing_invocation_from_record
    (template : PlanTemplate operations policy contracts tables world .none plan raw closingRequirements)
    (looked : RecursiveRequirements.lookup ⟨owner, .dispose⟩ records =
      some ⟨OwnerClosingSource.retirements plan, closingRequirements⟩)
    (unique : (ownedTickets (.live owner input answer capture caller tail)).Nodup)
    (built : makePlan capture = some plan)
    (evaluated : evaluate [] (OwnerPhases.ofStack tables tail)
      (spend (available (ownedTickets (.live owner input answer capture caller tail))) owner) closingRequirements = some row) :
    Checked records (OwnerPhases.ofStack tables (.live owner input answer capture caller tail))
      (available (ownedTickets (.live owner input answer capture caller tail)))
      (.invoke ⟨owner, .dispose⟩ (OwnerClosingSource.retirements plan) []) row := by
  let initial := available (ownedTickets (.live owner input answer capture caller tail))
  have planOwners := OwnerClosingSource.retirements_capture built
  have splitUnique := List.nodup_cons.mp unique
  have planUnique : (owner :: OwnerClosingSource.retirements plan).Nodup := by
    refine List.nodup_cons.mpr ⟨?_, planOwners.symm.nodup (List.nodup_append.mp splitUnique.2).1⟩
    intro member
    exact splitUnique.1 (List.mem_append_left _ (planOwners.mem_iff.mp member))
  have transition : OwnerPhaseTransitions.Trace initial (owner :: OwnerClosingSource.retirements plan)
      (spendAll initial (owner :: OwnerClosingSource.retirements plan)) :=
    OwnerPhaseTransitions.trace_of_available planUnique (by
      intro actual member
      apply if_pos
      rcases List.mem_cons.mp member with same | nested
      · exact List.mem_cons.mpr (Or.inl same)
      · exact List.mem_cons.mpr (Or.inr (List.mem_append_left _ (planOwners.mem_iff.mp nested))))
  have checked : Checked records (OwnerPhases.ofStack tables tail) (spend initial owner) closingRequirements row := by
    apply RecursiveRequirements.evaluate_sound
    rw [RecursiveConsumption.template_store (first := records) (second := []) template]
    exact evaluated
  have body : Checked records (OwnerPhases.ofStack tables (.live owner input answer capture caller tail))
      (spend initial owner) closingRequirements row := by
    apply RecursiveTransport.checked_transport checked (fun _ _ => rfl)
    simp only [OwnerPhases.ofStack, RecursiveTransport.normalize, OwnerPhaseTransitions.spend_self, if_true]
  exact .invoke looked (PhaseRechecking.check_owners_iff.mpr transition)
    (by exact OwnerPhases.Consumes.hit) (by simpa only [List.nil_append] using body)

theorem closing_invocation
    (source : Segment operations policy contracts tables world
      (.live owner input answer capture caller tail) result output demand requirements resumes)
    (closing : Records operations policy contracts tables world
      (.live owner input answer capture caller tail) disposals)
    (unique : (ownedTickets (.live owner input answer capture caller tail)).Nodup)
    (built : makePlan capture = some plan)
    (internal : InternalUses capture.erase.liveTickets capture.erase.pending) :
    ∃ (raw : Footprint) (closingRequirements : Requirements (OwnerClosingSource.retirements plan)),
      PlanTemplate operations policy contracts tables world .none plan raw closingRequirements ∧
      ∀ row, evaluate [] (OwnerPhases.ofStack tables tail)
        (spend (available (ownedTickets (.live owner input answer capture caller tail))) owner) closingRequirements = some row →
        Checked (resumes ++ disposals) (OwnerPhases.ofStack tables (.live owner input answer capture caller tail))
          (available (ownedTickets (.live owner input answer capture caller tail)))
          (.invoke ⟨owner, .dispose⟩ (OwnerClosingSource.retirements plan) []) row := by
  obtain ⟨raw, closingRequirements, template, looked⟩ := closing_record source closing built internal
  exact ⟨raw, closingRequirements, template, fun row evaluated =>
    closing_invocation_from_record template looked unique built evaluated⟩

/-- Assemble a live clause from its recursive source and actual store check.
    The ownership permutation transfers the existing waiting computation. -/
theorem checked_clause_configuration
    (known : contracts owner = some contract)
    (source : Segment operations policy contracts tables world
      (.live owner inputType answerType capture caller tail) contract.answer output tailDemand
      (.sequence (.spent owner) tailRequirements)
      ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: records))
    (closing : Records operations policy contracts tables world
      (.live owner inputType answerType capture caller tail) disposals)
    (savedCheck : Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (records ++ disposals))
      (OwnerPhases.ofStack tables tail) before capturedRequirements contract.resumeRow)
    (tailCheck : Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (records ++ disposals)) []
      (spendAll before contract.resumeDemand) tailRequirements tailRow)
    (phases : spend (available (ownedTickets (.live owner inputType answerType capture caller tail))) owner = before)
    (unique : (ownedTickets (.live owner inputType answerType capture caller tail)).Nodup)
    (current : Expression operations policy contracts world allowed (.ticket binder owner)
      Environment.empty code contract.answer clauseDemand clauseRequirements)
    (currentCheck : Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (records ++ disposals))
      (OwnerPhases.ofStack tables (.live owner inputType answerType capture caller tail))
      (available (ownedTickets (.live owner inputType answerType capture caller tail)))
      clauseRequirements clauseRow)
    (sameDemand : clauseDemand.Perm (owner :: contract.resumeDemand))
    (accepted : checkFootprint outside (clauseRow ++ tailRow) = true) :
    CheckedState operations policy contracts tables world outside (.ticket binder owner)
      code (.live owner inputType answerType capture caller tail) output
      (clauseDemand ++ tailDemand) (clauseRow ++ tailRow) ∧
    (clauseDemand ++ tailDemand).Perm ((owner :: contract.resumeDemand) ++ tailDemand) := by
  let initial := available (ownedTickets (.live owner inputType answerType capture caller tail))
  change spend initial owner = before at phases
  have consumed : before owner = .consumed := phases ▸ OwnerPhaseTransitions.spend_self initial owner
  have afterOwner : spendAll before contract.resumeDemand owner = .consumed :=
    OwnerPhaseTransitions.trace_monotone (RecursiveRequirements.checked_trace savedCheck) consumed
  have pending : Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (records ++ disposals)) []
      (spendAll initial clauseDemand) (.sequence (.spent owner) tailRequirements) tailRow := by
    rw [PhaseRechecking.spendAll_permutation sameDemand]
    simpa only [spendAll, phases, List.nil_append] using
      (Checked.sequence (Checked.spent (store := ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (records ++ disposals)))
        (receiving := []) afterOwner) tailCheck)
  exact ⟨.checked (.checked current (.bound (Owners.ports_lookup known)) source) closing unique
    (.sequence (RecursiveRequirements.checked_prepend_iff.mpr
      (by simpa only [List.append_nil, List.cons_append] using currentCheck)) pending) accepted,
    sameDemand.append_right _⟩

/-- Both invocation modes compile into the same source calculus. Ownership
    balance transfers the waiting check to the clause's actual final phase. -/
theorem fresh_clause_configuration
    (known : contracts owner = some contract)
    (source : Segment operations policy contracts tables world
      (.live owner inputType answerType capture caller tail) contract.answer output tailDemand
      (.sequence (.spent owner) tailRequirements)
      ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: records))
    (closing : Records operations policy contracts tables world
      (.live owner inputType answerType capture caller tail) disposals)
    (savedCheck : Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (records ++ disposals))
      (OwnerPhases.ofStack tables tail) before capturedRequirements contract.resumeRow)
    (tailCheck : Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (records ++ disposals)) []
      (spendAll before contract.resumeDemand) tailRequirements tailRow)
    (phases : spend (available (ownedTickets (.live owner inputType answerType capture caller tail))) owner = before)
    (unique : (ownedTickets (.live owner inputType answerType capture caller tail)).Nodup)
    (balance : contract.closeDemand.Perm contract.resumeDemand)
    (disposal : ∀ row, contract.closeRow = some row →
      Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (records ++ disposals))
        (OwnerPhases.ofStack tables (.live owner inputType answerType capture caller tail))
        (available (ownedTickets (.live owner inputType answerType capture caller tail)))
        (.invoke ⟨owner, .dispose⟩ contract.closeDemand []) row)
    (clause : Owners.Derives operations policy contracts
      (OwnerPhases.ofStack tables (.live owner inputType answerType capture caller tail)) world
      Environment.empty allowed (.ticket binder owner)
      (available (ownedTickets (.live owner inputType answerType capture caller tail)))
      code after contract.answer clauseDemand clauseRow)
    (completed : after owner = .consumed)
    (accepted : checkFootprint outside (clauseRow ++ tailRow) = true) :
    CheckedState operations policy contracts tables world outside (.ticket binder owner)
      code (.live owner inputType answerType capture caller tail) output
      (clauseDemand ++ tailDemand) (clauseRow ++ tailRow) ∧
    (clauseDemand ++ tailDemand).Perm ((owner :: contract.resumeDemand) ++ tailDemand) := by
  have sameDemand := consuming_balance clause known balance
    (by simp [available, ownedTickets]) completed
  have invocation := fresh_resume_check savedCheck phases
  obtain ⟨requirements, current, currentCheck⟩ := compile clause known invocation disposal (fun _ => rfl)
  exact checked_clause_configuration known source closing savedCheck tailCheck phases unique
    current currentCheck sameDemand accepted

theorem captured_held
    (known : contracts owner = some contract)
    (source : Segment operations policy contracts tables world
      (.live owner input answer capture caller tail) result output demand requirements resumes) :
    contract.held = ProtectionContexts.protectedMode capture.erase := by
  cases source with
  | live actual inputAnnotation answerAnnotation scopeKnown held saved rest =>
      have same := Option.some.inj (actual.symm.trans known)
      cases same
      exact held

theorem live_nil_tail_demand
    (source : Segment operations policy contracts tables world
      (.live owner input answer capture caller .nil) result output demand requirements resumes) : demand = [] := by
  cases source with
  | live known inputAnnotation answerAnnotation scopeKnown held saved rest =>
      cases rest
      rfl

/-- The retained source supplies a closing template before a new continuation
    contract or its closing-row annotation is chosen. -/
theorem source_closing_template
    (source : CheckedState operations policy contracts tables world outside scope code whole output demand row)
    (cut : HandlerCut requested whole capture tail handler)
    (built : makePlan capture = some plan) :
    ∃ raw, ∃ requirements : Requirements (OwnerClosingSource.retirements plan),
      PlanTemplate operations policy contracts tables world .none plan raw requirements := by
  cases source with
  | checked source closing unique checked accepted => cases source with
    | checked current scopeTyped pending =>
        obtain ⟨answer, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords,
          annotation, saved, remaining, sameDemand, sameRecords, evaluation⟩ := RecursiveCapture.capture_segments cut pending
        obtain ⟨raw, rows⟩ := RecursiveClosing.plan_rows saved built
        obtain ⟨requirements, template⟩ := RecursiveClosing.rows_template (scope := .none) (tables := tables) rows
        exact ⟨raw, requirements, template⟩

theorem prepare_capture_with_template
    (source : CheckedState operations policy contracts tables world outside scope
      (.perform (Instantiation.freezeEffect requested) operation operand) whole output demand row)
    (cut : HandlerCut requested whole capture tail handler)
    (clause : ClauseAt operation handler.clauses parameter binder body)
    (operationKnown : operations requested operation = some (argument, input))
    (isValue : operand.IsValue) (fresh : contracts owner = none)
    (resumeEffects closeEffects : List Instance) (closingRow : Footprint)
    (built : makePlan capture = some plan)
    (internal : InternalUses capture.erase.liveTickets capture.erase.pending)
    (chosen : PlanTemplate operations policy contracts tables world .none plan raw closingRequirements) :
    ∃ (contract : Owners.Contract) (offeredContract : ClauseContract) (offered requestRow tailRow : Footprint)
      (tailDemand : List Nat) (store : Store),
      contract.input = input ∧ contract.answer.port = ScopedPorts.eraseType handler.answer ∧
      contract.closeDemand = OwnerClosingSource.retirements plan ∧ contract.closeRow = some closingRow ∧
      contract.closeDemand.Perm contract.resumeDemand ∧
      contract.held = ProtectionContexts.protectedMode capture.erase ∧
      contract.resumeEffects = resumeEffects ∧ contract.closeEffects = closeEffects ∧
      PlanTemplate operations policy (contracts.insert owner contract) tables world .none plan raw closingRequirements ∧
      demand = contract.resumeDemand ++ tailDemand ∧
      (tail = .nil → tailDemand = []) ∧
      contract.resumeDemand.Sublist demand ∧
      row = (requestRow ++ contract.resumeRow) ++ tailRow ∧
      lookup operation (tables handler) = some offeredContract ∧
      modeCheck offeredContract.dispose (ProtectionContexts.protectedMode capture.erase) = true ∧
      offeredContract.row (ProtectionContexts.protectedMode capture.erase) = some offered ∧
      residualize (contextOf tables tail) offered = some requestRow ∧
      Checked store
        (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail))
        (available (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)))
        (.invoke ⟨owner, .resume⟩ contract.resumeDemand []) contract.resumeRow ∧
      (∀ actualRow, contract.closeRow = some actualRow →
        residualize (contextOf tables tail) raw = some closingRow →
        Checked store
        (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail))
        (available (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)))
          (.invoke ⟨owner, .dispose⟩ contract.closeDemand []) actualRow) ∧
      ∀ (allowed : List Instance) (clauseDemand : List Nat) (clauseRow : Footprint)
          (clauseRequirements : Requirements clauseDemand),
        Expression operations policy (contracts.insert owner contract) world allowed (.ticket binder owner)
          (Environment.empty.extend parameter argument) body contract.answer clauseDemand clauseRequirements →
        Checked store
        (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail))
        (available (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail))) clauseRequirements clauseRow →
        clauseDemand.Perm (owner :: contract.resumeDemand) → clauseRow ⊆ (requestRow ++ contract.resumeRow) →
        RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩
          ⟨body.subst parameter operand, .ticket binder owner,
            .live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail⟩ [.ticket owner] [] ∧
        CheckedState operations policy (contracts.insert owner contract) tables world outside (.ticket binder owner)
          (body.subst parameter operand) (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)
          output (clauseDemand ++ tailDemand) (clauseRow ++ tailRow) ∧
        (clauseDemand ++ tailDemand).Perm (owner :: demand) ∧
        (clauseRow ++ tailRow) ⊆ row ∧
        ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail) = owner :: ownedTickets whole := by
  cases source with
  | checked source closing unique checked accepted => cases source with
    | checked current scopeTyped pending =>
        obtain ⟨actualArgument, knownOperation, operandSummary, empty⟩ := RecursiveCapture.request_operand current isValue
        obtain ⟨sameArgument, sameInput⟩ := Prod.mk.inj (Option.some.inj (knownOperation.symm.trans operationKnown))
        subst_vars
        obtain ⟨currentRow, pendingRow, currentCheck, pendingCheck, sameRow⟩ := RecursiveRequirements.checked_sequence_parts checked
        have requestExport := RecursiveRequirements.checked_complete (RecursiveRequirements.checked_prepend_iff.mp currentCheck)
        rw [RecursiveDispatch.request_evaluation current isValue] at requestExport
        simp only [List.append_nil, OwnerSource.exportAt, OwnerPhaseTransitions.project_actual] at requestExport
        obtain ⟨offeredContract, offered, offeredKnown, offeredMode, offeredRow, offeredExport⟩ := RecursiveDispatch.cut_residual cut requestExport
        simp only [Bool.false_or] at offeredMode offeredRow
        obtain ⟨contract, capReq, tailDemand, tailReq, tailRow, inputSame, annotation, closeDemandSame, closeRowSame,
          resumeEffectsSame, closeEffectsSame, sameDemand, capturedRow, boundary, closingAfter, addedKeys, capCheck, tailCheck, afterUnique, map⟩ :=
          RecursiveAllocation.capture_record_with_template cut pending closing pendingCheck unique fresh (some closingRow) resumeEffects closeEffects built internal chosen
        have known : (contracts.insert owner contract) owner = some contract := by simp [Owners.Contracts.insert]
        have certificate := SourceTemplates.records_certified boundary
          (key := ⟨owner, .resume⟩) (body := ⟨contract.resumeDemand, capReq⟩) List.mem_cons_self
        obtain ⟨actualContract, actualRequirements, actualRecords, actualKnown, actualTemplate, saved⟩ :=
          SourceTemplates.certified_selected certificate afterUnique SourceTemplates.ActiveCapture.here
        have sameContract := Option.some.inj (actualKnown.symm.trans known)
        cases sameContract
        have sameRequirements := eq_of_heq (Sigma.mk.inj actualTemplate).2
        subst actualRequirements
        have captureBalance := captured_segment_balance boundary closingAfter afterUnique
          SourceTemplates.CapturedIn.here internal saved capCheck (by
            intro nested member
            apply if_pos
            rw [handler_cut_reconstructs cut, owned_tickets_append]
            exact List.mem_append_left _ member)
        have balance : contract.closeDemand.Perm contract.resumeDemand := by
          rw [closeDemandSame]
          exact (OwnerClosingSource.retirements_capture built).trans captureBalance.symm
        have totalRow : row = (currentRow ++ contract.resumeRow) ++ tailRow := by
          simp only [sameRow, capturedRow, List.append_assoc]
        have closed : ClosedValue operand :=
          ScopedPorts.typed_value_closed (operandSummary.ports .none) isValue
        have ready : ClosedExcept parameter body := by
          obtain ⟨savedTyped, tailTyped, handlerTyped⟩ := ScopedPorts.handler_cut_retains_typing cut (SourceTemplates.segment_ports pending)
          cases handlerTyped with
          | handler scopeKnown clauses coverage unique =>
              obtain ⟨inputPort, outputPort, knownPort, bodyTyped⟩ := ScopedPorts.selected_clause_typed clause clauses
              exact ScopedPorts.typed_suffix_ready bodyTyped
        have template := RecursiveRecords.template_extension chosen (Owners.insert_extends (contract := contract) contracts fresh)
        refine ⟨contract, offeredContract, offered, currentRow, tailRow, tailDemand, _,
          inputSame, annotation, closeDemandSame, closeRowSame, balance, captured_held known boundary,
          resumeEffectsSame, closeEffectsSame, template, sameDemand,
          (by intro empty; subst tail; exact live_nil_tail_demand boundary),
          (by simpa only [sameDemand, List.nil_append] using List.sublist_append_left contract.resumeDemand tailDemand),
          totalRow, offeredKnown, offeredMode, offeredRow, offeredExport,
          fresh_resume_check capCheck (RecursiveCapture.capture_phase_consumed cut (RecursiveCapture.fresh_unowned pending fresh)), ?_, ?_⟩
        · intro actualRow closable closingExport
          have evaluated := RecursivePlanAdmission.captured_evaluation template built afterUnique closingExport (store := [])
          have same := Option.some.inj (closeRowSame.symm.trans closable)
          subst actualRow
          rw [closeDemandSame]
          apply closing_invocation_from_record template ?_ afterUnique built evaluated
          rw [← List.cons_append, lookup_after_resumes (fun key body member => RecursiveRecords.resume_mode boundary member)]
          simp [RecursiveRequirements.lookup]
        · intro allowed clauseDemand clauseRow clauseRequirements bodySource bodyCheck sameClause bounded
          have substituted := RecursiveExpressions.substitution bodySource
            ((operandSummary.change_allowed isValue allowed).extension (Owners.insert_extends contracts fresh)) closed
          have included : (clauseRow ++ tailRow) ⊆ row := by
            rw [totalRow]
            intro request member
            rcases List.mem_append.mp member with current | remaining
            · exact List.mem_append_left _ (bounded current)
            · exact List.mem_append_right _ remaining
          obtain ⟨afterChecked, balanced⟩ := checked_clause_configuration known boundary closingAfter capCheck tailCheck
            (RecursiveCapture.capture_phase_consumed cut (RecursiveCapture.fresh_unowned pending fresh)) afterUnique
            substituted bodyCheck sameClause (checked_footprint_subset accepted included)
          exact ⟨.capture requested operation parameter binder owner operand body scope whole capture tail handler
            _ cut clause closed ready, afterChecked,
            by simpa only [sameDemand, List.nil_append, List.cons_append] using balanced,
            included, RecursiveCapture.capture_owned cut⟩

/-- Compute the closing row from the chosen source template and admitted
    upper bound before allocating its fresh continuation contract. Both invocation
    checks are outputs; disposal needs no caller-supplied actual export. -/
theorem prepare_capture_bounded_closing
    (source : CheckedState operations policy contracts tables world outside scope
      (.perform (Instantiation.freezeEffect requested) operation operand) whole output demand row)
    (cut : HandlerCut requested whole capture tail handler)
    (clause : ClauseAt operation handler.clauses parameter binder body)
    (operationKnown : operations requested operation = some (argument, input))
    (isValue : operand.IsValue) (fresh : contracts owner = none)
    (resumeEffects closeEffects : List Instance)
    (built : makePlan capture = some plan)
    (internal : InternalUses capture.erase.liveTickets capture.erase.pending)
    (chosen : PlanTemplate operations policy contracts tables world .none plan raw closingRequirements)
    (covered : EffectBounds.Covers upperRaw raw)
    (admitted : checkFootprint (contextOf tables tail ++ outside) upperRaw = true) :
    ∃ closingRow, residualize (contextOf tables tail) raw = some closingRow ∧
      checkFootprint outside closingRow = true ∧
    ∃ (contract : Owners.Contract) (offeredContract : ClauseContract) (offered requestRow tailRow : Footprint)
      (tailDemand : List Nat) (store : Store),
      contract.input = input ∧ contract.answer.port = ScopedPorts.eraseType handler.answer ∧
      contract.closeDemand = OwnerClosingSource.retirements plan ∧ contract.closeRow = some closingRow ∧
      contract.closeDemand.Perm contract.resumeDemand ∧
      contract.held = ProtectionContexts.protectedMode capture.erase ∧
      contract.resumeEffects = resumeEffects ∧ contract.closeEffects = closeEffects ∧
      PlanTemplate operations policy (contracts.insert owner contract) tables world .none plan raw closingRequirements ∧
      demand = contract.resumeDemand ++ tailDemand ∧
      (tail = .nil → tailDemand = []) ∧
      contract.resumeDemand.Sublist demand ∧
      row = (requestRow ++ contract.resumeRow) ++ tailRow ∧
      lookup operation (tables handler) = some offeredContract ∧
      modeCheck offeredContract.dispose (ProtectionContexts.protectedMode capture.erase) = true ∧
      offeredContract.row (ProtectionContexts.protectedMode capture.erase) = some offered ∧
      residualize (contextOf tables tail) offered = some requestRow ∧
      Checked store
        (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail))
        (available (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)))
        (.invoke ⟨owner, .resume⟩ contract.resumeDemand []) contract.resumeRow ∧
      (∀ actualRow, contract.closeRow = some actualRow →
        Checked store
        (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail))
        (available (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)))
          (.invoke ⟨owner, .dispose⟩ contract.closeDemand []) actualRow) ∧
      ∀ (allowed : List Instance) (clauseDemand : List Nat) (clauseRow : Footprint)
          (clauseRequirements : Requirements clauseDemand),
        Expression operations policy (contracts.insert owner contract) world allowed (.ticket binder owner)
          (Environment.empty.extend parameter argument) body contract.answer clauseDemand clauseRequirements →
        Checked store
        (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail))
        (available (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail))) clauseRequirements clauseRow →
        clauseDemand.Perm (owner :: contract.resumeDemand) → clauseRow ⊆ (requestRow ++ contract.resumeRow) →
        RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩
          ⟨body.subst parameter operand, .ticket binder owner,
            .live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail⟩ [.ticket owner] [] ∧
        CheckedState operations policy (contracts.insert owner contract) tables world outside (.ticket binder owner)
          (body.subst parameter operand) (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)
          output (clauseDemand ++ tailDemand) (clauseRow ++ tailRow) ∧
        (clauseDemand ++ tailDemand).Perm (owner :: demand) ∧
        (clauseRow ++ tailRow) ⊆ row ∧
        ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail) = owner :: ownedTickets whole := by
  obtain ⟨upperRow, upperExport, upperAccepted⟩ := residual_admitted_iff.mp admitted
  obtain ⟨closingRow, closingExport, coveredRow⟩ := UniformClauseBounds.residual_coverage covered upperExport
  obtain ⟨contract, offeredContract, offered, requestRow, tailRow, tailDemand, store,
    inputSame, answerSame, closeDemandSame, closeRowSame, balance, held, resumeSame, closeSame,
    template, sameDemand, emptyTail, subDemand, sameRow, offeredKnown, offeredMode, offeredRow, offeredExport,
    resumeCheck, disposeCheck, enter⟩ :=
    prepare_capture_with_template source cut clause operationKnown isValue fresh resumeEffects closeEffects closingRow built internal chosen
  exact ⟨closingRow, closingExport, EffectBounds.check_covered upperAccepted coveredRow,
    contract, offeredContract, offered, requestRow, tailRow, tailDemand, store,
    inputSame, answerSame, closeDemandSame, closeRowSame, balance, held, resumeSame, closeSame,
    template, sameDemand, emptyTail, subDemand, sameRow, offeredKnown, offeredMode, offeredRow, offeredExport,
    resumeCheck, fun actualRow closable => disposeCheck actualRow closable closingExport, enter⟩

theorem prepare_capture
    (source : CheckedState operations policy contracts tables world outside scope
      (.perform (Instantiation.freezeEffect requested) operation operand) whole output demand row)
    (cut : HandlerCut requested whole capture tail handler)
    (clause : ClauseAt operation handler.clauses parameter binder body)
    (operationKnown : operations requested operation = some (argument, input))
    (isValue : operand.IsValue) (fresh : contracts owner = none)
    (resumeEffects closeEffects : List Instance) (closingRow : Footprint)
    (built : makePlan capture = some plan)
    (internal : InternalUses capture.erase.liveTickets capture.erase.pending) :
    ∃ (contract : Owners.Contract) (offeredContract : ClauseContract) (offered requestRow tailRow raw : Footprint)
      (tailDemand : List Nat) (closingRequirements : Requirements (OwnerClosingSource.retirements plan)) (store : Store),
      contract.input = input ∧ contract.answer.port = ScopedPorts.eraseType handler.answer ∧
      contract.closeDemand = OwnerClosingSource.retirements plan ∧ contract.closeRow = some closingRow ∧
      contract.closeDemand.Perm contract.resumeDemand ∧
      contract.held = ProtectionContexts.protectedMode capture.erase ∧
      contract.resumeEffects = resumeEffects ∧ contract.closeEffects = closeEffects ∧
      PlanTemplate operations policy (contracts.insert owner contract) tables world .none plan raw closingRequirements ∧
      demand = contract.resumeDemand ++ tailDemand ∧
      (tail = .nil → tailDemand = []) ∧
      contract.resumeDemand.Sublist demand ∧
      row = (requestRow ++ contract.resumeRow) ++ tailRow ∧
      lookup operation (tables handler) = some offeredContract ∧
      modeCheck offeredContract.dispose (ProtectionContexts.protectedMode capture.erase) = true ∧
      offeredContract.row (ProtectionContexts.protectedMode capture.erase) = some offered ∧
      residualize (contextOf tables tail) offered = some requestRow ∧
      Checked store
        (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail))
        (available (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)))
        (.invoke ⟨owner, .resume⟩ contract.resumeDemand []) contract.resumeRow ∧
      (∀ actualRow, contract.closeRow = some actualRow →
        residualize (contextOf tables tail) raw = some closingRow →
        Checked store
        (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail))
        (available (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)))
          (.invoke ⟨owner, .dispose⟩ contract.closeDemand []) actualRow) ∧
      ∀ (allowed : List Instance) (clauseDemand : List Nat) (clauseRow : Footprint)
          (clauseRequirements : Requirements clauseDemand),
        Expression operations policy (contracts.insert owner contract) world allowed (.ticket binder owner)
          (Environment.empty.extend parameter argument) body contract.answer clauseDemand clauseRequirements →
        Checked store
        (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail))
        (available (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail))) clauseRequirements clauseRow →
        clauseDemand.Perm (owner :: contract.resumeDemand) → clauseRow ⊆ (requestRow ++ contract.resumeRow) →
        RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩
          ⟨body.subst parameter operand, .ticket binder owner,
            .live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail⟩ [.ticket owner] [] ∧
        CheckedState operations policy (contracts.insert owner contract) tables world outside (.ticket binder owner)
          (body.subst parameter operand) (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)
          output (clauseDemand ++ tailDemand) (clauseRow ++ tailRow) ∧
        (clauseDemand ++ tailDemand).Perm (owner :: demand) ∧
        (clauseRow ++ tailRow) ⊆ row ∧
        ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail) = owner :: ownedTickets whole := by
  obtain ⟨raw, closingRequirements, chosen⟩ := source_closing_template source cut built
  obtain ⟨contract, offeredContract, offered, requestRow, tailRow, tailDemand, store, result⟩ :=
    prepare_capture_with_template source cut clause operationKnown isValue fresh resumeEffects closeEffects closingRow built internal chosen
  exact ⟨contract, offeredContract, offered, requestRow, tailRow, raw, tailDemand, closingRequirements, store, result⟩

theorem capture_from_structural_clause
    (source : CheckedState operations policy contracts tables world outside scope
      (.perform (Instantiation.freezeEffect requested) operation operand) whole output demand row)
    (cut : HandlerCut requested whole capture tail handler)
    (clause : ClauseAt operation handler.clauses parameter binder body)
    (operationKnown : operations requested operation = some (argument, input))
    (isValue : operand.IsValue) (fresh : contracts owner = none)
    (resumeEffects closeEffects : List Instance) (closingRow : Footprint)
    (built : makePlan capture = some plan)
    (internal : InternalUses capture.erase.liveTickets capture.erase.pending) :
    ∃ (contract : Owners.Contract) (offeredContract : ClauseContract) (offered requestRow tailRow raw : Footprint)
      (tailDemand : List Nat) (closingRequirements : Requirements (OwnerClosingSource.retirements plan)),
      contract.input = input ∧ contract.answer.port = ScopedPorts.eraseType handler.answer ∧
      contract.closeDemand = OwnerClosingSource.retirements plan ∧ contract.closeRow = some closingRow ∧
      contract.closeDemand.Perm contract.resumeDemand ∧
      contract.held = ProtectionContexts.protectedMode capture.erase ∧
      contract.resumeEffects = resumeEffects ∧ contract.closeEffects = closeEffects ∧
      PlanTemplate operations policy (contracts.insert owner contract) tables world .none plan raw closingRequirements ∧
      demand = contract.resumeDemand ++ tailDemand ∧
      (tail = .nil → tailDemand = []) ∧
      contract.resumeDemand.Sublist demand ∧
      row = (requestRow ++ contract.resumeRow) ++ tailRow ∧
      lookup operation (tables handler) = some offeredContract ∧
      modeCheck offeredContract.dispose (ProtectionContexts.protectedMode capture.erase) = true ∧
      offeredContract.row (ProtectionContexts.protectedMode capture.erase) = some offered ∧
      residualize (contextOf tables tail) offered = some requestRow ∧
      ∀ (allowed : List Instance) (after : Phases) (clauseDemand : List Nat) (clauseRow : Footprint),
        residualize (contextOf tables tail) raw = some closingRow →
        Owners.Derives operations policy (contracts.insert owner contract)
          (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)) world
          (Environment.empty.extend parameter argument) allowed (.ticket binder owner)
          (available (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)))
          body after contract.answer clauseDemand clauseRow →
        after owner = .consumed → clauseRow ⊆ (requestRow ++ contract.resumeRow) →
        RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩
          ⟨body.subst parameter operand, .ticket binder owner,
            .live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail⟩ [.ticket owner] [] ∧
        CheckedState operations policy (contracts.insert owner contract) tables world outside (.ticket binder owner)
          (body.subst parameter operand) (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)
          output (clauseDemand ++ tailDemand) (clauseRow ++ tailRow) ∧
        (clauseDemand ++ tailDemand).Perm (owner :: demand) ∧
        (clauseRow ++ tailRow) ⊆ row ∧
        ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail) = owner :: ownedTickets whole := by
  obtain ⟨contract, offeredContract, offered, requestRow, tailRow, raw, tailDemand, closingRequirements, store,
    inputSame, answerSame, closeDemandSame, closeRowSame, balance, held, resumeSame, closeSame,
    template, sameDemand, emptyTail, subDemand, sameRow, offeredKnown, offeredMode, offeredRow, offeredExport,
    resumeCheck, disposeCheck, enter⟩ :=
    prepare_capture source cut clause operationKnown isValue fresh resumeEffects closeEffects closingRow built internal
  refine ⟨contract, offeredContract, offered, requestRow, tailRow, raw, tailDemand, closingRequirements,
    inputSame, answerSame, closeDemandSame, closeRowSame, balance, held, resumeSame, closeSame,
    template, sameDemand, emptyTail, subDemand, sameRow, offeredKnown, offeredMode, offeredRow, offeredExport, ?_⟩
  intro allowed after clauseDemand clauseRow closingExport bodySource completed bounded
  have known : (contracts.insert owner contract) owner = some contract := by simp [Owners.Contracts.insert]
  obtain ⟨requirements, current, currentCheck⟩ := compile bodySource known resumeCheck
    (fun actualRow closable => disposeCheck actualRow closable closingExport) (fun _ => rfl)
  have sameClause := consuming_balance bodySource known balance (by simp [available, ownedTickets]) completed
  exact enter allowed clauseDemand clauseRow requirements current currentCheck sameClause bounded


namespace Examples
open RecursiveRecords.Examples (policy inner)

def effect : Instance := .user 91 []
def operations : Operations := fun target operation => if target = effect ∧ operation = 0 then some (.unit, .unit) else none
def contracts : Owners.Contracts := fun owner => if owner = 19 then some inner else none
def clause : Code := .branch (.boolean false) (.resume 1 .unit) (.discard 1)
def handler : HandlerData := ⟨73, effect, .cons 0 2 1 clause .nil, .none, .unit, rfl⟩
def tables : Tables := fun _ => [(0, ⟨true, some [], some []⟩)]
def binding : PlainData := ⟨.bind 99 (.discard 0), .ticket 0 19, .unit, .unit, [19], rfl⟩
def handlerStack : Stack := .push (.handler handler) .nil
def innerBoundary : Stack := .live 19 .unit .unit .nil .none handlerStack
def capture : Stack := .push (.plain binding) innerBoundary
def boundary : Stack := .live 23 .unit .unit capture .none .nil

def emptyRequirements : Requirements [] := .request [] []
def handlerRequirements : Requirements [] := .sequence (emptyRequirements.prepend []) emptyRequirements
def innerRequirements : Requirements [] := .sequence (.spent 19) handlerRequirements
def pendingRequirements : Requirements [19] := .sequence
  ((Requirements.invoke ⟨19, .dispose⟩ [] []).prepend (OwnerPhases.ofStack tables innerBoundary)) innerRequirements

def resumes : Store := [(⟨19, .resume⟩, ⟨[], emptyRequirements⟩)]
def disposals : Store := [(⟨19, .dispose⟩, ⟨[], emptyRequirements⟩)]
def requestRequirements : Requirements [] := .emitAfter emptyRequirements [] [⟨effect, 0, false⟩]

theorem operation_known : operations effect 0 = some (.unit, .unit) := rfl
theorem inner_known : contracts 19 = some inner := rfl

theorem handler_typed : ScopedPorts.FrameTyped operations.ports contracts.ports.types [] (.handler handler) := by
  have body : ScopedPorts.Typed operations.ports [] (ScopedPorts.TypeEnv.empty.extend 2 .unit)
      (.bound 1 .unit .unit [] []) [] clause .unit :=
    .branch .boolean (.resume .unit (by simp) (by simp [ScopedPorts.InWorld, ScopedPorts.Port.resources])) (.discard (by simp))
  refine .handler (residual := []) ⟨.none, .none⟩ (.cons (port_lookup operation_known) body .nil) ?_ (by decide)
  intro operation input output known
  by_cases same : operation = 0
  · subst operation
    simp [handler, ScopedTyping.clauseKeys]
  · simp [Operations.ports, operations, same, handler] at known

theorem pending_source : Segment operations policy contracts tables [] capture .unit .unit [19] pendingRequirements resumes := by
  have body : Expression operations policy contracts [] [] binding.scope (Environment.empty.extend 99 .unit)
      (.discard 0) .unit [19] (.invoke ⟨19, .dispose⟩ [] []) :=
    .discard inner_known rfl rfl rfl (by simp [inner])
  exact .push (.plain (.bind body) (.bound (Owners.ports_lookup inner_known)) rfl rfl)
    (.live inner_known rfl rfl ⟨.none, .none⟩ rfl .nil (.push (.handler handler_typed rfl) .nil))

theorem pending_closing : Records operations policy contracts tables [] capture disposals :=
  .push (.close rfl .nil .nil .nil (.push .nil))

theorem pending_checked : Checked (resumes ++ disposals) [] (available (ownedTickets capture)) pendingRequirements [] := by
  have first : Checked (resumes ++ disposals) [] (available (ownedTickets capture))
      ((Requirements.invoke ⟨19, .dispose⟩ [] []).prepend (OwnerPhases.ofStack tables innerBoundary)) [] :=
    .invoke rfl (by decide) (by exact OwnerPhases.Consumes.hit)
      (.request (by simp [OwnerSource.exportAt, residual_empty]))
  have handlerCheck : Checked (resumes ++ disposals) [] (spendAll (available (ownedTickets capture)) [19]) handlerRequirements [] := by
    apply RecursiveRequirements.evaluate_sound
    simp [handlerRequirements, emptyRequirements, RecursiveRequirements.evaluate_sequence,
      RecursiveRequirements.evaluate_prepend, RecursiveRecomposition.evaluate_empty,
      RecursiveRecomposition.merge_empty_left, spendAll]
  have rest : Checked (resumes ++ disposals) [] (spendAll (available (ownedTickets capture)) [19]) innerRequirements [] :=
    .sequence (.spent (by decide)) handlerCheck
  exact .sequence first rest

/-- The captured pending computation genuinely needs the nested disposal
    record; retaining only resume records cannot check the requesting state. -/
theorem pending_mode_balance :
    (OwnerClosingSource.retirements [.retire 19]).Perm ([19] : List Nat) :=
  segment_mode_balance pending_source pending_closing (by decide) pending_checked rfl

theorem missing_disposal_rejected :
    ¬ Checked resumes [] (available (ownedTickets capture)) pendingRequirements row := by
  intro checked
  obtain ⟨firstRow, tailRow, first, rest, same⟩ := RecursiveRequirements.checked_sequence_parts checked
  have invocation := RecursiveRequirements.checked_prepend_iff.mp first
  obtain ⟨body, waiting, known, ready, selected, bodyCheck⟩ := RecursiveRequirements.checked_invocation invocation
  simp [resumes, RecursiveRequirements.lookup] at known

theorem request_checked : CheckedState operations policy contracts tables [] [] (.ticket 0 19)
    (.perform (Instantiation.freezeEffect effect) 0 .unit) capture .unit [19] [] := by
  have current : Expression operations policy contracts [] [effect] (.ticket 0 19) Environment.empty
      (.perform (Instantiation.freezeEffect effect) 0 .unit) .unit [] requestRequirements :=
    .perform operation_known List.mem_cons_self (.stable .unit) (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])
  have currentCheck : Checked (resumes ++ disposals) (OwnerPhases.ofStack tables capture)
      (available (ownedTickets capture)) requestRequirements [] :=
    .emitAfter (bodyRow := []) (requestRow := [])
      (.request (by simp [OwnerSource.exportAt, residual_empty])) (by decide)
  have prefixed : Checked (resumes ++ disposals) [] (available (ownedTickets capture))
      (requestRequirements.prepend (OwnerPhases.ofStack tables capture)) [] :=
    RecursiveRequirements.checked_prepend_iff.mpr (by simpa only [List.append_nil] using currentCheck)
  exact .checked (.checked current (.bound (Owners.ports_lookup inner_known)) pending_source) pending_closing (by decide)
    (by simpa only [List.nil_append] using Checked.sequence prefixed pending_checked) (by decide)

theorem selected_cut : HandlerCut effect capture capture .nil handler :=
  .push (.plain binding) innerBoundary innerBoundary .nil handler (by decide)
    (.live 19 .unit .unit .nil .none handlerStack handlerStack .nil handler (.hit handler .nil rfl))

theorem single_retirement_evaluation
    (template : PlanTemplate operations policy larger tables [] .none [.retire 19] raw requirements)
    (ready : before 19 = .available) : evaluate [] receiving before requirements = some [] := by
  cases template with
  | retire known rest => cases rest with
      | nil =>
          simp only [OwnerClosingSource.retirements]
          simp only [RecursiveRequirements.evaluate_sequence, RecursiveClosing.evaluate_retire, if_pos ready,
            RecursiveRecomposition.evaluate_empty, merge, List.nil_append]

theorem clause_source (contract : Owners.Contract)
    (input : contract.input = .unit) (answer : contract.answer = .unit)
    (resumeDemand : contract.resumeDemand = [19]) (closeDemand : contract.closeDemand = [19])
    (resumeRow : contract.resumeRow = []) (closeRow : contract.closeRow = some [])
    (unprotected : contract.held = false)
    (resumeEffects : contract.resumeEffects = []) (closeEffects : contract.closeEffects = []) :
    Owners.Derives operations policy (contracts.insert 23 contract) (OwnerPhases.ofStack tables boundary) []
      environment [] (.ticket 1 23) (available (ownedTickets boundary)) clause OwnerPhaseTransitions.empty .unit [23, 19] [] := by
  have known : (contracts.insert 23 contract) 23 = some contract := by simp [Owners.Contracts.insert]
  have transition : OwnerPhaseTransitions.Trace (available (ownedTickets boundary)) [23, 19] OwnerPhaseTransitions.empty :=
    OwnerPhaseTransitions.trace_all_owned (List.Perm.refl _) (by decide)
  have operand : Owners.Derives operations policy (contracts.insert 23 contract) (OwnerPhases.ofStack tables boundary) []
      environment [] (.ticket 1 23) (available (ownedTickets boundary)) .unit (available (ownedTickets boundary)) contract.input [] [] :=
    input.symm ▸ .stable .unit (by simp [OwnerSource.exportAt, residual_empty])
  have resumed : Owners.Derives operations policy (contracts.insert 23 contract) (OwnerPhases.ofStack tables boundary) []
      environment [] (.ticket 1 23) (available (ownedTickets boundary)) (.resume 1 .unit) OwnerPhaseTransitions.empty .unit [23, 19] [] := by
    simpa only [answer, resumeDemand, resumeRow, List.nil_append] using
      Owners.Derives.resume (policy := policy) (binder := 1) known (by rfl) (by rfl) operand
        (resumeDemand.symm ▸ transition) (resumeEffects.symm ▸ List.nil_subset [])
        (answer.symm ▸ (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources]))
  have disposed : Owners.Derives operations policy (contracts.insert 23 contract) (OwnerPhases.ofStack tables boundary) []
      environment [] (.ticket 1 23) (available (ownedTickets boundary)) (.discard 1) OwnerPhaseTransitions.empty .unit [23, 19] [] := by
    simpa only [closeDemand] using
      Owners.Derives.discard (policy := policy) (binder := 1) known (by rfl) (by rfl) unprotected closeRow
        (closeDemand.symm ▸ transition) (closeEffects.symm ▸ List.nil_subset [])
  exact .branch (.stable (row := []) .boolean (by simp [OwnerSource.exportAt, residual_empty])) resumed disposed

theorem capture_preserved : ∃ contract : Owners.Contract,
    RawStep ⟨.perform (Instantiation.freezeEffect effect) 0 .unit, .ticket 0 19, capture⟩
      ⟨clause, .ticket 1 23, boundary⟩ [.ticket 23] [] ∧
    CheckedState operations policy (contracts.insert 23 contract) tables [] [] (.ticket 1 23) clause boundary .unit [23, 19] [] := by
  have chosen : PlanTemplate operations policy contracts tables [] .none [.retire 19] []
      (.sequence (.retire 19) (.request [] [])) := .retire inner_known .nil
  obtain ⟨closingRow, closingExport, closingAccepted, contract, offeredContract, offered, requestRow, tailRow, tailDemand, store,
    input, annotation, closeDemand, closing, derivedBalance, held, resumeEffects, closeEffects, template,
    totalDemand, emptyTail, capturedDemand, totalRow, knownOffer, permitted, offeredRow, exported,
    resumeCheck, disposeCheck, dispatch⟩ :=
    prepare_capture_bounded_closing request_checked selected_cut (.hit) operation_known (by trivial)
      (owner := 23) (by decide) [] [] (by rfl) (by exact .cons 19 [] (by decide) .nil)
      chosen (EffectBounds.covers_refl []) (by decide)
  have closingEmpty : closingRow = [] := by
    simpa only [residual_empty, Option.some.injEq] using closingExport.symm
  subst closingRow
  have tailEmpty := emptyTail rfl
  have resumeDemand : contract.resumeDemand = [19] := by simpa only [tailEmpty, List.append_nil] using totalDemand.symm
  have actualCloseDemand : contract.closeDemand = [19] := closeDemand
  obtain ⟨headEmpty, tailRowEmpty⟩ := List.append_eq_nil_iff.mp totalRow.symm
  obtain ⟨requestEmpty, resumeEmpty⟩ := List.append_eq_nil_iff.mp headEmpty
  have answer : contract.answer = .unit := by
    change contract.answer.port = .unit at annotation
    have unit_port : ∀ value : Value, value.port = .unit → value = .unit := by
      intro value port
      cases value <;> cases port <;> rfl
    exact unit_port contract.answer annotation
  have unprotected : contract.held = false := by
    simpa only [capture, innerBoundary, handlerStack, Stack.erase, ProtectionContexts.protectedMode,
      ExecFrame.erase, PlainData.erase, HandlerData.erase, ProtectionContexts.frameProtected, Bool.false_or] using held
  have body := clause_source (environment := Environment.empty.extend 2 .unit) contract input answer resumeDemand
    actualCloseDemand resumeEmpty closing unprotected resumeEffects closeEffects
  have known : (contracts.insert 23 contract) 23 = some contract := by simp [Owners.Contracts.insert]
  obtain ⟨requirements, current, currentCheck⟩ := compile body known resumeCheck disposeCheck (fun _ => rfl)
  have sameClause := consuming_balance body known derivedBalance (by simp [available, ownedTickets, boundary]) rfl
  obtain ⟨step, checked, balance, included, owned⟩ := dispatch [] [23, 19] [] requirements
    (by simpa only [boundary, handler, Value.port, ScopedPorts.embedPort, answer] using current)
    (by simpa only [boundary, handler, Value.port, ScopedPorts.embedPort] using currentCheck)
    sameClause (List.nil_subset _)
  exact ⟨contract, by simpa [clause, Code.subst, handler, boundary, Value.port, ScopedPorts.embedPort] using step,
    by simpa [tailEmpty, tailRowEmpty, clause, Code.subst, handler, boundary, Value.port, ScopedPorts.embedPort] using checked⟩

def spent : Stack := .spent 23 .unit .none .nil
def closingStack : Stack := .push (.closing 41 (.ticket 1 23)) spent
def retiringStack : Stack := .push (.retiring 19) closingStack

theorem disposal_path_finishes
    (source : CheckedState operations policy (contracts.insert 23 contract) tables [] [] (.ticket 1 23)
      clause boundary .unit [23, 19] []) :
    RawTrace ⟨clause, .ticket 1 23, boundary⟩ ⟨.unit, .none, .nil⟩ [.close 41] [.close 41, .ticket 19, .ticket 23] ∧
    CheckedState operations policy (contracts.insert 23 contract) tables [] [] .none .unit .nil .unit [] [] := by
  obtain ⟨remaining, nextRow, branched, same, included⟩ := RecursiveExecution.branch_preserves source
  have noEffects : nextRow = [] := List.sublist_nil.mp included
  have selected : CheckedState operations policy (contracts.insert 23 contract) tables [] [] (.ticket 1 23)
      (.discard 1) boundary .unit remaining [] := noEffects ▸ branched
  obtain ⟨closingDemand, disposed, consumed, transition⟩ := RecursiveConsumption.discard_cut_preserves
    (front := .nil) selected rfl (plan := [.retire 19]) (by rfl) 41
  have scheduled : CheckedState operations policy (contracts.insert 23 contract) tables [] [] (.ticket 1 23)
      .unit retiringStack .unit closingDemand [] := disposed
  obtain ⟨finalDemand, demandEquation, retired, trace⟩ := RecursiveExecution.retire scheduled
  have closed := RecursiveExecution.finish_close retired
  have finished := RecursiveExecution.leave_clause closed (by trivial)
  have noDemand : finalDemand = [] := by
    obtain ⟨input, requirements, resumes, disposals, summary, scopeTyped, pending, closing, unique, checked, accepted⟩ :=
      RecursiveExecution.value_pending finished (by trivial)
    cases pending
    rfl
  have e0 := RawStep.ifFalse (.resume 1 .unit) (.discard 1) (.ticket 1 23) boundary
  have e1 := RawStep.discard 1 23 41 (.ticket 1 23) .none .unit .unit .nil capture .nil [.retire 19] rfl rfl
  have e2 := RawStep.retire 19 (.ticket 1 23) closingStack
  have e3 := RawStep.finishClose 41 (.ticket 1 23) (.ticket 1 23) spent
  have e4 := RawStep.leaveClause 23 .unit .unit CallableProtection.Examples.unit_closed (.ticket 1 23) .none .nil
  exact ⟨.next e0 (.next e1 (.next e2 (.next e3 (.next e4 (.refl _))))), noDemand ▸ finished⟩

def initial : RunState := ⟨⟨.perform (Instantiation.freezeEffect effect) 0 .unit, .ticket 0 19, capture⟩, [.ticket 19], []⟩
def terminal : RunState := ⟨⟨.unit, .none, .nil⟩, [.ticket 19, .ticket 23, .close 41], [.close 41, .ticket 19, .ticket 23]⟩

theorem initial_ledger : Ledger initial.erase := ⟨.refl _, by decide⟩

theorem captured_disposal_completes : ∃ contract : Owners.Contract,
    RunSteps initial terminal ∧
    CheckedState operations policy (contracts.insert 23 contract) tables [] [] .none .unit .nil .unit [] [] ∧
    Ledger terminal.erase ∧ terminal.completed.Nodup := by
  obtain ⟨contract, captured, source⟩ := capture_preserved
  obtain ⟨rest, returned⟩ := disposal_path_finishes source
  have trace : RawTrace initial.configuration terminal.configuration [.ticket 23, .close 41] [.close 41, .ticket 19, .ticket 23] :=
    .next captured rest
  have run : RunSteps initial terminal := raw_trace_enacts trace (issued := [.ticket 19]) (completed := []) (by decide)
  have ledger := run_steps_preserve_ledger run initial_ledger
  exact ⟨contract, run, returned, ledger, ledger_no_double_completion ledger⟩

/-- A requirement-level witness for the ownership-balance premise. This does
    not assert that the mismatched demands arise from an admitted source. -/
theorem unbalanced_caller_rejected :
    Checked [] [] (spendAll (available [19]) [19]) (.spent 19) [] ∧
    ¬ Checked [] [] (spendAll (available [19]) []) (.spent 19) row := by
  refine ⟨.spent (by decide), ?_⟩
  intro checked
  have evaluated := RecursiveRequirements.checked_complete checked
  simp [RecursiveRecomposition.evaluate_spent, spendAll, available] at evaluated

theorem balance_allows_different_orders :
    spendAll (available [19, 29]) [19, 29] = spendAll (available [19, 29]) [29, 19] :=
  PhaseRechecking.spendAll_permutation (List.Perm.swap 29 19 [])

end Examples

namespace OwnershipExamples
open SharedResumption.NestedExamples (outerBoundary)

theorem nested_resume_consumes_all :
    OwnerPhaseTransitions.Trace (available (ownedTickets outerBoundary)) [19, 29] OwnerPhaseTransitions.empty :=
  checked_state_consumes_all (RecursiveRecords.existing_state SourceTemplates.Examples.checked_configuration)

theorem nested_disposal_consumes_all :
    OwnerPhaseTransitions.Trace (available (ownedTickets RecursiveRecords.Examples.stack)) [23, 19] OwnerPhaseTransitions.empty :=
  checked_state_consumes_all RecursiveRecords.Examples.admitted_discard

theorem nested_demand_omission_rejected :
    ¬ CheckedState operations policy contracts tables world outside scope code outerBoundary output [19] row := by
  intro source
  have length := (checked_state_ownership_balance source).length_eq
  change 1 = 2 at length
  cases length

/-- Reuse the existing nested source derivation. Marking an outer owner spent
    by assumption can leave its dormant inner owner available; arbitrary entry
    phases therefore cannot support the full ownership-exhaustion induction. -/
theorem arbitrary_entry_leaves_dormant :
    SourceTemplates.Segment SharedResumption.Examples.operations SharedResumption.Examples.policy
      SharedResumption.NestedExamples.contracts SharedResumption.Examples.tables [] outerBoundary
      .unit .unit [] SourceTemplates.Examples.outerBoundaryRequirements SourceTemplates.Examples.records ∧
    Checked SourceTemplates.Examples.records [] (available [29]) SourceTemplates.Examples.outerBoundaryRequirements [] ∧
    29 ∈ dormantOwners outerBoundary ∧ spendAll (available [29]) [] 29 = .available := by
  refine ⟨SourceTemplates.Examples.outer_boundary_source, ?_, by decide, rfl⟩
  exact .sequence (.spent rfl) (.request (by simp [OwnerSource.exportAt, residual_empty]))

theorem actual_entry_rejects_unconsumed_boundary :
    ¬ Checked SourceTemplates.Examples.records [] (available (ownedTickets outerBoundary))
      SourceTemplates.Examples.outerBoundaryRequirements row := by
  intro checked
  have consumed := segment_spine_consumed SourceTemplates.Examples.outer_boundary_source checked 19 (by decide)
  change Syntax.UseState.available = .consumed at consumed
  cases consumed

end OwnershipExamples

end Ash.OneShot.RecursiveDisposalCapture

#print axioms Ash.OneShot.RecursiveDisposalCapture.demand_shape
#print axioms Ash.OneShot.RecursiveDisposalCapture.ownership_partition
#print axioms Ash.OneShot.RecursiveDisposalCapture.segment_spine_consumed
#print axioms Ash.OneShot.RecursiveDisposalCapture.checked_demand_owned
#print axioms Ash.OneShot.RecursiveDisposalCapture.segment_spine_demand
#print axioms Ash.OneShot.RecursiveDisposalCapture.undemanded_owner_dormant
#print axioms Ash.OneShot.RecursiveDisposalCapture.no_dormant_balance
#print axioms Ash.OneShot.RecursiveDisposalCapture.no_dormant_mode_balance
#print axioms Ash.OneShot.RecursiveDisposalCapture.Examples.pending_mode_balance
#print axioms Ash.OneShot.RecursiveDisposalCapture.OwnershipExamples.arbitrary_entry_leaves_dormant
#print axioms Ash.OneShot.RecursiveDisposalCapture.OwnershipExamples.actual_entry_rejects_unconsumed_boundary
#print axioms Ash.OneShot.RecursiveDisposalCapture.consuming_demand
#print axioms Ash.OneShot.RecursiveDisposalCapture.consuming_balance
#print axioms Ash.OneShot.RecursiveDisposalCapture.lookup_after_resumes
#print axioms Ash.OneShot.RecursiveDisposalCapture.closing_record
#print axioms Ash.OneShot.RecursiveDisposalCapture.closing_invocation
#print axioms Ash.OneShot.RecursiveDisposalCapture.checked_clause_configuration
#print axioms Ash.OneShot.RecursiveDisposalCapture.fresh_clause_configuration

#print axioms Ash.OneShot.RecursiveDisposalCapture.captured_held
#print axioms Ash.OneShot.RecursiveDisposalCapture.prepare_capture
#print axioms Ash.OneShot.RecursiveDisposalCapture.capture_from_structural_clause

#print axioms Ash.OneShot.RecursiveDisposalCapture.live_nil_tail_demand

#print axioms Ash.OneShot.RecursiveDisposalCapture.Examples.operation_known
#print axioms Ash.OneShot.RecursiveDisposalCapture.Examples.inner_known
#print axioms Ash.OneShot.RecursiveDisposalCapture.Examples.handler_typed
#print axioms Ash.OneShot.RecursiveDisposalCapture.Examples.pending_source
#print axioms Ash.OneShot.RecursiveDisposalCapture.Examples.pending_closing
#print axioms Ash.OneShot.RecursiveDisposalCapture.Examples.pending_checked
#print axioms Ash.OneShot.RecursiveDisposalCapture.Examples.missing_disposal_rejected
#print axioms Ash.OneShot.RecursiveDisposalCapture.Examples.request_checked
#print axioms Ash.OneShot.RecursiveDisposalCapture.Examples.selected_cut
#print axioms Ash.OneShot.RecursiveDisposalCapture.Examples.single_retirement_evaluation
#print axioms Ash.OneShot.RecursiveDisposalCapture.Examples.clause_source
#print axioms Ash.OneShot.RecursiveDisposalCapture.Examples.capture_preserved

#print axioms Ash.OneShot.RecursiveDisposalCapture.Examples.disposal_path_finishes
#print axioms Ash.OneShot.RecursiveDisposalCapture.Examples.initial_ledger
#print axioms Ash.OneShot.RecursiveDisposalCapture.Examples.captured_disposal_completes
#print axioms Ash.OneShot.RecursiveDisposalCapture.Examples.unbalanced_caller_rejected
#print axioms Ash.OneShot.RecursiveDisposalCapture.Examples.balance_allows_different_orders

#print axioms Ash.OneShot.RecursiveDisposalCapture.captured_owned_subset
#print axioms Ash.OneShot.RecursiveDisposalCapture.captured_inside
#print axioms Ash.OneShot.RecursiveDisposalCapture.scheduled_owned
#print axioms Ash.OneShot.RecursiveDisposalCapture.captured_scheduled_subset
#print axioms Ash.OneShot.RecursiveDisposalCapture.scheduled_not_captured
#print axioms Ash.OneShot.RecursiveDisposalCapture.owned_origin
#print axioms Ash.OneShot.RecursiveDisposalCapture.captured_ownership_closed
#print axioms Ash.OneShot.RecursiveDisposalCapture.retirements_prepend
#print axioms Ash.OneShot.RecursiveDisposalCapture.expression_no_retirements
#print axioms Ash.OneShot.RecursiveDisposalCapture.context_no_retirements
#print axioms Ash.OneShot.RecursiveDisposalCapture.frame_retirements
#print axioms Ash.OneShot.RecursiveDisposalCapture.scheduled_push
#print axioms Ash.OneShot.RecursiveDisposalCapture.segment_retirements
#print axioms Ash.OneShot.RecursiveDisposalCapture.checked_capture_spines
#print axioms Ash.OneShot.RecursiveDisposalCapture.ownership_tree_consumed
#print axioms Ash.OneShot.RecursiveDisposalCapture.segment_all_owned_consumed
#print axioms Ash.OneShot.RecursiveDisposalCapture.segment_ownership_balance
#print axioms Ash.OneShot.RecursiveDisposalCapture.segment_mode_balance
#print axioms Ash.OneShot.RecursiveDisposalCapture.checked_ownership_balance
#print axioms Ash.OneShot.RecursiveDisposalCapture.checked_state_ownership_balance
#print axioms Ash.OneShot.RecursiveDisposalCapture.checked_state_consumes_all
#print axioms Ash.OneShot.RecursiveDisposalCapture.OwnershipExamples.nested_resume_consumes_all
#print axioms Ash.OneShot.RecursiveDisposalCapture.OwnershipExamples.nested_disposal_consumes_all
#print axioms Ash.OneShot.RecursiveDisposalCapture.OwnershipExamples.nested_demand_omission_rejected

#print axioms Ash.OneShot.RecursiveDisposalCapture.captured_owned_sublist
#print axioms Ash.OneShot.RecursiveDisposalCapture.captured_in_region
#print axioms Ash.OneShot.RecursiveDisposalCapture.captured_pending_subset
#print axioms Ash.OneShot.RecursiveDisposalCapture.calls_prepend
#print axioms Ash.OneShot.RecursiveDisposalCapture.expression_call_ticket
#print axioms Ash.OneShot.RecursiveDisposalCapture.context_call_ticket
#print axioms Ash.OneShot.RecursiveDisposalCapture.frame_call_pending
#print axioms Ash.OneShot.RecursiveDisposalCapture.segment_call_pending
#print axioms Ash.OneShot.RecursiveDisposalCapture.checked_internal_demand
#print axioms Ash.OneShot.RecursiveDisposalCapture.captured_segment_balance
#print axioms Ash.OneShot.RecursiveDisposalCapture.hidden_retirements
#print axioms Ash.OneShot.RecursiveDisposalCapture.hidden_calls

#print axioms Ash.OneShot.RecursiveDisposalCapture.closing_invocation_from_record

#print axioms Ash.OneShot.RecursiveDisposalCapture.source_closing_template
#print axioms Ash.OneShot.RecursiveDisposalCapture.prepare_capture_with_template

#print axioms Ash.OneShot.RecursiveDisposalCapture.prepare_capture_bounded_closing
