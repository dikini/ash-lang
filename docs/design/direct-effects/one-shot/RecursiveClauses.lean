import RecursiveCapture

/-!
Structural clause derivations joined to authenticated recursive invocation
checks. A clause's local owner is fixed by scope resolution. Its effects before
and after invocation use the actual multi-owner phase map, not a cached Boolean
protection summary. Handler-table admission remains a separate source join.
-/

namespace Ash.OneShot.RecursiveClauses
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals CoherentSourceTypes
open SourceTemplates (Expression)
open RecursiveRequirements (Requirements Checked)
open OwnerPhaseTransitions (Phases)

theorem resolved_owner (resolved : (Execution.Scope.ticket binder owner).resolve name = some actual) : actual = owner := by
  simp only [Execution.Scope.resolve] at resolved
  split at resolved
  · exact (Option.some.inj resolved).symm
  · cases resolved

/-- If a clause leaves its local owner available, it has made no continuation
    transition. Consequently every other owner's phase is also unchanged. -/
theorem available_unchanged
    (source : Owners.Derives operations policy contracts inside world environment allowed (.ticket binder owner)
      before code after result demand row)
    (available : after owner = .available) : before = after ∧ demand = [] := by
  cases source with
  | stable summary exported => exact ⟨rfl, rfl⟩
  | pair left right | app left right _ _ | bind left right | cleanup left right _ _ =>
      obtain ⟨middle, rightEmpty⟩ := available_unchanged right available
      obtain ⟨first, leftEmpty⟩ := available_unchanged left (middle.symm ▸ available)
      exact ⟨first.trans middle, by simp only [leftEmpty, rightEmpty, List.nil_append]⟩
  | branch condition yes no =>
      obtain ⟨middle, yesEmpty⟩ := available_unchanged yes available
      obtain ⟨first, conditionEmpty⟩ := available_unchanged condition (middle.symm ▸ available)
      exact ⟨first.trans middle, by simp only [conditionEmpty, yesEmpty, List.nil_append]⟩
  | perform known admitted operand formed exported => exact available_unchanged operand available
  | resource initializer _ _ _ _ _ _ => exact available_unchanged initializer available
  | resume known resolved permission operand transition admitted formed =>
      have same := resolved_owner resolved
      subst_vars
      have spent := OwnerPhaseTransitions.trace_consumed transition List.mem_cons_self
      rw [available] at spent
      cases spent
  | discard known resolved permission unprotected closable transition admitted =>
      have same := resolved_owner resolved
      subst_vars
      have spent := OwnerPhaseTransitions.trace_consumed transition List.mem_cons_self
      rw [available] at spent
      cases spent
termination_by code.nodes
decreasing_by all_goals subst_vars; all_goals simp only [Code.nodes]; all_goals omega

theorem entry_after
    (source : Owners.Derives operations policy contracts inside world environment allowed (.ticket binder owner)
      before code after result demand row)
    (entry : before owner = .available → before = initial) : after owner = .available → after = initial := by
  intro available
  have same := (available_unchanged source available).1
  exact same.symm.trans (entry (same.symm ▸ available))

/-- Only invocation checks are supplied here, authenticated separately from
    the actual saved source or closing plan. All surrounding clause syntax and
    effect checks are reconstructed by induction on the structural derivation. -/
theorem compile
    (source : Owners.Derives operations policy contracts inside world environment allowed (.ticket binder owner)
      before code after result demand row)
    (known : contracts owner = some contract)
    (resumeCheck : Checked records inside initial (.invoke ⟨owner, .resume⟩ contract.resumeDemand []) contract.resumeRow)
    (disposeCheck : ∀ closingRow, contract.closeRow = some closingRow →
      Checked records inside initial (.invoke ⟨owner, .dispose⟩ contract.closeDemand []) closingRow)
    (entry : before owner = .available → before = initial) :
    ∃ requirements : Requirements demand,
      Expression operations policy contracts world allowed (.ticket binder owner) environment code result demand requirements ∧
      Checked records inside before requirements row := by
  have endpoint := OwnerPhaseTransitions.trace_result (Owners.source_trace source)
  cases source with
  | stable summary exported => exact ⟨_, .stable summary, .request exported⟩
  | pair left right =>
      obtain ⟨a, first, firstCheck⟩ := compile left known resumeCheck disposeCheck entry
      obtain ⟨b, second, secondCheck⟩ := compile right known resumeCheck disposeCheck (entry_after left entry)
      exact ⟨_, .pair first second, .sequence firstCheck
        (OwnerPhaseTransitions.trace_result (Owners.source_trace left) ▸ secondCheck)⟩
  | app function argument admitted exported =>
      obtain ⟨a, first, firstCheck⟩ := compile function known resumeCheck disposeCheck entry
      obtain ⟨b, second, secondCheck⟩ := compile argument known resumeCheck disposeCheck (entry_after function entry)
      refine ⟨_, .app first second admitted, .emitAfter (.sequence firstCheck
        (OwnerPhaseTransitions.trace_result (Owners.source_trace function) ▸ secondCheck)) ?_⟩
      simpa only [List.nil_append, ← endpoint] using exported
  | bind initializer body =>
      obtain ⟨a, first, firstCheck⟩ := compile initializer known resumeCheck disposeCheck entry
      obtain ⟨b, second, secondCheck⟩ := compile body known resumeCheck disposeCheck (entry_after initializer entry)
      exact ⟨_, .bind first second, .sequence firstCheck
        (OwnerPhaseTransitions.trace_result (Owners.source_trace initializer) ▸ secondCheck)⟩
  | branch condition yes no =>
      obtain ⟨a, first, firstCheck⟩ := compile condition known resumeCheck disposeCheck entry
      obtain ⟨b, second, secondCheck⟩ := compile yes known resumeCheck disposeCheck (entry_after condition entry)
      obtain ⟨c, third, thirdCheck⟩ := compile no known resumeCheck disposeCheck (entry_after condition entry)
      let same := Owners.branch_demands_agree yes no
      refine ⟨_, .branch first second third same, ?_⟩
      have branches := Checked.choice (same := same) secondCheck thirdCheck
      have combined := Checked.sequence firstCheck (OwnerPhaseTransitions.trace_result (Owners.source_trace condition) ▸ branches)
      simpa only [List.append_assoc] using combined
  | perform actual admitted operand formed exported =>
      obtain ⟨a, source, checked⟩ := compile operand known resumeCheck disposeCheck entry
      refine ⟨_, .perform actual admitted source formed, .emitAfter checked ?_⟩
      simpa only [List.nil_append, ← endpoint] using exported
  | resource initializer body formed effectsBound admitted outward exported =>
      obtain ⟨a, source, checked⟩ := compile initializer known resumeCheck disposeCheck entry
      refine ⟨_, .resource source (fun identity fresh => CallableSources.from_legacy (body identity fresh)
        (fun _ _ _ _ _ _ checked => .stable checked)) formed effectsBound admitted outward, .emitAfter checked ?_⟩
      simpa only [List.nil_append, ← endpoint] using exported
  | resume actual resolved permission operand transition admitted formed =>
      have sameOwner := resolved_owner resolved
      subst_vars
      have sameContract := Option.some.inj (actual.symm.trans known)
      cases sameContract
      obtain ⟨a, source, checked⟩ := compile operand known resumeCheck disposeCheck entry
      have available := OwnerPhaseTransitions.trace_available transition _ List.mem_cons_self
      have sameEntry := entry_after operand entry available
      exact ⟨_, .resume known resolved permission source admitted formed, .sequence checked
        (OwnerPhaseTransitions.trace_result (Owners.source_trace operand) ▸ (sameEntry.symm ▸ resumeCheck))⟩
  | discard actual resolved permission unprotected closable transition admitted =>
      have sameOwner := resolved_owner resolved
      subst_vars
      have sameContract := Option.some.inj (actual.symm.trans known)
      cases sameContract
      have available := OwnerPhaseTransitions.trace_available transition _ List.mem_cons_self
      exact ⟨_, .discard known resolved permission unprotected admitted,
        (entry available).symm ▸ disposeCheck _ closable⟩
  | cleanup callback body admitted exported =>
      obtain ⟨a, first, firstCheck⟩ := compile callback known resumeCheck disposeCheck entry
      obtain ⟨b, second, secondCheck⟩ := compile body known resumeCheck disposeCheck (entry_after callback entry)
      refine ⟨_, .cleanup first second admitted, .emitAfter (.sequence firstCheck
        (OwnerPhaseTransitions.trace_result (Owners.source_trace callback) ▸ secondCheck)) ?_⟩
      simpa only [List.nil_append, ← endpoint, OwnerSource.exportAt, residualize, DisposalProtection.through_barrier] using exported
termination_by code.nodes
decreasing_by all_goals subst_vars; all_goals simp only [Code.nodes]; all_goals omega


/-- A resume-only clause either does not invoke its continuation or has exactly
    the demand of that one invocation, including the saved body's demands. -/
theorem demand_shape
    (source : Owners.Derives operations policy contracts inside world environment allowed (.ticket binder owner)
      before code after result demand row)
    (known : contracts owner = some contract) (resumeOnly : contract.closeRow = none) :
    demand = [] ∨ demand = owner :: contract.resumeDemand := by
  cases source with
  | stable summary exported => exact Or.inl rfl
  | pair left right | app left right _ _ | bind left right | cleanup left right _ _ =>
      rcases demand_shape left known resumeOnly with leftEmpty | leftUse
      · simpa only [leftEmpty, List.nil_append] using demand_shape right known resumeOnly
      · rcases demand_shape right known resumeOnly with rightEmpty | rightUse
        · exact Or.inr (by simp only [leftUse, rightEmpty, List.append_nil])
        · have spent := OwnerPhaseTransitions.trace_consumed (Owners.source_trace left)
            (leftUse ▸ List.mem_cons_self)
          have ready := OwnerPhaseTransitions.trace_available (Owners.source_trace right) owner
            (rightUse ▸ List.mem_cons_self)
          rw [spent] at ready
          cases ready
  | branch condition yes no =>
      rcases demand_shape condition known resumeOnly with conditionEmpty | conditionUse
      · simpa only [conditionEmpty, List.nil_append] using demand_shape yes known resumeOnly
      · rcases demand_shape yes known resumeOnly with yesEmpty | yesUse
        · exact Or.inr (by simp only [conditionUse, yesEmpty, List.append_nil])
        · have spent := OwnerPhaseTransitions.trace_consumed (Owners.source_trace condition)
            (conditionUse ▸ List.mem_cons_self)
          have ready := OwnerPhaseTransitions.trace_available (Owners.source_trace yes) owner
            (yesUse ▸ List.mem_cons_self)
          rw [spent] at ready
          cases ready
  | perform actual admitted operand formed exported => exact demand_shape operand known resumeOnly
  | resource initializer _ _ _ _ _ _ => exact demand_shape initializer known resumeOnly
  | resume actual resolved permission operand transition admitted formed =>
      have sameOwner := resolved_owner resolved
      subst_vars
      have sameContract := Option.some.inj (actual.symm.trans known)
      cases sameContract
      have empty := (available_unchanged operand
        (OwnerPhaseTransitions.trace_available transition _ List.mem_cons_self)).2
      exact Or.inr (by simp only [empty, List.nil_append])
  | discard actual resolved permission unprotected closable transition admitted =>
      have sameOwner := resolved_owner resolved
      subst_vars
      have sameContract := Option.some.inj (actual.symm.trans known)
      cases sameContract
      rw [resumeOnly] at closable
      cases closable
termination_by code.nodes
decreasing_by all_goals subst_vars; all_goals simp only [Code.nodes]; all_goals omega

theorem consuming_demand
    (source : Owners.Derives operations policy contracts inside world environment allowed (.ticket binder owner)
      before code after result demand row)
    (known : contracts owner = some contract) (resumeOnly : contract.closeRow = none)
    (ready : before owner = .available) (consumed : after owner = .consumed) :
    demand = owner :: contract.resumeDemand := by
  rcases demand_shape source known resumeOnly with empty | used
  · have endpoint := OwnerPhaseTransitions.trace_result (Owners.source_trace source)
    simp only [empty, OwnerPhaseTransitions.spendAll] at endpoint
    rw [endpoint, ready] at consumed
    cases consumed
  · exact used

/-- The actual saved requirements authenticate an invocation at the fresh live
    boundary. This is independent of the surrounding clause syntax. -/
theorem fresh_resume_check
    (savedCheck : Checked ((⟨owner, .resume⟩, ⟨resumeDemand, capturedRequirements⟩) :: records)
      (OwnerPhases.ofStack tables tail) before capturedRequirements resumeRow)
    (phases : OwnerPhaseTransitions.spend
      (OwnerPhaseTransitions.available (ownedTickets (.live owner inputType answerType capture caller tail))) owner = before) :
    Checked ((⟨owner, .resume⟩, ⟨resumeDemand, capturedRequirements⟩) :: records)
      (OwnerPhases.ofStack tables (.live owner inputType answerType capture caller tail))
      (OwnerPhaseTransitions.available (ownedTickets (.live owner inputType answerType capture caller tail)))
      (.invoke ⟨owner, .resume⟩ resumeDemand []) resumeRow := by
  let initial := OwnerPhaseTransitions.available (ownedTickets (.live owner inputType answerType capture caller tail))
  let callerContext := OwnerPhases.ofStack tables (.live owner inputType answerType capture caller tail)
  change OwnerPhaseTransitions.spend initial owner = before at phases
  have consumed : before owner = .consumed := phases ▸ OwnerPhaseTransitions.spend_self initial owner
  have selectedBody : Checked ((⟨owner, .resume⟩, ⟨resumeDemand, capturedRequirements⟩) :: records)
      callerContext before capturedRequirements resumeRow := by
    apply RecursiveTransport.checked_transport savedCheck (fun _ _ => rfl)
    simp only [callerContext, OwnerPhases.ofStack, RecursiveTransport.normalize, consumed, if_true]
  have ready : initial owner = .available := by simp [initial, ownedTickets, OwnerPhaseTransitions.available]
  have trace : OwnerPhaseTransitions.Trace initial (owner :: resumeDemand)
      (OwnerPhaseTransitions.spendAll before resumeDemand) :=
    .cons ready (phases.symm ▸ RecursiveRequirements.checked_trace savedCheck)
  change Checked _ callerContext initial (.invoke ⟨owner, .resume⟩ resumeDemand []) resumeRow
  apply Checked.invoke (body := capturedRequirements) (by simp [RecursiveRequirements.lookup])
    (PhaseRechecking.check_owners_iff.mpr (by simpa only [OwnerPhaseTransitions.spendAll, phases] using trace))
    (by simpa only [List.nil_append, callerContext, OwnerPhases.ofStack] using
      (OwnerPhases.Consumes.hit (owner := owner) (held := ProtectionContexts.protectedMode capture.erase)
        (rest := OwnerPhases.ofStack tables tail)))
  simpa only [List.nil_append, phases] using selectedBody

/-- A structurally checked clause joins the actual fresh boundary and its
    surviving caller. The current source-collected store offers resume only;
    disposal authentication and admission of handler tables remain separate. -/
theorem fresh_clause_configuration_transport
    (known : contracts owner = some contract)
    (source : SourceTemplates.Segment operations policy contracts tables world
      (.live owner inputType answerType capture caller tail) contract.answer output tailDemand
      (.sequence (.spent owner) tailRequirements)
      ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: records))
    (savedCheck : Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: records)
      (OwnerPhases.ofStack tables tail) before capturedRequirements contract.resumeRow)
    (tailCheck : Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: records) []
      (OwnerPhaseTransitions.spendAll before contract.resumeDemand) tailRequirements tailRow)
    (phases : OwnerPhaseTransitions.spend
      (OwnerPhaseTransitions.available (ownedTickets (.live owner inputType answerType capture caller tail))) owner = before)
    (unique : (ownedTickets (.live owner inputType answerType capture caller tail)).Nodup)
    (resumeOnly : contract.closeRow = none)
    (clause : Owners.Derives operations policy contracts
      (OwnerPhases.ofStack tables (.live owner inputType answerType capture caller tail)) world
      environment allowed (.ticket binder owner)
      (OwnerPhaseTransitions.available (ownedTickets (.live owner inputType answerType capture caller tail)))
      code after contract.answer clauseDemand clauseRow)
    (closeSource : ∀ demand requirements,
      SourceTemplates.Expression operations policy contracts world allowed (.ticket binder owner) environment
        code contract.answer demand requirements →
      SourceTemplates.Expression operations policy contracts world allowed (.ticket binder owner) Environment.empty
        nextCode contract.answer demand requirements)
    (completed : after owner = .consumed)
    (accepted : checkFootprint outside (clauseRow ++ tailRow) = true) :
    SourceTemplates.CheckedConfiguration operations policy contracts tables world outside (.ticket binder owner)
      nextCode (.live owner inputType answerType capture caller tail) output
      ((owner :: contract.resumeDemand) ++ tailDemand) (clauseRow ++ tailRow) := by
  let initial := OwnerPhaseTransitions.available (ownedTickets (.live owner inputType answerType capture caller tail))
  change OwnerPhaseTransitions.spend initial owner = before at phases
  have sameDemand := consuming_demand clause known resumeOnly
    (by simp [OwnerPhaseTransitions.available, ownedTickets]) completed
  subst clauseDemand
  have invocation := fresh_resume_check savedCheck phases
  obtain ⟨requirements, current, currentCheck⟩ := compile clause known invocation
    (fun closingRow closable => by rw [resumeOnly] at closable; cases closable) (fun _ => rfl)
  have consumed : before owner = .consumed := phases ▸ OwnerPhaseTransitions.spend_self initial owner
  have afterOwner : OwnerPhaseTransitions.spendAll before contract.resumeDemand owner = .consumed :=
    OwnerPhaseTransitions.trace_monotone (RecursiveRequirements.checked_trace savedCheck) consumed
  have pending : Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: records) []
      (OwnerPhaseTransitions.spendAll initial (owner :: contract.resumeDemand))
      (.sequence (.spent owner) tailRequirements) tailRow := by
    have combined := Checked.sequence
      (Checked.spent (store := ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: records))
        (receiving := []) afterOwner) tailCheck
    simpa only [OwnerPhaseTransitions.spendAll, phases, List.nil_append] using combined
  exact .checked (.checked (closeSource _ _ current) (.bound (Owners.ports_lookup known)) source) unique
    (.sequence (RecursiveRequirements.checked_prepend_iff.mpr
      (by simpa only [List.append_nil] using currentCheck)) pending) accepted

theorem fresh_clause_configuration
    (known : contracts owner = some contract)
    (source : SourceTemplates.Segment operations policy contracts tables world
      (.live owner inputType answerType capture caller tail) contract.answer output tailDemand
      (.sequence (.spent owner) tailRequirements)
      ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: records))
    (savedCheck : Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: records)
      (OwnerPhases.ofStack tables tail) before capturedRequirements contract.resumeRow)
    (tailCheck : Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: records) []
      (OwnerPhaseTransitions.spendAll before contract.resumeDemand) tailRequirements tailRow)
    (phases : OwnerPhaseTransitions.spend
      (OwnerPhaseTransitions.available (ownedTickets (.live owner inputType answerType capture caller tail))) owner = before)
    (unique : (ownedTickets (.live owner inputType answerType capture caller tail)).Nodup)
    (resumeOnly : contract.closeRow = none)
    (clause : Owners.Derives operations policy contracts
      (OwnerPhases.ofStack tables (.live owner inputType answerType capture caller tail)) world
      Environment.empty allowed (.ticket binder owner)
      (OwnerPhaseTransitions.available (ownedTickets (.live owner inputType answerType capture caller tail)))
      code after contract.answer clauseDemand clauseRow)
    (completed : after owner = .consumed)
    (accepted : checkFootprint outside (clauseRow ++ tailRow) = true) :
    SourceTemplates.CheckedConfiguration operations policy contracts tables world outside (.ticket binder owner)
      code (.live owner inputType answerType capture caller tail) output
      ((owner :: contract.resumeDemand) ++ tailDemand) (clauseRow ++ tailRow) :=
  fresh_clause_configuration_transport known source savedCheck tailCheck phases unique resumeOnly clause
    (fun _ _ current => current) completed accepted

theorem fresh_substituted_clause_configuration
    (known : contracts owner = some contract)
    (source : SourceTemplates.Segment operations policy contracts tables world
      (.live owner inputType answerType capture caller tail) contract.answer output tailDemand
      (.sequence (.spent owner) tailRequirements)
      ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: records))
    (savedCheck : Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: records)
      (OwnerPhases.ofStack tables tail) before capturedRequirements contract.resumeRow)
    (tailCheck : Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: records) []
      (OwnerPhaseTransitions.spendAll before contract.resumeDemand) tailRequirements tailRow)
    (phases : OwnerPhaseTransitions.spend
      (OwnerPhaseTransitions.available (ownedTickets (.live owner inputType answerType capture caller tail))) owner = before)
    (unique : (ownedTickets (.live owner inputType answerType capture caller tail)).Nodup)
    (resumeOnly : contract.closeRow = none)
    (clause : Owners.Derives operations policy contracts
      (OwnerPhases.ofStack tables (.live owner inputType answerType capture caller tail)) world
      (Environment.empty.extend parameter argument) allowed (.ticket binder owner)
      (OwnerPhaseTransitions.available (ownedTickets (.live owner inputType answerType capture caller tail)))
      code after contract.answer clauseDemand clauseRow)
    (operand : SourceTemplates.ValueSummary operations policy contracts world Environment.empty allowed value argument)
    (closed : ClosedValue value)
    (completed : after owner = .consumed)
    (accepted : checkFootprint outside (clauseRow ++ tailRow) = true) :
    SourceTemplates.CheckedConfiguration operations policy contracts tables world outside (.ticket binder owner)
      (code.subst parameter value) (.live owner inputType answerType capture caller tail) output
      ((owner :: contract.resumeDemand) ++ tailDemand) (clauseRow ++ tailRow) :=
  fresh_clause_configuration_transport known source savedCheck tailCheck phases unique resumeOnly clause
    (fun _ _ current => SourceCallableSubstitution.substitution current operand closed) completed accepted

namespace Examples
open SharedSourceSegments.Examples
  (operations policy contracts contract tables capture effect operation_known owner_known)
open RecursiveCapture.Examples (captureRequirements captured_source captured_check)
open OwnerPhaseTransitions (available empty)

def boundary : Stack := .live 19 .integer .boolean capture .none .nil
def records : RecursiveRequirements.Store := [(⟨19, .resume⟩, ⟨[], captureRequirements⟩)]
def raw : Footprint := [⟨effect, 0, false⟩]
def outside : ProtectionContracts.Context := [.handler effect 41 [(0, ⟨false, some [], some []⟩)]]
def clause : Code := .bind 3 (.perform (Instantiation.freezeEffect effect) 0 .unit)
  (.bind 4 (.branch (.boolean true) (.resume 7 (.integer 17)) (.resume 7 (.integer 18)))
    (.bind 5 (.perform (Instantiation.freezeEffect effect) 0 .unit) (.boolean true)))

theorem boundary_source : SourceTemplates.Segment operations policy contracts tables [] boundary .boolean .boolean []
    (.sequence (.spent 19) (.request [] [])) records :=
  .live owner_known rfl rfl ⟨.none, .none⟩ rfl captured_source .nil

theorem saved_check : Checked records [] empty captureRequirements [] :=
  RecursiveCapture.checked_insert_consumed (captured_check (receiving := []) (before := empty)) rfl

theorem phase_return : OwnerPhaseTransitions.spend (available (ownedTickets boundary)) 19 = empty := by
  funext other
  simp [boundary, capture, ownedTickets, available, OwnerPhaseTransitions.spend, empty]

theorem request_source : Owners.Derives operations policy contracts (OwnerPhases.ofStack tables boundary)
    [] environment [effect] (.ticket 7 19) phases (.perform (Instantiation.freezeEffect effect) 0 .unit)
    phases .integer [] raw := by
  refine .perform operation_known List.mem_cons_self
    (.stable (row := []) .unit (by simp [OwnerSource.exportAt, residual_empty])) (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources]) ?_
  change residualize (if phases 19 = .available then [.barrier false] else []) raw = some raw
  split <;> rfl

theorem resume_source : Owners.Derives operations policy contracts (OwnerPhases.ofStack tables boundary)
    [] environment [effect] (.ticket 7 19) (available (ownedTickets boundary)) (.resume 7 (.integer value))
    empty .boolean [19] [] := by
  exact .resume (policy := policy) owner_known (by simp [Execution.Scope.resolve]) rfl (.stable (row := []) .integer (by simp [OwnerSource.exportAt, residual_empty]))
    (OwnerPhaseTransitions.trace_all_owned (List.Perm.refl _) (by decide)) (List.nil_subset _)
    (by simp [contract, ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])

theorem clause_source : Owners.Derives operations policy contracts (OwnerPhases.ofStack tables boundary)
    [] Environment.empty [effect] (.ticket 7 19) (available (ownedTickets boundary)) clause
    empty .boolean [19] (raw ++ raw) := by
  exact .bind request_source (.bind (.branch
    (.stable (row := []) .boolean (by simp [OwnerSource.exportAt, residual_empty])) resume_source resume_source)
    (.bind request_source (.stable (row := []) .boolean (by simp [OwnerSource.exportAt, residual_empty]))))

theorem clause_checked : SourceTemplates.CheckedConfiguration operations policy contracts tables [] outside (.ticket 7 19)
    clause boundary .boolean [19] (raw ++ raw) := by
  exact fresh_clause_configuration (clauseRow := raw ++ raw) (tailRow := []) owner_known boundary_source saved_check
    (Checked.request (raw := []) (nearer := []) (row := []) (by simp [OwnerSource.exportAt, residual_empty])) phase_return (by decide) rfl
    clause_source rfl (by decide)

theorem duplicate_resume_rejected :
    ¬ Owners.Derives operations policy contracts (OwnerPhases.ofStack tables boundary)
      [] Environment.empty [effect] (.ticket 7 19) before
      (.bind 4 (.resume 7 (.integer 17)) (.resume 7 (.integer 18))) after result demand row := by
  intro source
  exact Owners.sequential_resume_rejected source rfl

end Examples

end Ash.OneShot.RecursiveClauses

#print axioms Ash.OneShot.RecursiveClauses.resolved_owner
#print axioms Ash.OneShot.RecursiveClauses.available_unchanged
#print axioms Ash.OneShot.RecursiveClauses.entry_after
#print axioms Ash.OneShot.RecursiveClauses.compile
#print axioms Ash.OneShot.RecursiveClauses.demand_shape
#print axioms Ash.OneShot.RecursiveClauses.consuming_demand
#print axioms Ash.OneShot.RecursiveClauses.fresh_resume_check
#print axioms Ash.OneShot.RecursiveClauses.fresh_clause_configuration
#print axioms Ash.OneShot.RecursiveClauses.Examples.boundary_source
#print axioms Ash.OneShot.RecursiveClauses.Examples.saved_check
#print axioms Ash.OneShot.RecursiveClauses.Examples.phase_return
#print axioms Ash.OneShot.RecursiveClauses.Examples.request_source
#print axioms Ash.OneShot.RecursiveClauses.Examples.resume_source
#print axioms Ash.OneShot.RecursiveClauses.Examples.clause_source
#print axioms Ash.OneShot.RecursiveClauses.Examples.clause_checked
#print axioms Ash.OneShot.RecursiveClauses.Examples.duplicate_resume_rejected

#print axioms Ash.OneShot.RecursiveClauses.fresh_clause_configuration_transport
#print axioms Ash.OneShot.RecursiveClauses.fresh_substituted_clause_configuration
