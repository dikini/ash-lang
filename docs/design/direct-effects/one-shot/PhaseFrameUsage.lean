import SavedFrameRequirements

/-!
Source continuation phases realized by actual pending-frame usage and runtime
owners. The existing registry, active access and ownership balance supply the
evidence; source effect rows and contract alignment remain separate checks.
-/

namespace Ash.OneShot.PhaseFrameUsage
open ScopedExpressions ScopedExecution
open Syntax (UseState UseScope UseProtocol)
open ClauseProtectionFrames (ContextDerives)

/-- A nonempty one-shot protocol fixes its lexical binder independently of
    which rights record is used to check that same path. -/
theorem consuming_protocol_binder
    (source : UseProtocol (.ticket binder rights) .available actions .consumed)
    (other : UseProtocol scope before actions after) :
    ∃ otherRights, scope = .ticket binder otherRights ∧ before = .available ∧ after = .consumed := by
  cases source <;> cases other <;> exact ⟨_, rfl, rfl, rfl⟩

theorem unchanged_protocol_empty (protocol : UseProtocol scope phase actions phase) : actions = [] := by
  cases protocol
  rfl

/-- The runtime binder and owner come from CodeDemand's existing scope and
    registry lookup, rather than from a second source-to-owner registry. -/
theorem consuming_code_owner
    (source : Uses policy (.ticket binder rights) .available code .consumed)
    (runtime : CodeDemand policy tickets scope code demand) :
    ∃ owner recorded, scope = .ticket binder owner ∧ tickets owner = some recorded ∧ demand = [owner] := by
  obtain ⟨actions, path⟩ := syntax_path_exists code
  have sourceProtocol := usage_path_sound source path
  cases runtime with
  | idle known used =>
      obtain ⟨_, _, _, impossible⟩ := consuming_protocol_binder sourceProtocol (Syntax.usage_path_sound used path)
      cases impossible
  | consume known used =>
      obtain ⟨recorded, same, _, _⟩ := consuming_protocol_binder sourceProtocol (Syntax.usage_path_sound used path)
      cases same
      exact ⟨_, _, rfl, known, rfl⟩

theorem unchanged_code_demand_empty
    (source : Uses policy sourceScope phase code phase)
    (runtime : CodeDemand policy tickets scope code demand) : demand = [] := by
  obtain ⟨actions, path⟩ := syntax_path_exists code
  have empty := unchanged_protocol_empty (usage_path_sound source path)
  cases runtime with
  | idle => rfl
  | consume known used =>
      have protocol := Syntax.usage_path_sound used path
      rw [empty] at protocol
      cases protocol

theorem consuming_code_demand
    (source : Uses policy (.ticket binder rights) .available code .consumed)
    (runtime : CodeDemand policy tickets scope code demand)
    (resolved : scope.resolve binder = some owner) : demand = [owner] := by
  obtain ⟨actual, recorded, scopeEq, _, demandEq⟩ := consuming_code_owner source runtime
  have same : actual = owner := Option.some.inj (by simpa [scopeEq, Execution.Scope.resolve] using resolved)
  simpa only [same] using demandEq

theorem consuming_frame_owner
    (source : ContextDerives operations policy ticket inside environment plain.context
      .available input .consumed output row)
    (runtime : FrameDemand policy tickets (.plain plain) demand) :
    ∃ owner rights, plain.scope = .ticket ticket.binder owner ∧ tickets owner = some rights ∧ demand = [owner] := by
  cases runtime with
  | plain code => exact consuming_code_owner (ClauseProtectionFrames.context_usage source) code

theorem unchanged_frame_demand_empty
    (source : ContextDerives operations policy ticket inside environment plain.context phase input phase output row)
    (runtime : FrameDemand policy tickets (.plain plain) demand) : demand = [] := by
  cases runtime with
  | plain code => exact unchanged_code_demand_empty (ClauseProtectionFrames.context_usage source) code

theorem consuming_frame_demand
    (source : ContextDerives operations policy ticket inside environment plain.context
      .available input .consumed output row)
    (runtime : FrameDemand policy tickets (.plain plain) demand)
    (resolved : plain.scope.resolve ticket.binder = some owner) : demand = [owner] := by
  obtain ⟨actual, rights, scopeEq, _, demandEq⟩ := consuming_frame_owner source runtime
  have same : actual = owner := Option.some.inj (by simpa [scopeEq, Execution.Scope.resolve] using resolved)
  simpa only [same] using demandEq

/-- Active ticket access identifies an actual live boundary on the active
    spine. An occurrence hidden in a dormant capture cannot supply this proof. -/
theorem active_ticket_has_boundary (active : owner ∈ activeTickets stack) :
    ∃ (front : Stack) (input answer : Ty) (capture : Stack) (caller : Scope) (tail : Stack),
      stack = front.append (.live owner input answer capture caller tail) := by
  induction stack with
  | nil => cases active
  | push frame rest ih =>
      obtain ⟨front, input, answer, capture, caller, tail, same⟩ := ih active
      exact ⟨.push frame front, input, answer, capture, caller, tail, by rw [same]; rfl⟩
  | live name input answer saved caller rest ihSaved ihRest =>
      rcases List.mem_cons.mp active with same | remaining
      · subst name; exact ⟨.nil, input, answer, saved, caller, rest, rfl⟩
      · obtain ⟨front, q, a, capture, scope, tail, same⟩ := ihRest remaining
        exact ⟨.live name input answer saved caller front, q, a, capture, scope, tail, by rw [same]; rfl⟩
  | spent name answer caller rest ih =>
      obtain ⟨front, input, result, capture, scope, tail, same⟩ := ih active
      exact ⟨.spent name answer caller front, input, result, capture, scope, tail, by rw [same]; rfl⟩

variable {front middle tail : Stack} {state : RunState}

/-- Pending source consumption is realized by the same owner's live access
    below the frame or in the explicit external interface of a saved capture. -/
theorem stack_frame_owner
    (stackUse : StackUsage policy tickets (front.append (.push (.plain plain) tail)) outside demand)
    (source : ContextDerives operations policy ticket inside environment plain.context
      .available input .consumed output row) :
    ∃ owner rights, plain.scope = .ticket ticket.binder owner ∧
      plain.scope.resolve ticket.binder = some owner ∧ tickets owner = some rights ∧
      owner ∈ activeTickets tail ++ outside := by
  obtain ⟨prefixDemand, suffixDemand, same, prefixUse, suffix⟩ := stack_usage_decompose stackUse
  cases suffix with
  | push frame available rest =>
      obtain ⟨owner, rights, scopeEq, known, demandEq⟩ := consuming_frame_owner source frame
      refine ⟨owner, rights, scopeEq, ?_, known, ?_⟩
      · simp [scopeEq, Execution.Scope.resolve]
      · exact available (by simp [frameActiveDemand, demandEq])

theorem scheduled_frame_owner
    (usage : ConfigurationUsage policy tickets ⟨code, scope, front.append (.push (.plain plain) tail)⟩)
    (source : ContextDerives operations policy ticket inside environment plain.context
      .available input .consumed output row) :
    ∃ owner rights, plain.scope = .ticket ticket.binder owner ∧
      plain.scope.resolve ticket.binder = some owner ∧ tickets owner = some rights ∧
      owner ∈ activeTickets tail := by
  obtain ⟨current, control, currentCode, stackUse, accessible, balance, unique⟩ := usage
  simpa only [List.append_nil] using stack_frame_owner stackUse source

theorem scheduled_frame_live_boundary
    (usage : ConfigurationUsage policy tickets ⟨code, scope, front.append (.push (.plain plain) tail)⟩)
    (source : ContextDerives operations policy ticket inside environment plain.context
      .available input .consumed output row) :
    ∃ (owner : Nat) (rights : Syntax.OneShotRights) (inner : Stack) (q a : Ty)
      (capture : Stack) (caller : Scope) (outside : Stack),
      plain.scope = .ticket ticket.binder owner ∧ tickets owner = some rights ∧
      tail = inner.append (.live owner q a capture caller outside) := by
  obtain ⟨owner, rights, same, _, known, active⟩ := scheduled_frame_owner usage source
  obtain ⟨inner, q, a, capture, caller, outside, shape⟩ := active_ticket_has_boundary active
  exact ⟨owner, rights, inner, q, a, capture, caller, outside, same, known, shape⟩

theorem active_owner_not_completed (ledger : Ledger state.erase)
    (active : owner ∈ activeTickets state.configuration.stack) : Owner.ticket owner ∉ state.completed := by
  apply ledger_no_live_completed_alias ledger
  change Owner.ticket owner ∈ state.configuration.stack.erase.owners
  have owned := active_tickets_owned _ active
  rw [owned_tickets_project] at owned
  obtain ⟨entry, present, projection⟩ := List.mem_filterMap.mp owned
  cases entry <;> simp_all [Syntax.ticketProjection]

theorem scheduled_frame_not_completed
    (valid : CompletionJoint.Valid declarations policy registry ambient
      ⟨⟨⟨code, scope, front.append (.push (.plain plain) tail)⟩, issued, completed⟩, activations⟩ result outgoing bound)
    (source : ContextDerives operations policy ticket inside environment plain.context
      .available input .consumed output row) :
    ∃ owner, plain.scope.resolve ticket.binder = some owner ∧ Owner.ticket owner ∉ completed := by
  obtain ⟨owner, rights, _, resolved, _, active⟩ := scheduled_frame_owner valid.joint.usage source
  refine ⟨owner, resolved, active_owner_not_completed valid.joint.ledger ?_⟩
  change owner ∈ activeTickets (front.append (.push (.plain plain) tail))
  rw [active_tickets_append]
  exact List.mem_append_right _ active

/-- The two source binders may differ: it is their shared runtime owner that
    would be consumed twice. Ownership balance rules out that schedule. -/
theorem two_pending_consumptions_rejected
    (usage : ConfigurationUsage policy tickets
      ⟨code, scope, front.append (.push (.plain first) (middle.append (.push (.plain second) tail)))⟩)
    (left : ContextDerives operations policy firstTicket firstInside firstEnvironment first.context
      .available firstInput .consumed firstOutput firstRow)
    (right : ContextDerives operations policy secondTicket secondInside secondEnvironment second.context
      .available secondInput .consumed secondOutput secondRow)
    (leftOwner : first.scope.resolve firstTicket.binder = some owner)
    (rightOwner : second.scope.resolve secondTicket.binder = some owner) : False := by
  obtain ⟨current, control, currentCode, controlUse, access, balance, ownedUnique⟩ := usage
  have controlUnique := (List.nodup_append.mp (balance.symm.nodup ownedUnique)).2.1
  obtain ⟨prefixDemand, suffixDemand, same, prefixUse, suffix⟩ := stack_usage_decompose controlUse
  rw [same] at controlUnique
  have suffixUnique := (List.nodup_append.mp controlUnique).2.1
  cases suffix with
  | push firstUse firstAccess remaining =>
      have firstDemand := consuming_frame_demand left firstUse leftOwner
      rw [firstDemand, List.singleton_append] at suffixUnique
      have absent := (List.nodup_cons.mp suffixUnique).1
      obtain ⟨middleDemand, endDemand, remainingShape, middleUse, endUse⟩ := stack_usage_decompose remaining
      cases endUse with
      | push secondUse secondAccess rest =>
          have secondDemand := consuming_frame_demand right secondUse rightOwner
          exact absent (by simp [remainingShape, secondDemand])

theorem current_and_pending_consumption_rejected
    (usage : ConfigurationUsage policy tickets ⟨code, scope, front.append (.push (.plain plain) tail)⟩)
    (currentSource : Uses policy (.ticket binder rights) .available code .consumed)
    (pendingSource : ContextDerives operations policy ticket inside environment plain.context
      .available input .consumed output row)
    (currentOwner : scope.resolve binder = some owner)
    (pendingOwner : plain.scope.resolve ticket.binder = some owner) : False := by
  obtain ⟨current, control, currentCode, controlUse, access, balance, unique⟩ := usage
  have currentDemand := consuming_code_demand currentSource currentCode currentOwner
  have allUnique := balance.symm.nodup unique
  rw [currentDemand, List.singleton_append] at allUnique
  have absent := (List.nodup_cons.mp allUnique).1
  obtain ⟨frontDemand, tailDemand, same, frontUse, tailUse⟩ := stack_usage_decompose controlUse
  cases tailUse with
  | push frame accessible rest =>
      have pendingDemand := consuming_frame_demand pendingSource frame pendingOwner
      exact absent (by simp [same, pendingDemand])

namespace Examples
open ScopedExecution.ControlUsageExamples (policy tickets rights waiting waiting_usage nestedFront outerTail
  nestedBefore nested_configuration_usage terminal)
open CallableProtection ProtectionContracts

def operations : Operations := fun _ _ => some (.scalar, .scalar)
def sourceTicket (binder : Nat) : ClauseProtection.Ticket := ⟨binder, .scalar, .scalar, false, [], []⟩

theorem waiting_source : ContextDerives operations policy (sourceTicket binder) [] environment
    (waiting binder owner).context .available .scalar .consumed .scalar [] := .resume rfl rfl

theorem nested_waiting_owner_is_live :
    ∃ owner recorded, (waiting 10 5).scope = .ticket 10 owner ∧
      (waiting 10 5).scope.resolve 10 = some owner ∧ tickets owner = some recorded ∧
      owner ∈ activeTickets
        (.live 5 .unit .unit (.push (.plain (waiting 11 7)) (ControlUsageExamples.terminalAt 18)) .none
          (.live 3 .unit .unit terminal .none outerTail)) :=
  scheduled_frame_owner (front := .nil) nested_configuration_usage
    (waiting_source (binder := 10) (owner := 5) (environment := .empty))

theorem source_binder_and_owner_differ : (waiting 10 5).scope.resolve 10 = some 5 ∧
    (waiting 10 5).scope.resolve 10 ≠ some 10 := by decide

theorem resuming_another_owner_preserves_waiting_access :
    ∃ owner recorded, (waiting 10 5).scope = .ticket 10 owner ∧
      (waiting 10 5).scope.resolve 10 = some owner ∧ tickets owner = some recorded ∧
      owner ∈ activeTickets
        (.live 5 .unit .unit (.push (.plain (waiting 11 7)) (ControlUsageExamples.terminalAt 18)) .none
          (.spent 3 .unit .none outerTail)) :=
  scheduled_frame_owner (front := terminal) ControlUsageExamples.nested_resume_preserves_dormant_outside_demand
    (waiting_source (binder := 10) (owner := 5) (environment := .empty))

theorem dormant_frame_uses_external_owner :
    ∃ owner recorded, (waiting 11 7).scope = .ticket 11 owner ∧
      (waiting 11 7).scope.resolve 11 = some owner ∧ tickets owner = some recorded ∧ owner ∈ [3, 7] := by
  have usage := ControlUsageExamples.nested_front_usage
  generalize demandShape : ([5, 7] : List Nat) = demand at usage
  cases usage with
  | push frame access rest => cases rest with
      | live known scope saved remaining =>
          simpa [activeTickets, ControlUsageExamples.terminalAt, sourceTicket] using stack_frame_owner (front := .nil) saved
            (waiting_source (binder := 11) (owner := 7) (environment := .empty))

theorem pending_consumption_cannot_use_spent_owner :
    ¬ ConfigurationUsage policy tickets
      ⟨.unit, .none, .push (.plain (waiting 10 5)) (.spent 5 .unit .none .nil)⟩ := by
  intro usage
  obtain ⟨owner, recorded, scopeEq, _, _, active⟩ := scheduled_frame_owner (front := .nil) usage
    (waiting_source (binder := 10) (owner := 5) (environment := .empty))
  cases active

theorem two_binders_cannot_schedule_same_owner_twice :
    ¬ ConfigurationUsage policy tickets
      ⟨.unit, .none, .push (.plain (waiting 10 5))
        (.push (.plain (waiting 20 5)) (.live 5 .unit .unit terminal .none .nil))⟩ := by
  intro usage
  exact two_pending_consumptions_rejected (front := .nil) (middle := .nil) usage
    (waiting_source (binder := 10) (owner := 5) (environment := .empty))
    (waiting_source (binder := 20) (owner := 5) (environment := .empty)) rfl rfl

def branchFrame : PlainData :=
  ⟨.branch (.resume 10 .unit) (.resume 10 .unit), .ticket 10 5, .boolean, .unit, [5, 5], by decide⟩

theorem branch_source : ContextDerives operations policy (sourceTicket 10) [] CallableProtection.Environment.empty
    branchFrame.context .available .scalar .consumed .scalar [] := by
  have resumed : ClauseProtection.Derives operations policy (sourceTicket 10) [] CallableProtection.Environment.empty
      .available (.resume 10 .unit) .consumed .scalar [] := by
    have argument : ClauseProtection.Derives operations policy (sourceTicket 10) [] CallableProtection.Environment.empty
        .available .unit .available .scalar [] := .stable .unit rfl
    exact ClauseProtection.Derives.resume (resumedRow := []) rfl argument rfl
  exact .branch resumed resumed

theorem branch_consumes_once : FrameDemand policy tickets (.plain branchFrame) [5] :=
  .plain (.consume rfl (.branch .unit (.resume rfl .unit) (.resume rfl .unit)))

theorem alternative_branches_have_one_owner_demand
    (runtime : FrameDemand policy tickets (.plain branchFrame) demand) : demand = [5] :=
  consuming_frame_demand branch_source runtime rfl

def finishedFrame : PlainData := ⟨.bind 4 (.variable 4), .ticket 10 5, .unit, .unit, [], rfl⟩

theorem consumed_suffix_source : ContextDerives operations policy (sourceTicket 10) [] CallableProtection.Environment.empty
    finishedFrame.context .consumed .scalar .consumed .scalar [] :=
  .bind (.stable (.variable rfl) rfl)

theorem consumed_suffix_has_no_demand
    (runtime : FrameDemand policy tickets (.plain finishedFrame) demand) : demand = [] :=
  unchanged_frame_demand_empty consumed_suffix_source runtime

/-- A saved scope may still name a consumed owner when its remaining code has
    no demand for that owner. Requiring all saved scopes to name live owners
    would incorrectly reject this configuration. -/
theorem consumed_owner_is_allowed_in_idle_saved_scope : ConfigurationUsage policy tickets
    ⟨.unit, .none, .push (.plain finishedFrame) (.spent 5 .unit .none .nil)⟩ := by
  refine ⟨[], [], .idle .none .unit, ?_, List.nil_subset _, ?_, ?_⟩
  · exact .push (.plain (.idle (.bound rfl) (.bind .unit .variable))) (List.nil_subset _)
      (.spent rfl (ControlUsageExamples.none_known tickets) .nil)
  · decide
  · decide

theorem current_resume_cannot_duplicate_waiting_consumption :
    ¬ ConfigurationUsage policy tickets
      ⟨.resume 20 .unit, .ticket 20 5,
        .push (.plain (waiting 10 5)) (.live 5 .unit .unit terminal .none .nil)⟩ := by
  intro usage
  exact current_and_pending_consumption_rejected (front := .nil) usage
    (show Uses policy (.ticket 20 rights) .available (.resume 20 .unit) .consumed from .resume rfl .unit)
    (waiting_source (binder := 10) (owner := 5) (environment := .empty)) rfl rfl

end Examples

end Ash.OneShot.PhaseFrameUsage

#print axioms Ash.OneShot.PhaseFrameUsage.consuming_protocol_binder
#print axioms Ash.OneShot.PhaseFrameUsage.unchanged_protocol_empty
#print axioms Ash.OneShot.PhaseFrameUsage.consuming_code_owner
#print axioms Ash.OneShot.PhaseFrameUsage.unchanged_code_demand_empty
#print axioms Ash.OneShot.PhaseFrameUsage.consuming_code_demand
#print axioms Ash.OneShot.PhaseFrameUsage.consuming_frame_owner
#print axioms Ash.OneShot.PhaseFrameUsage.unchanged_frame_demand_empty
#print axioms Ash.OneShot.PhaseFrameUsage.consuming_frame_demand
#print axioms Ash.OneShot.PhaseFrameUsage.active_ticket_has_boundary
#print axioms Ash.OneShot.PhaseFrameUsage.stack_frame_owner
#print axioms Ash.OneShot.PhaseFrameUsage.scheduled_frame_owner
#print axioms Ash.OneShot.PhaseFrameUsage.scheduled_frame_live_boundary
#print axioms Ash.OneShot.PhaseFrameUsage.active_owner_not_completed
#print axioms Ash.OneShot.PhaseFrameUsage.scheduled_frame_not_completed
#print axioms Ash.OneShot.PhaseFrameUsage.two_pending_consumptions_rejected
#print axioms Ash.OneShot.PhaseFrameUsage.current_and_pending_consumption_rejected
#print axioms Ash.OneShot.PhaseFrameUsage.Examples.waiting_source
#print axioms Ash.OneShot.PhaseFrameUsage.Examples.nested_waiting_owner_is_live
#print axioms Ash.OneShot.PhaseFrameUsage.Examples.source_binder_and_owner_differ
#print axioms Ash.OneShot.PhaseFrameUsage.Examples.resuming_another_owner_preserves_waiting_access
#print axioms Ash.OneShot.PhaseFrameUsage.Examples.dormant_frame_uses_external_owner
#print axioms Ash.OneShot.PhaseFrameUsage.Examples.pending_consumption_cannot_use_spent_owner
#print axioms Ash.OneShot.PhaseFrameUsage.Examples.two_binders_cannot_schedule_same_owner_twice
#print axioms Ash.OneShot.PhaseFrameUsage.Examples.branch_source
#print axioms Ash.OneShot.PhaseFrameUsage.Examples.branch_consumes_once
#print axioms Ash.OneShot.PhaseFrameUsage.Examples.alternative_branches_have_one_owner_demand
#print axioms Ash.OneShot.PhaseFrameUsage.Examples.consumed_suffix_source
#print axioms Ash.OneShot.PhaseFrameUsage.Examples.consumed_suffix_has_no_demand
#print axioms Ash.OneShot.PhaseFrameUsage.Examples.consumed_owner_is_allowed_in_idle_saved_scope
#print axioms Ash.OneShot.PhaseFrameUsage.Examples.current_resume_cannot_duplicate_waiting_consumption
