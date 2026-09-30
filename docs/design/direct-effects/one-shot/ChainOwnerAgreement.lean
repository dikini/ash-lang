import PhaseContextChains

/-!
Derive the owner of a source chain's unique consumption from the existing
runtime ownership balance. No second owner registry or scope-admission
predicate is assumed. The active prefix consists of plain frames; other
interpretation boundaries still require source-invariant integration.
-/

namespace Ash.OneShot.ChainOwnerAgreement
open ScopedExpressions ScopedExecution CallableProtection ProtectionContracts
open ClauseProtection (Ticket Derives)
open ClauseProtectionFrames (ContextDerives)
open PhaseContextChains (Chain Source stackOf)
open Syntax (UseState)

/-- A projection of existing source and runtime derivations, not a new
    admission premise. The consumed phase cannot become available again. -/
inductive Demand : UseState → UseState → List Nat → Prop where
  | idle : Demand phase phase []
  | consume : Demand .available .consumed [owner]

theorem demand_compose (first : Demand before middle left) (second : Demand middle after right) :
    Demand before after (left ++ right) := by
  cases first <;> cases second <;> first | exact .idle | exact .consume

theorem demand_unchanged (demand : Demand phase phase names) : names = [] := by
  cases demand
  rfl

theorem demand_consuming (demand : Demand .available .consumed names) : ∃ owner, names = [owner] := by
  cases demand
  exact ⟨_, rfl⟩

theorem demand_member (demand : Demand before after names) (present : owner ∈ names) :
    before = .available ∧ after = .consumed ∧ names = [owner] := by
  cases demand with
  | idle => cases present
  | consume =>
      have same := List.mem_singleton.mp present
      exact ⟨rfl, rfl, same ▸ rfl⟩

theorem demand_of_code
    (source : Derives operations policy ticket inside environment before code after contract row)
    (runtime : CodeDemand policy tickets scope code names) : Demand before after names := by
  have usage := ClauseProtection.derives_usage source
  have monotone := ClauseProtection.phase_monotone source
  cases before <;> cases after
  · rw [PhaseFrameUsage.unchanged_code_demand_empty usage runtime]; exact .idle
  · obtain ⟨owner, rights, _, _, same⟩ := PhaseFrameUsage.consuming_code_owner usage runtime
    rw [same]; exact .consume
  · cases monotone rfl
  · rw [PhaseFrameUsage.unchanged_code_demand_empty usage runtime]; exact .idle

theorem demand_of_context
    (source : ContextDerives operations policy ticket inside environment plain.context before input after output row)
    (runtime : FrameDemand policy tickets (.plain plain) names) : Demand before after names := by
  have monotone := ClauseProtectionFrames.context_phase_monotone source
  cases before <;> cases after
  · rw [PhaseFrameUsage.unchanged_frame_demand_empty source runtime]; exact .idle
  · obtain ⟨owner, rights, _, _, same⟩ := PhaseFrameUsage.consuming_frame_owner source runtime
    rw [same]; exact .consume
  · cases monotone rfl
  · rw [PhaseFrameUsage.unchanged_frame_demand_empty source runtime]; exact .idle

theorem demand_of_chain
    (source : Chain operations policy ticket inside environment frames before input after output row)
    (runtime : StackUsage policy tickets (stackOf frames .nil) outside names) : Demand before after names := by
  induction source generalizing names with
  | nil => cases runtime; exact .idle
  | cons head rest ih => cases runtime with
      | push frame accessible tail => exact demand_compose (demand_of_context head frame) (ih tail)

theorem demand_of_source
    (source : Source operations policy ticket inside outside environment code frames before after output row)
    (current : CodeDemand policy tickets scope code currentNames)
    (pending : StackUsage policy tickets (stackOf frames .nil) external pendingNames) :
    Demand before after (currentNames ++ pendingNames) := by
  cases source with
  | checked currentSource chain accepted =>
      exact demand_compose (demand_of_code currentSource current) (demand_of_chain chain pending)

theorem plain_owned (frames : List PlainData) (tail : Stack) : ownedTickets (stackOf frames tail) = ownedTickets tail := by
  induction frames with
  | nil => rfl
  | cons frame rest ih => exact ih

theorem plain_active (frames : List PlainData) (tail : Stack) : activeTickets (stackOf frames tail) = activeTickets tail := by
  induction frames with
  | nil => rfl
  | cons frame rest ih => exact ih

/-- A live boundary's saved capture receives only the outside active owners;
    the boundary's own owner cannot be demanded inside that dormant capture. -/
theorem live_boundary_demand_excludes_owner
    (runtime : StackUsage policy tickets (.live owner input answer capture caller tail) [] names)
    (unique : (ownedTickets (.live owner input answer capture caller tail)).Nodup) : owner ∉ names := by
  have absent := (List.nodup_cons.mp unique).1
  cases runtime with
  | live known scope saved rest =>
      intro present
      rcases List.mem_append.mp present with captured | waiting
      · rcases List.mem_append.mp (stack_demand_access_bound saved captured) with owned | accessible
        · exact absent (List.mem_append_left _ owned)
        · exact absent (List.mem_append_right _ (active_tickets_owned tail (by simpa using accessible)))
      · have owned := stack_demand_access_bound rest waiting
        exact absent (List.mem_append_right _ (by simpa using owned))

/-- Split the current expression and active plain prefix from the same runtime
    usage derivation. Saved captures and the outside tail remain in baseNames. -/
theorem source_demand_decompose
    (source : Source operations policy ticket inside outside environment code frames before after output row)
    (runtime : ConfigurationUsage policy tickets ⟨code, scope, stackOf frames base⟩) :
    ∃ currentNames pendingNames baseNames,
      CodeDemand policy tickets scope code currentNames ∧
      StackUsage policy tickets (stackOf frames .nil) (activeTickets base) pendingNames ∧
      StackUsage policy tickets base [] baseNames ∧
      Demand before after (currentNames ++ pendingNames) ∧
      ((currentNames ++ pendingNames) ++ baseNames).Perm (ownedTickets base) ∧
      (ownedTickets base).Nodup := by
  obtain ⟨currentNames, controlNames, current, control, accessible, balance, unique⟩ := runtime
  have split : StackUsage policy tickets ((stackOf frames .nil).append base) [] controlNames := by
    simpa only [PhaseContextChains.stack_tail_append, Stack.append] using control
  obtain ⟨pendingNames, baseNames, same, pending, baseUse⟩ := stack_usage_decompose split
  have pendingUse : StackUsage policy tickets (stackOf frames .nil) (activeTickets base) pendingNames := by
    simpa only [List.append_nil] using pending
  refine ⟨currentNames, pendingNames, baseNames, current, pendingUse, baseUse,
    demand_of_source source current pendingUse, ?_, ?_⟩
  · simpa only [same, List.append_assoc, plain_owned] using balance
  · simpa only [plain_owned] using unique

/-- Ownership forces the one allowed source consumption to be the actual live
    boundary's owner. The source's final consumed phase is a conclusion. -/
theorem live_source_consumes_owner
    (source : Source operations policy ticket inside outside environment code frames .available after output row)
    (runtime : ConfigurationUsage policy tickets
      ⟨code, scope, stackOf frames (.live owner input answer capture caller tail)⟩) :
    after = .consumed ∧ ∃ currentNames pendingNames baseNames,
      CodeDemand policy tickets scope code currentNames ∧
      StackUsage policy tickets (stackOf frames .nil)
        (activeTickets (.live owner input answer capture caller tail)) pendingNames ∧
      StackUsage policy tickets (.live owner input answer capture caller tail) [] baseNames ∧
      currentNames ++ pendingNames = [owner] := by
  obtain ⟨currentNames, pendingNames, baseNames, current, pending, baseUse, demand, balance, unique⟩ :=
    source_demand_decompose source runtime
  have excluded := live_boundary_demand_excludes_owner baseUse unique
  have owned : owner ∈ ownedTickets (.live owner input answer capture caller tail) := by simp [ownedTickets]
  have present := balance.mem_iff.mpr owned
  have here : owner ∈ currentNames ++ pendingNames := (List.mem_append.mp present).resolve_right excluded
  obtain ⟨_, finalPhase, same⟩ := demand_member demand here
  exact ⟨finalPhase, currentNames, pendingNames, baseNames, current, pending, baseUse, same⟩

/-- Every consuming source frame in the prefix contributes its actual scope's
    owner to that prefix's existing runtime demand. -/
theorem member_frame_owner
    (runtime : StackUsage policy tickets (stackOf frames .nil) outside names)
    (member : plain ∈ frames)
    (source : ContextDerives operations policy ticket inside environment plain.context
      .available input .consumed output row) :
    ∃ owner, plain.scope.resolve ticket.binder = some owner ∧ owner ∈ names := by
  induction frames generalizing names with
  | nil => cases member
  | cons head rest ih => cases runtime with
      | push frame accessible tail =>
          rcases List.mem_cons.mp member with same | later
          · subst head
            obtain ⟨owner, rights, scopeEq, _, demandEq⟩ := PhaseFrameUsage.consuming_frame_owner source frame
            exact ⟨owner, by simp [scopeEq, Execution.Scope.resolve], by simp [demandEq]⟩
          · obtain ⟨owner, resolved, present⟩ := ih tail later
            exact ⟨owner, resolved, List.mem_append_right _ present⟩

theorem live_source_pending_owner
    (source : Source operations policy ticket inside outside environment code frames .available after output row)
    (runtime : ConfigurationUsage policy tickets
      ⟨code, scope, stackOf frames (.live owner input answer capture caller tail)⟩)
    (member : plain ∈ frames)
    (consumes : ContextDerives operations policy ticket otherInside otherEnvironment plain.context
      .available frameInput .consumed frameOutput frameRow) :
    plain.scope.resolve ticket.binder = some owner := by
  obtain ⟨_, currentNames, pendingNames, baseNames, current, pending, baseUse, same⟩ :=
    live_source_consumes_owner source runtime
  obtain ⟨actual, resolved, present⟩ := member_frame_owner pending member consumes
  have included : actual ∈ currentNames ++ pendingNames := List.mem_append_right _ present
  rw [same] at included
  exact List.mem_singleton.mp included ▸ resolved

theorem live_source_current_owner
    (source : Source operations policy ticket inside outside environment code frames .available after output row)
    (runtime : ConfigurationUsage policy tickets
      ⟨code, scope, stackOf frames (.live owner input answer capture caller tail)⟩)
    (consumes : Uses policy (.ticket ticket.binder rights) .available code .consumed) :
    scope.resolve ticket.binder = some owner := by
  obtain ⟨_, currentNames, pendingNames, baseNames, current, pending, baseUse, same⟩ :=
    live_source_consumes_owner source runtime
  obtain ⟨actual, recorded, scopeEq, _, demandEq⟩ := PhaseFrameUsage.consuming_code_owner consumes current
  have included : actual ∈ currentNames ++ pendingNames := by simp [demandEq]
  rw [same] at included
  have ownerEq := List.mem_singleton.mp included
  simp [scopeEq, Execution.Scope.resolve, ownerEq]

theorem live_resume_owner
    (source : Source operations policy ticket inside outside environment (.resume ticket.binder value)
      frames .available after output row)
    (runtime : ConfigurationUsage policy tickets
      ⟨.resume ticket.binder value, scope, stackOf frames (.live owner input answer capture caller tail)⟩) :
    scope.resolve ticket.binder = some owner := by
  apply live_source_current_owner source runtime
  cases source with
  | checked current pending accepted => cases current with
      | stable summary exported => cases summary
      | resume allowed operand exported => exact .resume allowed (ClauseProtection.derives_usage operand)

theorem live_discard_owner
    (source : Source operations policy ticket inside outside environment (.discard ticket.binder)
      frames .available after output row)
    (runtime : ConfigurationUsage policy tickets
      ⟨.discard ticket.binder, scope, stackOf frames (.live owner input answer capture caller tail)⟩) :
    scope.resolve ticket.binder = some owner := by
  apply live_source_current_owner source runtime
  cases source with
  | checked current pending accepted => cases current with
      | stable summary exported => cases summary
      | discard allowed unprotected exported => exact .discard allowed

/-- A consumed source segment retains no runtime continuation demand, even if
    its idle saved scopes still name historical owners. -/
theorem consumed_source_demands_empty
    (source : Source operations policy ticket inside outside environment code frames .consumed after output row)
    (runtime : ConfigurationUsage policy tickets ⟨code, scope, stackOf frames base⟩) :
    after = .consumed ∧ ∃ currentNames pendingNames baseNames,
      CodeDemand policy tickets scope code currentNames ∧
      StackUsage policy tickets (stackOf frames .nil) (activeTickets base) pendingNames ∧
      StackUsage policy tickets base [] baseNames ∧ currentNames = [] ∧ pendingNames = [] := by
  obtain ⟨currentNames, pendingNames, baseNames, current, pending, baseUse, demand, balance, unique⟩ :=
    source_demand_decompose source runtime
  have consumed : after = .consumed := by
    cases after
    · cases demand
    · rfl
  subst after
  have empty := List.append_eq_nil_iff.mp (demand_unchanged demand)
  exact ⟨rfl, currentNames, pendingNames, baseNames, current, pending, baseUse, empty⟩

/-- Resumption now derives the source binder's runtime owner from ownership
    balance. Its saved source suffix starts consumed; full source preservation
    through arbitrary captured interpretation frames remains a separate task. -/
theorem resume_joint
    (valid : CompletionJoint.Valid declarations policy registry ambient
      ⟨⟨⟨.resume ticket.binder value, scope, stackOf frames (.live owner input answer capture caller tail)⟩,
        issued, completed⟩, activations⟩ result outgoing bound)
    (source : Source operations policy ticket inside outside environment (.resume ticket.binder value)
      frames .available after output row)
    (isValue : value.IsValue) :
    let initial : NamedState := ⟨⟨⟨.resume ticket.binder value, scope,
      stackOf frames (.live owner input answer capture caller tail)⟩, issued, completed⟩, activations⟩
    let next : Configuration := ⟨value, scope, capture.append (stackOf frames (.spent owner answer caller tail))⟩
    NamedAccessStep ambient initial (ScopedPortJoint.advanceState initial next [] [.ticket owner]) ∧
      CompletionJoint.Valid declarations policy registry ambient
        (ScopedPortJoint.advanceState initial next [] [.ticket owner]) result outgoing bound ∧
      ∃ remaining, Chain operations policy ticket inside environment frames .consumed ticket.answer after output remaining ∧
        checkFootprint outside remaining = true := by
  have resolved := live_resume_owner source valid.joint.usage
  have beforeValid : CompletionJoint.Valid declarations policy registry ambient
      ⟨⟨⟨.resume ticket.binder value, scope,
        (stackOf frames .nil).append (.live owner input answer capture caller tail)⟩,
        issued, completed⟩, activations⟩ result outgoing bound := by
    simpa only [PhaseContextChains.stack_tail_append, Stack.append] using valid
  obtain ⟨step, nextValid⟩ := CompletionJoint.resume_preserves beforeValid resolved isValue
  refine ⟨?_, ?_, PhaseContextChains.pending_after_resume source⟩
  · simpa only [PhaseContextChains.stack_tail_append, Stack.append] using step
  · simpa only [PhaseContextChains.stack_tail_append, Stack.append] using nextValid

theorem live_source_requires_available
    (source : Source operations policy ticket inside outside environment code frames before after output row)
    (runtime : ConfigurationUsage policy tickets
      ⟨code, scope, stackOf frames (.live owner input answer capture caller tail)⟩) :
    before = .available ∧ after = .consumed := by
  obtain ⟨currentNames, pendingNames, baseNames, current, pending, baseUse, demand, balance, unique⟩ :=
    source_demand_decompose source runtime
  have excluded := live_boundary_demand_excludes_owner baseUse unique
  have owned : owner ∈ ownedTickets (.live owner input answer capture caller tail) := by simp [ownedTickets]
  have here := (List.mem_append.mp (balance.mem_iff.mpr owned)).resolve_right excluded
  exact (demand_member demand here).imp_right And.left

namespace Examples
open ScopedExecution.ControlUsageExamples (policy tickets waiting waiting_usage none_known terminalAt terminal_at_usage outerTail outer_tail_usage)
open PhaseFrameUsage.Examples (sourceTicket operations waiting_source)

def savedOutside : Stack := .push (.plain (waiting 11 7)) (terminalAt 18)
def liveBase : Stack := .live 5 .unit .unit savedOutside .none outerTail

theorem base_usage : StackUsage policy tickets liveBase [] [7] := by
  refine .live (captureDemand := [7]) rfl (none_known tickets) ?_ outer_tail_usage
  exact .push (waiting_usage rfl) (by simp [frameActiveDemand, activeTickets, outerTail])
    (terminal_at_usage tickets 18)

theorem pending_source : Source operations policy (sourceTicket 10) [] [] CallableProtection.Environment.empty
    .unit [waiting 10 5] .available .consumed .scalar [] := by
  have current : Derives operations policy (sourceTicket 10) [] CallableProtection.Environment.empty
      .available .unit .available .scalar [] := .stable .unit rfl
  exact Source.checked (outside := []) current
    (Chain.cons (frame := waiting 10 5) waiting_source .nil) rfl

theorem pending_usage : ConfigurationUsage policy tickets
    ⟨.unit, .none, stackOf [waiting 10 5] liveBase⟩ := by
  refine ⟨[], [5, 7], .idle .none .unit,
    .push (waiting_usage rfl) ?_ base_usage, List.nil_subset _, ?_, ?_⟩
  · simp [frameActiveDemand, activeTickets, liveBase, stackOf]
  · decide
  · decide

theorem dormant_outside_owner_is_distinct : 5 ∉ ([7] : List Nat) :=
  live_boundary_demand_excludes_owner base_usage (by decide)

theorem pending_owner_derived : (waiting 10 5).scope.resolve 10 = some 5 :=
  live_source_pending_owner pending_source pending_usage (by simp) (waiting_source (environment := .empty))

theorem live_phase_derived
    (source : Source operations policy (sourceTicket 10) inside outside environment
      .unit [waiting 10 5] before after output row) : before = .available ∧ after = .consumed :=
  live_source_requires_available source pending_usage

theorem wrong_pending_owner_rejected :
    ¬ ConfigurationUsage policy tickets ⟨.unit, .none, stackOf [waiting 10 7] liveBase⟩ := by
  intro runtime
  have current : Derives operations policy (sourceTicket 10) [] CallableProtection.Environment.empty
      .available .unit .available .scalar [] := .stable .unit rfl
  have source : Source operations policy (sourceTicket 10) [] [] CallableProtection.Environment.empty
      .unit [waiting 10 7] .available .consumed .scalar [] :=
    Source.checked (outside := []) current (Chain.cons (frame := waiting 10 7) waiting_source .nil) rfl
  have impossible := live_source_pending_owner source runtime (plain := waiting 10 7) (by simp)
    (waiting_source (environment := .empty))
  contradiction

/-- A phase-neutral source segment cannot abandon the selected live owner. -/
theorem abandoned_owner_rejected :
    ¬ ConfigurationUsage policy tickets ⟨.unit, .none, liveBase⟩ := by
  intro runtime
  have current : Derives operations policy (sourceTicket 10) [] CallableProtection.Environment.empty
      .available .unit .available .scalar [] := .stable .unit rfl
  have source : Source operations policy (sourceTicket 10) [] [] CallableProtection.Environment.empty
      .unit [] .available .available .scalar [] := Source.checked (outside := []) current .nil rfl
  have impossible := (live_source_requires_available source runtime).2
  cases impossible

theorem historical_scope_retains_no_demand : ∃ currentNames pendingNames baseNames,
    CodeDemand policy tickets .none .unit currentNames ∧
    StackUsage policy tickets (stackOf [PhaseFrameUsage.Examples.finishedFrame] .nil) [] pendingNames ∧
    StackUsage policy tickets (.spent 5 .unit .none .nil) [] baseNames ∧
    currentNames = [] ∧ pendingNames = [] := by
  have current : Derives operations policy (sourceTicket 10) [] CallableProtection.Environment.empty
      .consumed .unit .consumed .scalar [] := .stable .unit rfl
  have source : Source operations policy (sourceTicket 10) [] [] CallableProtection.Environment.empty
      .unit [PhaseFrameUsage.Examples.finishedFrame] .consumed .consumed .scalar [] :=
    Source.checked (outside := []) current
      (Chain.cons (frame := PhaseFrameUsage.Examples.finishedFrame) PhaseFrameUsage.Examples.consumed_suffix_source .nil) rfl
  exact (consumed_source_demands_empty source PhaseFrameUsage.Examples.consumed_owner_is_allowed_in_idle_saved_scope).2

namespace Joint
open CallableFrames.Examples (s1 clauseBody captured outside handler pendingFunction spent)
open CallableJoint.CaptureExample (liveState spentState initial source_enters_request)
open GenerativeFrames.Examples (declarations)
open CallableContracts.Examples (scalar)
open PhaseBoundaries.Examples (phaseTicket functionContract tables)

def resumed (plain : PlainData) : NamedState :=
  spentState ⟨.integer 17, .ticket 10 5, captured.append (.push (.plain plain) spent)⟩

/-- The actual frame is derived by focus. The resume theorem then recovers
    its owner's identity from the joined source and runtime judgments. -/
theorem callable_resume_without_owner_premise
    (valid : CompletionJoint.Valid declarations CallableJoint.CaptureExample.policy registry []
      (liveState s1) .integer [] scalar) :
    ∃ plain, NamedAccessSteps [] (liveState s1) (resumed plain) ∧
      CompletionJoint.Valid declarations CallableJoint.CaptureExample.policy registry []
        (resumed plain) .integer [] scalar ∧
      ∃ remaining, Chain PhaseBoundaries.Examples.operations CallableJoint.CaptureExample.policy (phaseTicket false)
        [] CallableProtection.Environment.empty [plain] .consumed functionContract .consumed functionContract remaining ∧
        checkFootprint (CallableProtectionFrames.contextOf tables outside) remaining = true := by
  have source : Source PhaseBoundaries.Examples.operations CallableJoint.CaptureExample.policy (phaseTicket false)
      [] (CallableProtectionFrames.contextOf tables outside) CallableProtection.Environment.empty
      clauseBody [] .available .consumed functionContract [] :=
    Source.checked (outside := CallableProtectionFrames.contextOf tables outside)
      PhaseBoundaries.Examples.clause_checked .nil (by decide)
  have focus : Focus clauseBody (.resume 10 (.integer 17)) (.bind 4 (.variable 4)) :=
    .bind (by intro impossible; cases impossible)
  obtain ⟨plain, shape, savedScope, e1, c2, _, focused⟩ := PhaseContextChains.focus_joint
    (inside := .nil) (tables := tables) valid source (PhaseBoundaries.Boundary.live rfl) focus
  obtain ⟨e2, c3, pending⟩ := resume_joint c2 focused trivial
  refine ⟨plain, ?_, ?_, pending⟩
  · simpa [resumed, ScopedPortJoint.advanceState, liveState, spentState, s1, stackOf,
      enteredActivations, clauseBody, spent, Stack.append] using (NamedAccessSteps.next e1 (.next e2 (.refl _)))
  · simpa [resumed, ScopedPortJoint.advanceState, liveState, spentState, s1, stackOf,
      enteredActivations, clauseBody, spent, Stack.append] using c3

theorem admitted_capture_and_resume : ∃ registry plain,
    NamedAccessSteps [] initial (resumed plain) ∧
      CompletionJoint.Valid declarations CallableJoint.CaptureExample.policy registry []
        (resumed plain) .integer [] scalar := by
  obtain ⟨registry, row, captureStep, capturedValid, _, _, _⟩ := PhaseBoundaries.Examples.capture_joined
  obtain ⟨plain, steps, finalValid, _⟩ := callable_resume_without_owner_premise capturedValid
  exact ⟨registry, plain, CallableJoint.execution_append source_enters_request.1 (.next captureStep steps), finalValid⟩

end Joint
end Examples

end Ash.OneShot.ChainOwnerAgreement

#print axioms Ash.OneShot.ChainOwnerAgreement.demand_compose
#print axioms Ash.OneShot.ChainOwnerAgreement.demand_unchanged
#print axioms Ash.OneShot.ChainOwnerAgreement.demand_consuming
#print axioms Ash.OneShot.ChainOwnerAgreement.demand_of_code
#print axioms Ash.OneShot.ChainOwnerAgreement.demand_of_context
#print axioms Ash.OneShot.ChainOwnerAgreement.demand_of_chain
#print axioms Ash.OneShot.ChainOwnerAgreement.demand_of_source
#print axioms Ash.OneShot.ChainOwnerAgreement.plain_owned
#print axioms Ash.OneShot.ChainOwnerAgreement.plain_active
#print axioms Ash.OneShot.ChainOwnerAgreement.live_boundary_demand_excludes_owner
#print axioms Ash.OneShot.ChainOwnerAgreement.source_demand_decompose
#print axioms Ash.OneShot.ChainOwnerAgreement.live_source_consumes_owner
#print axioms Ash.OneShot.ChainOwnerAgreement.demand_member
#print axioms Ash.OneShot.ChainOwnerAgreement.member_frame_owner
#print axioms Ash.OneShot.ChainOwnerAgreement.live_source_pending_owner
#print axioms Ash.OneShot.ChainOwnerAgreement.live_source_current_owner
#print axioms Ash.OneShot.ChainOwnerAgreement.live_resume_owner
#print axioms Ash.OneShot.ChainOwnerAgreement.live_discard_owner
#print axioms Ash.OneShot.ChainOwnerAgreement.consumed_source_demands_empty
#print axioms Ash.OneShot.ChainOwnerAgreement.resume_joint
#print axioms Ash.OneShot.ChainOwnerAgreement.live_source_requires_available
#print axioms Ash.OneShot.ChainOwnerAgreement.Examples.base_usage
#print axioms Ash.OneShot.ChainOwnerAgreement.Examples.pending_source
#print axioms Ash.OneShot.ChainOwnerAgreement.Examples.pending_usage
#print axioms Ash.OneShot.ChainOwnerAgreement.Examples.dormant_outside_owner_is_distinct
#print axioms Ash.OneShot.ChainOwnerAgreement.Examples.pending_owner_derived
#print axioms Ash.OneShot.ChainOwnerAgreement.Examples.live_phase_derived
#print axioms Ash.OneShot.ChainOwnerAgreement.Examples.wrong_pending_owner_rejected
#print axioms Ash.OneShot.ChainOwnerAgreement.Examples.abandoned_owner_rejected
#print axioms Ash.OneShot.ChainOwnerAgreement.Examples.Joint.callable_resume_without_owner_premise
#print axioms Ash.OneShot.ChainOwnerAgreement.Examples.Joint.admitted_capture_and_resume
#print axioms Ash.OneShot.ChainOwnerAgreement.Examples.historical_scope_retains_no_demand
