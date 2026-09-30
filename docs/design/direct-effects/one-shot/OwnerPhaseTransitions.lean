import PhaseResumption

/-!
Owner-indexed one-shot transitions for arbitrary finite demands. The index also
covers dormant owners retained inside captures. These transitions describe
ownership phases, not permission to commute effects or a whole source judgment.
-/

namespace Ash.OneShot.OwnerPhaseTransitions
open ScopedExpressions ScopedExecution
open Syntax (UseState)
open CallableProtectionFrames (Tables contextOf)

abbrev Phases := Nat → UseState

def spend (before : Phases) (owner : Nat) : Phases :=
  fun other => if other = owner then .consumed else before other

def spendAll : Phases → List Nat → Phases
  | before, [] => before
  | before, owner :: rest => spendAll (spend before owner) rest

def available (owners : List Nat) : Phases :=
  fun owner => if owner ∈ owners then .available else .consumed

def empty : Phases := fun _ => .consumed

/-- Each named owner must still be available when consumed. Permissions,
    lexical resolution and interpretation order remain independent checks. -/
inductive Trace : Phases → List Nat → Phases → Prop where
  | nil : Trace before [] before
  | cons (ready : before owner = .available) (rest : Trace (spend before owner) owners after) :
      Trace before (owner :: owners) after

theorem spend_self (before : Phases) (owner : Nat) : spend before owner owner = .consumed := by simp [spend]

theorem spend_other (different : other ≠ owner) : spend before owner other = before other := by simp [spend, different]

theorem spendAll_at (before : Phases) (owners : List Nat) (owner : Nat) :
    spendAll before owners owner = if owner ∈ owners then .consumed else before owner := by
  induction owners generalizing before with
  | nil => simp [spendAll]
  | cons first rest ih => simp only [spendAll, ih, List.mem_cons, spend]; split <;> simp_all

theorem trace_result (trace : Trace before owners after) : after = spendAll before owners := by
  induction trace with
  | nil => rfl
  | cons ready rest ih => exact ih

theorem trace_monotone (trace : Trace before owners after) (spent : before owner = .consumed) : after owner = .consumed := by
  rw [trace_result trace, spendAll_at]
  split <;> simp_all

theorem trace_available (trace : Trace before owners after) : ∀ owner ∈ owners, before owner = .available := by
  induction trace with
  | nil => simp
  | @cons before first rest after ready tail ih =>
      intro owner member
      rcases List.mem_cons.mp member with same | member
      · simpa only [same] using ready
      · have remaining := ih owner member
        by_cases same : owner = first
        · simp [spend, same] at remaining
        · simpa only [spend, if_neg same] using remaining

theorem trace_nodup (trace : Trace before owners after) : owners.Nodup := by
  induction trace with
  | nil => exact List.nodup_nil
  | @cons before owner rest after ready tail ih =>
      refine List.nodup_cons.mpr ⟨?_, ih⟩
      intro member
      have impossible := trace_available tail owner member
      simp [spend] at impossible

theorem trace_of_available (unique : owners.Nodup)
    (ready : ∀ owner ∈ owners, before owner = .available) : Trace before owners (spendAll before owners) := by
  induction owners generalizing before with
  | nil => exact .nil
  | cons owner rest ih =>
      obtain ⟨absent, uniqueRest⟩ := List.nodup_cons.mp unique
      refine .cons (ready owner List.mem_cons_self) (ih uniqueRest ?_)
      intro other member
      have different : other ≠ owner := fun same => absent (same ▸ member)
      rw [spend_other different]
      exact ready other (List.mem_cons_of_mem _ member)

theorem trace_iff : Trace before owners after ↔ owners.Nodup ∧
    (∀ owner ∈ owners, before owner = .available) ∧ after = spendAll before owners := by
  constructor
  · intro trace; exact ⟨trace_nodup trace, trace_available trace, trace_result trace⟩
  · rintro ⟨unique, ready, rfl⟩; exact trace_of_available unique ready

theorem trace_unique (first : Trace before owners after) (second : Trace before owners other) : after = other :=
  (trace_result first).trans (trace_result second).symm

theorem trace_append (first : Trace before left middle) (second : Trace middle right after) :
    Trace before (left ++ right) after := by
  induction first with
  | nil => exact second
  | cons ready rest ih => exact .cons ready (ih second)

theorem trace_decompose (trace : Trace before (left ++ right) after) :
    ∃ middle, Trace before left middle ∧ Trace middle right after := by
  induction left generalizing before with
  | nil => exact ⟨before, .nil, trace⟩
  | cons owner rest ih => cases trace with
      | cons ready tail =>
          obtain ⟨middle, first, second⟩ := ih tail
          exact ⟨middle, .cons ready first, second⟩

theorem trace_append_iff : Trace before (left ++ right) after ↔
    ∃ middle, Trace before left middle ∧ Trace middle right after :=
  ⟨trace_decompose, fun ⟨_, first, second⟩ => trace_append first second⟩

theorem trace_consumed (trace : Trace before owners after) (member : owner ∈ owners) : after owner = .consumed := by
  rw [trace_result trace, spendAll_at, if_pos member]

theorem trace_unchanged (trace : Trace before owners after) (absent : owner ∉ owners) : after owner = before owner := by
  rw [trace_result trace, spendAll_at, if_neg absent]

theorem trace_cannot_repeat (first : Trace before left middle) (second : Trace middle right after)
    (member : owner ∈ left) : owner ∉ right := by
  intro repeated
  have consumed := trace_consumed first member
  have ready := trace_available second owner repeated
  rw [consumed] at ready
  cases ready

/-- Permuting independent owner consumptions preserves only their final phase
    map. This theorem says nothing about effect rows or handler reordering. -/
theorem trace_permutation (trace : Trace before owners after) (same : owners.Perm reordered) :
    Trace before reordered after := by
  apply trace_iff.mpr
  refine ⟨same.nodup (trace_nodup trace), fun owner member => trace_available trace owner (same.mem_iff.mpr member), ?_⟩
  rw [trace_result trace]
  funext owner
  simp only [spendAll_at, same.mem_iff]

theorem trace_all_owned (balanced : owners.Perm owned) (unique : owned.Nodup) :
    Trace (available owned) owners empty := by
  apply trace_iff.mpr
  refine ⟨balanced.symm.nodup unique, ?_, ?_⟩
  · intro owner member
    simp [available, balanced.mem_iff.mp member]
  · funext owner
    simp only [spendAll_at, available, empty]
    by_cases member : owner ∈ owners <;> simp_all only [balanced.mem_iff, if_true, if_false]

/-- Restriction retains exactly the owners visible through an interface. -/
def restrict (before : Phases) (keep : Nat → Bool) : Phases :=
  fun owner => if keep owner then before owner else .consumed

theorem restrict_spend_kept (kept : keep owner = true) :
    restrict (spend before owner) keep = spend (restrict before keep) owner := by
  funext other
  by_cases same : other = owner <;> simp [restrict, spend, same, kept]

theorem restrict_spend_hidden (hidden : keep owner = false) :
    restrict (spend before owner) keep = restrict before keep := by
  funext other
  by_cases same : other = owner <;> simp [restrict, spend, same, hidden]

theorem trace_restrict (trace : Trace before owners after) (keep : Nat → Bool) :
    Trace (restrict before keep) (owners.filter keep) (restrict after keep) := by
  induction trace with
  | nil => exact .nil
  | @cons before owner owners after ready rest ih =>
      cases kept : keep owner with
      | false => simpa only [List.filter_cons, kept, Bool.false_eq_true, ↓reduceIte, restrict_spend_hidden kept] using ih
      | true =>
          rw [restrict_spend_kept kept] at ih
          simpa only [List.filter_cons, kept, ↓reduceIte] using
            Trace.cons (before := restrict before keep) (owner := owner) (by simp [restrict, kept, ready]) ih

/-- Every earlier single-owner protocol is a projection of the shared trace.
    The same trace supplies all projections, preventing incompatible choices of
    intermediate states for different owners. -/
theorem trace_owner_protocol (trace : Trace before owners after) (owner : Nat) :
    OwnedPhaseRows.Protocol owner (before owner) (after owner) (owners.filter (· == owner)) := by
  induction trace with
  | nil => exact .idle
  | @cons before first rest after ready remaining ih =>
      have head : OwnedPhaseRows.Protocol owner (before owner) (spend before first owner) ([first].filter (· == owner)) := by
        by_cases same : first = owner
        · subst first
          simpa only [List.filter_cons, beq_self_eq_true, ↓reduceIte, List.filter_nil, spend_self, ready] using
            OwnedPhaseRows.Protocol.consume (owner := owner)
        · simpa only [List.filter_cons, beq_iff_eq, same, ↓reduceIte, List.filter_nil, spend_other (Ne.symm same)] using
            OwnedPhaseRows.Protocol.idle (owner := owner) (phase := before owner)
      simpa only [← List.filter_append, List.singleton_append] using OwnedPhaseRows.protocol_compose head ih

theorem restrict_available (owners : List Nat) (keep : Nat → Bool) :
    restrict (available owners) keep = available (owners.filter keep) := by
  funext owner
  cases kept : keep owner <;> simp [restrict, available, List.mem_filter, kept]

theorem restrict_empty (keep : Nat → Bool) : restrict empty keep = empty := by
  funext owner
  simp [restrict, empty]

/-- Actual capture splitting determines the two demand lists. The intermediate
    phase map is derived by induction, rather than supplied as an admission
    predicate. Interior and dormant owners are included in the ownership map. -/
theorem capture_trace
    (runtime : ConfigurationUsage policy tickets ⟨.perform effect operation operand, scope, whole⟩)
    (cut : HandlerCut requested whole capture tail handler) (isValue : operand.IsValue) :
    ∃ interface : OpenOwnerUses.Interface policy tickets capture (activeTickets tail),
      ∃ remaining middle,
        StackUsage policy tickets tail [] remaining ∧
        Trace (available (ownedTickets whole)) interface.demand middle ∧
        Trace middle remaining empty ∧
        Trace (restrict (available (ownedTickets whole)) (fun owner => !(ownedTickets capture).contains owner))
          interface.external (restrict middle (fun owner => !(ownedTickets capture).contains owner)) := by
  obtain ⟨current, control, code, stack, accessible, balanced, unique⟩ := runtime
  have noCurrent := perform_value_demand_empty code isValue
  rw [noCurrent, List.nil_append] at balanced
  obtain ⟨saved, remaining, same, tailUsage, exposed⟩ := OpenOwnerUses.capture_interface cut stack
  let interface : OpenOwnerUses.Interface policy tickets capture (activeTickets tail) :=
    ⟨saved.demand, by simpa only [List.append_nil] using saved.source⟩
  have all := trace_all_owned balanced unique
  rw [same] at all
  obtain ⟨middle, captured, rest⟩ := trace_decompose all
  exact ⟨interface, remaining, middle, tailUsage, captured, rest, trace_restrict captured _⟩

/-- Interpret the fixed ordered context at the phase of each named owner.
    Ordinary layers and protected running frames retain their exact positions. -/
def project : OwnerPhases.Context → Phases → ProtectionContracts.Context
  | [], _ => []
  | .ordinary layer :: rest, phases => layer :: project rest phases
  | .live owner held :: rest, phases =>
      if phases owner = .available then .barrier held :: project rest phases else project rest phases
  | .spent _ :: rest, phases => project rest phases

def liveNames : OwnerPhases.Context → List Nat
  | [] => []
  | .ordinary _ :: rest | .spent _ :: rest => liveNames rest
  | .live owner _ :: rest => owner :: liveNames rest

theorem project_append (front tail : OwnerPhases.Context) (phases : Phases) :
    project (front ++ tail) phases = project front phases ++ project tail phases := by
  induction front with
  | nil => rfl
  | cons entry rest ih => cases entry <;> simp_all [project]; split <;> simp_all

theorem project_agrees (ready : ∀ owner ∈ liveNames context, phases owner = .available) :
    project context phases = OwnerPhases.project context := by
  induction context with
  | nil => rfl
  | cons entry rest ih => cases entry with
      | ordinary layer => exact congrArg (layer :: ·) (ih ready)
      | spent owner => exact ih ready
      | live owner held =>
          have head := ready owner (List.mem_cons_self)
          simp only [project, head, ↓reduceIte, OwnerPhases.project]
          exact congrArg (.barrier held :: ·) (ih (fun other member => ready other (List.mem_cons_of_mem _ member)))

theorem liveNames_stack (tables : Tables) (stack : Stack) : liveNames (OwnerPhases.ofStack tables stack) = activeTickets stack := by
  induction stack with
  | nil => rfl
  | push frame rest ih => cases frame <;> exact ih
  | live owner input answer saved scope rest ihSaved ihRest => exact congrArg (owner :: ·) ihRest
  | spent owner answer scope rest ih => exact ih

/-- Allocation freshness excludes an active alias in the selected handler's
receiving tail. This reuses the existing ownership decomposition of the cut. -/
theorem capture_tail_fresh
    (cut : HandlerCut requested whole capture tail handler)
    (absent : owner ∉ ownedTickets whole) :
    owner ∉ liveNames (OwnerPhases.ofStack tables tail) := by
  rw [liveNames_stack]
  intro member
  apply absent
  rw [handler_cut_reconstructs cut, owned_tickets_append]
  exact List.mem_append_right _ (active_tickets_owned tail member)

theorem project_actual (tables : Tables) (stack : Stack) :
    project (OwnerPhases.ofStack tables stack) (available (ownedTickets stack)) = contextOf tables stack := by
  rw [project_agrees, OwnerPhases.project_stack]
  intro owner member
  rw [liveNames_stack] at member
  simp [available, active_tickets_owned stack member]

/-- Spent markers do not depend on the phase map. Only an active alias of
this owner can change the surrounding interpretation when it is consumed. -/
theorem project_spend_absent_live (absent : owner ∉ liveNames context) :
    project context (spend phases owner) = project context phases := by
  induction context with
  | nil => rfl
  | cons entry rest ih => cases entry with
    | ordinary layer => exact congrArg (layer :: ·) (ih absent)
    | spent other => exact ih absent
    | live other held =>
      have different : other ≠ owner := fun same => absent (by simp [liveNames, same])
      have restAbsent : owner ∉ liveNames rest := fun member => absent (List.mem_cons_of_mem _ member)
      simp only [project, spend_other different, ih restAbsent]

theorem project_spendAll_absent_live
    (separate : ∀ owner ∈ demand, owner ∉ liveNames receiving) :
    project receiving (spendAll before demand) =
      project receiving before := by
  induction demand generalizing before with
  | nil => rfl
  | cons owner rest ih =>
      rw [spendAll, ih (fun other member => separate other (List.mem_cons_of_mem _ member))]
      exact project_spend_absent_live (separate owner List.mem_cons_self)


theorem owned_closing_demand_separate {closingDemand : List Nat} {capture tail : Stack}
    (accounting : closingDemand.Perm (ownedTickets capture))
    (unique : (ownedTickets (capture.append tail)).Nodup) :
    ∀ owner ∈ closingDemand, owner ∉ liveNames
      (OwnerPhases.ofStack tables tail) := by
  rw [owned_tickets_append] at unique
  obtain ⟨_, _, disjoint⟩ := List.nodup_append.mp unique
  intro owner member live
  rw [liveNames_stack] at live
  exact disjoint owner (accounting.mem_iff.mp member) owner
    (active_tickets_owned tail live) rfl


theorem project_after_selected_consumption
    (fresh : owner ∉ liveNames tail)
    (separate : ∀ other ∈ demand, other ∉ liveNames tail) :
    project (.live owner held :: tail) (spendAll before (owner :: demand)) =
      project tail before := by
  have consumed : spendAll before (owner :: demand) owner = Syntax.UseState.consumed := by
    simp [spendAll_at]
  simp only [project, consumed, reduceCtorEq, ↓reduceIte]
  rw [project_spendAll_absent_live (fun other member => by
    rcases List.mem_cons.mp member with same | later
    · simpa only [same] using fresh
    · exact separate other later)]


theorem owned_closing_demand_separate_at_live {closingDemand : List Nat} {capture tail : Stack}
    (accounting : closingDemand.Perm (ownedTickets capture))
    (unique : (ownedTickets (.live selected input answer capture caller tail)).Nodup) :
    ∀ owner ∈ closingDemand, owner ∉ liveNames (OwnerPhases.ofStack tables tail) := by
  apply owned_closing_demand_separate accounting
  rw [owned_tickets_append]
  exact (List.nodup_cons.mp unique).2

theorem project_spend_absent (absent : owner ∉ OwnerPhases.names context) :
    project context (spend phases owner) = project context phases := by
  induction context with
  | nil => rfl
  | cons entry rest ih => cases entry with
      | ordinary layer => exact congrArg (layer :: ·) (ih absent)
      | spent other => exact ih (fun member => absent (List.mem_cons_of_mem _ member))
      | live other held =>
          have different : other ≠ owner := fun same => absent (by simp [OwnerPhases.names, same])
          have restAbsent : owner ∉ OwnerPhases.names rest := fun member => absent (List.mem_cons_of_mem _ member)
          simp only [project, spend_other different, ih restAbsent]

/-- A physical live-to-spent update and a phase-map update interpret identically
    when owner names are distinct. This does not erase the restored capture. -/
theorem consume_project (step : OwnerPhases.Consumes owner before after)
    (unique : (OwnerPhases.names before).Nodup) :
    project before (spend phases owner) = project after phases := by
  induction step with
  | hit =>
      have absent := (List.nodup_cons.mp unique).1
      simpa [project, spend_self] using project_spend_absent (phases := phases) absent
  | ordinary next ih => exact congrArg (_ :: ·) (ih unique)
  | live different next ih =>
      have restUnique := (List.nodup_cons.mp unique).2
      simp only [project, spend_other (Ne.symm different), ih restUnique]
  | spent different next ih => exact ih (List.nodup_cons.mp unique).2

theorem capture_interpretation (cut : HandlerCut requested whole capture tail handler) (phases : Phases) :
    project (OwnerPhases.ofStack tables whole) phases =
      project (OwnerPhases.ofStack tables capture) phases ++ project (OwnerPhases.ofStack tables tail) phases := by
  rw [OwnerPhases.capture_context cut, project_append]

/-- Even when ownership phases have changed, residual interpretation still
    follows the original ordered split and uses the same shared phase map. -/
theorem capture_residual (cut : HandlerCut requested whole capture tail handler) (phases : Phases) :
    ProtectionResiduals.checkResidual (project (OwnerPhases.ofStack tables tail) phases)
      (ProtectionResiduals.residualize (project (OwnerPhases.ofStack tables capture) phases) row) =
      ProtectionContracts.checkFootprint (project (OwnerPhases.ofStack tables whole) phases) row := by
  rw [ProtectionResiduals.residual_check, capture_interpretation cut]

theorem available_permutation (same : first.Perm second) : available first = available second := by
  funext owner
  simp only [available, same.mem_iff]

theorem spend_available_cons (absent : owner ∉ rest) : spend (available (owner :: rest)) owner = available rest := by
  funext other
  by_cases same : other = owner
  · simp [spend, available, same, absent]
  · simp [spend, available, same]

section Runtime
variable {front capture tail : Stack}

/-- Restoration changes stack order, but removes exactly the resumed owner
    from ownership, including owners retained in dormant captures. -/
theorem resume_owned_permutation :
    (ownedTickets (front.append (.live owner input answer capture caller tail))).Perm
      (owner :: ownedTickets (capture.append (front.append (.spent owner answer caller tail)))) := by
  simp only [owned_tickets_append, ownedTickets]
  have moved := (List.perm_middle (a := owner) (l₁ := ownedTickets front)
    (l₂ := ownedTickets capture ++ ownedTickets tail))
  have exchanged := (List.perm_append_comm (l₁ := ownedTickets front) (l₂ := ownedTickets capture)).append_right (ownedTickets tail)
  exact moved.trans (.cons owner (by simpa only [List.append_assoc] using exchanged))

theorem resume_phase_trace
    (unique : (ownedTickets (front.append (.live owner input answer capture caller tail))).Nodup) :
    Trace (available (ownedTickets (front.append (.live owner input answer capture caller tail)))) [owner]
      (available (ownedTickets (capture.append (front.append (.spent owner answer caller tail))))) := by
  have ordered := resume_owned_permutation (front := front) (capture := capture) (tail := tail)
    (owner := owner) (input := input) (answer := answer) (caller := caller)
  have absent := (List.nodup_cons.mp (ordered.nodup unique)).1
  rw [available_permutation ordered]
  apply Trace.cons (by simp [available])
  rw [spend_available_cons absent]
  exact .nil

theorem resume_project
    (unique : (ownedTickets (front.append (.live owner input answer capture caller tail))).Nodup) :
    project (OwnerPhases.ofStack tables (capture.append (front.append (.spent owner answer caller tail))))
      (spend (available (ownedTickets (front.append (.live owner input answer capture caller tail)))) owner) =
      contextOf tables (capture.append (front.append (.spent owner answer caller tail))) := by
  have phases := trace_result (resume_phase_trace unique)
  change available (ownedTickets (capture.append (front.append (.spent owner answer caller tail)))) =
    spend (available (ownedTickets (front.append (.live owner input answer capture caller tail)))) owner at phases
  rw [← phases]
  exact project_actual tables _

/-- The shared map update accompanies the actual named resume and full joint
    invariant. There is no restriction on interior live or dormant owners. -/
theorem resume_joint
    (valid : CompletionJoint.Valid declarations policy registry ambient
      ⟨⟨⟨.resume binder value, scope, front.append (.live owner input answer capture caller tail)⟩,
        issued, completed⟩, activations⟩ result outgoing bound)
    (resolved : scope.resolve binder = some owner) (isValue : value.IsValue) (tables : Tables) :
    let before : NamedState := ⟨⟨⟨.resume binder value, scope,
      front.append (.live owner input answer capture caller tail)⟩, issued, completed⟩, activations⟩
    let after : Configuration := ⟨value, scope, capture.append (front.append (.spent owner answer caller tail))⟩
    NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [] [.ticket owner]) ∧
    CompletionJoint.Valid declarations policy registry ambient
      (ScopedPortJoint.advanceState before after [] [.ticket owner]) result outgoing bound ∧
    Trace (available (ownedTickets before.execution.configuration.stack)) [owner] (available (ownedTickets after.stack)) ∧
    project (OwnerPhases.ofStack tables after.stack)
      (spend (available (ownedTickets before.execution.configuration.stack)) owner) = contextOf tables after.stack := by
  obtain ⟨_, _, _, _, _, _, unique⟩ := valid.joint.usage
  obtain ⟨step, preserved⟩ := CompletionJoint.resume_preserves valid resolved isValue
  exact ⟨step, preserved, resume_phase_trace unique, resume_project unique⟩

end Runtime

theorem project_ordinary (inside : ProtectionContracts.Context) (phases : Phases) :
    project (inside.map OwnerPhases.Entry.ordinary) phases = inside := by
  induction inside with
  | nil => rfl
  | cons layer rest ih => exact congrArg (layer :: ·) ih

/-- Replacing the earlier pair of phases also preserves its residual effect
    interpretation. No effect-row conversion or second sequencing syntax is
    introduced by the owner-indexed representation. -/
theorem earlier_context_residual (contract : CapturedPhaseContracts.Contract) (outer : ClauseProtection.Ticket)
    (inside outside : ProtectionContracts.Context) (phases : Phases) (localOwner outerOwner : Nat) (row : ProtectionContracts.Footprint) :
    ProtectionResiduals.residualize
      (CapturedPhaseContracts.context contract outer inside ⟨phases localOwner, phases outerOwner⟩ ++ outside) row =
    ProtectionResiduals.residualize
      (project (.live localOwner contract.header.held ::
        (inside.map OwnerPhases.Entry.ordinary ++ [.live outerOwner outer.held])) phases ++ outside) row := by
  cases first : phases localOwner <;> cases second : phases outerOwner <;>
    simp only [CapturedPhaseContracts.context, ParametricClauseRows.Header.context, ParametricClauseRows.Header.ticket,
      ClauseProtection.phaseContext, ClauseProtection.ownedMode, first, second, project,
      project_append, project_ordinary, List.append_assoc, List.cons_append, List.nil_append,
      ↓reduceIte]
  all_goals simp [ProtectionResiduals.residual_append, ProtectionResiduals.residualize,
    DisposalProtection.through_barrier, ProtectionContracts.qualify]

theorem protocol_result_unique
    (first : OwnedPhaseRows.Protocol owner before after demand)
    (second : OwnedPhaseRows.Protocol owner before other demand) : after = other := by
  cases first <;> cases second <;> rfl

/-- The previous exposed-owner contract is a checked projection of the shared
    map, using source and usage evidence for the same physical capture. -/
theorem captured_contract_projection
    (interface : CapturedPhaseContracts.Interface operations policy tickets outer owner tables fixed capture outside contract)
    (trace : Trace before interface.usage.demand after)
    (starts : before owner = contract.sourcePhase) : after owner = contract.resultPhase := by
  have actual := trace_owner_protocol trace owner
  rw [starts] at actual
  exact protocol_result_unique actual
    (OpenPhaseSegments.segment_protocol interface.source interface.usage.source interface.separate)

/-- Local consumption and all captured consumptions share one map. Projecting
    onto the two earlier indices recovers their stated resumption transition. -/
theorem resumption_contract_projection
    (interface : CapturedPhaseContracts.Interface operations policy tickets outer owner tables fixed capture outside contract)
    (trace : Trace before (localOwner :: interface.usage.demand) after)
    (different : owner ≠ localOwner) (starts : before owner = contract.sourcePhase) :
    (CapturedPhaseContracts.State.mk (before localOwner) (before owner)) = ⟨.available, contract.sourcePhase⟩ ∧
    (CapturedPhaseContracts.State.mk (after localOwner) (after owner)) = ⟨.consumed, contract.resultPhase⟩ := by
  have localDone := trace_consumed trace List.mem_cons_self
  cases trace with
  | cons ready captured =>
      have outsideStart : spend before localOwner owner = contract.sourcePhase := (spend_other different).trans starts
      have outsideDone := captured_contract_projection interface captured outsideStart
      exact ⟨by rw [ready, starts], by rw [localDone, outsideDone]⟩

theorem trace_empty_iff (trace : Trace before owners after) : before = after ↔ owners = [] := by
  constructor
  · intro same
    cases trace with
    | nil => rfl
    | @cons before owner rest after ready tail =>
        have spent := trace_monotone tail (spend_self before owner)
        rw [← same, ready] at spent
        cases spent
  · intro absent
    subst owners
    cases trace
    rfl

/-- The outside interface changes exactly when at least one outside owner is
    consumed. Internal owners may still be consumed without changing it. -/
theorem external_phase_unchanged_iff
    (interface : OpenOwnerUses.Interface policy tickets capture outside)
    (trace : Trace before interface.demand after) :
    restrict before (fun owner => !(ownedTickets capture).contains owner) =
      restrict after (fun owner => !(ownedTickets capture).contains owner) ↔ interface.external = [] :=
  trace_empty_iff (trace_restrict trace _)

/-- Disposal's existing empty-outside-use premise preserves the entire outside
    map, rather than checking only one distinguished owner. -/
theorem disposal_preserves_external_map
    (interface : CapturedPhaseContracts.Interface operations policy tickets outer owner tables fixed capture outside contract)
    (trace : Trace before interface.usage.demand after)
    (closable : contract.closeRow = some bound) :
    restrict before (fun owner => !(ownedTickets capture).contains owner) =
      restrict after (fun owner => !(ownedTickets capture).contains owner) := by
  apply (external_phase_unchanged_iff interface.usage trace).mpr
  have closing := interface.closing
  rw [closable] at closing
  exact (CapturedPhaseContracts.closing_available closing).1

/-- Allocation changes a phase entry, but does not establish freshness.
    Actual allocation below retains the runtime's issued-name freshness check. -/
def introduce (before : Phases) (owner : Nat) : Phases :=
  fun other => if other = owner then .available else before other

theorem introduce_available (owners : List Nat) (owner : Nat) :
    introduce (available owners) owner = available (owner :: owners) := by
  funext other
  by_cases same : other = owner <;> simp [introduce, available, same]

theorem capture_map {whole capture tail : Stack}
    (cut : HandlerCut requested whole capture tail handler) :
    available (ownedTickets (.live owner input handler.answer capture handler.scope tail)) =
      introduce (available (ownedTickets whole)) owner := by
  rw [introduce_available, handler_cut_reconstructs cut, owned_tickets_append]
  rfl

section Capture
variable {whole capture tail : Stack} {issued completed : List Owner}

/-- Actual fresh capture retains a multi-owner phase interface across registry
    extension. The captured and surviving demands determine one intermediate
    map, including any live owners retained inside the captured stack. -/
theorem capture_joint
    (cut : HandlerCut requested whole capture tail handler)
    (valid : CompletionJoint.Valid declarations policy registry ambient
      ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩ result outgoing bound)
    (isValue : operand.IsValue) (fresh : (issued ++ [Owner.ticket owner]).Nodup) :
    ∃ (parameter binder : Nat) (body : Code) (output : ScopedPorts.Port) (record : CallableJoint.TicketRecord),
      ClauseAt operation handler.clauses parameter binder body ∧
      let before : NamedState := ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩
      let after : Configuration := ⟨body.subst parameter operand, .ticket binder owner,
        .live owner (ScopedPorts.embedPort output) handler.answer capture handler.scope tail⟩
      NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [.ticket owner] []) ∧
      CompletionJoint.Valid declarations policy (registry.insert owner record) ambient
        (ScopedPortJoint.advanceState before after [.ticket owner] []) result outgoing bound ∧
      available (ownedTickets after.stack) = introduce (available (ownedTickets whole)) owner ∧
      ∃ interface : OpenOwnerUses.Interface policy (registry.insert owner record).joint.usage capture (activeTickets tail),
        ∃ remaining middle,
          StackUsage policy (registry.insert owner record).joint.usage tail [] remaining ∧
          Trace (available (ownedTickets whole)) interface.demand middle ∧ Trace middle remaining empty := by
  obtain ⟨interface, remaining, middle, tailUsage, captured, rest, external⟩ := capture_trace valid.joint.usage cut isValue
  obtain ⟨parameter, binder, body, output, residual, record, recordEq, selected, signature,
    extension, step, preserved⟩ := CompletionJoint.capture_without_payload_premise cut valid isValue fresh
  have enlarged := CapturedPhaseContracts.registry_usage_extension extension
  let retained : OpenOwnerUses.Interface policy (registry.insert owner record).joint.usage capture (activeTickets tail) :=
    ⟨interface.demand, stack_usage_extension interface.source enlarged⟩
  exact ⟨parameter, binder, body, output, record, selected, step, preserved, capture_map cut,
    retained, remaining, middle, stack_usage_extension tailUsage enlarged, captured, rest⟩

end Capture

namespace Examples
open OpenOwnerUses.Examples (operations policy tickets tables tail localHandler)

def innerWaiting : PlainData := ⟨.bind 7 (.resume 30 .unit), .ticket 30 29, .unit, .unit, [29], rfl⟩
def capture : Stack := .push (.plain innerWaiting)
  (.live 29 .unit .unit .nil (.ticket 10 9) OpenOwnerUses.Examples.capture)
def whole : Stack := capture.append tail

theorem captured_usage : StackUsage policy tickets capture [9] [29, 9] := by
  have rest : StackUsage policy tickets (.live 29 .unit .unit .nil (.ticket 10 9) OpenOwnerUses.Examples.capture) [9] [9] :=
    .live rfl ⟨_, .bound rfl⟩ .nil OpenOwnerUses.Examples.captured_usage
  have head : FrameDemand policy tickets (.plain innerWaiting) [29] :=
    .plain (.consume rfl (.bind .unit (.resume rfl .unit)))
  exact .push head (by decide) rest

def interface : OpenOwnerUses.Interface policy tickets capture [9] := ⟨[29, 9], captured_usage⟩

theorem internal_and_external : ownedTickets capture = [29] ∧ interface.external = [9] := ⟨rfl, rfl⟩

theorem selected_cut : HandlerCut OpenOwnerUses.Examples.handled whole capture tail localHandler :=
  .push (.plain innerWaiting) _ _ _ _ (by decide)
    (.live 29 .unit .unit .nil (.ticket 10 9) _ _ _ _ OpenOwnerUses.Examples.selected_cut)

theorem request_usage : ConfigurationUsage policy tickets
    ⟨OpenOwnerUses.Examples.request, .ticket 30 29, whole⟩ := by
  have stack : StackUsage policy tickets whole [] [29, 9] :=
    stack_usage_append (left := capture) (leftDemand := [29, 9]) captured_usage OpenOwnerUses.Examples.tail_usage
  exact ⟨[], [29, 9], .idle (.bound rfl) (.perform .unit), stack, by simp, List.Perm.refl _, by decide⟩

theorem captured_transition : Trace (available (ownedTickets whole)) interface.demand empty :=
  trace_all_owned (List.Perm.refl _) (by decide)

theorem captured_outside_transition : Trace
    (restrict (available (ownedTickets whole)) (fun owner => !(ownedTickets capture).contains owner)) [9]
    (restrict empty (fun owner => !(ownedTickets capture).contains owner)) := trace_restrict captured_transition _

theorem old_segment_excludes_live_group :
    ¬ OpenPhaseSegments.Segment operations policy ticket owner tables fixed capture before input after output row := by
  intro source
  have noOwners := OpenPhaseSegments.segment_no_active_owner source
  cases noOwners

def beforeResume : Configuration :=
  ⟨.resume 20 .unit, .ticket 20 19, .live 19 .unit .integer capture (.ticket 10 9) tail⟩
def afterResume : Configuration :=
  ⟨.unit, .ticket 20 19, capture.append (.spent 19 .integer (.ticket 10 9) tail)⟩

theorem actual_resume : RawStep beforeResume afterResume [] [.ticket 19] :=
  .resume 20 19 (.ticket 20 19) (.ticket 10 9) .unit .integer .nil capture tail .unit
    CallableProtection.Examples.unit_closed rfl

theorem before_resume_usage : ConfigurationUsage policy tickets beforeResume := by
  have stack : StackUsage policy tickets beforeResume.stack [] [29, 9] := by
    change StackUsage policy tickets (.live 19 .unit .integer capture (.ticket 10 9) tail) [] [29, 9]
    exact .live rfl ⟨_, .bound rfl⟩ captured_usage OpenOwnerUses.Examples.tail_usage
  exact ⟨[19], [29, 9], .consume rfl (.resume rfl .unit), stack, by decide, List.Perm.refl _, by decide⟩

theorem after_resume_usage : ConfigurationUsage policy tickets afterResume :=
  resume_preserves_configuration_usage (front := .nil) before_resume_usage rfl trivial

theorem actual_phase_transition : Trace (available (ownedTickets beforeResume.stack)) [19]
    (available (ownedTickets afterResume.stack)) := resume_phase_trace (front := .nil) (by decide)

theorem remaining_owners : available (ownedTickets afterResume.stack) 19 = .consumed ∧
    available (ownedTickets afterResume.stack) 29 = .available ∧
    available (ownedTickets afterResume.stack) 9 = .available := by decide

theorem all_three_owners : Trace (available (ownedTickets beforeResume.stack)) [19, 29, 9] empty :=
  trace_append actual_phase_transition (trace_all_owned (List.Perm.refl _) (by decide))

theorem duplicate_owner_rejected : ¬ Trace (available [19, 29, 9]) [19, 29, 19, 9] after := by
  intro trace
  have unique := trace_nodup trace
  simp at unique

theorem restored_interpretation :
    project (OwnerPhases.ofStack tables afterResume.stack) (spend (available (ownedTickets beforeResume.stack)) 19) =
      contextOf tables afterResume.stack := resume_project (front := .nil) (by decide)

theorem earlier_contract_recovered :
    CapturedPhaseContracts.State.mk ((available [19, 9]) 19) ((available [19, 9]) 9) = CapturedPhaseContracts.Examples.initial ∧
    CapturedPhaseContracts.State.mk (empty 19) (empty 9) = CapturedPhaseContracts.Examples.completed :=
  resumption_contract_projection CapturedPhaseContracts.Examples.openInterface
    (trace_all_owned (List.Perm.refl _) (by decide)) (by decide) rfl

end Examples

end Ash.OneShot.OwnerPhaseTransitions

#print axioms Ash.OneShot.OwnerPhaseTransitions.spend_self
#print axioms Ash.OneShot.OwnerPhaseTransitions.spend_other
#print axioms Ash.OneShot.OwnerPhaseTransitions.spendAll_at
#print axioms Ash.OneShot.OwnerPhaseTransitions.trace_result
#print axioms Ash.OneShot.OwnerPhaseTransitions.trace_monotone
#print axioms Ash.OneShot.OwnerPhaseTransitions.trace_available
#print axioms Ash.OneShot.OwnerPhaseTransitions.trace_nodup
#print axioms Ash.OneShot.OwnerPhaseTransitions.trace_of_available
#print axioms Ash.OneShot.OwnerPhaseTransitions.trace_iff
#print axioms Ash.OneShot.OwnerPhaseTransitions.trace_unique
#print axioms Ash.OneShot.OwnerPhaseTransitions.trace_append
#print axioms Ash.OneShot.OwnerPhaseTransitions.trace_decompose
#print axioms Ash.OneShot.OwnerPhaseTransitions.trace_append_iff
#print axioms Ash.OneShot.OwnerPhaseTransitions.trace_consumed
#print axioms Ash.OneShot.OwnerPhaseTransitions.trace_unchanged
#print axioms Ash.OneShot.OwnerPhaseTransitions.trace_cannot_repeat
#print axioms Ash.OneShot.OwnerPhaseTransitions.trace_permutation
#print axioms Ash.OneShot.OwnerPhaseTransitions.trace_all_owned
#print axioms Ash.OneShot.OwnerPhaseTransitions.restrict_spend_kept
#print axioms Ash.OneShot.OwnerPhaseTransitions.restrict_spend_hidden
#print axioms Ash.OneShot.OwnerPhaseTransitions.trace_restrict
#print axioms Ash.OneShot.OwnerPhaseTransitions.trace_owner_protocol
#print axioms Ash.OneShot.OwnerPhaseTransitions.restrict_available
#print axioms Ash.OneShot.OwnerPhaseTransitions.restrict_empty
#print axioms Ash.OneShot.OwnerPhaseTransitions.capture_trace
#print axioms Ash.OneShot.OwnerPhaseTransitions.project_append
#print axioms Ash.OneShot.OwnerPhaseTransitions.project_agrees
#print axioms Ash.OneShot.OwnerPhaseTransitions.liveNames_stack
#print axioms Ash.OneShot.OwnerPhaseTransitions.project_actual
#print axioms Ash.OneShot.OwnerPhaseTransitions.project_spend_absent
#print axioms Ash.OneShot.OwnerPhaseTransitions.consume_project
#print axioms Ash.OneShot.OwnerPhaseTransitions.capture_interpretation
#print axioms Ash.OneShot.OwnerPhaseTransitions.capture_residual
#print axioms Ash.OneShot.OwnerPhaseTransitions.available_permutation
#print axioms Ash.OneShot.OwnerPhaseTransitions.spend_available_cons
#print axioms Ash.OneShot.OwnerPhaseTransitions.resume_owned_permutation
#print axioms Ash.OneShot.OwnerPhaseTransitions.resume_phase_trace
#print axioms Ash.OneShot.OwnerPhaseTransitions.resume_project
#print axioms Ash.OneShot.OwnerPhaseTransitions.resume_joint
#print axioms Ash.OneShot.OwnerPhaseTransitions.project_ordinary
#print axioms Ash.OneShot.OwnerPhaseTransitions.earlier_context_residual
#print axioms Ash.OneShot.OwnerPhaseTransitions.protocol_result_unique
#print axioms Ash.OneShot.OwnerPhaseTransitions.captured_contract_projection
#print axioms Ash.OneShot.OwnerPhaseTransitions.resumption_contract_projection
#print axioms Ash.OneShot.OwnerPhaseTransitions.trace_empty_iff
#print axioms Ash.OneShot.OwnerPhaseTransitions.external_phase_unchanged_iff
#print axioms Ash.OneShot.OwnerPhaseTransitions.disposal_preserves_external_map
#print axioms Ash.OneShot.OwnerPhaseTransitions.introduce_available
#print axioms Ash.OneShot.OwnerPhaseTransitions.capture_map
#print axioms Ash.OneShot.OwnerPhaseTransitions.capture_joint
#print axioms Ash.OneShot.OwnerPhaseTransitions.Examples.captured_usage
#print axioms Ash.OneShot.OwnerPhaseTransitions.Examples.internal_and_external
#print axioms Ash.OneShot.OwnerPhaseTransitions.Examples.selected_cut
#print axioms Ash.OneShot.OwnerPhaseTransitions.Examples.request_usage
#print axioms Ash.OneShot.OwnerPhaseTransitions.Examples.captured_transition
#print axioms Ash.OneShot.OwnerPhaseTransitions.Examples.captured_outside_transition
#print axioms Ash.OneShot.OwnerPhaseTransitions.Examples.old_segment_excludes_live_group
#print axioms Ash.OneShot.OwnerPhaseTransitions.Examples.actual_resume
#print axioms Ash.OneShot.OwnerPhaseTransitions.Examples.before_resume_usage
#print axioms Ash.OneShot.OwnerPhaseTransitions.Examples.after_resume_usage
#print axioms Ash.OneShot.OwnerPhaseTransitions.Examples.actual_phase_transition
#print axioms Ash.OneShot.OwnerPhaseTransitions.Examples.remaining_owners
#print axioms Ash.OneShot.OwnerPhaseTransitions.Examples.all_three_owners
#print axioms Ash.OneShot.OwnerPhaseTransitions.Examples.duplicate_owner_rejected
#print axioms Ash.OneShot.OwnerPhaseTransitions.Examples.restored_interpretation
#print axioms Ash.OneShot.OwnerPhaseTransitions.Examples.earlier_contract_recovered

#print axioms Ash.OneShot.OwnerPhaseTransitions.project_spend_absent_live

#print axioms Ash.OneShot.OwnerPhaseTransitions.capture_tail_fresh
