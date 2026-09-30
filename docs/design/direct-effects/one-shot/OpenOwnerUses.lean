import OwnedPhaseRows

/-!
Outside-owner obligations of a captured stack, derived from structural runtime
usage. The interface is separate from effect rows and plan availability. With
the existing ownership separation it is equivalent to the internal-use premise
needed by disposal. Open phase/effect interpretation remains a separate join.
-/

namespace Ash.OneShot.OpenOwnerUses
open ScopedExpressions ScopedExecution
open CallableProtection ProtectionContracts
open CallableProtectionFrames (Tables contextOf)

def externalUses (stack : Stack) (demand : List Nat) : List Nat :=
  demand.filter fun owner => !(ownedTickets stack).contains owner

theorem external_member : owner ∈ externalUses stack demand ↔ owner ∈ demand ∧ owner ∉ ownedTickets stack := by
  simp [externalUses]

theorem external_empty_iff : externalUses stack demand = [] ↔ demand ⊆ ownedTickets stack := by
  constructor
  · intro empty owner present
    by_cases owned : owner ∈ ownedTickets stack
    · exact owned
    · have found := external_member.mpr ⟨present, owned⟩
      rw [empty] at found
      cases found
  · intro included
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro owner member
    obtain ⟨present, absent⟩ := external_member.mp member
    exact absent (included present)

theorem external_access (runtime : StackUsage policy tickets stack outside demand) :
    externalUses stack demand ⊆ outside := by
  intro owner member
  obtain ⟨present, absent⟩ := external_member.mp member
  exact (List.mem_append.mp (stack_demand_access_bound runtime present)).resolve_left absent

theorem active_live (stack : Stack) : activeTickets stack ⊆ stack.erase.liveTickets := by
  induction stack with
  | nil => exact List.Subset.refl _
  | push frame rest ih => exact ih
  | live owner input answer saved scope rest ihSaved ihRest =>
      intro name member
      rcases List.mem_cons.mp member with same | later
      · exact List.mem_cons.mpr (Or.inl same)
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ihRest later))
  | spent owner answer scope rest ih => exact ih

theorem frame_pending_active (runtime : FrameDemand policy tickets frame demand) :
    frame.erase.pending ⊆ frameActiveDemand frame demand := by
  cases runtime with
  | plain source =>
      rename_i plain
      intro owner present
      exact (translated_demand_membership source plain.translated owner).mpr present
  | handler | cell | armed | running | closing | retiring => exact List.nil_subset _

theorem pending_demand (runtime : StackUsage policy tickets stack outside demand) : stack.erase.pending ⊆ demand := by
  induction runtime with
  | nil => exact List.nil_subset _
  | push frame accessible rest ih =>
      intro owner member
      rcases List.mem_append.mp member with here | later
      · exact List.mem_append_left _ (frame_active_demand_subset _ _ (frame_pending_active frame here))
      · exact List.mem_append_right _ (ih later)
  | live known scope saved rest ihSaved ihRest =>
      intro owner member
      rcases List.mem_append.mp member with here | later
      · exact List.mem_append_left _ (ihSaved here)
      · exact List.mem_append_right _ (ihRest later)
  | spent known scope rest ih => exact ih

theorem pending_access (runtime : StackUsage policy tickets stack outside demand) :
    stack.erase.pending ⊆ stack.erase.liveTickets ++ outside := by
  induction runtime with
  | nil => exact List.nil_subset _
  | push frame accessible rest ih =>
      intro owner member
      rcases List.mem_append.mp member with here | later
      · rcases List.mem_append.mp (accessible (frame_pending_active frame here)) with active | external
        · exact List.mem_append_left _ (active_live _ active)
        · exact List.mem_append_right _ external
      · exact ih later
  | live known scope saved rest ihSaved ihRest =>
      intro owner member
      rcases List.mem_append.mp member with here | later
      · rcases List.mem_append.mp (ihSaved here) with inside | external
        · exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_append_left _ inside))
        · rcases List.mem_append.mp external with active | outer
          · exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_append_right _ (active_live _ active)))
          · exact List.mem_append_right _ outer
      · rcases List.mem_append.mp (ihRest later) with inside | external
        · exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_append_right _ inside))
        · exact List.mem_append_right _ external
  | spent known scope rest ih => exact ih

theorem internal_of_subset (included : pending ⊆ owned) : InternalUses owned pending := by
  induction pending with
  | nil => exact .nil
  | cons owner rest ih =>
    exact .cons owner rest (included List.mem_cons_self)
      (ih (fun _ member => included (List.mem_cons_of_mem _ member)))

/-- Internal retirement is counted as ownership but supplies no outside access.
    Separation excludes a forged alias between it and an outside live owner. -/
theorem external_empty_internal
    (runtime : StackUsage policy tickets stack outside demand)
    (separate : ∀ owner ∈ ownedTickets stack, owner ∉ outside)
    (empty : externalUses stack demand = []) : InternalUses stack.erase.liveTickets stack.erase.pending := by
  apply internal_of_subset
  intro owner pending
  have owned := external_empty_iff.mp empty (pending_demand runtime pending)
  exact (List.mem_append.mp (pending_access runtime pending)).resolve_right (separate owner owned)

theorem internal_external_empty (runtime : StackUsage policy tickets stack outside demand)
    (internal : InternalUses stack.erase.liveTickets stack.erase.pending) : externalUses stack demand = [] :=
  external_empty_iff.mpr (internally_demanded_tickets_are_owned runtime internal)

theorem external_empty_iff_internal (runtime : StackUsage policy tickets stack outside demand)
    (separate : ∀ owner ∈ ownedTickets stack, owner ∉ outside) :
    externalUses stack demand = [] ↔ InternalUses stack.erase.liveTickets stack.erase.pending :=
  ⟨external_empty_internal runtime separate, internal_external_empty runtime⟩

structure Interface (policy : Syntax.TicketPolicy) (tickets : Syntax.UsageTickets) (capture : Stack) (outside : List Nat) where
  demand : List Nat
  source : StackUsage policy tickets capture outside demand

def Interface.external (interface : Interface policy tickets capture outside) : List Nat := externalUses capture interface.demand

theorem capture_interface (cut : HandlerCut requested whole capture tail handler)
    (runtime : StackUsage policy tickets whole outside demand) :
    ∃ (interface : Interface policy tickets capture (activeTickets tail ++ outside)) (remaining : List Nat),
      demand = interface.demand ++ remaining ∧ StackUsage policy tickets tail outside remaining ∧
      interface.external ⊆ activeTickets tail ++ outside := by
  rw [handler_cut_reconstructs cut] at runtime
  obtain ⟨inside, remaining, same, saved, rest⟩ := stack_usage_decompose runtime
  exact ⟨⟨inside, saved⟩, remaining, same, rest, external_access saved⟩

theorem capture_tail_separate {front capture tail : Stack}
    (unique : (ownedTickets (front.append (.live owner input answer capture caller tail))).Nodup) :
    ∀ name ∈ ownedTickets capture, name ∉ activeTickets tail := by
  rw [owned_tickets_append] at unique
  have after := (List.nodup_append.mp unique).2.1
  have middle := (List.nodup_cons.mp after).2
  have disjoint := (List.nodup_append.mp middle).2.2
  intro name owned active
  exact disjoint name owned name (active_tickets_owned tail active) rfl

/-- The new source interface supplies exactly the old ownership premise;
    physical plan construction and all other disposal conditions stay separate. -/
theorem discard_usage {front capture tail : Stack}
    (before : ConfigurationUsage policy tickets
      ⟨.discard binder, scope, front.append (.live owner input answer capture caller tail)⟩)
    (interface : Interface policy tickets capture (activeTickets tail))
    (empty : interface.external = []) (resolved : scope.resolve binder = some owner)
    (built : makePlan capture = some plan) :
    ConfigurationUsage policy tickets
      ⟨.unit, scope, (closeControl scope plan).append
        (.push (.closing closeId scope) (front.append (.spent owner answer caller tail)))⟩ := by
  obtain ⟨current, control, code, stack, available, balance, unique⟩ := before
  have separated := capture_tail_separate unique
  exact discard_preserves_configuration_usage ⟨current, control, code, stack, available, balance, unique⟩
    resolved built (external_empty_internal interface.source separated empty)

theorem outside_use_blocks_internal (interface : Interface policy tickets capture outside)
    (present : owner ∈ interface.external) : ¬ InternalUses capture.erase.liveTickets capture.erase.pending := by
  intro internal
  have empty := internal_external_empty interface.source internal
  change owner ∈ externalUses capture interface.demand at present
  rw [empty] at present
  cases present

theorem restore_interface {front capture tail : Stack}
    (interface : Interface policy tickets capture (activeTickets tail)) :
    ∃ restored : Interface policy tickets capture (activeTickets (front.append (.spent owner answer caller tail))),
      restored.demand = interface.demand ∧ restored.external = interface.external := by
  have source : StackUsage policy tickets capture (activeTickets (front.append (.spent owner answer caller tail))) interface.demand := by
    apply stack_usage_external_weaken interface.source
    intro name present
    rw [active_tickets_append]
    exact List.mem_append_right _ present
  exact ⟨⟨interface.demand, source⟩, rfl, rfl⟩

theorem restore_usage {capture waiting : Stack}
    (interface : Interface policy tickets capture (activeTickets waiting))
    (caller : StackUsage policy tickets waiting [] callerDemand) :
    StackUsage policy tickets (capture.append waiting) [] (interface.demand ++ callerDemand) := by
  apply stack_usage_append (by simpa only [List.append_nil] using interface.source) caller

theorem capture_linear_interface
    (runtime : ConfigurationUsage policy tickets ⟨.perform effect operation operand, scope, whole⟩)
    (cut : HandlerCut requested whole capture tail handler) (isValue : operand.IsValue) :
    ∃ interface : Interface policy tickets capture (activeTickets tail),
      interface.demand.Nodup ∧ interface.external.Nodup ∧ interface.external ⊆ activeTickets tail ∧
      (interface.external = [] ↔ InternalUses capture.erase.liveTickets capture.erase.pending) := by
  obtain ⟨current, control, code, stack, accessible, balance, unique⟩ := runtime
  have empty := perform_value_demand_empty code isValue
  rw [empty, List.nil_append] at balance
  obtain ⟨saved, remaining, same, rest, available⟩ := capture_interface cut stack
  let interface : Interface policy tickets capture (activeTickets tail) :=
    ⟨saved.demand, by simpa only [List.append_nil] using saved.source⟩
  have linear : saved.demand.Nodup := (List.nodup_append.mp (same ▸ balance.symm.nodup unique)).1
  have separated : ∀ name ∈ ownedTickets capture, name ∉ activeTickets tail := by
    rw [handler_cut_reconstructs cut, owned_tickets_append] at unique
    have distinct := (List.nodup_append.mp unique).2.2
    intro name inside outside
    exact distinct name inside name (active_tickets_owned _ outside) rfl
  exact ⟨interface, linear, linear.filter _, external_access interface.source,
    external_empty_iff_internal interface.source separated⟩

theorem frame_owned (frame : ExecFrame) (tail : Stack) :
    ownedTickets (.push frame tail) = ownedTickets (.push frame .nil) ++ ownedTickets tail := by
  cases frame <;> rfl

theorem ordinary_frame_internal
    (source : SavedFrameRequirements.FrameSource operations frame row)
    (runtime : FrameDemand policy tickets frame demand) : demand ⊆ ownedTickets (.push frame .nil) := by
  cases source with
  | plain summary =>
      let ticket : ClauseProtection.Ticket := ⟨0, .scalar, .scalar, false, [], []⟩
      have phase := ClauseProtectionFrames.stable_context (ticket := ticket) (policy := policy) summary
        (NeutralFrameRows.consumed_export_empty_inside _)
      rw [PhaseFrameUsage.unchanged_frame_demand_empty phase runtime]
      exact List.nil_subset _
  | handler | cell | armed | running | closing | retiring => cases runtime <;> exact List.Subset.refl _

theorem ordinary_sources_internal
    (source : SavedFrameRequirements.Sources operations stack)
    (runtime : StackUsage policy tickets stack outside demand) : demand ⊆ ownedTickets stack := by
  induction source generalizing outside demand with
  | nil => cases runtime; exact List.Subset.refl _
  | push source rest ih => cases runtime with
      | push frame accessible remaining =>
          rw [frame_owned]
          exact ScopedExpressions.append_subset (ordinary_frame_internal source frame) (ih remaining)
  | live saved rest ihSaved ihRest => cases runtime with
      | live known scope inside remaining =>
          exact fun _ member => List.mem_cons_of_mem _ (ScopedExpressions.append_subset (ihSaved inside) (ihRest remaining) member)
  | spent rest ih => cases runtime with
      | spent known scope remaining => exact ih remaining

theorem split_plain (runtime : StackUsage policy tickets (PhaseContextChains.stackOf frames base) outside demand) :
    ∃ first second, demand = first ++ second ∧
      StackUsage policy tickets (PhaseContextChains.stackOf frames .nil) (activeTickets base ++ outside) first ∧
      StackUsage policy tickets base outside second := by
  apply stack_usage_decompose
  simpa only [PhaseContextChains.stack_tail_append, Stack.append] using runtime

/-- The preceding row system represents only segments whose demanded owners
    are owned within them. This derives that limitation for every derivation. -/
theorem closed_rows_internal
    (source : OwnedPhaseRows.Rows operations policy tables stack row)
    (runtime : StackUsage policy tickets stack outside demand) : demand ⊆ ownedTickets stack := by
  induction source generalizing outside demand with
  | nil => cases runtime; exact List.Subset.refl _
  | push source exported rest ih => cases runtime with
      | push frame accessible remaining =>
          rw [frame_owned]
          exact ScopedExpressions.append_subset (ordinary_frame_internal source frame) (ih remaining)
  | live saved rest ih => cases runtime with
      | live known scope inside remaining =>
          exact fun _ member => List.mem_cons_of_mem _ (ScopedExpressions.append_subset (ordinary_sources_internal saved inside) (ih remaining) member)
  | spent rest ih => cases runtime with
      | spent known scope remaining => exact ih remaining
  | owned saved closing pending exported rest ihSaved ihRest =>
      obtain ⟨prefixDemand, boundaryDemand, same, frontUse, boundaryUse⟩ := split_plain runtime
      have consumed := OwnedPhaseRows.chain_consumes_actual_owner pending frontUse
      cases boundaryUse with
      | live known scope inside remaining =>
          rw [same, consumed, ChainOwnerAgreement.plain_owned]
          exact fun name member => by
            rcases List.mem_cons.mp member with current | later
            · exact List.mem_cons.mpr (Or.inl current)
            · exact List.mem_cons_of_mem _ (ScopedExpressions.append_subset (ihSaved inside) (ihRest remaining) later)

theorem closed_rows_no_external (source : OwnedPhaseRows.Rows operations policy tables capture row)
    (interface : Interface policy tickets capture outside) : interface.external = [] :=
  external_empty_iff.mpr (closed_rows_internal source interface.source)

namespace Examples

def rights : Syntax.OneShotRights := ⟨true, true⟩
def policy : Syntax.TicketPolicy := fun _ => rights
def tickets : Syntax.UsageTickets := fun _ => some rights
def operations : Operations := fun _ _ => some (.scalar, .scalar)
def inner : Instance := .user 71 []
def handled : Instance := .user 72 []
def request : Code := .perform (Instantiation.freezeEffect handled) 0 .unit
def pendingBody : Code := .bind 4 request (.resume 10 .unit)
def clauses : Clauses := .cons 0 2 20 (.resume 20 .unit) .nil
def innerHandler : HandlerData :=
  ⟨71, inner, .cons 0 1 10 (.handle (Instantiation.freezeEffect handled) pendingBody clauses) .nil, .none, .integer, rfl⟩
def localHandler : HandlerData := ⟨72, handled, clauses, .ticket 10 9, .integer, rfl⟩
def tables : Tables := fun _ => [(0, ⟨false, some [], some []⟩)]
def return17 : PlainData := ⟨.bind 3 (.integer 17), .none, .unit, .integer, [], rfl⟩
def saved : Stack := .push (.plain return17) (.push (.handler innerHandler) .nil)
def waiting : PlainData := ⟨.bind 4 (.resume 10 .unit), .ticket 10 9, .unit, .integer, [9], rfl⟩
def capture : Stack := .push (.plain waiting) (.push (.handler localHandler) .nil)
def tail : Stack := .live 9 .unit .integer saved .none .nil
def whole : Stack := capture.append tail
def callTicket : ClauseProtection.Ticket := CaptureInterfaces.ticketFor saved [] (some []) 10 .scalar .scalar

theorem waiting_source : ClauseProtectionFrames.ContextDerives operations policy callTicket
    (contextOf tables (.push (.handler localHandler) .nil)) CallableProtection.Environment.empty
    waiting.context .available .scalar .consumed .scalar [] := by
  have value : ClauseProtection.Derives operations policy callTicket
      (contextOf tables (.push (.handler localHandler) .nil)) (CallableProtection.Environment.empty.extend 4 .scalar)
      .available .unit .available .scalar [] := .stable .unit rfl
  exact .bind (.resume rfl value rfl)

theorem captured_usage : StackUsage policy tickets capture [9] [9] := by
  have frame : FrameDemand policy tickets (.plain waiting) [9] :=
    .plain (.consume rfl (.bind .unit (.resume rfl .unit)))
  have rest : StackUsage policy tickets (.push (.handler localHandler) .nil) [9] [] :=
    .push (.handler ⟨_, .bound rfl⟩ (.cons (.resume rfl .unit) .nil)) (by simp [frameActiveDemand]) .nil
  exact .push frame (by decide) rest

def interface : Interface policy tickets capture [9] := ⟨[9], captured_usage⟩

theorem outside_interface_exact : interface.external = [9] := by decide

theorem source_owner_is_outside : ∃ owner recorded,
    waiting.scope = .ticket callTicket.binder owner ∧ waiting.scope.resolve callTicket.binder = some owner ∧
      tickets owner = some recorded ∧ owner ∈ [9] := by
  simpa only [activeTickets, List.nil_append] using PhaseFrameUsage.stack_frame_owner
    (front := .nil) captured_usage waiting_source

theorem executable_plan_does_not_clear_obligation : makePlan capture = some [] ∧ interface.external = [9] :=
  ⟨rfl, outside_interface_exact⟩

theorem disposal_internal_check_rejected : ¬ InternalUses capture.erase.liveTickets capture.erase.pending :=
  outside_use_blocks_internal interface (owner := 9) (by decide)

theorem closed_row_system_rejects_open_capture : ¬ OwnedPhaseRows.Rows operations policy tables capture row := by
  intro source
  have impossible := closed_rows_no_external source interface
  rw [outside_interface_exact] at impossible
  cases impossible

theorem saved_usage (outside : List Nat) : StackUsage policy tickets saved outside [] :=
  .push (.plain (.idle .none (.bind .unit .integer))) (by simp [frameActiveDemand])
    (.push (.handler ⟨_, .none⟩
      (.cons (.handle (.bind (.perform .unit) (.resume rfl .unit)) (.cons (.resume rfl .unit) .nil)) .nil))
      (by simp [frameActiveDemand]) .nil)

theorem tail_usage : StackUsage policy tickets tail [] [] := .live rfl ⟨_, .none⟩ (saved_usage _) .nil

theorem request_usage : ConfigurationUsage policy tickets ⟨request, .ticket 10 9, whole⟩ := by
  have control : StackUsage policy tickets whole [] [9] :=
    stack_usage_append (left := capture) (leftDemand := [9]) captured_usage tail_usage
  exact ⟨[], [9], .idle (.bound rfl) (.perform .unit), control, by simp, List.Perm.refl _, by decide⟩

theorem selected_cut : HandlerCut handled whole capture tail localHandler :=
  .push (.plain waiting) _ _ _ _ (by decide) (.hit localHandler tail rfl)

theorem request_derives_linear_interface :
    ∃ checked : Interface policy tickets capture (activeTickets tail),
      checked.demand.Nodup ∧ checked.external.Nodup ∧ checked.external ⊆ activeTickets tail ∧
      (checked.external = [] ↔ InternalUses capture.erase.liveTickets capture.erase.pending) :=
  capture_linear_interface request_usage selected_cut trivial

def beforeResume : Configuration :=
  ⟨.resume 20 .unit, .ticket 20 19, .live 19 .unit .integer capture (.ticket 10 9) tail⟩
def afterResume : Configuration :=
  ⟨.unit, .ticket 20 19, capture.append (.spent 19 .integer (.ticket 10 9) tail)⟩

theorem before_resume_usage : ConfigurationUsage policy tickets beforeResume := by
  have control : StackUsage policy tickets beforeResume.stack [] [9] := by
    change StackUsage policy tickets (.live 19 .unit .integer capture (.ticket 10 9) tail) [] [9]
    exact .live rfl ⟨_, .bound rfl⟩ captured_usage tail_usage
  exact ⟨[19], [9], .consume rfl (.resume rfl .unit), control,
    by decide, List.Perm.refl _, by decide⟩

theorem open_resume_step : RawStep beforeResume afterResume [] [.ticket 19] :=
  .resume 20 19 (.ticket 20 19) (.ticket 10 9) .unit .integer .nil capture tail .unit
    CallableProtection.Examples.unit_closed rfl

theorem open_resume_preserves_usage : ConfigurationUsage policy tickets afterResume :=
  resume_preserves_configuration_usage (front := .nil) before_resume_usage rfl trivial

theorem restored_open_interface :
    ∃ restored : Interface policy tickets capture (activeTickets (.spent 19 .integer (.ticket 10 9) tail)),
      restored.demand = [9] ∧ restored.external = [9] := by
  obtain ⟨restored, same, external⟩ := restore_interface (front := .nil) (tail := tail) (capture := capture)
    (owner := 19) (answer := Ty.integer) (caller := Execution.Scope.ticket 10 9) interface
  exact ⟨restored, same, external.trans outside_interface_exact⟩

end Examples

end Ash.OneShot.OpenOwnerUses

#print axioms Ash.OneShot.OpenOwnerUses.external_member
#print axioms Ash.OneShot.OpenOwnerUses.external_empty_iff
#print axioms Ash.OneShot.OpenOwnerUses.external_access
#print axioms Ash.OneShot.OpenOwnerUses.active_live
#print axioms Ash.OneShot.OpenOwnerUses.frame_pending_active
#print axioms Ash.OneShot.OpenOwnerUses.pending_demand
#print axioms Ash.OneShot.OpenOwnerUses.pending_access
#print axioms Ash.OneShot.OpenOwnerUses.internal_of_subset
#print axioms Ash.OneShot.OpenOwnerUses.external_empty_internal
#print axioms Ash.OneShot.OpenOwnerUses.internal_external_empty
#print axioms Ash.OneShot.OpenOwnerUses.external_empty_iff_internal
#print axioms Ash.OneShot.OpenOwnerUses.capture_interface
#print axioms Ash.OneShot.OpenOwnerUses.capture_tail_separate
#print axioms Ash.OneShot.OpenOwnerUses.discard_usage
#print axioms Ash.OneShot.OpenOwnerUses.outside_use_blocks_internal
#print axioms Ash.OneShot.OpenOwnerUses.restore_interface
#print axioms Ash.OneShot.OpenOwnerUses.restore_usage
#print axioms Ash.OneShot.OpenOwnerUses.capture_linear_interface
#print axioms Ash.OneShot.OpenOwnerUses.frame_owned
#print axioms Ash.OneShot.OpenOwnerUses.ordinary_frame_internal
#print axioms Ash.OneShot.OpenOwnerUses.ordinary_sources_internal
#print axioms Ash.OneShot.OpenOwnerUses.split_plain
#print axioms Ash.OneShot.OpenOwnerUses.closed_rows_internal
#print axioms Ash.OneShot.OpenOwnerUses.closed_rows_no_external
#print axioms Ash.OneShot.OpenOwnerUses.Examples.waiting_source
#print axioms Ash.OneShot.OpenOwnerUses.Examples.captured_usage
#print axioms Ash.OneShot.OpenOwnerUses.Examples.outside_interface_exact
#print axioms Ash.OneShot.OpenOwnerUses.Examples.source_owner_is_outside
#print axioms Ash.OneShot.OpenOwnerUses.Examples.executable_plan_does_not_clear_obligation
#print axioms Ash.OneShot.OpenOwnerUses.Examples.disposal_internal_check_rejected
#print axioms Ash.OneShot.OpenOwnerUses.Examples.closed_row_system_rejects_open_capture
#print axioms Ash.OneShot.OpenOwnerUses.Examples.saved_usage
#print axioms Ash.OneShot.OpenOwnerUses.Examples.tail_usage
#print axioms Ash.OneShot.OpenOwnerUses.Examples.request_usage
#print axioms Ash.OneShot.OpenOwnerUses.Examples.selected_cut
#print axioms Ash.OneShot.OpenOwnerUses.Examples.request_derives_linear_interface
#print axioms Ash.OneShot.OpenOwnerUses.Examples.before_resume_usage
#print axioms Ash.OneShot.OpenOwnerUses.Examples.open_resume_step
#print axioms Ash.OneShot.OpenOwnerUses.Examples.open_resume_preserves_usage
#print axioms Ash.OneShot.OpenOwnerUses.Examples.restored_open_interface
