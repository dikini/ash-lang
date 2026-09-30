import ScopedProfiles

/-!
Internal retirement originates in recursive closure of an owned capture.
Explicit resume/dispose permissions govern clause expressions; nested completion
is delegated by the selected outer discard. Its structural origin is tracked
separately from usage, closing safety and the exactly-once ownership ledger.
-/

namespace Ash.OneShot.ScopedRetirement
open ScopedExpressions ScopedExecution

def scheduled : Stack → List Nat
  | .nil => []
  | .push (.retiring owner) rest => owner :: scheduled rest
  | .push _ rest => scheduled rest
  | .live _ _ _ saved _ rest => scheduled saved ++ scheduled rest
  | .spent _ _ _ rest => scheduled rest

theorem scheduled_append (left right : Stack) :
    scheduled (left.append right) = scheduled left ++ scheduled right := by
  induction left with
  | nil => rfl
  | push frame rest ih => cases frame <;> simp_all [Stack.append, scheduled]
  | live | spent => simp_all [Stack.append, scheduled, List.append_assoc]

theorem scheduled_close_owned (plan : List CloseEntry) (scope : Scope) :
    scheduled (closeControl scope plan) = ownedTickets (closeControl scope plan) := by
  induction plan with
  | nil => rfl
  | cons entry rest ih => cases entry <;> simp_all [closeControl, CloseEntry.frame, scheduled, ownedTickets]

/-- Existing retirement is protected, so a successfully closable capture's
    owned tickets are exactly its recursively live clause tickets. -/
theorem make_plan_owned_live (stack : Stack) (built : makePlan stack = some plan) :
    ownedTickets stack = stack.erase.liveTickets := by
  induction stack generalizing plan with
  | nil => rfl
  | push frame rest ih =>
    cases frame <;> cases known : makePlan rest <;> simp only [makePlan, known] at built
    all_goals first | cases built | skip
    all_goals exact ih known
  | live ticket q a saved scope rest ihSaved ihRest =>
    cases inside : makePlan saved <;> cases outside : makePlan rest <;>
      simp only [makePlan, inside, outside] at built
    all_goals first | cases built | skip
    simp only [ownedTickets, Stack.erase, Control.liveTickets, ihSaved inside, ihRest outside]
  | spent _ _ _ _ ih => exact ih built

theorem plan_retires_exact_live_tickets (built : makePlan capture = some plan) :
    (scheduled (closeControl scope plan)).Perm capture.erase.liveTickets := by
  rw [scheduled_close_owned, ← make_plan_owned_live capture built]
  exact make_plan_preserves_owned_tickets built

theorem scheduled_update (selected : CellUpdate identity old new before after) : scheduled after = scheduled before := by
  induction selected with
  | hit => rfl
  | push miss next ih => rename_i frame; cases frame <;> simp_all [scheduled]
  | live | spent => simp_all [scheduled]

/-- A structural delegation event, not an admission oracle: the initiating
    discard closes a capture containing this live ticket. Source permission and
    safe closure are checked separately at that discard. -/
inductive Delegates (nested : Nat) : Configuration → Configuration → Prop where
  | discard (binder owner closeId : Nat) (scope caller : Scope) (q a : Ty)
      (front capture tail : Stack) (plan : List CloseEntry)
      (resolved : scope.resolve binder = some owner)
      (built : makePlan capture = some plan)
      (contained : nested ∈ capture.erase.liveTickets) :
      Delegates nested
        ⟨.discard binder, scope, front.append (.live owner q a capture caller tail)⟩
        ⟨.unit, scope, (closeControl scope plan).append
          (.push (.closing closeId scope) (front.append (.spent owner a caller tail)))⟩

theorem raw_scheduled_origin (raw : RawStep before after created discharged)
    (member : owner ∈ scheduled after.stack) :
    owner ∈ scheduled before.stack ∨ Delegates owner before after := by
  cases raw with
  | focus | plug | bind | beta | ifTrue | ifFalse | enterHandler | leaveHandler | enterCell | leaveCell
  | enterCleanup | startCleanup | finishCleanup | leaveClause | finishClose => exact .inl member
  | retire => exact .inl (List.mem_cons_of_mem _ member)
  | capture requested operation parameter binder ticket operand body scope whole cap tail handler output cut clause closed ready =>
    left
    rw [handler_cut_reconstructs cut, scheduled_append]
    exact member
  | resume =>
    left
    simp only [scheduled_append, scheduled, List.mem_append] at member ⊢
    grind only
  | discard binder ticket closeId scope caller q a front cap tail plan resolved built =>
    simp only [scheduled_append, scheduled, List.mem_append] at member
    cases member with
    | inl new => exact .inr (.discard binder ticket closeId scope caller q a front cap tail plan resolved built
        ((plan_retires_exact_live_tickets built).mem_iff.mp new))
    | inr old =>
      left
      simp only [scheduled_append, scheduled, List.mem_append]
      grind only
  | readCell _ _ _ _ _ selected | writeCell _ _ _ _ _ _ selected =>
    exact .inl (by rwa [scheduled_update selected] at member)

/-- A trace retains its intermediate configurations as data, so occurrence
    statements refer to this execution rather than an existential reachability
    proof. Every edge is an actual raw transition. -/
inductive RecordedTrace : Configuration → Configuration → List Owner → List Owner → Type where
  | refl (configuration : Configuration) : RecordedTrace configuration configuration [] []
  | next (first : RawStep before middle created discharged)
      (rest : RecordedTrace middle after laterCreated laterDischarged) :
      RecordedTrace before after (created ++ laterCreated) (laterDischarged ++ discharged)

theorem RecordedTrace.raw : RecordedTrace before after created discharged → RawTrace before after created discharged
  | .refl configuration => .refl configuration
  | .next first rest => .next first rest.raw

theorem trace_has_recording (trace : RawTrace before after created discharged) :
    Nonempty (RecordedTrace before after created discharged) := by
  induction trace with
  | refl configuration => exact ⟨.refl configuration⟩
  | next first rest ih => obtain ⟨recorded⟩ := ih; exact ⟨.next first recorded⟩

/-- This recorded trace contains a concrete delegating discard event. -/
def DelegatedAlong (owner : Nat) : RecordedTrace before after created discharged → Prop
  | .refl _ => False
  | @RecordedTrace.next before middle _ _ after _ _ first rest =>
    Delegates owner before middle ∨ DelegatedAlong owner rest

theorem trace_scheduled_origin (trace : RecordedTrace before after created discharged)
    (member : owner ∈ scheduled after.stack) :
    owner ∈ scheduled before.stack ∨ DelegatedAlong owner trace := by
  induction trace with
  | refl => exact .inl member
  | next first rest ih =>
    cases ih member with
    | inl prior =>
      cases raw_scheduled_origin first prior with
      | inl original => exact .inl original
      | inr delegated => exact .inr (.inl delegated)
    | inr later => exact .inr (.inr later)

theorem retirement_has_prior_delegation
    (trace : RecordedTrace ⟨source, .none, .nil⟩ ⟨.unit, scope, .push (.retiring owner) tail⟩ created discharged) :
    DelegatedAlong owner trace := by
  have origin := trace_scheduled_origin trace (List.mem_cons_self (l := scheduled tail))
  cases origin with
  | inl impossible => cases impossible
  | inr delegated => exact delegated

theorem delegated_discard_requires_permission
    (delegation : Delegates nested before after)
    (used : CodeDemand policy tickets before.scope before.expression demand) :
    ∃ binder selected rights, before.expression = .discard binder ∧ before.scope.resolve binder = some selected ∧
      tickets selected = some rights ∧ rights.dispose = true := by
  cases delegation with
  | discard binder owner closeId scope caller q a front cap tail plan resolved built contained =>
    cases used with
    | idle scope used => cases used
    | consume known used =>
      cases used with
      | discard allowed => exact ⟨_, _, _, rfl, by simp [Execution.Scope.resolve], known, allowed⟩

def UsageChecksAlong (policy : Syntax.TicketPolicy) (tickets : Syntax.UsageTickets) :
    RecordedTrace before after created discharged → Prop
  | .refl _ => True
  | @RecordedTrace.next before middle made _ _ _ _ _ rest =>
    UsageChecks tickets before made ∧ UsageChecksAlong policy (advanceUsageTickets policy tickets middle made) rest

def PermittedAlong (policy : Syntax.TicketPolicy) (tickets : Syntax.UsageTickets) (nested : Nat) :
    RecordedTrace before after created discharged → Prop
  | .refl _ => False
  | @RecordedTrace.next before middle made _ _ _ _ _ rest =>
    (Delegates nested before middle ∧ ∃ binder selected rights,
      before.expression = .discard binder ∧ before.scope.resolve binder = some selected ∧
      tickets selected = some rights ∧ rights.dispose = true) ∨
    PermittedAlong policy (advanceUsageTickets policy tickets middle made) nested rest

theorem trace_delegation_has_selected_permission
    (trace : RecordedTrace before after created discharged)
    (checked : UsageChecksAlong policy tickets trace)
    (initial : ConfigurationUsage policy tickets before)
    (delegated : DelegatedAlong nested trace) : PermittedAlong policy tickets nested trace := by
  induction trace generalizing tickets with
  | refl => cases delegated
  | next first rest ih =>
    obtain ⟨currentChecks, laterChecks⟩ := checked
    cases delegated with
    | inl here =>
      obtain ⟨_, _, code, _, _, _, _⟩ := initial
      exact .inl ⟨here, delegated_discard_requires_permission here code⟩
    | inr later =>
      exact .inr (ih laterChecks (raw_step_preserves_configuration_usage first currentChecks initial) later)

def AccessAlong (ambient : List Nat) : RecordedTrace before after created discharged → Prop
  | .refl _ => True
  | @RecordedTrace.next before _ _ _ _ _ _ _ rest => AccessChecks before ambient ∧ AccessAlong ambient rest

theorem recorded_usage_checks_from_access
    (trace : RecordedTrace before after created discharged)
    (access : AccessAlong ambient trace) (history : UsageRegistryHistory tickets issued)
    (fresh : (issued ++ created).Nodup) : UsageChecksAlong policy tickets trace := by
  induction trace generalizing issued tickets with
  | refl => trivial
  | @next before middle made done after laterMade laterDone first rest ih =>
    have allFresh : ((issued ++ made) ++ laterMade).Nodup := by simpa only [List.append_assoc] using fresh
    exact ⟨usage_checks_from_allocation_and_access history (List.nodup_append.mp allFresh).1 access.1,
      ih access.2 (raw_step_preserves_usage_registry_history first history) allFresh⟩

/-- Initial usage, fresh creation history and the existing access checks derive
    selected-discard permission at the prior delegating event. No nested
    dispose flag is required. Future access establishment remains separate. -/
theorem source_retirement_has_permitted_delegation
    (trace : RecordedTrace ⟨source, .none, .nil⟩ ⟨.unit, scope, .push (.retiring owner) tail⟩ created discharged)
    (used : ScopedExpressions.Uses policy .none .available source .available)
    (access : AccessAlong ambient trace) (fresh : created.Nodup) :
    PermittedAlong policy (fun _ => Option.none) owner trace := by
  apply trace_delegation_has_selected_permission trace
  · exact recorded_usage_checks_from_access trace access (issued := [])
      (by intro owner; simp) (by simpa using fresh)
  · exact ⟨[], [], .idle .none used, .nil, List.nil_subset _, .refl [], by simp [ownedTickets]⟩
  · exact retirement_has_prior_delegation trace

theorem plan_retirement_unique (built : makePlan capture = some plan)
    (unique : (ownedTickets capture).Nodup) :
    (scheduled (closeControl scope plan)).Nodup := by
  rw [scheduled_close_owned]
  exact (make_plan_preserves_owned_tickets built).nodup_iff.mpr unique

theorem plan_retires_no_outside_ticket (built : makePlan capture = some plan)
    (outside : owner ∉ capture.erase.liveTickets) : owner ∉ scheduled (closeControl scope plan) :=
  fun member => outside ((plan_retires_exact_live_tickets built).mem_iff.mp member)

theorem recorded_no_double_completion
    (trace : RecordedTrace ⟨source, .none, .nil⟩ after created discharged)
    (fresh : created.Nodup) : discharged.Nodup := by
  have steps := raw_trace_enacts trace.raw (issued := []) (completed := []) (by simpa using fresh)
  have unique := run_no_double_completion steps (⟨.refl [], by simp [RunState.erase]⟩ : Ledger _)
  simpa only [List.append_nil] using unique

namespace Examples
open ActionRequirements
open ScopedExecution.ControlUsageExamples (abandonedTicket ticketCloseScope ticketCloseTail terminalAt terminal demoHandler)

def policy : Syntax.TicketPolicy := fun _ => resumeOnly
def tickets : Syntax.UsageTickets :=
  Syntax.UsageTickets.insert (Syntax.UsageTickets.insert (fun _ => Option.none) 3 disposeOnly) 5 resumeOnly

def before : Configuration := ⟨.discard 9, ticketCloseScope, .live 3 .unit .unit abandonedTicket .none .nil⟩
def scheduledState : Configuration := ⟨.unit, ticketCloseScope, .push (.retiring 5) ticketCloseTail⟩
def after : Configuration := ⟨.unit, ticketCloseScope, ticketCloseTail⟩

theorem inner_direct_disposal_denied : tickets 5 = some resumeOnly ∧ resumeOnly.dispose = false := ⟨rfl, rfl⟩

theorem before_usage : ConfigurationUsage policy tickets before := by
  unfold before
  refine ⟨[3], [5], .consume rfl (.discard rfl), ?_, ?_, by decide, by decide⟩
  refine .live (owner := 3) (captureDemand := [5]) (restDemand := []) rfl ⟨_, .none⟩ ?_ .nil
  · refine .push (.plain (data := ScopedExecution.ControlUsageExamples.waiting 10 5)
      (.consume rfl (.resume rfl .unit))) ?_
      (.live (policy := policy) (tickets := tickets) (owner := 5) (captureDemand := []) (restDemand := []) rfl ⟨_, .none⟩ ?_ ?_)
    · simp [frameActiveDemand, activeTickets]
    · exact .push (.handler ⟨_, .none⟩ (.cons (.resume rfl .unit) .nil)) (List.nil_subset _) .nil
    · exact .push (.handler ⟨_, .none⟩ (.cons (.resume rfl .unit) .nil)) (List.nil_subset _) .nil
  · simp [activeTickets]

theorem actual_discard : RawStep before scheduledState [.close 31] [.ticket 3] :=
  .discard 9 3 31 ticketCloseScope .none .unit .unit .nil abandonedTicket .nil [.retire 5] rfl rfl

theorem nested_retirement_delegated : Delegates 5 before scheduledState :=
  .discard 9 3 31 ticketCloseScope .none .unit .unit .nil abandonedTicket .nil [.retire 5] rfl rfl (by decide)

theorem scheduled_usage : ConfigurationUsage policy tickets scheduledState :=
  discard_preserves_configuration_usage (front := .nil) (closeId := 31)
    before_usage rfl (plan := [.retire 5]) rfl (.cons 5 [] (by decide) .nil)

theorem retirement_executes_without_inner_dispose_permission :
    tickets 5 = some resumeOnly ∧ resumeOnly.dispose = false ∧
      RawStep scheduledState after [] [.ticket 5] ∧ ConfigurationUsage policy tickets after :=
  ⟨rfl, rfl, .retire 5 ticketCloseScope ticketCloseTail,
    raw_value_step_preserves_configuration_usage (.retire 5 ticketCloseScope ticketCloseTail)
      ScopedExecution.ControlUsageExamples.closed_unit scheduled_usage⟩

def recorded_disposal : RecordedTrace before after [.close 31] [.ticket 5, .ticket 3] :=
  .next actual_discard (.next (.retire 5 ticketCloseScope ticketCloseTail) (.refl after))

theorem recorded_delegation : DelegatedAlong 5 recorded_disposal := .inl nested_retirement_delegated

theorem unrelated_ticket_has_no_plan_authority :
    7 ∉ scheduled (closeControl ticketCloseScope [.retire 5]) := by decide

end Examples

end Ash.OneShot.ScopedRetirement

#print axioms Ash.OneShot.ScopedRetirement.scheduled_append
#print axioms Ash.OneShot.ScopedRetirement.scheduled_close_owned
#print axioms Ash.OneShot.ScopedRetirement.make_plan_owned_live
#print axioms Ash.OneShot.ScopedRetirement.plan_retires_exact_live_tickets
#print axioms Ash.OneShot.ScopedRetirement.scheduled_update
#print axioms Ash.OneShot.ScopedRetirement.raw_scheduled_origin
#print axioms Ash.OneShot.ScopedRetirement.RecordedTrace.raw
#print axioms Ash.OneShot.ScopedRetirement.trace_has_recording
#print axioms Ash.OneShot.ScopedRetirement.trace_scheduled_origin
#print axioms Ash.OneShot.ScopedRetirement.retirement_has_prior_delegation
#print axioms Ash.OneShot.ScopedRetirement.delegated_discard_requires_permission
#print axioms Ash.OneShot.ScopedRetirement.trace_delegation_has_selected_permission
#print axioms Ash.OneShot.ScopedRetirement.recorded_usage_checks_from_access
#print axioms Ash.OneShot.ScopedRetirement.source_retirement_has_permitted_delegation
#print axioms Ash.OneShot.ScopedRetirement.plan_retirement_unique
#print axioms Ash.OneShot.ScopedRetirement.plan_retires_no_outside_ticket
#print axioms Ash.OneShot.ScopedRetirement.recorded_no_double_completion
#print axioms Ash.OneShot.ScopedRetirement.Examples.inner_direct_disposal_denied
#print axioms Ash.OneShot.ScopedRetirement.Examples.before_usage
#print axioms Ash.OneShot.ScopedRetirement.Examples.actual_discard
#print axioms Ash.OneShot.ScopedRetirement.Examples.nested_retirement_delegated
#print axioms Ash.OneShot.ScopedRetirement.Examples.scheduled_usage
#print axioms Ash.OneShot.ScopedRetirement.Examples.retirement_executes_without_inner_dispose_permission
#print axioms Ash.OneShot.ScopedRetirement.Examples.recorded_delegation
#print axioms Ash.OneShot.ScopedRetirement.Examples.unrelated_ticket_has_no_plan_authority
