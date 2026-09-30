import ScopedControlUsage

/-!
All-transition preservation of structural usage for scoped execution. Fresh
acquisition instantiates code while preserving its demand. The local usage
checks follow from owner allocation history and the actual access checks;
this does not derive those access checks or disposal readiness from source.
-/

namespace Ash.OneShot.ScopedExecution
open ScopedExpressions
open Syntax (TicketPolicy UsageTickets UsageScopeKnown code_demand_scope)

theorem focus_preserves_configuration_usage (plain : PlainData)
    (focus : Focus whole child plain.context)
    (before : ConfigurationUsage policy tickets ⟨whole, plain.scope, tail⟩) :
    ConfigurationUsage policy tickets ⟨child, plain.scope, .push (.plain plain) tail⟩ := by
  obtain ⟨currentDemand, controlDemand, code, control, accessible, balance, unique⟩ := before
  obtain ⟨childDemand, frameDemand, same, childCode, frameCode⟩ := focus_splits_code_demand focus code
  subst currentDemand
  refine ⟨childDemand, frameDemand ++ controlDemand, childCode, .push (.plain frameCode) ?_ control, ?_, ?_, unique⟩
  · intro owner present
    exact List.mem_append_left _ (accessible (List.mem_append_right _ present))
  · intro owner present
    exact accessible (List.mem_append_left _ present)
  · simpa only [List.append_assoc, ownedTickets] using balance

theorem branch_code_demand
    (code : CodeDemand policy tickets scope (.branch (.boolean condition) yes no) demand) :
    CodeDemand policy tickets scope yes demand ∧ CodeDemand policy tickets scope no demand := by
  cases code with
  | idle scope checked => cases checked with
      | branch condition yes no => cases condition; exact ⟨.idle scope yes, .idle scope no⟩
  | consume known checked => cases checked with
      | branch condition yes no => cases condition; exact ⟨.consume known yes, .consume known no⟩

theorem bind_preserves_configuration_usage
    (before : ConfigurationUsage policy tickets ⟨.bind parameter value body, scope, tail⟩)
    (isValue : value.IsValue) :
    ConfigurationUsage policy tickets ⟨body.subst parameter value, scope, tail⟩ := by
  obtain ⟨currentDemand, controlDemand, code, control, accessible, balance, unique⟩ := before
  exact ⟨currentDemand, controlDemand, bind_code_demand code isValue, control, accessible, balance, unique⟩

theorem branch_preserves_configuration_usage
    (before : ConfigurationUsage policy tickets ⟨.branch (.boolean condition) yes no, scope, tail⟩) :
    ConfigurationUsage policy tickets ⟨yes, scope, tail⟩ ∧
    ConfigurationUsage policy tickets ⟨no, scope, tail⟩ := by
  obtain ⟨currentDemand, controlDemand, code, control, accessible, balance, unique⟩ := before
  obtain ⟨yesCode, noCode⟩ := branch_code_demand code
  exact ⟨⟨currentDemand, controlDemand, yesCode, control, accessible, balance, unique⟩,
    ⟨currentDemand, controlDemand, noCode, control, accessible, balance, unique⟩⟩

theorem beta_preserves_configuration_usage
    (before : ConfigurationUsage policy tickets ⟨.app (.lambda parameter body) value, scope, tail⟩)
    (isValue : value.IsValue) :
    ConfigurationUsage policy tickets ⟨body.subst parameter value, .none, tail⟩ := by
  obtain ⟨currentDemand, controlDemand, code, control, accessible, balance, unique⟩ := before
  obtain ⟨same, afterCode⟩ := beta_code_demand code isValue
  subst currentDemand
  exact ⟨[], controlDemand, afterCode, control, accessible, balance, unique⟩

theorem handler_code_demand
    (code : CodeDemand policy tickets scope (.handle effectInst body clauses) demand) :
    CodeDemand policy tickets scope body demand ∧ ClausesUse policy clauses := by
  cases code with
  | idle scope checked => cases checked with
      | handle body clauses => exact ⟨.idle scope body, clauses⟩
  | consume known checked => cases checked with
      | handle body clauses => exact ⟨.consume known body, clauses⟩

theorem handler_entry_preserves_configuration_usage (handler : HandlerData)
    (before : ConfigurationUsage policy tickets
      ⟨.handle (Instantiation.freezeEffect handler.effectInst) body handler.clauses, handler.scope, tail⟩) :
    ConfigurationUsage policy tickets ⟨body, handler.scope, .push (.handler handler) tail⟩ := by
  obtain ⟨currentDemand, controlDemand, code, control, accessible, balance, unique⟩ := before
  obtain ⟨bodyCode, clauses⟩ := handler_code_demand code
  exact ⟨currentDemand, controlDemand, bodyCode,
    .push (.handler (code_demand_scope code) clauses) (List.nil_subset _) control, accessible, balance, unique⟩

theorem cell_code_demand
    (code : CodeDemand policy tickets scope (.resource identity (.integer payload) body) demand) :
    CodeDemand policy tickets scope body demand := by
  cases code with
  | idle scope checked => cases checked with
      | resource initializer body => cases initializer; exact .idle scope body
  | consume known checked => cases checked with
      | resource initializer body => cases initializer; exact .consume known body

theorem cell_entry_preserves_configuration_usage
    (before : ConfigurationUsage policy tickets ⟨.resource binder (.integer payload) body, scope, tail⟩)
    (identity : Nat) (answer : Ty) :
    ConfigurationUsage policy tickets
      ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
        .push (.cell identity payload scope answer) tail⟩ := by
  obtain ⟨currentDemand, controlDemand, code, control, accessible, balance, unique⟩ := before
  exact ⟨currentDemand, controlDemand, acquisition_preserves_code_demand code _,
    .push (.cell (code_demand_scope code)) (List.nil_subset _) control, accessible, balance, unique⟩

theorem cleanup_code_demand
    (code : CodeDemand policy tickets scope (.cleanup action body) demand) (isValue : action.IsValue) :
    CodeDemand policy tickets scope body demand ∧ Uses policy .none .available action .available := by
  cases code with
  | idle scope checked => cases checked with
      | cleanup action body =>
          have same := value_use_preserves_state isValue action
          subst same
          exact ⟨.idle scope body, value_use_transport isValue action .none .available⟩
  | consume known checked => cases checked with
      | cleanup action body =>
          have same := value_use_preserves_state isValue action
          subst same
          exact ⟨.consume known body, value_use_transport isValue action .none .available⟩

theorem cleanup_entry_preserves_configuration_usage (action : ActionData)
    (before : ConfigurationUsage policy tickets ⟨.cleanup action.action body, action.scope, tail⟩) :
    ConfigurationUsage policy tickets ⟨body, action.scope, .push (.armed action) tail⟩ := by
  obtain ⟨currentDemand, controlDemand, code, control, accessible, balance, unique⟩ := before
  obtain ⟨bodyCode, callable⟩ := cleanup_code_demand code action.closed.1
  exact ⟨currentDemand, controlDemand, bodyCode,
    .push (.armed (code_demand_scope code) callable) (List.nil_subset _) control, accessible, balance, unique⟩

theorem cell_update_active_tickets (update : CellUpdate identity old new before after) :
    activeTickets before = activeTickets after := by
  induction update <;> simp_all [activeTickets]

theorem cell_update_owned_tickets (update : CellUpdate identity old new before after) :
    ownedTickets before = ownedTickets after := by
  rw [owned_tickets_project, owned_tickets_project, cell_update_erases update]

theorem cell_update_preserves_stack_usage (update : CellUpdate identity old new before after)
    (checked : StackUsage policy tickets before outside demand) :
    StackUsage policy tickets after outside demand := by
  induction update generalizing outside demand with
  | hit => cases checked with
      | push frame accessible rest => cases frame with
          | cell scope => exact .push (.cell scope) accessible rest
  | push miss next ih => cases checked with
      | push frame accessible rest =>
          exact .push frame (by simpa only [cell_update_active_tickets next] using accessible) (ih rest)
  | live next ih => cases checked with
      | live known scope saved rest =>
          exact .live known scope (by simpa only [cell_update_active_tickets next] using saved) (ih rest)
  | spent next ih => cases checked with
      | spent known scope rest => exact .spent known scope (ih rest)

theorem cell_read_preserves_configuration_usage
    (update : CellUpdate identity payload payload before after)
    (checked : ConfigurationUsage policy tickets ⟨.perform (Instantiation.freezeEffect (.cell identity)) 0 (.resourceRef (.activation identity)), scope, before⟩) :
    ConfigurationUsage policy tickets ⟨.integer payload, scope, after⟩ := by
  obtain ⟨currentDemand, controlDemand, code, control, accessible, balance, unique⟩ := checked
  have same := perform_value_demand_empty code (by trivial)
  subst currentDemand
  obtain ⟨useScope, scopeChecked⟩ := code_demand_scope code
  exact ⟨[], controlDemand, .idle scopeChecked .integer, cell_update_preserves_stack_usage update control,
    List.nil_subset _, by simpa only [cell_update_owned_tickets update] using balance,
    by simpa only [cell_update_owned_tickets update] using unique⟩

theorem cell_write_preserves_configuration_usage
    (update : CellUpdate identity old new before after)
    (checked : ConfigurationUsage policy tickets
      ⟨.perform (Instantiation.freezeEffect (.cell identity)) 1 (.pair (.resourceRef (.activation identity)) (.integer new)), scope, before⟩) :
    ConfigurationUsage policy tickets ⟨.unit, scope, after⟩ := by
  obtain ⟨currentDemand, controlDemand, code, control, accessible, balance, unique⟩ := checked
  have same := perform_value_demand_empty code (by trivial)
  subst currentDemand
  obtain ⟨useScope, scopeChecked⟩ := code_demand_scope code
  exact ⟨[], controlDemand, .idle scopeChecked .unit, cell_update_preserves_stack_usage update control,
    List.nil_subset _, by simpa only [cell_update_owned_tickets update] using balance,
    by simpa only [cell_update_owned_tickets update] using unique⟩

/-- The registry update reads the concrete allocation event and clause scope.
    Its behavior for executable capture is established by the raw-step proof. -/
def advanceUsageTickets (policy : TicketPolicy) (tickets : UsageTickets)
    (after : Configuration) (created : List Owner) : UsageTickets :=
  match created with
  | [.ticket owner] => match after.scope with
    | .ticket binder _ => tickets.insert owner (policy binder)
    | .none => tickets
  | _ => tickets

/-- Fresh allocation preserves every existing ticket's permissions, including
registrations for consumed tickets and saved local interfaces. -/
theorem advance_usage_tickets_extends
    (fresh : ∀ owner, Owner.ticket owner ∈ created → tickets owner = none) :
    Syntax.UsageExtension tickets (advanceUsageTickets policy tickets after created) := by
  unfold advanceUsageTickets
  split
  next remaining owner =>
    split
    next binder ticket scope =>
      exact Syntax.fresh_usage_insert_extends (fresh owner (by simp_all))
    next => exact fun _ _ known => known
  next => exact fun _ _ known => known

/-- Structural pre-step requirements beyond current configuration usage.
    Allocation/history and the existing access check supply these below. -/
structure UsageChecks (tickets : UsageTickets) (before : Configuration) (created : List Owner) : Prop where
  allocation : ∀ owner, Owner.ticket owner ∈ created → tickets owner = none
  discard : ∀ binder owner scope caller input answer (front capture tail : Stack) plan,
    before = ⟨.discard binder, scope, front.append (.live owner input answer capture caller tail)⟩ →
    scope.resolve binder = some owner → makePlan capture = some plan →
    InternalUses capture.erase.liveTickets capture.erase.pending

theorem raw_step_preserves_configuration_usage
    (step : RawStep before after created discharged) (checks : UsageChecks tickets before created)
    (checked : ConfigurationUsage policy tickets before) :
    ConfigurationUsage policy (advanceUsageTickets policy tickets after created) after := by
  have actual := step
  cases step with
  | focus plain focus tail => exact focus_preserves_configuration_usage plain focus checked
  | bind parameter value body scope tail closed environment =>
      exact bind_preserves_configuration_usage checked closed.1
  | beta parameter body value scope tail closed closure =>
      exact beta_preserves_configuration_usage checked closed.1
  | ifTrue => exact (branch_preserves_configuration_usage checked).1
  | ifFalse => exact (branch_preserves_configuration_usage checked).2
  | enterHandler handler body tail => exact handler_entry_preserves_configuration_usage handler checked
  | enterCell => exact cell_entry_preserves_configuration_usage checked _ _
  | enterCleanup action body tail => exact cleanup_entry_preserves_configuration_usage action checked
  | capture requested operation parameter binder owner operand body scope whole capture tail handler
      input cut selected closed environment =>
      exact capture_preserves_configuration_usage cut selected checked closed.1 (checks.allocation owner (by simp))
  | resume binder owner scope caller input answer front capture tail value closed resolved =>
      exact resume_preserves_configuration_usage checked resolved closed.1
  | discard binder owner closeId scope caller input answer front capture tail plan resolved built =>
      exact discard_preserves_configuration_usage checked resolved built
        (checks.discard binder owner scope caller input answer front capture tail plan rfl resolved built)
  | readCell identity payload scope before after update => exact cell_read_preserves_configuration_usage update checked
  | writeCell identity old new scope before after update => exact cell_write_preserves_configuration_usage update checked
  | plug | leaveHandler | leaveCell | startCleanup | finishCleanup | leaveClause | finishClose | retire =>
      apply raw_value_step_preserves_configuration_usage actual ?_ checked
      first | assumption | simp [ClosedValue, Code.IsValue, Code.dependencies, Code.ResourceClosed, Code.freeNames]

/-- The registry contains exactly the historically issued ticket identities.
    Consumption retains an entry; allocation installs its selected permissions. -/
def UsageRegistryHistory (tickets : UsageTickets) (issued : List Owner) : Prop :=
  ∀ owner, (∃ rights, tickets owner = some rights) ↔ Owner.ticket owner ∈ issued

theorem empty_usage_registry_history : UsageRegistryHistory (fun _ => none) [] := by
  intro owner
  simp

theorem raw_step_preserves_usage_registry_history
    (step : RawStep before after created discharged)
    (history : UsageRegistryHistory tickets issued) :
    UsageRegistryHistory (advanceUsageTickets policy tickets after created) (issued ++ created) := by
  cases step with
  | capture requested operation parameter binder owner operand body scope whole capture tail handler
      input cut selected closed environment =>
      intro name
      by_cases same : name = owner
      · subst name
        simp [advanceUsageTickets, UsageTickets.insert]
      · simpa [advanceUsageTickets, UsageTickets.insert, same] using history name
  | focus | plug | bind | beta | ifTrue | ifFalse | enterHandler | leaveHandler | enterCell
  | leaveCell | enterCleanup | startCleanup | finishCleanup | resume | discard | leaveClause
  | finishClose | retire | readCell | writeCell =>
      simpa [UsageRegistryHistory, advanceUsageTickets] using history

theorem usage_checks_from_allocation_and_access
    (history : UsageRegistryHistory tickets issued)
    (fresh : (issued ++ created).Nodup) (access : AccessChecks before ambient) :
    UsageChecks tickets before created := by
  constructor
  · intro owner allocated
    cases existing : tickets owner with
    | none => rfl
    | some rights =>
        have earlier := (history owner).mp ⟨rights, existing⟩
        exact False.elim ((List.nodup_append.mp fresh).2.2 (.ticket owner) earlier
          (.ticket owner) allocated rfl)
  · intro binder owner scope caller input answer front capture tail plan same resolved built
    have allowed := access.discard binder owner scope caller input answer front capture tail plan same resolved built
    cases allowed with
    | checked closing internal => exact internal

theorem named_access_step_preserves_usage_extension
    (step : NamedAccessStep ambient before after)
    (usage : ConfigurationUsage policy tickets before.execution.configuration)
    (registry : UsageRegistryHistory tickets before.execution.issued) :
    ∃ afterTickets, ConfigurationUsage policy afterTickets after.execution.configuration ∧
      UsageRegistryHistory afterTickets after.execution.issued ∧
      Syntax.UsageExtension tickets afterTickets := by
  cases step with
  | mk execution access => cases execution with
      | event after created discharged raw freshOwners freshHandlers =>
          have checks := usage_checks_from_allocation_and_access registry freshOwners access
          exact ⟨_, raw_step_preserves_configuration_usage raw
            checks usage, raw_step_preserves_usage_registry_history raw registry,
            advance_usage_tickets_extends checks.allocation⟩

theorem named_access_step_preserves_usage
    (step : NamedAccessStep ambient before after)
    (usage : ConfigurationUsage policy tickets before.execution.configuration)
    (registry : UsageRegistryHistory tickets before.execution.issued) :
    ∃ afterTickets, ConfigurationUsage policy afterTickets after.execution.configuration ∧
      UsageRegistryHistory afterTickets after.execution.issued := by
  obtain ⟨afterTickets, nextUsage, nextRegistry, extension⟩ :=
    named_access_step_preserves_usage_extension step usage registry
  exact ⟨afterTickets, nextUsage, nextRegistry⟩

/-- The same admitted finite execution preserves name history, the lifetime
    ledger, resource support, whole-control usage, and the registry domain.
    Initial source admission and type/effect preservation are not premises
    silently supplied by this theorem; those remain separate obligations. -/
theorem named_access_steps_joint_usage_extension
    (steps : NamedAccessSteps ambient before after)
    (ledger : Ledger before.execution.erase)
    (history : NameHistory before.execution before.activations)
    (access : AccessValid before.execution.configuration ambient)
    (usage : ConfigurationUsage policy tickets before.execution.configuration)
    (registry : UsageRegistryHistory tickets before.execution.issued) :
    ∃ afterTickets, Ledger after.execution.erase ∧
      NameHistory after.execution after.activations ∧ AccessValid after.execution.configuration ambient ∧
      ConfigurationUsage policy afterTickets after.execution.configuration ∧
      UsageRegistryHistory afterTickets after.execution.issued ∧
      Syntax.UsageExtension tickets afterTickets := by
  induction steps generalizing tickets with
  | refl => exact ⟨tickets, ledger, history, access, usage, registry, fun _ _ known => known⟩
  | next first rest ih =>
      obtain ⟨nextLedger, nextHistory, nextAccess⟩ := named_access_step_preserves first ledger history access
      obtain ⟨nextTickets, nextUsage, nextRegistry, extension⟩ :=
        named_access_step_preserves_usage_extension first usage registry
      obtain ⟨lastTickets, lastLedger, lastHistory, lastAccess, lastUsage, lastRegistry, later⟩ :=
        ih nextLedger nextHistory nextAccess nextUsage nextRegistry
      exact ⟨lastTickets, lastLedger, lastHistory, lastAccess, lastUsage, lastRegistry,
        fun owner rights known => later owner rights (extension owner rights known)⟩

/-- Preserve the previous interface as a projection of the strengthened
finite-run result, rather than maintaining a second execution induction. -/
theorem named_access_steps_joint_usage
    (steps : NamedAccessSteps ambient before after)
    (ledger : Ledger before.execution.erase)
    (history : NameHistory before.execution before.activations)
    (access : AccessValid before.execution.configuration ambient)
    (usage : ConfigurationUsage policy tickets before.execution.configuration)
    (registry : UsageRegistryHistory tickets before.execution.issued) :
    ∃ afterTickets, Ledger after.execution.erase ∧
      NameHistory after.execution after.activations ∧ AccessValid after.execution.configuration ambient ∧
      ConfigurationUsage policy afterTickets after.execution.configuration ∧
      UsageRegistryHistory afterTickets after.execution.issued := by
  obtain ⟨afterTickets, nextLedger, nextHistory, nextAccess, nextUsage, nextRegistry, extension⟩ :=
    named_access_steps_joint_usage_extension steps ledger history access usage registry
  exact ⟨afterTickets, nextLedger, nextHistory, nextAccess, nextUsage, nextRegistry⟩


/-- Resource-name closure joins the same execution; no additional usage or
    ownership condition is assumed at a successor state. -/
theorem scoped_named_access_steps_joint_usage
    (steps : NamedAccessSteps ambient before after)
    (closed : before.execution.configuration.ResourceClosed)
    (ledger : Ledger before.execution.erase)
    (history : NameHistory before.execution before.activations)
    (access : AccessValid before.execution.configuration ambient)
    (usage : ConfigurationUsage policy tickets before.execution.configuration)
    (registry : UsageRegistryHistory tickets before.execution.issued) :
    ∃ afterTickets, after.execution.configuration.ResourceClosed ∧ Ledger after.execution.erase ∧
      NameHistory after.execution after.activations ∧ AccessValid after.execution.configuration ambient ∧
      ConfigurationUsage policy afterTickets after.execution.configuration ∧
      UsageRegistryHistory afterTickets after.execution.issued := by
  obtain ⟨afterTickets, invariants⟩ := named_access_steps_joint_usage steps ledger history access usage registry
  exact ⟨afterTickets,
    run_steps_preserve_resource_closure (named_steps_execute (named_access_steps_have_names steps)) closed,
    invariants⟩

namespace UsageExecutionExamples
open ControlUsageExamples (policy rights closed_unit)

theorem initial_usage {expression : Code}
    (checked : Uses policy .none .available expression .available) :
    ConfigurationUsage policy tickets ⟨expression, .none, .nil⟩ :=
  ⟨[], [], .idle .none checked, .nil, List.nil_subset _, .refl _, by simp [ownedTickets]⟩

/-- Actual fresh scoped allocation, metadata realization, builtin read, and release. -/
theorem fresh_cell_execution_joint_usage :
    ∃ tickets, AccessExamples.terminal.configuration.ResourceClosed ∧ Ledger AccessExamples.terminal.erase ∧
      NameHistory AccessExamples.terminal [] ∧ AccessValid AccessExamples.terminal.configuration [] ∧
      ConfigurationUsage policy tickets AccessExamples.terminal.configuration ∧
      UsageRegistryHistory tickets AccessExamples.terminal.issued := by
  apply scoped_named_access_steps_joint_usage (tickets := fun _ => none)
    AccessExamples.fresh_read_named_access_execution
  · exact ⟨rfl, trivial⟩
  · exact ⟨.refl _, by decide⟩
  · refine ⟨?_, ?_, by decide⟩ <;> intro name <;>
      simp [AccessExamples.initial, Stack.erase, Control.ticketNames, Control.activations]
  · exact ⟨.nil [], List.nil_subset _⟩
  · exact initial_usage (.resource .integer (.perform .resourceRef))
  · exact empty_usage_registry_history

def handler : HandlerData :=
  ⟨8, .user 1 [], .cons 0 1 9 (.resume 9 .unit) .nil, .none, .unit, rfl⟩
def cap : Stack := .push (.handler handler) .nil
def request : Code := .perform (Instantiation.freezeEffect handler.effectInst) 0 .unit
def initial : NamedState :=
  ⟨⟨⟨.handle (Instantiation.freezeEffect handler.effectInst) request handler.clauses, .none, .nil⟩, [], []⟩, []⟩
def terminal : NamedState := ⟨⟨⟨.unit, .none, .nil⟩, [.ticket 3], [.ticket 3]⟩, [8]⟩

/-- The combined theorem is inhabited by actual capture and consumption, with
    a fresh owner and a nonempty handler activation history. -/
theorem capture_resume_execution : NamedAccessSteps [] initial terminal := by
  have e0 := RawStep.enterHandler handler request Stack.nil
  have e1 := RawStep.capture handler.effectInst 0 1 9 3 .unit (.resume 9 .unit)
    .none cap cap .nil handler .unit (.hit handler .nil rfl) .hit closed_unit
    (by simp [ClosedExcept, Code.dependencies])
  have e2 := RawStep.resume 9 3 (.ticket 9 3) .none .unit .unit .nil cap .nil .unit closed_unit rfl
  have e3 := RawStep.leaveHandler handler .unit closed_unit (.ticket 9 3) (.spent 3 .unit .none .nil)
  have e4 := RawStep.leaveClause 3 .unit .unit closed_unit .none .none .nil
  exact .next ⟨.event _ _ _ _ e0 (by decide) (by decide),
      resource_free_access_checks rfl (by intro _ impossible; cases impossible)⟩
    (.next ⟨.event _ _ _ _ e1 (by decide) (by decide),
      resource_free_access_checks rfl (by intro _ impossible; cases impossible)⟩
    (.next ⟨.event _ _ _ _ e2 (by decide) (by decide),
      resource_free_access_checks rfl (by intro _ impossible; cases impossible)⟩
    (.next ⟨.event _ _ _ _ e3 (by decide) (by decide),
      resource_free_access_checks rfl (by intro _ impossible; cases impossible)⟩
    (.next ⟨.event _ _ _ _ e4 (by decide) (by decide),
      resource_free_access_checks rfl (by intro _ impossible; cases impossible)⟩ (.refl _)))))

theorem capture_resume_joint_usage :
    ∃ tickets, terminal.execution.configuration.ResourceClosed ∧ Ledger terminal.execution.erase ∧
      NameHistory terminal.execution terminal.activations ∧ AccessValid terminal.execution.configuration [] ∧
      ConfigurationUsage policy tickets terminal.execution.configuration ∧
      UsageRegistryHistory tickets terminal.execution.issued := by
  apply scoped_named_access_steps_joint_usage (tickets := fun _ => none) capture_resume_execution
  · exact ⟨rfl, trivial⟩
  · exact ⟨.refl _, by decide⟩
  · refine ⟨?_, ?_, by decide⟩ <;> intro name <;>
      simp [initial, Stack.erase, Control.ticketNames, Control.activations]
  · exact ⟨.nil [], List.nil_subset _⟩
  · exact initial_usage (.handle (.perform .unit) (.cons (.resume rfl .unit) .nil))
  · exact empty_usage_registry_history

end UsageExecutionExamples

end Ash.OneShot.ScopedExecution

#print axioms Ash.OneShot.ScopedExecution.cell_entry_preserves_configuration_usage
#print axioms Ash.OneShot.ScopedExecution.advance_usage_tickets_extends
#print axioms Ash.OneShot.ScopedExecution.raw_step_preserves_configuration_usage
#print axioms Ash.OneShot.ScopedExecution.raw_step_preserves_usage_registry_history
#print axioms Ash.OneShot.ScopedExecution.usage_checks_from_allocation_and_access
#print axioms Ash.OneShot.ScopedExecution.named_access_step_preserves_usage_extension
#print axioms Ash.OneShot.ScopedExecution.named_access_steps_joint_usage_extension
#print axioms Ash.OneShot.ScopedExecution.named_access_steps_joint_usage
#print axioms Ash.OneShot.ScopedExecution.scoped_named_access_steps_joint_usage
#print axioms Ash.OneShot.ScopedExecution.UsageExecutionExamples.fresh_cell_execution_joint_usage
#print axioms Ash.OneShot.ScopedExecution.UsageExecutionExamples.capture_resume_execution
#print axioms Ash.OneShot.ScopedExecution.UsageExecutionExamples.capture_resume_joint_usage
