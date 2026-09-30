import ControlUsage

/-!
Continuation usage through expression evaluation and administrative entry.
This layer relates the independent usage invariant to executable transitions;
source admission and the joint type/effect/resource invariant remain separate.
-/

namespace Ash.OneShot.Syntax
open Execution Typing

theorem focus_splits_code_demand
    (focus : Focus whole child context)
    (code : CodeDemand policy tickets scope whole demand) :
    ∃ childDemand frameDemand,
      demand = childDemand ++ frameDemand ∧
      CodeDemand policy tickets scope child childDemand ∧
      CodeDemand policy tickets scope (context.plug .unit) frameDemand := by
  cases code with
  | idle scope checked =>
      obtain ⟨middle, childUse, contextUse⟩ := focus_decomposes_usage focus checked
      cases middle with
      | available =>
          exact ⟨[], [], rfl, .idle scope childUse,
            .idle scope (context_plug_preserves_usage contextUse .unit)⟩
      | consumed =>
          have impossible := use_state_monotone (context_plug_preserves_usage contextUse .unit) rfl
          cases impossible
  | consume known checked =>
      obtain ⟨middle, childUse, contextUse⟩ := focus_decomposes_usage focus checked
      cases middle with
      | available =>
          exact ⟨[], [_], rfl, .idle (.bound known) childUse,
            .consume known (context_plug_preserves_usage contextUse .unit)⟩
      | consumed =>
          exact ⟨[_], [], rfl, .consume known childUse,
            .idle (.bound known) (usage_from_consumed_is_idle
              (context_plug_preserves_usage contextUse .unit))⟩

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

theorem bind_code_demand
    (code : CodeDemand policy tickets scope (.bind parameter value body) demand)
    (isValue : value.IsValue) :
    CodeDemand policy tickets scope (body.subst parameter value) demand := by
  cases code with
  | idle scope checked => cases checked with
      | bind initializer suffix =>
          have same := value_use_preserves_state isValue initializer
          subst same
          exact .idle scope (usage_substitution suffix isValue
            (value_use_transport isValue initializer .none .available) parameter)
  | consume known checked => cases checked with
      | bind initializer suffix =>
          have same := value_use_preserves_state isValue initializer
          subst same
          exact .consume known (usage_substitution suffix isValue
            (value_use_transport isValue initializer .none .available) parameter)

theorem branch_code_demand
    (code : CodeDemand policy tickets scope (.branch (.boolean condition) yes no) demand) :
    CodeDemand policy tickets scope yes demand ∧ CodeDemand policy tickets scope no demand := by
  cases code with
  | idle scope checked => cases checked with
      | branch condition yes no => cases condition; exact ⟨.idle scope yes, .idle scope no⟩
  | consume known checked => cases checked with
      | branch condition yes no => cases condition; exact ⟨.consume known yes, .consume known no⟩

theorem beta_code_demand
    (code : CodeDemand policy tickets scope (.app (.lambda parameter body) value) demand)
    (isValue : value.IsValue) :
    demand = [] ∧ CodeDemand policy tickets .none (body.subst parameter value) [] := by
  cases code with
  | idle scope checked => cases checked with
      | app function argument => cases function with
          | lambda body =>
              exact ⟨rfl, .idle .none (usage_substitution body isValue
                (value_use_transport isValue argument .none .available) parameter)⟩
  | consume known checked => cases checked with
      | app function argument => cases function with
          | lambda body => cases value_use_preserves_state isValue argument

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
      ⟨.handle handler.effectInst body handler.clauses, handler.scope, tail⟩) :
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
    (before : ConfigurationUsage policy tickets ⟨.resource identity (.integer payload) body, scope, tail⟩) :
    ConfigurationUsage policy tickets ⟨body, scope, .push (.cell identity payload scope answer) tail⟩ := by
  obtain ⟨currentDemand, controlDemand, code, control, accessible, balance, unique⟩ := before
  exact ⟨currentDemand, controlDemand, cell_code_demand code,
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
    (checked : ConfigurationUsage policy tickets ⟨.perform (.cell identity) 0 (.resourceRef identity), scope, before⟩) :
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
      ⟨.perform (.cell identity) 1 (.pair (.resourceRef identity) (.integer new)), scope, before⟩) :
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
  | bind parameter value body scope tail closed environment fresh =>
      exact bind_preserves_configuration_usage checked closed.1
  | beta parameter body value scope tail closed closure fresh =>
      exact beta_preserves_configuration_usage checked closed.1
  | ifTrue => exact (branch_preserves_configuration_usage checked).1
  | ifFalse => exact (branch_preserves_configuration_usage checked).2
  | enterHandler handler body tail => exact handler_entry_preserves_configuration_usage handler checked
  | enterCell => exact cell_entry_preserves_configuration_usage checked
  | enterCleanup action body tail => exact cleanup_entry_preserves_configuration_usage action checked
  | capture requested operation parameter binder owner operand body scope whole capture tail handler
      input cut selected closed environment fresh =>
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
      first | assumption | simp [ClosedValue, Expr.IsValue, Expr.dependencies]

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
      input cut selected closed environment fresh =>
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

theorem named_access_step_preserves_usage
    (step : NamedAccessStep ambient before after)
    (usage : ConfigurationUsage policy tickets before.execution.configuration)
    (registry : UsageRegistryHistory tickets before.execution.issued) :
    ∃ afterTickets, ConfigurationUsage policy afterTickets after.execution.configuration ∧
      UsageRegistryHistory afterTickets after.execution.issued := by
  cases step with
  | mk execution access => cases execution with
      | event after created discharged raw freshOwners freshHandlers =>
          exact ⟨_, raw_step_preserves_configuration_usage raw
            (usage_checks_from_allocation_and_access registry freshOwners access) usage,
            raw_step_preserves_usage_registry_history raw registry⟩

/-- The same admitted finite execution preserves name history, the lifetime
    ledger, resource support, whole-control usage, and the registry domain.
    Initial source admission and type/effect preservation are not premises
    silently supplied by this theorem; those remain separate obligations. -/
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
  induction steps generalizing tickets with
  | refl => exact ⟨tickets, ledger, history, access, usage, registry⟩
  | next first rest ih =>
      obtain ⟨nextLedger, nextHistory, nextAccess⟩ := named_access_step_preserves first ledger history access
      obtain ⟨nextTickets, nextUsage, nextRegistry⟩ := named_access_step_preserves_usage first usage registry
      exact ih nextLedger nextHistory nextAccess nextUsage nextRegistry

namespace UsageExecutionExamples
open Execution.Examples
open ControlUsageExamples (policy rights none_known)

/-- Initial usage is checked from the expression, without a future invariant. -/
theorem initial_usage (checked : Uses policy .none .available expression .available) :
    ConfigurationUsage policy tickets ⟨expression, .none, .nil⟩ :=
  ⟨[], [], .idle .none checked, .nil, List.nil_subset _, .refl _, by simp [ownedTickets]⟩

theorem cleanup_execution_joint_usage :
    let final : RunState := ⟨⟨.integer 42, .none, .nil⟩,
      [.cleanup 7, .ticket 3], [.cleanup 7, .ticket 3]⟩
    ∃ tickets, Ledger final.erase ∧ NameHistory final [8] ∧
      AccessValid final.configuration [] ∧ ConfigurationUsage policy tickets final.configuration ∧
      UsageRegistryHistory tickets final.issued := by
  apply named_access_steps_joint_usage (tickets := fun _ => none) NameExamples.cleanup_execution_has_joint_checks
    ⟨.refl [], by decide⟩
    ⟨by simp [Stack.erase, Control.ticketNames], by simp [Stack.erase, Control.activations], by decide⟩
  · constructor
    · exact .nil _
    · simp [Expr.dependencies, callback, callbackBody, clauses, Clauses.dependencies,
        resourceDependencies, instanceDependencies, Instance.resources, without]
  · exact initial_usage (.handle (.cleanup (.lambda (.perform .unit)) .integer)
      (.cons (.resume rfl .unit) .nil))
  · exact empty_usage_registry_history

/-- Completion retains the issued ticket's historical registry entry. -/
theorem cleanup_consumed_ticket_stays_registered :
    ∃ tickets, ConfigurationUsage policy tickets ⟨.integer 42, .none, .nil⟩ ∧
      ∃ permissions, tickets 3 = some permissions := by
  obtain ⟨tickets, _, _, _, usage, history⟩ := cleanup_execution_joint_usage
  exact ⟨tickets, usage, (history 3).mpr (by simp)⟩

private theorem append_live_ne_nil (front : Stack) :
    front.append (.live owner input answer capture scope tail) ≠ .nil := by
  cases front <;> simp [Stack.append]

/-- This actual cut also satisfies close-plan support and interpretation. -/
theorem cell_disposal_access_checks :
    AccessChecks ⟨.discard 9, closeScope, .live 3 .unit .unit abandoned .none .nil⟩ [] := by
  constructor
  · intro identity payload answer savedScope scope value tail same closed
    cases same
  · intro requested operation operand scope whole cap tail handler same
    cases same
  · intro binder owner scope caller input answer front cap tail plan same resolved built
    have expr := congrArg Configuration.expression same
    have scopes : closeScope = scope := congrArg Configuration.scope same
    have stacks : Stack.live 3 .unit .unit abandoned .none .nil =
        front.append (.live owner input answer cap caller tail) := congrArg Configuration.stack same
    simp only [Expr.discard.injEq] at expr
    subst binder
    subst scope
    simp [closeScope, Scope.resolve] at resolved
    subst owner
    cases front with
    | nil =>
        simp only [Stack.append, Stack.live.injEq] at stacks
        rcases stacks with ⟨_, rfl, rfl, rfl, rfl, rfl⟩
        have samePlan : plan = closePlan := by simpa [makePlan, abandoned, closePlan] using built.symm
        subst plan
        exact cell_cleanup_disposal_is_admitted
    | push => cases stacks
    | spent => cases stacks
    | live outer q a saved savedScope rest =>
        have impossible := (Stack.live.inj stacks).2.2.2.2.2
        exact False.elim (append_live_ne_nil rest impossible.symm)

theorem ordinary_access_checks
    (notValue : ¬ expression.IsValue)
    (notRequest : ∀ requested operation operand, expression ≠ .perform requested operation operand)
    (notDiscard : ∀ binder, expression ≠ .discard binder) :
    AccessChecks ⟨expression, scope, stack⟩ ambient := by
  constructor
  · intro identity payload answer savedScope current value tail same closed
    have equal : expression = value := congrArg Configuration.expression same
    exact False.elim (notValue (equal.symm ▸ closed.1))
  · intro requested operation operand current whole cap tail handler same
    exact False.elim (notRequest requested operation operand (congrArg Configuration.expression same))
  · intro binder owner current caller q answer front cap tail plan same
    exact False.elim (notDiscard binder (congrArg Configuration.expression same))

theorem cell_update_excludes_handler_cut {capture tail : Stack} {selected : HandlerData}
    (update : CellUpdate identity old new before after) :
    ¬ HandlerCut (.cell identity) before capture tail selected := by
  induction update generalizing capture tail selected with
  | hit =>
      intro cut
      cases cut with
      | push frame rest cap tail handler miss next => exact miss rfl
  | push miss next ih =>
      intro cut
      cases cut with
      | hit handler tail same => exact miss (by simp [ExecFrame.erase, HandlerData.erase, Frame.target, same])
      | push frame rest cap tail handler otherMiss further => exact ih further
  | live next ih => intro cut; cases cut with | live _ _ _ _ _ _ _ _ _ further => exact ih further
  | spent next ih => intro cut; cases cut with | spent _ _ _ _ _ _ _ further => exact ih further

theorem builtin_read_access_checks (update : CellUpdate identity old new before after) :
    AccessChecks ⟨.perform (.cell identity) 0 (.resourceRef identity), scope, before⟩ ambient := by
  constructor
  · intro other payload answer savedScope current value tail same closed
    cases same
    exact False.elim closed.1
  · intro requested operation operand current whole cap tail handler same cut closed
    cases same
    exact False.elim (cell_update_excludes_handler_cut update cut)
  · intro binder owner current caller q answer front cap tail plan same
    cases same

/-- Every step uses the existing access and allocation admission checks. -/
theorem cell_disposal_joint_execution :
    NamedAccessSteps []
      ⟨⟨⟨.discard 9, closeScope, .live 3 .unit .unit abandoned .none .nil⟩,
        [.resource 4, .cleanup 7, .ticket 3], []⟩, [10]⟩
      ⟨⟨⟨.unit, .none, .nil⟩, [.resource 4, .cleanup 7, .ticket 3, .close 8],
        [.close 8, .resource 4, .cleanup 7, .ticket 3]⟩, [10]⟩ := by
  have e0 := RawStep.discard 9 3 8 closeScope .none .unit .unit .nil abandoned .nil closePlan rfl rfl
  have e1 := RawStep.startCleanup closingAction .unit closed_unit closeScope closeCellTail
  have e2 := RawStep.beta 2 readBody .unit .none runningClose closed_unit read_callback_closed
    (by simp [ResourceFresh, Expr.dependencies])
  have e3 := RawStep.focus readSuffix
    (Focus.bind (initializer := .perform (.cell 4) 0 (.resourceRef 4))
      (by simp [Expr.IsValue])) runningClose
  have cell : CellUpdate 4 17 17 (.push (.plain readSuffix) runningClose)
      (.push (.plain readSuffix) runningClose) :=
    .push (by simp [ExecFrame.erase, PlainData.erase, Frame.target])
      (.push (by simp [ExecFrame.erase, Frame.target]) .hit)
  have e4 := RawStep.readCell 4 17 .none _ _ cell
  have e5 := RawStep.plug readSuffix (.integer 17) (closed_integer 17) .none runningClose
  have e6 := RawStep.bind 0 (.integer 17) .unit .none runningClose (closed_integer 17)
    (by simp [ClosedExcept, Expr.dependencies]) (by simp [ResourceFresh, Expr.dependencies])
  have e7 := RawStep.finishCleanup closingAction .unit closed_unit .none closeCellTail
  have e8 := RawStep.leaveCell 4 17 .unit closeScope closeScope .unit closed_unit closeTail
  have e9 := RawStep.finishClose 8 closeScope closeScope (.spent 3 .unit .none .nil)
  have e10 := RawStep.leaveClause 3 .unit .unit closed_unit closeScope .none .nil
  refine .next ⟨.event _ _ _ _ e0 (by decide) (by decide), ?_⟩ ?_
  · exact cell_disposal_access_checks
  refine .next ⟨.event _ _ _ _ e1 (by decide) (by decide), ?_⟩ ?_
  · exact resource_free_access_checks rfl (by intro binder same; cases same)
  refine .next ⟨.event _ _ _ _ e2 (by decide) (by decide), ?_⟩ ?_
  · apply ordinary_access_checks <;> simp [Expr.IsValue]
  refine .next ⟨.event _ _ _ _ e3 (by decide) (by decide), ?_⟩ ?_
  · change AccessChecks ⟨.bind 0 (.perform (.cell 4) 0 (.resourceRef 4)) .unit, .none, runningClose⟩ []
    apply ordinary_access_checks <;> simp [Expr.IsValue]
  refine .next ⟨.event _ _ _ _ e4 (by decide) (by decide), ?_⟩ ?_
  · exact builtin_read_access_checks cell
  refine .next ⟨.event _ _ _ _ e5 (by decide) (by decide), ?_⟩ ?_
  · exact resource_free_access_checks rfl (by intro binder same; cases same)
  refine .next ⟨.event _ _ _ _ e6 (by decide) (by decide), ?_⟩ ?_
  · exact resource_free_access_checks rfl (by intro binder same; cases same)
  refine .next ⟨.event _ _ _ _ e7 (by decide) (by decide), ?_⟩ ?_
  · exact resource_free_access_checks rfl (by intro binder same; cases same)
  refine .next ⟨.event _ _ _ _ e8 (by decide) (by decide), ?_⟩ ?_
  · exact resource_free_access_checks rfl (by intro binder same; cases same)
  refine .next ⟨.event _ _ _ _ e9 (by decide) (by decide), ?_⟩ ?_
  · exact resource_free_access_checks rfl (by intro binder same; cases same)
  refine .next ⟨.event _ _ _ _ e10 (by decide) (by decide), ?_⟩ ?_
  · exact resource_free_access_checks rfl (by intro binder same; cases same)
  exact .refl _

def disposalTickets : UsageTickets := UsageTickets.insert (fun _ => none) 3 rights

theorem cell_disposal_initial_usage : ConfigurationUsage policy disposalTickets
    ⟨.discard 9, closeScope, .live 3 .unit .unit abandoned .none .nil⟩ := by
  refine ⟨[3], [], .consume rfl (.discard rfl), ?_, ?_, .refl _, by decide⟩
  · refine .live (owner := 3) (captureDemand := []) (restDemand := []) rfl
      (none_known disposalTickets) ?_ .nil
    exact .push (.armed (none_known disposalTickets) (.lambda (.bind (.perform .resourceRef) .unit)))
      (List.nil_subset _) (.push (.cell (none_known disposalTickets)) (List.nil_subset _)
        (.push (.handler (none_known disposalTickets) (.cons (.discard rfl) .nil))
          (List.nil_subset _) .nil))
  · simp [activeTickets]

/-- The joint invariant is inhabited by an actual disposal execution whose
    callback reads an owned cell before that cell is released. -/
theorem cell_disposal_joint_usage :
    let final : RunState := ⟨⟨.unit, .none, .nil⟩,
      [.resource 4, .cleanup 7, .ticket 3, .close 8],
      [.close 8, .resource 4, .cleanup 7, .ticket 3]⟩
    ∃ tickets, Ledger final.erase ∧ NameHistory final [10] ∧
      AccessValid final.configuration [] ∧ ConfigurationUsage policy tickets final.configuration ∧
      UsageRegistryHistory tickets final.issued := by
  apply named_access_steps_joint_usage (tickets := disposalTickets) cell_disposal_joint_execution
  · exact ⟨(List.reverse_perm [Owner.resource 4, .cleanup 7, .ticket 3]).symm, by decide⟩
  · constructor
    · intro ticket
      simp [abandoned, readAction, discardHandler, Stack.erase, ExecFrame.erase,
        ActionData.erase, HandlerData.erase, Control.ticketNames, List.count_cons]
    · intro activation
      simp [abandoned, readAction, discardHandler, Stack.erase, ExecFrame.erase,
        ActionData.erase, HandlerData.erase, Control.activations, Frame.activation]
    · decide
  · constructor
    · refine .live _ _ _ _ _ _ ?_ (.nil _)
      refine .push _ _ _ (.push _ _ _ (.push _ _ _ (.nil _) ?_) ?_) ?_
      · simp [discardHandler, ExecFrame.erase, HandlerData.erase, Clauses.dependencies, Expr.dependencies,
          Instance.resources, resourceDependencies, without]
      · simp [ExecFrame.erase]
      · simp [readAction, ActionData.erase, readCallback, readBody, Expr.dependencies,
          resourceDependencies, instanceDependencies, Instance.resources, without,
          Stack.erase, ExecFrame.erase, Control.visible, Frame.visible]
    · simp [Expr.dependencies, resourceDependencies]
  · exact cell_disposal_initial_usage
  · intro owner
    simp [disposalTickets, UsageTickets.insert]

end UsageExecutionExamples

end Ash.OneShot.Syntax

#print axioms Ash.OneShot.Syntax.focus_preserves_configuration_usage
#print axioms Ash.OneShot.Syntax.bind_preserves_configuration_usage
#print axioms Ash.OneShot.Syntax.beta_preserves_configuration_usage
#print axioms Ash.OneShot.Syntax.handler_entry_preserves_configuration_usage
#print axioms Ash.OneShot.Syntax.cleanup_entry_preserves_configuration_usage
#print axioms Ash.OneShot.Syntax.cell_write_preserves_configuration_usage
#print axioms Ash.OneShot.Syntax.raw_step_preserves_configuration_usage
#print axioms Ash.OneShot.Syntax.usage_checks_from_allocation_and_access
#print axioms Ash.OneShot.Syntax.named_access_steps_joint_usage

#print axioms Ash.OneShot.Syntax.UsageExecutionExamples.cleanup_execution_joint_usage
#print axioms Ash.OneShot.Syntax.UsageExecutionExamples.cell_disposal_joint_usage
