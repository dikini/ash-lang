import CoreCallableRichAdmittedEventConsumers
import CoreTicketHistory
import CoreCallableGeneratedTicketBound

/-! Source-only experiment under DN-0033. Original-root registry domains retain
actual ticket origins. This does not establish general rich capture preservation,
contextual ticket correspondence, M4 availability, or Rust capacity behavior. -/
namespace Ash.OneShot.CoreCallableRichRegistryOrigins
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreSyntax CoreMachine CoreCallableGeneratedChronology CoreCallableInitialChronology
open CoreCallableContractRegistries (Registry Owners OwnerContract)
open CoreCallableContractAdmission (Globals SubstitutionPolicyStable)
open CoreCallableContractExecution (Site)
open CoreCallableInitialAdmission (Program)
open CoreCallableRichAdmittedCurrentOrigins (Current)
open CoreCallableRichAdmittedEventConsumers (BetaEvent beta_event)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourcePlannedChecks (DeclarationPolicy)

section
variable [evidence : DeclarationPolicy]

/-- The accepted original Program/Input index one literal initial Core root.
Every full owner-contract and action entry has an issued capture identity.
These domain facts are retained evidence, not consequences of weak Current. -/
structure RegistryOrigin
    (program : Program originalGlobals originalActions originalBudget originalCode)
    (initialInput : InitialInput graph originalCode) (endpoint : Endpoint graph)
    (owners : Owners) (actions : Syntax.UsageTickets) : Prop where
  actual : ∃ count, CoreAllocationHistory.Steps graph count (CoreMachine.initial graph)
    endpoint.state
  ownerIssued : ∀ owner contract, owners owner = some contract →
    owner ∈ CoreTicketHistory.capturedTickets endpoint.state.observations
  actionIssued : ∀ owner rights, actions owner = some rights →
    owner ∈ CoreTicketHistory.capturedTickets endpoint.state.observations

/-- Only literal empty maps seed registry origins. An arbitrary accepted Program
may have nonempty owner/action parameters and does not imply this seed. -/
theorem initial_registry_origin (registry : Registry)
    (program : Program ⟨registry.operations, registry.policy, fun _ => none⟩
      (fun _ => none) originalBudget originalCode)
    (initialInput : InitialInput graph originalCode) :
    RegistryOrigin program initialInput (initial_endpoint initialInput)
      (fun _ => none) (fun _ => none) := by
  refine ⟨⟨0, .refl _⟩, ?_, ?_⟩
  · intro owner contract impossible
    cases impossible
  · intro owner rights impossible
    cases impossible

/-- Actual original-root history supplies counter freshness independently of
static Source proofs, phantom Program indices and target machine equality. -/
theorem RegistryOrigin.history
    (origin : RegistryOrigin program initialInput endpoint owners actions) :
    CoreTicketHistory.History endpoint.state := by
  obtain ⟨count, steps⟩ := origin.actual
  exact CoreTicketHistory.initial_steps_history _ steps

/-- The actual current counter cannot already name a full owner contract. -/
theorem RegistryOrigin.owner_fresh
    (origin : RegistryOrigin program initialInput endpoint owners actions) :
    owners endpoint.state.nextOwner = none := by
  cases known : owners endpoint.state.nextOwner with
  | none => rfl
  | some contract =>
      exact False.elim (CoreTicketHistory.history_fresh _ origin.history
        (origin.ownerIssued _ contract known))

/-- The same derived counter absence applies to current action rights. -/
theorem RegistryOrigin.action_fresh
    (origin : RegistryOrigin program initialInput endpoint owners actions) :
    actions endpoint.state.nextOwner = none := by
  cases known : actions endpoint.state.nextOwner with
  | none => rfl
  | some rights =>
      exact False.elim (CoreTicketHistory.history_fresh _ origin.history
        (origin.actionIssued _ rights known))

/-- The computed actual beta edge changes neither registry domain nor capture
observations. No successful future edge or desired successor Site is supplied. -/
theorem RegistryOrigin.beta
    (origin : RegistryOrigin program initialInput endpoint owners actions)
    (input : BetaInput endpoint) :
    RegistryOrigin program initialInput (beta_result input).after owners actions := by
  obtain ⟨count, steps⟩ := origin.actual
  have observations : (beta_result input).after.state.observations =
      endpoint.state.observations := rfl
  refine ⟨⟨count + 1, .snoc steps (beta_result input).core⟩, ?_, ?_⟩
  · intro owner contract known
    rw [observations]
    exact origin.ownerIssued owner contract known
  · intro owner rights known
    rw [observations]
    exact origin.actionIssued owner rights known

/-- Derived absence retains every existing full contract and action right under
insertion at the actual counter. No lower-port equality replaces a contract. -/
theorem RegistryOrigin.insertion_preserves_existing
    (origin : RegistryOrigin program initialInput endpoint owners actions)
    (contract : OwnerContract) (rights : Syntax.OneShotRights) :
    CoreCallableContractAdmission.OwnerKnownMonotone owners
      (owners.insert endpoint.state.nextOwner contract) ∧
    Syntax.UsageExtension actions (actions.insert endpoint.state.nextOwner rights) :=
  ⟨CoreCallableContractAdmission.OwnerKnownMonotone.insert_fresh origin.owner_fresh,
    Syntax.fresh_usage_insert_extends origin.action_fresh⟩

/-- The SAME actual capture emits the old nextOwner. Structural insertion keeps
its full supplied contract and rights; this theorem does not construct or
validate the rich selected-family successor using those values. -/
theorem RegistryOrigin.capture_insert
    (origin : RegistryOrigin program initialInput endpoint owners actions)
    (input : CaptureInput endpoint) (contract : OwnerContract)
    (rights : Syntax.OneShotRights) :
    RegistryOrigin program initialInput (capture_result input).after
      (owners.insert endpoint.state.nextOwner contract)
      (actions.insert endpoint.state.nextOwner rights) := by
  obtain ⟨count, steps⟩ := origin.actual
  have tickets : CoreTicketHistory.capturedTickets
      (capture_result input).after.state.observations =
      CoreTicketHistory.capturedTickets endpoint.state.observations ++
        [endpoint.state.nextOwner] := by
    simpa only [CoreCallableReachableResume.issuedTickets, List.filterMap_cons, List.filterMap_nil] using
      CoreCallableGeneratedTicketBound.Operation.ticket_events (.capture input)
  refine ⟨⟨count + 1, .snoc steps (capture_result input).core⟩, ?_, ?_⟩
  · intro owner selected known
    rw [tickets]
    by_cases same : owner = endpoint.state.nextOwner
    · subst owner
      exact List.mem_append_right _ (by simp)
    · have old : owners owner = some selected := by
        simpa only [Owners.insert, if_neg same] using known
      exact List.mem_append_left _ (origin.ownerIssued owner selected old)
  · intro owner selected known
    rw [tickets]
    by_cases same : owner = endpoint.state.nextOwner
    · subst owner
      exact List.mem_append_right _ (by simp)
    · have old : actions owner = some selected := by
        simpa only [Syntax.UsageTickets.insert, if_neg same] using known
      exact List.mem_append_left _ (origin.actionIssued owner selected old)

/-- Full BetaEvent/BetaPreserved is produced by the unchanged rich consumer.
Original functions, arguments, private Plans/Rows and root transport remain in
that receipt; registry origins accompany its SAME computed rich successor. -/
theorem beta_event_with_registry_origin
    (stable : SubstitutionPolicyStable (evidence := evidence) outward)
    (input : BetaInput endpoint)
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.app (.lambda input.parameter input.bodyCode) input.argument) input.scope endpoint.lexical
      output final context root)
    (current : Current program endpoint site)
    (origin : RegistryOrigin program current.input endpoint globals.owners actions) :
    ∃ event : BetaEvent input site current,
      event.after.input = current.input ∧
      RegistryOrigin program current.input (beta_result input).after globals.owners actions ∧
      RegistryOrigin program event.after.input (beta_result input).after globals.owners actions ∧
      globals.owners (beta_result input).after.state.nextOwner = none ∧
      actions (beta_result input).after.state.nextOwner = none := by
  obtain ⟨event⟩ := beta_event stable input site current
  have after := origin.beta input
  have consumer : RegistryOrigin program event.after.input
      (beta_result input).after globals.owners actions := by
    have same : event.after.input = current.input := Subsingleton.elim _ _
    rw [same]
    exact after
  exact ⟨event, Subsingleton.elim _ _, after, consumer, after.owner_fresh,
    after.action_fresh⟩

/-- A known entry at the exact current counter contradicts retained origins. -/
theorem current_owner_entry_rejected
    (origin : RegistryOrigin program initialInput endpoint owners actions)
    (known : owners endpoint.state.nextOwner = some contract) : False := by
  rw [origin.owner_fresh] at known
  cases known

/-- A known action at the exact current counter contradicts the same history. -/
theorem current_action_entry_rejected
    (origin : RegistryOrigin program initialInput endpoint owners actions)
    (known : actions endpoint.state.nextOwner = some rights) : False := by
  rw [origin.action_fresh] at known
  cases known

end

#check RegistryOrigin
#check CoreCallableRichAdmittedCurrentOrigins.initial_from_input
#check initial_registry_origin
#check RegistryOrigin.ownerIssued
#check RegistryOrigin.actionIssued
#check RegistryOrigin.actual
#check RegistryOrigin.owner_fresh
#check RegistryOrigin.action_fresh
#check RegistryOrigin.beta
#check RegistryOrigin.insertion_preserves_existing
#check RegistryOrigin.capture_insert
#check beta_event_with_registry_origin
#check CoreCallableContractExecution.BetaPreserved.originalFunction
#check CoreCallableContractExecution.BetaPreserved.originalArgument
#check CoreCallableContractExecution.BetaPreserved.selected
#check CoreCallableContractExecution.BetaPreserved.exactPlan
#check CoreCallableContractExecution.BetaPreserved.exactRows
#print axioms initial_registry_origin
#print axioms RegistryOrigin.history
#print axioms RegistryOrigin.owner_fresh
#print axioms RegistryOrigin.action_fresh
#print axioms RegistryOrigin.beta
#print axioms RegistryOrigin.insertion_preserves_existing
#print axioms RegistryOrigin.capture_insert
#print axioms beta_event_with_registry_origin
#print axioms current_owner_entry_rejected
#print axioms current_action_entry_rejected
end Ash.OneShot.CoreCallableRichRegistryOrigins
