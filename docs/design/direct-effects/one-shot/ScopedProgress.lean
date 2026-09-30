import ScopedJoint

/-!
Progress at an arbitrary current scoped expression, under structural prestate
access and closing checks. This layer must not assume a next step or a valid
successor. Source establishment and preservation of future readiness are
separate obligations.
-/

namespace Ash.OneShot.ScopedProgress
open Syntax Instantiation ScopedExpressions ScopedExecution ScopedTyping ScopedJoint
open Typing (Signature TypeEnv withCellSignatures)
open Joint (Registry TicketRecord)
open PreparedExecution (RegistryExtends registry_extends_refl registry_extends_fresh_insert)

/-- Exhaustive current-expression forms. The constructors contain only syntax
    and value/focus evidence; none contains an execution witness. -/
inductive CurrentForm : Code → Prop where
  | value (isValue : code.IsValue) : CurrentForm code
  | focus (position : ScopedExecution.Focus code child context) : CurrentForm code
  | bind (isValue : value.IsValue) : CurrentForm (.bind parameter value body)
  | app (functionValue : function.IsValue) (argumentValue : argument.IsValue) : CurrentForm (.app function argument)
  | branch (isValue : condition.IsValue) : CurrentForm (.branch condition yes no)
  | request (isValue : operand.IsValue) : CurrentForm (.perform (freezeEffect requested) operation operand)
  | handler : CurrentForm (.handle effect body clauses)
  | resume (isValue : operand.IsValue) : CurrentForm (.resume binder operand)
  | discard : CurrentForm (.discard binder)
  | resource (isValue : initializer.IsValue) : CurrentForm (.resource binder initializer body)
  | cleanup (isValue : callback.IsValue) : CurrentForm (.cleanup callback body)

theorem typed_current_form
    (typed : Typed signature world TypeEnv.empty ticket allowed code type) : CurrentForm code := by
  classical
  cases code with
  | unit | boolean | integer | lambda => exact .value trivial
  | «variable» name => cases typed with
      | «variable» known formed => simp [TypeEnv.empty] at known
  | resourceRef name => cases typed; exact .value trivial
  | pair left right =>
      by_cases lv : left.IsValue
      · by_cases rv : right.IsValue
        · exact .value ⟨lv, rv⟩
        · exact .focus (.pairRight lv rv)
      · exact .focus (.pairLeft lv)
  | app function argument =>
      by_cases fv : function.IsValue
      · by_cases av : argument.IsValue
        · exact .app fv av
        · exact .focus (.appArgument fv av)
      · exact .focus (.appFunction fv)
  | bind parameter initializer body =>
      by_cases value : initializer.IsValue
      · exact .bind value
      · exact .focus (.bind value)
  | branch condition yes no =>
      by_cases value : condition.IsValue
      · exact .branch value
      · exact .focus (.branch value)
  | perform requested operation operand =>
      cases typed with
      | perform known effects argument formed =>
          by_cases value : operand.IsValue
          · exact .request value
          · exact .focus (.perform value)
  | handle => exact .handler
  | resume binder operand =>
      by_cases value : operand.IsValue
      · exact .resume value
      · exact .focus (.resume value)
  | discard => exact .discard
  | resource binder initializer body =>
      by_cases value : initializer.IsValue
      · exact .resource value
      · exact .focus (.resource value)
  | cleanup callback body =>
      by_cases value : callback.IsValue
      · exact .cleanup value
      · exact .focus (.cleanup value)

/-- Each owner family can allocate above a finite history. The chosen number
    is deliberately conservative across the disjoint owner families. -/
theorem fresh_owner_exists (family : Nat → Owner)
    (number : ∀ n, Progress.ownerNumber (family n) = n) (unique : issued.Nodup) :
    ∃ identity, (issued ++ [family identity]).Nodup := by
  refine ⟨Progress.aboveOwners issued, List.nodup_append.mpr ⟨unique, by simp, ?_⟩⟩
  intro old present new singleton same
  simp only [List.mem_singleton] at singleton
  subst new
  subst old
  have below := Progress.owner_number_below present
  rw [number] at below
  exact (Nat.lt_irrefl _) below

theorem activation_below {activations : List Nat} (present : n ∈ activations) :
    n < activations.foldr (fun k bound => max (k + 1) bound) 0 := by
  induction activations with
  | nil => cases present
  | cons head tail ih =>
      rcases List.mem_cons.mp present with rfl | later
      · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (ih later) (Nat.le_max_right _ _)

theorem fresh_activation_exists {activations : List Nat} (unique : activations.Nodup) :
    ∃ identity, (activations ++ [identity]).Nodup := by
  refine ⟨activations.foldr (fun n bound => max (n + 1) bound) 0,
    List.nodup_append.mpr ⟨unique, by simp, ?_⟩⟩
  intro old present new singleton same
  exact (Nat.ne_of_lt (activation_below present)) (same.trans (List.mem_singleton.mp singleton))

theorem bind_value_progress
    (valid : Valid (withCellSignatures users) policy registry ambient
      ⟨⟨⟨.bind parameter value body, scope, tail⟩, issued, completed⟩, activations⟩ result outgoing)
    (isValue : value.IsValue) :
    ∃ after, NamedAccessStep ambient
      ⟨⟨⟨.bind parameter value body, scope, tail⟩, issued, completed⟩, activations⟩ after ∧
      Valid (withCellSignatures users) policy registry ambient after result outgoing := by
  obtain ⟨input, expression, ports⟩ := effect_configuration_has_types valid.effects
  cases expression with
  | checked scopeTyped typed => cases typed with
      | bind initializer suffix =>
          exact ⟨_, ordinary_step_preserves_joint_configuration
            (.bind (typed_value_closed initializer isValue) (typed_suffix_ready suffix)) valid⟩

theorem application_value_progress
    (valid : Valid (withCellSignatures users) policy registry ambient
      ⟨⟨⟨.app function argument, scope, tail⟩, issued, completed⟩, activations⟩ result outgoing)
    (fv : function.IsValue) (av : argument.IsValue) :
    ∃ after, NamedAccessStep ambient
      ⟨⟨⟨.app function argument, scope, tail⟩, issued, completed⟩, activations⟩ after ∧
      Valid (withCellSignatures users) policy registry ambient after result outgoing := by
  obtain ⟨input, expression, ports⟩ := effect_configuration_has_types valid.effects
  cases expression with
  | checked scopeTyped typed => cases typed with
      | app functionTyped argumentTyped effects =>
          obtain ⟨parameter, body, rfl⟩ := typed_function_value functionTyped fv
          exact ⟨_, ordinary_step_preserves_joint_configuration
            (.beta (typed_value_closed argumentTyped av) (typed_value_closed functionTyped fv)) valid⟩

theorem branch_value_progress
    (valid : Valid (withCellSignatures users) policy registry ambient
      ⟨⟨⟨.branch condition yes no, scope, tail⟩, issued, completed⟩, activations⟩ result outgoing)
    (isValue : condition.IsValue) :
    ∃ after, NamedAccessStep ambient
      ⟨⟨⟨.branch condition yes no, scope, tail⟩, issued, completed⟩, activations⟩ after ∧
      Valid (withCellSignatures users) policy registry ambient after result outgoing := by
  obtain ⟨input, expression, ports⟩ := effect_configuration_has_types valid.effects
  cases expression with
  | checked scopeTyped typed => cases typed with
      | branch conditionTyped yesTyped noTyped =>
          obtain ⟨boolean, rfl⟩ := typed_boolean_value conditionTyped isValue
          cases boolean
          · exact ⟨_, ordinary_step_preserves_joint_configuration .ifFalse valid⟩
          · exact ⟨_, ordinary_step_preserves_joint_configuration .ifTrue valid⟩

/-- Active and dormant tickets are inspected structurally. A resume-only
    capture is not required to have a disposal plan. This checks current
    retained captures, not code which may create future captures. -/
inductive ClosingInterfaces (signature : Signature) (world : World) (registry : Registry) : Stack → Prop where
  | nil : ClosingInterfaces signature world registry .nil
  | push (rest : ClosingInterfaces signature world registry tail) :
      ClosingInterfaces signature world registry (.push frame tail)
  | live (known : registry owner = some record)
      (dispose : record.permissions.dispose = true → CloseReady signature world record.contract.closeEffects capture)
      (saved : ClosingInterfaces signature world registry capture)
      (rest : ClosingInterfaces signature world registry tail) :
      ClosingInterfaces signature world registry (.live owner input answer capture caller tail)
  | spent (rest : ClosingInterfaces signature world registry tail) :
      ClosingInterfaces signature world registry (.spent owner answer caller tail)

theorem closing_interface_at_live {front capture tail : Stack}
    (ready : ClosingInterfaces signature world registry
      (front.append (.live owner input answer capture caller tail))) :
    ∃ record, registry owner = some record ∧
      (record.permissions.dispose = true → CloseReady signature world record.contract.closeEffects capture) := by
  induction front with
  | nil => cases ready with
      | live known dispose saved rest => exact ⟨_, known, dispose⟩
  | push frame rest ih => cases ready with
      | push next => exact ih next
  | live name q a saved caller rest ihSaved ihRest => cases ready with
      | live known dispose saved next => exact ihRest next
  | spent name answer caller rest ih => cases ready with
      | spent next => exact ih next

theorem discard_demand_supplies_authority {registry : Registry}
    (checked : ScopedExecution.CodeDemand policy registry.usage scope (.discard binder) demand) :
    ∃ owner record, registry owner = some record ∧ scope.resolve binder = some owner ∧
      demand = [owner] ∧ record.permissions.dispose = true := by
  cases checked with
  | idle scope used => cases used
  | @consume owner rights binder expression known used =>
      cases used with
      | discard permitted =>
          cases stored : registry owner with
          | none => simp [Registry.usage, stored] at known
          | some record =>
              have same : record.permissions = rights := by simpa [Registry.usage, stored] using known
              exact ⟨owner, record, stored, by simp [Execution.Scope.resolve], rfl, same.symm ▸ permitted⟩


theorem focused_request_has_nonvalue_operand
    (position : ScopedExecution.Focus whole child context)
    (same : whole = .perform requested operation operand) : ¬ operand.IsValue := by
  cases position <;> cases same
  assumption

/-- An evaluated nonallocating request can only be a builtin operation; focus
    is excluded by the operand value and source capture allocates a ticket. -/
theorem nonallocating_request_is_ordinary
    (raw : RawStep before after [] [])
    (same : before.expression = .perform requested operation operand)
    (isValue : operand.IsValue) : OrdinaryStep before after := by
  cases raw with
  | focus plain position tail =>
      exact False.elim (focused_request_has_nonvalue_operand position same isValue)
  | readCell identity payload scope before after selected => exact .read selected
  | writeCell identity old new scope before after selected => exact .write selected
  | plug plain value closed scope tail | leaveHandler handler value closed scope tail
  | startCleanup action value closed scope tail | leaveClause owner answer value closed scope caller tail =>
      have value := closed.1
      dsimp only at same
      rw [same] at value
      cases value
  | bind | beta | ifTrue | ifFalse | enterHandler => cases same

theorem request_progress
    (valid : Valid (withCellSignatures users) policy registry ambient
      ⟨⟨⟨.perform (freezeEffect requested) operation operand, scope, stack⟩, issued, completed⟩, activations⟩ result outgoing)
    (isValue : operand.IsValue)
    (checks : AccessChecks ⟨.perform (freezeEffect requested) operation operand, scope, stack⟩ ambient) :
    (requested ∈ outgoing ∧ stack.erase.resolve requested = none) ∨
      ∃ next after, NamedAccessStep ambient
        ⟨⟨⟨.perform (freezeEffect requested) operation operand, scope, stack⟩, issued, completed⟩, activations⟩ after ∧
        Valid (withCellSignatures users) policy next ambient after result outgoing ∧ RegistryExtends registry next := by
  cases resolved : stack.erase.resolve requested with
  | none =>
      rcases current_request_is_interpreted_or_exported valid.effects with ⟨target, found⟩ | exported
      · simp [resolved] at found
      · exact Or.inl ⟨exported, rfl⟩
  | some target => cases target with
      | builtin identity =>
          obtain rfl := builtin_resolution_instance stack resolved
          obtain ⟨after, raw, effects⟩ := builtin_effect_progress valid.effects isValue resolved
          obtain ⟨step, afterValid⟩ := ordinary_step_preserves_joint_configuration
            (nonallocating_request_is_ordinary raw rfl isValue) valid
          exact Or.inr ⟨registry, _, step, afterValid, registry_extends_refl _⟩
      | source activation =>
          obtain ⟨cap, tail, handler, cut, active⟩ := handler_selection_of_resolution stack resolved
          obtain ⟨owner, fresh⟩ := fresh_owner_exists Owner.ticket (fun _ => rfl) valid.ledger.2
          obtain ⟨parameter, binder, body, output, residual, step, afterValid⟩ :=
            capture_constructs_joint_configuration cut valid isValue fresh checks
          exact Or.inr ⟨_, _, step, afterValid, registry_extends_fresh_insert (Joint.registry_fresh valid.registry fresh)⟩

/-- Usage supplies authority and the active boundary. The structural stack
    check supplies closing readiness for that same historical record; the plan
    and close identity are then constructed by the joint disposal theorem. -/
theorem discard_progress
    (valid : Valid signature policy registry ambient
      ⟨⟨⟨.discard binder, scope, stack⟩, issued, completed⟩, activations⟩ result outgoing)
    (interfaces : ClosingInterfaces signature (resourceWorld issued) registry stack)
    (checks : AccessChecks ⟨.discard binder, scope, stack⟩ ambient) :
    ∃ after, NamedAccessStep ambient
      ⟨⟨⟨.discard binder, scope, stack⟩, issued, completed⟩, activations⟩ after ∧
      Valid signature policy registry ambient after result outgoing := by
  obtain ⟨current, demand, code, control, accessible, balance, unique⟩ := valid.usage
  obtain ⟨owner, record, known, resolved, same, permitted⟩ := discard_demand_supplies_authority code
  have present : owner ∈ ScopedExecution.activeTickets stack := accessible (same ▸ List.mem_cons_self)
  obtain ⟨front, input, answer, capture, caller, tail, shape⟩ := active_ticket_has_boundary present
  subst stack
  obtain ⟨actual, registered, dispose⟩ := closing_interface_at_live interfaces
  have records : actual = record := Option.some.inj (registered.symm.trans known)
  subst actual
  have effectKnown : registry.effects owner = some record.contract := by simp [Registry.effects, known]
  obtain ⟨contract, found, inputEq, answerEq⟩ := active_live_contract valid.effects
  have contracts : contract = record.contract := Option.some.inj (found.symm.trans effectKnown)
  subst contract
  subst input
  subst answer
  exact ready_disposal_constructs_joint_configuration valid effectKnown resolved (dispose permitted) checks

/-- A terminal value is distinct from an outward operation observation. -/
def Terminal (configuration : Configuration) : Prop :=
  configuration.expression.IsValue ∧ configuration.stack = .nil

def OutwardRequest (configuration : Configuration) (outgoing : List Instance) : Prop :=
  ∃ requested operation operand,
    configuration.expression = .perform (freezeEffect requested) operation operand ∧ operand.IsValue ∧
    requested ∈ outgoing ∧ configuration.stack.erase.resolve requested = none

/-- All expression forms progress under the explicit prestate structural
    checks. Neither premise asks for an execution step or successor validity.
    The conclusion preserves Valid and old registry records, not ClosingInterfaces
    or future AccessChecks. -/
theorem current_progress
    (valid : Valid (withCellSignatures users) policy registry ambient before result outgoing)
    (interfaces : ClosingInterfaces (withCellSignatures users) (resourceWorld before.execution.issued)
      registry before.execution.configuration.stack)
    (checks : AccessChecks before.execution.configuration ambient) :
    Terminal before.execution.configuration ∨ OutwardRequest before.execution.configuration outgoing ∨
      ∃ next after, NamedAccessStep ambient before after ∧
        Valid (withCellSignatures users) policy next ambient after result outgoing ∧ RegistryExtends registry next := by
  obtain ⟨⟨⟨expression, scope, stack⟩, issued, completed⟩, activations⟩ := before
  obtain ⟨input, current, ports⟩ := effect_configuration_has_types valid.effects
  have form : CurrentForm expression := by
    cases current with
    | checked scopeTyped typed => exact typed_current_form typed
  cases form with
  | value isValue =>
      rcases value_progress valid isValue with terminal | step
      · exact Or.inl ⟨isValue, terminal⟩
      · obtain ⟨after, step, afterValid⟩ := step
        exact Or.inr (Or.inr ⟨registry, after, step, afterValid, registry_extends_refl _⟩)
  | focus position =>
      obtain ⟨plain, step, afterValid⟩ := focus_constructs_joint_configuration valid position
      exact Or.inr (Or.inr ⟨registry, _, step, afterValid, registry_extends_refl _⟩)
  | bind isValue =>
      obtain ⟨after, step, afterValid⟩ := bind_value_progress valid isValue
      exact Or.inr (Or.inr ⟨registry, after, step, afterValid, registry_extends_refl _⟩)
  | app fv av =>
      obtain ⟨after, step, afterValid⟩ := application_value_progress valid fv av
      exact Or.inr (Or.inr ⟨registry, after, step, afterValid, registry_extends_refl _⟩)
  | branch isValue =>
      obtain ⟨after, step, afterValid⟩ := branch_value_progress valid isValue
      exact Or.inr (Or.inr ⟨registry, after, step, afterValid, registry_extends_refl _⟩)
  | request isValue =>
      rcases request_progress valid isValue checks with outward | step
      · exact Or.inr (Or.inl ⟨_, _, _, rfl, isValue, outward⟩)
      · exact Or.inr (Or.inr step)
  | handler =>
      obtain ⟨activation, fresh⟩ := fresh_activation_exists valid.names.unique
      obtain ⟨handler, same, step, afterValid⟩ := handler_entry_constructs_joint_configuration valid fresh
      exact Or.inr (Or.inr ⟨registry, _, step, afterValid, registry_extends_refl _⟩)
  | resume isValue =>
      obtain ⟨after, step, afterValid⟩ := resume_value_progress valid isValue
      exact Or.inr (Or.inr ⟨registry, after, step, afterValid, registry_extends_refl _⟩)
  | discard =>
      obtain ⟨after, step, afterValid⟩ := discard_progress valid interfaces checks
      exact Or.inr (Or.inr ⟨registry, after, step, afterValid, registry_extends_refl _⟩)
  | resource isValue =>
      obtain ⟨after, step, afterValid⟩ := resource_entry_constructs_joint_configuration valid isValue
      exact Or.inr (Or.inr ⟨registry, after, step, afterValid, registry_extends_refl _⟩)
  | cleanup isValue =>
      obtain ⟨identity, fresh⟩ := fresh_owner_exists Owner.cleanup (fun _ => rfl) valid.ledger.2
      obtain ⟨action, step, afterValid⟩ := cleanup_entry_constructs_joint_configuration valid isValue fresh
      exact Or.inr (Or.inr ⟨registry, _, step, afterValid, registry_extends_refl _⟩)

theorem closed_current_progress
    (valid : Valid (withCellSignatures users) policy registry ambient before result [])
    (interfaces : ClosingInterfaces (withCellSignatures users) (resourceWorld before.execution.issued)
      registry before.execution.configuration.stack)
    (checks : AccessChecks before.execution.configuration ambient) :
    Terminal before.execution.configuration ∨
      ∃ next after, NamedAccessStep ambient before after ∧
        Valid (withCellSignatures users) policy next ambient after result [] ∧ RegistryExtends registry next := by
  rcases current_progress valid interfaces checks with terminal | outward | step
  · exact Or.inl terminal
  · obtain ⟨requested, operation, operand, same, isValue, impossible, missing⟩ := outward
    cases impossible
  · exact Or.inr step


/-- Empty control and an empty runtime ticket scope establish the local access
    checks directly, without inspecting a successor or a hypothetical plan. -/
theorem empty_control_access_checks : AccessChecks ⟨expression, .none, .nil⟩ ambient := by
  constructor
  · intro identity payload answer savedScope scope value tail same closed
    have shape := congrArg Configuration.stack same
    cases shape
  · intro requested operation operand scope whole cap tail handler same selected closed
    have shape := congrArg Configuration.stack same
    cases shape
    cases selected
  · intro binder owner scope caller input answer front capture tail plan same resolved built
    have sameScope := congrArg Configuration.scope same
    simp only at sameScope
    rw [← sameScope] at resolved
    cases resolved

/-- Closed expression checks suffice to start execution. This is a first-step
    theorem, not a claim that the source checks preserve future readiness. -/
theorem initial_progress
    (typed : Typed (withCellSignatures users) [] TypeEnv.empty .none [] expression result)
    (used : ScopedExpressions.Uses policy .none .available expression .available)
    (support : resourceDependencies expression.dependencies = []) :
    expression.IsValue ∨ ∃ registry after,
      NamedAccessStep [] ⟨⟨⟨expression, .none, .nil⟩, [], []⟩, []⟩ after ∧
      Valid (withCellSignatures users) policy registry [] after result [] := by
  rcases closed_current_progress (initial_configuration_valid typed used support) .nil
      empty_control_access_checks with terminal | step
  · exact Or.inl terminal.1
  · obtain ⟨registry, after, step, afterValid, extension⟩ := step
    exact Or.inr ⟨registry, after, step, afterValid⟩

namespace Examples
open Syntax.ControlUsageExamples (policy)

theorem source_resource_progress :
    ∃ registry after, NamedAccessStep [] ⟨AccessExamples.initial, []⟩ after ∧
      Valid (withCellSignatures users) policy registry [] after .integer [] := by
  rcases initial_progress (TypingExamples.resource_read_typed [] 4 17)
    (.resource .integer (.perform .resourceRef)) rfl with value | step
  · cases value
  · exact step

/-- Existing captures can have disposable rights without forcing the current
    expression to discard. The general theorem also handles this resume case. -/
theorem nested_resumption_progress :
    ∃ registry after, NamedAccessStep [] ScopedJoint.Examples.nestedCaptured after ∧
      Valid EffectExamples.twoRequests policy registry [] after .unit [] ∧
      RegistryExtends ScopedJoint.Examples.nestedRegistry registry := by
  have interfaces : ClosingInterfaces EffectExamples.twoRequests [] ScopedJoint.Examples.nestedRegistry
      ScopedJoint.Examples.nestedCaptured.execution.configuration.stack :=
    .live rfl (fun _ => .plain (.handler .nil)) (.push (.push .nil)) (.push .nil)
  have checks : AccessChecks ScopedJoint.Examples.nestedCaptured.execution.configuration [] :=
    ordinary_access_checks (by simp [Code.IsValue])
      (by intro requested operation operand same; cases same) (by intro binder same; cases same)
  rcases closed_current_progress ScopedJoint.Examples.nested_capture_valid interfaces checks with terminal | step
  · cases terminal.1
  · exact step

def protectedCapture (action : ActionData) : Stack :=
  .push (.running action .unit ScopedExecution.Examples.unit_closed) .nil

def record (dispose : Bool) : TicketRecord := ⟨⟨.unit, .unit, [], []⟩, ⟨true, dispose⟩⟩
def registry (dispose : Bool) : Registry := fun owner => if owner = 3 then some (record dispose) else none

theorem protected_resume_only_has_closing_interfaces (action : ActionData) :
    ClosingInterfaces signature world (registry false)
      (.live 3 .unit .unit (protectedCapture action) .none .nil) :=
  .live rfl (by intro denied; cases denied) (.push .nil) .nil

theorem protected_dispose_permission_rejects_closing_interfaces (action : ActionData) :
    ¬ ClosingInterfaces signature world (registry true)
      (.live 3 .unit .unit (protectedCapture action) .none .nil) := by
  intro checked
  cases checked with
  | live known dispose saved rest =>
      have same := Option.some.inj known
      cases same
      have impossible := dispose rfl
      cases impossible

def outward : NamedState := ⟨⟨⟨RetainedExamples.request, .none, .nil⟩, [], []⟩, []⟩

theorem outward_valid :
    Valid EffectExamples.twoRequests policy ScopedJoint.Examples.emptyRegistry [] outward .unit [.user 1 []] :=
  initial_configuration_valid (.perform rfl List.mem_cons_self .unit (List.nil_subset _)) (.perform .unit) rfl

/-- This outcome is forced by actual missing lookup: it cannot be silently
    treated as a return or an internal step, even though its outward row permits it. -/
theorem permitted_outward_request_is_observed :
    OutwardRequest outward.execution.configuration [.user 1 []] := by
  rcases current_progress outward_valid .nil empty_control_access_checks with terminal | observed | step
  · cases terminal.1
  · exact observed
  · obtain ⟨next, after, step, afterValid, extension⟩ := step
    cases step.1 with
    | event next created discharged raw freshOwners freshHandlers =>
        exact False.elim (RetainedExamples.unhandled_request_has_no_step raw)

end Examples

end Ash.OneShot.ScopedProgress

#print axioms Ash.OneShot.ScopedProgress.typed_current_form
#print axioms Ash.OneShot.ScopedProgress.fresh_owner_exists
#print axioms Ash.OneShot.ScopedProgress.activation_below
#print axioms Ash.OneShot.ScopedProgress.fresh_activation_exists
#print axioms Ash.OneShot.ScopedProgress.bind_value_progress
#print axioms Ash.OneShot.ScopedProgress.application_value_progress
#print axioms Ash.OneShot.ScopedProgress.branch_value_progress
#print axioms Ash.OneShot.ScopedProgress.closing_interface_at_live
#print axioms Ash.OneShot.ScopedProgress.discard_demand_supplies_authority
#print axioms Ash.OneShot.ScopedProgress.focused_request_has_nonvalue_operand
#print axioms Ash.OneShot.ScopedProgress.nonallocating_request_is_ordinary
#print axioms Ash.OneShot.ScopedProgress.request_progress
#print axioms Ash.OneShot.ScopedProgress.discard_progress
#print axioms Ash.OneShot.ScopedProgress.current_progress
#print axioms Ash.OneShot.ScopedProgress.closed_current_progress
#print axioms Ash.OneShot.ScopedProgress.empty_control_access_checks
#print axioms Ash.OneShot.ScopedProgress.initial_progress
#print axioms Ash.OneShot.ScopedProgress.Examples.source_resource_progress
#print axioms Ash.OneShot.ScopedProgress.Examples.nested_resumption_progress
#print axioms Ash.OneShot.ScopedProgress.Examples.protected_resume_only_has_closing_interfaces
#print axioms Ash.OneShot.ScopedProgress.Examples.protected_dispose_permission_rejects_closing_interfaces
#print axioms Ash.OneShot.ScopedProgress.Examples.outward_valid
#print axioms Ash.OneShot.ScopedProgress.Examples.permitted_outward_request_is_observed
