import ClauseProgress

/-!
Progress with a preserved combined invariant for the current structural result
fragment. Application, disposal and cleanup have no result-admission rule here.
The underlying machine is unchanged; this is not a Core translation theorem.
-/

namespace Ash.OneShot.ClauseExecution
open Instantiation ScopedExpressions ScopedExecution ScopedPorts
open ScopedTyping (resourceWorld resource_world_append)
open DeclarationResults (signature)
open ClauseFrames (ConfigurationReturns StackReturns)
open GenerativeProgress (NoSourceRequest)

def SupportedHead : Code → Prop
  | .app _ _ | .discard _ | .cleanup _ _ => False
  | _ => True

theorem supported_head
    (checked : ClauseResults.Derives declarations environment world ticket code bound) :
    SupportedHead code := by
  cases checked with
  | existing checked =>
      have old := GenerativeProgress.supported_head checked
      cases code <;> simp_all [SupportedHead, GenerativeProgress.SupportedHead]
  | pair | bind | branch | perform | resource | resume | handle => trivial

theorem focus_boundary (focus : Focus whole child context) :
    NoSourceRequest ⟨whole, scope, stack⟩ := by
  intro requested operation operand capture tail handler same isValue cut
  exact False.elim (ScopedPortProgress.focused_request_has_nonvalue_operand focus same isValue)

theorem return_access_checks
    (checked : ConfigurationReturns declarations registry world configuration output)
    (boundary : NoSourceRequest configuration) : AccessChecks configuration ambient := by
  obtain ⟨environment, ticket, bound, scope, code, stack⟩ := checked
  constructor
  · intro identity payload answer savedScope scope value tail same closed
    rw [same] at code stack
    cases stack with
    | cell saved absent rest => exact fun member => absent (ClauseResults.value_support code closed member)
  · intro requested operation operand scope whole cap tail handler same cut closed
    exact False.elim (boundary requested operation operand cap tail handler
      (congrArg Configuration.expression same) closed.1 (same.symm ▸ cut))
  · intro binder owner scope caller input answer front cap tail plan same resolved built
    rw [same] at code
    exact False.elim (supported_head code)

theorem branch_results
    (checked : ConfigurationReturns declarations registry world
      ⟨.branch (.boolean condition) yes no, scope, stack⟩ output) :
    ConfigurationReturns declarations registry world
      ⟨if condition then yes else no, scope, stack⟩ output := by
  obtain ⟨environment, ticket, bound, scopeChecked, code, rest⟩ := checked
  refine ⟨environment, ticket, bound, scopeChecked, ?_, rest⟩
  cases code with
  | existing code => cases code with
      | leaf shape closed finite => simp [Code.IsValue] at shape
      | branch conditionChecked yesChecked noChecked =>
          cases condition
          · exact .existing noChecked
          · exact .existing yesChecked
  | branch conditionChecked yesChecked noChecked =>
      cases condition
      · exact noChecked
      · exact yesChecked

/-- Only the capture case needs a changed result registry. At all other
    current boundaries the same records survive the actual raw event. -/
theorem raw_preserves_results
    (step : RawStep before after created discharged)
    (fresh : (issued ++ created).Nodup)
    (checked : ConfigurationReturns declarations registry (resourceWorld issued) before output)
    (boundary : NoSourceRequest before) :
    ConfigurationReturns declarations registry (resourceWorld (issued ++ created)) after output := by
  cases step with
  | focus plain focus tail => simpa using (ClauseFrames.focus_step focus checked).2
  | plug plain value closed scope tail => simpa using (ClauseFrames.plug_step checked closed).2
  | bind name value body scope tail closed suffix => simpa using (ClauseFrames.bind_step checked closed suffix).2
  | beta | enterCleanup | discard =>
      obtain ⟨environment, ticket, bound, scope, code, stack⟩ := checked
      exact False.elim (supported_head code)
  | ifTrue => simpa using branch_results (condition := true) checked
  | ifFalse => simpa using branch_results (condition := false) checked
  | enterHandler handler body tail => simpa using (ClauseFrames.handler_entry_step checked).2
  | leaveHandler handler value closed scope tail => simpa using (ClauseFrames.handler_return_step checked closed).2
  | enterCell binder identity payload body scope answer tail closed =>
      have unused : identity ∉ resourceWorld issued := by
        intro member
        exact (List.nodup_append.mp fresh).2.2 (.resource identity)
          (ScopedTyping.mem_resource_world.mp member) (.resource identity) (by simp) rfl
      simpa [resource_world_append, resourceWorld] using (ClauseFrames.resource_step checked unused).2
  | leaveCell identity payload answer savedScope scope value closed tail =>
      simpa using (ClauseFrames.cell_return_step (ambient := []) checked closed).2.2
  | startCleanup | finishCleanup | finishClose | retire =>
      obtain ⟨environment, ticket, bound, scope, code, stack⟩ := checked
      cases stack
  | capture requested operation parameter binder owner operand body scope whole cap tail handler answer cut clause closed ready =>
      exact False.elim (boundary requested operation operand cap tail handler rfl closed.1 cut)
  | resume binder owner scope caller input answer front capture tail value closed resolved =>
      simpa using (ClauseFrames.resume_step resolved checked closed).2
  | leaveClause owner answer value closed scope caller tail =>
      simpa using (ClauseFrames.clause_return_step checked closed).2
  | readCell identity payload scope before after selected =>
      simpa using ClauseProgress.builtin_request_preserves_results (.readCell identity payload scope before after selected) rfl trivial checked
  | writeCell identity old new scope before after selected =>
      simpa using ClauseProgress.builtin_request_preserves_results (.writeCell identity old new scope before after selected) rfl ⟨trivial, trivial⟩ checked

theorem named_preserves_results
    (step : NamedAccessStep ambient before after)
    (checked : ConfigurationReturns declarations registry (resourceWorld before.execution.issued)
      before.execution.configuration output)
    (boundary : NoSourceRequest before.execution.configuration) :
    ConfigurationReturns declarations registry (resourceWorld after.execution.issued)
      after.execution.configuration output := by
  cases step.execution with
  | event after created discharged raw fresh freshHandlers => exact raw_preserves_results raw fresh checked boundary

theorem join_non_capture
    (valid : ClauseJoint.Valid declarations policy registry ambient before result outgoing bound)
    (boundary : NoSourceRequest before.execution.configuration)
    (step : NamedAccessStep ambient before after)
    (joint : ScopedPortJoint.Valid (signature declarations) policy registry.joint ambient after result outgoing) :
    ClauseJoint.Valid declarations policy registry ambient after result outgoing bound :=
  ⟨joint, named_preserves_results step valid.results boundary⟩

theorem current_progress
    (valid : ClauseJoint.Valid declarations policy registry ambient before result outgoing bound) :
    ScopedPortProgress.Terminal before.execution.configuration ∨
      ScopedPortProgress.OutwardRequest before.execution.configuration outgoing ∨
      ∃ next after, NamedAccessStep ambient before after ∧
        ClauseJoint.Valid declarations policy next ambient after result outgoing bound ∧
        ClauseJoint.RegistryExtends registry next := by
  obtain ⟨⟨⟨expression, scope, stack⟩, issued, completed⟩, activations⟩ := before
  obtain ⟨input, current, ports⟩ := effect_configuration_has_types valid.joint.effects
  have admitted : SupportedHead expression := by
    obtain ⟨environment, ticket, bound, scope, code, rest⟩ := valid.results
    exact supported_head code
  have form : ScopedPortProgress.CurrentForm expression := by
    cases current with
    | checked scopeTyped typed => exact ScopedPortProgress.typed_current_form typed
  cases form with
  | value isValue =>
      have boundary := GenerativeProgress.value_boundary (configuration := ⟨expression, scope, stack⟩) isValue
      rcases ScopedPortJoint.checked_value_progress valid.joint isValue
        (return_access_checks valid.results boundary) with terminal | next
      · exact Or.inl ⟨isValue, terminal⟩
      · obtain ⟨after, step, joint⟩ := next
        exact Or.inr (Or.inr ⟨registry, after, step, join_non_capture valid boundary step joint,
          ClauseJoint.registry_extends_refl _⟩)
  | focus position =>
      obtain ⟨plain, step, joint⟩ := ScopedPortJoint.focus_constructs_joint_configuration valid.joint position
      exact Or.inr (Or.inr ⟨registry, _, step, join_non_capture valid (focus_boundary position) step joint,
        ClauseJoint.registry_extends_refl _⟩)
  | bind isValue =>
      obtain ⟨after, step, joint⟩ := ScopedPortProgress.bind_value_progress valid.joint isValue
      exact Or.inr (Or.inr ⟨registry, after, step, join_non_capture valid
        (GenerativeProgress.nonrequest_boundary (by intro requested operation operand same; cases same)) step joint,
        ClauseJoint.registry_extends_refl _⟩)
  | branch isValue =>
      obtain ⟨after, step, joint⟩ := ScopedPortProgress.branch_value_progress valid.joint isValue
      exact Or.inr (Or.inr ⟨registry, after, step, join_non_capture valid
        (GenerativeProgress.nonrequest_boundary (by intro requested operation operand same; cases same)) step joint,
        ClauseJoint.registry_extends_refl _⟩)
  | request isValue =>
      rcases ClauseProgress.request_progress valid isValue with outward | next
      · exact Or.inr (Or.inl ⟨_, _, _, rfl, isValue, outward⟩)
      · exact Or.inr (Or.inr next)
  | handler =>
      obtain ⟨activation, fresh⟩ := ScopedPortProgress.fresh_activation_exists valid.joint.names.unique
      obtain ⟨handler, active, effectEq, clausesEq, scopeEq, step, afterValid⟩ := ClauseJoint.handler_entry_preserves valid fresh
      exact Or.inr (Or.inr ⟨registry, _, step, afterValid, ClauseJoint.registry_extends_refl _⟩)
  | resume isValue =>
      obtain ⟨after, step, afterValid⟩ := ClauseProgress.resume_progress valid isValue
      exact Or.inr (Or.inr ⟨registry, after, step, afterValid, ClauseJoint.registry_extends_refl _⟩)
  | resource isValue =>
      obtain ⟨after, step, joint⟩ := ScopedPortJoint.resource_entry_constructs_joint_configuration valid.joint isValue
      exact Or.inr (Or.inr ⟨registry, after, step, join_non_capture valid
        (GenerativeProgress.nonrequest_boundary (by intro requested operation operand same; cases same)) step joint,
        ClauseJoint.registry_extends_refl _⟩)
  | app | discard | cleanup => exact False.elim admitted

theorem closed_progress
    (valid : ClauseJoint.Valid declarations policy registry ambient before result [] bound) :
    ScopedPortProgress.Terminal before.execution.configuration ∨
      ∃ next after, NamedAccessStep ambient before after ∧
        ClauseJoint.Valid declarations policy next ambient after result [] bound ∧
        ClauseJoint.RegistryExtends registry next := by
  rcases current_progress valid with terminal | outward | next
  · exact Or.inl terminal
  · obtain ⟨requested, operation, operand, same, value, exported, missing⟩ := outward
    cases exported
  · exact Or.inr next

theorem initial_progress
    (typed : Typed (signature declarations) [] TypeEnv.empty .none [] expression result)
    (used : Uses policy .none .available expression .available)
    (support : Syntax.resourceDependencies expression.dependencies = [])
    (checked : ClauseResults.Derives declarations environment [] .none expression bound) :
    let initial : NamedState := ⟨⟨⟨expression, .none, .nil⟩, [], []⟩, []⟩
    ScopedPortProgress.Terminal initial.execution.configuration ∨
      ∃ registry after, NamedAccessStep [] initial after ∧
        ClauseJoint.Valid declarations policy registry [] after result [] bound ∧
        ClauseJoint.RegistryExtends (fun _ => none) registry :=
  closed_progress (ClauseJoint.initial_configuration_valid typed used support checked)

theorem certified_endpoint_progress
    (execution : ClauseJoint.CertifiedSteps declarations policy ambient result [] bound
      registry before finalRegistry after) :
    ScopedPortProgress.Terminal after.execution.configuration ∨
      ∃ next later, NamedAccessStep ambient after later ∧
        ClauseJoint.Valid declarations policy next ambient later result [] bound ∧
        ClauseJoint.RegistryExtends finalRegistry next :=
  closed_progress (ClauseJoint.certified_final execution)

/-- A length index on existing machine steps, with no additional transition. -/
inductive CountedSteps (ambient : List Nat) : Nat → NamedState → NamedState → Prop where
  | zero : CountedSteps ambient 0 state state
  | next (step : NamedAccessStep ambient before middle)
      (rest : CountedSteps ambient count middle after) :
      CountedSteps ambient (count + 1) before after

theorem counted_execution (steps : CountedSteps ambient count before after) :
    NamedAccessSteps ambient before after := by
  induction steps with
  | zero => exact .refl _
  | next step rest ih => exact .next step ih

/-- Count and invariants describe one shared sequence of actual events. -/
inductive CertifiedPrefix (declarations : DeclarationRegistry) (policy : Syntax.TicketPolicy)
    (ambient : List Nat) (result : Port) (outgoing : List Instance) (bound : List Nat) :
    Nat → ClauseJoint.Registry → NamedState → ClauseJoint.Registry → NamedState → Prop where
  | zero (valid : ClauseJoint.Valid declarations policy registry ambient state result outgoing bound) :
      CertifiedPrefix declarations policy ambient result outgoing bound 0 registry state registry state
  | next (valid : ClauseJoint.Valid declarations policy registry ambient before result outgoing bound)
      (step : NamedAccessStep ambient before middle)
      (extended : ClauseJoint.RegistryExtends registry nextRegistry)
      (rest : CertifiedPrefix declarations policy ambient result outgoing bound count nextRegistry middle finalRegistry after) :
      CertifiedPrefix declarations policy ambient result outgoing bound (count + 1) registry before finalRegistry after

theorem prefix_counted
    (checked : CertifiedPrefix declarations policy ambient result outgoing bound count registry before finalRegistry after) :
    CountedSteps ambient count before after := by
  induction checked with
  | zero valid => exact .zero
  | next valid step extended rest ih => exact .next step ih

theorem prefix_certified
    (checked : CertifiedPrefix declarations policy ambient result outgoing bound count registry before finalRegistry after) :
    ClauseJoint.CertifiedSteps declarations policy ambient result outgoing bound registry before finalRegistry after := by
  induction checked with
  | zero valid => exact .refl valid
  | next valid step extended rest ih => exact .next valid step extended ih

/-- From one initial invariant, construct as many checked actual steps as
    requested, unless the computation reaches an ordinary terminal first. -/
theorem finite_prefix (fuel : Nat)
    (valid : ClauseJoint.Valid declarations policy registry ambient before result [] bound) :
    ∃ finalRegistry after count, count ≤ fuel ∧
      CertifiedPrefix declarations policy ambient result [] bound count registry before finalRegistry after ∧
      (count = fuel ∨ ScopedPortProgress.Terminal after.execution.configuration) := by
  induction fuel generalizing registry before with
  | zero => exact ⟨registry, before, 0, Nat.le_refl _, .zero valid, Or.inl rfl⟩
  | succ fuel ih =>
      rcases closed_progress valid with terminal | next
      · exact ⟨registry, before, 0, Nat.zero_le _, .zero valid, Or.inr terminal⟩
      · obtain ⟨nextRegistry, middle, step, afterValid, extension⟩ := next
        obtain ⟨finalRegistry, after, count, bounded, checked, outcome⟩ := ih afterValid
        refine ⟨finalRegistry, after, count + 1, Nat.succ_le_succ bounded,
          .next valid step extension checked, ?_⟩
        rcases outcome with exhausted | terminal
        · exact Or.inl (congrArg Nat.succ exhausted)
        · exact Or.inr terminal

theorem initial_finite_prefix (fuel : Nat)
    (typed : Typed (signature declarations) [] TypeEnv.empty .none [] expression result)
    (used : Uses policy .none .available expression .available)
    (support : Syntax.resourceDependencies expression.dependencies = [])
    (checked : ClauseResults.Derives declarations environment [] .none expression bound) :
    let initial : NamedState := ⟨⟨⟨expression, .none, .nil⟩, [], []⟩, []⟩
    ∃ registry after count, count ≤ fuel ∧
      CertifiedPrefix declarations policy [] result [] bound count (fun _ => none) initial registry after ∧
      (count = fuel ∨ ScopedPortProgress.Terminal after.execution.configuration) :=
  finite_prefix fuel (ClauseJoint.initial_configuration_valid typed used support checked)

theorem terminal_accounting
    (valid : ClauseJoint.Valid declarations policy registry ambient state result outgoing bound)
    (terminal : ScopedPortProgress.Terminal state.execution.configuration) :
    state.execution.issued.Perm state.execution.completed ∧ state.execution.completed.Nodup := by
  have ledger := valid.joint.ledger
  have completed := ledger_no_double_completion ledger
  obtain ⟨⟨⟨value, scope, stack⟩, issued, done⟩, activations⟩ := state
  obtain ⟨isValue, rfl⟩ := terminal
  exact ⟨by simpa [RunState.erase, Stack.erase, Control.owners] using ledger.1, completed⟩

theorem terminal_result_support
    (valid : ClauseJoint.Valid declarations policy registry ambient state result outgoing bound)
    (terminal : ScopedPortProgress.Terminal state.execution.configuration) :
    Syntax.resourceDependencies state.execution.configuration.expression.dependencies ⊆ bound := by
  obtain ⟨environment, ticket, input, scope, code, stack⟩ := valid.results
  have closed := ClauseJoint.current_closed_value valid terminal.1
  rw [terminal.2] at stack
  cases stack with
  | nil included => exact (ClauseResults.value_support code closed).trans included

end Ash.OneShot.ClauseExecution

#print axioms Ash.OneShot.ClauseExecution.supported_head
#print axioms Ash.OneShot.ClauseExecution.focus_boundary
#print axioms Ash.OneShot.ClauseExecution.return_access_checks
#print axioms Ash.OneShot.ClauseExecution.branch_results
#print axioms Ash.OneShot.ClauseExecution.raw_preserves_results
#print axioms Ash.OneShot.ClauseExecution.named_preserves_results
#print axioms Ash.OneShot.ClauseExecution.join_non_capture
#print axioms Ash.OneShot.ClauseExecution.current_progress
#print axioms Ash.OneShot.ClauseExecution.closed_progress
#print axioms Ash.OneShot.ClauseExecution.initial_progress
#print axioms Ash.OneShot.ClauseExecution.certified_endpoint_progress
#print axioms Ash.OneShot.ClauseExecution.counted_execution
#print axioms Ash.OneShot.ClauseExecution.prefix_counted
#print axioms Ash.OneShot.ClauseExecution.prefix_certified
#print axioms Ash.OneShot.ClauseExecution.finite_prefix
#print axioms Ash.OneShot.ClauseExecution.initial_finite_prefix
#print axioms Ash.OneShot.ClauseExecution.terminal_accounting
#print axioms Ash.OneShot.ClauseExecution.terminal_result_support
