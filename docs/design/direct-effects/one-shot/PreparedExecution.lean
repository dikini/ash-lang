import Progress

/-!
Preservation of structural disposal certificates through actual execution.
Old ticket records remain immutable; a new capture checks its own disposal
certificate when its independent permissions allow disposal. This is a local
preservation layer, not a proof of source-derived capture admission.
-/

namespace Ash.OneShot.PreparedExecution
open Syntax Execution Typing Joint Admission Progress

def RegistryExtends (before after : Registry) : Prop :=
  ∀ owner record, before owner = some record → after owner = some record

theorem registry_extends_refl (registry : Registry) : RegistryExtends registry registry :=
  fun _ _ known => known

theorem registry_extends_fresh_insert (fresh : registry owner = none) :
    RegistryExtends registry (registry.insert owner record) := by
  intro other old known
  by_cases same : other = owner
  · subst other
    rw [fresh] at known
    cases known
  · simpa [Registry.insert, same] using known

theorem prepared_captures_extension
    (checked : PreparedCaptures signature before stack) (extension : RegistryExtends before after) :
    PreparedCaptures signature after stack := by
  induction checked with
  | nil => exact .nil
  | push rest ih => exact .push ih
  | live known ready saved rest ihSaved ihRest => exact .live (extension _ _ known) ready ihSaved ihRest
  | spent rest ih => exact .spent ih

theorem prepared_captures_append
    (front : PreparedCaptures signature registry left)
    (tail : PreparedCaptures signature registry right) :
    PreparedCaptures signature registry (left.append right) := by
  induction front with
  | nil => exact tail
  | push rest ih => exact .push ih
  | live known ready saved rest ihSaved ihRest => exact .live known ready saved ihRest
  | spent rest ih => exact .spent ih

theorem prepared_captures_decompose {front tail : Stack}
    (checked : PreparedCaptures signature registry (front.append tail)) :
    PreparedCaptures signature registry front ∧ PreparedCaptures signature registry tail := by
  induction front with
  | nil => exact ⟨.nil, checked⟩
  | push frame rest ih => cases checked with
      | push next =>
          obtain ⟨inside, outside⟩ := ih next
          exact ⟨.push inside, outside⟩
  | live owner input answer capture caller rest ihCapture ihRest => cases checked with
      | live known ready saved next =>
          obtain ⟨inside, outside⟩ := ihRest next
          exact ⟨.live known ready saved inside, outside⟩
  | spent owner answer caller rest ih => cases checked with
      | spent next =>
          obtain ⟨inside, outside⟩ := ih next
          exact ⟨.spent inside, outside⟩

theorem prepared_captures_resume {front capture tail : Stack}
    (checked : PreparedCaptures signature registry
      (front.append (.live owner input answer capture caller tail))) :
    PreparedCaptures signature registry (capture.append (front.append (.spent owner answer caller tail))) := by
  obtain ⟨inside, boundary⟩ := prepared_captures_decompose checked
  cases boundary with
  | live known ready saved outside =>
      exact prepared_captures_append saved (prepared_captures_append inside (.spent outside))

/-- Materialized closing control contains no live capture boundaries; its
    callback code and retirement authority are checked by other judgments. -/
theorem close_control_prepared (scope : Scope) (plan : List CloseEntry) :
    PreparedCaptures signature registry (closeControl scope plan) := by
  induction plan with
  | nil => exact .nil
  | cons entry rest ih => exact .push ih

theorem prepared_captures_discard {front capture tail : Stack}
    (checked : PreparedCaptures signature registry
      (front.append (.live owner input answer capture caller tail))) :
    PreparedCaptures signature registry ((closeControl scope plan).append
      (.push (.closing closeId scope) (front.append (.spent owner answer caller tail)))) := by
  obtain ⟨inside, boundary⟩ := prepared_captures_decompose checked
  cases boundary with
  | live known ready saved outside =>
      exact prepared_captures_append (close_control_prepared _ _) (.push (prepared_captures_append inside (.spent outside)))

theorem cell_update_preserves_prepared
    (update : CellUpdate identity old new before after)
    (checked : PreparedCaptures signature registry before) :
    PreparedCaptures signature registry after := by
  induction update with
  | hit => cases checked with
      | push rest => exact .push rest
  | push miss next ih => cases checked with
      | push rest => exact .push (ih rest)
  | live next ih => cases checked with
      | live known ready saved rest => exact .live known ready saved (ih rest)
  | spent next ih => cases checked with
      | spent rest => exact .spent (ih rest)

/-- Only newly captured control needs a new certificate. This judgment checks
    a successful concrete plan, not the complete post-state invariant. -/
inductive AllocationPrepared (signature : Signature) (registry : Registry) : List Owner → Stack → Prop where
  | none (absent : ∀ owner, Owner.ticket owner ∉ created) : AllocationPrepared signature registry created stack
  | capture (known : registry owner = some record)
      (ready : record.permissions.dispose = true →
        Nonempty (PreparedDisposal signature record.contract.closeEffects capture)) :
      AllocationPrepared signature registry [.ticket owner] (.live owner input answer capture caller tail)

theorem raw_step_preserves_prepared
    (step : RawStep before after created discharged)
    (checked : PreparedCaptures signature registry before.stack)
    (extension : RegistryExtends registry nextRegistry)
    (allocation : AllocationPrepared signature nextRegistry created after.stack) :
    PreparedCaptures signature nextRegistry after.stack := by
  have beforePrepared := prepared_captures_extension checked extension
  cases step with
  | focus => exact .push beforePrepared
  | plug => cases beforePrepared with
      | push rest => exact rest
  | bind | beta | ifTrue | ifFalse => exact beforePrepared
  | enterHandler | enterCell | enterCleanup => exact .push beforePrepared
  | leaveHandler | leaveCell => cases beforePrepared with
      | push rest => exact rest
  | startCleanup => cases beforePrepared with
      | push rest => exact .push rest
  | finishCleanup => cases beforePrepared with
      | push rest => exact rest
  | capture requested operation parameter binder owner operand body scope whole cap tail handler output cut clause closed environment fresh =>
      rw [handler_cut_reconstructs cut] at beforePrepared
      obtain ⟨saved, outside⟩ := prepared_captures_decompose beforePrepared
      cases allocation with
      | none absent => exact False.elim (absent owner (by simp))
      | capture known ready => exact .live known ready saved outside
  | resume => exact prepared_captures_resume beforePrepared
  | discard => exact prepared_captures_discard beforePrepared
  | leaveClause => cases beforePrepared with
      | spent rest => exact rest
  | finishClose | retire => cases beforePrepared with
      | push rest => exact rest
  | readCell identity payload scope before after selected => exact cell_update_preserves_prepared selected beforePrepared
  | writeCell identity old new scope before after selected => exact cell_update_preserves_prepared selected beforePrepared

/-- A non-request expression cannot allocate a captured ticket. Ordinary
    resource and completion-owner allocation remains possible. -/
theorem nonrequest_allocates_no_ticket
    (step : RawStep before after created discharged)
    (notRequest : ∀ requested operation operand, before.expression ≠ .perform requested operation operand) :
    ∀ owner, Owner.ticket owner ∉ created := by
  cases step <;> try { intro owner; simp }
  rename_i requested operation parameter binder owner operand body scope whole capture tail handler output cut clause closed environment fresh
  exact False.elim (notRequest requested operation operand rfl)

theorem nonrequest_named_step_preserves_prepared
    (step : NamedAccessStep ambient before after)
    (checked : PreparedCaptures signature registry before.execution.configuration.stack)
    (notRequest : ∀ requested operation operand,
      before.execution.configuration.expression ≠ .perform requested operation operand) :
    PreparedCaptures signature registry after.execution.configuration.stack := by
  cases step.execution with
  | event after created discharged raw freshOwners freshHandlers =>
      exact raw_step_preserves_prepared raw checked (registry_extends_refl _)
        (.none (nonrequest_allocates_no_ticket raw notRequest))

/-- The joint invariant and retained certificates are independently checked.
    This state judgment does not yet certify every future source capture. -/
structure Ready (signature : Signature) (policy : TicketPolicy) (registry : Registry)
    (ambient : List Nat) (state : NamedState) (result : Ty) (outgoing : List Instance) : Prop where
  joint : Valid signature policy registry ambient state result outgoing
  captures : PreparedCaptures signature registry state.execution.configuration.stack

theorem ready_initial_configuration
    (typed : Typed signature TypeEnv.empty .none outgoing expression result)
    (used : Uses policy .none .available expression .available)
    (support : resourceDependencies expression.dependencies = []) :
    Ready signature policy (fun _ => none) []
      ⟨⟨⟨expression, .none, .nil⟩, [], []⟩, []⟩ result outgoing :=
  ⟨initial_configuration_valid typed used support, .nil⟩

/-- Value progress preserves both the joint invariant and retained readiness. -/
theorem ready_value_progress
    (ready : Ready signature policy registry ambient before result outgoing)
    (isValue : before.execution.configuration.expression.IsValue) :
    before.execution.configuration.stack = .nil ∨
    ∃ after, NamedAccessStep ambient before after ∧
      Ready signature policy registry ambient after result outgoing := by
  rcases value_progress ready.joint isValue with terminal | step
  · exact Or.inl terminal
  · obtain ⟨after, step, valid⟩ := step
    refine Or.inr ⟨after, step, valid, nonrequest_named_step_preserves_prepared step ready.captures ?_⟩
    intro requested operation operand same
    rw [same] at isValue
    exact isValue

theorem ready_resume_value_progress
    (ready : Ready signature policy registry ambient
      ⟨⟨⟨.resume binder value, scope, stack⟩, issued, completed⟩, activations⟩ result outgoing)
    (isValue : value.IsValue) :
    ∃ after, NamedAccessStep ambient
      ⟨⟨⟨.resume binder value, scope, stack⟩, issued, completed⟩, activations⟩ after ∧
      Ready signature policy registry ambient after result outgoing := by
  obtain ⟨after, step, valid⟩ := resume_value_progress ready.joint isValue
  exact ⟨after, step, valid, nonrequest_named_step_preserves_prepared step ready.captures
    (by intro requested operation operand same; cases same)⟩

/-- Prepared disposal now preserves its readiness premise in the successor;
    invoking and completing its callbacks is covered by the same raw theorem. -/
theorem ready_discard_progress
    (ready : Ready signature policy registry []
      ⟨⟨⟨.discard binder, scope, stack⟩, issued, completed⟩, activations⟩ result []) :
    ∃ after, NamedAccessStep []
      ⟨⟨⟨.discard binder, scope, stack⟩, issued, completed⟩, activations⟩ after ∧
      Ready signature policy registry [] after result [] := by
  obtain ⟨after, step, valid⟩ := prepared_discard_progress ready.joint ready.captures
  exact ⟨after, step, valid, nonrequest_named_step_preserves_prepared step ready.captures
    (by intro requested operation operand same; cases same)⟩

/-- Ordinary computation and exact builtin operations preserve readiness. -/
theorem ready_ordinary_step
    (step : OrdinaryStep before.execution.configuration after)
    (ready : Ready (withCellSignatures users) policy registry ambient before result outgoing) :
    NamedAccessStep ambient before (advanceState before after [] []) ∧
    Ready (withCellSignatures users) policy registry ambient (advanceState before after [] []) result outgoing := by
  obtain ⟨named, valid⟩ := Admission.ordinary_step_preserves step ready.joint
  exact ⟨named, valid, raw_step_preserves_prepared (ordinary_step_executes step) ready.captures
    (registry_extends_refl _) (.none (by intro owner; simp))⟩

/-- Type-directed capture first determines the actual clause and contract.
    Its new disposal certificate is then checked at that contract's precise
    effect bound. No universal stronger bound is imposed on callback effects. -/
theorem ready_capture_constructs {cap tail : Stack}
    (cut : HandlerCut requested whole cap tail handler)
    (ready : Ready signature policy registry ambient
      ⟨⟨⟨.perform requested operation operand, scope, whole⟩, issued, completed⟩, activations⟩ result outgoing)
    (isValue : operand.IsValue)
    (hygiene : ∀ parameter binder body, ClauseAt operation handler.clauses parameter binder body → ResourceFresh operand body)
    (fresh : (issued ++ [Owner.ticket owner]).Nodup)
    (checks : AccessChecks ⟨.perform requested operation operand, scope, whole⟩ ambient) :
    ∃ (parameter binder : Nat) (body : Expr) (output : Ty) (residual : List Instance),
      let record : TicketRecord := ⟨⟨output, handler.answer, residual, residual⟩, policy binder⟩
      let initial : NamedState := ⟨⟨⟨.perform requested operation operand, scope, whole⟩, issued, completed⟩, activations⟩
      let after : Configuration := ⟨body.subst parameter operand, .ticket binder owner,
        .live owner output handler.answer cap handler.scope tail⟩
      NamedAccessStep ambient initial (advanceState initial after [.ticket owner] []) ∧
      Valid signature policy (registry.insert owner record) ambient
        (advanceState initial after [.ticket owner] []) result outgoing ∧
      (((policy binder).dispose = true → Nonempty (PreparedDisposal signature residual cap)) →
        Ready signature policy (registry.insert owner record) ambient
          (advanceState initial after [.ticket owner] []) result outgoing) := by
  obtain ⟨parameter, binder, body, output, residual, named, valid⟩ :=
    capture_constructs_joint_configuration cut ready.joint isValue hygiene fresh checks
  refine ⟨parameter, binder, body, output, residual, named, valid, ?_⟩
  intro certificate
  refine ⟨valid, ?_⟩
  have extension := registry_extends_fresh_insert (record := (⟨⟨output, handler.answer, residual, residual⟩, policy binder⟩ : TicketRecord))
    (registry_fresh ready.joint.registry fresh)
  have retained := prepared_captures_extension ready.captures extension
  rw [handler_cut_reconstructs cut] at retained
  obtain ⟨saved, outside⟩ := prepared_captures_decompose retained
  exact .live (record := ⟨⟨output, handler.answer, residual, residual⟩, policy binder⟩)
    (by simp [Registry.insert]) certificate saved outside

/-- Discarding a capture containing only a source handler invokes no callback.
    Its actual empty plan is valid at any declared closing effect bound. -/
def handler_only_prepared (signature : Signature) (outward : List Instance) (handler : HandlerData) :
    PreparedDisposal signature outward (.push (.handler handler) .nil) :=
  ⟨[], rfl, .nil,
    .handler handler.erase handler.effectInst handler.activation .nil .nil .nil _ outward [] rfl (.nil _ _ _ _),
    .nil⟩

namespace Examples
open Execution.Examples
open ControlUsageExamples (policy)

def captureInitial : NamedState :=
  ⟨⟨⟨.perform (.user 1 []) 0 .unit, .none, .push (.handler discardHandler) .nil⟩, [], []⟩, [10]⟩

theorem capture_initial_ready :
    Ready RetainedExamples.userAndCells policy (fun _ => none) [] captureInitial .unit [] := by
  refine ⟨?_, .push .nil⟩
  constructor
  · simp [Ledger, RunState.erase, captureInitial, Stack.erase, Control.owners, Frame.owners,
      ExecFrame.erase, HandlerData.erase]
  · constructor
    · intro owner
      simp [captureInitial, Stack.erase, ExecFrame.erase, HandlerData.erase, Control.ticketNames]
    · intro activation
      simp [captureInitial, Stack.erase, ExecFrame.erase, HandlerData.erase, Control.activations,
        Frame.activation, discardHandler]
    · decide
  · constructor
    · refine .push _ _ _ (.nil _) ?_
      simp [ExecFrame.erase, HandlerData.erase, discardHandler, Clauses.dependencies, Expr.dependencies,
        Instance.resources, resourceDependencies, without]
    · simp [captureInitial, Expr.dependencies, resourceDependencies, instanceDependencies, Instance.resources]
  · refine ⟨.unit, [.user 1 []], .checked .none (.perform rfl (by simp) .unit), ?_, ?_⟩
    · exact .push (effect_frame_has_types Joint.Examples.discard_handler_effects) .nil
    · exact .push Joint.Examples.discard_handler_effects (.nil (fun _ used => used)) (fun _ used => used)
  · exact ⟨[], [], .idle .none (.perform .unit),
      .push (.handler ⟨_, .none⟩ (.cons (.discard rfl) .nil)) (List.nil_subset _) .nil,
      List.nil_subset _, .refl _, by decide⟩
  · intro owner
    simp [captureInitial]

/-- Actual capture with disposal permission has a certificate at its chosen
    contract, and preserves Ready under a fresh historical ticket record. -/
theorem pure_capture_preserves_ready :
    ∃ registry after, NamedAccessStep [] captureInitial after ∧
      Ready RetainedExamples.userAndCells policy registry [] after .unit [] := by
  have cut := HandlerCut.hit discardHandler Stack.nil rfl
  have access : AccessChecks captureInitial.execution.configuration [] :=
    selected_capture_access_checks cut (by simp [Expr.dependencies, resourceDependencies])
  obtain ⟨parameter, binder, body, output, residual, named, valid, upgrade⟩ :=
    ready_capture_constructs (owner := 3) cut capture_initial_ready (by trivial)
      (by intro parameter binder body clause; simp [ResourceFresh, Expr.dependencies])
      (by decide) access
  exact ⟨_, _, named, upgrade (fun _ => ⟨handler_only_prepared _ _ _⟩)⟩

theorem resource_disposal_preserves_ready :
    ∃ after, NamedAccessStep [] Joint.Examples.disposalInitial after ∧
      Ready RetainedExamples.userAndCells policy Joint.Examples.disposalRegistry [] after .unit [] :=
  ready_discard_progress ⟨Joint.Examples.disposal_initial_valid, Progress.Examples.disposal_initial_prepared⟩

end Examples

end Ash.OneShot.PreparedExecution

#print axioms Ash.OneShot.PreparedExecution.prepared_captures_extension
#print axioms Ash.OneShot.PreparedExecution.prepared_captures_resume
#print axioms Ash.OneShot.PreparedExecution.prepared_captures_discard
#print axioms Ash.OneShot.PreparedExecution.raw_step_preserves_prepared
#print axioms Ash.OneShot.PreparedExecution.ready_initial_configuration
#print axioms Ash.OneShot.PreparedExecution.ready_value_progress
#print axioms Ash.OneShot.PreparedExecution.ready_resume_value_progress
#print axioms Ash.OneShot.PreparedExecution.ready_discard_progress
#print axioms Ash.OneShot.PreparedExecution.ready_ordinary_step
#print axioms Ash.OneShot.PreparedExecution.ready_capture_constructs
#print axioms Ash.OneShot.PreparedExecution.Examples.pure_capture_preserves_ready
#print axioms Ash.OneShot.PreparedExecution.Examples.resource_disposal_preserves_ready
