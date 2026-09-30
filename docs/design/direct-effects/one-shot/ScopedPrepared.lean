import ScopedProgress

/-!
Preservation of structural closing interfaces for the actual scoped machine.
Old captured interfaces survive control movement and fresh world growth. A
newly created capture checks its own conditional CloseReady obligation; this
local judgment is not source establishment of that obligation.
-/

namespace Ash.OneShot.ScopedPrepared
open Syntax Instantiation ScopedExpressions ScopedExecution ScopedTyping ScopedJoint ScopedProgress
open Joint (Registry TicketRecord)
open PreparedExecution (RegistryExtends registry_extends_refl registry_extends_fresh_insert)

theorem closing_interfaces_extension
    (checked : ClosingInterfaces signature world before stack) (extension : RegistryExtends before after) :
    ClosingInterfaces signature world after stack := by
  induction checked with
  | nil => exact .nil
  | push rest ih => exact .push ih
  | live known ready saved rest ihSaved ihRest => exact .live (extension _ _ known) ready ihSaved ihRest
  | spent rest ih => exact .spent ih

theorem closing_interfaces_append
    (front : ClosingInterfaces signature world registry left)
    (tail : ClosingInterfaces signature world registry right) :
    ClosingInterfaces signature world registry (left.append right) := by
  induction front with
  | nil => exact tail
  | push rest ih => exact .push ih
  | live known ready saved rest ihSaved ihRest => exact .live known ready saved ihRest
  | spent rest ih => exact .spent ih

theorem closing_interfaces_decompose {front tail : Stack}
    (checked : ClosingInterfaces signature world registry (front.append tail)) :
    ClosingInterfaces signature world registry front ∧ ClosingInterfaces signature world registry tail := by
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

theorem closing_interfaces_resume {front capture tail : Stack}
    (checked : ClosingInterfaces signature world registry
      (front.append (.live owner input answer capture caller tail))) :
    ClosingInterfaces signature world registry (capture.append (front.append (.spent owner answer caller tail))) := by
  obtain ⟨inside, boundary⟩ := closing_interfaces_decompose checked
  cases boundary with
  | live known ready saved outside =>
      exact closing_interfaces_append saved (closing_interfaces_append inside (.spent outside))

/-- Materialized closing control contains no live capture boundaries; its
    callback code and retirement authority are checked by other judgments. -/
theorem close_control_closing_interfaces (scope : Scope) (plan : List CloseEntry) :
    ClosingInterfaces signature world registry (closeControl scope plan) := by
  induction plan with
  | nil => exact .nil
  | cons entry rest ih => exact .push ih

theorem closing_interfaces_discard {front capture tail : Stack}
    (checked : ClosingInterfaces signature world registry
      (front.append (.live owner input answer capture caller tail))) :
    ClosingInterfaces signature world registry ((closeControl scope plan).append
      (.push (.closing closeId scope) (front.append (.spent owner answer caller tail)))) := by
  obtain ⟨inside, boundary⟩ := closing_interfaces_decompose checked
  cases boundary with
  | live known ready saved outside =>
      exact closing_interfaces_append (close_control_closing_interfaces _ _) (.push (closing_interfaces_append inside (.spent outside)))

theorem cell_update_preserves_closing_interfaces
    (update : CellUpdate identity old new before after)
    (checked : ClosingInterfaces signature world registry before) :
    ClosingInterfaces signature world registry after := by
  induction update with
  | hit => cases checked with
      | push rest => exact .push rest
  | push miss next ih => cases checked with
      | push rest => exact .push (ih rest)
  | live next ih => cases checked with
      | live known ready saved rest => exact .live known ready saved (ih rest)
  | spent next ih => cases checked with
      | spent rest => exact .spent (ih rest)

theorem closing_interfaces_world_weaken
    (checked : ClosingInterfaces signature world registry stack) (larger : world ⊆ nextWorld) :
    ClosingInterfaces signature nextWorld registry stack := by
  induction checked with
  | nil => exact .nil
  | push rest ih => exact .push ih
  | live known ready saved rest ihSaved ihRest =>
      exact .live known (fun permitted => close_ready_world_weaken (ready permitted) larger) ihSaved ihRest
  | spent rest ih => exact .spent ih

/-- Only the newly allocated live boundary needs new closing evidence. The
    capture constructor checks its stored contract and actual captured stack;
    it contains neither a next-step witness nor the full successor invariant. -/
inductive AllocationClosing (signature : Typing.Signature) (world : World) (registry : Registry) :
    List Owner → Stack → Prop where
  | none (absent : ∀ owner, Owner.ticket owner ∉ created) : AllocationClosing signature world registry created stack
  | capture (known : registry owner = some record)
      (ready : record.permissions.dispose = true → CloseReady signature world record.contract.closeEffects capture) :
      AllocationClosing signature world registry [.ticket owner] (.live owner input answer capture caller tail)

theorem raw_step_preserves_closing_interfaces
    (step : RawStep before after created discharged)
    (checked : ClosingInterfaces signature world registry before.stack)
    (extension : RegistryExtends registry nextRegistry)
    (larger : world ⊆ nextWorld)
    (allocation : AllocationClosing signature nextWorld nextRegistry created after.stack) :
    ClosingInterfaces signature nextWorld nextRegistry after.stack := by
  have beforePrepared := closing_interfaces_world_weaken (closing_interfaces_extension checked extension) larger
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
  | capture requested operation parameter binder owner operand body scope whole cap tail handler output cut clause closed environment =>
      rw [handler_cut_reconstructs cut] at beforePrepared
      obtain ⟨saved, outside⟩ := closing_interfaces_decompose beforePrepared
      cases allocation with
      | none absent => exact False.elim (absent owner (by simp))
      | capture known ready => exact .live known ready saved outside
  | resume => exact closing_interfaces_resume beforePrepared
  | discard => exact closing_interfaces_discard beforePrepared
  | leaveClause => cases beforePrepared with
      | spent rest => exact rest
  | finishClose | retire => cases beforePrepared with
      | push rest => exact rest
  | readCell identity payload scope before after selected => exact cell_update_preserves_closing_interfaces selected beforePrepared
  | writeCell identity old new scope before after selected => exact cell_update_preserves_closing_interfaces selected beforePrepared

/-- A non-request expression cannot allocate a captured ticket. -/
theorem nonrequest_allocates_no_ticket
    (step : RawStep before after created discharged)
    (notRequest : ∀ requested operation operand, before.expression ≠ .perform (freezeEffect requested) operation operand) :
    ∀ owner, Owner.ticket owner ∉ created := by
  cases step <;> try { intro owner; simp }
  rename_i requested operation parameter binder owner operand body scope whole capture tail handler output cut clause closed environment
  exact False.elim (notRequest requested operation operand rfl)

/-- Named non-request transitions preserve current closing interfaces,
    including generative resource entry and its larger historical world. -/
theorem nonrequest_named_step_preserves_closing_interfaces
    (step : NamedAccessStep ambient before after)
    (checked : ClosingInterfaces signature (resourceWorld before.execution.issued) registry before.execution.configuration.stack)
    (notRequest : ∀ requested operation operand,
      before.execution.configuration.expression ≠ .perform (freezeEffect requested) operation operand) :
    ClosingInterfaces signature (resourceWorld after.execution.issued) registry after.execution.configuration.stack := by
  cases step.execution with
  | event after created discharged raw freshOwners freshHandlers =>
      exact raw_step_preserves_closing_interfaces raw checked (registry_extends_refl _)
        (by rw [resource_world_append]; exact List.subset_append_left _ _)
        (.none (nonrequest_allocates_no_ticket raw notRequest))


/-- Registry history plus extension fixes every record when the event creates
    no ticket. Resource, cleanup and close-owner allocation may still occur. -/
theorem registry_unchanged_without_ticket_allocation
    (before : Joint.RegistryHistory registry issued)
    (after : Joint.RegistryHistory nextRegistry (issued ++ created))
    (extension : RegistryExtends registry nextRegistry)
    (absent : ∀ owner, Owner.ticket owner ∉ created) : registry = nextRegistry := by
  funext owner
  cases known : registry owner with
  | some record => exact (extension owner record known).symm
  | none =>
      cases nextKnown : nextRegistry owner with
      | none => rfl
      | some record =>
          have issuedOwner := (after owner).mp ⟨record, nextKnown⟩
          rcases List.mem_append.mp issuedOwner with old | new
          · obtain ⟨oldRecord, oldKnown⟩ := (before owner).mpr old
            rw [known] at oldKnown
            cases oldKnown
          · exact False.elim (absent owner new)

theorem nonrequest_named_registry_unchanged
    (step : NamedAccessStep ambient before after)
    (beforeHistory : Joint.RegistryHistory registry before.execution.issued)
    (afterHistory : Joint.RegistryHistory nextRegistry after.execution.issued)
    (extension : RegistryExtends registry nextRegistry)
    (notRequest : ∀ requested operation operand,
      before.execution.configuration.expression ≠ .perform (freezeEffect requested) operation operand) :
    registry = nextRegistry := by
  cases step.execution with
  | event after created discharged raw freshOwners freshHandlers =>
      exact registry_unchanged_without_ticket_allocation beforeHistory afterHistory extension
        (nonrequest_allocates_no_ticket raw notRequest)

/-- The joint invariant and current retained closing interfaces are checked
    independently. This does not assert readiness of future capture-producing code. -/
structure Ready (signature : Typing.Signature) (policy : TicketPolicy) (registry : Registry)
    (ambient : List Nat) (state : NamedState) (result : Ty) (outgoing : List Instance) : Prop where
  joint : Valid signature policy registry ambient state result outgoing
  closing : ClosingInterfaces signature (resourceWorld state.execution.issued) registry state.execution.configuration.stack

/-- All non-request expression forms progress while retaining current closing
    interfaces. An outward operation is excluded by syntax; no ticket allocation
    means the historical registry remains exactly the same. -/
theorem nonrequest_ready_progress
    (ready : Ready (Typing.withCellSignatures users) policy registry ambient before result outgoing)
    (checks : AccessChecks before.execution.configuration ambient)
    (notRequest : ∀ requested operation operand,
      before.execution.configuration.expression ≠ .perform (freezeEffect requested) operation operand) :
    Terminal before.execution.configuration ∨ ∃ after,
      NamedAccessStep ambient before after ∧
      Ready (Typing.withCellSignatures users) policy registry ambient after result outgoing := by
  rcases current_progress ready.joint ready.closing checks with terminal | outward | next
  · exact Or.inl terminal
  · obtain ⟨requested, operation, operand, same, isValue, exported, missing⟩ := outward
    exact False.elim (notRequest requested operation operand same)
  · obtain ⟨nextRegistry, after, step, afterValid, extension⟩ := next
    have same := nonrequest_named_registry_unchanged step ready.joint.registry afterValid.registry extension notRequest
    subst nextRegistry
    exact Or.inr ⟨after, step, afterValid, nonrequest_named_step_preserves_closing_interfaces step ready.closing notRequest⟩

theorem ready_value_progress
    (ready : Ready (Typing.withCellSignatures users) policy registry ambient before result outgoing)
    (isValue : before.execution.configuration.expression.IsValue) :
    Terminal before.execution.configuration ∨ ∃ after,
      NamedAccessStep ambient before after ∧
      Ready (Typing.withCellSignatures users) policy registry ambient after result outgoing := by
  apply nonrequest_ready_progress ready (value_access_checks ready.joint.effects isValue)
  intro requested operation operand same
  rw [same] at isValue
  cases isValue

/-- Initial expression checks establish the current closing invariant because
    no captures exist yet. They do not establish the future capture obligation. -/
theorem initial_ready
    (typed : Typed signature [] Typing.TypeEnv.empty .none outgoing expression result)
    (used : ScopedExpressions.Uses policy .none .available expression .available)
    (support : resourceDependencies expression.dependencies = []) :
    Ready signature policy (fun _ => none) [] ⟨⟨⟨expression, .none, .nil⟩, [], []⟩, []⟩ result outgoing :=
  ⟨initial_configuration_valid typed used support, .nil⟩

/-- Capture constructs its actual contract and joint successor first. The
    remaining implication asks only for that new capture's conditional structural
    readiness, at the chosen closing interface; old captures are preserved. -/
theorem capture_constructs_ready_obligation
    (cut : HandlerCut requested whole cap tail handler)
    (ready : Ready signature policy registry ambient
      ⟨⟨⟨.perform (freezeEffect requested) operation operand, scope, whole⟩, issued, completed⟩, activations⟩ result outgoing)
    (isValue : operand.IsValue) (fresh : (issued ++ [Owner.ticket owner]).Nodup)
    (checks : AccessChecks ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩ ambient) :
    ∃ (parameter binder : Nat) (body : Code) (output : Ty) (residual : List Instance),
      let record : TicketRecord := ⟨⟨output, handler.answer, residual, residual⟩, policy binder⟩
      let initial : NamedState := ⟨⟨⟨.perform (freezeEffect requested) operation operand, scope, whole⟩, issued, completed⟩, activations⟩
      let after : Configuration := ⟨body.subst parameter operand, .ticket binder owner,
        .live owner output handler.answer cap handler.scope tail⟩
      NamedAccessStep ambient initial (advanceState initial after [.ticket owner] []) ∧
      Valid signature policy (registry.insert owner record) ambient
        (advanceState initial after [.ticket owner] []) result outgoing ∧
      (((policy binder).dispose = true → CloseReady signature (resourceWorld issued) residual cap) →
        Ready signature policy (registry.insert owner record) ambient
          (advanceState initial after [.ticket owner] []) result outgoing) := by
  obtain ⟨parameter, binder, body, output, residual, step, valid⟩ :=
    capture_constructs_joint_configuration cut ready.joint isValue fresh checks
  refine ⟨parameter, binder, body, output, residual, step, valid, ?_⟩
  intro certificate
  have extension := registry_extends_fresh_insert
    (record := (⟨⟨output, handler.answer, residual, residual⟩, policy binder⟩ : TicketRecord))
    (Joint.registry_fresh ready.joint.registry fresh)
  have retained := closing_interfaces_extension ready.closing extension
  rw [handler_cut_reconstructs cut] at retained
  obtain ⟨saved, outside⟩ := closing_interfaces_decompose retained
  refine ⟨valid, ?_⟩
  change ClosingInterfaces signature (resourceWorld (issued ++ [.ticket owner])) _ _
  rw [resource_world_append]
  change ClosingInterfaces signature (resourceWorld issued ++ []) _ _
  rw [List.append_nil]
  exact .live (record := ⟨⟨output, handler.answer, residual, residual⟩, policy binder⟩)
    (by simp [Registry.insert]) certificate saved outside


namespace Examples

abbrev signature := EffectExamples.twoRequests
abbrev handler := UsageExecutionExamples.handler
abbrev request := UsageExecutionExamples.request
abbrev emptyRegistry := ScopedJoint.Examples.emptyRegistry

def policy (dispose : Bool) : TicketPolicy := fun _ => ⟨true, dispose⟩
def callback : Code := .lambda 0 request

theorem callback_typed :
    Typed signature [] Typing.TypeEnv.empty .none allowed callback
      (.function .unit .unit [.user 1 []] []) :=
  .lambda (.perform rfl List.mem_cons_self .unit (List.nil_subset _)) (List.nil_subset _) (List.nil_subset _)

def action : ActionData :=
  ⟨7, callback, typed_value_closed (callback_typed (allowed := [])) trivial, .none, .unit, [.user 1 []]⟩

def cap : Stack := .push (.running action .unit ScopedExecution.Examples.unit_closed)
  (.push (.handler handler) .nil)

def source : NamedState :=
  ⟨⟨⟨.handle (freezeEffect handler.effectInst) (.cleanup callback .unit) handler.clauses, .none, .nil⟩,
    [], []⟩, []⟩

def before : NamedState := ⟨⟨⟨request, .none, cap⟩, [.cleanup 7], []⟩, [8]⟩

theorem clauses_typed :
    ClausesTyped signature [] Typing.TypeEnv.empty handler.effectInst .unit [] handler.clauses :=
  .cons rfl (.resume .unit (List.nil_subset _) (List.nil_subset _)) .nil

theorem handler_coverage : Covers signature handler.effectInst handler.clauses := by
  intro operation input output known
  cases operation with
  | zero => simp [handler, UsageExecutionExamples.handler, clauseKeys]
  | succ n => simp [handler, UsageExecutionExamples.handler, signature, EffectExamples.twoRequests,
      Typing.withCellSignatures] at known

theorem handler_effects : EffectFrame signature tickets [] (.handler handler) [.user 1 []] [] :=
  .handler ⟨_, .none⟩ clauses_typed handler_coverage (by decide)

theorem source_ready (dispose : Bool) : Ready signature (policy dispose) emptyRegistry [] source .unit [] :=
  initial_ready
    (.handle (.cleanup callback_typed .unit (List.Subset.refl _)) clauses_typed handler_coverage
      (by decide) (List.nil_subset _))
    (.handle (.cleanup (.lambda (.perform .unit)) .unit) (.cons (.resume rfl .unit) .nil)) rfl

/-- Four actual source-prefix steps start the callback and reach its request.
    This source expression has no existing captured tickets at initialization. -/
theorem source_reaches_running_request : NamedAccessSteps [] source before := by
  let tail : Stack := .push (.handler handler) .nil
  have e0 := RawStep.enterHandler handler (.cleanup callback .unit) Stack.nil
  have e1 := RawStep.enterCleanup action .unit tail
  have e2 := RawStep.startCleanup action .unit ScopedExecution.Examples.unit_closed .none tail
  have e3 := RawStep.beta 0 request .unit .none cap ScopedExecution.Examples.unit_closed action.closed
  exact .next ⟨.event _ _ _ _ e0 (by decide) (by decide),
      resource_free_access_checks rfl (by intro _ same; cases same)⟩
    (.next ⟨.event _ _ _ _ e1 (by decide) (by decide),
      resource_free_access_checks rfl (by intro _ same; cases same)⟩
      (.next ⟨.event _ _ _ _ e2 (by decide) (by decide),
        resource_free_access_checks rfl (by intro _ same; cases same)⟩
        (.next ⟨.event _ _ _ _ e3 (by decide) (by decide),
          resource_free_access_checks rfl (by intro _ same; cases same)⟩ (.refl _))))

theorem before_joint (dispose : Bool) : Valid signature (policy dispose) emptyRegistry [] before .unit [] := by
  have runningEffects : EffectFrame signature emptyRegistry.effects []
      (.running action .unit ScopedExecution.Examples.unit_closed) [.user 1 []] [.user 1 []] :=
    .running ⟨_, .none⟩ callback_typed .unit (List.Subset.refl _)
  have control : ScopedExecution.StackUsage (policy dispose) emptyRegistry.usage cap [] [] :=
    .push (.running ⟨_, .none⟩ (.lambda (.perform .unit)) .unit) (List.nil_subset _)
      (.push (.handler ⟨_, .none⟩ (.cons (.resume rfl .unit) .nil)) (List.nil_subset _) .nil)
  constructor
  · exact ⟨.refl [Owner.cleanup 7], by decide⟩
  · refine ⟨?_, ?_, by decide⟩
    · intro owner
      simp [before, cap, Stack.erase, ExecFrame.erase, ActionData.erase, HandlerData.erase,
        handler, UsageExecutionExamples.handler, Control.ticketNames]
    · intro activation
      exact Nat.le_refl _
  · exact ⟨.push _ _ _ (.push _ _ _ (.nil []) (List.nil_subset _)) (List.nil_subset _), List.nil_subset _⟩
  · exact ⟨.unit, [.user 1 []], .checked .none (.perform rfl List.mem_cons_self .unit (List.nil_subset _)),
      .push (effect_frame_has_types runningEffects) (.push (effect_frame_has_types handler_effects) .nil),
      .push runningEffects (.push handler_effects (.nil (List.Subset.refl _)) (List.Subset.refl _)) (List.Subset.refl _)⟩
  · exact ⟨[], [], .idle .none (.perform .unit), control, List.nil_subset _, .refl [], by decide⟩
  · intro owner
    simp [emptyRegistry, ScopedJoint.Examples.emptyRegistry, before]
  · exact ⟨rfl, trivial, rfl, trivial⟩

theorem before_ready (dispose : Bool) : Ready signature (policy dispose) emptyRegistry [] before .unit [] :=
  ⟨before_joint dispose, .push (.push .nil)⟩

theorem actual_cut : HandlerCut handler.effectInst cap cap .nil handler :=
  .push _ _ _ _ _ (by simp [ExecFrame.erase, ActionData.erase, Frame.target]) (.hit handler .nil rfl)

theorem before_access_checks : AccessChecks before.execution.configuration [] :=
  resource_free_access_checks rfl (by intro _ same; cases same)

/-- Supplied extra dispose authority is not established by the initial source
    checks. Actual capture preserves Valid but fails the new closing interface.
    This is a model-policy counterexample, not a claim about accepted Core. -/
theorem initial_ready_does_not_establish_new_capture_readiness :
    Ready signature (policy true) emptyRegistry [] source .unit [] ∧
      NamedAccessSteps [] source before ∧ Ready signature (policy true) emptyRegistry [] before .unit [] ∧
      ∃ next after, NamedAccessStep [] before after ∧ Valid signature (policy true) next [] after .unit [] ∧
        ¬ ClosingInterfaces signature (resourceWorld after.execution.issued) next after.execution.configuration.stack := by
  obtain ⟨parameter, binder, body, output, residual, step, valid, obligation⟩ :=
    capture_constructs_ready_obligation actual_cut (before_ready true) trivial (owner := 3) (by decide) before_access_checks
  refine ⟨source_ready true, source_reaches_running_request, before_ready true, _, _, step, valid, ?_⟩
  intro checked
  cases checked with
  | live known dispose saved rest =>
      have same := Option.some.inj known
      cases same
      have impossible := dispose rfl
      cases impossible

/-- The same callback, clause and capture are compatible with resume-only
    authority. Only the independent policy changes; no plan is required. -/
theorem resume_only_capture_preserves_ready :
    ∃ next after, NamedAccessStep [] before after ∧ Ready signature (policy false) next [] after .unit [] := by
  obtain ⟨parameter, binder, body, output, residual, step, valid, obligation⟩ :=
    capture_constructs_ready_obligation actual_cut (before_ready false) trivial (owner := 3) (by decide) before_access_checks
  exact ⟨_, _, step, obligation (by intro denied; cases denied)⟩

end Examples

end Ash.OneShot.ScopedPrepared

#print axioms Ash.OneShot.ScopedPrepared.closing_interfaces_extension
#print axioms Ash.OneShot.ScopedPrepared.closing_interfaces_append
#print axioms Ash.OneShot.ScopedPrepared.closing_interfaces_decompose
#print axioms Ash.OneShot.ScopedPrepared.closing_interfaces_resume
#print axioms Ash.OneShot.ScopedPrepared.close_control_closing_interfaces
#print axioms Ash.OneShot.ScopedPrepared.closing_interfaces_discard
#print axioms Ash.OneShot.ScopedPrepared.cell_update_preserves_closing_interfaces
#print axioms Ash.OneShot.ScopedPrepared.closing_interfaces_world_weaken
#print axioms Ash.OneShot.ScopedPrepared.raw_step_preserves_closing_interfaces
#print axioms Ash.OneShot.ScopedPrepared.nonrequest_allocates_no_ticket
#print axioms Ash.OneShot.ScopedPrepared.nonrequest_named_step_preserves_closing_interfaces
#print axioms Ash.OneShot.ScopedPrepared.registry_unchanged_without_ticket_allocation
#print axioms Ash.OneShot.ScopedPrepared.nonrequest_named_registry_unchanged
#print axioms Ash.OneShot.ScopedPrepared.nonrequest_ready_progress
#print axioms Ash.OneShot.ScopedPrepared.ready_value_progress
#print axioms Ash.OneShot.ScopedPrepared.initial_ready
#print axioms Ash.OneShot.ScopedPrepared.capture_constructs_ready_obligation
#print axioms Ash.OneShot.ScopedPrepared.Examples.callback_typed
#print axioms Ash.OneShot.ScopedPrepared.Examples.clauses_typed
#print axioms Ash.OneShot.ScopedPrepared.Examples.handler_coverage
#print axioms Ash.OneShot.ScopedPrepared.Examples.handler_effects
#print axioms Ash.OneShot.ScopedPrepared.Examples.source_ready
#print axioms Ash.OneShot.ScopedPrepared.Examples.source_reaches_running_request
#print axioms Ash.OneShot.ScopedPrepared.Examples.before_joint
#print axioms Ash.OneShot.ScopedPrepared.Examples.before_ready
#print axioms Ash.OneShot.ScopedPrepared.Examples.actual_cut
#print axioms Ash.OneShot.ScopedPrepared.Examples.before_access_checks
#print axioms Ash.OneShot.ScopedPrepared.Examples.initial_ready_does_not_establish_new_capture_readiness
#print axioms Ash.OneShot.ScopedPrepared.Examples.resume_only_capture_preserves_ready
