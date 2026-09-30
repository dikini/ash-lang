import DeclaredClosingInvariant

/-! Connect deterministic computation to the action-guarded state invariant.
These transitions allocate no source annotations. Existing substitution, branch,
usage, ownership, source and result proofs determine the same actual successor.
The handler-cut decomposition exposes the interface needed for the separate
capture-admission work; it does not assume or establish that admission.
-/
namespace Ash.OneShot.ScopedActionInterfaces
open ScopedExpressions ScopedExecution ScopedPorts

theorem bind_preserves_configuration
    (typed : ConfigurationConnected signature tickets actions world ⟨.bind parameter value body, scope, tail⟩ result outgoing)
    (isValue : value.IsValue) :
    ConfigurationConnected signature tickets actions world ⟨body.subst parameter value, scope, tail⟩ result outgoing := by
  obtain ⟨input, effects, expression, stack, effectStack⟩ := typed
  cases expression with
  | checked scopeTyped expression => cases expression with
      | bind initializer suffix =>
          exact ⟨input, effects, .checked scopeTyped
            (typed_substitution suffix (typed_value_transport initializer isValue .none [])
              (typed_value_closed initializer isValue)), stack, effectStack⟩

theorem beta_preserves_configuration
    (typed : ConfigurationConnected signature tickets actions world ⟨.app (.lambda parameter body) value, scope, tail⟩ result outgoing)
    (isValue : value.IsValue) :
    ConfigurationConnected signature tickets actions world ⟨body.subst parameter value, .none, tail⟩ result outgoing := by
  obtain ⟨input, effects, expression, stack, effectStack⟩ := typed
  cases expression with
  | checked scopeTyped expression => cases expression with
      | app function argument available => cases function with
          | lambda bodyTyped formed =>
              exact ⟨input, _, .checked .none
                (typed_substitution bodyTyped (typed_value_transport argument isValue .none [])
                  (typed_value_closed argument isValue)), stack, input_weaken effectStack available⟩

theorem branch_preserves_configuration
    (typed : ConfigurationConnected signature tickets actions world ⟨.branch (.boolean condition) yes no, scope, tail⟩ result outgoing) :
    ConfigurationConnected signature tickets actions world ⟨if condition then yes else no, scope, tail⟩ result outgoing := by
  obtain ⟨input, effects, expression, stack, effectStack⟩ := typed
  cases expression with
  | checked scopeTyped expression => cases expression with
      | branch test yesTyped noTyped =>
          cases condition
          · exact ⟨input, effects, .checked scopeTyped noTyped, stack, effectStack⟩
          · exact ⟨input, effects, .checked scopeTyped yesTyped, stack, effectStack⟩

theorem cell_update_preserves_connections
    (update : CellUpdate identity old new before after)
    (typed : Connected signature tickets actions world before incoming outgoing) :
    Connected signature tickets actions world after incoming outgoing := by
  induction update generalizing incoming with
  | hit => cases typed with
      | push frame rest bound => cases frame with
          | cell scope noEscape => exact .push (.cell scope noEscape) rest bound
  | push miss next ih => cases typed with
      | push frame rest bound => exact .push frame (ih rest) bound
  | live next ih => cases typed with
      | live known actionKnown scope saved rest resume close bound => exact .live known actionKnown scope saved (ih rest) resume close bound
  | spent next ih => cases typed with
      | spent known scope rest bound => exact .spent known scope (ih rest) bound

theorem cell_read_preserves_configuration
    (typed : ConfigurationConnected (withCellSignatures users) tickets actions world
      ⟨.perform (Instantiation.freezeEffect (.cell identity)) 0 (.resourceRef (.activation identity)), scope, before⟩ result outgoing)
    (selected : CellUpdate identity payload payload before after) :
    ConfigurationConnected (withCellSignatures users) tickets actions world ⟨.integer payload, scope, after⟩ result outgoing := by
  obtain ⟨input, effects, expression, stack, effectStack⟩ := typed
  cases expression with
  | checked scopeTyped expression =>
          obtain ⟨input, operation, available, operand⟩ := typed_perform_inversion expression
          simp only [withCellSignatures, Option.some.injEq, Prod.mk.injEq] at operation
          obtain ⟨rfl, rfl⟩ := operation
          exact ⟨.integer, [], .checked scopeTyped .integer, cell_update_preserves_stack_typing selected stack,
            input_weaken (cell_update_preserves_connections selected effectStack) (by simp)⟩

theorem cell_write_preserves_configuration
    (typed : ConfigurationConnected (withCellSignatures users) tickets actions world
      ⟨.perform (Instantiation.freezeEffect (.cell identity)) 1 (.pair (.resourceRef (.activation identity)) (.integer new)), scope, before⟩ result outgoing)
    (selected : CellUpdate identity old new before after) :
    ConfigurationConnected (withCellSignatures users) tickets actions world ⟨.unit, scope, after⟩ result outgoing := by
  obtain ⟨input, effects, expression, stack, effectStack⟩ := typed
  cases expression with
  | checked scopeTyped expression =>
          obtain ⟨input, operation, available, operand⟩ := typed_perform_inversion expression
          simp only [withCellSignatures, Option.some.injEq, Prod.mk.injEq] at operation
          obtain ⟨rfl, rfl⟩ := operation
          exact ⟨.unit, [], .checked scopeTyped .unit, cell_update_preserves_stack_typing selected stack,
            input_weaken (cell_update_preserves_connections selected effectStack) (by simp)⟩


/-- The existing nonallocating-request classification selects the actual cell
update. No annotation-bearing entry is hidden in this preservation lemma. -/
theorem raw_builtin_preserves_configuration
    (typed : ConfigurationConnected (withCellSignatures users) tickets actions world before result outgoing)
    (raw : RawStep before after [] [])
    (same : before.expression = .perform effect operation operand) (isValue : operand.IsValue) :
    ConfigurationConnected (withCellSignatures users) tickets actions world after result outgoing := by
  have ordinary := ScopedPortProgress.nonallocating_request_is_ordinary raw same isValue
  cases ordinary with
  | bind | beta | ifTrue | ifFalse => cases same
  | read selected => exact cell_read_preserves_configuration typed selected
  | write selected => exact cell_write_preserves_configuration typed selected

/-- Reuse the existing ready-form classification and value/focus exclusions. -/
theorem raw_ready_preserves_configuration
    (ready : RecursiveExpressions.Ready before.expression)
    (step : RawStep before after created discharged)
    (typed : ConfigurationConnected signature tickets actions world before result outgoing) :
    ConfigurationConnected signature tickets actions world after result outgoing := by
  cases step with
  | focus plain focus tail => exact False.elim (RecursiveExpressions.ready_not_focus ready focus)
  | plug plain value closed scope tail => exact False.elim (RecursiveExpressions.ready_not_value ready closed.1)
  | leaveHandler handler value closed scope tail => exact False.elim (RecursiveExpressions.ready_not_value ready closed.1)
  | leaveCell identity payload answer savedScope scope value closed tail => exact False.elim (RecursiveExpressions.ready_not_value ready closed.1)
  | startCleanup action saved closed scope tail => exact False.elim (RecursiveExpressions.ready_not_value ready closed.1)
  | leaveClause owner answer value closed scope caller tail => exact False.elim (RecursiveExpressions.ready_not_value ready closed.1)
  | bind parameter value body scope tail closed environment => exact bind_preserves_configuration typed closed.1
  | beta parameter body value scope tail closed closure => exact beta_preserves_configuration typed closed.1
  | ifTrue => exact branch_preserves_configuration typed
  | ifFalse => exact branch_preserves_configuration typed
  | enterHandler | enterCell | enterCleanup | finishCleanup | capture | resume | discard | finishClose | retire | readCell | writeCell => cases ready

/-- The existing exact cut removes one source handler. The same residual
connects its captured segment, surviving caller and checked handler frame. -/
theorem handler_cut_decomposition
    (cut : HandlerCut requested whole capture tail handler)
    (typed : Connected signature tickets actions world whole incoming outgoing) :
    ∃ residual, Connected signature tickets actions world capture incoming residual ∧
      Connected signature tickets actions world tail residual outgoing ∧
      EffectFrame signature tickets world (.handler handler) (handler.effectInst :: residual) residual := by
  induction cut generalizing incoming with
  | hit handler tail same => cases typed with
      | push frame rest bound => cases frame with
          | handler scope clauses coverage unique =>
              exact ⟨_, .push (.handler scope clauses coverage unique) (.nil (List.Subset.refl _)) bound,
                rest, .handler scope clauses coverage unique⟩
  | push frame rest capture tail handler miss next ih => cases typed with
      | push frame rest bound =>
          obtain ⟨residual, inside, outside, checkedHandler⟩ := ih rest
          exact ⟨residual, .push frame inside bound, outside, checkedHandler⟩
  | live owner input answer saved caller rest capture tail handler next ih => cases typed with
      | live known actionKnown scope saved rest resume close bound =>
          obtain ⟨residual, inside, outside, checkedHandler⟩ := ih rest
          exact ⟨residual, .live known actionKnown scope saved inside resume close bound, outside, checkedHandler⟩
  | spent owner answer caller rest capture tail handler next ih => cases typed with
      | spent known scope rest bound =>
          obtain ⟨residual, inside, outside, checkedHandler⟩ := ih rest
          exact ⟨residual, .spent known scope inside bound, outside, checkedHandler⟩

end Ash.OneShot.ScopedActionInterfaces

namespace Ash.OneShot.DeclaredClosingInvariant
open ScopedExpressions ScopedExecution CoherentSourceTypes
open ScopedTyping (resourceWorld)

/-- Join the source-produced successor to interface and certificate preservation.
The progress theorem below derives that successor rather than assuming it. -/
theorem ready_preserves_prepared
    (before : Prepared operations declarations policy registry tables state output demand row bound)
    (ready : RecursiveExpressions.Ready state.execution.configuration.expression)
    (step : NamedAccessStep [] state after)
    (current : DeclaredExecution.Valid operations declarations policy registry tables [] [] after output nextDemand nextRow bound) :
    Prepared operations declarations policy registry tables after output nextDemand nextRow bound := by
  obtain ⟨actions, usage, history, requests, closing⟩ := before.actions
  obtain ⟨nextActions, nextUsage, nextHistory, actionExtension⟩ :=
    ScopedActionUsage.named_step_preserves step usage history
  cases step.execution with
  | event next created discharged raw freshOwners freshHandlers =>
      have requests := ScopedActionInterfaces.raw_ready_preserves_configuration ready raw requests
      have unique : (ownedTickets next.stack).Nodup := by
        cases current.source with
        | checked _ _ unique _ _ => exact unique
      have larger : resourceWorld state.execution.issued ⊆ resourceWorld (state.execution.issued ++ created) := by
        rw [ScopedTyping.resource_world_append]
        exact List.subset_append_left _ _
      refine ⟨current, ⟨nextActions, nextUsage, nextHistory,
        ScopedActionInterfaces.configuration_action_extension
          (ScopedActionInterfaces.configuration_world_weaken requests larger) actionExtension, ?_⟩⟩
      apply raw_step_preserves_retained raw closing (fun _ _ known => known) actionExtension larger _ unique
      apply Allocation.none (ScopedPortPrepared.nonrequest_allocates_no_ticket raw ?_)
      intro requested operation operand impossible
      rw [impossible] at ready
      cases ready

/-- Ready bind, application and branch expressions construct an actual step
and preserve the complete action-guarded state. Demand is preserved up to
permutation, and the checked source row decreases by sublist. -/
theorem ready_progress
    (before : Prepared operations declarations policy registry tables state output demand row bound)
    (ready : RecursiveExpressions.Ready state.execution.configuration.expression) :
    ∃ after remaining nextRow,
      NamedAccessStep [] state (ScopedPortJoint.advanceState state after [] []) ∧
      Prepared operations declarations policy registry tables
        (ScopedPortJoint.advanceState state after [] []) output remaining nextRow bound ∧
      demand.Perm remaining ∧ nextRow.Sublist row := by
  obtain ⟨after, remaining, nextRow, step, current, accounting, included⟩ :=
    DeclaredExecution.ready_progress before.current ready
  exact ⟨after, remaining, nextRow, step, ready_preserves_prepared before ready step current, accounting, included⟩

/-- Actual builtin read/write preserve the same source-selected update, checked
row and action-guarded interfaces, including through nested completion frames. -/
theorem builtin_step_preserves
    (before : Prepared operations declarations policy registry tables
      ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, stack⟩, issued, completed⟩, activations⟩
      output demand row bound)
    (isValue : operand.IsValue)
    (raw : RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, stack⟩ after [] []) :
    ∃ nextRow,
      let state : NamedState := ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, stack⟩,
        issued, completed⟩, activations⟩
      NamedAccessStep [] state (ScopedPortJoint.advanceState state after [] []) ∧
      Prepared operations declarations policy registry tables
        (ScopedPortJoint.advanceState state after [] []) output demand nextRow bound ∧ nextRow.Sublist row := by
  obtain ⟨nextRow, step, current, included⟩ := DeclaredExecution.builtin_step_preserves before.current isValue raw
  obtain ⟨actions, usage, history, requests, closing⟩ := before.actions
  obtain ⟨nextActions, nextUsage, nextHistory, actionExtension⟩ := ScopedActionUsage.named_step_preserves step usage history
  rw [before.current.signature] at requests
  have requests := ScopedActionInterfaces.raw_builtin_preserves_configuration requests raw rfl isValue
  change ScopedActionInterfaces.ConfigurationConnected (DeclarationResults.signature declarations)
    registry.contracts.ports actions (resourceWorld issued) after output.port [] at requests
  rw [← before.current.signature] at requests
  have unique : (ownedTickets after.stack).Nodup := by
    cases current.source with
    | checked _ _ unique _ _ => exact unique
  refine ⟨nextRow, step, ⟨current, ⟨nextActions, nextUsage, nextHistory, ?_, ?_⟩⟩, included⟩
  · simpa only [ScopedPortJoint.advanceState, List.append_nil] using
      ScopedActionInterfaces.configuration_action_extension requests actionExtension
  · simpa only [ScopedPortJoint.advanceState, List.append_nil] using
      raw_step_preserves_retained raw closing (fun _ _ known => known) actionExtension
        (List.Subset.refl _) (.none (by simp)) unique

/-- A closed request either takes an actual builtin step preserving Prepared,
or exposes the nearest source-handler cut. The cut still needs capture admission. -/
theorem request_selection
    (before : Prepared operations declarations policy registry tables
      ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, stack⟩, issued, completed⟩, activations⟩
      output demand row bound)
    (isValue : operand.IsValue) :
    (∃ after nextRow,
      let state : NamedState := ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, stack⟩,
        issued, completed⟩, activations⟩
      NamedAccessStep [] state (ScopedPortJoint.advanceState state after [] []) ∧
      Prepared operations declarations policy registry tables
        (ScopedPortJoint.advanceState state after [] []) output demand nextRow bound ∧ nextRow.Sublist row) ∨
    (∃ capture tail handler, HandlerCut requested stack capture tail handler) := by
  rcases RecursiveRequestProgress.request_selection before.current.signature
      (DeclaredSourceStates.checked_state_erase before.current.source) isValue with
    ⟨after, nextRow, raw, source, included⟩ | selected
  · obtain ⟨nextRow, step, current, included⟩ := builtin_step_preserves before isValue raw
    exact Or.inl ⟨after, nextRow, step, current, included⟩
  · exact Or.inr selected

end Ash.OneShot.DeclaredClosingInvariant

#print axioms Ash.OneShot.ScopedActionInterfaces.bind_preserves_configuration
#print axioms Ash.OneShot.ScopedActionInterfaces.beta_preserves_configuration
#print axioms Ash.OneShot.ScopedActionInterfaces.branch_preserves_configuration
#print axioms Ash.OneShot.ScopedActionInterfaces.raw_ready_preserves_configuration
#print axioms Ash.OneShot.ScopedActionInterfaces.handler_cut_decomposition
#print axioms Ash.OneShot.DeclaredClosingInvariant.ready_preserves_prepared
#print axioms Ash.OneShot.DeclaredClosingInvariant.ready_progress


namespace Ash.OneShot.EntryAnnotationExample
open ScopedExpressions ScopedExecution ScopedPorts CoherentSourceTypes

def action := DeclaredDisposalAdmissionGap.action
def before : Configuration := ⟨.cleanup action.action .unit, .none, .nil⟩
def after : Configuration := ⟨.unit, .none, .push (.armed action) .nil⟩
def noTickets : EffectTickets := fun _ => none
def noActions : Syntax.UsageTickets := fun _ => none

theorem before_source : DeclaredSources.Expression operations policy (fun _ => none) [] []
    .none Environment.empty before.expression .unit []
    (.emitAfter (.sequence (.request [] []) (.request [] [])) [] []) := by
  exact DeclaredSources.Expression.cleanup
    (.stable (.lambda .unit (by simp [InWorld, Value.port, Port.resources])))
    (.stable .unit) (List.nil_subset _)

theorem before_connected :
    ScopedActionInterfaces.ConfigurationConnected signature noTickets noActions [] before .unit [] := by
  refine ⟨.unit, [], .checked .none ?_, .nil, .nil (List.Subset.refl [])⟩
  exact .cleanup (.lambda .unit (by simp [InWorld, Port.resources])) .unit (List.nil_subset _)

/-- Raw entry does not constrain the callback request annotation by its
predecessor's typing derivation. This is not a failure of existential progress. -/
theorem raw_entry : RawStep before after [.cleanup 102] [] := .enterCleanup action .unit .nil

theorem incompatible_annotation_rejected :
    ¬ ScopedActionInterfaces.ConfigurationConnected signature noTickets noActions [] after .unit [] := by
  rintro ⟨input, effects, expression, ports, connected⟩
  cases connected with
  | push frame rest bound => cases frame with
      | armed scope callable requests => cases rest with
          | nil outside =>
              exact List.not_mem_nil (outside (requests
                (show ResumeOnlyCapture.Examples.callbackEffect ∈ action.requests from List.mem_cons_self)))

/-- The same code has a correctly annotated entry. The counterexample identifies
an annotation-selection obligation; it does not justify rejecting this source. -/
theorem compatible_entry_exists :
    ∃ next, RawStep before next [.cleanup 102] [] ∧
      ScopedActionInterfaces.ConfigurationConnected signature noTickets noActions [] next .unit [] := by
  let chosen : ActionData := { action with requests := [] }
  have callback : Typed signature [] TypeEnv.empty .none [] chosen.action (.function .unit .unit []) :=
    .lambda .unit (by simp [InWorld, Port.resources])
  refine ⟨⟨.unit, .none, .push (.armed chosen) .nil⟩, .enterCleanup chosen .unit .nil,
    .unit, [], .checked .none .unit, ?_, ?_⟩
  · exact .push (.armed ⟨.none, .none⟩ callback) .nil
  · exact .push (.armed ⟨.none, .none⟩ callback (List.nil_subset _))
      (.nil (List.Subset.refl [])) (List.Subset.refl [])

end Ash.OneShot.EntryAnnotationExample

#print axioms Ash.OneShot.EntryAnnotationExample.before_source
#print axioms Ash.OneShot.EntryAnnotationExample.before_connected
#print axioms Ash.OneShot.EntryAnnotationExample.raw_entry
#print axioms Ash.OneShot.EntryAnnotationExample.incompatible_annotation_rejected
#print axioms Ash.OneShot.EntryAnnotationExample.compatible_entry_exists

#print axioms Ash.OneShot.ScopedActionInterfaces.cell_update_preserves_connections
#print axioms Ash.OneShot.ScopedActionInterfaces.cell_read_preserves_configuration
#print axioms Ash.OneShot.ScopedActionInterfaces.cell_write_preserves_configuration
#print axioms Ash.OneShot.ScopedActionInterfaces.raw_builtin_preserves_configuration
#print axioms Ash.OneShot.DeclaredClosingInvariant.builtin_step_preserves
#print axioms Ash.OneShot.DeclaredClosingInvariant.request_selection
