import ScopedRetained

/-!
Type-directed handler and cleanup entry, and exact builtin cell transitions
for actual scoped configurations. These derive stored annotations and value
forms; effect availability and continuation permissions remain independent.
-/

namespace Ash.OneShot.ScopedTyping
open Syntax Instantiation ScopedExpressions ScopedExecution
open Typing (Signature TypeEnv TicketType TicketSignatures withCellSignatures)

theorem clauses_lexical_dependencies
    (typed : ClausesTyped signature world environment effect answer residual clauses) :
    LexicallyBound environment .none clauses.dependencies := by
  cases clauses with
  | nil => exact lexical_nil
  | cons operation parameter binder body rest => cases typed with
      | cons known bodyTyped restTyped =>
          exact lexical_append (lexical_remove_ticket (lexical_remove_variable
            (typed_lexical_dependencies bodyTyped))) (clauses_lexical_dependencies restTyped)
termination_by sizeOf clauses

theorem clauses_have_ticket_barrier
    (typed : ClausesTyped signature world environment effect answer residual clauses) :
    ticketDependencies clauses.dependencies = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro binder used
  have impossible := clauses_lexical_dependencies typed (.ticket binder) (mem_ticketDependencies.mp used)
  cases impossible

/-- The answer annotation and ticket barrier follow from the source derivation.
    The chosen activation still needs freshness in the named machine. -/
theorem configuration_handler_entry_progress
    (typed : ConfigurationTyped signature tickets world
      ⟨.handle source body clauses, scope, tail⟩ result) (activation : Nat) :
    ∃ handler : HandlerData,
      handler.activation = activation ∧
      RawStep ⟨.handle source body clauses, scope, tail⟩
        ⟨body, scope, .push (.handler handler) tail⟩ [] [] ∧
      ConfigurationTyped signature tickets world
        ⟨body, scope, .push (.handler handler) tail⟩ result := by
  obtain ⟨answer, expression, stack⟩ := typed
  cases expression with
  | checked scopeTyped expression => cases expression with
      | @handle _ _ _ effect _ _ _ _ _ bodyTyped clausesTyped coverage unique effects =>
          let handler : HandlerData := ⟨activation, effect, clauses, scope, answer,
            clauses_have_ticket_barrier clausesTyped⟩
          exact ⟨handler, rfl, .enterHandler handler body tail,
            answer, .checked scopeTyped bodyTyped,
            .push (.handler ⟨_, scopeTyped⟩ clausesTyped coverage unique) stack⟩

/-- Stored callback closure and latent requests are derived from the value's
    type. Ownership freshness for the chosen cleanup identity is separate. -/
theorem configuration_cleanup_entry_progress
    (typed : ConfigurationTyped signature tickets world
      ⟨.cleanup callback body, scope, tail⟩ result)
    (isValue : callback.IsValue) (identity : Nat) :
    ∃ action : ActionData,
      action.identity = identity ∧
      RawStep ⟨.cleanup callback body, scope, tail⟩
        ⟨body, scope, .push (.armed action) tail⟩ [.cleanup identity] [] ∧
      ConfigurationTyped signature tickets world
        ⟨body, scope, .push (.armed action) tail⟩ result := by
  obtain ⟨answer, expression, stack⟩ := typed
  cases expression with
  | checked scopeTyped expression => cases expression with
      | @cleanup _ _ _ _ _ latent retained _ _ callbackTyped bodyTyped effects =>
          have closed := typed_value_closed callbackTyped isValue
          let action : ActionData := ⟨identity, callback, closed, scope, answer, latent⟩
          exact ⟨action, rfl, .enterCleanup action body tail,
            answer, .checked scopeTyped bodyTyped,
            .push (.armed ⟨_, scopeTyped⟩ (typed_value_transport callbackTyped closed.1 .none [])) stack⟩

/-- Selection follows active frames only and respects nearer source overrides.
    A payload update preserves all actual active and dormant retained types. -/
theorem cell_update_preserves_stack_typing
    (update : CellUpdate identity old new before after)
    (typed : StackTyped signature tickets world before input result) :
    StackTyped signature tickets world after input result := by
  induction update generalizing input result with
  | hit => cases typed with
      | push frame rest => cases frame with
          | cell caller noEscape => exact .push (.cell caller noEscape) rest
  | push miss next ih => cases typed with
      | push frame rest => exact .push frame (ih rest)
  | live next ih => cases typed with
      | live known caller saved rest => exact .live known caller saved (ih rest)
  | spent next ih => cases typed with
      | spent known caller rest => exact .spent known caller (ih rest)

theorem configuration_cell_read_typed
    (typed : ConfigurationTyped (withCellSignatures users) tickets world
      ⟨.perform (freezeEffect (.cell identity)) 0 (.resourceRef (.activation identity)), scope, before⟩ result)
    (selected : CellUpdate identity payload payload before after) :
    ConfigurationTyped (withCellSignatures users) tickets world ⟨.integer payload, scope, after⟩ result := by
  obtain ⟨answer, expression, stack⟩ := typed
  cases expression with
  | checked scopeTyped expression =>
      obtain ⟨input, operation, available, operand⟩ := typed_perform_inversion expression
      simp only [withCellSignatures, Option.some.injEq, Prod.mk.injEq] at operation
      obtain ⟨rfl, rfl⟩ := operation
      exact ⟨.integer, .checked scopeTyped (Typed.integer (allowed := [])),
        cell_update_preserves_stack_typing selected stack⟩

theorem configuration_cell_write_typed
    (typed : ConfigurationTyped (withCellSignatures users) tickets world
      ⟨.perform (freezeEffect (.cell identity)) 1
        (.pair (.resourceRef (.activation identity)) (.integer new)), scope, before⟩ result)
    (selected : CellUpdate identity old new before after) :
    ConfigurationTyped (withCellSignatures users) tickets world ⟨.unit, scope, after⟩ result := by
  obtain ⟨answer, expression, stack⟩ := typed
  cases expression with
  | checked scopeTyped expression =>
      obtain ⟨input, operation, available, operand⟩ := typed_perform_inversion expression
      simp only [withCellSignatures, Option.some.injEq, Prod.mk.injEq] at operation
      obtain ⟨rfl, rfl⟩ := operation
      exact ⟨.unit, .checked scopeTyped (Typed.unit (allowed := [])),
        cell_update_preserves_stack_typing selected stack⟩

theorem typed_reference_value
    (typed : Typed signature world TypeEnv.empty ticket allowed value (.reference identity))
    (isValue : value.IsValue) : value = .resourceRef (.activation identity) := by
  cases typed <;> simp_all [Code.IsValue]

theorem typed_product_value
    (typed : Typed signature world TypeEnv.empty ticket allowed value (.product leftType rightType))
    (isValue : value.IsValue) :
    ∃ left right, value = .pair left right ∧ left.IsValue ∧ right.IsValue ∧
      Typed signature world TypeEnv.empty ticket allowed left leftType ∧
      Typed signature world TypeEnv.empty ticket allowed right rightType := by
  cases typed <;> simp_all [Code.IsValue]
  exact ⟨_, _, ⟨rfl, rfl⟩, isValue.1, isValue.2, by assumption, by assumption⟩

theorem frame_resolution_none_of_miss (frame : Frame)
    (miss : frame.target ≠ some effect) : frame.resolve effect = none := by
  cases frame with
  | mk kind input output access pending requests =>
      cases kind <;> simp_all [Frame.target, Frame.resolve, eq_comm]

/-- A successful abstract builtin lookup constructs the exact executable
    selection. Live records are traversed through their active suffix only. -/
theorem cell_selection_of_resolution (stack : Stack)
    (resolved : stack.erase.resolve (.cell identity) = some (.builtin identity)) :
    ∃ old, ∀ new, ∃ after, CellUpdate identity old new stack after := by
  induction stack with
  | nil => cases resolved
  | push frame tail ih =>
      by_cases selected : frame.erase.target = some (.cell identity)
      · cases frame with
        | plain | armed | running | unwinding | closing | retiring =>
            simp_all [ExecFrame.erase, PlainData.erase, ActionData.erase, closeFrame, CloseItem.frame, Frame.target]
        | handler handler =>
            simp only [ExecFrame.erase, HandlerData.erase, Frame.target, Option.some.injEq] at selected
            simp [Stack.erase, Control.resolve, ExecFrame.erase, HandlerData.erase, Frame.resolve, selected] at resolved
        | cell key payload scope answer =>
            simp only [ExecFrame.erase, Frame.target, Option.some.injEq, Instance.cell.injEq] at selected
            subst key
            exact ⟨payload, fun new => ⟨_, .hit⟩⟩
      · have miss := frame_resolution_none_of_miss frame.erase selected
        simp only [Stack.erase, Control.resolve, miss] at resolved
        obtain ⟨old, update⟩ := ih resolved
        exact ⟨old, fun new => by
          obtain ⟨after, step⟩ := update new
          exact ⟨_, .push selected step⟩⟩
  | live owner input answer capture scope tail ihCapture ihTail =>
      obtain ⟨old, update⟩ := ihTail resolved
      exact ⟨old, fun new => by
        obtain ⟨after, step⟩ := update new
        exact ⟨_, .live step⟩⟩
  | spent owner answer scope tail ih =>
      obtain ⟨old, update⟩ := ih resolved
      exact ⟨old, fun new => by
        obtain ⟨after, step⟩ := update new
        exact ⟨_, .spent step⟩⟩

/-- For any typed value operand, exact builtin resolution supplies an actual
    read or write step. Operation validity and operand shape are consequences
    of the fixed builtin signature, rather than extra readiness premises. -/
theorem configuration_builtin_progress
    (typed : ConfigurationTyped (withCellSignatures users) tickets world
      ⟨.perform (freezeEffect (.cell identity)) operation operand, scope, stack⟩ result)
    (isValue : operand.IsValue)
    (resolved : stack.erase.resolve (.cell identity) = some (.builtin identity)) :
    ∃ after, RawStep ⟨.perform (freezeEffect (.cell identity)) operation operand, scope, stack⟩ after [] [] ∧
      ConfigurationTyped (withCellSignatures users) tickets world after result := by
  obtain ⟨old, update⟩ := cell_selection_of_resolution stack resolved
  obtain ⟨answer, expression, retained⟩ := typed
  cases expression with
  | checked scopeTyped expression =>
      obtain ⟨input, known, available, operandTyped⟩ := typed_perform_inversion expression
      cases operation with
      | zero =>
          simp only [withCellSignatures, Option.some.injEq, Prod.mk.injEq] at known
          obtain ⟨rfl, rfl⟩ := known
          obtain rfl := typed_reference_value operandTyped isValue
          obtain ⟨after, selected⟩ := update old
          exact ⟨_, .readCell identity old scope stack after selected,
            configuration_cell_read_typed ⟨_, .checked scopeTyped expression, retained⟩ selected⟩
      | succ operation => cases operation with
          | zero =>
              simp only [withCellSignatures, Option.some.injEq, Prod.mk.injEq] at known
              obtain ⟨rfl, rfl⟩ := known
              obtain ⟨reference, value, rfl, referenceValue, numberValue, referenceTyped, numberTyped⟩ :=
                typed_product_value operandTyped isValue
              obtain rfl := typed_reference_value referenceTyped referenceValue
              obtain ⟨new, rfl⟩ := typed_integer_value numberTyped numberValue
              obtain ⟨after, selected⟩ := update new
              exact ⟨_, .writeCell identity old new scope stack after selected,
                configuration_cell_write_typed ⟨_, .checked scopeTyped expression, retained⟩ selected⟩
          | succ operation => cases known

theorem frame_target_miss_of_resolution_none (frame : Frame)
    (missing : frame.resolve effect = none) : frame.target ≠ some effect := by
  cases frame with
  | mk kind input output access pending requests =>
      cases kind <;> simp_all [Frame.target, Frame.resolve, eq_comm]

theorem frame_builtin_resolution_instance (frame : Frame)
    (resolved : frame.resolve requested = some (.builtin identity)) : requested = .cell identity := by
  cases frame with
  | mk kind input output access pending requests =>
      cases kind <;> simp_all [Frame.resolve]
      all_goals split at resolved <;> simp_all

theorem builtin_resolution_instance (stack : Stack)
    (resolved : stack.erase.resolve requested = some (.builtin identity)) : requested = .cell identity := by
  induction stack with
  | nil => cases resolved
  | push frame tail ih =>
      cases first : frame.erase.resolve requested with
      | none => exact ih (by simpa only [Stack.erase, Control.resolve, first] using resolved)
      | some target =>
          have same : target = .builtin identity := by
            simpa only [Stack.erase, Control.resolve, first, Option.some.injEq] using resolved
          subst target
          exact frame_builtin_resolution_instance frame.erase first
  | live owner input answer capture scope tail ihCapture ihTail => exact ihTail resolved
  | spent owner answer scope tail ih => exact ih resolved

theorem frame_source_resolution (frame : ExecFrame)
    (resolved : frame.erase.resolve requested = some (.source activation)) :
    ∃ handler, frame = .handler handler ∧ handler.effectInst = requested ∧ handler.activation = activation := by
  cases frame <;> simp_all [ExecFrame.erase, PlainData.erase, ActionData.erase,
    HandlerData.erase, closeFrame, CloseItem.frame, Frame.resolve]
  all_goals split at resolved <;> simp_all

/-- Source lookup reconstructs the nearest actual handler cut, including each
    intervening live/spent record and its untouched dormant capture. -/
theorem handler_selection_of_resolution (stack : Stack)
    (resolved : stack.erase.resolve requested = some (.source activation)) :
    ∃ cap tail handler, HandlerCut requested stack cap tail handler ∧ handler.activation = activation := by
  induction stack with
  | nil => cases resolved
  | push frame tail ih =>
      cases first : frame.erase.resolve requested with
      | none =>
          obtain ⟨cap, outside, handler, cut, same⟩ := ih
            (by simpa only [Stack.erase, Control.resolve, first] using resolved)
          exact ⟨_, outside, handler, .push frame tail cap outside handler
            (frame_target_miss_of_resolution_none frame.erase first) cut, same⟩
      | some target =>
          have same : target = .source activation := by
            simpa only [Stack.erase, Control.resolve, first, Option.some.injEq] using resolved
          subst target
          obtain ⟨handler, rfl, effect, active⟩ := frame_source_resolution frame first
          exact ⟨_, tail, handler, .hit handler tail effect, active⟩
  | live owner input answer capture scope tail ihCapture ihTail =>
      obtain ⟨cap, outside, handler, cut, same⟩ := ihTail resolved
      exact ⟨_, outside, handler, .live owner input answer capture scope tail cap outside handler cut, same⟩
  | spent owner answer scope tail ih =>
      obtain ⟨cap, outside, handler, cut, same⟩ := ih resolved
      exact ⟨_, outside, handler, .spent owner answer scope tail cap outside handler cut, same⟩

namespace EntryExamples
open RetainedExamples

theorem derived_handler_entry :
    ∃ handler : HandlerData, handler.activation = 8 ∧
      RawStep ⟨.handle (freezeEffect ScopedExecution.UsageExecutionExamples.handler.effectInst) request
        ScopedExecution.UsageExecutionExamples.handler.clauses, .none, .nil⟩
        ⟨request, .none, .push (.handler handler) .nil⟩ [] [] ∧
      ConfigurationTyped signature noTickets [] ⟨request, .none, .push (.handler handler) .nil⟩ .unit := by
  have frame := handler_typed (registry := noTickets) (world := [])
  cases frame with
  | handler scope clauses coverage unique =>
      apply configuration_handler_entry_progress (activation := 8)
      refine ⟨.unit, .checked .none (.handle ?_ clauses coverage unique (List.Subset.refl _)), .nil⟩
      exact .perform (effect := .user 1 []) rfl (by simp [ScopedExecution.UsageExecutionExamples.handler])
        .unit (List.nil_subset _)

theorem derived_cleanup_entry :
    ∃ entry : ActionData, entry.identity = 7 ∧
      RawStep ⟨.cleanup action.action (.integer 17), .none, .nil⟩
        ⟨.integer 17, .none, .push (.armed entry) .nil⟩ [.cleanup 7] [] ∧
      ConfigurationTyped signature noTickets [] ⟨.integer 17, .none, .push (.armed entry) .nil⟩ .integer := by
  apply configuration_cleanup_entry_progress (identity := 7)
  · have frame := action_typed
    cases frame with
    | armed caller callable =>
        exact ⟨.integer, .checked .none (.cleanup callable .integer (List.nil_subset _)), .nil⟩
  · exact action.closed.1

end EntryExamples

end Ash.OneShot.ScopedTyping

#print axioms Ash.OneShot.ScopedTyping.clauses_have_ticket_barrier
#print axioms Ash.OneShot.ScopedTyping.configuration_handler_entry_progress
#print axioms Ash.OneShot.ScopedTyping.configuration_cleanup_entry_progress
#print axioms Ash.OneShot.ScopedTyping.cell_update_preserves_stack_typing
#print axioms Ash.OneShot.ScopedTyping.configuration_cell_read_typed
#print axioms Ash.OneShot.ScopedTyping.configuration_cell_write_typed
#print axioms Ash.OneShot.ScopedTyping.typed_reference_value
#print axioms Ash.OneShot.ScopedTyping.typed_product_value
#print axioms Ash.OneShot.ScopedTyping.cell_selection_of_resolution
#print axioms Ash.OneShot.ScopedTyping.configuration_builtin_progress
#print axioms Ash.OneShot.ScopedTyping.builtin_resolution_instance
#print axioms Ash.OneShot.ScopedTyping.handler_selection_of_resolution
#print axioms Ash.OneShot.ScopedTyping.EntryExamples.derived_handler_entry
#print axioms Ash.OneShot.ScopedTyping.EntryExamples.derived_cleanup_entry
