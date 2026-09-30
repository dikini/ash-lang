import SourceScheduledRuntimeCapture

/-! Exhaustive progress for the retained structural one-shot source/runtime
invariant. Each nonterminal case constructs a real machine transition and a
successor carrying that same invariant. Initial source admission is separate. -/
namespace Ash.OneShot.SourceScheduledExecution
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceRetainedPlans (Forest)
open SourceScheduledSavedPlans (Saved)

/-- Exact handler coverage chooses the source clause; its mode declaration
supplies the matching table entry. -/
theorem Run.selected_clause
    (run : Run operations declarations policy contracts registry tables families required annotations
      ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩ forest output demand row bound)
    (cut : HandlerCut requested whole capture tail handler) :
    ∃ parameter binder code offered,
      ClauseAt operation handler.clauses parameter binder code ∧ lookup operation (tables handler) = some offered := by
  obtain ⟨input, current, stack⟩ := DeclaredReturnAdmission.ports run.current.source
  cases current with
  | checked scopeTyped typed =>
    generalize frozen : Instantiation.freezeEffect requested = effect at typed
    cases typed with
    | perform known admitted operandTyped formed =>
      cases freeze_effect_injective frozen
      obtain ⟨savedTyped, waitingTyped, handlerTyped⟩ := ScopedPorts.handler_cut_retains_typing cut stack
      cases handlerTyped with
      | handler scopeKnown clauses coverage unique =>
        have atHandler := known
        rw [← ScopedTyping.handler_cut_instance cut] at atHandler
        obtain ⟨parameter, binder, code, selected⟩ := ScopedTyping.clause_at_of_key (coverage _ _ _ atHandler)
        obtain ⟨actions, usage, history, source, retained⟩ := run.actions
        cases source with
        | checked current scope pending closing templates matched contextual unique evaluated accepted accounting =>
          obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords,
            capScope, tailScope, annotation, frame, saved, waiting, rest⟩ :=
            SourceDependencyFrames.capture_segments cut pending.source.source.erase
          cases frame with
          | handler scope annotation clauses coverage unique declarations capabilities modes =>
            obtain ⟨offered, found, permission⟩ := SourceTemplates.selected_clause_mode selected modes
            exact ⟨parameter, binder, code, offered, selected, found⟩

private theorem successor_witness
    (step : NamedAccessStep [] before after)
    (next : Run operations declarations policy contracts registry tables families required annotations
      after forest output demand row bound) :
    ∃ after nextContracts nextRegistry nextTables nextFamilies nextRequired nextAnnotations, ∃ saved : Saved, ∃ nextDemand nextRow,
      NamedAccessStep [] before after ∧
      Run operations declarations policy nextContracts nextRegistry nextTables nextFamilies nextRequired nextAnnotations
        after saved.forest output nextDemand nextRow bound :=
  ⟨after, contracts, registry, tables, families, required, annotations, ⟨_, _, forest⟩, demand, row, step, next⟩

/-- All typed expression forms are covered. The returned source derivation is
for the actual successor, with fresh registries and retained plans when needed. -/
theorem Run.progress
    (before : Run operations declarations policy contracts registry tables families required annotations
      state forest output demand row bound) :
    (state.execution.configuration.expression.IsValue ∧ state.execution.configuration.stack = .nil) ∨
    ∃ after nextContracts nextRegistry nextTables nextFamilies nextRequired nextAnnotations, ∃ saved : Saved, ∃ nextDemand nextRow,
      NamedAccessStep [] state after ∧
      Run operations declarations policy nextContracts nextRegistry nextTables nextFamilies nextRequired nextAnnotations
        after saved.forest output nextDemand nextRow bound := by
  obtain ⟨⟨⟨code, scope, stack⟩, issued, completed⟩, activations⟩ := state
  obtain ⟨input, current, stackTyped⟩ := DeclaredReturnAdmission.ports before.current.source
  cases current with
  | checked scopeTyped typed =>
    have form := ScopedPortProgress.typed_current_form typed
    cases form with
    | value isValue =>
      rcases value_progress before isValue with terminal | ⟨after, discharged, remaining, saved, step, next, accounting⟩
      · exact Or.inl ⟨isValue, terminal⟩
      · exact Or.inr (successor_witness step next)
    | focus position =>
      obtain ⟨plain, saved, contextSame, scopeSame, step, next⟩ := focus_progress before position
      exact Or.inr (successor_witness step next)
    | bind isValue =>
      obtain ⟨after, remaining, nextRow, step, next, accounting, included⟩ := ready_progress before (.bind isValue)
      exact Or.inr (successor_witness step next)
    | app functionValue argumentValue => cases typed with
      | app function argument available =>
        obtain ⟨parameter, body, same⟩ := ScopedPorts.typed_function_value function functionValue
        subst_vars
        obtain ⟨after, remaining, nextRow, step, next, accounting, included⟩ := ready_progress before (.app argumentValue)
        exact Or.inr (successor_witness step next)
    | branch isValue => cases typed with
      | branch condition yes no =>
        obtain ⟨flag, same⟩ := ScopedPorts.typed_boolean_value condition isValue
        subst_vars
        obtain ⟨after, remaining, nextRow, step, next, accounting, included⟩ := ready_progress before .branch
        exact Or.inr (successor_witness step next)
    | request isValue =>
      rcases request_selection before isValue with ⟨after, nextRow, step, next, included⟩ | ⟨capture, tail, handler, cut⟩
      · exact Or.inr (successor_witness step next)
      · obtain ⟨parameter, binder, body, offered, selected, found⟩ := before.selected_clause cut
        obtain ⟨owner, contract, record, captured, waiting, after, nextDemand, nextRow,
          annotation, step, next, accounting, included, owners⟩ := before.capture_progress cut isValue selected found
        exact Or.inr (successor_witness step next)
    | handler =>
      obtain ⟨handler, table, clauseFamilies, declarationRequirements, saved, fresh, step, next⟩ := handler_progress before
      exact Or.inr (successor_witness step next)
    | resume isValue =>
      obtain ⟨after, owner, remaining, saved, step, next, accounting⟩ := resume_progress before isValue
      exact Or.inr (successor_witness step next)
    | discard =>
      obtain ⟨after, owner, remaining, saved, step, next, accounting⟩ := before.discard_progress
      exact Or.inr (successor_witness step next)
    | resource isValue =>
      obtain ⟨identity, payload, answer, saved, same, step, next⟩ := resource_progress before isValue
      exact Or.inr (successor_witness step next)
    | cleanup isValue =>
      obtain ⟨action, saved, step, next⟩ := cleanup_progress before isValue
      exact Or.inr (successor_witness step next)

end Ash.OneShot.SourceScheduledExecution

#print axioms Ash.OneShot.SourceScheduledExecution.Run.selected_clause
#print axioms Ash.OneShot.SourceScheduledExecution.Run.progress
