import SourceAnnotatedExecutionExactControl

/-! The common checked-event interface covers focus, ordinary reduction,
returns, resumption, builtin replies, entry, capture and disposal. The rules contain
syntax, finite guards and name freshness only. Preservation constructs changing
proof registries. Initial source admission remains a separate obligation. -/
namespace Ash.OneShot.SourceAnnotatedExecutionEvents
open ScopedExecution (NamedAccessStep)
open SourceAnnotatedRuntime (NamedState advanceState)
open SourceAnnotatedExecution (Run checkEntryPort checkCleanupPorts)
open SourceScheduledSavedPlans (Saved)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)

inductive Step (signature : ScopedPorts.Signature) (result : ScopedPorts.Port) : NamedState → NamedState → Prop where
  | discard {front capture tail : SourceAnnotatedRuntime.Stack}
      (resolved : scope.resolve binder = some owner)
      (built : SourceAnnotatedRuntime.makePlan capture = some plan)
      (fresh : (issued ++ [Owner.close identity]).Nodup) :
      Step signature result
        ⟨⟨⟨.discard hint binder, scope, front.append (.live owner input answer capture caller tail)⟩,
          issued, completed⟩, activations⟩
        (advanceState
          ⟨⟨⟨.discard hint binder, scope, front.append (.live owner input answer capture caller tail)⟩,
            issued, completed⟩, activations⟩
          ⟨.unit .unit, scope, (SourceAnnotatedRuntime.closeControl scope plan).append
            (.push (.closing identity scope) (front.append (.spent owner answer caller tail)))⟩ [.close identity] [.ticket owner])
  | readCell {stack afterStack : SourceAnnotatedRuntime.Stack}
      (selected : SourceAnnotatedRuntime.CellUpdate identity payload payload stack afterStack) :
      Step signature result
        ⟨⟨⟨.perform hint (Instantiation.freezeEffect (.cell identity)) 0
          (.resourceRef referenceHint (.activation identity)), scope, stack⟩, issued, completed⟩, activations⟩
        (advanceState
          ⟨⟨⟨.perform hint (Instantiation.freezeEffect (.cell identity)) 0
            (.resourceRef referenceHint (.activation identity)), scope, stack⟩, issued, completed⟩, activations⟩
          ⟨.integer .integer payload, scope, afterStack⟩ [] [])
  | writeCell {stack afterStack : SourceAnnotatedRuntime.Stack}
      (selected : SourceAnnotatedRuntime.CellUpdate identity old new stack afterStack) :
      Step signature result
        ⟨⟨⟨.perform hint (Instantiation.freezeEffect (.cell identity)) 1
          (.pair pairHint (.resourceRef referenceHint (.activation identity)) (.integer integerHint new)), scope, stack⟩,
          issued, completed⟩, activations⟩
        (advanceState
          ⟨⟨⟨.perform hint (Instantiation.freezeEffect (.cell identity)) 1
            (.pair pairHint (.resourceRef referenceHint (.activation identity)) (.integer integerHint new)), scope, stack⟩,
            issued, completed⟩, activations⟩
          ⟨.unit .unit, scope, afterStack⟩ [] [])
  | capture {whole capture tail : SourceAnnotatedRuntime.Stack} {handler : SourceAnnotatedRuntime.Handler}
      {code operand : SourceAnnotatedCode.Term}
      (cut : SourceAnnotatedRuntime.HandlerCut requested whole capture tail handler)
      (isValue : operand.erase.IsValue)
      (selected : SourceAnnotatedRuntime.ClauseAt operation handler.clauses parameter binder code)
      (ports : signature requested operation = some (argumentPort, inputPort))
      (fresh : (issued ++ [Owner.ticket owner]).Nodup) :
      Step signature result
        ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
          issued, completed⟩, activations⟩
        (advanceState
          ⟨⟨⟨.perform hint (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
            issued, completed⟩, activations⟩
          ⟨code.subst parameter operand, .ticket binder owner,
            .live owner (ScopedPorts.embedPort inputPort) handler.answer capture handler.scope tail⟩ [.ticket owner] [])
  | ordinary (event : SourceAnnotatedCode.Reduction code scope afterCode afterScope) :
      Step signature result
        ⟨⟨⟨code, scope, stack⟩, issued, completed⟩, activations⟩
        (advanceState ⟨⟨⟨code, scope, stack⟩, issued, completed⟩, activations⟩
          ⟨afterCode, afterScope, stack⟩ [] [])
  | returned (event : SourceAnnotatedRuntime.ReturnStep before.execution.configuration after [] discharged) :
      Step signature result before (advanceState before after [] discharged)
  | resume {front capture tail : SourceAnnotatedRuntime.Stack}
      (resolved : scope.resolve binder = some owner) (isValue : value.erase.IsValue) :
      Step signature result
        ⟨⟨⟨.resume hint binder value, scope, front.append (.live owner inputType answerType capture caller tail)⟩,
          issued, completed⟩, activations⟩
        (advanceState
          ⟨⟨⟨.resume hint binder value, scope, front.append (.live owner inputType answerType capture caller tail)⟩,
            issued, completed⟩, activations⟩
          ⟨value, scope, capture.append (front.append (.spent owner answerType caller tail))⟩ [] [.ticket owner])
  | focus {plain : SourceAnnotatedRuntime.Plain}
      (position : SourceAnnotatedCode.Focus code child plain.context)
      (ports : SourceAnnotatedCode.checkFocusFrame Instantiation.Environment.empty child result stack.erase plain.erase = true) :
      Step signature result
        ⟨⟨⟨code, plain.scope, stack⟩, issued, completed⟩, activations⟩
        (advanceState ⟨⟨⟨code, plain.scope, stack⟩, issued, completed⟩, activations⟩
          ⟨child, plain.scope, .push (.plain plain) stack⟩ [] [])
  | resource
      (fresh : (issued ++ [Owner.resource identity]).Nodup)
      (ports : checkEntryPort hint answer = true) :
      Step signature result
        ⟨⟨⟨.resource hint binder (.integer initialHint payload) body, scope, stack⟩, issued, completed⟩, activations⟩
        (advanceState
          ⟨⟨⟨.resource hint binder (.integer initialHint payload) body, scope, stack⟩, issued, completed⟩, activations⟩
          ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
            .push (.cell identity payload scope answer) stack⟩ [.resource identity] [])
  | handler {handler : SourceAnnotatedRuntime.Handler}
      (fresh : handler.activation ∉ activations)
      (ports : checkEntryPort hint handler.answer = true) :
      Step signature result
        ⟨⟨⟨.handle hint (Instantiation.freezeEffect handler.effectInst) body handler.clauses,
          handler.scope, stack⟩, issued, completed⟩, activations⟩
        (advanceState
          ⟨⟨⟨.handle hint (Instantiation.freezeEffect handler.effectInst) body handler.clauses,
            handler.scope, stack⟩, issued, completed⟩, activations⟩
          ⟨body, handler.scope, .push (.handler handler) stack⟩ [] [])
  | cleanup {action : SourceAnnotatedRuntime.Action}
      (fresh : (issued ++ [Owner.cleanup action.identity]).Nodup)
      (ports : checkCleanupPorts hint action = true) :
      Step signature result
        ⟨⟨⟨.cleanup hint action.action body, action.scope, stack⟩, issued, completed⟩, activations⟩
        (advanceState
          ⟨⟨⟨.cleanup hint action.action body, action.scope, stack⟩, issued, completed⟩, activations⟩
          ⟨body, action.scope, .push (.armed action) stack⟩ [.cleanup action.identity] [])

/-- Every event of the stated interface preserves the supplied initial
invariant. Neither the event nor its target supplies a new source derivation. -/
theorem step_preserves {output : SourcePlannedTyping.Value}
    (event : Step operations.erase.erase.ports output.erase.erase.port before after)
    (run : Run operations declarations policy contracts registry tables families required annotations
      before forest output demand row bound) :
    NamedAccessStep [] before.erase after.erase ∧
    ∃ nextContracts nextRegistry nextTables nextFamilies nextRequired nextAnnotations, ∃ saved : Saved, ∃ nextDemand nextRow,
      Run operations declarations policy nextContracts nextRegistry nextTables nextFamilies nextRequired nextAnnotations
        after saved.forest output nextDemand nextRow bound ∧ nextRow ⊆ row := by
  cases event with
  | discard resolved built fresh =>
      obtain ⟨remaining, saved, step, next, _⟩ := run.discard_at resolved built fresh
      exact ⟨step, _, _, _, _, _, _, saved, remaining, _, next, List.Subset.refl _⟩
  | readCell selected =>
      obtain ⟨nextRow, step, next, included⟩ := run.read_step selected
      exact ⟨step, _, _, _, _, _, _, ⟨_, _, forest⟩, _, nextRow, next, included.subset⟩
  | writeCell selected =>
      obtain ⟨nextRow, step, next, included⟩ := run.write_step selected
      exact ⟨step, _, _, _, _, _, _, ⟨_, _, forest⟩, _, nextRow, next, included.subset⟩
  | capture cut isValue selected ports fresh =>
      obtain ⟨_, _, _, offered, _, found⟩ := run.selected_clause cut
      obtain ⟨contract, record, captured, waiting, actual, nextDemand, nextRow, annotation,
        step, next, balance, included, owners, shape, argument, known⟩ :=
        run.capture_preserves cut isValue selected found fresh
      have portKnown := CoherentSourceTypes.port_lookup
        (SourceDependencyAnnotations.operation_erase (SourcePlannedSources.operation_erase known))
      have inputSame := (Prod.mk.inj (Option.some.inj (portKnown.symm.trans ports))).2
      rw [inputSame] at shape
      subst actual
      exact ⟨step, _, _, _, _, _, _, ⟨_, _, _⟩, nextDemand, nextRow, next, included⟩
  | ordinary reduction =>
      obtain ⟨remaining, nextRow, step, next, _, included⟩ := run.ordinary_step reduction
      exact ⟨step, _, _, _, _, _, _, ⟨_, _, forest⟩, remaining, nextRow, next, included.subset⟩
  | returned transition =>
      obtain ⟨remaining, saved, step, next, _⟩ := run.return_step transition
      exact ⟨step, _, _, _, _, _, _, saved, remaining, _, next, List.Subset.refl _⟩
  | resume resolved isValue =>
      obtain ⟨remaining, saved, step, next, _⟩ := run.resume_preserves resolved isValue
      exact ⟨step, _, _, _, _, _, _, saved, remaining, _, next, List.Subset.refl _⟩
  | focus position ports =>
      obtain ⟨saved, step, next⟩ := run.focus_preserves position ports
      exact ⟨step, _, _, _, _, _, _, saved, _, _, next, List.Subset.refl _⟩
  | resource fresh ports =>
      obtain ⟨saved, nextRow, step, next, included⟩ := run.resource_entry fresh ports
      exact ⟨step, _, _, _, _, _, _, saved, _, nextRow, next, included.subset⟩
  | handler fresh ports =>
      obtain ⟨table, clauseFamilies, declarationRequirements, saved, step, next⟩ := run.handler_entry fresh ports
      exact ⟨step, _, _, _, _, _, _, saved, _, _, next, List.Subset.refl _⟩
  | cleanup fresh ports =>
      obtain ⟨saved, step, next⟩ := run.cleanup_entry fresh ports
      exact ⟨step, _, _, _, _, _, _, saved, _, _, next, List.Subset.refl _⟩

/-- A finite supplied trace contains only operational steps, with no current,
intermediate or final runtime invariant stored in its constructors. -/
inductive Steps (signature : ScopedPorts.Signature) (result : ScopedPorts.Port) : Nat → NamedState → NamedState → Prop where
  | zero : Steps signature result 0 state state
  | next : Step signature result before middle → Steps signature result count middle after → Steps signature result (count + 1) before after

/-- Reuse finite-trace induction while threading each derived registry update.
Every supplied trace starts from just one runtime invariant. -/
theorem steps_preserve {output : SourcePlannedTyping.Value}
    {hints : Hints receiving} {forest : Forest hints}
    (trace : Steps operations.erase.erase.ports output.erase.erase.port count before after)
    (run : Run operations declarations policy contracts registry tables families required annotations
      before forest output demand row bound) :
    ClauseExecution.CountedSteps [] count before.erase after.erase ∧
    ∃ nextContracts nextRegistry nextTables nextFamilies nextRequired nextAnnotations, ∃ saved : Saved, ∃ nextDemand nextRow,
      Run operations declarations policy nextContracts nextRegistry nextTables nextFamilies nextRequired nextAnnotations
        after saved.forest output nextDemand nextRow bound ∧ nextRow ⊆ row := by
  induction trace generalizing contracts registry tables families required annotations receiving demand row with
  | zero => exact ⟨.zero, _, _, _, _, _, _, ⟨_, _, forest⟩, _, _, run, List.Subset.refl _⟩
  | next event trace ih =>
      obtain ⟨step, nextContracts, nextRegistry, nextTables, nextFamilies, nextRequired, nextAnnotations,
        saved, nextDemand, nextRow, next, included⟩ := step_preserves event run
      obtain ⟨execution, finalContracts, finalRegistry, finalTables, finalFamilies, finalRequired, finalAnnotations, finalSaved, finalDemand, finalRow, final, remaining⟩ := ih next
      exact ⟨.next step execution, finalContracts, finalRegistry, finalTables, finalFamilies, finalRequired, finalAnnotations, finalSaved, finalDemand, finalRow,
        final, List.Subset.trans remaining included⟩

/-- Exact-once retirement holds at every terminal endpoint of a supplied trace
in the current interface, using only the initial invariant and its events. -/
theorem terminal_accounting {output : SourcePlannedTyping.Value}
    (trace : Steps operations.erase.erase.ports output.erase.erase.port count before after)
    (run : Run operations declarations policy contracts registry tables families required annotations
      before forest output demand row bound)
    (terminal : ScopedPortProgress.Terminal after.execution.configuration.erase) :
    after.execution.issued.Perm after.execution.completed ∧ after.execution.completed.Nodup := by
  obtain ⟨_, _, _, _, _, _, _, saved, nextDemand, nextRow, next, _⟩ := steps_preserve trace run
  exact next.terminal_accounting terminal

end Ash.OneShot.SourceAnnotatedExecutionEvents

#print axioms Ash.OneShot.SourceAnnotatedExecutionEvents.step_preserves
#print axioms Ash.OneShot.SourceAnnotatedExecutionEvents.steps_preserve
#print axioms Ash.OneShot.SourceAnnotatedExecutionEvents.terminal_accounting
