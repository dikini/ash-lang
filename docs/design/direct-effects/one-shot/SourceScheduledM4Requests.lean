import SourceScheduledM4Evaluation
import SourceScheduledBuiltinSignatures
import SourceScheduledM4RequestPackaging

/-! Availability of an M3 request for a ready operation.  The immutable
operation environment supplies the canonical builtin boundary; handler capture
premises are recovered from the current structural source. -/

namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open ScopedExpressions ScopedExecution ProtectionContracts

private theorem Context.Source.selected_builtin_update
    {hints : SourceDependencyChecks.Lexical.ReturnHints receiving} {context : Context hints}
    (source : Context.Source operations policy contracts tables families world context before)
    (found : select (.cell identity) operation context = some (.builtin identity)) :
    ∃ old, ∀ new, ∃ after, CellUpdate identity old new before after := by
  induction source with
  | nil => cases found
  | cell tail ih =>
      simp only [select] at found
      split at found
      · rename_i selected
        have identityEq := Instance.cell.inj selected
        cases identityEq
        exact ⟨_, fun _ => ⟨_, .hit⟩⟩
      · rename_i missed
        simp only [Option.map_eq_some_iff] at found
        obtain ⟨selected, selectedEq, mapped⟩ := found
        cases selected <;> cases mapped
        obtain ⟨old, update⟩ := ih selectedEq
        exact ⟨old, fun new => by
          obtain ⟨after, next⟩ := update new
          exact ⟨_, .push (by
            intro equal
            apply missed
            simpa [ExecFrame.erase, Frame.target] using equal.symm) next⟩⟩
  | handler declaration tail ih =>
      simp only [select] at found
      split at found
      · split at found <;> simp_all
      · rename_i missed
        simp only [Option.map_eq_some_iff] at found
        obtain ⟨selected, selectedEq, mapped⟩ := found
        cases selected <;> cases mapped
        obtain ⟨old, update⟩ := ih selectedEq
        exact ⟨old, fun new => by
          obtain ⟨after, next⟩ := update new
          exact ⟨_, .push (by
            intro equal
            apply missed
            simpa [ExecFrame.erase, HandlerData.erase, Frame.target] using equal.symm) next⟩⟩
  | plain tail ih | cleanup callback tail ih | normal tail ih | unwinding tail ih
  | closing tail ih | retiring tail ih =>
      simp only [select, Option.map_eq_some_iff] at found
      obtain ⟨selected, selectedEq, mapped⟩ := found
      cases selected <;> cases mapped
      obtain ⟨old, update⟩ := ih selectedEq
      exact ⟨old, fun new => by
        obtain ⟨after, next⟩ := update new
        exact ⟨_, .push (by simp [ExecFrame.erase, PlainData.erase, ActionData.erase,
          closeFrame, CloseItem.frame, Frame.target]) next⟩⟩
  | live saved tail ihSaved ihTail =>
      simp only [select, Option.map_eq_some_iff] at found
      obtain ⟨selected, selectedEq, mapped⟩ := found
      cases selected <;> cases mapped
      obtain ⟨old, update⟩ := ihTail selectedEq
      exact ⟨old, fun new => by obtain ⟨after, next⟩ := update new; exact ⟨_, .live next⟩⟩
  | spent tail ih =>
      simp only [select, Option.map_eq_some_iff] at found
      obtain ⟨selected, selectedEq, mapped⟩ := found
      cases selected <;> cases mapped
      obtain ⟨old, update⟩ := ih selectedEq
      exact ⟨old, fun new => by obtain ⟨after, next⟩ := update new; exact ⟨_, .spent next⟩⟩

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual

namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation

open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Operations Value)
open RecursiveRequirements (Requirements)

theorem request_available
    {operations : Operations} {snapshot : Snapshot operations}
    {ports : OperationRows operations}
    {emptyRows : EnvironmentRows (fun _ => none)}
    {output : Value} {outputRows : ValueRows output}
    (compatible : SourceScheduledBuiltinSignatures.Compatible operations)
    (valid : Valid (operations := operations) policy outward ambient budget ports emptyRows output outputRows snapshot)
    (shape : snapshot.run =
      ⟨⟨.eval ⟨.perform (Instantiation.freezeEffect effect) operation operand,
        runtimeScope, stack⟩, issued, completed⟩, actions⟩)
    (isValue : operand.IsValue) : Nonempty (Request snapshot) := by
  have state := valid.unpack
  rw [shape] at state
  have source := state.source
  dsimp only at source
  generalize machineEq : LexicalUnwind.Machine.eval
    ⟨.perform (Instantiation.freezeEffect effect) operation operand, runtimeScope, stack⟩ = machine at source
  cases source with
  | eval site phaseAgreement rooted bound annotation checked bounded =>
      obtain ⟨expressionEq, runtimeEq, stackEq⟩ :=
        Configuration.mk.inj (LexicalUnwind.Machine.eval.inj machineEq)
      obtain ⟨requested, input, known, effectEq, resultRows, primitive, resource⟩ :=
        checked_request_origin site.current.previous.authenticated expressionEq.symm site.currentResource
      have same := freeze_effect_injective effectEq
      subst requested
      obtain ⟨ticket, scopeTyped⟩ := site.scopeTyped
      have expressionTyped := SourceTemplates.expression_ports
        (DeclaredSources.expression_erase
          (SourceDependencyAnnotations.expression_erase
            (SourcePlannedSources.expression_erase site.current.previous.source))) scopeTyped
      rw [← expressionEq] at expressionTyped
      obtain ⟨operandType, portKnown, available, operandTyped⟩ :=
        ScopedPorts.typed_perform_inversion expressionTyped
      have closed : ClosedValue operand := ScopedPorts.typed_value_closed operandTyped isValue
      cases primitive with
      | builtin found =>
          rename_i identity
          have erased : SourceDependencyCapture.select effect operation site.receiving =
              some (.builtin identity) := by
            rw [← Contextual.select_sound effect operation site.context, found]
            rfl
          have effectCell := SourceHandlerCoverage.selected_builtin_effect erased
          subst effect
          rcases compatible identity operation _ _ portKnown with read | write
          · obtain ⟨operationEq, inputEq, outputEq⟩ := read
            subst operation
            have referenceTyped : ScopedPorts.Typed operations.erase.erase.ports snapshot.world
                (SourcePlannedTyping.Environment.erase (fun _ => none)).erase.ports ticket site.allowed
                operand (.reference identity) := by
              simpa only [inputEq] using operandTyped
            obtain rfl := ScopedPorts.typed_reference_value referenceTyped isValue
            obtain ⟨old, update⟩ :=
              site.coherent.forget.source.selected_builtin_update found
            obtain ⟨afterStack, selected⟩ := update old
            have selected' : CellUpdate identity old old stack afterStack := by
              simpa only [stackEq] using selected
            have builtin : operations.erase.erase.ports (.cell identity) 0 =
                some (.reference identity, .integer) := by
              simpa only [inputEq, outputEq] using portKnown
            exact request_of_stable_at shape
              (.read_cell (snapshot := snapshot) builtin selected')
          · obtain ⟨operationEq, inputEq, outputEq⟩ := write
            subst operation
            have productTyped : ScopedPorts.Typed operations.erase.erase.ports snapshot.world
                (SourcePlannedTyping.Environment.erase (fun _ => none)).erase.ports ticket site.allowed
                operand (.product (.reference identity) .integer) := by
              simpa only [inputEq] using operandTyped
            obtain ⟨reference, number, rfl, referenceValue, numberValue,
                referenceTyped, numberTyped⟩ :=
              ScopedPorts.typed_product_value productTyped isValue
            obtain rfl := ScopedPorts.typed_reference_value referenceTyped referenceValue
            obtain ⟨new, rfl⟩ := ScopedPorts.typed_integer_value numberTyped numberValue
            obtain ⟨old, update⟩ :=
              site.coherent.forget.source.selected_builtin_update found
            obtain ⟨afterStack, selected⟩ := update new
            have selected' : CellUpdate identity old new stack afterStack := by
              simpa only [stackEq] using selected
            have builtin : operations.erase.erase.ports (.cell identity) 1 =
                some (.product (.reference identity) .integer, .unit) := by
              simpa only [inputEq, outputEq] using portKnown
            exact request_of_stable_at shape
              (.write_cell (snapshot := snapshot) builtin selected')
      | request cut guarded callbacks ownerBound cleanupBudget selected terminal rights retained body =>
          obtain ⟨capturedStack, tailStack, handler, physical, _, _⟩ :=
            site.pending.realizes.selected_handler_cut cut.select_sound
          obtain ⟨owner, fresh⟩ := ScopedPortProgress.fresh_owner_exists Owner.ticket (fun _ => rfl) state.ledger.2
          have physical' : HandlerCut effect stack capturedStack tailStack handler := by
            simpa only [stackEq] using physical
          exact ⟨.allocating (.capture shape physical' closed owner fresh [] none)⟩
  | unwind => cases machineEq

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.request_available
