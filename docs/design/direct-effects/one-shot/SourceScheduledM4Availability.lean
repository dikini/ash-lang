import SourceScheduledM4Requests
import SourceScheduledM4Returns
import SourceScheduledM4Execution

/-! Exhaustive current-state request availability for M4. -/

namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation
open ScopedExpressions ScopedExecution ProtectionContracts
open ScopedPortProgress (CurrentForm)
open RecursiveExpressions (Ready)
open SourcePlannedTyping (Operations Value)

private theorem handler_request
    (valid : Valid policy outward ambient budget ports emptyRows output outputRows snapshot)
    (shape : snapshot.run =
      ⟨⟨.eval ⟨.handle effect body arms, runtimeScope, stack⟩, issued, completed⟩, actions⟩) :
    Nonempty (Request snapshot) := by
  have source := valid.unpack.source
  generalize machineEq : snapshot.run.execution.machine = machine at source
  cases source with
  | eval site phaseAgreement rooted bound annotation checked bounded =>
      have target : snapshot.run.execution.machine =
          .eval ⟨.handle effect body arms, runtimeScope, stack⟩ :=
        congrArg (fun run => run.execution.machine) shape
      obtain ⟨expressionEq, scopeEq, stackEq⟩ :=
        Configuration.mk.inj (LexicalUnwind.Machine.eval.inj (machineEq.symm.trans target))
      obtain ⟨ticket, scopeTyped⟩ := site.scopeTyped
      have typed := SourceTemplates.expression_ports
        (DeclaredSources.expression_erase
          (SourceDependencyAnnotations.expression_erase
            (SourcePlannedSources.expression_erase site.current.previous.source))) scopeTyped
      rw [expressionEq] at typed
      cases typed with
      | handle => exact InstallationState.request_of_handler (effect := _) shape
  | unwind => cases machineEq.symm.trans (congrArg (fun run => run.execution.machine) shape)

theorem eval_available
    {operations : Operations} {snapshot : Snapshot operations} {ports : OperationRows operations}
    (compatible : SourceScheduledBuiltinSignatures.Compatible operations)
    (valid : Valid policy outward ambient budget ports emptyRows output outputRows snapshot)
    (shape : snapshot.run = ⟨⟨.eval ⟨code, runtimeScope, stack⟩, issued, completed⟩, actions⟩) :
    Terminal snapshot ∨ Nonempty (Request snapshot) := by
  have form := InstallationState.current_form valid (congrArg (fun run => run.execution.machine) shape)
  cases form with
  | value isValue => exact InstallationState.value_return_progress valid shape isValue
  | focus position => exact .inr (InstallationState.request_of_focus shape position)
  | bind isValue => exact .inr (InstallationState.request_of_ready valid shape (.bind isValue))
  | app functionValue argumentValue =>
      exact .inr (InstallationState.request_of_app valid shape functionValue argumentValue)
  | branch conditionValue =>
      exact .inr (InstallationState.request_of_branch valid shape conditionValue)
  | request operandValue => exact .inr (request_available compatible valid shape operandValue)
  | handler => exact .inr (handler_request valid shape)
  | resume operandValue => exact .inr (InstallationState.request_of_resume valid shape operandValue)
  | discard => exact .inr (InstallationState.request_of_discard valid shape)
  | resource initializerValue => exact .inr (InstallationState.request_of_resource shape initializerValue)
  | cleanup callbackValue => exact .inr (InstallationState.request_of_cleanup valid shape callbackValue)

theorem available
    {operations : Operations} {snapshot : Snapshot operations} {ports : OperationRows operations}
    (compatible : SourceScheduledBuiltinSignatures.Compatible operations)
    (valid : Valid policy outward ambient budget ports emptyRows output outputRows snapshot) :
    Terminal snapshot ∨ Nonempty (Request snapshot) := by
  cases runShape : snapshot.run with
  | mk execution actions =>
      cases execution with
      | mk machine issued completed =>
          cases machine with
          | eval configuration =>
              cases configuration with
              | mk code runtimeScope stack => exact eval_available compatible valid runShape
          | unwind runtimeScope stack => exact .inr (InstallationState.unwind_progress valid runShape)

/-- Every valid current state is terminal or takes an actual lexical event to
another valid state.  Request availability and preservation remain separate
premises internally; this is their public M4 progress composition. -/
theorem progress
    {operations : Operations} {snapshot : Snapshot operations} {ports : OperationRows operations}
    (compatible : SourceScheduledBuiltinSignatures.Compatible operations)
    (valid : Valid policy outward ambient budget ports emptyRows output outputRows snapshot) :
    Terminal snapshot ∨
      ∃ after : Snapshot operations,
        LexicalUnwind.Event snapshot.run.execution after.run.execution ∧
        Valid policy outward ambient budget ports emptyRows output outputRows after := by
  rcases available compatible valid with terminal | request
  · exact .inl terminal
  · cases request with
    | intro request =>
        obtain ⟨after, event, realizes, next⟩ := preservation valid request
        exact .inr ⟨after, event, next⟩

theorem finite_prefix
    {operations : Operations} {snapshot : Snapshot operations} {ports : OperationRows operations}
    (compatible : SourceScheduledBuiltinSignatures.Compatible operations)
    (valid : Valid policy outward ambient budget ports emptyRows output outputRows snapshot)
    (fuel : Nat) :
    ∃ count final,
      RawTrace snapshot.run.execution count final.run.execution ∧
      Valid policy outward ambient budget ports emptyRows output outputRows final ∧
      count ≤ fuel ∧ (count = fuel ∨ Terminal final) :=
  finite_prefix_with (fun _ next => available compatible next) valid fuel

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.eval_available
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.available
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.progress
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.finite_prefix
