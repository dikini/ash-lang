import SourceScheduledM4Progress
import SourceScheduledM4Terminal

/-! Ordinary-evaluation request adapters for M4.

The current snapshot keeps source typing inside `InstallationState`.  These
lemmas expose only the consequences needed by progress: value closedness,
ordinary ready computation, and source-independent request packaging. -/

namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Operations)
open RecursiveExpressions (Ready)

/-- Empty-environment source typing closes every current value. -/
theorem ExecutionSite.current_value_closed
    (site : ExecutionSite ambient operations policy contracts tables families required outward actions phases world installations
      resumes budget ports owners emptyRows output outputRows)
    (isValue : site.expression.IsValue) :
    ClosedValue site.expression := by
  obtain ⟨ticket, scopeTyped⟩ := site.scopeTyped
  have typed := SourceTemplates.expression_ports
    (DeclaredSources.expression_erase
      (SourceDependencyAnnotations.expression_erase
        (SourcePlannedSources.expression_erase site.current.previous.source)))
    scopeTyped
  exact ScopedPorts.typed_value_closed typed isValue

theorem ExecutionSite.resume_operand_closed
    (site : ExecutionSite ambient operations policy contracts tables families required outward actions phases world installations
      resumes budget ports owners emptyRows output outputRows)
    (expression : site.expression = .resume binder operand)
    (isValue : operand.IsValue) : ClosedValue operand := by
  obtain ⟨ticket, scopeTyped⟩ := site.scopeTyped
  have typed := SourceTemplates.expression_ports
    (DeclaredSources.expression_erase
      (SourceDependencyAnnotations.expression_erase
        (SourcePlannedSources.expression_erase site.current.previous.source))) scopeTyped
  rw [expression] at typed
  cases typed with
  | resume operandTyped => exact ScopedPorts.typed_value_closed operandTyped isValue

theorem ExecutionSite.ready_of_app
    (site : ExecutionSite ambient operations policy contracts tables families required outward actions phases world installations
      resumes budget ports owners emptyRows output outputRows)
    (expression : site.expression = .app function argument)
    (functionValue : function.IsValue) (argumentValue : argument.IsValue) :
    Ready site.expression := by
  obtain ⟨ticket, scopeTyped⟩ := site.scopeTyped
  have typed := SourceTemplates.expression_ports
    (DeclaredSources.expression_erase
      (SourceDependencyAnnotations.expression_erase
        (SourcePlannedSources.expression_erase site.current.previous.source))) scopeTyped
  rw [expression] at typed ⊢
  cases typed with
  | app functionTyped argumentTyped effects =>
      obtain ⟨parameter, body, rfl⟩ := ScopedPorts.typed_function_value functionTyped functionValue
      exact .app argumentValue

theorem ExecutionSite.ready_of_branch
    (site : ExecutionSite ambient operations policy contracts tables families required outward actions phases world installations
      resumes budget ports owners emptyRows output outputRows)
    (expression : site.expression = .branch condition yes no)
    (conditionValue : condition.IsValue) : Ready site.expression := by
  obtain ⟨ticket, scopeTyped⟩ := site.scopeTyped
  have typed := SourceTemplates.expression_ports
    (DeclaredSources.expression_erase
      (SourceDependencyAnnotations.expression_erase
        (SourcePlannedSources.expression_erase site.current.previous.source))) scopeTyped
  rw [expression] at typed ⊢
  cases typed with
  | branch conditionTyped yesTyped noTyped =>
      obtain ⟨flag, rfl⟩ := ScopedPorts.typed_boolean_value conditionTyped conditionValue
      exact .branch


/-- Closedness is recovered from the executable source at its actual machine
shape. -/
theorem ExecutableSource.current_value_closed
    (source : ExecutableSource ambient operations policy contracts tables families required outward actions annotations
      world installations resumes annotatedStore budget ports owners emptyRows output outputRows machine)
    (shape : machine = .eval ⟨code, runtimeScope, stack⟩)
    (isValue : code.IsValue) : ClosedValue code := by
  cases source with
  | eval site phaseAgreement rooted bound annotation checked bounded =>
      have fields := LexicalUnwind.Machine.eval.inj shape
      obtain ⟨expressionEq, runtimeEq, stackEq⟩ := ScopedExecution.Configuration.mk.inj fields
      simpa only [expressionEq] using
        ExecutionSite.current_value_closed site (expressionEq.symm ▸ isValue)
  | unwind pending coherent certificate waiting bound annotation checked bounded resourceChecked =>
      cases shape

theorem ExecutableSource.resume_operand_closed
    (source : ExecutableSource ambient operations policy contracts tables families required outward actions annotations
      world installations resumes annotatedStore budget ports owners emptyRows output outputRows machine)
    (shape : machine = .eval ⟨.resume binder operand, runtimeScope, stack⟩)
    (isValue : operand.IsValue) : ClosedValue operand := by
  cases source with
  | eval site phaseAgreement rooted bound annotation checked bounded =>
      have fields := LexicalUnwind.Machine.eval.inj shape
      obtain ⟨expressionEq, runtimeEq, stackEq⟩ := ScopedExecution.Configuration.mk.inj fields
      exact ExecutionSite.resume_operand_closed site expressionEq isValue
  | unwind pending coherent certificate waiting bound annotation checked bounded resourceChecked =>
      cases shape

theorem ExecutableSource.ready_of_app
    (source : ExecutableSource ambient operations policy contracts tables families required outward actions annotations
      world installations resumes annotatedStore budget ports owners emptyRows output outputRows machine)
    (shape : machine = .eval ⟨.app function argument, runtimeScope, stack⟩)
    (functionValue : function.IsValue) (argumentValue : argument.IsValue) :
    Ready (.app function argument) := by
  cases source with
  | eval site phaseAgreement rooted bound annotation checked bounded =>
      have fields := LexicalUnwind.Machine.eval.inj shape
      obtain ⟨expressionEq, runtimeEq, stackEq⟩ := ScopedExecution.Configuration.mk.inj fields
      simpa only [expressionEq] using
        ExecutionSite.ready_of_app site expressionEq functionValue argumentValue
  | unwind pending coherent certificate waiting bound annotation checked bounded resourceChecked => cases shape

theorem ExecutableSource.ready_of_branch
    (source : ExecutableSource ambient operations policy contracts tables families required outward actions annotations
      world installations resumes annotatedStore budget ports owners emptyRows output outputRows machine)
    (shape : machine = .eval ⟨.branch condition yes no, runtimeScope, stack⟩)
    (conditionValue : condition.IsValue) : Ready (.branch condition yes no) := by
  cases source with
  | eval site phaseAgreement rooted bound annotation checked bounded =>
      have fields := LexicalUnwind.Machine.eval.inj shape
      obtain ⟨expressionEq, runtimeEq, stackEq⟩ := ScopedExecution.Configuration.mk.inj fields
      simpa only [expressionEq] using
        ExecutionSite.ready_of_branch site expressionEq conditionValue
  | unwind pending coherent certificate waiting bound annotation checked bounded resourceChecked => cases shape

/-- The current source certificate supplies closedness without a raw-step
closedness premise. -/
theorem InstallationState.current_value_closed
    (valid : Valid policy outward ambient budget ports emptyRows output outputRows snapshot)
    (shape : snapshot.run.execution.machine =
      .eval ⟨code, runtimeScope, stack⟩)
    (isValue : code.IsValue) : ClosedValue code :=
  ExecutableSource.current_value_closed valid.unpack.source shape isValue

/-- Source typing constructs the ordinary raw step for every ready current
expression. -/
theorem ExecutionSite.ready_step
    (site : ExecutionSite ambient operations policy contracts tables families required outward actions phases world installations
      resumes budget ports owners emptyRows output outputRows)
    (ready : Ready site.expression) :
    ∃ after, RawStep ⟨site.expression, site.runtimeScope, site.stack⟩ after [] [] := by
  obtain ⟨ticket, scopeTyped⟩ := site.scopeTyped
  have typed := SourceTemplates.expression_ports
    (DeclaredSources.expression_erase
      (SourceDependencyAnnotations.expression_erase
        (SourcePlannedSources.expression_erase site.current.previous.source)))
    scopeTyped
  generalize expressionEq : site.expression = expression at ready typed ⊢
  cases ready with
  | bind isValue =>
      exact ⟨_, (ScopedPorts.typed_bind_value_progress typed isValue _ _).1⟩
  | app isValue =>
      obtain ⟨after, step, _typedAfter⟩ :=
        ScopedPorts.typed_application_value_progress typed trivial isValue _ _
      exact ⟨⟨after, .none, site.stack⟩, step⟩
  | @branch flag yes no =>
      cases flag
      · exact ⟨_, .ifFalse yes no _ _⟩
      · exact ⟨_, .ifTrue yes no _ _⟩

/-- Ready computation is recovered from the current executable source at its
actual machine shape. -/
theorem ExecutableSource.ready_step
    (source : ExecutableSource ambient operations policy contracts tables families required outward actions annotations
      world installations resumes annotatedStore budget ports owners emptyRows output outputRows machine)
    (shape : machine = .eval ⟨code, runtimeScope, stack⟩)
    (ready : Ready code) :
    ∃ after, RawStep ⟨code, runtimeScope, stack⟩ after [] [] := by
  cases source with
  | eval site phaseAgreement rooted bound annotation checked bounded =>
      have fields := LexicalUnwind.Machine.eval.inj shape
      obtain ⟨expressionEq, runtimeEq, stackEq⟩ := ScopedExecution.Configuration.mk.inj fields
      obtain ⟨after, raw⟩ := ExecutionSite.ready_step site (expressionEq.symm ▸ ready)
      exact ⟨after, by simpa only [expressionEq, runtimeEq, stackEq] using raw⟩
  | unwind pending coherent certificate waiting bound annotation checked bounded resourceChecked =>
      cases shape

/-- A ready current expression always supplies the stable M3 request expected
by preservation. -/
theorem InstallationState.request_of_ready
    {operations : Operations} {snapshot : Snapshot operations}
    {ports : OperationRows operations}
    (valid : Valid policy outward ambient budget ports emptyRows output outputRows snapshot)
    (shape : snapshot.run =
      ⟨⟨.eval ⟨code, runtimeScope, stack⟩, issued, completed⟩, actions⟩)
    (ready : Ready code) : Nonempty (Request snapshot) := by
  have machineShape : snapshot.run.execution.machine =
      .eval ⟨code, runtimeScope, stack⟩ := congrArg (fun run => run.execution.machine) shape
  obtain ⟨after, raw⟩ := ExecutableSource.ready_step valid.unpack.source machineShape ready
  cases snapshot with
  | mk contracts tables families required annotations world history resumes disposals annotatedStore owners run =>
      cases shape
      let before := Snapshot.mk (operations := operations) contracts tables families required annotations world history resumes
          disposals annotatedStore owners
          ⟨⟨.eval ⟨code, runtimeScope, stack⟩, issued, completed⟩, actions⟩
      exact ⟨.stable { before with
        run := ⟨⟨.eval after, issued, completed⟩, actions⟩ }
        (.computation (snapshot := before) (issued := issued) (completed := completed)
          (actions := actions) ready raw)⟩

/-- Any authenticated focus position is an allocating M3 request. -/
theorem InstallationState.request_of_focus
    (shape : snapshot.run =
      ⟨⟨.eval ⟨whole, runtimeScope, stack⟩, issued, completed⟩, actions⟩)
    (position : Focus whole child evaluationContext) : Nonempty (Request snapshot) :=
  ⟨.allocating (.focus shape position)⟩

theorem InstallationState.request_of_app
    (valid : Valid policy outward ambient budget ports emptyRows output outputRows snapshot)
    (shape : snapshot.run =
      ⟨⟨.eval ⟨.app function argument, runtimeScope, stack⟩, issued, completed⟩, actions⟩)
    (functionValue : function.IsValue) (argumentValue : argument.IsValue) :
    Nonempty (Request snapshot) := by
  have machineShape := congrArg (fun run => run.execution.machine) shape
  exact InstallationState.request_of_ready valid shape
    (ExecutableSource.ready_of_app valid.unpack.source machineShape functionValue argumentValue)

theorem InstallationState.request_of_branch
    (valid : Valid policy outward ambient budget ports emptyRows output outputRows snapshot)
    (shape : snapshot.run =
      ⟨⟨.eval ⟨.branch condition yes no, runtimeScope, stack⟩, issued, completed⟩, actions⟩)
    (conditionValue : condition.IsValue) : Nonempty (Request snapshot) := by
  have machineShape := congrArg (fun run => run.execution.machine) shape
  exact InstallationState.request_of_ready valid shape
    (ExecutableSource.ready_of_branch valid.unpack.source machineShape conditionValue)

theorem InstallationState.request_of_handler
    (shape : snapshot.run =
      ⟨⟨.eval ⟨.handle (Instantiation.freezeEffect effect) body arms, runtimeScope, stack⟩,
        issued, completed⟩, actions⟩) : Nonempty (Request snapshot) :=
  ⟨.allocating (.installHandler shape)⟩

theorem InstallationState.request_of_cleanup
    (valid : Valid policy outward ambient budget ports emptyRows output outputRows snapshot)
    (shape : snapshot.run =
      ⟨⟨.eval ⟨.cleanup callback body, runtimeScope, stack⟩, issued, completed⟩, actions⟩)
    (isValue : callback.IsValue) : Nonempty (Request snapshot) := by
  obtain ⟨identity, fresh⟩ := ScopedPortProgress.fresh_owner_exists Owner.cleanup
    (fun _ => rfl) valid.unpack.ledger.2
  rw [shape] at fresh
  exact ⟨.allocating (.registerCleanup shape isValue fresh)⟩

theorem InstallationState.request_of_resource
    (shape : snapshot.run =
      ⟨⟨.eval ⟨.resource binder initializer body, runtimeScope, stack⟩,
        issued, completed⟩, actions⟩)
    (isValue : initializer.IsValue) : Nonempty (Request snapshot) := by
  let identity := snapshot.world.foldr (fun n bound => max (n + 1) bound) 0
  have fresh : identity ∉ snapshot.world := by
    intro member
    exact (Nat.ne_of_lt (ScopedPortProgress.activation_below member)) rfl
  exact ⟨.allocating (.enterResource shape isValue fresh)⟩

theorem InstallationState.request_of_resume
    (valid : Valid policy outward ambient budget ports emptyRows output outputRows snapshot)
    (shape : snapshot.run =
      ⟨⟨.eval ⟨.resume binder operand, runtimeScope, stack⟩, issued, completed⟩, actions⟩)
    (isValue : operand.IsValue) : Nonempty (Request snapshot) := by
  have machineShape : snapshot.run.execution.machine =
      .eval ⟨.resume binder operand, runtimeScope, stack⟩ :=
    congrArg (fun run => run.execution.machine) shape
  exact ⟨.allocating (.resume shape
    (ExecutableSource.resume_operand_closed valid.unpack.source machineShape isValue))⟩

theorem InstallationState.request_of_discard
    (valid : Valid policy outward ambient budget ports emptyRows output outputRows snapshot)
    (shape : snapshot.run =
      ⟨⟨.eval ⟨.discard binder, runtimeScope, stack⟩, issued, completed⟩, actions⟩) :
    Nonempty (Request snapshot) := by
  obtain ⟨identity, fresh⟩ := ScopedPortProgress.fresh_owner_exists Owner.close
    (fun _ => rfl) valid.unpack.ledger.2
  rw [shape] at fresh
  have absent : Owner.close identity ∉ issued := by
    change (issued ++ [Owner.close identity]).Nodup at fresh
    intro present
    exact (List.nodup_append.mp fresh).2.2 _ present _ (by simp) rfl
  exact ⟨.allocating (.discard shape identity absent)⟩

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.ExecutionSite.current_value_closed
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.ExecutableSource.current_value_closed
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.ExecutionSite.resume_operand_closed
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.ExecutionSite.ready_of_app
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.ExecutionSite.ready_of_branch
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.ExecutableSource.resume_operand_closed
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.ExecutableSource.ready_of_app
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.ExecutableSource.ready_of_branch
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.InstallationState.current_value_closed
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.ExecutionSite.ready_step
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.ExecutableSource.ready_step
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.InstallationState.request_of_ready
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.InstallationState.request_of_focus
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.InstallationState.request_of_app
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.InstallationState.request_of_branch
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.InstallationState.request_of_handler
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.InstallationState.request_of_cleanup
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.InstallationState.request_of_resource
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.InstallationState.request_of_resume
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.InstallationState.request_of_discard
