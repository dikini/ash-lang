import SourceScheduledM4Evaluation
import SourceScheduledM4RequestPackaging

/-! Returned-value and unwind request availability for the current M4 state. -/

namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation
open ScopedExpressions ScopedExecution ProtectionContracts
open RecursiveRequirements (Requirements)

theorem ExecutionSite.value_raw_progress
    (site : ExecutionSite ambient operations policy contracts tables families required outward actions phases world installations
      resumes budget ports owners emptyRows output outputRows)
    (rooted : ExecutionRoot operations policy contracts tables families required outward actions phases world installations
      resumes budget ports owners emptyRows output outputRows site (root : Requirements demand))
    (phaseAgreement : phases = OwnerPhaseTransitions.available (ownedTickets site.stack))
    (annotation : SourceDependencyAnnotations.RowAnnotation root annotated)
    (checked : RecursiveRequirements.Checked (annotateDisposalStore annotatedStore) [] phases
      (annotateDisposals annotated) row)
    (isValue : site.expression.IsValue) :
    site.stack = .nil ∨
      (∃ after discharged,
        RawStep ⟨site.expression, site.runtimeScope, site.stack⟩ after [] discharged) ∨
      (∃ identity caller tail, site.stack = .push (.closing identity caller) tail) ∨
      (∃ owner tail, site.stack = .push (.retiring owner) tail) ∨
      (∃ action tail, site.expression = .unit ∧ site.stack = .push (.unwinding action) tail) := by
  rcases site with ⟨expression, runtimeScope, stack, result, resultRows, allowed,
    dependencies, plan, rows, sourceDemand, sourceRequirements, receiving, hints, context,
    current, certified, scopeTyped, pendingDemand, pendingRequirements, pending, coherent,
    retained, currentResource, retainedResource⟩
  dsimp only at rooted phaseAgreement annotation checked isValue ⊢
  obtain ⟨ticket, scopeTyped⟩ := scopeTyped
  have typed := SourceTemplates.expression_ports
    (DeclaredSources.expression_erase
      (SourceDependencyAnnotations.expression_erase
        (SourcePlannedSources.expression_erase current.previous.source)))
    scopeTyped
  have closed := ScopedPorts.typed_value_closed typed isValue
  have waiting := rooted.value_wait isValue
  cases coherent with
  | nil => exact .inl rfl
  | live answerRows agreement inside tail =>
      cases waiting with
      | live tailWaiting =>
        obtain ⟨rootRow, rootCheck, _included⟩ := (disposal_annotation_map annotation).checked checked
        obtain ⟨spentRow, tailRow, spentCheck, _tailCheck, _same⟩ :=
          RecursiveRequirements.checked_sequence_parts rootCheck
        have evaluated := RecursiveRequirements.checked_complete spentCheck
        simp only [annotateDisposals, RecursiveRecomposition.evaluate_spent] at evaluated
        simp [phaseAgreement, OwnerPhaseTransitions.available, ownedTickets] at evaluated
  | spent tail =>
      exact .inr (.inl ⟨_, [], .leaveClause _ _ _ closed _ _ _⟩)
  | push head tail =>
      cases head with
      | ordinary authenticated =>
          cases authenticated with
          | plain authenticated => exact .inr (.inl ⟨_, [], .plug _ _ closed _ _⟩)
          | handler authenticated => exact .inr (.inl ⟨_, [], .leaveHandler _ _ closed _ _⟩)
          | cell => exact .inr (.inl ⟨_, [_], .leaveCell _ _ _ _ _ _ closed _⟩)
          | armed authenticated => exact .inr (.inl ⟨_, [], .startCleanup _ _ closed _ _⟩)
          | running callback saved =>
              have unit : expression = Code.unit := ScopedPortJoint.scoped_unit_value typed isValue
              subst expression
              exact .inr (.inl ⟨_, [_], .finishCleanup _ _ _ _ _⟩)
          | closing => exact .inr (.inr (.inl ⟨_, _, _, rfl⟩))
          | retiring => exact .inr (.inr (.inr (.inl ⟨_, _, rfl⟩)))
      | unwinding authenticated =>
          have unit : expression = Code.unit := ScopedPortJoint.scoped_unit_value typed isValue
          subst expression
          exact .inr (.inr (.inr (.inr ⟨_, _, rfl, rfl⟩)))
      | closing => exact .inr (.inr (.inl ⟨_, _, _, rfl⟩))
      | retiring => exact .inr (.inr (.inr (.inl ⟨_, _, rfl⟩)))

/-- An executable unwind source always exposes its next lexical transition.
The impossible empty and value-input cases are excluded by the mode indices. -/
theorem PlannedModeSource.unwind_transition
    (source : PlannedModeSource operations policy contracts tables families required outward actions world
      stack .unwind (.value output) demand requirements receiving) :
    ∃ after discharged,
      LexicalUnwind.Transition (.unwind runtimeScope stack) after [] discharged := by
  cases source with
  | push head tail =>
      cases head with
      | closing => exact ⟨_, _, .finishClose⟩
      | retiring => exact ⟨_, _, .advance .retire⟩
      | skipped => exact ⟨_, _, .advance .plain⟩
      | handler source => exact ⟨_, _, .advance .handler⟩
      | cell => exact ⟨_, _, .advance .cell⟩
      | cleanup callback certified => exact ⟨_, _, .startCleanup⟩
  | opening saved tail => exact ⟨_, _, .advance .live⟩
  | skippedSpent tail => exact ⟨_, _, .advance .spent⟩

theorem InstallationState.value_return_progress
    {operations : SourcePlannedTyping.Operations} {snapshot : Snapshot operations}
    {ports : OperationRows operations}
    (valid : Valid policy outward ambient budget ports emptyRows output outputRows snapshot)
    (shape : snapshot.run =
      ⟨⟨.eval ⟨value, runtimeScope, stack⟩, issued, completed⟩, actions⟩)
    (isValue : value.IsValue) : Terminal snapshot ∨ Nonempty (Request snapshot) := by
  have source := valid.unpack.source
  have machineShape : snapshot.run.execution.machine = .eval ⟨value, runtimeScope, stack⟩ :=
    congrArg (fun run => run.execution.machine) shape
  generalize sourceMachineEq : snapshot.run.execution.machine = machine at source
  cases source with
  | eval site phaseAgreement rooted bound annotation checked bounded =>
      obtain ⟨expressionEq, scopeEq, stackEq⟩ :=
        Configuration.mk.inj (LexicalUnwind.Machine.eval.inj (sourceMachineEq.symm.trans machineShape))
      have siteValue : site.expression.IsValue := expressionEq.symm ▸ isValue
      have closed := InstallationSupport.Preservation.ExecutionSite.current_value_closed site siteValue
      rcases InstallationSupport.Preservation.ExecutionSite.value_raw_progress site rooted phaseAgreement annotation checked siteValue with terminal | raw | closing | retiring | unwinding
      · refine .inl ⟨value, runtimeScope, isValue, ?_⟩
        exact machineShape.trans (by simp only [← expressionEq, ← scopeEq, ← stackEq, terminal])
      · obtain ⟨after, discharged, step⟩ := raw
        have raw' : RawStep ⟨value, runtimeScope, stack⟩ after [] discharged := by
          simpa only [expressionEq, scopeEq, stackEq] using step
        cases raw' with
        | plug plain value valueClosed scope tail =>
            exact .inr (request_of_stable_at shape (.plug (snapshot := snapshot) valueClosed))
        | leaveHandler handler value valueClosed scope tail =>
            exact .inr (request_of_stable_at shape (.leave_handler (snapshot := snapshot) valueClosed))
        | leaveCell identity payload answer savedScope scope value valueClosed tail =>
            exact .inr (request_of_stable_at shape (.leave_resource (snapshot := snapshot) valueClosed))
        | startCleanup action saved savedClosed scope tail =>
            exact .inr (request_of_stable_at shape (.start_normal_cleanup (snapshot := snapshot) savedClosed))
        | finishCleanup action saved savedClosed scope tail =>
            exact .inr (request_of_stable_at shape (.finish_normal_cleanup (snapshot := snapshot)))
        | leaveClause ticket answer value valueClosed scope caller tail =>
            exact .inr (request_of_stable_at shape (.leave_clause (snapshot := snapshot) valueClosed))
        | focus plain focus tail => exact False.elim (ScopedPorts.focus_is_not_value focus isValue)
        | finishClose identity scope caller tail =>
            exact .inr (request_of_stable_at shape (.finish_close_unit (snapshot := snapshot)))
        | retire ticket scope tail =>
            exact .inr (request_of_stable_at shape (.retire (snapshot := snapshot)))
        | bind | beta | ifTrue | ifFalse | enterHandler | resume | readCell | writeCell =>
            simp_all [Code.IsValue]
      · obtain ⟨identity, caller, tail, stackSame⟩ := closing
        have explicitStack : stack = .push (.closing identity caller) tail := stackEq.symm.trans stackSame
        have beforeShape : snapshot.run =
            ⟨⟨.eval ⟨value, runtimeScope, .push (.closing identity caller) tail⟩, issued, completed⟩, actions⟩ := by
          simpa only [explicitStack] using shape
        exact .inr (request_of_stable_at beforeShape
          (.close_value (snapshot := snapshot) (by simpa only [expressionEq] using closed)))
      · obtain ⟨owner, tail, stackSame⟩ := retiring
        have explicitStack : stack = .push (.retiring owner) tail := stackEq.symm.trans stackSame
        have beforeShape : snapshot.run =
            ⟨⟨.eval ⟨value, runtimeScope, .push (.retiring owner) tail⟩, issued, completed⟩, actions⟩ := by
          simpa only [explicitStack] using shape
        exact .inr (request_of_stable_at beforeShape
          (.retire_value (snapshot := snapshot) (by simpa only [expressionEq] using closed)))
      · obtain ⟨action, tail, expressionSame, stackSame⟩ := unwinding
        have explicitExpression : value = .unit := expressionEq.symm.trans expressionSame
        have explicitStack : stack = .push (.unwinding action) tail := stackEq.symm.trans stackSame
        have beforeShape : snapshot.run =
            ⟨⟨.eval ⟨.unit, runtimeScope, .push (.unwinding action) tail⟩, issued, completed⟩, actions⟩ := by
          simpa only [explicitExpression, explicitStack] using shape
        exact .inr (request_of_stable_at beforeShape
          (.finish_unwind_cleanup (snapshot := snapshot)))
  | unwind => cases sourceMachineEq.symm.trans machineShape

theorem InstallationState.unwind_progress
    {operations : SourcePlannedTyping.Operations} {snapshot : Snapshot operations}
    {ports : OperationRows operations}
    (valid : Valid policy outward ambient budget ports emptyRows output outputRows snapshot)
    (shape : snapshot.run =
      ⟨⟨.unwind runtimeScope stack, issued, completed⟩, actions⟩) :
    Nonempty (Request snapshot) := by
  have source := valid.unpack.source
  have machineShape : snapshot.run.execution.machine = .unwind runtimeScope stack :=
    congrArg (fun run => run.execution.machine) shape
  generalize sourceMachineEq : snapshot.run.execution.machine = machine at source
  cases source with
  | eval => cases sourceMachineEq.symm.trans machineShape
  | unwind pending coherent certificate waiting bound annotation checked bounded resourceChecked =>
      obtain ⟨scopeEq, stackEq⟩ := LexicalUnwind.Machine.unwind.inj (sourceMachineEq.symm.trans machineShape)
      cases scopeEq
      cases stackEq
      obtain ⟨after, discharged, transition⟩ :=
        InstallationSupport.Preservation.PlannedModeSource.unwind_transition
          (runtimeScope := runtimeScope) pending
      cases transition with
      | advance step =>
          exact request_of_stable_at shape (.advance (snapshot := snapshot) step)
      | startCleanup =>
          exact request_of_stable_at shape (.start_unwind_cleanup (snapshot := snapshot))
      | finishClose =>
          exact request_of_stable_at shape (.finish_unwind_close (snapshot := snapshot))

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.ExecutionSite.value_raw_progress
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.PlannedModeSource.unwind_transition
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.InstallationState.value_return_progress
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.InstallationState.unwind_progress
