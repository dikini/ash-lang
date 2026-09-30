import SourcePlannedSourceSubstitution
import SourcePlanSignatureChecking

/-! Bind and beta reduction retain the synchronized body derivation. The
ownership and requirement evaluation arguments reuse the established lemmas;
no weaker paired source certificate is used as the successor. -/
namespace Ash.OneShot.SourcePlannedSources
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open RecursiveRequirements (Requirements evaluate)
open OwnerPhaseTransitions (spendAll)
open RecursiveContexts (evaluate_request)
open SourcePlannedTyping (Value Environment Operations Contract Contracts)
open SourcePlanSignatures (Signature)
open SourceScheduledCleanupInterfaces.Lexical.Recursive (annotateDisposals)

/-- Extract the actual lambda body without selecting another intermediate type. -/
theorem lambda_body
    (function : Expression operations policy contracts world allowed scope environment
      (.lambda parameter code) (.function input output requests latent bodySignature) functionDemand functionRequirements functionSignature) :
    ∃ demand requirements,
      Expression operations policy contracts world requests .none (environment.extend parameter input)
        code output demand requirements bodySignature ∧ RecursiveOutward.Outward requirements (some latent) := by
  cases function with
  | lambda body outward formed bound => exact ⟨_, _, body, outward⟩

theorem beta_body
    (function : Expression operations policy contracts world allowed scope environment
      (.lambda parameter code) (.function input output requests latent bodySignature) functionDemand functionRequirements functionSignature)
    (argument : ValueSummary operations policy contracts world environment allowed value input)
    (closed : ClosedValue value) (admitted : requests ⊆ allowed) :
    ∃ demand requirements,
      Expression operations policy contracts world allowed .none environment
        (code.subst parameter value) output demand requirements bodySignature ∧
      RecursiveOutward.Outward requirements (some latent) := by
  obtain ⟨demand, requirements, body, outward⟩ := lambda_body function
  have replaced := substitution body (Values.change_allowed argument closed.1 requests) closed
  exact ⟨demand, requirements, expression_allowed_mono replaced admitted, outward⟩

theorem bind_expression
    (source : Expression operations policy contracts world allowed scope environment (.bind parameter value body)
      result demand requirements (.sequence initialSignature bodySignature))
    (closed : ClosedValue value) :
    ∃ reduced, Expression operations policy contracts world allowed scope environment (body.subst parameter value)
      result demand reduced bodySignature ∧
      ∀ store receiving before, evaluate store receiving before reduced = evaluate store receiving before requirements := by
  cases source with
  | bind initializer body =>
      have empty := SourceTemplates.expression_value_demand
        (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase (expression_erase initializer))) closed.1
      subst_vars
      refine ⟨_, substitution body (Values.summary initializer closed.1) closed, ?_⟩
      intro store receiving before
      rw [RecursiveRequirements.evaluate_sequence,
        RecursiveRecomposition.value_evaluation
          (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase (expression_erase initializer))) closed.1]
      simp only [OwnerPhaseTransitions.spendAll, RecursiveRecomposition.merge_empty_left]

theorem beta_expression
    (source : Expression operations policy contracts world allowed scope environment (.app (.lambda parameter body) value)
      result demand requirements (.sequence functionSignature (.sequence argumentSignature bodySignature)))
    (closed : ClosedValue value) :
    ∃ reduced, Expression operations policy contracts world allowed .none environment (body.subst parameter value)
      result demand reduced bodySignature ∧
      ∀ store receiving before, evaluate store receiving before reduced = evaluate store receiving before requirements := by
  cases source with
  | app function argument admitted =>
      have functionDemand := SourceTemplates.expression_value_demand
        (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase (expression_erase function))) trivial
      have argumentDemand := SourceTemplates.expression_value_demand
        (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase (expression_erase argument))) closed.1
      subst_vars
      obtain ⟨demand, reduced, next, outward⟩ := beta_body function (Values.summary argument closed.1) closed admitted
      have empty := RecursiveOutward.no_owners outward
      subst demand
      refine ⟨reduced, next, ?_⟩
      intro store receiving before
      rw [RecursiveOutward.evaluation outward, RecursiveRequirements.evaluate_emit, RecursiveRequirements.evaluate_sequence,
        RecursiveRecomposition.value_evaluation
          (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase (expression_erase function))) trivial,
        RecursiveRecomposition.value_evaluation
          (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase (expression_erase argument))) closed.1]
      simp only [OwnerPhaseTransitions.spendAll, List.nil_append, RecursiveRecomposition.merge_empty_left]
      rfl

/-- A pure dependency index has no scope-sensitive immediate operation.
Latent lambda bodies retain their complete original derivations. -/
theorem pure_scope {checking : Signature dependencies}
    (source : Expression operations policy contracts world allowed scope environment code value demand requirements checking)
    (silent : dependencies = .pure) (next : Execution.Scope) :
    Expression operations policy contracts world allowed next environment code value demand requirements checking := by
  induction source using Expression.rec
    (motive_2 := fun _ _ _ _ _ _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ _ _ _ _ _ => True) with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference issued => exact .reference issued
  | «variable» known formed => exact .variable known formed
  | lambda body outward formed bound ih => exact .lambda body outward formed bound
  | purePair left right ihLeft ihRight => exact .purePair (ihLeft rfl) (ihRight rfl)
  | pair | app | bind | branch | perform | handler | resume | discard | cleanup | resource => cases silent
  | typed | unavailable | available | nil | cons => trivial

theorem summary_expression
    (source : ValueSummary operations policy contracts world environment allowed code value) (scope : Execution.Scope) :
    Expression operations policy contracts world allowed scope environment code value [] (.request [] []) .pure :=
  pure_scope source rfl scope

/-- Recomposition retains the same intermediate types and source signatures.
Only the resulting syntax's signature is constructed by the appropriate rule;
all requirement composition laws are reused. -/
theorem context_plug_disposals
    (context : Context operations policy contracts world environment allowed scope position input output restDemand rest checking)
    (child : Expression operations policy contracts world allowed scope environment code input childDemand current childChecking) :
    ∃ (combined : Requirements (childDemand ++ restDemand)) (dependencies : SourceDependencyAnnotations.Dependencies)
      (resultChecking : Signature dependencies),
      Expression operations policy contracts world allowed scope environment (position.plug code) output
        (childDemand ++ restDemand) combined resultChecking ∧
      ∀ store receiving before,
        (evaluate store receiving before combined =
          merge (evaluate store receiving before current) (evaluate store receiving (spendAll before childDemand) rest)) ∧
        evaluate store receiving before (annotateDisposals combined) =
          merge (evaluate store receiving before (annotateDisposals current))
            (evaluate store receiving (spendAll before childDemand) (annotateDisposals rest)) := by
  cases context with
  | pairLeft right => exact ⟨_, _, _, .pair child right, fun _ _ _ => ⟨RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_sequence⟩⟩
  | pairRight left =>
      rw [List.append_nil]
      refine ⟨_, _, _, .pair (summary_expression left _) child, ?_⟩
      intro store receiving before
      constructor <;> simp only [annotateDisposals, RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.evaluate_empty, spendAll,
        RecursiveRecomposition.merge_empty_left, RecursiveRecomposition.merge_empty_right]
  | appFunction argument admitted =>
      refine ⟨_, _, _, .app child argument admitted, ?_⟩
      intro store receiving before
      constructor <;> simp only [annotateDisposals, RecursiveRequirements.evaluate_emit, RecursiveRequirements.evaluate_sequence, PhaseRechecking.spendAll_append, merge_assoc]
  | appArgument function admitted =>
      rw [List.append_nil]
      refine ⟨_, _, _, .app (summary_expression function _) child admitted, ?_⟩
      intro store receiving before
      constructor <;> simp only [annotateDisposals, RecursiveRequirements.evaluate_emit, RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.evaluate_empty,
        spendAll, List.nil_append, RecursiveRecomposition.merge_empty_left, evaluate_request]
  | bind body => exact ⟨_, _, _, .bind child body, fun _ _ _ => ⟨RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_sequence⟩⟩
  | branch yes no same => exact ⟨_, _, _, .branch child yes no same, fun _ _ _ => ⟨RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_sequence⟩⟩
  | perform known admitted formed =>
      rw [List.append_nil]
      refine ⟨_, _, _, .perform known admitted child formed, ?_⟩
      intro store receiving before
      constructor <;> simp only [annotateDisposals, RecursiveRequirements.evaluate_emit, evaluate_request, List.nil_append]
  | resource body formed effectsBound admitted hidden =>
      exact ⟨_, _, _, .resource child body formed effectsBound admitted hidden,
        fun _ _ _ => ⟨RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_sequence⟩⟩
  | resume known resolved permission admitted formed =>
      exact ⟨_, _, _, .resume known resolved permission child admitted formed, fun _ _ _ => ⟨RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_sequence⟩⟩
  | cleanup body admitted =>
      refine ⟨_, _, _, .cleanup child body admitted, ?_⟩
      intro store receiving before
      constructor <;> simp only [annotateDisposals, RecursiveRequirements.evaluate_emit, RecursiveRequirements.evaluate_sequence, PhaseRechecking.spendAll_append, merge_assoc]

/-- Preserve the existing ordinary interface by projecting the paired equations. -/
theorem context_plug
    (context : Context operations policy contracts world environment allowed scope position input output restDemand rest checking)
    (child : Expression operations policy contracts world allowed scope environment code input childDemand current childChecking) :
    ∃ (combined : Requirements (childDemand ++ restDemand)) (dependencies : SourceDependencyAnnotations.Dependencies)
      (resultChecking : Signature dependencies),
      Expression operations policy contracts world allowed scope environment (position.plug code) output
        (childDemand ++ restDemand) combined resultChecking ∧
      ∀ store receiving before, evaluate store receiving before combined =
        merge (evaluate store receiving before current)
          (evaluate store receiving (OwnerPhaseTransitions.spendAll before childDemand) rest) := by
  obtain ⟨combined, dependencies, signature, source, evaluation⟩ := context_plug_disposals context child
  exact ⟨combined, dependencies, signature, source, fun store receiving before => (evaluation store receiving before).1⟩

/-- The full source derivation and the local checker now meet at the same
actual handler witness, preserving the full body/declaration typing. -/
theorem actual_handler_checked {plans : SourceDeclarationPlans.ClausePlans before families}
    (source : Expression operations policy contracts world allowed scope environment
      (.handle (Instantiation.freezeEffect effect) code arms) answer demand requirements
      (SourcePlanSignatures.signature (.handler (effect := effect) (table := table) required plans bodyPlan)))
    (checked : SourcePlannedChecks.Local outward actions phases world
      (.handler (effect := effect) (table := table) required plans bodyPlan) hints) :
    ∃ residual, ∃ bodyRequirements : Requirements demand, ∃ actual : SourceDeclarationPlans.ClausePlans arms families,
      Expression operations policy contracts world (effect :: residual) scope environment code answer demand bodyRequirements
        (SourcePlanSignatures.signature bodyPlan) ∧
      Declarations operations policy contracts world environment residual effect answer arms table actual ∧
      SourcePlannedChecks.Local outward actions phases world
        (.handler (effect := effect) (table := table) required actual bodyPlan) hints := by
  obtain ⟨residual, bodyRequirements, actual, body, declarations, same, requirementsSame⟩ := handler_body source
  exact ⟨residual, bodyRequirements, actual, body, declarations,
    SourcePlanSignatureChecking.local_congr checked (by simp only [SourcePlanSignatures.signature, same])⟩

/-- Binding a closed value preserves both the synchronized source derivation
and the stronger local check at the unchanged receiving scope and owner phase. -/
theorem bind_checked
    (source : Expression operations policy contracts world allowed scope environment (.bind parameter value body)
      result demand requirements (SourcePlanSignatures.signature (.sequence initialPlan bodyPlan)))
    (checked : SourcePlannedChecks.Local outward actions phases world (.sequence initialPlan bodyPlan) hints)
    (closed : ClosedValue value) :
    ∃ reduced, Expression operations policy contracts world allowed scope environment (body.subst parameter value)
      result demand reduced (SourcePlanSignatures.signature bodyPlan) ∧
      SourcePlannedChecks.Local outward actions phases world bodyPlan hints ∧
      ∀ store receiving before, evaluate store receiving before reduced = evaluate store receiving before requirements := by
  obtain ⟨reduced, next, evaluation⟩ := bind_expression source closed
  cases checked with
  | sequence first second => exact ⟨reduced, next, second, evaluation⟩

/-- Calling a closed lambda exposes the same locally checked body plan while
retaining the full source proof; no rechecking assumption is introduced. -/
theorem beta_checked
    (source : Expression operations policy contracts world allowed scope environment (.app (.lambda parameter body) value)
      result demand requirements (SourcePlanSignatures.signature (.sequence functionPlan (.sequence argumentPlan bodyPlan))))
    (checked : SourcePlannedChecks.Local outward actions phases world (.sequence functionPlan (.sequence argumentPlan bodyPlan)) hints)
    (closed : ClosedValue value) :
    ∃ reduced, Expression operations policy contracts world allowed .none environment (body.subst parameter value)
      result demand reduced (SourcePlanSignatures.signature bodyPlan) ∧
      SourcePlannedChecks.Local outward actions phases world bodyPlan hints ∧
      ∀ store receiving before, evaluate store receiving before reduced = evaluate store receiving before requirements := by
  obtain ⟨reduced, next, evaluation⟩ := beta_expression source closed
  cases checked with
  | sequence function argumentAndBody => cases argumentAndBody with
    | sequence argument body => exact ⟨reduced, next, body, evaluation⟩

namespace Examples
open SourceDependencyAnnotations.Examples (effectE effectF allowed policy noRequirements requestRequirements cleanupBody
  cleanupRequirements cleanupDependencies cleanupRow functionCode boundProgram invokedRequirements)
open SourcePlannedTyping.Examples (operations contracts environment cleanupSignature functionType)

theorem cleanup_source (environment : Environment) :
    Expression operations policy contracts [] allowed .none environment cleanupBody .unit [] cleanupRequirements cleanupSignature := by
  have callbackSource : Expression operations policy contracts [] allowed .none environment
      SourceDependencyAnnotations.Examples.callback
      (.function .unit .unit [effectF] [⟨effectF, 0, false⟩] (.sequence .pure (.request (effect := effectF) (operation := 0))))
      [] noRequirements .pure :=
    .lambda (.perform rfl (by simp) .unit
      (by simp [Value.erase, SourceDependencyAnnotations.Value.erase, ScopedPorts.InWorld, CoherentSourceTypes.Value.port, ScopedPorts.Port.resources]))
      (.emitAfter (layers := []) (.request (layers := [])))
      (by simp [Value.erase, SourceDependencyAnnotations.Value.erase, ScopedPorts.InWorld, CoherentSourceTypes.Value.port,
        ScopedPorts.Port.resources, effectF, Instance.resources])
      (by intro request member; cases List.mem_singleton.mp member; exact List.mem_cons_self)
  exact .cleanup callbackSource (.perform rfl (by simp [allowed]) .unit
    (by simp [Value.erase, SourceDependencyAnnotations.Value.erase, ScopedPorts.InWorld, CoherentSourceTypes.Value.port, ScopedPorts.Port.resources]))
    (by simp [allowed])

theorem function_source : Expression operations policy contracts [] allowed .none environment functionCode functionType
    [] noRequirements .pure :=
  .lambda (cleanup_source _) SourceDependencyAnnotations.Examples.cleanup_outward
    (by simp [Value.erase, SourceDependencyAnnotations.Value.erase, ScopedPorts.InWorld, CoherentSourceTypes.Value.port,
      ScopedPorts.Port.resources, allowed, effectE, effectF, Instance.resources])
    (by intro request member; simp [cleanupRow] at member; rcases member with rfl | rfl <;> simp [allowed])

theorem bound_source : Expression operations policy contracts [] allowed .none environment boundProgram .unit
    [] (.sequence noRequirements invokedRequirements)
    (.sequence .pure (.sequence .pure (.sequence .pure cleanupSignature))) :=
  .bind function_source (.app (.variable rfl
    (by simp [Value.erase, SourceDependencyAnnotations.Value.erase, ScopedPorts.InWorld, CoherentSourceTypes.Value.port,
      ScopedPorts.Port.resources, allowed, effectE, effectF, Instance.resources])) .unit (List.Subset.refl _))

/-- Both substitutions return the full synchronized source derivation. -/
theorem higher_order_reduction : ∃ first second,
    Expression operations policy contracts [] allowed .none environment (.app functionCode .unit) .unit [] first
      (.sequence .pure (.sequence .pure cleanupSignature)) ∧
    Expression operations policy contracts [] allowed .none environment cleanupBody .unit [] second cleanupSignature ∧
    ∀ store receiving before,
      evaluate store receiving before first = evaluate store receiving before (.sequence noRequirements invokedRequirements) ∧
      evaluate store receiving before second = evaluate store receiving before first := by
  obtain ⟨first, bound, bindEvaluation⟩ := bind_expression bound_source SourceDependencyAnnotations.Examples.annotated_function_closed
  obtain ⟨second, beta, betaEvaluation⟩ := beta_expression bound CallableProtection.Examples.unit_closed
  exact ⟨first, second, bound, beta, fun store receiving before =>
    ⟨bindEvaluation store receiving before, betaEvaluation store receiving before⟩⟩

end Examples

end Ash.OneShot.SourcePlannedSources

#print axioms Ash.OneShot.SourcePlannedSources.lambda_body
#print axioms Ash.OneShot.SourcePlannedSources.beta_body
#print axioms Ash.OneShot.SourcePlannedSources.bind_expression
#print axioms Ash.OneShot.SourcePlannedSources.beta_expression

#print axioms Ash.OneShot.SourcePlannedSources.summary_expression
#print axioms Ash.OneShot.SourcePlannedSources.context_plug

#print axioms Ash.OneShot.SourcePlannedSources.pure_scope

#print axioms Ash.OneShot.SourcePlannedSources.actual_handler_checked
#print axioms Ash.OneShot.SourcePlannedSources.Examples.cleanup_source
#print axioms Ash.OneShot.SourcePlannedSources.Examples.function_source
#print axioms Ash.OneShot.SourcePlannedSources.Examples.bound_source
#print axioms Ash.OneShot.SourcePlannedSources.Examples.higher_order_reduction

#print axioms Ash.OneShot.SourcePlannedSources.bind_checked
#print axioms Ash.OneShot.SourcePlannedSources.beta_checked

#print axioms Ash.OneShot.SourcePlannedSources.context_plug_disposals
