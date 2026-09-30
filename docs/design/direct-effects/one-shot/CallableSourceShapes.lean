import ScopedRequirementShapes

/-! Callable bodies retain source grouping using the existing parameterized
callable judgment. All callable conversion and substitution reuse established
proofs. This exposes body geometry for capture checking; it does not yet prove
that source admission supplies every future capture's owner/closing checks. -/
namespace Ash.OneShot.CallableSourceShapes
open ScopedExpressions ScopedExecution CoherentSourceTypes ProtectionContracts
open RecursiveRequirements (Requirements)
open ScopedRequirementShapes (Shape Describes)

inductive Body (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Owners.Contracts) :
    CallableSources.BodyJudgment where
  | shaped (source : DeclaredSources.Expression operations policy contracts world allowed .none environment
        code output demand requirements)
      (shape : Shape requirements) (described : Describes code shape) :
      Body operations policy contracts world environment allowed code output demand requirements

abbrev Callable (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Owners.Contracts) :=
  CallableSources.Summary operations (Body operations policy contracts)

theorem body_source
    (body : Body operations policy contracts world environment allowed code output demand requirements) :
    DeclaredSources.Expression operations policy contracts world allowed .none environment
      code output demand requirements := by
  cases body with
  | shaped source shape described => exact source

theorem shape_body
    (source : DeclaredSources.Expression operations policy contracts world allowed .none environment
      code output demand requirements) :
    Body operations policy contracts world environment allowed code output demand requirements := by
  obtain ⟨shape, described⟩ := ScopedRequirementShapes.source_shape (DeclaredSources.expression_erase source)
  exact .shaped source shape described

/-- Reuse the generic body mapping; callable rules and their induction do not
change. Bodies keep their exact existing requirement indices. -/
theorem enrich
    (source : DeclaredSources.Callable operations policy contracts world environment allowed code value row) :
    Callable operations policy contracts world environment allowed code value row :=
  CallableSources.map_body source.to_generic (fun _ _ _ _ _ _ _ body => shape_body body)

theorem erase
    (source : Callable operations policy contracts world environment allowed code value row) :
    DeclaredSources.Callable operations policy contracts world environment allowed code value row :=
  DeclaredSources.Callable.from_generic
    (CallableSources.map_body source (fun _ _ _ _ _ _ _ body => body_source body))

/-- Existing closed substitution supplies the substituted source at the same
requirement index. Its grouping is derived from that resulting source code. -/
theorem body_substitution
    (body : Body operations policy contracts world (environment.extend name input) allowed code result demand requirements)
    (replacement : Callable operations policy contracts world environment allowed value input [])
    (closed : ClosedValue value) :
    Body operations policy contracts world environment allowed (code.subst name value) result demand requirements :=
  shape_body (DeclaredSourceSubstitution.substitution (body_source body) (erase replacement) closed)

theorem callable_substitution
    (source : Callable operations policy contracts world (environment.extend name input) allowed code result row)
    (replacement : Callable operations policy contracts world environment allowed value input [])
    (closed : ClosedValue value) :
    Callable operations policy contracts world environment allowed (code.subst name value) result row :=
  enrich (DeclaredSourceSubstitution.callable_substitution (erase source) (erase replacement) closed)

/-- Extract the retained grouping, rather than treating an empty latent row
as evidence that the body contains no interpretations or operations. -/
theorem lambda_shape
    (function : Callable operations policy contracts world environment allowed (.lambda parameter code)
      (.function input output requests latent) row) :
    ∃ demand, ∃ requirements : Requirements demand, ∃ shape : Shape requirements,
      DeclaredSources.Expression operations policy contracts world requests .none
        (environment.extend parameter input) code output demand requirements ∧
      Describes code shape ∧ RecursiveOutward.Outward requirements (some latent) := by
  cases function with
  | summaryLambda body outward formed => cases body with
    | shaped source shape described => exact ⟨_, _, shape, source, described, outward⟩

/-- Instantiate the body with an actual closed argument and expose its
source grouping. Old outward factorization proves the same effect result in
every ordered caller context and owner phase. No new preservation induction. -/
theorem application_shape
    (function : Callable operations policy contracts world environment allowed (.lambda parameter code)
      (.function input output requests latent) [])
    (argument : Callable operations policy contracts world environment allowed value input [])
    (closed : ClosedValue value) (admitted : requests ⊆ allowed) :
    ∃ requirements : Requirements [], ∃ shape : Shape requirements,
      DeclaredSources.Expression operations policy contracts world allowed .none environment
        (code.subst parameter value) output [] requirements ∧
      Describes (code.subst parameter value) shape ∧
      RecursiveOutward.Outward requirements (some latent) ∧
      ∀ store receiving phases, ScopedRequirementShapes.evaluate shape store receiving phases =
        OwnerSource.exportAt receiving phases latent := by
  obtain ⟨demand, requirements, source, outward⟩ := DeclaredSourceSubstitution.beta_body
    (DeclaredSourceValues.expression (erase function) .none) (erase argument) closed admitted
  have empty := RecursiveOutward.no_owners outward
  subst demand
  obtain ⟨shape, described⟩ := ScopedRequirementShapes.source_shape (DeclaredSources.expression_erase source)
  refine ⟨requirements, shape, source, described, outward, ?_⟩
  intro store receiving phases
  simpa only [Option.bind_some, ScopedRequirementShapes.evaluate, OwnerSource.exportAt]
    using RecursiveOutward.evaluation outward store receiving phases

/-- The grouped body can be checked using exactly the old latent-row result.
This is effect checking only; the per-site owner and closing checks are separate. -/
theorem checked_application_shape
    (function : Callable operations policy contracts world environment allowed (.lambda parameter code)
      (.function input output requests latent) [])
    (argument : Callable operations policy contracts world environment allowed value input [])
    (closed : ClosedValue value) (admitted : requests ⊆ allowed)
    (accepted : OwnerSource.exportAt receiving phases latent = some row) :
    ∃ requirements : Requirements [], ∃ shape : Shape requirements,
      DeclaredSources.Expression operations policy contracts world allowed .none environment
        (code.subst parameter value) output [] requirements ∧
      Describes (code.subst parameter value) shape ∧
      RecursiveRequirements.Checked store receiving phases requirements row := by
  obtain ⟨requirements, shape, source, described, outward, evaluated⟩ :=
    application_shape function argument closed admitted
  exact ⟨requirements, shape, source, described,
    RecursiveRequirements.evaluate_sound ((evaluated store receiving phases).trans accepted)⟩

namespace Examples
open SourceCallableExamples (operations policy contracts function functionType body)

theorem shaped_function : Callable operations policy contracts [] Environment.empty [] function functionType [] :=
  enrich (DeclaredSourceValues.value_summary
    (DeclaredSources.Examples.function_source contracts Environment.empty .none) trivial)

/-- Reuse the existing handler-bearing function with empty latent row. The
actual instantiated source still starts with a handler scope. -/
theorem empty_latent_retains_handler :
    ∃ requirements : Requirements [], ∃ shape : Shape requirements,
      DeclaredSources.Expression operations policy contracts [] [] .none Environment.empty
        (body.subst 0 .unit) .unit [] requirements ∧
      Describes (body.subst 0 .unit) shape ∧
      ScopedRequirementShapes.startsScope shape = true ∧
      ∀ store receiving phases, ScopedRequirementShapes.evaluate shape store receiving phases = some [] := by
  have argument : Callable operations policy contracts [] Environment.empty [] .unit .unit [] := .summaryUnit
  obtain ⟨requirements, shape, source, described, outward, evaluated⟩ :=
    application_shape shaped_function argument ScopedExecution.Examples.unit_closed (List.Subset.refl [])
  have grouped := ScopedRequirementShapes.handler_grouping described
  refine ⟨requirements, shape, source, described, grouped.symm, ?_⟩
  intro store receiving phases
  simpa only [OwnerSource.exportAt, ProtectionResiduals.residual_empty]
    using evaluated store receiving phases

end Examples
end Ash.OneShot.CallableSourceShapes

#print axioms Ash.OneShot.CallableSourceShapes.body_source
#print axioms Ash.OneShot.CallableSourceShapes.shape_body
#print axioms Ash.OneShot.CallableSourceShapes.enrich
#print axioms Ash.OneShot.CallableSourceShapes.erase
#print axioms Ash.OneShot.CallableSourceShapes.body_substitution
#print axioms Ash.OneShot.CallableSourceShapes.callable_substitution
#print axioms Ash.OneShot.CallableSourceShapes.lambda_shape
#print axioms Ash.OneShot.CallableSourceShapes.application_shape
#print axioms Ash.OneShot.CallableSourceShapes.checked_application_shape
#print axioms Ash.OneShot.CallableSourceShapes.Examples.shaped_function
#print axioms Ash.OneShot.CallableSourceShapes.Examples.empty_latent_retains_handler
