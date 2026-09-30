import SourceRequestFootprints
import SourcePlannedSourceReduction

/-! Request interfaces follow the signatures already retained by rich source
typing. Substitution and beta reduction reuse their established proofs; actual
handler witnesses retain the same interface when source typing materializes
different clause syntax. This is interface provenance, not complete admission. -/
namespace Ash.OneShot.SourceRequestInterfaceRetention
open ScopedExpressions ScopedExecution
open SourceRequestFootprints (Footprint)
open SourceDeclarationPlans (Plan ClausePlans)
open SourcePlanSignatures (signature clauseSignatures substituteClauses)
open SourcePlannedSources (Expression ValueSummary)

/-- Closed source substitution preserves the same checking signature and
therefore the same finite operation interface. -/
theorem substitution
    (source : Expression operations policy contracts world allowed scope (environment.extend name input)
      code result demand requirements checking)
    (replacement : ValueSummary operations policy contracts world environment allowed value input)
    (closed : ClosedValue value) (interface : Footprint checking required) :
    Expression operations policy contracts world allowed scope environment (code.subst name value)
      result demand requirements checking ∧ Footprint checking required :=
  ⟨SourcePlannedSources.substitution source replacement closed, interface⟩

/-- A function's declared interface belongs to its latent signature. The
existing beta theorem returns that exact signature for the substituted body. -/
theorem beta
    (source : Expression operations policy contracts world allowed scope environment
      (.app (.lambda parameter body) value) result demand requirements
      (.sequence functionSignature (.sequence argumentSignature bodySignature)))
    (closed : ClosedValue value) (interface : Footprint bodySignature required) :
    ∃ reduced,
      Expression operations policy contracts world allowed .none environment (body.subst parameter value)
        result demand reduced bodySignature ∧ Footprint bodySignature required ∧
      ∀ store receiving before,
        RecursiveRequirements.evaluate store receiving before reduced =
          RecursiveRequirements.evaluate store receiving before requirements := by
  obtain ⟨reduced, body, evaluation⟩ := SourcePlannedSources.beta_expression source closed
  exact ⟨reduced, body, interface, evaluation⟩

/-- Source handler decomposition authenticates its actual declarations.
The reference clause syntax may differ, but the stable signature and request
interface remain the same. No declaration recipe is inferred from this fact. -/
theorem actual_handler {reference : ClausePlans referenceClauses families} {bodyPlan : Plan dependencies}
    (source : Expression operations policy contracts world allowed scope environment
      (.handle (Instantiation.freezeEffect effect) code arms) answer demand requirements
      (signature (.handler (effect := effect) (table := table) required reference bodyPlan)))
    (interface : Footprint (signature (.handler (effect := effect) (table := table) required reference bodyPlan)) exposed) :
    ∃ residual, ∃ bodyRequirements, ∃ actual : ClausePlans arms families,
      Expression operations policy contracts world (effect :: residual) scope environment code answer demand bodyRequirements
        (signature bodyPlan) ∧
      SourcePlannedSources.Declarations operations policy contracts world environment residual effect answer arms table actual ∧
      Footprint (signature (.handler (effect := effect) (table := table) required actual bodyPlan)) exposed := by
  obtain ⟨residual, bodyRequirements, actual, body, declarations, same, rows⟩ :=
    SourcePlannedSources.handler_body source
  exact ⟨residual, bodyRequirements, actual, body, declarations,
    interface.congr (by simp only [signature, same])⟩

/-- Value substitution may change literal declaration bodies. Reuse their
established signature preservation rather than rechecking their interface. -/
theorem substituted_declarations {plans : ClausePlans clauses families} {body : Plan dependencies}
    (interface : Footprint (signature (.handler (effect := effect) (table := table) required plans body)) exposed)
    (isValue : value.IsValue) :
    Footprint (signature (.handler (effect := effect) (table := table) required
      (substituteClauses plans name value) body)) exposed :=
  interface.congr (by simp only [signature, SourcePlanSignatures.substitution_signature plans isValue])

namespace Examples
open SourceDependencyAnnotations.Examples (effectE effectF policy allowed cleanupBody functionCode noRequirements invokedRequirements)
open SourcePlannedTyping.Examples (operations contracts environment cleanupSignature)

/-- This interface is read from a callable signature, without constructing a
concrete declaration-plan witness for the future function invocation. -/
theorem callable_interface : Footprint cleanupSignature [(effectF, 0), (effectE, 0)] :=
  .sequence (firstRequired := []) (secondRequired := [(effectF, 0), (effectE, 0)]) .pure
    (.cleanup (callbackRequired := [(effectF, 0)]) (bodyRequired := [(effectE, 0)])
      (.sequence (firstRequired := []) (secondRequired := [(effectF, 0)]) .pure .request)
      (.sequence (firstRequired := []) (secondRequired := [(effectE, 0)]) .pure .request))

/-- Reuse the existing higher-order source example through actual bind and
beta substitutions. Both typed stages carry the same callable body interface. -/
theorem higher_order_interface_retained : ∃ first second,
    Expression operations policy contracts [] allowed .none environment (.app functionCode .unit) .unit [] first
      (.sequence .pure (.sequence .pure cleanupSignature)) ∧
    Expression operations policy contracts [] allowed .none environment cleanupBody .unit [] second cleanupSignature ∧
    Footprint cleanupSignature [(effectF, 0), (effectE, 0)] ∧
    ∀ store receiving before,
      RecursiveRequirements.evaluate store receiving before first =
        RecursiveRequirements.evaluate store receiving before (.sequence noRequirements invokedRequirements) ∧
      RecursiveRequirements.evaluate store receiving before second =
        RecursiveRequirements.evaluate store receiving before first := by
  obtain ⟨first, second, bound, reduced, evaluation⟩ := SourcePlannedSources.Examples.higher_order_reduction
  exact ⟨first, second, bound, reduced, callable_interface, evaluation⟩

/-- The actual clause changes under substitution, while its computation
interface remains valid at the unchanged signature. -/
theorem changed_clause_retains_interface :
    SourcePlanSignatures.Examples.clauses.subst 2 .unit ≠ SourcePlanSignatures.Examples.clauses ∧
    Footprint (signature (.handler (effect := effectE) (table := []) []
      (substituteClauses SourcePlanSignatures.Examples.plans 2 .unit) Plan.pure)) [] := by
  exact ⟨SourcePlanSignatures.Examples.substituted_clause_changes,
    substituted_declarations (plans := SourcePlanSignatures.Examples.plans)
      (Footprint.handler (bodyRequired := []) .pure rfl) (by trivial)⟩

/-- Equal dependency indices do not permit erasing an installed handler's
requirements: those lists are part of the stable signature. -/
theorem changed_requirement_changes_signature :
    signature (.handler (effect := effectE) (table := []) [] ClausePlans.nil Plan.pure) ≠
    signature (.handler (effect := effectE) (table := []) [(effectF, 0)] ClausePlans.nil Plan.pure) := by
  intro same
  obtain ⟨different, _, _⟩ := SourcePlanSignatures.Signature.handler.inj same
  cases different

end Examples
end Ash.OneShot.SourceRequestInterfaceRetention

#print axioms Ash.OneShot.SourceRequestInterfaceRetention.substitution
#print axioms Ash.OneShot.SourceRequestInterfaceRetention.beta
#print axioms Ash.OneShot.SourceRequestInterfaceRetention.actual_handler
#print axioms Ash.OneShot.SourceRequestInterfaceRetention.substituted_declarations
#print axioms Ash.OneShot.SourceRequestInterfaceRetention.Examples.callable_interface
#print axioms Ash.OneShot.SourceRequestInterfaceRetention.Examples.higher_order_interface_retained
#print axioms Ash.OneShot.SourceRequestInterfaceRetention.Examples.changed_clause_retains_interface
#print axioms Ash.OneShot.SourceRequestInterfaceRetention.Examples.changed_requirement_changes_signature
