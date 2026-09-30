import ContextualClauseChecks
import DeclaredSourceCapture

/-! Clause-row admission under an abstract, authenticated continuation
interface. Each source family produces a finite contextual derivation for its
exact requirement tree and an explicit advertised-row bound. Quantification is
over the local continuation interface, not future execution or successor
admissibility. Hereditary declarations retain these same certificates. -/
namespace Ash.OneShot.ClauseRowAdmission
open ScopedExpressions ScopedExecution CoherentSourceTypes ProtectionContracts ProtectionResiduals
open DeclaredSources (Expression)
open RecursiveRequirements (Requirements Store Checked)
open OwnerPhaseTransitions (Phases)
open ContextualClauseChecks (Derivation Invocation)

/-- The public clause interface is the same hereditary body judgment used in
all declarations; it does not wrap a weaker independently chosen source. -/
abbrev Body (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Owners.Contracts)
    (world : List Nat) (allowed : List Instance) (environment : Environment)
    (binder owner : Nat) (contract : Owners.Contract) (disposes : Bool) (advertised : Footprint)
    (code : Code) (answer : Value) : Prop :=
  DeclaredSources.Body operations policy contracts world allowed (.ticket binder owner) environment code answer
    ⟨owner, contract, disposes, advertised⟩

theorem source
    (admitted : Body operations policy contracts world allowed environment binder owner contract disposes advertised code answer) :
    ∃ demand, ∃ requirements : Requirements demand,
      Expression operations policy contracts world allowed (.ticket binder owner) environment code answer demand requirements := by
  cases admitted with
  | typed source rows => exact ⟨_, _, source⟩

/-- Instantiation returns source and checking at exactly the same requirement
index. No whole-clause check is assumed. -/
theorem instantiate
    (admitted : Body operations policy contracts world allowed environment binder owner contract disposes advertised code answer)
    (interface : Interface owner contract disposes store tail before requestRow)
    (exported : OwnerSource.exportAt tail before advertised = some requestRow)
    (templates : SourceStore operations owner contract store) :
    ∃ demand, ∃ requirements : Requirements demand, ∃ row,
      Expression operations policy contracts world allowed (.ticket binder owner) environment code answer demand requirements ∧
      Checked store (.live owner contract.held :: tail) before requirements row ∧
      EffectBounds.Covers (requestRow ++ contract.resumeRow) row := by
  cases admitted with
  | typed source rows =>
      obtain ⟨row, checked, covered⟩ := rows.instantiate interface exported templates
      exact ⟨_, _, row, source, checked, covered⟩

theorem environment_congr
    (admitted : Body operations policy contracts world allowed environment binder owner contract disposes advertised code answer)
    (same : AgreeOn environment destination code.dependencies) :
    Body operations policy contracts world allowed destination binder owner contract disposes advertised code answer := by
  cases admitted with
  | typed source rows => exact .typed (DeclaredSourceTransport.expression_environment_congr source same) rows

theorem world_weaken
    (admitted : Body operations policy contracts world allowed environment binder owner contract disposes advertised code answer)
    (larger : world ⊆ next) :
    Body operations policy contracts next allowed environment binder owner contract disposes advertised code answer := by
  cases admitted with
  | typed source rows => exact .typed (DeclaredSourceTransport.expression_world_weaken source larger) rows

theorem extension
    (admitted : Body operations policy contracts world allowed environment binder owner contract disposes advertised code answer)
    (larger : contracts.Extends next) :
    Body operations policy next world allowed environment binder owner contract disposes advertised code answer := by
  cases admitted with
  | typed source rows => exact .typed (DeclaredSourceTransport.expression_extension source larger) rows

theorem substitution
    (admitted : Body operations policy contracts world allowed (environment.extend name input)
      binder owner contract disposes advertised code answer)
    (replacement : DeclaredSourceValues.ValueSummary operations policy contracts world environment allowed value input)
    (closed : ClosedValue value) :
    Body operations policy contracts world allowed environment binder owner contract disposes advertised (code.subst name value) answer := by
  cases admitted with
  | typed source rows => exact .typed (DeclaredSourceSubstitution.substitution source replacement closed) rows

/-- Immediate value resumption derives its certificate from the authenticated
resume argument using the established source/value lemma. -/
theorem resume_value
    (current : Expression operations policy contracts world allowed (.ticket binder owner) environment
      (.resume binder value) answer demand requirements)
    (isValue : value.IsValue) (known : contracts owner = some contract) :
    Body operations policy contracts world allowed environment binder owner contract disposes advertised (.resume binder value) answer := by
  apply DeclaredSources.Body.typed current
  intro store tail before requestRow interface exported
  have checked := SourceClauseCapture.resume_value_certificate (DeclaredSources.expression_erase current) isValue known interface.resume
  obtain ⟨calls, derived, supplied⟩ := ContextualClauseChecks.open_checked checked
  exact ⟨contract.resumeRow, calls, derived, supplied, List.subset_append_right _ _⟩

end Ash.OneShot.ClauseRowAdmission

#print axioms Ash.OneShot.ClauseRowAdmission.source
#print axioms Ash.OneShot.ClauseRowAdmission.instantiate
#print axioms Ash.OneShot.ClauseRowAdmission.environment_congr
#print axioms Ash.OneShot.ClauseRowAdmission.world_weaken
#print axioms Ash.OneShot.ClauseRowAdmission.extension
#print axioms Ash.OneShot.ClauseRowAdmission.substitution
#print axioms Ash.OneShot.ClauseRowAdmission.resume_value
