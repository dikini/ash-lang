import CoreCallableContractExecution

/-! Work in progress for authenticated common-contract handlers. The first
checkpoint checks literal clause substitution, the same recursive private
source, complete row retention and actual declaration-policy certification.
It does not yet construct a Source.handler or a capture successor Site. -/
namespace Ash.OneShot.CoreCallableContractHandlerExamples
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations (Dependencies ClauseDependencies)
open SourceDeclarationPlans (Plan ModePlans ClausePlans)
open SourcePlanSignatures (signature clauseSignatures substituteClauses)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive (declarationPolicy)
open CoreCallableContractSource (Contract Environment)
open CoreCallableContractRegistries (Registry OwnerContract Owners)
open CoreCallableContractAdmission
open SourcePlannedChecks (Certified CertifiedClauses)

local instance : SourcePlannedChecks.DeclarationPolicy := declarationPolicy

def registry : Registry := ⟨fun _ _ => none, fun _ => ⟨true, false⟩⟩
def owners : Owners := fun _ => none

def ownerContract : OwnerContract :=
  ⟨.unit, .unit, false, [], [], [], none, [], []⟩

def beforeBody : Code := .resume 9 (.variable 2)
def afterBody : Code := .resume 9 .unit

def bodyDependencies (owner : Nat) : Dependencies :=
  .sequence .pure (.invoke ⟨owner, .resume⟩)
def bodyPlan (owner : Nat) : Plan (bodyDependencies owner) := .sequence .pure .invoke
def bodyRows (owner : Nat) : Rows (signature (bodyPlan owner)) := .sequence .pure .invoke

def bodyRequirements (owner : Nat) : RecursiveRequirements.Requirements [owner] :=
  .sequence (.request [] []) (.invoke ⟨owner, .resume⟩ [] [])

/-- The captured ordinary variable is typed before closing the actual clause.
The owner is universally quantified, including occupied numeric identities. -/
theorem before_source (owner : Nat) :
    IndexedSource registry [] (owners.insert owner ownerContract) [] [] (.ticket 9 owner)
      ((Environment.empty.extend 1 .unit).extend 2 .unit) beforeBody .unit
      [owner] (bodyRequirements owner) (bodyPlan owner) (bodyRows owner) := by
  apply IndexedSource.resume (contract := ownerContract) (operandDemand := [])
    (operandReq := .request [] []) (operandPlan := .pure) (operandRows := Rows.pure)
    CoreCallableContractRegistries.Owners.insert_here rfl rfl
  · exact IndexedSource.variable (by simp [Environment.extend, ownerContract]) (by change [] ⊆ []; exact List.Subset.refl _)
  · exact List.Subset.refl _
  · change [] ⊆ []; exact List.Subset.refl _

/-- Closing preserves the same common endpoints, scalar requirements and
private body evidence, while the literal clause code changes. -/
theorem after_source (owner : Nat) :
    IndexedSource registry [] (owners.insert owner ownerContract) [] [] (.ticket 9 owner)
      (Environment.empty.extend 1 .unit) afterBody .unit
      [owner] (bodyRequirements owner) (bodyPlan owner) (bodyRows owner) := by
  simpa only [beforeBody, afterBody, Code.subst, ↓reduceIte] using
    (before_source owner).closed_substitution IndexedSource.unit ScopedExecution.Examples.unit_closed

def beforeClauses : Clauses := .cons 0 1 9 beforeBody .nil
def afterClauses : Clauses := .cons 0 1 9 afterBody .nil

def families : ClauseDependencies := [(0, some bodyDependencies, none)]
def beforePlans : ClausePlans beforeClauses families := .cons (.available bodyPlan) .unavailable .nil
def afterPlans : ClausePlans afterClauses families := substituteClauses beforePlans 2 .unit

def beforeRows : ClauseRows (clauseSignatures beforePlans) :=
  .cons (.available bodyRows) .unavailable .nil []
def afterRows : ClauseRows (clauseSignatures afterPlans) :=
  beforeRows.substitute 2 .unit trivial

theorem actual_clauses_changed : beforeClauses ≠ afterClauses := by
  intro same
  cases same

theorem exact_clause_closing : beforeClauses.subst 2 .unit = afterClauses := rfl

theorem actual_clause_signature : clauseSignatures afterPlans = clauseSignatures beforePlans :=
  SourcePlanSignatures.substitution_signature beforePlans trivial

theorem complete_clause_rows_retained : HEq afterRows beforeRows :=
  ClauseRows.substitute_heq beforeRows 2 .unit trivial

theorem before_certified :
    Certified (evidence := declarationPolicy) [] []
      (.handler (effect := Instance.user 9 []) (table := []) [] beforePlans Plan.pure) := by
  apply Certified.handler
  · exact .cons (.available (.existing (.silent (.resume rfl) .pure))) .unavailable .nil
  · exact .cons (.available (fun owner => (before_source owner).certified)) .unavailable .nil
  · exact .pure

/-- Certification is transported by the current structural declaration policy,
whose clause-signature stability law is proved in the existing M4 baseline. -/
theorem after_certified :
    Certified (evidence := declarationPolicy) [] []
      (.handler (effect := Instance.user 9 []) (table := []) [] afterPlans Plan.pure) := by
  apply SourceScheduledCleanupInterfaces.Lexical.Recursive.certified_signature before_certified
  simp only [signature, actual_clause_signature]

/-- Logical family packaging selects only witnesses proved by closing each
actual clause. It is not an executable initial annotation compiler. -/
theorem same_substituted_family :
    ∃ nextPlans : ∀ owner, Plan (bodyDependencies owner),
      ∃ nextRows : ∀ owner, Rows (signature (nextPlans owner)),
        ∀ owner,
          IndexedSource registry [] (owners.insert owner ownerContract) [] [] (.ticket 9 owner)
            (Environment.empty.extend 1 .unit) afterBody .unit [owner]
            (bodyRequirements owner) (nextPlans owner) (nextRows owner) ∧
          Certified [] [] (nextPlans owner) ∧
          signature (nextPlans owner) = signature (bodyPlan owner) ∧ HEq (nextRows owner) (bodyRows owner) := by
  apply IndexedSource.substituted_family
  intro owner
  exact ⟨bodyPlan owner, bodyRows owner, after_source owner, rfl, HEq.rfl⟩

#print axioms after_source
#print axioms actual_clauses_changed
#print axioms exact_clause_closing
#print axioms complete_clause_rows_retained
#print axioms after_certified
#print axioms same_substituted_family
end Ash.OneShot.CoreCallableContractHandlerExamples
