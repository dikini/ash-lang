import CoreCallableAuthenticatedLexical
import CoreCallableAuthenticatedClosedReceiver
import CoreCallableAuthenticatedSubstitution
import CoreCallableAuthenticatedValueSummary
namespace Ash.OneShot.CoreCallableContractAdmission
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDeclarationPlans (Plan ModePlans ClausePlans)
open SourcePlanSignatures (signature clauseSignatures modeSignatures)
open SourceDependencyAnnotations (Dependencies ClauseDependencies)
open RecursiveRequirements (Requirements)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open CoreCallableContractSource (Contract Environment sequenceRows choiceRows)
open CoreCallableContractRegistries (Registry OwnerContract Owners)
open CoreCallableRootRefinement (Refines RootTransport)
open CoreCallableReceiverRefinement (CallBounds ReceiverRefines LexicalBounds)
open SourceDependencyAnnotations (RowAnnotation)
open RecursiveRequirements (Checked)
open SourceScheduledCleanupInterfaces.Lexical.Recursive (annotateDisposals)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourcePlannedChecks (Certified DeclarationPolicy)

section
variable [evidence : DeclarationPolicy]
structure Supported (globals : Globals) (outward : List Instance) (world : List Nat)
    (allowed : List Instance) (scope : Execution.Scope) (environment : Environment)
    (supportEnvironment : ScopedPorts.Support.Env) (code : Code) (contract : Contract)
    (demand : List Nat) (requirements : Requirements demand)
    {dependencies : Dependencies} (plan : Plan dependencies) (rows : Rows (signature plan))
    (bound receiver : List Nat) : Prop where
  source : Source globals outward world allowed scope environment code contract demand requirements plan rows
  support : SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.Bounds supportEnvironment code.dependencies bound
  issued : bound ⊆ world
  /-- The full actual receiver is independent of aggregate syntax support.
  Finite bindings project to the same support environment used by Bounds. -/
  authentication : ∃ lexical : LexicalBounds,
    lexical.environment = supportEnvironment ∧ Authenticated globals.registry outward source lexical receiver
  receiverIssued : receiver ⊆ world

namespace Supported
open SourceScheduledCleanupInterfaces.Lexical.Recursive
open ScopedPorts.Support (evaluate extend)
/-- Canonical actual support does not manufacture hereditary admission.
The same recursively authenticated source and finite environment are required. -/
theorem canonical (source : Source globals outward world allowed scope environment code contract demand requirements plan rows)
    (lexical : LexicalBounds) (receiver : List Nat)
    (authentication : Authenticated globals.registry outward source lexical receiver)
    (issued : evaluate lexical.environment code.dependencies ⊆ world)
    (receiverIssued : receiver ⊆ world) :
    Supported globals outward world allowed scope environment lexical.environment code contract demand requirements plan rows
      (evaluate lexical.environment code.dependencies) receiver :=
  ⟨source, SourceSupport.Bounds.canonical _ _, issued, ⟨lexical, rfl, authentication⟩, receiverIssued⟩

/-- Actual dependency support is received even when the separately stored
aggregate bound was conservative. This is the bound used for payload origins. -/
theorem actual_received
    (supported : Supported globals outward world allowed scope environment supportEnvironment code contract
      demand requirements plan rows bound receiver) :
    evaluate supportEnvironment code.dependencies ⊆ receiver := by
  obtain ⟨lexical, sameEnvironment, authenticated⟩ := supported.authentication
  rw [← sameEnvironment]
  exact SourceSupport.bounds_iff.mp authenticated.current_support

theorem substitution_reannotated
    (stable : SubstitutionPolicyStable (evidence := evidence) outward)
    (body : Supported globals outward world allowed scope (environment.extend name input)
      (extend supportEnvironment name valueBound) code output demand requirements plan rows bodyBound receiver)
    (replacement : Supported globals outward world allowed scope environment replacementEnvironment value input
      replacementDemand replacementRequirements replacementPlan replacementRows valueBound replacementReceiver)
    (closed : ClosedValue value) :
    ∃ nextPlan : Plan _, ∃ nextRows : Rows (signature nextPlan),
      Supported globals outward world allowed scope environment supportEnvironment (code.subst name value)
        output demand requirements nextPlan nextRows bodyBound receiver ∧
      nextPlan = CoreCallablePlanSubstitution.plan code plan name value ∧
      signature nextPlan = signature plan ∧ HEq nextRows rows := by
  obtain ⟨sourceLexical, sameEnvironment, authenticated⟩ := body.authentication
  let lexical := sourceLexical.extend name (supportEnvironment name)
  have newEnvironment : lexical.environment = supportEnvironment := by
    funext n
    by_cases same : n = name
    · subst n; simp [lexical, LexicalBounds.environment]
    · have old := congrFun sameEnvironment n
      simpa only [LexicalBounds.environment, lexical_lookup_extend, lexical, same, ↓reduceIte,
        ScopedPorts.Support.extend] using old
  have nameEnvironment : sourceLexical.environment name = valueBound := by
    simpa only [ScopedPorts.Support.extend, ↓reduceIte] using congrFun sameEnvironment name
  have completed : Authenticated globals.registry outward body.source
      (sourceLexical.extend name valueBound) receiver := by
    simpa only [nameEnvironment] using authenticated.complete_binding name
  have lexicalAgree : ∀ n, Syntax.Dependency.variable n ∈ code.dependencies →
      (sourceLexical.extend name valueBound).lookup n = (lexical.extend name valueBound).lookup n := by
    intro n _
    by_cases same : n = name
    · subst n; simp
    · simp only [lexical_lookup_extend, lexical, same, ↓reduceIte]
  have replacementSupport : Syntax.resourceDependencies value.dependencies ⊆ valueBound := replacement.support.resources
  have replacementAuthentication : Syntax.Dependency.variable name ∈ code.dependencies →
      Authenticated globals.registry outward (IndexedSource.value_summary replacement.source closed.1) lexical receiver := by
    intro occurs
    have boundReceived : valueBound ⊆ receiver := by
      intro identity member
      apply body.actual_received
      exact List.mem_flatMap.mpr ⟨.variable name, occurs, by simpa [extend] using member⟩
    obtain ⟨oldLexical, _same, oldAuthenticated⟩ := replacement.authentication
    apply (oldAuthenticated.value_summary closed.1).value_reauthenticate closed
    intro identity member
    have resource : identity ∈ Syntax.resourceDependencies value.dependencies := by
      obtain ⟨dependency, belongs, supported⟩ := List.mem_flatMap.mp member
      cases dependency with
      | «variable» n => exact False.elim (ScopedTyping.closedValue_no_variable closed belongs)
      | ticket n => simp at supported
      | resource n =>
        simp only [List.mem_singleton] at supported
        subst identity
        exact Syntax.mem_resourceDependencies.mpr belongs
    exact boundReceived (replacementSupport resource)
  obtain ⟨nextPlan, nextRows, nextSource, nextAuthentication, exactPlan, sameSignature, sameRows⟩ :=
    completed.substitution_reannotated_at stable environment name input value lexical valueBound rfl
      lexicalAgree (IndexedSource.value_summary replacement.source closed.1) closed replacementSupport replacementAuthentication
  refine ⟨nextPlan, nextRows, ⟨nextSource, ?_, body.issued, ⟨lexical, newEnvironment, nextAuthentication⟩, body.receiverIssued⟩,
    exactPlan, sameSignature, sameRows⟩
  apply SourceSupport.bounds_iff.mpr
  exact (ScopedPorts.Support.substitution_support_bound code name closed replacementSupport).trans
    (SourceSupport.bounds_iff.mp body.support)
end Supported
end
open SourceScheduledCleanupInterfaces.Lexical.Recursive (declarationPolicy ClauseDeclarations)
theorem Supported.substitution
    (body : Supported (evidence := declarationPolicy) globals outward world allowed scope (environment.extend name input)
      (ScopedPorts.Support.extend supportEnvironment name valueBound) code output demand requirements plan rows bodyBound receiver)
    (replacement : Supported (evidence := declarationPolicy) globals outward world allowed scope environment replacementEnvironment value input
      replacementDemand replacementRequirements replacementPlan replacementRows valueBound replacementReceiver)
    (closed : ClosedValue value) :
    ∃ nextPlan : Plan _, ∃ nextRows : Rows (signature nextPlan),
      Supported (evidence := declarationPolicy) globals outward world allowed scope environment supportEnvironment (code.subst name value)
        output demand requirements nextPlan nextRows bodyBound receiver ∧
      nextPlan = CoreCallablePlanSubstitution.plan code plan name value ∧
      signature nextPlan = signature plan ∧ HEq nextRows rows :=
  Supported.substitution_reannotated (evidence := declarationPolicy) (fun recipes same => ClauseDeclarations.signature_congr recipes same) body replacement closed
end Ash.OneShot.CoreCallableContractAdmission
#print axioms Ash.OneShot.CoreCallableContractAdmission.Supported.substitution_reannotated
#print axioms Ash.OneShot.CoreCallableContractAdmission.Supported.substitution
