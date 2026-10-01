import CoreCallableContractExecution

/-! Outer allowance subsumption preserves the exact installed handler residual,
private owner families, plans and complete rows. -/
namespace Ash.OneShot.CoreCallableContractAdmission
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceDependencyAnnotations (Dependencies)
open RecursiveRequirements (Requirements)
open SourcePlannedChecks (DeclarationPolicy)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open CoreCallableContractSource (Contract Environment)
section
variable [DeclarationPolicy]

set_option linter.unusedVariables false in
/-- Only the outer expression allowance grows. Handler bodies and declarations
retain their original residual, and lambda bodies retain their public requests. -/
theorem IndexedSource.allowed_weaken
    (source : IndexedSource registry outward owners world allowed scope environment code contract demand requirements plan rows)
    (larger : allowed ⊆ nextAllowed) :
    IndexedSource registry outward owners world nextAllowed scope environment code contract demand requirements plan rows := by
  induction source using IndexedSource.rec
    (motive_2 := fun _ _ _ _ _ _ _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ _ _ _ _ _ _ => True)
    generalizing nextAllowed with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference issued => exact .reference issued
  | «variable» known formed => exact .variable known formed
  | lambda body refinement bodyOutward latentBound publicCertified formed ih =>
      exact .lambda body refinement bodyOutward latentBound publicCertified formed
  | receiverLambda body bodyOutward latentBound publicCertified formed ih =>
      exact .receiverLambda body bodyOutward latentBound publicCertified formed
  | purePair left right ihL ihR => exact .purePair (ihL larger) (ihR larger)
  | pair left right ihL ihR => exact .pair (ihL larger) (ihR larger)
  | app function argument admitted publicCertified ihF ihA => exact .app (ihF larger) (ihA larger) (admitted.trans larger) publicCertified
  | bind initial body ihI ihB => exact .bind (ihI larger) (ihB larger)
  | branch condition yes no same ihC ihY ihN => exact .branch (ihC larger) (ihY larger) (ihN larger) same
  | perform known admitted operand formed ih => exact .perform known (larger admitted) (ih larger) formed
  | handler body clauses capabilities coverage unique admitted table modes declarations recipes ihBody ihDecl =>
      exact .handler body clauses capabilities coverage unique (admitted.trans larger) table modes declarations recipes
  | resume known resolved permission operand admitted formed ih =>
      exact .resume known resolved permission (ih larger) (admitted.trans larger) formed
  | discard known resolved permission unprotected admitted => exact .discard known resolved permission unprotected (admitted.trans larger)
  | typed | unavailable | available | nil | cons => trivial

set_option linter.unusedVariables false in
/-- Authentication follows the deterministic outer source transport. It never
reconstructs an installed declaration at a widened private residual. -/
theorem Authenticated.allowed_weaken
    {source : IndexedSource registry outward owners world allowed scope environment code contract demand requirements plan rows}
    (authenticated : Authenticated registry outward source lexical receiver)
    (larger : allowed ⊆ nextAllowed) :
    Authenticated registry outward (source.allowed_weaken larger) lexical receiver := by
  induction authenticated using Authenticated.rec
    (motive_2 := fun {owners world allowed scope environment code contract demand requirements dependencies plan rows} source lexical receiver _ =>
      ∀ nextAllowed, allowed ⊆ nextAllowed →
      ∀ nextSource : IndexedSource registry outward owners world nextAllowed scope environment code contract demand requirements plan rows,
      Hereditary registry outward nextSource lexical receiver)
    (motive_3 := fun {owners world allowed scope environment code answer header dependencies plan rows} source lexical receiver _ => True)
    (motive_4 := fun {owners world environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row family plans rows} source lexical receiver _ => True)
    (motive_5 := fun {owners world environment allowed requested answer clauses table families plans rows} source lexical receiver _ => True)
    generalizing nextAllowed with
  | checked current hereditary ih => exact .checked current (ih _ larger _)
  | unit => intros; exact .unit
  | boolean => intros; exact .boolean
  | integer => intros; exact .integer
  | reference => intros; exact .reference (issued := by assumption)
  | «variable» knownSupport => intros; exact .variable (known := by assumption) (formed := by assumption) knownSupport
  | purePair left right ihL ihR =>
      rename_i nextAllowed larger nextSource
      exact .purePair (ihL larger) (ihR larger)
  | pair left right ihL ihR =>
      rename_i nextAllowed larger nextSource
      exact .pair (ihL larger) (ihR larger)
  | app function argument ihF ihA =>
      rename_i nextAllowed larger nextSource
      exact .app (publicCertified := by assumption) (admitted := List.Subset.trans (by assumption) larger) (ihF larger) (ihA larger)
  | bind initial body ihI ihB =>
      rename_i nextAllowed larger nextSource
      exact .bind (ihI larger) (ihB larger)
  | branch condition yes no ihC ihY ihN =>
      rename_i nextAllowed larger nextSource
      exact .branch (sameDemand := by assumption) (ihC larger) (ihY larger) (ihN larger)
  | perform operand ih =>
      rename_i nextAllowed larger nextSource
      exact .perform (known := by assumption) (formed := by assumption) (admitted := larger (by assumption)) (ih larger)
  | resume operand ih =>
      rename_i nextAllowed larger nextSource
      exact .resume (known := by assumption) (resolved := by assumption) (permission := by assumption) (formed := by assumption) (admitted := List.Subset.trans (by assumption) larger) (ih larger)
  | discard known resolved permission unprotected admitted =>
      rename_i nextAllowed larger nextSource
      exact .discard known resolved permission unprotected (admitted.trans larger)
  | lambda refinement bodyOutward latentBound publicCertified formed known body ih =>
      intros
      exact .lambda (bodySource := by assumption) refinement bodyOutward latentBound publicCertified formed known body
  | receiverLambda bodyOutward latentBound publicCertified formed known body refinement ih =>
      intros
      exact .receiverLambda (bodySource := by assumption) bodyOutward latentBound publicCertified formed known body refinement
  | handler clauses capabilities coverage unique admitted modes recipes body declarations ihB ihD =>
      rename_i nextAllowed larger nextSource
      exact .handler clauses capabilities coverage unique (admitted.trans larger) modes recipes body declarations
  | typed | unavailable | available | nil | cons => trivial

/-- Bounds and receiver evidence are unchanged by outer allowance subsumption. -/
theorem Supported.allowed_weaken
    (supported : Supported globals outward world allowed scope environment supportEnvironment code contract demand requirements plan rows bound receiver)
    (larger : allowed ⊆ nextAllowed) :
    Supported globals outward world nextAllowed scope environment supportEnvironment code contract demand requirements plan rows bound receiver := by
  obtain ⟨lexical, empty, authenticated⟩ := supported.authentication
  exact ⟨supported.source.allowed_weaken larger, supported.support, supported.issued,
    ⟨lexical, empty, authenticated.allowed_weaken larger⟩, supported.receiverIssued⟩

#print axioms Supported.allowed_weaken
#print axioms IndexedSource.allowed_weaken
#print axioms Authenticated.allowed_weaken
end
end Ash.OneShot.CoreCallableContractAdmission

namespace Ash.OneShot.CoreCallableContractExecution
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open RecursiveRequirements (Requirements)
open SourcePlannedChecks (DeclarationPolicy)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open CoreCallableContractSource (Contract Environment)
section
variable [DeclarationPolicy]
/-- A plain frame retains its exact plan and complete rows while its outer
expression allowance grows. -/
theorem FrameSource.allowed_weaken
    (frame : FrameSource globals outward world allowed data input output parameter body demand requirements plan rows inputBound bodyBound receiver)
    (larger : allowed ⊆ nextAllowed) :
    FrameSource globals outward world nextAllowed data input output parameter body demand requirements plan rows inputBound bodyBound receiver :=
  ⟨frame.position, frame.inputAnnotation, frame.outputAnnotation, frame.inputIssued,
    frame.bodySource.allowed_weaken larger⟩
#print axioms FrameSource.allowed_weaken
end
end Ash.OneShot.CoreCallableContractExecution
