import CoreCallableAuthenticatedLexical
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
def EnvironmentExtension (first second : LexicalBounds) : Prop :=
  (∀ n, first.environment n = second.environment n) ∧
  (∀ n, (∃ resources, first.lookup n = some resources) → ∃ resources, second.lookup n = some resources)
omit evidence in
private theorem EnvironmentExtension.extend (agree : EnvironmentExtension first second) :
    EnvironmentExtension (first.extend parameter resources) (second.extend parameter resources) := by
  constructor
  · intro n
    by_cases same : n = parameter
    · subst n; simp [LexicalBounds.environment]
    · simpa only [LexicalBounds.environment, lexical_lookup_extend, same, ↓reduceIte] using agree.1 n
  · intro n found
    by_cases same : n = parameter
    · subst n; exact ⟨resources, by simp⟩
    · simp only [lexical_lookup_extend, same, ↓reduceIte] at found ⊢
      exact agree.2 n found
omit evidence in
private theorem bounds_environment (bound : SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.Bounds first.environment deps receiver)
    (agree : EnvironmentExtension first second) :
    SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.Bounds second.environment deps receiver := by
  have equality : first.environment = second.environment := funext agree.1
  simpa only [← equality] using bound
omit evidence in
private theorem known_environment (known : LexicalBounds.Known first deps) (agree : EnvironmentExtension first second) :
    LexicalBounds.Known second deps := fun n mem => agree.2 n (known n mem)

theorem Authenticated.lexical_environment_congr
    (checked : Authenticated registry outward
      (source : IndexedSource registry outward owners world allowed scope environment code contract demand requirements plan rows)
      lexical receiver)
    (agree : EnvironmentExtension lexical destination) :
    Authenticated registry outward source destination receiver := by
  induction checked using Authenticated.rec
    (motive_2 := fun {owners world allowed scope environment code contract demand requirements dependencies plan rows} source lexical receiver _ =>
      ∀ destination, EnvironmentExtension lexical destination → Hereditary registry outward source destination receiver)
    (motive_3 := fun {owners world allowed scope environment code answer header dependencies plan rows} source lexical receiver _ =>
      ∀ destination, EnvironmentExtension lexical destination → BodyAuthentication registry outward source destination receiver)
    (motive_4 := fun {owners world environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row family plans rows} source lexical receiver _ =>
      ∀ destination, EnvironmentExtension lexical destination → OfferAuthentication registry outward source destination receiver)
    (motive_5 := fun {owners world environment allowed requested answer clauses table families plans rows} source lexical receiver _ =>
      ∀ destination, EnvironmentExtension lexical destination → DeclarationAuthentication registry outward source destination receiver)
    generalizing destination with
  | checked current hereditary ih => exact .checked (bounds_environment current agree) (ih destination agree)
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference => exact .reference (issued := by assumption)
  | «variable» knownSupport =>
      rename_i destination agree
      obtain ⟨resources, found⟩ := knownSupport
      exact .variable (known := by assumption) (formed := by assumption) (agree.2 _ ⟨resources, found⟩)
  | purePair left right ihL ihR =>
      rename_i destination agree
      exact .purePair (ihL agree) (ihR agree)
  | pair left right ihL ihR =>
      rename_i destination agree
      exact .pair (ihL agree) (ihR agree)
  | app function argument ihF ihA =>
      rename_i destination agree
      exact .app (admitted := by assumption) (publicCertified := by assumption)
        (ihF agree) (ihA agree)
  | cleanup callback body ihF ihA =>
      rename_i destination agree
      exact .cleanup (admitted := by assumption) (publicCertified := by assumption)
        (ihF agree) (ihA agree)
  | branch condition yes no ihC ihY ihN =>
      rename_i destination agree
      exact .branch (ihC agree)
        (ihY agree)
        (ihN agree)
  | perform operand ih =>
      rename_i destination agree
      exact .perform (known := by assumption) (admitted := by assumption) (formed := by assumption)
        (ih agree)
  | resume operand ih =>
      rename_i destination agree
      exact .resume (known := by assumption) (resolved := by assumption) (permission := by assumption)
        (admitted := by assumption) (formed := by assumption) (ih agree)
  | discard known resolved permission unprotected admitted => exact .discard known resolved permission unprotected admitted
  | bind initial body ihI ihB =>
      rename_i destination agree
      exact .bind (ihI agree)
        (ihB (EnvironmentExtension.extend agree))
  | lambda refinement bodyOutward latentBound publicCertified formed known body _ih =>
      rename_i destination agree
      exact .lambda (bodySource := by assumption) refinement bodyOutward latentBound publicCertified formed
        (known_environment known agree) body
  | receiverLambda bodyOutward latentBound publicCertified formed known body refinement _ih =>
      rename_i destination agree
      exact .receiverLambda bodyOutward latentBound publicCertified formed (known_environment known agree) body refinement
  | handler clauses capabilities coverage unique admitted modes recipes body declarations ihB ihD =>
      rename_i destination agree
      exact .handler clauses capabilities coverage unique admitted modes recipes
        (ihB agree)
        (ihD destination agree)
  | typed source ih =>
      rename_i destination agree
      exact .typed (normal := by assumption) (closing := by assumption) (ih agree)
  | unavailable => exact .unavailable
  | available resumeInterface closeInterface body ih =>
      rename_i destination agree
      exact .available resumeInterface closeInterface (fun owner contract a b c d e balanced => ih owner contract a b c d e balanced destination agree)
  | nil => exact .nil
  | cons known bodyBound storedReceived ordinary protectedMode rest ihO ihP ihR =>
      rename_i owners world environment allowed parameter binder argument input answer resumeEffects closeEffects body disposes ordinaryRow ordinaryFamilies ordinaryPlan ordinaryRows protectedRow protectedFamilies protectedPlan protectedRows requested clauses table restFamilies restPlan restRows operation supportBound receiver lexical ordinarySource protectedSource restSource destination agree
      have bodyAgree : EnvironmentExtension (lexical.extend parameter receiver) (destination.extend parameter receiver) := EnvironmentExtension.extend agree
      exact .cons known (bounds_environment bodyBound bodyAgree) storedReceived
        (ihO _ bodyAgree) (ihP _ bodyAgree) (ihR destination agree)
theorem Authenticated.complete_binding
    (checked : Authenticated registry outward
      (source : IndexedSource registry outward owners world allowed scope environment code contract demand requirements plan rows)
      lexical receiver) (name : Nat) :
    Authenticated registry outward source (lexical.extend name (lexical.environment name)) receiver := by
  apply checked.lexical_environment_congr
  constructor
  · intro n
    by_cases same : n = name
    · subst n; simp [LexicalBounds.environment]
    · simp only [LexicalBounds.environment, lexical_lookup_extend, same, ↓reduceIte]
  · intro n found
    by_cases same : n = name
    · subst n; exact ⟨lexical.environment name, by simp⟩
    · simp only [lexical_lookup_extend, same, ↓reduceIte]; exact found
end
end Ash.OneShot.CoreCallableContractAdmission
#print axioms Ash.OneShot.CoreCallableContractAdmission.Authenticated.lexical_environment_congr
#print axioms Ash.OneShot.CoreCallableContractAdmission.Authenticated.complete_binding
