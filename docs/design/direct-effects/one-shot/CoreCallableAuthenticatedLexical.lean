import CoreCallableSubstitutionSupport
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
private def LexicalAgree (first second : LexicalBounds) (deps : List Syntax.Dependency) :=
  ∀ name, Syntax.Dependency.variable name ∈ deps → first.lookup name = second.lookup name
omit evidence in
private theorem LexicalAgree.environment (agree : LexicalAgree first second deps) :
    ∀ name, Syntax.Dependency.variable name ∈ deps → first.environment name = second.environment name :=
  fun n mem => congrArg (fun entry : Option (List Nat) => entry.getD []) (agree n mem)
omit evidence in
private theorem LexicalAgree.extend {first second : LexicalBounds} {code : Code}
    (agree : LexicalAgree first second (Syntax.without (.variable parameter) code.dependencies)) :
    LexicalAgree (first.extend parameter resources) (second.extend parameter resources) code.dependencies := by
  intro n mem
  by_cases same : n = parameter
  · subst n; simp
  · simp only [lexical_lookup_extend, same, ↓reduceIte]
    exact agree n (Syntax.mem_without.mpr ⟨mem, by simpa using same⟩)
omit evidence in
private theorem bounds_lexical (bound : SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.Bounds first.environment deps receiver)
    (agree : LexicalAgree first second deps) :
    SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.Bounds second.environment deps receiver := by
  apply SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.bounds_iff.mpr
  rw [← ScopedPorts.Support.evaluation_congr agree.environment]
  exact SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.bounds_iff.mp bound
omit evidence in
private theorem known_lexical (known : LexicalBounds.Known first deps) (agree : LexicalAgree first second deps) :
    LexicalBounds.Known second deps := by
  intro n mem
  obtain ⟨resources, found⟩ := known n mem
  exact ⟨resources, (agree n mem).symm.trans found⟩

theorem Authenticated.lexical_congr
    (checked : Authenticated registry outward
      (source : IndexedSource registry outward owners world allowed scope environment code contract demand requirements plan rows)
      lexical receiver)
    (agree : ∀ n, Syntax.Dependency.variable n ∈ code.dependencies → lexical.lookup n = destination.lookup n) :
    Authenticated registry outward source destination receiver := by
  induction checked using Authenticated.rec
    (motive_2 := fun {owners world allowed scope environment code contract demand requirements dependencies plan rows} source lexical receiver _ =>
      ∀ destination, LexicalAgree lexical destination code.dependencies → Hereditary registry outward source destination receiver)
    (motive_3 := fun {owners world allowed scope environment code answer header dependencies plan rows} source lexical receiver _ =>
      ∀ destination, LexicalAgree lexical destination code.dependencies → BodyAuthentication registry outward source destination receiver)
    (motive_4 := fun {owners world environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row family plans rows} source lexical receiver _ =>
      ∀ destination, LexicalAgree lexical destination code.dependencies → OfferAuthentication registry outward source destination receiver)
    (motive_5 := fun {owners world environment allowed requested answer clauses table families plans rows} source lexical receiver _ =>
      ∀ destination, LexicalAgree lexical destination clauses.dependencies → DeclarationAuthentication registry outward source destination receiver)
    generalizing destination with
  | checked current hereditary ih => exact .checked (bounds_lexical current agree) (ih destination agree)
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference => exact .reference (issued := by assumption)
  | «variable» knownSupport =>
      rename_i destination agree
      obtain ⟨resources, found⟩ := knownSupport
      exact .variable (known := by assumption) (formed := by assumption) ⟨resources, (agree _ (by simp [Code.dependencies])).symm.trans found⟩
  | purePair left right ihL ihR =>
      rename_i destination agree
      exact .purePair (ihL (fun n mem => agree n (List.mem_append_left _ mem))) (ihR (fun n mem => agree n (List.mem_append_right _ mem)))
  | pair left right ihL ihR =>
      rename_i destination agree
      exact .pair (ihL (fun n mem => agree n (List.mem_append_left _ mem))) (ihR (fun n mem => agree n (List.mem_append_right _ mem)))
  | app function argument ihF ihA =>
      rename_i destination agree
      exact .app (admitted := by assumption) (publicCertified := by assumption)
        (ihF (fun n mem => agree n (List.mem_append_left _ mem))) (ihA (fun n mem => agree n (List.mem_append_right _ mem)))
  | branch condition yes no ihC ihY ihN =>
      rename_i destination agree
      exact .branch (ihC (fun n mem => agree n (List.mem_append_left _ (List.mem_append_left _ mem))))
        (ihY (fun n mem => agree n (List.mem_append_left _ (List.mem_append_right _ mem))))
        (ihN (fun n mem => agree n (List.mem_append_right _ mem)))
  | perform operand ih =>
      rename_i destination agree
      exact .perform (known := by assumption) (admitted := by assumption) (formed := by assumption)
        (ih (fun n mem => agree n (List.mem_append_right _ mem)))
  | resume operand ih =>
      rename_i destination agree
      exact .resume (known := by assumption) (resolved := by assumption) (permission := by assumption)
        (admitted := by assumption) (formed := by assumption) (ih (fun n mem => agree n (List.mem_cons_of_mem _ mem)))
  | discard known resolved permission unprotected admitted => exact .discard known resolved permission unprotected admitted
  | bind initial body ihI ihB =>
      rename_i destination agree
      exact .bind (ihI (fun n mem => agree n (List.mem_append_left _ mem)))
        (ihB (LexicalAgree.extend (fun n mem => agree n (List.mem_append_right _ mem))))
  | lambda refinement bodyOutward latentBound publicCertified formed known body _ih =>
      rename_i destination agree
      exact .lambda (bodySource := by assumption) refinement bodyOutward latentBound publicCertified formed
        (known_lexical known agree) body
  | receiverLambda bodyOutward latentBound publicCertified formed known body refinement _ih =>
      rename_i destination agree
      exact .receiverLambda bodyOutward latentBound publicCertified formed (known_lexical known agree) body refinement
  | handler clauses capabilities coverage unique admitted modes recipes body declarations ihB ihD =>
      rename_i destination agree
      exact .handler clauses capabilities coverage unique admitted modes recipes
        (ihB (fun n mem => agree n (List.mem_append_left _ (List.mem_append_right _ mem))))
        (ihD destination (fun n mem => agree n (List.mem_append_right _ mem)))
  | typed source ih =>
      rename_i destination agree
      exact .typed (normal := by assumption) (closing := by assumption) (ih agree)
  | unavailable => exact .unavailable
  | available resumeInterface closeInterface body ih =>
      rename_i destination agree
      exact .available resumeInterface closeInterface (fun owner contract a b c d e balanced => ih owner contract a b c d e balanced destination agree)
  | nil => exact .nil
  | cons known bodyBound storedReceived ordinary protectedMode rest ihO ihP ihR =>
      rename_i receiver lexical ordinarySource protectedSource restSource destination agree
      have bodyAgree := LexicalAgree.extend (resources := receiver) (fun n mem => agree n (List.mem_append_left _ (Syntax.mem_without.mpr ⟨mem, by simp⟩)))
      exact .cons known (bounds_lexical bodyBound bodyAgree) storedReceived
        (ihO _ bodyAgree) (ihP _ bodyAgree) (ihR destination (fun n mem => agree n (List.mem_append_right _ mem)))
end
end Ash.OneShot.CoreCallableContractAdmission
#print axioms Ash.OneShot.CoreCallableContractAdmission.Authenticated.lexical_congr
