import CoreCallableAuthenticatedEnvironment
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
private def OwnerAgree (first second : Owners) (scope : Execution.Scope) :=
  ∀ binder owner, scope.resolve binder = some owner → first owner = second owner
omit evidence in
private theorem owner_none : OwnerAgree first second .none := by intro binder owner resolved; cases resolved
omit evidence in
private theorem owner_insert {first second : Owners} : OwnerAgree (first.insert owner contract) (second.insert owner contract) (.ticket binder owner) := by
  intro binder resolvedOwner resolved
  simp only [Execution.Scope.resolve] at resolved
  split at resolved
  · cases Option.some.inj resolved; simp only [Owners.insert_here]
  · cases resolved

theorem Authenticated.owners_congr
    {source : IndexedSource registry outward owners world allowed scope environment code contract demand requirements plan rows}
    (authenticated : Authenticated registry outward source lexical receiver)
    (agree : ∀ binder owner, scope.resolve binder = some owner → owners owner = destination owner)
    (nextSource : IndexedSource registry outward destination world allowed scope environment code contract demand requirements plan rows) :
    Authenticated registry outward nextSource lexical receiver := by
  induction authenticated using Authenticated.rec
    (motive_2 := fun {owners world allowed scope environment code contract demand requirements dependencies plan rows} source lexical receiver _ =>
      ∀ destination, OwnerAgree owners destination scope →
      ∀ nextSource : IndexedSource registry outward destination world allowed scope environment code contract demand requirements plan rows,
      Hereditary registry outward nextSource lexical receiver)
    (motive_3 := fun {owners world allowed scope environment code answer header dependencies plan rows} source lexical receiver _ =>
      ∀ destination, OwnerAgree owners destination scope →
      ∃ nextSource : SourceBody registry outward destination world allowed scope environment code answer header plan rows,
      BodyAuthentication registry outward nextSource lexical receiver)
    (motive_4 := fun {owners world environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row family plans rows} source lexical receiver _ =>
      ∀ destination,
      ∃ nextSource : SourceOffer registry outward destination world environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row plans rows,
      OfferAuthentication registry outward nextSource lexical receiver)
    (motive_5 := fun {owners world environment allowed requested answer clauses table families plans rows} source lexical receiver _ =>
      ∀ destination,
      ∃ nextSource : SourceDeclarations registry outward destination world environment allowed requested answer clauses table plans rows,
      DeclarationAuthentication registry outward nextSource lexical receiver)
    (motive_6 := fun {owners world environment allowed requested answer clauses table families plans rows} source lexical receiver _ =>
      ∀ destination,
      ∃ nextSource : SourceDeclarations registry outward destination world environment allowed requested answer clauses table plans rows,
      DomainDeclarationAuthentication registry outward nextSource lexical receiver)
    generalizing destination with
  | checked current hereditary ih => exact .checked current (ih destination agree nextSource)
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference => exact .reference (issued := by assumption)
  | «variable» knownSupport => exact .variable (known := by assumption) (formed := by assumption) knownSupport
  | purePair left right ihL ihR =>
      rename_i destination agree nextSource
      refine .purePair (ihL agree ?_) (ihR agree ?_)
      all_goals apply IndexedSource.owners_congr (by assumption); exact agree
  | pair left right ihL ihR =>
      rename_i destination agree nextSource
      refine .pair (ihL agree ?_) (ihR agree ?_)
      all_goals apply IndexedSource.owners_congr (by assumption); exact agree
  | app function argument ihF ihA =>
      rename_i destination agree nextSource
      refine .app (admitted := by assumption) (publicCertified := by assumption) (ihF agree ?_) (ihA agree ?_)
      all_goals apply IndexedSource.owners_congr (by assumption); exact agree
  | cleanup callback body ihF ihA =>
      rename_i destination agree nextSource
      refine .cleanup (admitted := by assumption) (publicCertified := by assumption) (ihF agree ?_) (ihA agree ?_)
      all_goals apply IndexedSource.owners_congr (by assumption); exact agree
  | resource initial body ihI ihB =>
      rename_i initialSource bodySource outwardRequirements formed effectsBound admitted hidden destination agree nextSource
      let changed := fun identity fresh => (bodySource identity fresh).owners_congr agree
      refine .resource (bodySource := changed) (formed := formed) (effectsBound := effectsBound)
        (admitted := admitted) (hidden := hidden) (ihI agree (initialSource.owners_congr agree)) ?_
      intro identity fresh
      exact ihB identity fresh agree (changed identity fresh)
  | branch condition yes no ihC ihY ihN =>
      rename_i destination agree nextSource
      refine .branch (ihC agree ?_) (ihY agree ?_) (ihN agree ?_)
      all_goals apply IndexedSource.owners_congr (by assumption); exact agree
  | perform operand ih =>
      rename_i destination agree nextSource
      refine .perform (known := by assumption) (admitted := by assumption) (formed := by assumption) (ih agree ?_)
      apply IndexedSource.owners_congr (by assumption); exact agree
  | resume operand ih =>
      rename_i destination agree nextSource
      refine .resume (known := (agree _ _ (by assumption)).symm.trans (by assumption)) (resolved := by assumption)
        (permission := by assumption) (admitted := by assumption) (formed := by assumption) (ih agree ?_)
      apply IndexedSource.owners_congr (by assumption); exact agree
  | discard known resolved permission unprotected admitted =>
      rename_i destination agree nextSource
      exact .discard ((agree _ _ resolved).symm.trans known) resolved permission unprotected admitted
  | bind initial body ihI ihB =>
      rename_i destination agree nextSource
      refine .bind (ihI agree ?_) (ihB agree ?_)
      all_goals apply IndexedSource.owners_congr (by assumption); exact agree
  | lambda refinement bodyOutward latentBound publicCertified formed known body ih =>
      rename_i environment bodySource contractDeps contractPlan contractRows destination agree nextSource
      apply Hereditary.lambda (bodySource := bodySource.owners_congr owner_none)
        refinement bodyOutward latentBound publicCertified formed known
      intro nextLexical call known received
      exact ih nextLexical call known received owner_none ((bodySource.world_weaken call.worldExtended).owners_congr owner_none)
  | receiverLambda bodyOutward latentBound publicCertified formed known body refinement ih =>
      rename_i owners world environment privateDependencies privatePlans privateRows bodySource contractDeps contractPlan contractRows destination agree nextSource
      apply Hereditary.receiverLambda (bodySource := fun lexical call => (bodySource lexical call).owners_congr owner_none)
        bodyOutward latentBound publicCertified formed known
      · intro nextLexical call known received
        exact ih nextLexical call known received owner_none ((bodySource nextLexical call).owners_congr owner_none)
      · exact refinement
  | handler clauses capabilities coverage unique admitted modes recipes body declarations ihB ihD =>
      rename_i destination agree nextSource
      obtain ⟨nextDecl, authDecl⟩ := ihD destination
      refine .handler (bodySource := ?_) clauses capabilities coverage unique admitted modes recipes ?_ authDecl
      · apply IndexedSource.owners_congr (by assumption); exact agree
      · exact ihB agree _
  | handlerDomain clauses capabilities coverage unique admitted modes recipes body declarations ihB ihD =>
      rename_i destination agree nextSource
      obtain ⟨nextDecl, authDecl⟩ := ihD destination
      refine .handlerDomain (bodySource := ?_) clauses capabilities coverage unique admitted modes recipes ?_ authDecl
      · apply IndexedSource.owners_congr (by assumption); exact agree
      · exact ihB agree _
  | typed source ih =>
      rename_i destination agree
      refine ⟨SourceBody.typed ?_ (by assumption) (by assumption), .typed (normal := by assumption) (closing := by assumption) (ih agree ?_)⟩
      all_goals apply IndexedSource.owners_congr (by assumption); exact agree
  | unavailable => exact ⟨.unavailable, .unavailable⟩
  | available resumeInterface closeInterface body ih =>
      rename_i resumeEffects closeEffects held allowed binder parameter code disposes row lexical receiver owners world environment argument input answer family plans rows bodySource destination
      let changed := fun owner contract a b c d e balanced =>
        Classical.choose (ih owner contract a b c d e balanced (destination.insert owner contract) owner_insert)
      refine ⟨SourceOffer.available resumeInterface closeInterface changed, .available (bodySource := changed) resumeInterface closeInterface ?_⟩
      intro owner contract a b c d e balanced
      exact Classical.choose_spec (ih owner contract a b c d e balanced (destination.insert owner contract) owner_insert)
  | nil => exact ⟨.nil, .nil⟩
  | domainNil => exact ⟨.nil, .domainNil⟩
  | cons known bodyBound storedReceived ordinary protectedMode rest ihO ihP ihR =>
      rename_i destination
      obtain ⟨nextOrd, authOrd⟩ := ihO destination
      obtain ⟨nextProt, authProt⟩ := ihP destination
      obtain ⟨nextRest, authRest⟩ := ihR destination
      exact ⟨.cons _ known nextOrd nextProt nextRest, .cons known bodyBound storedReceived authOrd authProt authRest⟩
  | domainCons known domainCovered formalReceived bodyBound storedReceived ordinary protectedMode rest ihO ihP ihR =>
      rename_i destination
      obtain ⟨nextOrd, authOrd⟩ := ihO destination
      obtain ⟨nextProt, authProt⟩ := ihP destination
      obtain ⟨nextRest, authRest⟩ := ihR destination
      exact ⟨.cons _ known nextOrd nextProt nextRest, .domainCons known domainCovered formalReceived bodyBound storedReceived authOrd authProt authRest⟩
set_option maxRecDepth 4000
set_option maxHeartbeats 800000
private theorem authenticated_value_allowed
    (checked : Authenticated registry outward
      (source : IndexedSource registry outward owners world allowed scope environment value contract demand requirements plan rows)
      lexical receiver)
    (isValue : value.IsValue) (next : List Instance) (nextScope : Execution.Scope) :
    Authenticated registry outward (source.value_allowed isValue next nextScope) lexical receiver := by
  cases checked with
  | checked current hereditary =>
    apply Authenticated.checked current
    cases hereditary with
    | unit => exact .unit
    | boolean => exact .boolean
    | integer => exact .integer
    | reference => exact .reference (issued := by assumption)
    | purePair left right | pair left right =>
      first | apply Hereditary.purePair | apply Hereditary.pair
      · exact authenticated_value_allowed left isValue.1 next nextScope
      · exact authenticated_value_allowed right isValue.2 next nextScope
    | lambda refinement bodyOutward latentBound publicCertified formed known body =>
      exact .lambda (bodySource := by assumption) refinement bodyOutward latentBound publicCertified formed known body
    | receiverLambda bodyOutward latentBound publicCertified formed known body refinement =>
      exact .receiverLambda bodyOutward latentBound publicCertified formed known body refinement
    | «variable» | app | bind | branch | perform | resume | discard | handler | handlerDomain | cleanup | resource => exact False.elim isValue
termination_by sizeOf value

theorem Authenticated.value_allowed
    (checked : Authenticated registry outward
      (source : IndexedSource registry outward owners world allowed scope environment value contract [] (.request [] []) .pure Rows.pure)
      lexical receiver)
    (isValue : value.IsValue) (next : List Instance) (nextScope : Execution.Scope) :
    Authenticated registry outward (source.value_allowed isValue next nextScope) lexical receiver :=
  authenticated_value_allowed checked isValue next nextScope

theorem Authenticated.value_owner_insert
    (checked : Authenticated registry outward
      (source : IndexedSource registry outward owners world allowed scope environment value contract [] (.request [] []) .pure Rows.pure)
      lexical receiver)
    (isValue : value.IsValue) (ticket : Nat) (inserted : OwnerContract) :
    Authenticated registry outward (source.value_owner_insert isValue ticket inserted) lexical receiver :=
  (checked.value_allowed isValue allowed .none).owners_congr
    (by intro binder owner resolved; cases resolved) _
end
end Ash.OneShot.CoreCallableContractAdmission
#print axioms Ash.OneShot.CoreCallableContractAdmission.Authenticated.owners_congr

#print axioms Ash.OneShot.CoreCallableContractAdmission.Authenticated.value_allowed
#print axioms Ash.OneShot.CoreCallableContractAdmission.Authenticated.value_owner_insert
