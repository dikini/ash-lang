import CoreCallableSupportedSubstitution
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
def OwnerKnownMonotone (first second : Owners) : Prop :=
  ∀ owner contract, first owner = some contract → second owner = some contract
omit evidence in
theorem OwnerKnownMonotone.insert_fresh (fresh : owners owner = none) :
    OwnerKnownMonotone owners (owners.insert owner contract) := by
  intro existing allocated known
  by_cases same : existing = owner
  · subst existing; rw [fresh] at known; cases known
  · simpa [Owners.insert, same] using known
private def ScopeOwnerAgree (first second : Owners) (scope : Execution.Scope) :=
  ∀ binder owner, scope.resolve binder = some owner → first owner = second owner
omit evidence in
private theorem scope_owner_insert {first second : Owners} : ScopeOwnerAgree (first.insert owner contract) (second.insert owner contract) (.ticket binder owner) := by
  intro binder resolvedOwner resolved
  simp only [Execution.Scope.resolve] at resolved
  split at resolved
  · cases Option.some.inj resolved; simp only [Owners.insert_here]
  · cases resolved
theorem IndexedSource.owners_known_mono
    (source : IndexedSource registry outward owners world allowed scope environment code contract demand requirements plan rows)
    (agree : OwnerKnownMonotone owners destination) :
    IndexedSource registry outward destination world allowed scope environment code contract demand requirements plan rows := by
  induction source using IndexedSource.rec
      (motive_2 := fun owners world allowed scope environment code answer header _ plan rows _ =>
        ∀ destination, (∀ binder owner, scope.resolve binder = some owner → owners owner = destination owner) →
          SourceBody registry outward destination world allowed scope environment code answer header plan rows)
      (motive_3 := fun _ world environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row _ plans rows _ =>
        ∀ destination, SourceOffer registry outward destination world environment allowed parameter binder argument input answer
          resumeEffects closeEffects code held disposes row plans rows)
      (motive_4 := fun _ world environment allowed requested answer clauses table _ plans rows _ =>
        ∀ destination, SourceDeclarations registry outward destination world environment allowed requested answer clauses table plans rows)
      generalizing destination with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference issued => exact .reference issued
  | «variable» known formed => exact .variable known formed
  | lambda body refinement bodyOutward latentBound publicCertified formed ih =>
      exact .lambda (ih agree) refinement bodyOutward latentBound publicCertified formed
  | receiverLambda body bodyOutward latentBound publicCertified formed ih =>
      exact .receiverLambda (fun lexical call => ih lexical call agree)
        bodyOutward latentBound publicCertified formed
  | purePair left right ihL ihR => exact .purePair (ihL agree) (ihR agree)
  | pair left right ihL ihR => exact .pair (ihL agree) (ihR agree)
  | app function argument admitted publicCertified ihF ihA => exact .app (ihF agree) (ihA agree) admitted publicCertified
  | bind initial body ihI ihB => exact .bind (ihI agree) (ihB agree)
  | cleanup callback body admitted publicCertified ihC ihB => exact .cleanup (ihC agree) (ihB agree) admitted publicCertified
  | resource initializer body formed effectsBound admitted hidden ihI ihB =>
      exact .resource (ihI agree) (fun identity fresh => ihB identity fresh agree) formed effectsBound admitted hidden
  | branch condition yes no same ihC ihY ihN => exact .branch (ihC agree) (ihY agree) (ihN agree) same
  | perform known admitted operand formed ih => exact .perform known admitted (ih agree) formed
  | handler body clauses capabilities coverage unique admitted table modes declarations recipes ihBody ihDecl =>
      exact .handler (ihBody agree) clauses capabilities coverage unique admitted table modes (ihDecl destination) recipes
  | resume known resolved permission operand admitted formed ih =>
      exact .resume (agree _ _ known) resolved permission (ih agree) admitted formed
  | discard known resolved permission unprotected admitted =>
      exact .discard (agree _ _ known) resolved permission unprotected admitted
  | typed source normal closing ih =>
      rename_i destination agree
      exact .typed (source.owners_congr agree) normal closing
  | unavailable => exact .unavailable
  | available resumeInterface closeInterface source ih =>
      rename_i destination
      apply SourceOffer.available resumeInterface closeInterface
      intro owner contract inputSame answerSame resumeSame closeSame heldSame balanced
      apply ih owner contract inputSame answerSame resumeSame closeSame heldSame balanced
      intro binder resolvedOwner resolved
      simp only [Execution.Scope.resolve] at resolved
      split at resolved
      · cases Option.some.inj resolved
        simp only [CoreCallableContractRegistries.Owners.insert_here]
      · cases resolved
  | nil => exact .nil
  | cons supportBound known ordinary protectedMode rest ihOrd ihProt ihRest =>
      rename_i destination
      exact .cons supportBound known (ihOrd destination) (ihProt destination) (ihRest destination)


theorem BodyAuthentication.owners_congr
    (checked : BodyAuthentication registry outward
      (source : SourceBody registry outward owners world allowed scope environment code answer header plan rows) lexical receiver)
    (agree : ∀ binder owner, scope.resolve binder = some owner → owners owner = destination owner) :
    ∃ nextSource : SourceBody registry outward destination world allowed scope environment code answer header plan rows,
      BodyAuthentication registry outward nextSource lexical receiver := by
  cases checked with
  | typed authenticated =>
    rename_i bodyDemand bodyReq normal closing sourceProof
    let nextProof := sourceProof.owners_congr agree
    exact ⟨.typed nextProof normal closing,
      .typed (normal := normal) (closing := closing) (authenticated.owners_congr agree nextProof)⟩
theorem OfferAuthentication.owners_congr
    (checked : OfferAuthentication registry outward
      (source : SourceOffer registry outward owners world environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row plans rows)
      lexical receiver) (destination : Owners) :
    ∃ nextSource : SourceOffer registry outward destination world environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row plans rows,
      OfferAuthentication registry outward nextSource lexical receiver := by
  cases checked with
  | unavailable => exact ⟨.unavailable, .unavailable⟩
  | available resumeInterface closeInterface body =>
    let changed := fun owner contract a b c d e balanced =>
      Classical.choose ((body owner contract a b c d e balanced).owners_congr
        (destination := destination.insert owner contract) scope_owner_insert)
    exact ⟨.available resumeInterface closeInterface changed,
      .available (bodySource := changed) resumeInterface closeInterface
        (fun owner contract a b c d e balanced => Classical.choose_spec
          ((body owner contract a b c d e balanced).owners_congr
            (destination := destination.insert owner contract) scope_owner_insert))⟩
theorem DeclarationAuthentication.owners_congr
    (checked : DeclarationAuthentication registry outward
      (source : SourceDeclarations registry outward owners world environment allowed requested answer clauses table plans rows)
      lexical receiver) (destination : Owners) :
    ∃ nextSource : SourceDeclarations registry outward destination world environment allowed requested answer clauses table plans rows,
      DeclarationAuthentication registry outward nextSource lexical receiver := by
  induction checked using DeclarationAuthentication.rec
    (motive_1 := fun {owners world allowed scope environment code contract demand requirements dependencies plan rows} source lexical receiver _ => True)
    (motive_2 := fun {owners world allowed scope environment code contract demand requirements dependencies plan rows} source lexical receiver _ => True)
    (motive_3 := fun {owners world allowed scope environment code answer header dependencies plan rows} source lexical receiver _ => True)
    (motive_4 := fun {owners world environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row family plans rows} source lexical receiver _ => True)
    (motive_6 := fun {owners world environment allowed requested answer clauses table families plans rows} source lexical receiver _ => True)
    generalizing destination with
  | nil => exact ⟨.nil, .nil⟩
  | cons known bodyBound storedReceived ordinary protectedMode rest _ihO _ihP ihR =>
    rename_i destination
    obtain ⟨nextOrd, authOrd⟩ := ordinary.owners_congr destination
    obtain ⟨nextProt, authProt⟩ := protectedMode.owners_congr destination
    obtain ⟨nextRest, authRest⟩ := ihR destination
    exact ⟨.cons _ known nextOrd nextProt nextRest, .cons known bodyBound storedReceived authOrd authProt authRest⟩
  | checked | unit | boolean | integer | reference | «variable» | purePair | pair | app | branch | perform | resume | discard | cleanup | bind | lambda | receiverLambda | handler | handlerDomain | resource | typed | unavailable | available | domainNil | domainCons => trivial

theorem DomainDeclarationAuthentication.owners_congr
    (checked : DomainDeclarationAuthentication registry outward
      (source : SourceDeclarations registry outward owners world environment allowed requested answer clauses table plans rows)
      lexical receiver) (destination : Owners) :
    ∃ nextSource : SourceDeclarations registry outward destination world environment allowed requested answer clauses table plans rows,
      DomainDeclarationAuthentication registry outward nextSource lexical receiver := by
  induction checked using DomainDeclarationAuthentication.rec
    (motive_1 := fun {owners world allowed scope environment code contract demand requirements dependencies plan rows} source lexical receiver _ => True)
    (motive_2 := fun {owners world allowed scope environment code contract demand requirements dependencies plan rows} source lexical receiver _ => True)
    (motive_3 := fun {owners world allowed scope environment code answer header dependencies plan rows} source lexical receiver _ => True)
    (motive_4 := fun {owners world environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row family plans rows} source lexical receiver _ => True)
    (motive_5 := fun {owners world environment allowed requested answer clauses table families plans rows} source lexical receiver _ => True)
    generalizing destination with
  | domainNil => exact ⟨.nil, .domainNil⟩
  | domainCons known domainCovered formalReceived bodyBound storedReceived ordinary protectedMode rest _ihO _ihP ihR =>
    rename_i destination
    obtain ⟨nextOrd, authOrd⟩ := ordinary.owners_congr destination
    obtain ⟨nextProt, authProt⟩ := protectedMode.owners_congr destination
    obtain ⟨nextRest, authRest⟩ := ihR destination
    exact ⟨.cons _ known nextOrd nextProt nextRest, .domainCons known domainCovered formalReceived bodyBound storedReceived authOrd authProt authRest⟩
  | checked | unit | boolean | integer | reference | «variable» | purePair | pair | app | branch | perform | resume | discard | cleanup | bind | lambda | receiverLambda | handler | handlerDomain | resource | typed | unavailable | available | nil | cons => trivial

theorem Authenticated.owners_known_mono
    {source : IndexedSource registry outward owners world allowed scope environment code contract demand requirements plan rows}
    (authenticated : Authenticated registry outward source lexical receiver)
    (agree : OwnerKnownMonotone owners destination)
    (nextSource : IndexedSource registry outward destination world allowed scope environment code contract demand requirements plan rows) :
    Authenticated registry outward nextSource lexical receiver := by
  induction authenticated using Authenticated.rec
    (motive_2 := fun {owners world allowed scope environment code contract demand requirements dependencies plan rows} source lexical receiver _ =>
      ∀ destination, OwnerKnownMonotone owners destination →
      ∀ nextSource : IndexedSource registry outward destination world allowed scope environment code contract demand requirements plan rows,
      Hereditary registry outward nextSource lexical receiver)
    (motive_3 := fun {owners world allowed scope environment code answer header dependencies plan rows} source lexical receiver _ => True)
    (motive_4 := fun {owners world environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row family plans rows} source lexical receiver _ => True)
    (motive_5 := fun {owners world environment allowed requested answer clauses table families plans rows} source lexical receiver _ => True)
    (motive_6 := fun {owners world environment allowed requested answer clauses table families plans rows} source lexical receiver _ => True)
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
      all_goals apply IndexedSource.owners_known_mono (by assumption); exact agree
  | pair left right ihL ihR =>
      rename_i destination agree nextSource
      refine .pair (ihL agree ?_) (ihR agree ?_)
      all_goals apply IndexedSource.owners_known_mono (by assumption); exact agree
  | cleanup callback body ihC ihB =>
      rename_i destination agree nextSource
      refine .cleanup (admitted := by assumption) (publicCertified := by assumption) (ihC agree ?_) (ihB agree ?_)
      all_goals apply IndexedSource.owners_known_mono (by assumption); exact agree
  | app function argument ihF ihA =>
      rename_i destination agree nextSource
      refine .app (admitted := by assumption) (publicCertified := by assumption) (ihF agree ?_) (ihA agree ?_)
      all_goals apply IndexedSource.owners_known_mono (by assumption); exact agree
  | resource initial body ihI ihB =>
      rename_i initialSource bodySource outwardRequirements formed effectsBound admitted hidden destination agree nextSource
      let changed := fun identity fresh => (bodySource identity fresh).owners_known_mono agree
      refine .resource (bodySource := changed) (formed := formed) (effectsBound := effectsBound)
        (admitted := admitted) (hidden := hidden) (ihI agree (initialSource.owners_known_mono agree)) ?_
      intro identity fresh
      exact ihB identity fresh agree (changed identity fresh)
  | branch condition yes no ihC ihY ihN =>
      rename_i destination agree nextSource
      refine .branch (ihC agree ?_) (ihY agree ?_) (ihN agree ?_)
      all_goals apply IndexedSource.owners_known_mono (by assumption); exact agree
  | perform operand ih =>
      rename_i destination agree nextSource
      refine .perform (known := by assumption) (admitted := by assumption) (formed := by assumption) (ih agree ?_)
      apply IndexedSource.owners_known_mono (by assumption); exact agree
  | resume operand ih =>
      rename_i destination agree nextSource
      refine .resume (known := agree _ _ (by assumption)) (resolved := by assumption)
        (permission := by assumption) (admitted := by assumption) (formed := by assumption) (ih agree ?_)
      apply IndexedSource.owners_known_mono (by assumption); exact agree
  | discard known resolved permission unprotected admitted =>
      rename_i destination agree nextSource
      exact .discard (agree _ _ known) resolved permission unprotected admitted
  | bind initial body ihI ihB =>
      rename_i destination agree nextSource
      refine .bind (ihI agree ?_) (ihB agree ?_)
      all_goals apply IndexedSource.owners_known_mono (by assumption); exact agree
  | lambda refinement bodyOutward latentBound publicCertified formed known body ih =>
      rename_i environment bodySource contractDeps contractPlan contractRows destination agree nextSource
      apply Hereditary.lambda (bodySource := bodySource.owners_known_mono agree)
        refinement bodyOutward latentBound publicCertified formed known
      intro nextLexical call known received
      exact ih nextLexical call known received agree ((bodySource.world_weaken call.worldExtended).owners_known_mono agree)
  | receiverLambda bodyOutward latentBound publicCertified formed known body refinement ih =>
      rename_i owners world environment privateDependencies privatePlans privateRows bodySource contractDeps contractPlan contractRows destination agree nextSource
      apply Hereditary.receiverLambda (bodySource := fun lexical call => (bodySource lexical call).owners_known_mono agree)
        bodyOutward latentBound publicCertified formed known
      · intro nextLexical call known received
        exact ih nextLexical call known received agree ((bodySource nextLexical call).owners_known_mono agree)
      · exact refinement
  | handler clauses capabilities coverage unique admitted modes recipes body declarations ihB _ihD =>
      rename_i destination agree nextSource
      obtain ⟨nextDecl, authDecl⟩ := declarations.owners_congr destination
      refine .handler (bodySource := ?_) clauses capabilities coverage unique admitted modes recipes ?_ authDecl
      · apply IndexedSource.owners_known_mono (by assumption); exact agree
      · exact ihB agree _
  | handlerDomain clauses capabilities coverage unique admitted modes recipes body declarations ihB _ihD =>
      rename_i destination agree nextSource
      obtain ⟨nextDecl, authDecl⟩ := declarations.owners_congr destination
      refine .handlerDomain (bodySource := ?_) clauses capabilities coverage unique admitted modes recipes ?_ authDecl
      · apply IndexedSource.owners_known_mono (by assumption); exact agree
      · exact ihB agree _
  | typed | unavailable | available | nil | cons | domainNil | domainCons => trivial
def Globals.withOwners (globals : Globals) (owners : Owners) : Globals := {globals with owners := owners}
theorem Supported.owners_known_mono
    (supported : Supported globals outward world allowed scope environment supportEnvironment code contract demand requirements plan rows bound receiver)
    (agree : OwnerKnownMonotone globals.owners destination) :
    Supported (globals.withOwners destination) outward world allowed scope environment supportEnvironment code contract demand requirements plan rows bound receiver := by
  obtain ⟨lexical, sameEnvironment, authenticated⟩ := supported.authentication
  let source := IndexedSource.owners_known_mono supported.source agree
  exact ⟨source, supported.support, supported.issued,
    ⟨lexical, sameEnvironment, authenticated.owners_known_mono agree source⟩, supported.receiverIssued⟩
end
end Ash.OneShot.CoreCallableContractAdmission
#print axioms Ash.OneShot.CoreCallableContractAdmission.IndexedSource.owners_known_mono
#print axioms Ash.OneShot.CoreCallableContractAdmission.Authenticated.owners_known_mono
#print axioms Ash.OneShot.CoreCallableContractAdmission.DeclarationAuthentication.owners_congr

#print axioms Ash.OneShot.CoreCallableContractAdmission.Supported.owners_known_mono

#print axioms Ash.OneShot.CoreCallableContractAdmission.DomainDeclarationAuthentication.owners_congr
