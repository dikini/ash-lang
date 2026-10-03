import CoreCallableSourceSubstitution
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
private def EnvAgree (first second : Environment) (deps : List Syntax.Dependency) :=
  ∀ name, Syntax.Dependency.variable name ∈ deps → first name = second name

omit evidence in
private theorem EnvAgree.bound {code : Code} (agree : EnvAgree environment destination (Syntax.without (.variable parameter) code.dependencies)) :
    EnvAgree (environment.extend parameter input) (destination.extend parameter input) code.dependencies := by
  intro n mem
  by_cases same : n = parameter
  · subst n; simp [Environment.extend]
  · simp only [Environment.extend, same, ↓reduceIte]
    exact agree n (Syntax.mem_without.mpr ⟨mem, by simpa using same⟩)

theorem Authenticated.environment_congr
    {source : IndexedSource registry outward owners world allowed scope environment code contract demand requirements plan rows}
    (authenticated : Authenticated registry outward source lexical receiver)
    (agree : ∀ name, Syntax.Dependency.variable name ∈ code.dependencies → environment name = destination name)
    (nextSource : IndexedSource registry outward owners world allowed scope destination code contract demand requirements plan rows) :
    Authenticated registry outward nextSource lexical receiver := by
  induction authenticated using Authenticated.rec
    (motive_2 := fun {owners world allowed scope environment code contract demand requirements dependencies plan rows} source lexical receiver _ =>
      ∀ destination, EnvAgree environment destination code.dependencies →
      ∀ nextSource : IndexedSource registry outward owners world allowed scope destination code contract demand requirements plan rows,
      Hereditary registry outward nextSource lexical receiver)
    (motive_3 := fun {owners world allowed scope environment code answer header dependencies plan rows} source lexical receiver _ =>
      ∀ destination, EnvAgree environment destination code.dependencies →
      ∃ nextSource : SourceBody registry outward owners world allowed scope destination code answer header plan rows,
      BodyAuthentication registry outward nextSource lexical receiver)
    (motive_4 := fun {owners world environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row family plans rows} source lexical receiver _ =>
      ∀ destination, EnvAgree environment destination (Syntax.without (.variable parameter) code.dependencies) →
      ∃ nextSource : SourceOffer registry outward owners world destination allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row plans rows,
      OfferAuthentication registry outward nextSource lexical receiver)
    (motive_5 := fun {owners world environment allowed requested answer clauses table families plans rows} source lexical receiver _ =>
      ∀ destination, EnvAgree environment destination clauses.dependencies →
      ∃ nextSource : SourceDeclarations registry outward owners world destination allowed requested answer clauses table plans rows,
      DeclarationAuthentication registry outward nextSource lexical receiver)
    (motive_6 := fun {owners world environment allowed requested answer clauses table families plans rows} source lexical receiver _ =>
      ∀ destination, EnvAgree environment destination clauses.dependencies →
      ∃ nextSource : SourceDeclarations registry outward owners world destination allowed requested answer clauses table plans rows,
      DomainDeclarationAuthentication registry outward nextSource lexical receiver)
    generalizing destination with
  | checked current hereditary ih => exact .checked current (ih destination agree nextSource)
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference =>
      rename_i destination agree nextSource
      exact .reference (issued := by assumption)
  | «variable» knownSupport =>
      rename_i destination agree nextSource
      exact .variable (known := (agree _ (by simp [Code.dependencies])).symm.trans (by assumption))
        (formed := by assumption) knownSupport
  | purePair left right ihL ihR =>
      rename_i destination agree nextSource
      refine .purePair (ihL (fun n mem => agree n (List.mem_append_left _ mem)) ?_) (ihR (fun n mem => agree n (List.mem_append_right _ mem)) ?_)
      · apply IndexedSource.environment_congr (by assumption); exact fun n mem => agree n (List.mem_append_left _ mem)
      · apply IndexedSource.environment_congr (by assumption); exact fun n mem => agree n (List.mem_append_right _ mem)
  | pair left right ihL ihR =>
      rename_i destination agree nextSource
      refine .pair (ihL (fun n mem => agree n (List.mem_append_left _ mem)) ?_) (ihR (fun n mem => agree n (List.mem_append_right _ mem)) ?_)
      · apply IndexedSource.environment_congr (by assumption); exact fun n mem => agree n (List.mem_append_left _ mem)
      · apply IndexedSource.environment_congr (by assumption); exact fun n mem => agree n (List.mem_append_right _ mem)
  | app function argument ihF ihA =>
      rename_i destination agree nextSource
      refine .app (admitted := by assumption) (publicCertified := by assumption) (ihF (fun n mem => agree n (List.mem_append_left _ mem)) ?_) (ihA (fun n mem => agree n (List.mem_append_right _ mem)) ?_)
      · apply IndexedSource.environment_congr (by assumption); exact fun n mem => agree n (List.mem_append_left _ mem)
      · apply IndexedSource.environment_congr (by assumption); exact fun n mem => agree n (List.mem_append_right _ mem)
  | cleanup callback body ihF ihA =>
      rename_i destination agree nextSource
      refine .cleanup (admitted := by assumption) (publicCertified := by assumption) (ihF (fun n mem => agree n (List.mem_append_left _ mem)) ?_) (ihA (fun n mem => agree n (List.mem_append_right _ mem)) ?_)
      · apply IndexedSource.environment_congr (by assumption); exact fun n mem => agree n (List.mem_append_left _ mem)
      · apply IndexedSource.environment_congr (by assumption); exact fun n mem => agree n (List.mem_append_right _ mem)
  | resource initial body ihI ihB =>
      rename_i initialSource bodySource outwardRequirements formed effectsBound admitted hidden destination agree nextSource
      let changed := fun identity fresh => (bodySource identity fresh).environment_congr (destination := destination) (by
        intro n mem
        rcases List.mem_append.mp (acquisition_dependency_bound _ identity _ mem) with old | introduced
        · exact agree n (List.mem_append_right _ old)
        · simp at introduced)
      refine .resource (bodySource := changed) (formed := formed) (effectsBound := effectsBound)
        (admitted := admitted) (hidden := hidden)
        (ihI (fun n mem => agree n (List.mem_append_left _ mem)) ?_) ?_
      · exact initialSource.environment_congr (fun n mem => agree n (List.mem_append_left _ mem))
      · intro identity fresh
        apply ihB identity fresh ?_ (changed identity fresh)
        intro n mem
        rcases List.mem_append.mp (acquisition_dependency_bound _ identity _ mem) with old | introduced
        · exact agree n (List.mem_append_right _ old)
        · simp at introduced
  | branch condition yes no ihC ihY ihN =>
      rename_i destination agree nextSource
      refine .branch (ihC (fun n mem => agree n (List.mem_append_left _ (List.mem_append_left _ mem))) ?_)
        (ihY (fun n mem => agree n (List.mem_append_left _ (List.mem_append_right _ mem))) ?_)
        (ihN (fun n mem => agree n (List.mem_append_right _ mem)) ?_)
      · apply IndexedSource.environment_congr (by assumption); exact fun n mem => agree n (List.mem_append_left _ (List.mem_append_left _ mem))
      · apply IndexedSource.environment_congr (by assumption); exact fun n mem => agree n (List.mem_append_left _ (List.mem_append_right _ mem))
      · apply IndexedSource.environment_congr (by assumption); exact fun n mem => agree n (List.mem_append_right _ mem)
  | perform operand ih =>
      rename_i destination agree nextSource
      refine .perform (known := by assumption) (admitted := by assumption) (formed := by assumption) (ih (fun n mem => agree n (List.mem_append_right _ mem)) ?_)
      apply IndexedSource.environment_congr (by assumption); exact fun n mem => agree n (List.mem_append_right _ mem)
  | resume operand ih =>
      rename_i destination agree nextSource
      refine .resume (known := by assumption) (resolved := by assumption) (permission := by assumption) (admitted := by assumption) (formed := by assumption) (ih (fun n mem => agree n (List.mem_cons_of_mem _ mem)) ?_)
      apply IndexedSource.environment_congr (by assumption); exact fun n mem => agree n (List.mem_cons_of_mem _ mem)
  | discard known resolved permission unprotected admitted => exact .discard known resolved permission unprotected admitted
  | bind initial body ihI ihB =>
      rename_i owners world allowed scope environment a input initialDemand initialReq initialDeps initialPlan initialRows parameter b output bodyDemand bodyReq bodyDeps bodyPlan bodyRows lexical receiver initialSource bodySource destination agree nextSource
      have agreeI : EnvAgree environment destination a.dependencies := fun n mem => agree n (List.mem_append_left _ mem)
      have agreeB : EnvAgree (environment.extend parameter input) (destination.extend parameter input) b.dependencies := by
        intro n mem
        by_cases same : n = parameter
        · subst n; simp [Environment.extend]
        · simp only [Environment.extend, same, ↓reduceIte]
          exact agree n (List.mem_append_right _ (Syntax.mem_without.mpr ⟨mem, by simpa using same⟩))
      exact .bind (ihI agreeI (initialSource.environment_congr agreeI)) (ihB agreeB (bodySource.environment_congr agreeB))
  | lambda refinement bodyOutward latentBound publicCertified formed known body ih =>
      rename_i environment bodySource contractDeps contractPlan contractRows destination agree nextSource
      apply Hereditary.lambda (bodySource := bodySource.environment_congr (EnvAgree.bound agree))
        refinement bodyOutward latentBound publicCertified formed known
      intro nextLexical call known received
      exact ih nextLexical call known received (EnvAgree.bound agree) ((bodySource.world_weaken call.worldExtended).environment_congr (EnvAgree.bound agree))
  | receiverLambda bodyOutward latentBound publicCertified formed known body refinement ih =>
      rename_i owners world environment privateDependencies privatePlans privateRows bodySource contractDeps contractPlan contractRows destination agree nextSource
      apply Hereditary.receiverLambda (bodySource := fun lexical call => (bodySource lexical call).environment_congr (EnvAgree.bound agree))
        bodyOutward latentBound publicCertified formed known
      · intro nextLexical call known received
        exact ih nextLexical call known received (EnvAgree.bound agree) ((bodySource nextLexical call).environment_congr (EnvAgree.bound agree))
      · exact refinement
  | handler clauses capabilities coverage unique admitted modes recipes body declarations ihB ihD =>
      rename_i destination agree nextSource
      obtain ⟨nextDecl, authDecl⟩ := ihD destination (fun n mem => agree n (List.mem_append_right _ mem))
      refine .handler (bodySource := ?_) ?_ capabilities coverage unique admitted modes recipes ?_ authDecl
      · apply IndexedSource.environment_congr (by assumption)
        exact fun n mem => agree n (List.mem_append_left _ (List.mem_append_right _ mem))
      · apply ScopedPorts.clauses_environment_congr clauses
        intro n mem
        exact congrArg (fun binding => binding.map Contract.port) (agree n (List.mem_append_right _ mem))
      · refine ihB (fun n mem => agree n (List.mem_append_left _ (List.mem_append_right _ mem))) ?_
  | handlerDomain clauses capabilities coverage unique admitted modes recipes body declarations ihB ihD =>
      rename_i destination agree nextSource
      obtain ⟨nextDecl, authDecl⟩ := ihD destination (fun n mem => agree n (List.mem_append_right _ mem))
      refine .handlerDomain (bodySource := ?_) ?_ capabilities coverage unique admitted modes recipes ?_ authDecl
      · apply IndexedSource.environment_congr (by assumption)
        exact fun n mem => agree n (List.mem_append_left _ (List.mem_append_right _ mem))
      · apply ScopedPorts.clauses_environment_congr clauses
        intro n mem
        exact congrArg (fun binding => binding.map Contract.port) (agree n (List.mem_append_right _ mem))
      · refine ihB (fun n mem => agree n (List.mem_append_left _ (List.mem_append_right _ mem))) ?_
  | typed source ih =>
      rename_i destination agree
      refine ⟨SourceBody.typed ?_ (by assumption) (by assumption), .typed (normal := by assumption) (closing := by assumption) (ih agree ?_)⟩
      all_goals apply IndexedSource.environment_congr (by assumption); exact agree
  | unavailable => exact ⟨.unavailable, .unavailable⟩
  | available resumeInterface closeInterface body ih =>
      rename_i resumeEffects closeEffects held allowed binder parameter code disposes row lexical receiver owners world environment argument input answer family plans rows bodySource destination agree
      let changed := fun owner contract a b c d e balanced =>
        Classical.choose (ih owner contract a b c d e balanced (destination.extend parameter argument) (EnvAgree.bound agree))
      refine ⟨SourceOffer.available resumeInterface closeInterface changed, .available (bodySource := changed) resumeInterface closeInterface ?_⟩
      intro owner contract a b c d e balanced
      exact Classical.choose_spec (ih owner contract a b c d e balanced (destination.extend parameter argument) (EnvAgree.bound agree))
  | nil => exact ⟨.nil, .nil⟩
  | domainNil => exact ⟨.nil, .domainNil⟩
  | cons known bodyBound storedReceived ordinary protectedMode rest ihO ihP ihR =>
      rename_i destination agree
      obtain ⟨nextOrd, authOrd⟩ := ihO destination (fun n mem => agree n (List.mem_append_left _ (Syntax.mem_without.mpr ⟨mem, by simp⟩)))
      obtain ⟨nextProt, authProt⟩ := ihP destination (fun n mem => agree n (List.mem_append_left _ (Syntax.mem_without.mpr ⟨mem, by simp⟩)))
      obtain ⟨nextRest, authRest⟩ := ihR destination (fun n mem => agree n (List.mem_append_right _ mem))
      exact ⟨.cons _ known nextOrd nextProt nextRest, .cons known bodyBound storedReceived authOrd authProt authRest⟩
  | domainCons known domainCovered formalReceived bodyBound storedReceived ordinary protectedMode rest ihO ihP ihR =>
      rename_i destination agree
      obtain ⟨nextOrd, authOrd⟩ := ihO destination (fun n mem => agree n (List.mem_append_left _ (Syntax.mem_without.mpr ⟨mem, by simp⟩)))
      obtain ⟨nextProt, authProt⟩ := ihP destination (fun n mem => agree n (List.mem_append_left _ (Syntax.mem_without.mpr ⟨mem, by simp⟩)))
      obtain ⟨nextRest, authRest⟩ := ihR destination (fun n mem => agree n (List.mem_append_right _ mem))
      exact ⟨.cons _ known nextOrd nextProt nextRest, .domainCons known domainCovered formalReceived bodyBound storedReceived authOrd authProt authRest⟩
theorem Authenticated.closed_environment
    (authenticated : Authenticated registry outward
      (source : IndexedSource registry outward owners world allowed scope environment value contract [] (.request [] []) .pure Rows.pure)
      lexical receiver)
    (closed : ClosedValue value) (destination : Environment) :
    Authenticated registry outward (source.closed_environment closed destination) lexical receiver :=
  authenticated.environment_congr
    (fun _ member => False.elim (ScopedTyping.closedValue_no_variable closed member)) _
end
end Ash.OneShot.CoreCallableContractAdmission
#print axioms Ash.OneShot.CoreCallableContractAdmission.Authenticated.environment_congr
#print axioms Ash.OneShot.CoreCallableContractAdmission.Authenticated.closed_environment
