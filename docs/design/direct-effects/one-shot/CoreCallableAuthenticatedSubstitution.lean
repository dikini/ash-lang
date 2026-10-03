import CoreCallableAuthenticatedLexical
import CoreCallableAuthenticatedClosedReceiver
import CoreCallableAuthenticatedLambdaSubstitution
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
set_option maxRecDepth 4000
set_option maxHeartbeats 800000
omit evidence in
private theorem sequence_rows_heq
    {first nextFirst : SourcePlanSignatures.Signature firstDependencies}
    {second nextSecond : SourcePlanSignatures.Signature secondDependencies}
    {left : Rows first} {nextLeft : Rows nextFirst} {right : Rows second} {nextRight : Rows nextSecond}
    (sameLeft : nextFirst = first) (sameRight : nextSecond = second)
    (alignedLeft : HEq nextLeft left) (alignedRight : HEq nextRight right) :
    HEq (Rows.sequence nextLeft nextRight) (Rows.sequence left right) := by
  cases sameLeft
  cases sameRight
  cases eq_of_heq alignedLeft
  cases eq_of_heq alignedRight
  rfl

omit evidence in
private theorem cleanup_rows_heq
    {callback : SourcePlanSignatures.Signature callbackDependencies}
    {body nextBody : SourcePlanSignatures.Signature bodyDependencies}
    {callbackRows : Rows callback} {bodyRows : Rows body} {nextBodyRows : Rows nextBody}
    (same : nextBody = body) (aligned : HEq nextBodyRows bodyRows) :
    HEq (Rows.cleanup (needs := needs) latent callbackRows nextBodyRows)
      (Rows.cleanup (needs := needs) latent callbackRows bodyRows) := by
  cases same
  cases eq_of_heq aligned
  rfl

omit evidence in
private theorem choice_rows_heq
    {first nextFirst : SourcePlanSignatures.Signature firstDependencies}
    {second nextSecond : SourcePlanSignatures.Signature secondDependencies}
    {left : Rows first} {nextLeft : Rows nextFirst} {right : Rows second} {nextRight : Rows nextSecond}
    (sameLeft : nextFirst = first) (sameRight : nextSecond = second)
    (alignedLeft : HEq nextLeft left) (alignedRight : HEq nextRight right) :
    HEq (Rows.choice nextLeft nextRight) (Rows.choice left right) := by
  cases sameLeft
  cases sameRight
  cases eq_of_heq alignedLeft
  cases eq_of_heq alignedRight
  rfl

omit evidence in
private theorem refines_rows_heq
    {first nextFirst : SourcePlanSignatures.Signature dependencies}
    {firstRows : Rows first} {nextRows : Rows nextFirst}
    (refinement : Refines contractRows firstRows) (same : nextFirst = first)
    (aligned : HEq nextRows firstRows) : Refines contractRows nextRows := by
  cases same
  cases eq_of_heq aligned
  exact refinement
omit evidence in
private theorem signature_sequence_same
    {first nextFirst : SourcePlanSignatures.Signature firstDependencies}
    {second nextSecond : SourcePlanSignatures.Signature secondDependencies}
    (sameLeft : nextFirst = first) (sameRight : nextSecond = second) :
    SourcePlanSignatures.Signature.sequence nextFirst nextSecond = .sequence first second := by
  cases sameLeft
  cases sameRight
  rfl
omit evidence in
private theorem signature_choice_same
    {first nextFirst : SourcePlanSignatures.Signature firstDependencies}
    {second nextSecond : SourcePlanSignatures.Signature secondDependencies}
    (sameLeft : nextFirst = first) (sameRight : nextSecond = second) :
    SourcePlanSignatures.Signature.choice nextFirst nextSecond = .choice first second := by
  cases sameLeft
  cases sameRight
  rfl
omit evidence in
private theorem rows_cast_heq {first second : SourcePlanSignatures.Signature dependencies}
    (same : first = second) (rows : Rows second) : HEq (same.symm ▸ rows) rows := by
  cases same
  rfl

omit evidence in
private theorem transport_heq {α β : Sort u} (same : α = β) (value : β) : HEq (same.mpr value) value := by
  cases same; rfl

omit evidence in
private theorem resource_rows_heq
    {family : Nat → Dependencies}
    {first second : ∀ identity, SourcePlanSignatures.Signature (family identity)}
    {firstRows : ∀ identity, Rows (first identity)} {secondRows : ∀ identity, Rows (second identity)}
    (same : ∀ identity, first identity = second identity)
    (aligned : ∀ identity, HEq (firstRows identity) (secondRows identity)) :
    HEq (Rows.resource firstRows) (Rows.resource secondRows) := by
  have sameFunctions : first = second := funext same
  cases sameFunctions
  have sameRows : firstRows = secondRows := funext (fun identity => eq_of_heq (aligned identity))
  cases sameRows
  rfl

omit evidence in
private theorem available_rows_heq
    {family : Nat → Dependencies}
    {first second : ∀ owner, SourcePlanSignatures.Signature (family owner)}
    {firstRows : ∀ owner, Rows (first owner)} {secondRows : ∀ owner, Rows (second owner)}
    (same : ∀ owner, first owner = second owner)
    (aligned : ∀ owner, HEq (firstRows owner) (secondRows owner)) :
    HEq (ModeRows.available firstRows) (ModeRows.available secondRows) := by
  have sameFunctions : first = second := funext same
  cases sameFunctions
  have sameRows : firstRows = secondRows := funext (fun owner => eq_of_heq (aligned owner))
  cases sameRows
  rfl

omit evidence in
private theorem declaration_cons_heq
    {ordinary nextOrdinary : SourcePlanSignatures.ModeSignatures ordinaryFamily}
    {protectedMode nextProtected : SourcePlanSignatures.ModeSignatures protectedFamily}
    {rest nextRest : SourcePlanSignatures.ClauseSignatures restFamily}
    {ordinaryRows : ModeRows ordinary} {nextOrdinaryRows : ModeRows nextOrdinary}
    {protectedRows : ModeRows protectedMode} {nextProtectedRows : ModeRows nextProtected}
    {restRows : ClauseRows rest} {nextRestRows : ClauseRows nextRest}
    (sameOrdinary : nextOrdinary = ordinary) (sameProtected : nextProtected = protectedMode)
    (sameRest : nextRest = rest) (sameRights : nextRights = rights)
    (alignedOrdinary : HEq nextOrdinaryRows ordinaryRows) (alignedProtected : HEq nextProtectedRows protectedRows)
    (alignedRest : HEq nextRestRows restRows) :
    HEq (ClauseRows.cons (operation := operation) (rights := nextRights) nextOrdinaryRows nextProtectedRows nextRestRows supportBound)
      (ClauseRows.cons (operation := operation) (rights := rights) ordinaryRows protectedRows restRows supportBound) := by
  cases sameOrdinary
  cases sameProtected
  cases sameRest
  cases sameRights
  cases eq_of_heq alignedOrdinary
  cases eq_of_heq alignedProtected
  cases eq_of_heq alignedRest
  rfl

omit evidence in
private theorem handler_rows_heq
    {first nextFirst : SourcePlanSignatures.ClauseSignatures families}
    {body nextBody : SourcePlanSignatures.Signature dependencies}
    {declarations : ClauseRows first} {nextDeclarations : ClauseRows nextFirst}
    {bodyRows : Rows body} {nextBodyRows : Rows nextBody}
    (sameDeclarations : nextFirst = first) (sameBody : nextBody = body)
    (alignedDeclarations : HEq nextDeclarations declarations) (alignedBody : HEq nextBodyRows bodyRows) :
    HEq (Rows.handler (effect := effect) (table := table) (required := required) nextDeclarations nextBodyRows)
      (Rows.handler (effect := effect) (table := table) (required := required) declarations bodyRows) := by
  cases sameDeclarations
  cases sameBody
  cases eq_of_heq alignedDeclarations
  cases eq_of_heq alignedBody
  rfl

omit evidence in
private theorem signature_handler_same
    {first nextFirst : SourcePlanSignatures.ClauseSignatures families}
    {body nextBody : SourcePlanSignatures.Signature dependencies}
    (sameDeclarations : nextFirst = first) (sameBody : nextBody = body) :
    SourcePlanSignatures.Signature.handler (effect := effect) (table := table) required nextFirst nextBody =
      SourcePlanSignatures.Signature.handler (effect := effect) (table := table) required first body := by
  cases sameDeclarations
  cases sameBody
  rfl
omit evidence in
private theorem signature_declaration_cons_same
    {ordinary nextOrdinary : SourcePlanSignatures.ModeSignatures ordinaryFamily}
    {protectedMode nextProtected : SourcePlanSignatures.ModeSignatures protectedFamily}
    {rest nextRest : SourcePlanSignatures.ClauseSignatures restFamily}
    (sameOrdinary : nextOrdinary = ordinary) (sameProtected : nextProtected = protectedMode)
    (sameRest : nextRest = rest) (sameRights : nextRights = rights) :
    SourcePlanSignatures.ClauseSignatures.cons (operation := operation) nextRights nextOrdinary nextProtected nextRest =
      SourcePlanSignatures.ClauseSignatures.cons (operation := operation) rights ordinary protectedMode rest := by
  cases sameOrdinary
  cases sameProtected
  cases sameRest
  cases sameRights
  rfl
omit evidence in
private theorem evaluated_lookup_congr {first second : LexicalBounds}
    (agree : ∀ n, Syntax.Dependency.variable n ∈ deps → first.lookup n = second.lookup n) :
    ScopedPorts.Support.evaluate first.environment deps = ScopedPorts.Support.evaluate second.environment deps :=
  ScopedPorts.Support.evaluation_congr (fun n mem => congrArg (fun entry : Option (List Nat) => entry.getD []) (agree n mem))

def SubstitutionPolicyStable (outward : List Instance) := ∀ {before after families required}
      {first : ClausePlans before families} {second : ClausePlans after families},
      evidence.accepts outward required first → clauseSignatures first = clauseSignatures second →
      evidence.accepts outward required second

private theorem IndexedSource.usage_for_substitution
    (source : IndexedSource registry outward owners world allowed scope environment code contract demand requirements plan rows)
    (empty : scope = .none) : ScopedExpressions.Uses registry.policy .none .available code .available := by
  induction source using IndexedSource.rec
      (motive_2 := fun _ _ _ _ _ _ _ _ _ _ _ _ => True)
      (motive_3 := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True)
      (motive_4 := fun _ _ _ _ _ _ _ _ _ _ _ _ => True) with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference => exact .resourceRef
  | «variable» => exact .variable
  | lambda body refinement bodyOutward latentBound publicCertified formed ih => exact .lambda (ih rfl)
  | receiverLambda body bodyOutward latentBound publicCertified formed ih => exact .lambda (ih [] (CallBounds.current _) rfl)
  | purePair left right ihL ihR | pair left right ihL ihR => exact .pair (ihL empty) (ihR empty)
  | app function argument admitted publicCertified ihF ihA => exact .app (ihF empty) (ihA empty)
  | bind initial body ihI ihB => exact .bind (ihI empty) (ihB empty)
  | cleanup callback body admitted publicCertified ihC ihB => exact .cleanup (ihC empty) (ihB empty)
  | resource initializer body formed effectsBound admitted hidden ihI ihB =>
      obtain ⟨identity, fresh⟩ := ScopedTyping.fresh_world_name _
      exact .resource (ihI empty) ((instantiation_preserves_usage_iff _ _).mp (ihB identity fresh empty))
  | branch condition yes no same ihC ihY ihN => exact .branch (ihC empty) (ihY empty) (ihN empty)
  | perform known admitted operand formed ih => exact .perform (ih empty)
  | handler body clauses capabilities coverage unique admitted table modes declarations recipes ihBody ihDecl => exact .handle (ihBody empty) capabilities
  | resume known resolved permission operand admitted formed ih => subst_vars; cases resolved
  | discard known resolved permission unprotected admitted => subst_vars; cases resolved
  | typed | unavailable | available | nil | cons => trivial
private theorem BodyAuthentication.transport
    (checked : BodyAuthentication registry outward
      (source : SourceBody registry outward owners world allowed scope sourceEnvironment code answer header plan rows) sourceLexical receiver)
    (environmentAgree : ∀ n, Syntax.Dependency.variable n ∈ code.dependencies → sourceEnvironment n = destination n)
    (lexicalAgree : ∀ n, Syntax.Dependency.variable n ∈ code.dependencies → sourceLexical.lookup n = nextLexical.lookup n) :
    ∃ nextSource : SourceBody registry outward owners world allowed scope destination code answer header plan rows,
      BodyAuthentication registry outward nextSource nextLexical receiver := by
  cases checked with
  | typed authenticated =>
    rename_i bodyDemand bodyReq normal closing sourceProof
    let nextProof := sourceProof.environment_congr environmentAgree
    exact ⟨.typed nextProof normal closing, .typed (normal := normal) (closing := closing)
      ((authenticated.environment_congr environmentAgree nextProof).lexical_congr lexicalAgree)⟩

theorem Authenticated.substitution_reannotated_at
    (stable : SubstitutionPolicyStable outward)
    {source : IndexedSource registry outward owners world allowed scope sourceEnvironment code result demand requirements plan rows}
    (checked : Authenticated registry outward source sourceLexical receiver) :
    ∀ environment name input value lexical valueBound,
      sourceEnvironment = environment.extend name input → (∀ n, Syntax.Dependency.variable n ∈ code.dependencies → sourceLexical.lookup n = (lexical.extend name valueBound).lookup n) →
      (replacement : IndexedSource registry outward owners world allowed scope environment value input [] (.request [] []) .pure Rows.pure) →
      ClosedValue value → Syntax.resourceDependencies value.dependencies ⊆ valueBound →
      (Syntax.Dependency.variable name ∈ code.dependencies → Authenticated registry outward replacement lexical receiver) →
      ∃ nextPlan : Plan _, ∃ nextRows : Rows (signature nextPlan),
        ∃ nextSource : IndexedSource registry outward owners world allowed scope environment (code.subst name value) result demand requirements nextPlan nextRows,
        Authenticated registry outward nextSource lexical receiver ∧
        nextPlan = CoreCallablePlanSubstitution.plan code plan name value ∧ signature nextPlan = signature plan ∧ HEq nextRows rows := by
  induction checked using Authenticated.rec
    (motive_2 := fun {owners world allowed scope sourceEnvironment code result demand requirements dependencies plan rows} source sourceLexical receiver _ =>
      ∀ environment name input value lexical valueBound,
      sourceEnvironment = environment.extend name input → (∀ n, Syntax.Dependency.variable n ∈ code.dependencies → sourceLexical.lookup n = (lexical.extend name valueBound).lookup n) →
      (replacement : IndexedSource registry outward owners world allowed scope environment value input [] (.request [] []) .pure Rows.pure) →
      ClosedValue value → Syntax.resourceDependencies value.dependencies ⊆ valueBound →
      (Syntax.Dependency.variable name ∈ code.dependencies → Authenticated registry outward replacement lexical receiver) →
      ∃ nextPlan : Plan dependencies, ∃ nextRows : Rows (signature nextPlan),
        ∃ nextSource : IndexedSource registry outward owners world allowed scope environment (code.subst name value) result demand requirements nextPlan nextRows,
        Hereditary registry outward nextSource lexical receiver ∧
        nextPlan = CoreCallablePlanSubstitution.plan code plan name value ∧ signature nextPlan = signature plan ∧ HEq nextRows rows)
    (motive_3 := fun {owners world allowed scope sourceEnvironment code answer header dependencies plan rows} source sourceLexical receiver _ =>
      ∀ environment name input value lexical valueBound,
      sourceEnvironment = environment.extend name input → (∀ n, Syntax.Dependency.variable n ∈ code.dependencies → sourceLexical.lookup n = (lexical.extend name valueBound).lookup n) →
      (replacement : IndexedSource registry outward owners world allowed scope environment value input [] (.request [] []) .pure Rows.pure) →
      ClosedValue value → Syntax.resourceDependencies value.dependencies ⊆ valueBound →
      (Syntax.Dependency.variable name ∈ code.dependencies → Authenticated registry outward replacement lexical receiver) →
      ∃ nextPlan : Plan dependencies, ∃ nextRows : Rows (signature nextPlan),
        ∃ nextSource : SourceBody registry outward owners world allowed scope environment (code.subst name value) answer header nextPlan nextRows,
        BodyAuthentication registry outward nextSource lexical receiver ∧
        nextPlan = CoreCallablePlanSubstitution.plan code plan name value ∧ signature nextPlan = signature plan ∧ HEq nextRows rows)
    (motive_4 := fun {owners world sourceEnvironment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row family plans rows} source sourceLexical receiver _ =>
      ∀ formalSupport environment name replacementType value lexical valueBound,
      sourceEnvironment = environment.extend name replacementType → (∀ n, Syntax.Dependency.variable n ∈ code.dependencies → sourceLexical.lookup n = ((lexical.extend name valueBound).extend parameter formalSupport).lookup n) →
      (replacement : IndexedSource registry outward owners world allowed .none environment value replacementType [] (.request [] []) .pure Rows.pure) →
      ClosedValue value → Syntax.resourceDependencies value.dependencies ⊆ valueBound →
      (Syntax.Dependency.variable name ∈ Syntax.without (.variable parameter) code.dependencies → Authenticated registry outward replacement lexical receiver) →
      ∃ nextPlans : ModePlans family, ∃ nextRows : ModeRows (modeSignatures nextPlans),
        ∃ nextSource : SourceOffer registry outward owners world environment allowed parameter binder argument input answer resumeEffects closeEffects
          (if name = parameter then code else code.subst name value) held disposes row nextPlans nextRows,
        OfferAuthentication registry outward nextSource (lexical.extend parameter formalSupport) receiver ∧
        nextPlans = (if name = parameter then plans else CoreCallablePlanSubstitution.modes code plans name value) ∧ modeSignatures nextPlans = modeSignatures plans ∧ HEq nextRows rows)
    (motive_5 := fun {owners world sourceEnvironment allowed requested answer clauses table families plans rows} source sourceLexical receiver _ =>
      ∀ environment name input value lexical valueBound,
      sourceEnvironment = environment.extend name input → (∀ n, Syntax.Dependency.variable n ∈ clauses.dependencies → sourceLexical.lookup n = (lexical.extend name valueBound).lookup n) →
      (replacement : IndexedSource registry outward owners world allowed .none environment value input [] (.request [] []) .pure Rows.pure) →
      ClosedValue value → Syntax.resourceDependencies value.dependencies ⊆ valueBound →
      (Syntax.Dependency.variable name ∈ clauses.dependencies → Authenticated registry outward replacement lexical receiver) →
      ∃ nextPlans : ClausePlans (clauses.subst name value) families, ∃ nextRows : ClauseRows (clauseSignatures nextPlans),
        ∃ nextSource : SourceDeclarations registry outward owners world environment allowed requested answer (clauses.subst name value) table nextPlans nextRows,
        DeclarationAuthentication registry outward nextSource lexical receiver ∧
        nextPlans = CoreCallablePlanSubstitution.clauses plans name value ∧ clauseSignatures nextPlans = clauseSignatures plans ∧ HEq nextRows rows)
    (motive_6 := fun {owners world sourceEnvironment allowed requested answer clauses table families plans rows} source sourceLexical receiver _ =>
      ∀ environment name input value lexical valueBound,
      sourceEnvironment = environment.extend name input → (∀ n, Syntax.Dependency.variable n ∈ clauses.dependencies → sourceLexical.lookup n = (lexical.extend name valueBound).lookup n) →
      (replacement : IndexedSource registry outward owners world allowed .none environment value input [] (.request [] []) .pure Rows.pure) →
      ClosedValue value → Syntax.resourceDependencies value.dependencies ⊆ valueBound →
      (Syntax.Dependency.variable name ∈ clauses.dependencies → Authenticated registry outward replacement lexical receiver) →
      ∃ nextPlans : ClausePlans (clauses.subst name value) families, ∃ nextRows : ClauseRows (clauseSignatures nextPlans),
        ∃ nextSource : SourceDeclarations registry outward owners world environment allowed requested answer (clauses.subst name value) table nextPlans nextRows,
        DomainDeclarationAuthentication registry outward nextSource lexical receiver ∧
        nextPlans = CoreCallablePlanSubstitution.clauses plans name value ∧ clauseSignatures nextPlans = clauseSignatures plans ∧ HEq nextRows rows) with
  | checked current hereditary ih =>
      intro environment name input value lexical bound sameEnvironment sameLexical replacement closed actual authReplacement
      obtain ⟨nextPlan, nextRows, nextSource, hereditary, exactPlan, sameSignature, sameRows⟩ :=
        ih environment name input value lexical bound sameEnvironment sameLexical replacement closed actual authReplacement
      refine ⟨nextPlan, nextRows, nextSource, .checked ?_ hereditary, exactPlan, sameSignature, sameRows⟩
      apply SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.bounds_iff.mpr
      exact (ScopedPorts.Support.substitution_support_bound (environment := lexical.environment) _ name closed actual).trans
        (by
          have currentReceived := SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.bounds_iff.mp current
          rw [evaluated_lookup_congr sameLexical] at currentReceived
          simpa only [LexicalBounds.environment_extend] using currentReceived)
  | unit | boolean | integer | reference =>
      rename_i environment name input value lexical bound sameEnvironment sameLexical replacement closed actual authReplacement
      cases sameEnvironment
      refine ⟨_, _, ?_, ?_, rfl, rfl, HEq.rfl⟩
      all_goals first | exact .unit | exact .boolean | exact .integer | exact .reference (by assumption) | exact .reference (issued := by assumption)
  | «variable» knownSupport =>
      rename_i owners allowed scope other sourceEnvironment result known world formed sourceLexical receiver environment name input value lexical bound sameEnvironment sameLexical replacement closed actual authReplacement
      cases sameEnvironment
      by_cases same : name = other
      · subst name
        simp only [Environment.extend, ↓reduceIte] at known
        cases Option.some.inj known
        simp only [Code.subst, ↓reduceIte, CoreCallablePlanSubstitution.plan]
        have auth := authReplacement (by simp [Code.dependencies])
        cases auth with
        | checked current hereditary =>
          exact ⟨_, _, replacement, by simpa only [Code.subst, ↓reduceIte] using hereditary, rfl, rfl, HEq.rfl⟩
      · simp only [Code.subst, if_neg same, CoreCallablePlanSubstitution.plan]
        obtain ⟨resources, found⟩ := knownSupport
        have nextKnown : environment other = some result := by simpa [Environment.extend, Ne.symm same] using known
        have nextFound : lexical.lookup other = some resources := by
          have foundNext := (sameLexical other (by simp [Code.dependencies])).symm.trans found
          simpa [lexical_lookup_extend, Ne.symm same] using foundNext
        exact ⟨_, _, .variable nextKnown formed,
          by simpa only [Code.subst, if_neg same] using Hereditary.variable (known := nextKnown) (formed := formed) ⟨resources, nextFound⟩,
          rfl, rfl, HEq.rfl⟩
  | pair left right ihL ihR =>
      rename_i environment name input value lexical bound sameEnvironment sameLexical replacement closed actual authReplacement
      obtain ⟨nextL, rowsL, sourceL, authL, phiL, sigL, alignedL⟩ := ihL environment name input value lexical bound sameEnvironment (fun n mem => sameLexical n (List.mem_append_left _ mem)) replacement closed actual
        (fun occurs => authReplacement (List.mem_append_left _ occurs))
      obtain ⟨nextR, rowsR, sourceR, authR, phiR, sigR, alignedR⟩ := ihR environment name input value lexical bound sameEnvironment (fun n mem => sameLexical n (List.mem_append_right _ mem)) replacement closed actual
        (fun occurs => authReplacement (List.mem_append_right _ occurs))
      refine ⟨.sequence nextL nextR, sequenceRows rowsL rowsR, by simpa only [Code.subst, CoreCallablePlanSubstitution.plan] using IndexedSource.pair sourceL sourceR,
        by simpa only [Code.subst, CoreCallablePlanSubstitution.plan] using Hereditary.pair authL authR, ?_, ?_, ?_⟩
      · simp only [CoreCallablePlanSubstitution.plan]; rw [phiL, phiR]
      · simp only [signature]; exact signature_sequence_same sigL sigR
      · exact sequence_rows_heq sigL sigR alignedL alignedR
  | purePair left right ihL ihR =>
      rename_i environment name input value lexical bound sameEnvironment sameLexical replacement closed actual authReplacement
      obtain ⟨nextL, rowsL, sourceL, authL, phiL, sigL, alignedL⟩ := ihL environment name input value lexical bound sameEnvironment (fun n mem => sameLexical n (List.mem_append_left _ mem)) replacement closed actual
        (fun occurs => authReplacement (List.mem_append_left _ occurs))
      obtain ⟨nextR, rowsR, sourceR, authR, phiR, sigR, alignedR⟩ := ihR environment name input value lexical bound sameEnvironment (fun n mem => sameLexical n (List.mem_append_right _ mem)) replacement closed actual
        (fun occurs => authReplacement (List.mem_append_right _ occurs))
      cases nextL; cases nextR; cases rowsL; cases rowsR
      exact ⟨_, _, by simpa only [Code.subst, CoreCallablePlanSubstitution.plan] using IndexedSource.purePair sourceL sourceR,
        by simpa only [Code.subst, CoreCallablePlanSubstitution.plan] using Hereditary.purePair authL authR, rfl, rfl, HEq.rfl⟩
  | app function argument ihF ihA =>
      rename_i environment name input value lexical bound sameEnvironment sameLexical replacement closed actual authReplacement
      obtain ⟨nextF, rowsF, sourceF, authF, phiF, sigF, alignedF⟩ := ihF environment name input value lexical bound sameEnvironment (fun n mem => sameLexical n (List.mem_append_left _ mem)) replacement closed actual
        (fun occurs => authReplacement (List.mem_append_left _ occurs))
      obtain ⟨nextA, rowsA, sourceA, authA, phiA, sigA, alignedA⟩ := ihA environment name input value lexical bound sameEnvironment (fun n mem => sameLexical n (List.mem_append_right _ mem)) replacement closed actual
        (fun occurs => authReplacement (List.mem_append_right _ occurs))
      refine ⟨_, _, by simpa only [Code.subst, CoreCallablePlanSubstitution.plan] using IndexedSource.app sourceF sourceA (by assumption) (by assumption),
        by simpa only [Code.subst, CoreCallablePlanSubstitution.plan] using Hereditary.app (admitted := by assumption) (publicCertified := by assumption) authF authA, ?_, ?_, ?_⟩
      · simp only [CoreCallablePlanSubstitution.plan]; rw [phiF, phiA]
      · simp only [signature]; exact signature_sequence_same sigF (signature_sequence_same sigA rfl)
      · exact sequence_rows_heq sigF (signature_sequence_same sigA rfl) alignedF (sequence_rows_heq sigA rfl alignedA HEq.rfl)
  | resource initial body ihI ihB =>
      rename_i environment name input value lexical bound sameEnvironment sameLexical replacement closed actual authReplacement
      rename_i bodyDemand owners world allowed scope originalEnvironment initialCode initialDemand
        initialRequirements initialDependencies initialPlan initialRows residual binder output originalLexical
        receiver template bodyRequirements bodyDependencies bodyPlans bodyRows initialSource bodySource
        outwardRequirements formed effectsBound admitted hidden
      obtain ⟨nextI, rowsI, sourceI, authI, phiI, sigI, alignedI⟩ :=
        ihI environment name input value lexical bound sameEnvironment
          (fun n mem => sameLexical n (List.mem_append_left _ mem)) replacement closed actual
          (fun occurs => authReplacement (List.mem_append_left _ occurs))
      let nextPlans := fun identity => CoreCallablePlanSubstitution.plan
        (template.instantiate (Instantiation.Environment.empty.bind binder identity)) (bodyPlans identity) name value
      have sigB : ∀ identity, signature (nextPlans identity) = signature (bodyPlans identity) :=
        fun identity => CoreCallablePlanSubstitution.plan_signature _ _ name closed.1
      let nextRows := fun identity => (sigB identity).symm ▸ bodyRows identity
      have alignedB : ∀ identity, HEq (nextRows identity) (bodyRows identity) :=
        fun identity => rows_cast_heq (sigB identity) (bodyRows identity)
      have transported : ∀ identity, identity ∉ world →
          ∃ nextSource : IndexedSource registry outward owners (world ++ [identity]) (.cell identity :: residual)
            scope environment
            ((template.subst name value).instantiate (Instantiation.Environment.empty.bind binder identity))
            output bodyDemand (bodyRequirements identity) (nextPlans identity) (nextRows identity),
          Authenticated registry outward nextSource lexical (identity :: receiver) := by
        intro identity fresh
        have bodyOccurs : ∀ n, Syntax.Dependency.variable n ∈
            (template.instantiate (Instantiation.Environment.empty.bind binder identity)).dependencies →
            Syntax.Dependency.variable n ∈ (Code.resource binder initialCode template).dependencies := by
          intro n mem
          rcases List.mem_append.mp (acquisition_dependency_bound _ identity _ mem) with old | introduced
          · exact List.mem_append_right _ old
          · simp at introduced
        let openedReplacement := (replacement.world_weaken (nextWorld := world ++ [identity])
            (by intro id member; exact List.mem_append_left _ member)).value_allowed closed.1 (.cell identity :: residual) scope
        have replacementAuth : Syntax.Dependency.variable name ∈
            (template.instantiate (Instantiation.Environment.empty.bind binder identity)).dependencies →
            Authenticated registry outward openedReplacement lexical (identity :: receiver) := by
          intro occurs
          have auth := authReplacement (bodyOccurs name occurs)
          have weakened := (auth.value_world_weaken (nextWorld := world ++ [identity]) closed.1
            (by intro id member; exact List.mem_append_left _ member)).value_allowed closed.1 (.cell identity :: residual) scope
          apply weakened.value_reauthenticate closed
          exact (SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.bounds_iff.mp auth.current_support).trans
            (by intro id member; exact List.mem_cons_of_mem _ member)
        obtain ⟨newPlan, newRows, newSource, newAuth, phi, sig, aligned⟩ :=
          ihB identity fresh environment name input value lexical bound sameEnvironment
            (fun n mem => sameLexical n (bodyOccurs n mem)) openedReplacement closed actual replacementAuth
        change newPlan = nextPlans identity at phi
        cases phi
        have rowSame : newRows = nextRows identity := eq_of_heq (aligned.trans (alignedB identity).symm)
        cases rowSame
        rw [Code.instantiation_subst _ name value _ closed.2.1]
        exact ⟨newSource, newAuth⟩
      let opened := fun identity fresh => Classical.choose (transported identity fresh)
      have openedAuth := fun identity fresh => Classical.choose_spec (transported identity fresh)
      refine ⟨.sequence nextI (.resource nextPlans), sequenceRows rowsI (Rows.resource nextRows),
        by simpa only [Code.subst] using IndexedSource.resource sourceI opened formed effectsBound admitted hidden,
        ?_, ?_, ?_, ?_⟩
      · simpa only [Code.subst] using Hereditary.resource (bodySource := opened)
          (formed := formed) (effectsBound := effectsBound) (admitted := admitted) (hidden := hidden) authI openedAuth
      · simp only [CoreCallablePlanSubstitution.plan]; rw [phiI]
      · exact signature_sequence_same sigI (congrArg SourcePlanSignatures.Signature.resource (funext sigB))
      · exact sequence_rows_heq sigI (congrArg SourcePlanSignatures.Signature.resource (funext sigB))
          alignedI (resource_rows_heq sigB alignedB)
  | cleanup callback body ihC ihB =>
      rename_i environment name input value lexical bound sameEnvironment sameLexical replacement closed actual authReplacement
      obtain ⟨nextC, rowsC, sourceC, authC, phiC, sigC, alignedC⟩ := ihC environment name input value lexical bound sameEnvironment (fun n mem => sameLexical n (List.mem_append_left _ mem)) replacement closed actual
        (fun occurs => authReplacement (List.mem_append_left _ occurs))
      obtain ⟨nextB, rowsB, sourceB, authB, phiB, sigB, alignedB⟩ := ihB environment name input value lexical bound sameEnvironment (fun n mem => sameLexical n (List.mem_append_right _ mem)) replacement closed actual
        (fun occurs => authReplacement (List.mem_append_right _ occurs))
      refine ⟨_, _, by simpa only [Code.subst, CoreCallablePlanSubstitution.plan] using IndexedSource.cleanup sourceC sourceB (by assumption) (by assumption),
        by simpa only [Code.subst, CoreCallablePlanSubstitution.plan] using Hereditary.cleanup (admitted := by assumption) (publicCertified := by assumption) authC authB, ?_, ?_, ?_⟩
      · simp only [CoreCallablePlanSubstitution.plan]; rw [phiC, phiB]
      · simp only [signature]; exact signature_sequence_same sigC
          (congrArg (fun body => SourcePlanSignatures.Signature.cleanup _ body) sigB)
      · exact sequence_rows_heq sigC
          (congrArg (fun body => SourcePlanSignatures.Signature.cleanup _ body) sigB)
          alignedC (cleanup_rows_heq sigB alignedB)
  | perform operand ih =>
      rename_i environment name input value lexical bound sameEnvironment sameLexical replacement closed actual authReplacement
      obtain ⟨next, nextRows, nextSource, auth, phiSame, sameSig, aligned⟩ := ih environment name input value lexical bound sameEnvironment (fun n mem => sameLexical n (List.mem_append_right _ mem)) replacement closed actual
        (fun occurs => authReplacement (List.mem_append_right _ occurs))
      refine ⟨.sequence next .request, sequenceRows nextRows Rows.request,
        by simpa only [Code.subst, CoreCallablePlanSubstitution.plan] using IndexedSource.perform (by assumption) (by assumption) nextSource (by assumption),
        by simpa only [Code.subst, CoreCallablePlanSubstitution.plan] using Hereditary.perform (known := by assumption) (admitted := by assumption) (formed := by assumption) auth, ?_, ?_, ?_⟩
      · simp only [CoreCallablePlanSubstitution.plan]; rw [phiSame]
      · simp only [signature]; exact signature_sequence_same sameSig rfl
      · exact sequence_rows_heq sameSig rfl aligned HEq.rfl
  | resume operand ih =>
      rename_i environment name input value lexical bound sameEnvironment sameLexical replacement closed actual authReplacement
      obtain ⟨next, nextRows, nextSource, auth, phiSame, sameSig, aligned⟩ := ih environment name input value lexical bound sameEnvironment (fun n mem => sameLexical n (List.mem_cons_of_mem _ mem)) replacement closed actual
        (fun occurs => authReplacement (List.mem_cons_of_mem _ occurs))
      refine ⟨.sequence next .invoke, sequenceRows nextRows Rows.invoke,
        by simpa only [Code.subst, CoreCallablePlanSubstitution.plan] using IndexedSource.resume (by assumption) (by assumption) (by assumption) nextSource (by assumption) (by assumption),
        by simpa only [Code.subst, CoreCallablePlanSubstitution.plan] using Hereditary.resume (known := by assumption) (resolved := by assumption) (permission := by assumption) (admitted := by assumption) (formed := by assumption) auth, ?_, ?_, ?_⟩
      · simp only [CoreCallablePlanSubstitution.plan]; rw [phiSame]
      · simp only [signature]; exact signature_sequence_same sameSig rfl
      · exact sequence_rows_heq sameSig rfl aligned HEq.rfl
  | discard known resolved permission unprotected admitted =>
      rename_i environment name input value lexical bound sameEnvironment sameLexical replacement closed actual authReplacement
      exact ⟨_, _, by simpa only [Code.subst, CoreCallablePlanSubstitution.plan] using IndexedSource.discard known resolved permission unprotected admitted,
        by simpa only [Code.subst, CoreCallablePlanSubstitution.plan] using Hereditary.discard known resolved permission unprotected admitted, rfl, rfl, HEq.rfl⟩
  | branch condition yes no ihC ihY ihN =>
      rename_i environment name input value lexical bound sameEnvironment sameLexical replacement closed actual authReplacement
      obtain ⟨nextC, rowsC, sourceC, authC, phiC, sigC, alignedC⟩ := ihC environment name input value lexical bound sameEnvironment (fun n mem => sameLexical n (List.mem_append_left _ (List.mem_append_left _ mem))) replacement closed actual
        (fun occurs => authReplacement (List.mem_append_left _ (List.mem_append_left _ occurs)))
      obtain ⟨nextY, rowsY, sourceY, authY, phiY, sigY, alignedY⟩ := ihY environment name input value lexical bound sameEnvironment (fun n mem => sameLexical n (List.mem_append_left _ (List.mem_append_right _ mem))) replacement closed actual
        (fun occurs => authReplacement (List.mem_append_left _ (List.mem_append_right _ occurs)))
      obtain ⟨nextN, rowsN, sourceN, authN, phiN, sigN, alignedN⟩ := ihN environment name input value lexical bound sameEnvironment (fun n mem => sameLexical n (List.mem_append_right _ mem)) replacement closed actual
        (fun occurs => authReplacement (List.mem_append_right _ occurs))
      refine ⟨_, _, by simpa only [Code.subst, CoreCallablePlanSubstitution.plan] using IndexedSource.branch sourceC sourceY sourceN (by assumption),
        by simpa only [Code.subst, CoreCallablePlanSubstitution.plan] using Hereditary.branch (sameDemand := by assumption) authC authY authN, ?_, ?_, ?_⟩
      · simp only [CoreCallablePlanSubstitution.plan]; rw [phiC, phiY, phiN]
      · simp only [signature]; exact signature_sequence_same sigC (signature_choice_same sigY sigN)
      · exact sequence_rows_heq sigC (signature_choice_same sigY sigN) alignedC (choice_rows_heq sigY sigN alignedY alignedN)
  | typed source ih =>
      rename_i environment name input value lexical bound sameEnvironment sameLexical replacement closed actual authReplacement
      obtain ⟨next, nextRows, nextSource, auth, phiSame, sameSig, aligned⟩ := ih environment name input value lexical bound sameEnvironment sameLexical replacement closed actual authReplacement
      exact ⟨_, _, .typed nextSource (by assumption) (by assumption), .typed (normal := by assumption) (closing := by assumption) auth, phiSame, sameSig, aligned⟩
  | unavailable =>
      rename_i formalSupport environment name input value lexical bound sameEnvironment sameLexical replacement closed actual authReplacement
      exact ⟨.unavailable, .unavailable, .unavailable, .unavailable, by simp [CoreCallablePlanSubstitution.modes], rfl, HEq.rfl⟩
  | nil =>
      exact ⟨.nil, .nil, .nil, .nil, rfl, rfl, HEq.rfl⟩
  | domainNil =>
      exact ⟨.nil, .nil, .nil, .domainNil, rfl, rfl, HEq.rfl⟩
  | bind initial body ihI ihB =>
      rename_i owners world allowed scope sourceEnvironment a parameterInput initialDemand initialReq initialDeps initialPlan initialRows parameter b output bodyDemand bodyReq bodyDeps bodyPlan bodyRows sourceLexical receiver initialSource bodySource environment name input value lexical bound sameEnvironment sameLexical replacement closed actual authReplacement
      cases sameEnvironment
      obtain ⟨nextI, rowsI, sourceI, authI, phiI, sigI, alignedI⟩ := ihI environment name input value lexical bound rfl
        (fun n mem => sameLexical n (List.mem_append_left _ mem)) replacement closed actual
        (fun occurs => authReplacement (List.mem_append_left _ occurs))
      by_cases same : name = parameter
      · subst name
        have typeAgree : ∀ n, Syntax.Dependency.variable n ∈ b.dependencies →
            (environment.extend parameter input).extend parameter parameterInput n = environment.extend parameter parameterInput n := by
          intro n _; by_cases equal : n = parameter <;> simp [Environment.extend, equal]
        let nextBodySource := bodySource.environment_congr typeAgree
        have lexicalAgree : ∀ n, Syntax.Dependency.variable n ∈ b.dependencies →
            (sourceLexical.extend parameter receiver).lookup n = (lexical.extend parameter receiver).lookup n := by
          intro n mem
          by_cases shadow : n = parameter
          · subst n; simp
          · have old := sameLexical n (List.mem_append_right _ (Syntax.mem_without.mpr ⟨mem, by simpa using shadow⟩))
            simpa [lexical_lookup_extend, shadow] using old
        have nextAuth := (body.environment_congr typeAgree nextBodySource).lexical_congr lexicalAgree
        refine ⟨.sequence nextI bodyPlan, sequenceRows rowsI bodyRows,
          by simpa only [Code.subst, ↓reduceIte] using IndexedSource.bind sourceI nextBodySource,
          by simpa only [Code.subst, ↓reduceIte] using Hereditary.bind authI nextAuth, ?_, ?_, ?_⟩
        · simp only [CoreCallablePlanSubstitution.plan, ↓reduceIte]; rw [phiI]
        · simp only [signature]; exact signature_sequence_same sigI rfl
        · exact sequence_rows_heq sigI rfl alignedI HEq.rfl
      · have lexicalAgree : ∀ n, Syntax.Dependency.variable n ∈ b.dependencies →
            (sourceLexical.extend parameter receiver).lookup n = ((lexical.extend parameter receiver).extend name bound).lookup n := by
          intro n mem
          by_cases shadow : n = parameter
          · subst n; simp [lexical_lookup_extend, Ne.symm same]
          · have old := sameLexical n (List.mem_append_right _ (Syntax.mem_without.mpr ⟨mem, by simpa using shadow⟩))
            simpa [lexical_lookup_extend, shadow] using old
        let replacementB := replacement.closed_environment closed (environment.extend parameter parameterInput)
        obtain ⟨nextB, rowsB, sourceB, authB, phiB, sigB, alignedB⟩ := ihB _ name input value (lexical.extend parameter receiver) bound
          (Environment.extend_commute environment name parameter input parameterInput same) lexicalAgree replacementB closed actual
          (fun occurs => ((authReplacement (List.mem_append_right _ (Syntax.mem_without.mpr ⟨occurs, by simpa using same⟩))).closed_environment closed _).lexical_congr
            (fun n mem => False.elim (ScopedTyping.closedValue_no_variable closed mem)))
        refine ⟨.sequence nextI nextB, sequenceRows rowsI rowsB,
          by simpa only [Code.subst, if_neg same] using IndexedSource.bind sourceI sourceB,
          by simpa only [Code.subst, if_neg same] using Hereditary.bind authI authB, ?_, ?_, ?_⟩
        · simp only [CoreCallablePlanSubstitution.plan, if_neg same]; rw [phiI, phiB]
        · simp only [signature]; exact signature_sequence_same sigI sigB
        · exact sequence_rows_heq sigI sigB alignedI alignedB
  | lambda refinement bodyOutward latentBound publicCertified formed known body ih =>
      rename_i sourceEnv bodySource contractDeps contractPlan contractRows environment name input value lexical bound sameEnvironment sameLexical replacement closed actual authReplacement
      cases sameEnvironment
      obtain ⟨nextSource, hereditary⟩ := lambda_hereditary_substitution stable
        (bodySource := fun _ call => bodySource.world_weaken call.worldExtended)
        (privatePlans := fun _ _ => _) (privateRows := fun _ _ => _)
        body (fun _ _ _ _ => ReceiverRefines.of_universal refinement _ _) ih
        bodyOutward latentBound publicCertified formed known sameLexical replacement closed authReplacement
      exact ⟨.pure, Rows.pure, nextSource, hereditary, rfl, rfl, HEq.rfl⟩
  | receiverLambda bodyOutward latentBound publicCertified formed known body refinement ih =>
      rename_i owners world sourceEnv privateDependencies privatePlans privateRows bodySource contractDeps contractPlan contractRows environment name input value lexical bound sameEnvironment sameLexical replacement closed actual authReplacement
      cases sameEnvironment
      obtain ⟨nextSource, hereditary⟩ := lambda_hereditary_substitution stable bodySource body refinement ih
        bodyOutward latentBound publicCertified formed known sameLexical replacement closed authReplacement
      exact ⟨.pure, Rows.pure, nextSource, hereditary, rfl, rfl, HEq.rfl⟩
  | available resumeInterface closeInterface body ih =>
      rename_i resumeEffects closeEffects held allowed binder parameter code disposes row sourceLexical receiver owners world sourceEnv argument parameterInput answer family originalPlans originalRows bodySource formalSupport environment name input value lexical bound sameEnvironment sameLexical replacement closed actual authReplacement
      cases sameEnvironment
      by_cases shadow : name = parameter
      · subst name
        have typeAgree : ∀ n, Syntax.Dependency.variable n ∈ code.dependencies →
            (environment.extend parameter input).extend parameter argument n = environment.extend parameter argument n := by
          intro n _; by_cases same : n = parameter <;> simp [Environment.extend, same]
        have lexicalAgree : ∀ n, Syntax.Dependency.variable n ∈ code.dependencies → sourceLexical.lookup n = (lexical.extend parameter formalSupport).lookup n := by
          intro n mem
          have old := sameLexical n mem
          by_cases same : n = parameter <;> simpa [lexical_lookup_extend, same] using old
        have derived := fun owner contract a b c d e balanced =>
          (body owner contract a b c d e balanced).transport typeAgree lexicalAgree
        let changedSource := fun owner contract a b c d e balanced => Classical.choose (derived owner contract a b c d e balanced)
        refine ⟨_, _, by simpa only [↓reduceIte] using SourceOffer.available resumeInterface closeInterface changedSource,
          by simpa only [↓reduceIte] using (OfferAuthentication.available (bodySource := changedSource) resumeInterface closeInterface
            (fun owner contract a b c d e balanced => Classical.choose_spec (derived owner contract a b c d e balanced))), by simp, rfl, HEq.rfl⟩
      · let changedPlans := fun owner => CoreCallablePlanSubstitution.plan code (originalPlans owner) name value
        let changedRows := fun owner =>
          (CoreCallablePlanSubstitution.plan_signature code (originalPlans owner) name closed.1).symm ▸ originalRows owner
        have lexicalAgree : ∀ n, Syntax.Dependency.variable n ∈ code.dependencies →
            sourceLexical.lookup n = ((lexical.extend parameter formalSupport).extend name bound).lookup n := by
          intro n mem
          have old := sameLexical n mem
          by_cases same : n = parameter
          · subst n; simpa [lexical_lookup_extend, Ne.symm shadow] using old
          · simpa [lexical_lookup_extend, same] using old
        have derived : ∀ owner (contract : OwnerContract) (a : contract.input = parameterInput) (b : contract.answer = answer)
            (c : contract.resumeEffects = resumeEffects) (d : contract.closeEffects = closeEffects) (e : contract.held = held)
            (balanced : contract.closeDemand.Perm contract.resumeDemand),
            ∃ nextSource : SourceBody registry outward (owners.insert owner contract) world allowed (.ticket binder owner)
              (environment.extend parameter argument) (code.subst name value) answer ⟨owner, contract.lower, disposes, row⟩ (changedPlans owner) (changedRows owner),
              BodyAuthentication registry outward nextSource (lexical.extend parameter formalSupport) receiver := by
          intro owner contract a b c d e balanced
          let replacementAt := (((replacement.value_owner_insert closed.1 owner contract).value_allowed closed.1 allowed (.ticket binder owner)).closed_environment closed (environment.extend parameter argument))
          have replacementAuth : Syntax.Dependency.variable name ∈ code.dependencies →
              Authenticated registry outward replacementAt (lexical.extend parameter formalSupport) receiver := by
            intro occurs
            exact ((((authReplacement (Syntax.mem_without.mpr ⟨occurs, by simpa using shadow⟩)).value_owner_insert closed.1 owner contract).value_allowed closed.1 allowed (.ticket binder owner)).closed_environment closed _).lexical_congr
              (fun _ mem => False.elim (ScopedTyping.closedValue_no_variable closed mem))
          obtain ⟨nextPlan, nextRows, nextSource, auth, exactPlan, sameSignature, aligned⟩ := ih owner contract a b c d e balanced
            _ name input value (lexical.extend parameter formalSupport) bound
            (Environment.extend_commute environment name parameter input argument shadow) lexicalAgree replacementAt closed actual replacementAuth
          cases exactPlan
          have sameRows : HEq nextRows (changedRows owner) := aligned.trans
            (rows_cast_heq (CoreCallablePlanSubstitution.plan_signature _ _ name closed.1) _).symm
          cases eq_of_heq sameRows
          exact ⟨nextSource, auth⟩
        let changedSource := fun owner contract a b c d e balanced => Classical.choose (derived owner contract a b c d e balanced)
        have resumeChanged : (code.subst name value).requiredActions.resume = true → resumeEffects = allowed := by simpa only [Code.substitution_required_actions _ _ closed.1] using resumeInterface
        have closeChanged : (code.subst name value).requiredActions.dispose = true → closeEffects = allowed := by simpa only [Code.substitution_required_actions _ _ closed.1] using closeInterface
        refine ⟨.available changedPlans, .available changedRows,
          by simpa only [if_neg shadow] using SourceOffer.available resumeChanged closeChanged changedSource,
          by simpa only [if_neg shadow] using (OfferAuthentication.available (bodySource := changedSource) resumeChanged closeChanged
            (fun owner contract a b c d e balanced => Classical.choose_spec (derived owner contract a b c d e balanced))), ?_, ?_, ?_⟩
        · simp only [if_neg shadow, CoreCallablePlanSubstitution.modes]; rfl
        · exact CoreCallablePlanSubstitution.modes_signature code (.available originalPlans) name closed.1
        · exact available_rows_heq (fun owner => CoreCallablePlanSubstitution.plan_signature code (originalPlans owner) name closed.1)
            (fun owner => rows_cast_heq (CoreCallablePlanSubstitution.plan_signature code (originalPlans owner) name closed.1) (originalRows owner))
  | cons known bodyBound storedReceived ordinary protectedMode rest ihO ihP ihR =>
      rename_i owners world sourceEnv allowed parameter binder argument parameterInput answer resumeEffects closeEffects code disposes ordinaryRow ordinaryFamily originalOrdinary originalOrdinaryRows protectedRow protectedFamily originalProtected originalProtectedRows requested clauses table restFamily originalRest originalRestRows operation supportBound receiver sourceLexical ordinarySource protectedSource restSource environment name input value lexical bound sameEnvironment sameLexical replacement closed actual authReplacement
      cases sameEnvironment
      have lookupBody : ∀ n, Syntax.Dependency.variable n ∈ code.dependencies →
          (sourceLexical.extend parameter receiver).lookup n = ((lexical.extend name bound).extend parameter receiver).lookup n := by
        intro n mem
        by_cases shadow : n = parameter
        · subst n; simp
        · have old := sameLexical n (List.mem_append_left _
            (Syntax.mem_without.mpr ⟨Syntax.mem_without.mpr ⟨mem, by simpa using shadow⟩, by simp⟩))
          simpa [lexical_lookup_extend, shadow] using old
      have authMode : Syntax.Dependency.variable name ∈ Syntax.without (.variable parameter) code.dependencies →
          Authenticated registry outward replacement lexical receiver := by
        intro occurs
        exact authReplacement (List.mem_append_left _ (Syntax.mem_without.mpr ⟨occurs, by simp⟩))
      obtain ⟨nextOrd, rowsOrd, sourceOrd, authOrd, phiOrd, sigOrd, alignedOrd⟩ :=
        ihO receiver environment name input value lexical bound rfl lookupBody replacement closed actual authMode
      obtain ⟨nextProt, rowsProt, sourceProt, authProt, phiProt, sigProt, alignedProt⟩ :=
        ihP receiver environment name input value lexical bound rfl lookupBody replacement closed actual authMode
      obtain ⟨nextRest, rowsRest, sourceRest, authRest, phiRest, sigRest, alignedRest⟩ :=
        ihR environment name input value lexical bound rfl (fun n mem => sameLexical n (List.mem_append_right _ mem)) replacement closed actual
          (fun occurs => authReplacement (List.mem_append_right _ occurs))
      have newBound : SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.Bounds
          (lexical.extend parameter receiver).environment (if name = parameter then code else code.subst name value).dependencies supportBound := by
        apply SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.bounds_iff.mpr
        have oldReceived := SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.bounds_iff.mp bodyBound
        rw [evaluated_lookup_congr lookupBody] at oldReceived
        by_cases shadow : name = parameter
        · subst name
          have sameLookup : ∀ n, Syntax.Dependency.variable n ∈ code.dependencies →
              ((lexical.extend parameter bound).extend parameter receiver).lookup n = (lexical.extend parameter receiver).lookup n := by
            intro n _; by_cases same : n = parameter <;> simp [lexical_lookup_extend, same]
          simpa only [↓reduceIte] using (evaluated_lookup_congr sameLookup ▸ oldReceived)
        · have sameLookup : ∀ n, Syntax.Dependency.variable n ∈ code.dependencies →
              ((lexical.extend name bound).extend parameter receiver).lookup n = ((lexical.extend parameter receiver).extend name bound).lookup n := by
            intro n _; by_cases same : n = parameter <;> simp [lexical_lookup_extend, same, Ne.symm shadow]
          rw [evaluated_lookup_congr sameLookup, LexicalBounds.environment_extend] at oldReceived
          simpa only [if_neg shadow] using
            (ScopedPorts.Support.substitution_support_bound (environment := (lexical.extend parameter receiver).environment) code name closed actual).trans oldReceived
      have rights : (if name = parameter then code else code.subst name value).requiredActions = code.requiredActions := by
        split <;> simp only [Code.substitution_required_actions code name closed.1]
      refine ⟨.cons nextOrd nextProt nextRest, _,
        by simpa only [Clauses.subst] using SourceDeclarations.cons supportBound known sourceOrd sourceProt sourceRest,
        by simpa only [Clauses.subst] using DeclarationAuthentication.cons known newBound storedReceived authOrd authProt authRest, ?_, ?_, ?_⟩
      · simp only [CoreCallablePlanSubstitution.clauses]; rw [phiOrd, phiProt, phiRest]; split <;> simp_all <;> try rfl
      · simp only [clauseSignatures]; exact signature_declaration_cons_same sigOrd sigProt sigRest rights
      · exact (transport_heq _ _).trans ((declaration_cons_heq sigOrd sigProt sigRest rights alignedOrd alignedProt alignedRest).trans (transport_heq _ _).symm)
  | domainCons known domainCovered formalReceived bodyBound storedReceived ordinary protectedMode rest ihO ihP ihR =>
      rename_i owners world sourceEnv allowed parameter binder argument parameterInput answer resumeEffects closeEffects code disposes ordinaryRow ordinaryFamily originalOrdinary originalOrdinaryRows protectedRow protectedFamily originalProtected originalProtectedRows requested clauses table restFamily originalRest originalRestRows operation receiver formalSupport supportBound sourceLexical ordinarySource protectedSource restSource environment name input value lexical bound sameEnvironment sameLexical replacement closed actual authReplacement
      cases sameEnvironment
      have lookupBody : ∀ n, Syntax.Dependency.variable n ∈ code.dependencies →
          (sourceLexical.extend parameter formalSupport).lookup n = ((lexical.extend name bound).extend parameter formalSupport).lookup n := by
        intro n mem
        by_cases shadow : n = parameter
        · subst n; simp
        · have old := sameLexical n (List.mem_append_left _
            (Syntax.mem_without.mpr ⟨Syntax.mem_without.mpr ⟨mem, by simpa using shadow⟩, by simp⟩))
          simpa [lexical_lookup_extend, shadow] using old
      have authMode : Syntax.Dependency.variable name ∈ Syntax.without (.variable parameter) code.dependencies →
          Authenticated registry outward replacement lexical receiver := by
        intro occurs
        exact authReplacement (List.mem_append_left _ (Syntax.mem_without.mpr ⟨occurs, by simp⟩))
      obtain ⟨nextOrd, rowsOrd, sourceOrd, authOrd, phiOrd, sigOrd, alignedOrd⟩ :=
        ihO formalSupport environment name input value lexical bound rfl lookupBody replacement closed actual authMode
      obtain ⟨nextProt, rowsProt, sourceProt, authProt, phiProt, sigProt, alignedProt⟩ :=
        ihP formalSupport environment name input value lexical bound rfl lookupBody replacement closed actual authMode
      obtain ⟨nextRest, rowsRest, sourceRest, authRest, phiRest, sigRest, alignedRest⟩ :=
        ihR environment name input value lexical bound rfl (fun n mem => sameLexical n (List.mem_append_right _ mem)) replacement closed actual
          (fun occurs => authReplacement (List.mem_append_right _ occurs))
      have newBound : SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.Bounds
          (lexical.extend parameter formalSupport).environment (if name = parameter then code else code.subst name value).dependencies supportBound := by
        apply SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.bounds_iff.mpr
        have oldReceived := SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.bounds_iff.mp bodyBound
        rw [evaluated_lookup_congr lookupBody] at oldReceived
        by_cases shadow : name = parameter
        · subst name
          have sameLookup : ∀ n, Syntax.Dependency.variable n ∈ code.dependencies →
              ((lexical.extend parameter bound).extend parameter formalSupport).lookup n = (lexical.extend parameter formalSupport).lookup n := by
            intro n _; by_cases same : n = parameter <;> simp [lexical_lookup_extend, same]
          simpa only [↓reduceIte] using (evaluated_lookup_congr sameLookup ▸ oldReceived)
        · have sameLookup : ∀ n, Syntax.Dependency.variable n ∈ code.dependencies →
              ((lexical.extend name bound).extend parameter formalSupport).lookup n = ((lexical.extend parameter formalSupport).extend name bound).lookup n := by
            intro n _; by_cases same : n = parameter <;> simp [lexical_lookup_extend, same, Ne.symm shadow]
          rw [evaluated_lookup_congr sameLookup, LexicalBounds.environment_extend] at oldReceived
          simpa only [if_neg shadow] using
            (ScopedPorts.Support.substitution_support_bound (environment := (lexical.extend parameter formalSupport).environment) code name closed actual).trans oldReceived
      have rights : (if name = parameter then code else code.subst name value).requiredActions = code.requiredActions := by
        split <;> simp only [Code.substitution_required_actions code name closed.1]
      refine ⟨.cons nextOrd nextProt nextRest, _,
        by simpa only [Clauses.subst] using SourceDeclarations.cons supportBound known sourceOrd sourceProt sourceRest,
        by simpa only [Clauses.subst] using DomainDeclarationAuthentication.domainCons known domainCovered formalReceived newBound storedReceived authOrd authProt authRest, ?_, ?_, ?_⟩
      · simp only [CoreCallablePlanSubstitution.clauses]; rw [phiOrd, phiProt, phiRest]; split <;> simp_all <;> try rfl
      · simp only [clauseSignatures]; exact signature_declaration_cons_same sigOrd sigProt sigRest rights
      · exact (transport_heq _ _).trans ((declaration_cons_heq sigOrd sigProt sigRest rights alignedOrd alignedProt alignedRest).trans (transport_heq _ _).symm)
  | handler clauses capabilities coverage unique admitted modes recipes body declarations ihB ihD =>
      rename_i environment name input value lexical bound sameEnvironment sameLexical replacement closed actual authReplacement
      cases sameEnvironment
      obtain ⟨nextBody, rowsBody, sourceBody, authBody, phiBody, sigBody, alignedBody⟩ :=
        ihB environment name input value lexical bound rfl
          (fun n mem => sameLexical n (List.mem_append_left _ (List.mem_append_right _ mem))) (replacement.value_allowed closed.1 _ _) closed actual
          (fun occurs => (authReplacement (List.mem_append_left _ (List.mem_append_right _ occurs))).value_allowed closed.1 _ _)
      obtain ⟨nextDecl, rowsDecl, sourceDecl, authDecl, phiDecl, sigDecl, alignedDecl⟩ :=
        ihD environment name input value lexical bound rfl
          (fun n mem => sameLexical n (List.mem_append_right _ mem)) (replacement.value_allowed closed.1 _ .none) closed actual
          (fun occurs => (authReplacement (List.mem_append_right _ occurs)).value_allowed closed.1 _ .none)
      have nextClauses := ScopedPorts.clauses_typed_substitution
        (by simpa only [Environment.ports_extend] using clauses)
        ((replacement.value_allowed closed.1 [] .none).erase) closed
      have nextCapabilities := ScopedExpressions.clauses_usage_substitution capabilities closed.1
        ((replacement.value_allowed closed.1 [] .none).usage_for_substitution rfl) name
      have nextModes := SourceTemplates.clause_modes_substitution modes closed.1 name
      refine ⟨.handler _ nextDecl nextBody, _,
        by simpa only [Code.subst] using (IndexedSource.handler sourceBody
          (by simpa only [Environment.ports_extend] using nextClauses) nextCapabilities (by simpa only [ScopedPorts.Covers, ScopedTyping.clause_keys_substitution] using coverage) (by simpa only [ScopedTyping.clause_keys_substitution] using unique) admitted _ nextModes sourceDecl (stable recipes sigDecl.symm)),
        by simpa only [Code.subst] using (Hereditary.handler
          (by simpa only [Environment.ports_extend] using nextClauses) nextCapabilities (by simpa only [ScopedPorts.Covers, ScopedTyping.clause_keys_substitution] using coverage) (by simpa only [ScopedTyping.clause_keys_substitution] using unique) admitted nextModes (stable recipes sigDecl.symm) authBody authDecl), ?_, ?_, ?_⟩
      · simp only [CoreCallablePlanSubstitution.plan]; rw [phiBody, phiDecl]
      · simp only [signature]; exact signature_handler_same sigDecl sigBody
      · exact (transport_heq _ _).trans ((handler_rows_heq sigDecl sigBody alignedDecl alignedBody).trans (transport_heq _ _).symm)
  | handlerDomain clauses capabilities coverage unique admitted modes recipes body declarations ihB ihD =>
      rename_i environment name input value lexical bound sameEnvironment sameLexical replacement closed actual authReplacement
      cases sameEnvironment
      obtain ⟨nextBody, rowsBody, sourceBody, authBody, phiBody, sigBody, alignedBody⟩ :=
        ihB environment name input value lexical bound rfl
          (fun n mem => sameLexical n (List.mem_append_left _ (List.mem_append_right _ mem))) (replacement.value_allowed closed.1 _ _) closed actual
          (fun occurs => (authReplacement (List.mem_append_left _ (List.mem_append_right _ occurs))).value_allowed closed.1 _ _)
      obtain ⟨nextDecl, rowsDecl, sourceDecl, authDecl, phiDecl, sigDecl, alignedDecl⟩ :=
        ihD environment name input value lexical bound rfl
          (fun n mem => sameLexical n (List.mem_append_right _ mem)) (replacement.value_allowed closed.1 _ .none) closed actual
          (fun occurs => (authReplacement (List.mem_append_right _ occurs)).value_allowed closed.1 _ .none)
      have nextClauses := ScopedPorts.clauses_typed_substitution
        (by simpa only [Environment.ports_extend] using clauses)
        ((replacement.value_allowed closed.1 [] .none).erase) closed
      have nextCapabilities := ScopedExpressions.clauses_usage_substitution capabilities closed.1
        ((replacement.value_allowed closed.1 [] .none).usage_for_substitution rfl) name
      have nextModes := SourceTemplates.clause_modes_substitution modes closed.1 name
      refine ⟨.handler _ nextDecl nextBody, _,
        by simpa only [Code.subst] using (IndexedSource.handler sourceBody
          (by simpa only [Environment.ports_extend] using nextClauses) nextCapabilities (by simpa only [ScopedPorts.Covers, ScopedTyping.clause_keys_substitution] using coverage) (by simpa only [ScopedTyping.clause_keys_substitution] using unique) admitted _ nextModes sourceDecl (stable recipes sigDecl.symm)),
        by simpa only [Code.subst] using (Hereditary.handlerDomain
          (by simpa only [Environment.ports_extend] using nextClauses) nextCapabilities (by simpa only [ScopedPorts.Covers, ScopedTyping.clause_keys_substitution] using coverage) (by simpa only [ScopedTyping.clause_keys_substitution] using unique) admitted nextModes (stable recipes sigDecl.symm) authBody authDecl), ?_, ?_, ?_⟩
      · simp only [CoreCallablePlanSubstitution.plan]; rw [phiBody, phiDecl]
      · simp only [signature]; exact signature_handler_same sigDecl sigBody
      · exact (transport_heq _ _).trans ((handler_rows_heq sigDecl sigBody alignedDecl alignedBody).trans (transport_heq _ _).symm)

end
end Ash.OneShot.CoreCallableContractAdmission

#print axioms Ash.OneShot.CoreCallableContractAdmission.Authenticated.substitution_reannotated_at
