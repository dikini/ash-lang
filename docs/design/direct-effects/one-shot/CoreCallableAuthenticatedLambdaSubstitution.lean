import CoreCallableAuthenticatedLexical
import CoreCallableAuthenticatedClosedReceiver
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
set_option maxHeartbeats 1600000
omit evidence in
private theorem cast_rows_heq {first second : SourcePlanSignatures.Signature dependencies}
    (same : first = second) (rows : Rows second) : HEq (same.symm ▸ rows) rows := by cases same; rfl
omit evidence in
private theorem closed_evaluation {value : Code} (closed : ClosedValue value) (environment : ScopedPorts.Support.Env) :
    ScopedPorts.Support.evaluate environment value.dependencies = Syntax.resourceDependencies value.dependencies := by
  rw [ScopedPorts.Support.evaluation_congr (destination := ScopedPorts.Support.empty)
    (fun _ member => False.elim (ScopedTyping.closedValue_no_variable closed member))]
  exact ScopedPorts.Support.empty_evaluation _
omit evidence in
private theorem refinement_rows {first second : SourcePlanSignatures.Signature dependencies}
    {original : Rows first} {changed : Rows second}
    (refinement : ReceiverRefines contractRows original receiver required) (same : second = first)
    (aligned : HEq changed original) (received : required ⊆ receiver) :
    ReceiverRefines contractRows changed receiver nextRequired := by
  cases same; cases eq_of_heq aligned
  exact {
    code := refinement.code
    checked := by
      intro ambient outward actions budget phases world installations scope hints context retained certificate _ issued visible pending checked
      exact refinement.checked ambient outward actions budget phases world installations context retained certificate received issued visible pending checked
    accounting := refinement.accounting }

theorem lambda_hereditary_substitution
    (stable : ∀ {before after families required} {first : ClausePlans before families} {second : ClausePlans after families},
      evidence.accepts outward required first → clauseSignatures first = clauseSignatures second → evidence.accepts outward required second)
    {contractDependencies : Dependencies} {contractPlan : Plan contractDependencies}
    {contractRows : Rows (signature contractPlan)}
    {privateDependencies : LexicalBounds → CallBounds world → Dependencies}
    {privatePlans : ∀ lexical call, Plan (privateDependencies lexical call)}
    {privateRows : ∀ lexical call, Rows (signature (privatePlans lexical call))}
    (bodySource : ∀ nextLexical : LexicalBounds, ∀ call : CallBounds world,
      IndexedSource registry outward owners call.world requests .none
        ((environment.extend name replacementType).extend parameter input) code output bodyDemand bodyReq
        (privatePlans nextLexical call) (privateRows nextLexical call))
    (body : ∀ nextLexical : LexicalBounds, ∀ call : CallBounds world,
      LexicalBounds.Known nextLexical (Code.lambda parameter code).dependencies →
      ScopedPorts.Support.evaluate nextLexical.environment (Code.lambda parameter code).dependencies ⊆ call.receiver →
      Authenticated registry outward (bodySource nextLexical call) (nextLexical.extend parameter call.argument) call.receiver)
    (refinement : ∀ nextLexical : LexicalBounds, ∀ call : CallBounds world,
      LexicalBounds.Known nextLexical (Code.lambda parameter code).dependencies →
      ScopedPorts.Support.evaluate nextLexical.environment (Code.lambda parameter code).dependencies ⊆ call.receiver →
      ReceiverRefines contractRows (privateRows nextLexical call) call.receiver
        (ScopedPorts.Support.evaluate (nextLexical.extend parameter call.argument).environment code.dependencies))
    (bodyIH : ∀ nextLexical : LexicalBounds, ∀ call : CallBounds world,
      ∀ _known : LexicalBounds.Known nextLexical (Code.lambda parameter code).dependencies,
      ∀ _received : ScopedPorts.Support.evaluate nextLexical.environment (Code.lambda parameter code).dependencies ⊆ call.receiver,
      ∀ destination replacementName replacementInput replacementValue nextLexicalBase nextBound,
        (environment.extend name replacementType).extend parameter input = destination.extend replacementName replacementInput →
        (∀ n, Syntax.Dependency.variable n ∈ code.dependencies → (nextLexical.extend parameter call.argument).lookup n = (nextLexicalBase.extend replacementName nextBound).lookup n) →
        (replacement : IndexedSource registry outward owners call.world requests .none destination replacementValue replacementInput [] (.request [] []) .pure Rows.pure) →
        ClosedValue replacementValue → Syntax.resourceDependencies replacementValue.dependencies ⊆ nextBound →
        (Syntax.Dependency.variable replacementName ∈ code.dependencies → Authenticated registry outward replacement nextLexicalBase call.receiver) →
        ∃ nextPlan : Plan (privateDependencies nextLexical call), ∃ nextRows : Rows (signature nextPlan),
          ∃ nextSource : IndexedSource registry outward owners call.world requests .none destination (code.subst replacementName replacementValue) output bodyDemand bodyReq nextPlan nextRows,
          Authenticated registry outward nextSource nextLexicalBase call.receiver ∧
          nextPlan = CoreCallablePlanSubstitution.plan code (privatePlans nextLexical call) replacementName replacementValue ∧
          signature nextPlan = signature (privatePlans nextLexical call) ∧ HEq nextRows (privateRows nextLexical call))
    (bodyOutward : RecursiveOutward.Outward bodyReq (some latent))
    (latentBound : ∀ request ∈ latent, request.effect ∈ requests)
    (publicCertified : Certified outward world contractPlan)
    (formed : ScopedPorts.InWorld world (Contract.function input output requests latent contractPlan contractRows).port)
    (known : LexicalBounds.Known sourceLexical (Code.lambda parameter code).dependencies)
    (sameLexical : ∀ n, Syntax.Dependency.variable n ∈ (Code.lambda parameter code).dependencies → sourceLexical.lookup n = (lexical.extend name valueBound).lookup n)
    (replacement : IndexedSource registry outward owners world allowed scope environment value replacementType [] (.request [] []) .pure Rows.pure)
    (closed : ClosedValue value)
    (authReplacement : Syntax.Dependency.variable name ∈ (Code.lambda parameter code).dependencies → Authenticated registry outward replacement lexical receiver) :
    ∃ nextSource : IndexedSource registry outward owners world allowed scope environment
      ((Code.lambda parameter code).subst name value) (Contract.function input output requests latent contractPlan contractRows) [] (.request [] []) .pure Rows.pure,
      Hereditary registry outward nextSource lexical receiver := by
  by_cases shadow : name = parameter
  · subst name
    have typeAgree : ∀ n, Syntax.Dependency.variable n ∈ code.dependencies →
        (environment.extend parameter replacementType).extend parameter input n = environment.extend parameter input n := by
      intro n _; by_cases same : n = parameter <;> simp [Environment.extend, same]
    let changedSource := fun nextLexical call => (bodySource nextLexical call).environment_congr typeAgree
    have currentKnown : LexicalBounds.Known lexical (Code.lambda parameter code).dependencies := by
      intro n mem
      have unequal : n ≠ parameter := by
        have absent := (Syntax.mem_without.mp mem).2
        simpa using absent
      obtain ⟨resources, found⟩ := known n mem
      exact ⟨resources, by simpa [lexical_lookup_extend, unequal] using (sameLexical n mem).symm.trans found⟩
    refine ⟨by simpa only [Code.subst, ↓reduceIte] using IndexedSource.receiverLambda changedSource bodyOutward latentBound publicCertified formed, ?_⟩
    simpa only [Code.subst, ↓reduceIte] using
      (Hereditary.receiverLambda (bodySource := changedSource) bodyOutward latentBound publicCertified formed currentKnown
        (fun nextLexical call known received =>
          (body nextLexical call known received).environment_congr typeAgree (changedSource nextLexical call)) refinement)
  · let actual := Syntax.resourceDependencies value.dependencies
    let originalLexical := fun nextLexical : LexicalBounds => nextLexical.extend name actual
    let changedPlans := fun nextLexical call => CoreCallablePlanSubstitution.plan code (privatePlans (originalLexical nextLexical) call) name value
    let changedRows := fun nextLexical call =>
      (CoreCallablePlanSubstitution.plan_signature code (privatePlans (originalLexical nextLexical) call) name closed.1).symm ▸ privateRows (originalLexical nextLexical) call
    let replacementAt := fun call : CallBounds world =>
      (((replacement.world_weaken call.worldExtended).value_allowed closed.1 requests .none).closed_environment closed (environment.extend parameter input))
    let changedSource : ∀ nextLexical : LexicalBounds, ∀ call : CallBounds world,
        IndexedSource registry outward owners call.world requests .none (environment.extend parameter input)
          (code.subst name value) output bodyDemand bodyReq (changedPlans nextLexical call) (changedRows nextLexical call) := by
      intro nextLexical call
      obtain ⟨nextPlan, nextRows, nextSource, exactPlan, sameSignature, aligned⟩ :=
        (bodySource (originalLexical nextLexical) call).substitution_reannotated_at stable
          (environment.extend parameter input) name replacementType value
          (Environment.extend_commute environment name parameter replacementType input shadow) (replacementAt call) closed
      cases exactPlan
      have alignedChanged : HEq nextRows (changedRows nextLexical call) := aligned.trans
        (cast_rows_heq (CoreCallablePlanSubstitution.plan_signature _ _ name closed.1) _).symm
      cases eq_of_heq alignedChanged
      exact nextSource
    have currentKnown : LexicalBounds.Known lexical ((Code.lambda parameter code).subst name value).dependencies := by
      apply known_substitution_remove (value := value) (resources := valueBound) ?_ closed
      intro n mem
      obtain ⟨resources, found⟩ := known n mem
      exact ⟨resources, (sameLexical n mem).symm.trans found⟩
    have callFacts : ∀ nextLexical : LexicalBounds, ∀ call : CallBounds world,
        LexicalBounds.Known nextLexical ((Code.lambda parameter code).subst name value).dependencies →
        ScopedPorts.Support.evaluate nextLexical.environment ((Code.lambda parameter code).subst name value).dependencies ⊆ call.receiver →
        LexicalBounds.Known (originalLexical nextLexical) (Code.lambda parameter code).dependencies ∧
        ScopedPorts.Support.evaluate (originalLexical nextLexical).environment (Code.lambda parameter code).dependencies ⊆ call.receiver := by
      intro nextLexical call known received
      exact ⟨known_substitution_restore known closed,
        by simpa only [originalLexical, actual, LexicalBounds.environment_extend] using
          (substitution_support_reverse (environment := nextLexical.environment) (Code.lambda parameter code) name closed).trans received⟩
    have changedAuth : ∀ nextLexical : LexicalBounds, ∀ call : CallBounds world,
        LexicalBounds.Known nextLexical ((Code.lambda parameter code).subst name value).dependencies →
        ScopedPorts.Support.evaluate nextLexical.environment ((Code.lambda parameter code).subst name value).dependencies ⊆ call.receiver →
        Authenticated registry outward (changedSource nextLexical call) (nextLexical.extend parameter call.argument) call.receiver := by
      intro nextLexical call known received
      obtain ⟨oldKnown, oldReceived⟩ := callFacts nextLexical call known received
      have lexicalAgree : ∀ n, Syntax.Dependency.variable n ∈ code.dependencies →
          ((originalLexical nextLexical).extend parameter call.argument).lookup n = ((nextLexical.extend parameter call.argument).extend name actual).lookup n := by
        intro n _
        by_cases same : n = parameter
        · subst n; simp [originalLexical, lexical_lookup_extend, Ne.symm shadow]
        · simp [originalLexical, lexical_lookup_extend, same]
      have replacementAuth : Syntax.Dependency.variable name ∈ code.dependencies →
          Authenticated registry outward (replacementAt call) (nextLexical.extend parameter call.argument) call.receiver := by
        intro occurs
        have captured : Syntax.Dependency.variable name ∈ (Code.lambda parameter code).dependencies :=
          Syntax.mem_without.mpr ⟨occurs, by simpa using shadow⟩
        have actualReceived : actual ⊆ call.receiver := by
          intro identity member
          apply oldReceived
          exact List.mem_flatMap.mpr ⟨.variable name, captured, by
            simp only [originalLexical, LexicalBounds.environment, lexical_lookup_extend, ↓reduceIte, Option.getD_some]
            exact member⟩
        apply (((authReplacement captured).value_world_weaken closed.1 call.worldExtended).value_allowed closed.1 requests .none).closed_environment closed _ |>.value_reauthenticate closed
        rw [closed_evaluation closed]
        exact actualReceived
      obtain ⟨nextPlan, nextRows, nextSource, auth, exactPlan, sameSignature, aligned⟩ := bodyIH
        (originalLexical nextLexical) call oldKnown oldReceived (environment.extend parameter input) name replacementType value
        (nextLexical.extend parameter call.argument) actual
        (Environment.extend_commute environment name parameter replacementType input shadow) lexicalAgree (replacementAt call) closed (List.Subset.refl _) replacementAuth
      cases exactPlan
      have alignedChanged : HEq nextRows (changedRows nextLexical call) := aligned.trans
        (cast_rows_heq (CoreCallablePlanSubstitution.plan_signature _ _ name closed.1) _).symm
      cases eq_of_heq alignedChanged
      exact auth
    have changedRefinement : ∀ nextLexical : LexicalBounds, ∀ call : CallBounds world,
        LexicalBounds.Known nextLexical ((Code.lambda parameter code).subst name value).dependencies →
        ScopedPorts.Support.evaluate nextLexical.environment ((Code.lambda parameter code).subst name value).dependencies ⊆ call.receiver →
        ReceiverRefines contractRows (changedRows nextLexical call) call.receiver
          (ScopedPorts.Support.evaluate (nextLexical.extend parameter call.argument).environment (code.subst name value).dependencies) := by
      intro nextLexical call known received
      obtain ⟨oldKnown, oldReceived⟩ := callFacts nextLexical call known received
      exact refinement_rows (refinement (originalLexical nextLexical) call oldKnown oldReceived)
        (CoreCallablePlanSubstitution.plan_signature _ _ name closed.1) (cast_rows_heq (CoreCallablePlanSubstitution.plan_signature _ _ name closed.1) _)
        (SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.bounds_iff.mp
          (body (originalLexical nextLexical) call oldKnown oldReceived).current_support)
    refine ⟨by simpa only [Code.subst, if_neg shadow] using IndexedSource.receiverLambda changedSource bodyOutward latentBound publicCertified formed, ?_⟩
    simpa only [Code.subst, if_neg shadow] using
      (Hereditary.receiverLambda (bodySource := changedSource) bodyOutward latentBound publicCertified formed
        (by simpa only [Code.subst, if_neg shadow] using currentKnown)
        (by simpa only [Code.subst, if_neg shadow] using changedAuth)
        (by simpa only [Code.subst, if_neg shadow] using changedRefinement))
end
end Ash.OneShot.CoreCallableContractAdmission

#print axioms Ash.OneShot.CoreCallableContractAdmission.lambda_hereditary_substitution
