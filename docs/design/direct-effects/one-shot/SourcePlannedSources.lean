import SourcePlannedSubstitution

/-! One structural derivation chooses intermediate value types, effects,
requirements and stable checking signatures together. Its projections reuse
both previous source layers; their separate existence is not a constructor. -/
namespace Ash.OneShot.SourcePlannedSources
open ScopedExpressions ScopedExecution ProtectionContracts
open RecursiveRequirements (Requirements)
open SourceDependencyAnnotations (Dependencies ClauseDependencies)
open SourcePlannedTyping (Value Environment Operations Contract Contracts)
open SourceDeclarationPlans (Plan ModePlans ClausePlans)
open SourcePlanSignatures (Signature signature clauseSignatures)

mutual
inductive Expression (operations : Operations) (policy : Syntax.TicketPolicy) :
    Contracts → List Nat → List Instance → Execution.Scope → Environment → Code → Value →
      (demand : List Nat) → Requirements demand → {dependencies : Dependencies} → Signature dependencies → Prop where
  | unit : Expression operations policy contracts world allowed scope environment .unit .unit [] (.request [] []) .pure
  | boolean : Expression operations policy contracts world allowed scope environment (.boolean value) .boolean [] (.request [] []) .pure
  | integer : Expression operations policy contracts world allowed scope environment (.integer value) .integer [] (.request [] []) .pure
  | reference (issued : identity ∈ world) :
      Expression operations policy contracts world allowed scope environment (.resourceRef (.activation identity))
        (.reference identity) [] (.request [] []) .pure
  | variable (known : environment name = some value) (formed : ScopedPorts.InWorld world value.erase.erase.port) :
      Expression operations policy contracts world allowed scope environment (.variable name) value [] (.request [] []) .pure
  | lambda (body : Expression operations policy contracts world requests .none
        (environment.extend parameter input) code output bodyDemand bodyRequirements dependencies)
      (outward : RecursiveOutward.Outward bodyRequirements (some latent))
      (formed : ScopedPorts.InWorld world (CoherentSourceTypes.Value.function input.erase.erase output.erase.erase requests latent).port)
      (latentBound : ∀ request ∈ latent, request.effect ∈ requests) :
      Expression operations policy contracts world allowed scope environment (.lambda parameter code)
        (.function input output requests latent dependencies) [] (.request [] []) .pure
  | purePair (left : Expression operations policy contracts world allowed scope environment a first [] (.request [] []) .pure)
      (right : Expression operations policy contracts world allowed scope environment b second [] (.request [] []) .pure) :
      Expression operations policy contracts world allowed scope environment (.pair a b) (.pair first second) [] (.request [] []) .pure
  | pair (left : Expression operations policy contracts world allowed scope environment a first leftDemand leftReq leftDep)
      (right : Expression operations policy contracts world allowed scope environment b second rightDemand rightReq rightDep) :
      Expression operations policy contracts world allowed scope environment (.pair a b) (.pair first second)
        (leftDemand ++ rightDemand) (.sequence leftReq rightReq) (.sequence leftDep rightDep)
  | app (function : Expression operations policy contracts world allowed scope environment f
        (.function input output requests latent dependencies) functionDemand functionReq functionDep)
      (argument : Expression operations policy contracts world allowed scope environment a input argumentDemand argumentReq argumentDep)
      (admitted : requests ⊆ allowed) :
      Expression operations policy contracts world allowed scope environment (.app f a) output
        (functionDemand ++ argumentDemand) (.emitAfter (.sequence functionReq argumentReq) [] latent)
        (.sequence functionDep (.sequence argumentDep dependencies))
  | bind (initializer : Expression operations policy contracts world allowed scope environment a input initialDemand initialReq initialDep)
      (body : Expression operations policy contracts world allowed scope (environment.extend parameter input) b output bodyDemand bodyReq bodyDep) :
      Expression operations policy contracts world allowed scope environment (.bind parameter a b) output
        (initialDemand ++ bodyDemand) (.sequence initialReq bodyReq) (.sequence initialDep bodyDep)
  | branch (condition : Expression operations policy contracts world allowed scope environment test .boolean conditionDemand conditionReq conditionDep)
      (yes : Expression operations policy contracts world allowed scope environment a output yesDemand yesReq yesDep)
      (no : Expression operations policy contracts world allowed scope environment b output noDemand noReq noDep)
      (same : yesDemand.Perm noDemand) :
      Expression operations policy contracts world allowed scope environment (.branch test a b) output
        (conditionDemand ++ yesDemand) (.sequence conditionReq (.choice yesReq noReq same))
        (.sequence conditionDep (.choice yesDep noDep))
  | perform (known : operations effect operation = some (input, output)) (admitted : effect ∈ allowed)
      (operand : Expression operations policy contracts world allowed scope environment value input operandDemand operandReq operandDep)
      (formed : ScopedPorts.InWorld world output.erase.erase.port) :
      Expression operations policy contracts world allowed scope environment (.perform (Instantiation.freezeEffect effect) operation value)
        output operandDemand (.emitAfter operandReq [] [⟨effect, operation, false⟩])
        (.sequence operandDep (.request (effect := effect) (operation := operation)))
  | handler {plans : ClausePlans arms families} (body : Expression operations policy contracts world (effect :: residual) scope environment
        code answer demand requirements dependencies)
      (clauses : ScopedPorts.ClausesTyped operations.erase.erase.ports world environment.erase.erase.ports effect answer.erase.erase.port residual arms)
      (capabilities : ClausesUse policy arms)
      (coverage : ScopedPorts.Covers operations.erase.erase.ports effect arms)
      (unique : (ScopedTyping.clauseKeys arms).Nodup) (admitted : residual ⊆ allowed)
      (table : List (Nat × ClauseContract)) (modes : SourceTemplates.ClauseModes arms table)
      (declarations : Declarations operations policy contracts world environment residual effect answer arms table plans) :
      Expression operations policy contracts world allowed scope environment
        (.handle (Instantiation.freezeEffect effect) code arms) answer demand
        (requirements.prepend [.ordinary (.handler effect 0 table)]) (.handler (effect := effect) (table := table) required (clauseSignatures plans) dependencies)
  | resume (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner)
      (permission : (policy binder).resume = true)
      (operand : Expression operations policy contracts world allowed scope environment value contract.input operandDemand operandReq operandDep)
      (admitted : contract.resumeEffects ⊆ allowed) (formed : ScopedPorts.InWorld world contract.answer.erase.erase.port) :
      Expression operations policy contracts world allowed scope environment (.resume binder value) contract.answer
        (operandDemand ++ owner :: contract.resumeDemand) (.sequence operandReq (.invoke ⟨owner, .resume⟩ contract.resumeDemand []))
        (.sequence operandDep (.invoke (key := ⟨owner, .resume⟩)))
  | discard (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner)
      (permission : (policy binder).dispose = true) (unprotected : contract.held = false)
      (admitted : contract.closeEffects ⊆ allowed) :
      Expression operations policy contracts world allowed scope environment (.discard binder) .unit
        (owner :: contract.closeDemand) (.invoke ⟨owner, .dispose⟩ contract.closeDemand []) (.invoke (key := ⟨owner, .dispose⟩))
  | cleanup (callback : Expression operations policy contracts world allowed scope environment action
        (.function .unit .unit requests latent callbackBody) callbackDemand callbackReq callbackDep)
      (body : Expression operations policy contracts world allowed scope environment code output bodyDemand bodyReq bodyDep)
      (admitted : requests ⊆ allowed) :
      Expression operations policy contracts world allowed scope environment (.cleanup action code) output
        (callbackDemand ++ bodyDemand) (.emitAfter (.sequence callbackReq bodyReq) [] (qualify true latent))
        (.sequence callbackDep (.cleanup (needs := requests) callbackBody bodyDep))
  | resource {bodyRequirements : Nat → Requirements bodyDemand} {bodyDependencies : Nat → Dependencies} {bodySignatures : ∀ identity, Signature (bodyDependencies identity)}
      (initializer : Expression operations policy contracts world allowed scope environment initial .integer initialDemand initialRequirements initialDep)
      (body : ∀ identity, identity ∉ world → Expression operations policy contracts (world ++ [identity])
        (.cell identity :: residual) scope environment
        (code.instantiate (Instantiation.Environment.empty.bind binder identity)) output bodyDemand (bodyRequirements identity) (bodySignatures identity))
      (formed : ScopedPorts.InWorld world output.erase.erase.port)
      (effectsBound : residual.flatMap Instance.resources ⊆ world) (admitted : residual ⊆ allowed)
      (hidden : ∀ identity, identity ∉ world → ResourceRequirements.Hides identity (bodyRequirements identity) outward) :
      Expression operations policy contracts world allowed scope environment (.resource binder initial code)
        output (initialDemand ++ bodyDemand) (.sequence initialRequirements outward)
        (.sequence initialDep (.resource bodySignatures))

inductive Body (operations : Operations) (policy : Syntax.TicketPolicy) :
    Contracts → List Nat → List Instance → Execution.Scope → Environment → Code → Value → ClauseRowAdmission.Header → {dependencies : Dependencies} → Signature dependencies → Prop where
  | typed (source : Expression operations policy contracts world allowed scope environment code answer demand requirements dependencies)
      (rows : ClauseRowAdmission.Rows header requirements (ClauseRowAdmission.SourceStore operations.erase.erase header.owner header.contract))
      (closingRows : ClauseRowAdmission.ProtectedRows header requirements (ClauseRowAdmission.SourceStore operations.erase.erase header.owner header.contract)) :
      Body operations policy contracts world allowed scope environment code answer header dependencies

inductive Offer (operations : Operations) (policy : Syntax.TicketPolicy) :
    Contracts → List Nat → Environment → List Instance → Nat → Nat → Value → Value → Value →
      List Instance → List Instance → Code → Bool → Bool → Option Footprint → {family : Option (Nat → Dependencies)} → ModePlans family → Prop where
  | unavailable : Offer operations policy contracts world environment allowed parameter binder argument input answer
      resumeEffects closeEffects code held disposes none .unavailable
  | available
      (resumeInterface : code.requiredActions.resume = true → resumeEffects = allowed)
      (closeInterface : code.requiredActions.dispose = true → closeEffects = allowed)
      (source : ∀ owner (contract : Contract), contracts owner = none →
        contract.input = input → contract.answer = answer →
        contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
        contract.held = held → contract.closeDemand.Perm contract.resumeDemand →
        Body operations policy (contracts.insert owner contract) world allowed (.ticket binder owner)
          (environment.extend parameter argument) code answer ⟨owner, contract.erase.erase, disposes, row⟩ (signature (plans owner))) :
      Offer operations policy contracts world environment allowed parameter binder argument input answer
        resumeEffects closeEffects code held disposes (some row) (.available plans)

inductive Declarations (operations : Operations) (policy : Syntax.TicketPolicy) :
    Contracts → List Nat → Environment → List Instance → Instance → Value → (clauses : Clauses) →
      List (Nat × ClauseContract) → {families : ClauseDependencies} → ClausePlans clauses families → Prop where
  | nil : Declarations operations policy contracts world environment allowed requested answer .nil [] .nil
  | cons (known : operations requested operation = some (argument, input))
      (ordinary : Offer operations policy contracts world environment allowed parameter binder argument input answer
        resumeEffects closeEffects body false dispose ordinaryRow ordinaryPlan)
      (protectedMode : Offer operations policy contracts world environment allowed parameter binder argument input answer
        resumeEffects closeEffects body true dispose protectedRow protectedPlan)
      (rest : Declarations operations policy contracts world environment allowed requested answer clauses table restPlan) :
      Declarations operations policy contracts world environment allowed requested answer
        (.cons operation parameter binder body clauses)
        ((operation, ⟨dispose, ordinaryRow, protectedRow⟩) :: table)
        (.cons ordinaryPlan protectedPlan restPlan)
end

/-- Refine an existing continuation contract at the already selected stable
input and answer annotations. All ownership and effect fields are reused. -/
def refineContract (contract : SourceDependencyAnnotations.Contract) (input answer : Value) : Contract :=
  ⟨input, answer, contract.held, contract.resumeDemand, contract.resumeRow,
    contract.closeDemand, contract.closeRow, contract.resumeEffects, contract.closeEffects⟩

theorem refine_contract_erase (inputSame : contract.input = input.erase)
    (answerSame : contract.answer = answer.erase) : (refineContract contract input answer).erase = contract := by
  cases contract
  cases inputSame
  cases answerSame
  rfl

theorem operation_erase (known : operations effect operation = some (input, output)) :
    Operations.erase operations effect operation = some (input.erase, output.erase) := by
  simp [Operations.erase, known]

theorem contract_erase_known (known : contracts owner = some contract) :
    Contracts.erase contracts owner = some contract.erase := by
  simp [Contracts.erase, known]

/-- Forget only the stable signature refinement. Each recursive source premise
uses the same intermediate type, requirement and owner indices as its parent. -/
theorem expression_erase {checking : Signature dependencies}
    (source : Expression operations policy contracts world allowed scope environment code value demand requirements checking) :
    SourceDependencyAnnotations.Expression operations.erase policy contracts.erase world allowed scope environment.erase
      code value.erase demand requirements dependencies := by
  induction source using Expression.rec
    (motive_2 := fun contracts world allowed scope environment code value header dependencies _ _ =>
      SourceDependencyAnnotations.Body operations.erase policy contracts.erase world allowed scope environment.erase
        code value.erase header dependencies)
    (motive_3 := fun contracts world environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row family _ _ =>
      SourceDependencyAnnotations.Offer operations.erase policy contracts.erase world environment.erase allowed parameter binder
        argument.erase input.erase answer.erase resumeEffects closeEffects code held disposes row family)
    (motive_4 := fun contracts world environment allowed requested answer clauses table families _ _ =>
      SourceDependencyAnnotations.Declarations operations.erase policy contracts.erase world environment.erase allowed requested
        answer.erase clauses table families) with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference issued => exact .reference issued
  | «variable» known formed => exact .variable (by simp [Environment.erase, known]) formed
  | lambda body outward formed latentBound ih =>
      exact .lambda (by simpa only [SourcePlannedTyping.environment_erase_extend] using ih) outward formed latentBound
  | purePair left right ihLeft ihRight => exact .purePair ihLeft ihRight
  | pair left right ihLeft ihRight => exact .pair ihLeft ihRight
  | app function argument admitted ihFunction ihArgument => exact .app ihFunction ihArgument admitted
  | bind initializer body ihInit ihBody =>
      exact .bind ihInit (by simpa only [SourcePlannedTyping.environment_erase_extend] using ihBody)
  | branch condition yes no same ihCondition ihYes ihNo => exact .branch ihCondition ihYes ihNo same
  | perform known admitted operand formed ih => exact .perform (operation_erase known) admitted ih formed
  | handler body clauses capabilities coverage unique admitted table modes declarations ihBody ihDecl =>
      exact .handler ihBody clauses capabilities coverage unique admitted table modes ihDecl
  | resume known resolved permission operand admitted formed ih => exact .resume (contract_erase_known known) resolved permission ih admitted formed
  | discard known resolved permission unprotected admitted => exact .discard (contract_erase_known known) resolved permission unprotected admitted
  | cleanup callback body admitted ihCallback ihBody => exact .cleanup ihCallback ihBody admitted
  | resource initializer body formed effectsBound admitted hidden ihInit ihBody =>
      exact .resource ihInit ihBody formed effectsBound admitted hidden
  | typed source rows closingRows ih => exact .typed ih rows
  | unavailable => exact .unavailable
  | available resumeInterface closeInterface source ih =>
      apply SourceDependencyAnnotations.Offer.available resumeInterface closeInterface
      intro owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
      have result := ih owner (refineContract contract _ _) (Option.map_eq_none_iff.mp fresh)
        rfl rfl resumeSame closeSame heldSame balance
      simpa only [SourcePlannedTyping.contracts_erase_insert, SourcePlannedTyping.environment_erase_extend,
        refine_contract_erase inputSame answerSame] using result
  | nil => exact .nil
  | cons known ordinary protectedMode rest ihOrdinary ihProtected ihRest =>
      exact .cons (operation_erase known) ihOrdinary ihProtected ihRest

/-- The same structural derivation also supplies the prior annotation proof;
no second selection of intermediate value types is made. -/
theorem expression_annotation
    (source : Expression operations policy contracts world allowed scope environment code value demand requirements checking) :
    SourcePlannedTyping.Annotation operations contracts world scope environment code value checking := by
  induction source using Expression.rec
    (motive_2 := fun contracts world _ scope environment code value _ _ checking _ =>
      SourcePlannedTyping.Annotation operations contracts world scope environment code value checking)
    (motive_3 := fun contracts world environment _ parameter binder argument input answer resumeEffects closeEffects code held _ _ _ plans _ =>
      SourcePlannedTyping.Offer operations contracts world environment parameter binder argument input answer resumeEffects closeEffects code held plans)
    (motive_4 := fun contracts world environment _ requested answer _ _ _ plans _ =>
      SourcePlannedTyping.Declarations operations contracts world environment requested answer plans) with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference issued => exact .reference
  | «variable» known formed => exact .variable known
  | lambda body outward formed latentBound ih => exact .lambda ih
  | purePair left right ihLeft ihRight => exact .purePair ihLeft ihRight
  | pair left right ihLeft ihRight => exact .pair ihLeft ihRight
  | app function argument admitted ihFunction ihArgument => exact .app ihFunction ihArgument
  | bind initializer body ihInit ihBody => exact .bind ihInit ihBody
  | branch condition yes no same ihCondition ihYes ihNo => exact .branch ihCondition ihYes ihNo
  | perform known admitted operand formed ih => exact .perform known ih
  | handler body clauses capabilities coverage unique admitted table modes declarations ihBody ihDecl => exact .handler ihBody ihDecl
  | resume known resolved permission operand admitted formed ih => exact .resume known resolved ih
  | discard known resolved permission unprotected admitted => exact .discard known resolved
  | cleanup callback body admitted ihCallback ihBody => exact .cleanup ihCallback ihBody
  | resource initializer body formed effectsBound admitted hidden ihInit ihBody => exact .resource ihInit ihBody
  | typed source rows closingRows ih => exact ih
  | unavailable => exact .unavailable
  | available resumeInterface closeInterface source ih => exact .available ih
  | nil => exact .nil
  | cons known ordinary protectedMode rest ihOrdinary ihProtected ihRest => exact .cons known ihOrdinary ihProtected ihRest

theorem Expression.paired
    (source : Expression operations policy contracts world allowed scope environment code value demand requirements checking) :
    SourcePlannedTyping.Typed operations policy contracts world allowed scope environment code value demand requirements checking :=
  ⟨expression_erase source, expression_annotation source⟩

/-- Handler decomposition retains the same full body and declaration proofs.
The actual clause witness is authenticated before any frame is installed. -/
theorem handler_body {declarationsSignature : SourcePlanSignatures.ClauseSignatures families}
    (source : Expression operations policy contracts world allowed scope environment
      (.handle (Instantiation.freezeEffect effect) code arms) answer demand requirements
      (.handler (effect := effect) (table := table) required declarationsSignature bodySignature)) :
    ∃ residual, ∃ bodyRequirements : Requirements demand, ∃ plans : ClausePlans arms families,
      Expression operations policy contracts world (effect :: residual) scope environment code answer demand bodyRequirements bodySignature ∧
      Declarations operations policy contracts world environment residual effect answer arms table plans ∧
      clauseSignatures plans = declarationsSignature ∧
      requirements = bodyRequirements.prepend [.ordinary (.handler effect 0 table)] := by
  generalize frozen : Instantiation.freezeEffect effect = actualEffect at source
  cases source with
  | handler body clauses capabilities coverage unique admitted table modes declarations =>
      exact ⟨_, _, _, body, declarations, rfl, rfl⟩

end Ash.OneShot.SourcePlannedSources

#print axioms Ash.OneShot.SourcePlannedSources.refine_contract_erase
#print axioms Ash.OneShot.SourcePlannedSources.operation_erase
#print axioms Ash.OneShot.SourcePlannedSources.contract_erase_known
#print axioms Ash.OneShot.SourcePlannedSources.expression_erase
#print axioms Ash.OneShot.SourcePlannedSources.expression_annotation
#print axioms Ash.OneShot.SourcePlannedSources.Expression.paired

#print axioms Ash.OneShot.SourcePlannedSources.handler_body
