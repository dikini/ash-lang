import SourceAnnotatedNames

/-! Rich source checking retains annotated nodes and checks every selected
intermediate type against that node's finite hint. Recursive rules keep the
existing source types, effects, requirements, signatures and continuation modes.
Erasure forgets metadata checks and reuses the existing rich source judgment.
No constructor assumes a successor state or successful future execution. -/
namespace Ash.OneShot.SourceAnnotatedSources
open ScopedExecution ProtectionContracts
open ScopedExpressions (ClausesUse)
open SourceAnnotatedCode (Term)
open RecursiveRequirements (Requirements)
open SourceDependencyAnnotations (Dependencies ClauseDependencies)
open SourcePlannedTyping (Value Environment Operations Contract Contracts)
open SourceDeclarationPlans (Plan ModePlans ClausePlans)
open SourcePlanSignatures (Signature signature clauseSignatures)

mutual
inductive Expression (operations : Operations) (policy : Syntax.TicketPolicy) :
    Contracts → List Nat → List Instance → Execution.Scope → Environment → Term → Value →
      (demand : List Nat) → Requirements demand → {dependencies : Dependencies} → Signature dependencies → Prop where
  | checked
      (hint : SourceFocusHints.checkSource Instantiation.Environment.empty code.hint value = true)
      (closed : code.checkClosed = true)
      (node : Node operations policy contracts world allowed scope environment code value demand requirements checking) :
      Expression operations policy contracts world allowed scope environment code value demand requirements checking

inductive Node (operations : Operations) (policy : Syntax.TicketPolicy) :
    Contracts → List Nat → List Instance → Execution.Scope → Environment → Term → Value →
      (demand : List Nat) → Requirements demand → {dependencies : Dependencies} → Signature dependencies → Prop where
  | unit : Node operations policy contracts world allowed scope environment (.unit hint) .unit [] (.request [] []) .pure
  | boolean : Node operations policy contracts world allowed scope environment (.boolean hint value) .boolean [] (.request [] []) .pure
  | integer : Node operations policy contracts world allowed scope environment (.integer hint value) .integer [] (.request [] []) .pure
  | reference (issued : identity ∈ world) :
      Node operations policy contracts world allowed scope environment (.resourceRef hint (.activation identity))
        (.reference identity) [] (.request [] []) .pure
  | variable (known : environment name = some value) (formed : ScopedPorts.InWorld world value.erase.erase.port) :
      Node operations policy contracts world allowed scope environment (.variable hint name) value [] (.request [] []) .pure
  | lambda (body : Expression operations policy contracts world requests .none
        (environment.extend parameter input) code output bodyDemand bodyRequirements dependencies)
      (outward : RecursiveOutward.Outward bodyRequirements (some latent))
      (formed : ScopedPorts.InWorld world (CoherentSourceTypes.Value.function input.erase.erase output.erase.erase requests latent).port)
      (latentBound : ∀ request ∈ latent, request.effect ∈ requests) :
      Node operations policy contracts world allowed scope environment (.lambda hint parameter code)
        (.function input output requests latent dependencies) [] (.request [] []) .pure
  | purePair (left : Expression operations policy contracts world allowed scope environment a first [] (.request [] []) .pure)
      (right : Expression operations policy contracts world allowed scope environment b second [] (.request [] []) .pure) :
      Node operations policy contracts world allowed scope environment (.pair hint a b) (.pair first second) [] (.request [] []) .pure
  | pair (left : Expression operations policy contracts world allowed scope environment a first leftDemand leftReq leftDep)
      (right : Expression operations policy contracts world allowed scope environment b second rightDemand rightReq rightDep) :
      Node operations policy contracts world allowed scope environment (.pair hint a b) (.pair first second)
        (leftDemand ++ rightDemand) (.sequence leftReq rightReq) (.sequence leftDep rightDep)
  | app (function : Expression operations policy contracts world allowed scope environment f
        (.function input output requests latent dependencies) functionDemand functionReq functionDep)
      (argument : Expression operations policy contracts world allowed scope environment a input argumentDemand argumentReq argumentDep)
      (admitted : requests ⊆ allowed) :
      Node operations policy contracts world allowed scope environment (.app hint f a) output
        (functionDemand ++ argumentDemand) (.emitAfter (.sequence functionReq argumentReq) [] latent)
        (.sequence functionDep (.sequence argumentDep dependencies))
  | bind (initializer : Expression operations policy contracts world allowed scope environment a input initialDemand initialReq initialDep)
      (body : Expression operations policy contracts world allowed scope (environment.extend parameter input) b output bodyDemand bodyReq bodyDep) :
      Node operations policy contracts world allowed scope environment (.bind hint parameter a b) output
        (initialDemand ++ bodyDemand) (.sequence initialReq bodyReq) (.sequence initialDep bodyDep)
  | branch (condition : Expression operations policy contracts world allowed scope environment test .boolean conditionDemand conditionReq conditionDep)
      (yes : Expression operations policy contracts world allowed scope environment a output yesDemand yesReq yesDep)
      (no : Expression operations policy contracts world allowed scope environment b output noDemand noReq noDep)
      (same : yesDemand.Perm noDemand) :
      Node operations policy contracts world allowed scope environment (.branch hint test a b) output
        (conditionDemand ++ yesDemand) (.sequence conditionReq (.choice yesReq noReq same))
        (.sequence conditionDep (.choice yesDep noDep))
  | perform (known : operations effect operation = some (input, output)) (admitted : effect ∈ allowed)
      (operand : Expression operations policy contracts world allowed scope environment value input operandDemand operandReq operandDep)
      (formed : ScopedPorts.InWorld world output.erase.erase.port) :
      Node operations policy contracts world allowed scope environment (.perform hint (Instantiation.freezeEffect effect) operation value)
        output operandDemand (.emitAfter operandReq [] [⟨effect, operation, false⟩])
        (.sequence operandDep (.request (effect := effect) (operation := operation)))
  | handler {arms : SourceAnnotatedCode.Clauses} {plans : ClausePlans arms.erase families} (body : Expression operations policy contracts world (effect :: residual) scope environment
        code answer demand requirements dependencies)
      (clauses : ScopedPorts.ClausesTyped operations.erase.erase.ports world environment.erase.erase.ports effect answer.erase.erase.port residual arms.erase)
      (capabilities : ClausesUse policy arms.erase)
      (coverage : ScopedPorts.Covers operations.erase.erase.ports effect arms.erase)
      (unique : (ScopedTyping.clauseKeys arms.erase).Nodup) (admitted : residual ⊆ allowed)
      (table : List (Nat × ClauseContract)) (modes : SourceTemplates.ClauseModes arms.erase table)
      (declarations : Declarations operations policy contracts world environment residual effect answer arms table plans) :
      Node operations policy contracts world allowed scope environment
        (.handle hint (Instantiation.freezeEffect effect) code arms) answer demand
        (requirements.prepend [.ordinary (.handler effect 0 table)]) (.handler (effect := effect) (table := table) required (clauseSignatures plans) dependencies)
  | resume (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner)
      (permission : (policy binder).resume = true)
      (operand : Expression operations policy contracts world allowed scope environment value contract.input operandDemand operandReq operandDep)
      (admitted : contract.resumeEffects ⊆ allowed) (formed : ScopedPorts.InWorld world contract.answer.erase.erase.port) :
      Node operations policy contracts world allowed scope environment (.resume hint binder value) contract.answer
        (operandDemand ++ owner :: contract.resumeDemand) (.sequence operandReq (.invoke ⟨owner, .resume⟩ contract.resumeDemand []))
        (.sequence operandDep (.invoke (key := ⟨owner, .resume⟩)))
  | discard (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner)
      (permission : (policy binder).dispose = true) (unprotected : contract.held = false)
      (admitted : contract.closeEffects ⊆ allowed) :
      Node operations policy contracts world allowed scope environment (.discard hint binder) .unit
        (owner :: contract.closeDemand) (.invoke ⟨owner, .dispose⟩ contract.closeDemand []) (.invoke (key := ⟨owner, .dispose⟩))
  | cleanup (callback : Expression operations policy contracts world allowed scope environment action
        (.function .unit .unit requests latent callbackBody) callbackDemand callbackReq callbackDep)
      (body : Expression operations policy contracts world allowed scope environment code output bodyDemand bodyReq bodyDep)
      (admitted : requests ⊆ allowed) :
      Node operations policy contracts world allowed scope environment (.cleanup hint action code) output
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
      Node operations policy contracts world allowed scope environment (.resource hint binder initial code)
        output (initialDemand ++ bodyDemand) (.sequence initialRequirements outward)
        (.sequence initialDep (.resource bodySignatures))

inductive Body (operations : Operations) (policy : Syntax.TicketPolicy) :
    Contracts → List Nat → List Instance → Execution.Scope → Environment → Term → Value → ClauseRowAdmission.Header → {dependencies : Dependencies} → Signature dependencies → Prop where
  | typed (source : Expression operations policy contracts world allowed scope environment code answer demand requirements dependencies)
      (rows : ClauseRowAdmission.Rows header requirements (ClauseRowAdmission.SourceStore operations.erase.erase header.owner header.contract))
      (closingRows : ClauseRowAdmission.ProtectedRows header requirements (ClauseRowAdmission.SourceStore operations.erase.erase header.owner header.contract)) :
      Body operations policy contracts world allowed scope environment code answer header dependencies

inductive Offer (operations : Operations) (policy : Syntax.TicketPolicy) :
    Contracts → List Nat → Environment → List Instance → Nat → Nat → Value → Value → Value →
      List Instance → List Instance → Term → Bool → Bool → Option Footprint → {family : Option (Nat → Dependencies)} → ModePlans family → Prop where
  | unavailable : Offer operations policy contracts world environment allowed parameter binder argument input answer
      resumeEffects closeEffects code held disposes none .unavailable
  | available {code : Term}
      (resumeInterface : code.erase.requiredActions.resume = true → resumeEffects = allowed)
      (closeInterface : code.erase.requiredActions.dispose = true → closeEffects = allowed)
      (source : ∀ owner (contract : Contract), contracts owner = none →
        contract.input = input → contract.answer = answer →
        contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
        contract.held = held → contract.closeDemand.Perm contract.resumeDemand →
        Body operations policy (contracts.insert owner contract) world allowed (.ticket binder owner)
          (environment.extend parameter argument) code answer ⟨owner, contract.erase.erase, disposes, row⟩ (signature (plans owner))) :
      Offer operations policy contracts world environment allowed parameter binder argument input answer
        resumeEffects closeEffects code held disposes (some row) (.available plans)

inductive Declarations (operations : Operations) (policy : Syntax.TicketPolicy) :
    Contracts → List Nat → Environment → List Instance → Instance → Value → (clauses : SourceAnnotatedCode.Clauses) →
      List (Nat × ClauseContract) → {families : ClauseDependencies} → ClausePlans clauses.erase families → Prop where
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

theorem Expression.erase
    (source : Expression operations policy contracts world allowed scope environment code value demand requirements checking) :
    SourcePlannedSources.Expression operations policy contracts world allowed scope environment code.erase value demand requirements checking := by
  induction source using Expression.rec
    (motive_2 := fun contracts world allowed scope environment code value demand requirements dependencies checking _ =>
      SourcePlannedSources.Expression operations policy contracts world allowed scope environment
        code.erase value demand requirements checking)
    (motive_3 := fun contracts world allowed scope environment code value header dependencies checking _ =>
      SourcePlannedSources.Body operations policy contracts world allowed scope environment
        code.erase value header checking)
    (motive_4 := fun contracts world environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row family plan _ =>
      SourcePlannedSources.Offer operations policy contracts world environment allowed parameter binder
        argument input answer resumeEffects closeEffects code.erase held disposes row plan)
    (motive_5 := fun contracts world environment allowed requested answer clauses table families plans _ =>
      SourcePlannedSources.Declarations operations policy contracts world environment allowed requested
        answer clauses.erase table plans) with
  | checked hint closed node ih => exact ih
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference issued => exact .reference issued
  | «variable» known formed => exact .variable known formed
  | lambda body outward formed latentBound ih =>
      exact .lambda ih outward formed latentBound
  | purePair left right ihLeft ihRight => exact .purePair ihLeft ihRight
  | pair left right ihLeft ihRight => exact .pair ihLeft ihRight
  | app function argument admitted ihFunction ihArgument => exact .app ihFunction ihArgument admitted
  | bind initializer body ihInit ihBody =>
      exact .bind ihInit ihBody
  | branch condition yes no same ihCondition ihYes ihNo => exact .branch ihCondition ihYes ihNo same
  | perform known admitted operand formed ih => exact .perform known admitted ih formed
  | handler body clauses capabilities coverage unique admitted table modes declarations ihBody ihDecl =>
      exact .handler ihBody clauses capabilities coverage unique admitted table modes ihDecl
  | resume known resolved permission operand admitted formed ih => exact .resume known resolved permission ih admitted formed
  | discard known resolved permission unprotected admitted => exact .discard known resolved permission unprotected admitted
  | cleanup callback body admitted ihCallback ihBody => exact .cleanup ihCallback ihBody admitted
  | resource initializer body formed effectsBound admitted hidden ihInit ihBody =>
      exact .resource ihInit (fun identity fresh => by
        simpa only [Term.erase_instantiate] using ihBody identity fresh) formed effectsBound admitted hidden
  | typed source rows closingRows ih => exact .typed ih rows closingRows
  | unavailable => exact .unavailable
  | available resumeInterface closeInterface source ih =>
      exact .available resumeInterface closeInterface ih
  | nil => exact .nil
  | cons known ordinary protectedMode rest ihOrdinary ihProtected ihRest =>
      exact .cons known ihOrdinary ihProtected ihRest

theorem Body.erase
    (source : Body operations policy contracts world allowed scope environment code value header checking) :
    SourcePlannedSources.Body operations policy contracts world allowed scope environment code.erase value header checking := by
  cases source with
  | typed source rows closingRows => exact .typed source.erase rows closingRows


theorem Offer.erase
    (source : Offer operations policy contracts world environment allowed parameter binder argument input answer
      resumeEffects closeEffects code held disposes row plan) :
    SourcePlannedSources.Offer operations policy contracts world environment allowed parameter binder argument input answer
      resumeEffects closeEffects code.erase held disposes row plan := by
  cases source with
  | unavailable => exact .unavailable
  | available resumeInterface closeInterface source =>
      exact .available resumeInterface closeInterface (fun owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance =>
        (source owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance).erase)


theorem Declarations.erase
    (source : Declarations operations policy contracts world environment allowed requested answer clauses table plans) :
    SourcePlannedSources.Declarations operations policy contracts world environment allowed requested answer clauses.erase table plans := by
  induction source using Declarations.rec
    (motive_1 := fun _ _ _ _ _ _ _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ _ _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True) with
  | nil => exact .nil
  | cons known ordinary protectedMode rest ihOrdinary ihProtected ihRest =>
      exact .cons known ordinary.erase protectedMode.erase ihRest
  | checked | unit | boolean | integer | reference | «variable» | lambda | purePair | pair
    | app | bind | branch | perform | handler | resume | discard | cleanup | resource
    | typed | unavailable | available => trivial

theorem Node.erase
    (source : Node operations policy contracts world allowed scope environment code value demand requirements checking) :
    SourcePlannedSources.Expression operations policy contracts world allowed scope environment code.erase value demand requirements checking := by
  cases source with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference issued => exact .reference issued
  | «variable» known formed => exact .variable known formed
  | lambda body outward formed latentBound => exact .lambda body.erase outward formed latentBound
  | purePair left right => exact .purePair left.erase right.erase
  | pair left right => exact .pair left.erase right.erase
  | app function argument admitted => exact .app function.erase argument.erase admitted
  | bind initializer body => exact .bind initializer.erase body.erase
  | branch condition yes no same => exact .branch condition.erase yes.erase no.erase same
  | perform known admitted operand formed => exact .perform known admitted operand.erase formed
  | handler body clauses capabilities coverage unique admitted table modes declarations =>
      exact .handler body.erase clauses capabilities coverage unique admitted table modes declarations.erase
  | resume known resolved permission operand admitted formed => exact .resume known resolved permission operand.erase admitted formed
  | discard known resolved permission unprotected admitted => exact .discard known resolved permission unprotected admitted
  | cleanup callback body admitted => exact .cleanup callback.erase body.erase admitted
  | resource initializer body formed effectsBound admitted hidden =>
      exact .resource initializer.erase (fun identity fresh => by
        simpa only [Term.erase_instantiate] using (body identity fresh).erase) formed effectsBound admitted hidden


theorem Expression.hint_checked
    (source : Expression operations policy contracts world allowed scope environment code value demand requirements checking) :
    SourceFocusHints.checkSource Instantiation.Environment.empty code.hint value = true := by
  cases source with | checked hint closed node => exact hint

theorem Expression.resource_closed
    (source : Expression operations policy contracts world allowed scope environment code value demand requirements checking) :
    code.ResourceClosed := by
  cases source with | checked hint closed node => exact Term.check_closed_iff.mp closed

/-- Fixed source annotation data determine the erased type, even when rich
proofs differ in requirements or stable checking signatures. -/
theorem Expression.port_unique
    (first : Expression operations policy contracts world allowed scope environment code a demand requirements checking)
    (second : Expression otherOperations otherPolicy otherContracts otherWorld otherAllowed otherScope otherEnvironment
      code b otherDemand otherRequirements otherChecking) : a.erase.erase.port = b.erase.erase.port :=
  SourceFocusHints.source_port_unique first.hint_checked second.hint_checked

end Ash.OneShot.SourceAnnotatedSources

#print axioms Ash.OneShot.SourceAnnotatedSources.Expression.erase
#print axioms Ash.OneShot.SourceAnnotatedSources.Node.erase
#print axioms Ash.OneShot.SourceAnnotatedSources.Body.erase
#print axioms Ash.OneShot.SourceAnnotatedSources.Offer.erase
#print axioms Ash.OneShot.SourceAnnotatedSources.Declarations.erase
#print axioms Ash.OneShot.SourceAnnotatedSources.Expression.hint_checked
#print axioms Ash.OneShot.SourceAnnotatedSources.Expression.resource_closed
#print axioms Ash.OneShot.SourceAnnotatedSources.Expression.port_unique
