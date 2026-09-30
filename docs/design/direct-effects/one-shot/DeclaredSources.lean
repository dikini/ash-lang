import SourceClauseDeclarations
import ClauseRowContracts

/-! Hereditary clause declarations on the existing source grammar. The stronger
    judgment retains declarations in executable clause and callable bodies.
    Erasure preserves the existing full value, demand and requirement indices.
    Clause bodies retain independently checked advertised effect bounds at
    their exact source requirement index, including nested declarations.
    Each used continuation interface equals the declaring handler's residual;
    unused interfaces do not impose an equality or caller obligation. -/
namespace Ash.OneShot.DeclaredSources
open ScopedExpressions ScopedExecution ProtectionContracts CoherentSourceTypes
open RecursiveRequirements (Requirements)
open Owners (Contracts)

mutual
inductive Expression (operations : Operations) (policy : Syntax.TicketPolicy) :
    Contracts → List Nat → List Instance → Execution.Scope → Environment → Code → Value →
      (demand : List Nat) → Requirements demand → Prop where
  | stable (summary : Summary operations world environment allowed code result raw) :
      Expression operations policy contracts world allowed scope environment code result [] (.request [] raw)
  | callable (summary : Callable operations policy contracts
        world environment allowed code result raw) :
      Expression operations policy contracts world allowed scope environment code result [] (.request [] raw)
  | lambda (body : Expression operations policy contracts world requests .none
        (environment.extend parameter input) code output bodyDemand bodyRequirements)
      (outward : RecursiveOutward.Outward bodyRequirements (some latent))
      (formed : ScopedPorts.InWorld world (Value.function input output requests latent).port) :
      Expression operations policy contracts world allowed scope environment (.lambda parameter code)
        (.function input output requests latent) [] (.request [] [])
  | purePair (left : Expression operations policy contracts world allowed scope environment a first [] (.request [] []))
      (right : Expression operations policy contracts world allowed scope environment b second [] (.request [] [])) :
      Expression operations policy contracts world allowed scope environment (.pair a b) (.pair first second) [] (.request [] [])
  | pair (leftSource : Expression operations policy contracts world allowed scope environment a first leftDemand left)
      (rightSource : Expression operations policy contracts world allowed scope environment b second rightDemand right) :
      Expression operations policy contracts world allowed scope environment (.pair a b) (.pair first second)
        (leftDemand ++ rightDemand) (.sequence left right)
  | app (functionSource : Expression operations policy contracts world allowed scope environment f
        (.function input output requests latent) functionDemand function)
      (argumentSource : Expression operations policy contracts world allowed scope environment a input argumentDemand argument)
      (admitted : requests ⊆ allowed) :
      Expression operations policy contracts world allowed scope environment (.app f a) output
        (functionDemand ++ argumentDemand) (.emitAfter (.sequence function argument) [] latent)
  | bind (initializerSource : Expression operations policy contracts world allowed scope environment a input initializerDemand initializer)
      (bodySource : Expression operations policy contracts world allowed scope (environment.extend parameter input) b output bodyDemand body) :
      Expression operations policy contracts world allowed scope environment (.bind parameter a b) output
        (initializerDemand ++ bodyDemand) (.sequence initializer body)
  | branch (conditionSource : Expression operations policy contracts world allowed scope environment test .boolean conditionDemand condition)
      (yesSource : Expression operations policy contracts world allowed scope environment a output yesDemand yes)
      (noSource : Expression operations policy contracts world allowed scope environment b output noDemand no)
      (same : yesDemand.Perm noDemand) :
      Expression operations policy contracts world allowed scope environment (.branch test a b) output
        (conditionDemand ++ yesDemand) (.sequence condition (.choice yes no same))
  | perform (known : operations effect operation = some (input, output)) (admitted : effect ∈ allowed)
      (operandSource : Expression operations policy contracts world allowed scope environment value input operandDemand operand)
      (formed : ScopedPorts.InWorld world output.port) :
      Expression operations policy contracts world allowed scope environment (.perform (Instantiation.freezeEffect effect) operation value)
        output operandDemand (.emitAfter operand [] [⟨effect, operation, false⟩])
  | handler (body : Expression operations policy contracts world (effect :: residual) scope environment
        code answer demand requirements)
      (clauses : ScopedPorts.ClausesTyped operations.ports world environment.ports effect answer.port residual arms)
      (capabilities : ClausesUse policy arms)
      (coverage : ScopedPorts.Covers operations.ports effect arms)
      (unique : (ScopedTyping.clauseKeys arms).Nodup) (admitted : residual ⊆ allowed)
      (table : List (Nat × ClauseContract)) (modes : SourceTemplates.ClauseModes arms table)
      (declarations : Declarations operations policy contracts world environment residual effect answer arms table) :
      Expression operations policy contracts world allowed scope environment
        (.handle (Instantiation.freezeEffect effect) code arms) answer demand
        (requirements.prepend [.ordinary (.handler effect 0 table)])
  | resume (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner)
      (permission : (policy binder).resume = true)
      (operandSource : Expression operations policy contracts world allowed scope environment value contract.input operandDemand operand)
      (admitted : contract.resumeEffects ⊆ allowed) (formed : ScopedPorts.InWorld world contract.answer.port) :
      Expression operations policy contracts world allowed scope environment (.resume binder value) contract.answer
        (operandDemand ++ owner :: contract.resumeDemand) (.sequence operand (.invoke ⟨owner, .resume⟩ contract.resumeDemand []))
  | discard (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner)
      (permission : (policy binder).dispose = true) (unprotected : contract.held = false)
      (admitted : contract.closeEffects ⊆ allowed) :
      Expression operations policy contracts world allowed scope environment (.discard binder) .unit
        (owner :: contract.closeDemand) (.invoke ⟨owner, .dispose⟩ contract.closeDemand [])
  | cleanup (callbackSource : Expression operations policy contracts world allowed scope environment action
        (.function .unit .unit requests latent) callbackDemand callback)
      (bodySource : Expression operations policy contracts world allowed scope environment code output bodyDemand body)
      (admitted : requests ⊆ allowed) :
      Expression operations policy contracts world allowed scope environment (.cleanup action code) output
        (callbackDemand ++ bodyDemand) (.emitAfter (.sequence callback body) [] (qualify true latent))
  | resource {bodyRow : Nat → Footprint}
      (initializer : Expression operations policy contracts world allowed scope environment initial .integer demand requirements)
      (body : ∀ identity, identity ∉ world → Callable operations policy contracts
        (world ++ [identity]) environment (.cell identity :: residual)
        (code.instantiate (Instantiation.Environment.empty.bind binder identity)) output (bodyRow identity))
      (formed : ScopedPorts.InWorld world output.port)
      (effectsBound : residual.flatMap Instance.resources ⊆ world) (admitted : residual ⊆ allowed)
      (outward : ∀ identity, identity ∉ world → CallableProtection.outsideCell identity (bodyRow identity) = raw) :
      Expression operations policy contracts world allowed scope environment (.resource binder initial code)
        output demand (.emitAfter requirements [] raw)
  | scopedResource {bodyRequirements : Nat → Requirements bodyDemand}
      (initializer : Expression operations policy contracts world allowed scope environment initial .integer initialDemand initialRequirements)
      (body : ∀ identity, identity ∉ world → Expression operations policy contracts (world ++ [identity])
        (.cell identity :: residual) scope environment
        (code.instantiate (Instantiation.Environment.empty.bind binder identity)) output bodyDemand (bodyRequirements identity))
      (formed : ScopedPorts.InWorld world output.port)
      (effectsBound : residual.flatMap Instance.resources ⊆ world) (admitted : residual ⊆ allowed)
      (hidden : ∀ identity, identity ∉ world → ResourceRequirements.Hides identity (bodyRequirements identity) outward) :
      Expression operations policy contracts world allowed scope environment (.resource binder initial code)
        output (initialDemand ++ bodyDemand) (.sequence initialRequirements outward)

inductive Callable (operations : Operations) (policy : Syntax.TicketPolicy) :
    Contracts → List Nat → Environment → List Instance → Code → Value → Footprint → Prop where
  | summaryUnit : Callable operations policy contracts world environment allowed .unit .unit []
  | summaryBoolean : Callable operations policy contracts world environment allowed (.boolean value) .boolean []
  | summaryInteger : Callable operations policy contracts world environment allowed (.integer value) .integer []
  | summaryReference (issued : identity ∈ world) :
      Callable operations policy contracts world environment allowed (.resourceRef (.activation identity)) (.reference identity) []
  | summaryVariable (known : environment name = some value) (formed : ScopedPorts.InWorld world value.port) :
      Callable operations policy contracts world environment allowed (.variable name) value []
  | summaryPair (left : Callable operations policy contracts world environment allowed a first leftRow)
      (right : Callable operations policy contracts world environment allowed b second rightRow) :
      Callable operations policy contracts world environment allowed (.pair a b) (.pair first second) (leftRow ++ rightRow)
  | summaryLambda (body : Expression operations policy contracts world latentRequests .none (environment.extend parameter input) code output bodyDemand bodyRequirements)
      (outward : RecursiveOutward.Outward bodyRequirements (some latentRow))
      (formed : ScopedPorts.InWorld world (Value.function input output latentRequests latentRow).port) :
      Callable operations policy contracts world environment allowed (.lambda parameter code) (.function input output latentRequests latentRow) []
  | summaryApp (function : Callable operations policy contracts world environment allowed f (.function input output latentRequests latentRow) functionRow)
      (argument : Callable operations policy contracts world environment allowed a input argumentRow) (admitted : latentRequests ⊆ allowed) :
      Callable operations policy contracts world environment allowed (.app f a) output (functionRow ++ argumentRow ++ latentRow)
  | summaryBind (initializer : Callable operations policy contracts world environment allowed a input initializerRow)
      (body : Callable operations policy contracts world (environment.extend parameter input) allowed b output bodyRow) :
      Callable operations policy contracts world environment allowed (.bind parameter a b) output (initializerRow ++ bodyRow)
  | summaryBranch (condition : Callable operations policy contracts world environment allowed test .boolean conditionRow)
      (yes : Callable operations policy contracts world environment allowed a output yesRow)
      (no : Callable operations policy contracts world environment allowed b output noRow) :
      Callable operations policy contracts world environment allowed (.branch test a b) output (conditionRow ++ yesRow ++ noRow)
  | summaryPerform (known : operations effect operation = some (input, output)) (admitted : effect ∈ allowed)
      (operand : Callable operations policy contracts world environment allowed value input operandRow) (formed : ScopedPorts.InWorld world output.port) :
      Callable operations policy contracts world environment allowed (.perform (Instantiation.freezeEffect effect) operation value) output
        (operandRow ++ [⟨effect, operation, false⟩])
  | summaryCleanup (callback : Callable operations policy contracts world environment allowed action (.function .unit .unit latentRequests latentRow) callbackRow)
      (body : Callable operations policy contracts world environment allowed code output bodyRow) (admitted : latentRequests ⊆ allowed) :
      Callable operations policy contracts world environment allowed (.cleanup action code) output (callbackRow ++ bodyRow ++ qualify true latentRow)
  | summaryResource {bodyRow : Nat → Footprint}
      (initializer : Callable operations policy contracts world environment allowed initial .integer initialRow)
      (body : ∀ identity, identity ∉ world →
        Callable operations policy contracts (world ++ [identity]) environment (.cell identity :: residual)
          (code.instantiate (Instantiation.Environment.empty.bind binder identity)) output (bodyRow identity))
      (formed : ScopedPorts.InWorld world output.port)
      (effectsBound : residual.flatMap Instance.resources ⊆ world) (admitted : residual ⊆ allowed)
      (outward : ∀ identity, identity ∉ world → CallableProtection.outsideCell identity (bodyRow identity) = row) :
      Callable operations policy contracts world environment allowed (.resource binder initial code) output (initialRow ++ row)

inductive Body (operations : Operations) (policy : Syntax.TicketPolicy) :
    Contracts → List Nat → List Instance → Execution.Scope → Environment → Code → Value → ClauseRowAdmission.Header → Prop where
  | typed (source : Expression operations policy contracts world allowed scope environment code answer demand requirements)
      (rows : ClauseRowAdmission.Rows header requirements (ClauseRowAdmission.SourceStore operations header.owner header.contract)) :
      Body operations policy contracts world allowed scope environment code answer header

inductive Offer (operations : Operations) (policy : Syntax.TicketPolicy) :
    Contracts → List Nat → Environment → List Instance → Nat → Nat → Value → Value → Value →
      List Instance → List Instance → Code → Bool → Bool → Option Footprint → Prop where
  | unavailable : Offer operations policy contracts world environment allowed parameter binder argument input answer
      resumeEffects closeEffects code held disposes none
  | available
      (resumeInterface : code.requiredActions.resume = true → resumeEffects = allowed)
      (closeInterface : code.requiredActions.dispose = true → closeEffects = allowed)
      (source : ∀ owner (contract : Owners.Contract), contracts owner = none →
        contract.input = input → contract.answer = answer →
        contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
        contract.held = held → contract.closeDemand.Perm contract.resumeDemand →
        Body operations policy (contracts.insert owner contract) world allowed (.ticket binder owner)
          (environment.extend parameter argument) code answer ⟨owner, contract, disposes, row⟩) :
      Offer operations policy contracts world environment allowed parameter binder argument input answer
        resumeEffects closeEffects code held disposes (some row)

inductive Declarations (operations : Operations) (policy : Syntax.TicketPolicy) :
    Contracts → List Nat → Environment → List Instance → Instance → Value → Clauses →
      List (Nat × ClauseContract) → Prop where
  | nil : Declarations operations policy contracts world environment allowed requested answer .nil []
  | cons (known : operations requested operation = some (argument, input))
      (ordinary : Offer operations policy contracts world environment allowed parameter binder argument input answer
        resumeEffects closeEffects body false dispose ordinaryRow)
      (protectedMode : Offer operations policy contracts world environment allowed parameter binder argument input answer
        resumeEffects closeEffects body true dispose protectedRow)
      (rest : Declarations operations policy contracts world environment allowed requested answer clauses table) :
      Declarations operations policy contracts world environment allowed requested answer
        (.cons operation parameter binder body clauses)
        ((operation, ⟨dispose, ordinaryRow, protectedRow⟩) :: table)
end

theorem expression_erase
    (source : Expression operations policy contracts world allowed scope environment code value demand requirements) :
    SourceTemplates.Expression operations policy contracts world allowed scope environment code value demand requirements := by
  induction source using Expression.rec
      (motive_2 := fun contracts world environment allowed code value row _ =>
        SourceTemplates.CallableSummary operations policy contracts world environment allowed code value row)
      (motive_3 := fun _ _ _ _ _ _ _ _ _ => True)
      (motive_4 := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True)
      (motive_5 := fun _ _ _ _ _ _ _ _ _ => True) with
  | stable summary => exact .stable summary
  | callable summary ih => exact .callable ih
  | lambda body outward formed ih => exact .lambda ih outward formed
  | purePair left right ihLeft ihRight => exact .purePair ihLeft ihRight
  | pair left right ihLeft ihRight => exact .pair ihLeft ihRight
  | app function argument admitted ihFunction ihArgument => exact .app ihFunction ihArgument admitted
  | bind initializer body ihInit ihBody => exact .bind ihInit ihBody
  | branch condition yes no same ihCondition ihYes ihNo => exact .branch ihCondition ihYes ihNo same
  | perform known admitted operand formed ih => exact .perform known admitted ih formed
  | handler body clauses capabilities coverage unique admitted table modes declarations ihBody ihDecl =>
      exact .handler ihBody clauses capabilities coverage unique admitted table modes
  | resume known resolved permission operand admitted formed ih =>
      exact .resume known resolved permission ih admitted formed
  | discard known resolved permission unprotected admitted => exact .discard known resolved permission unprotected admitted
  | cleanup callback body admitted ihCallback ihBody => exact .cleanup ihCallback ihBody admitted
  | resource initializer body formed effectsBound admitted outward ihInit ihBody =>
      exact .resource ihInit ihBody formed effectsBound admitted outward
  | scopedResource initializer body formed effectsBound admitted hidden ihInit ihBody =>
      exact .scopedResource ihInit ihBody formed effectsBound admitted hidden
  | summaryUnit => exact .summaryUnit
  | summaryBoolean => exact .summaryBoolean
  | summaryInteger => exact .summaryInteger
  | summaryReference issued => exact .summaryReference issued
  | summaryVariable known formed => exact .summaryVariable known formed
  | summaryPair left right ihLeft ihRight => exact .summaryPair ihLeft ihRight
  | summaryLambda body outward formed ih => exact .summaryLambda ih outward formed
  | summaryApp function argument admitted ihFunction ihArgument => exact .summaryApp ihFunction ihArgument admitted
  | summaryBind initializer body ihInit ihBody => exact .summaryBind ihInit ihBody
  | summaryBranch condition yes no ihCondition ihYes ihNo => exact .summaryBranch ihCondition ihYes ihNo
  | summaryPerform known admitted operand formed ih => exact .summaryPerform known admitted ih formed
  | summaryCleanup callback body admitted ihCallback ihBody => exact .summaryCleanup ihCallback ihBody admitted
  | summaryResource initializer body formed effectsBound admitted outward ihInit ihBody =>
      exact .summaryResource ihInit ihBody formed effectsBound admitted outward
  | typed | unavailable | available | nil | cons => trivial

/-- The indexed callable representation is equivalent to the existing generic
    summary with hereditary expression bodies. It adds no callable rules. -/
theorem Callable.to_generic
    (source : Callable operations policy contracts world environment allowed code value row) :
    CallableSources.Summary operations
      (fun world environment requests code value demand requirements =>
        Expression operations policy contracts world requests .none environment code value demand requirements)
      world environment allowed code value row := by
  induction source using Callable.rec
      (motive_1 := fun _ _ _ _ _ _ _ _ _ _ => True)
      (motive_3 := fun _ _ _ _ _ _ _ _ _ => True)
      (motive_4 := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True)
      (motive_5 := fun _ _ _ _ _ _ _ _ _ => True)
  case summaryUnit => exact .summaryUnit
  case summaryBoolean => exact .summaryBoolean
  case summaryInteger => exact .summaryInteger
  case summaryReference issued => exact .summaryReference issued
  case summaryVariable known formed => exact .summaryVariable known formed
  case summaryPair left right ihLeft ihRight => exact .summaryPair ihLeft ihRight
  case summaryLambda body outward formed ih => exact .summaryLambda body outward formed
  case summaryApp function argument admitted ihFunction ihArgument => exact .summaryApp ihFunction ihArgument admitted
  case summaryBind initializer body ihInit ihBody => exact .summaryBind ihInit ihBody
  case summaryBranch condition yes no ihCondition ihYes ihNo => exact .summaryBranch ihCondition ihYes ihNo
  case summaryPerform known admitted operand formed ih => exact .summaryPerform known admitted ih formed
  case summaryCleanup callback body admitted ihCallback ihBody => exact .summaryCleanup ihCallback ihBody admitted
  case summaryResource initializer body formed effectsBound admitted outward ihInit ihBody =>
    exact .summaryResource ihInit ihBody formed effectsBound admitted outward
  all_goals trivial

theorem Callable.from_generic
    (source : CallableSources.Summary operations
      (fun world environment requests code value demand requirements =>
        Expression operations policy contracts world requests .none environment code value demand requirements)
      world environment allowed code value row) :
    Callable operations policy contracts world environment allowed code value row := by
  induction source with
  | summaryUnit => exact .summaryUnit
  | summaryBoolean => exact .summaryBoolean
  | summaryInteger => exact .summaryInteger
  | summaryReference issued => exact .summaryReference issued
  | summaryVariable known formed => exact .summaryVariable known formed
  | summaryPair left right ihLeft ihRight => exact .summaryPair ihLeft ihRight
  | summaryLambda body outward formed => exact .summaryLambda body outward formed
  | summaryApp function argument admitted ihFunction ihArgument => exact .summaryApp ihFunction ihArgument admitted
  | summaryBind initializer body ihInit ihBody => exact .summaryBind ihInit ihBody
  | summaryBranch condition yes no ihCondition ihYes ihNo => exact .summaryBranch ihCondition ihYes ihNo
  | summaryPerform known admitted operand formed ih => exact .summaryPerform known admitted ih formed
  | summaryCleanup callback body admitted ihCallback ihBody => exact .summaryCleanup ihCallback ihBody admitted
  | summaryResource initializer body formed effectsBound admitted outward ihInit ihBody =>
      exact .summaryResource ihInit ihBody formed effectsBound admitted outward

theorem Callable.erase
    (source : Callable operations policy contracts world environment allowed code value row) :
    SourceTemplates.CallableSummary operations policy contracts world environment allowed code value row :=
  CallableSources.map_body source.to_generic (fun _ _ _ _ _ _ _ body => expression_erase body)

theorem lambda_body
    (source : Expression operations policy contracts world allowed scope environment
      (.lambda parameter code) (.function input output requests latent) demand requirements) :
    ∃ bodyDemand, ∃ bodyRequirements : Requirements bodyDemand,
      Expression operations policy contracts world requests .none (environment.extend parameter input)
        code output bodyDemand bodyRequirements ∧ RecursiveOutward.Outward bodyRequirements (some latent) := by
  cases source with
  | stable summary => cases summary with
    | lambda body formed => exact ⟨[], .request [] _, .stable body, .request (layers := [])⟩
  | callable summary => cases summary with
    | summaryLambda body outward formed => exact ⟨_, _, body, outward⟩
  | lambda body outward formed => exact ⟨_, _, body, outward⟩

theorem Offer.erase
    (source : Offer operations policy contracts world environment allowed parameter binder argument input answer
      resumeEffects closeEffects code held disposes row) :
    SourceClauseDeclarations.SourceOffer operations policy contracts world environment allowed parameter binder argument input answer
      resumeEffects closeEffects code held row := by
  cases source with
  | unavailable => exact .unavailable
  | available resumeInterface closeInterface family =>
      apply SourceClauseDeclarations.SourceOffer.available
      intro owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
      cases family owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance with
      | typed body rows => exact ⟨_, _, expression_erase body⟩

theorem Declarations.erase
    (source : Declarations operations policy contracts world environment allowed requested answer clauses table) :
    SourceClauseDeclarations.SourceClauses operations policy contracts world environment allowed requested answer clauses table := by
  induction clauses using Clauses.rec (motive_1 := fun _ => True) generalizing table
  case nil => cases source; exact .nil
  case cons operation parameter binder body rest ihBody ihRest =>
    cases source with
    | cons known ordinary protectedMode rest => exact .cons known ordinary.erase protectedMode.erase (ihRest rest)
  all_goals trivial

theorem Body.erase
    (source : Body operations policy contracts world allowed scope environment code answer header) :
    ∃ demand, ∃ requirements : Requirements demand,
      SourceTemplates.Expression operations policy contracts world allowed scope environment code answer demand requirements := by
  cases source with
  | typed body rows => exact ⟨_, _, expression_erase body⟩

/-- Exact runtime selection retains the stronger body judgment, so a handler
    inside the selected clause or a returned function keeps its declarations. -/
theorem selected_body
    (source : Declarations operations policy contracts world environment allowed requested answer clauses table)
    (selected : ClauseAt operation clauses parameter binder code)
    (found : lookup operation table = some offered)
    (available : offered.row held = some row) :
    ∃ argument input resumeEffects closeEffects,
      operations requested operation = some (argument, input) ∧
      (code.requiredActions.resume = true → resumeEffects = allowed) ∧
      (code.requiredActions.dispose = true → closeEffects = allowed) ∧
      ∀ owner (contract : Owners.Contract), contracts owner = none →
        contract.input = input → contract.answer = answer →
        contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
        contract.held = held → contract.closeDemand.Perm contract.resumeDemand →
        Body operations policy (contracts.insert owner contract) world allowed (.ticket binder owner)
          (environment.extend parameter argument) code answer ⟨owner, contract, offered.dispose, row⟩ := by
  induction selected generalizing table with
  | hit => cases source with
    | cons known ordinary protectedMode rest =>
        simp only [lookup, if_true] at found
        cases Option.some.inj found
        cases held with
        | false =>
            simp [ClauseContract.row] at available
            cases available ▸ ordinary with
            | available resumeInterface closeInterface family => exact ⟨_, _, _, _, known, resumeInterface, closeInterface, family⟩
        | true =>
            simp [ClauseContract.row] at available
            cases available ▸ protectedMode with
            | available resumeInterface closeInterface family => exact ⟨_, _, _, _, known, resumeInterface, closeInterface, family⟩
  | pass different next ih => cases source with
    | cons known ordinary protectedMode rest =>
        exact ih rest (by simpa only [lookup, if_neg different] using found)

theorem handler_parts
    (source : Expression operations policy contracts world allowed scope environment
      (.handle requested code clauses) answer demand requirements) :
    ∃ effect residual table, ∃ bodyRequirements : Requirements demand,
      requested = Instantiation.freezeEffect effect ∧
      requirements = bodyRequirements.prepend [.ordinary (.handler effect 0 table)] ∧
      Expression operations policy contracts world (effect :: residual) scope environment code answer demand bodyRequirements ∧
      ScopedPorts.ClausesTyped operations.ports world environment.ports effect answer.port residual clauses ∧
      ClausesUse policy clauses ∧ ScopedPorts.Covers operations.ports effect clauses ∧
      (ScopedTyping.clauseKeys clauses).Nodup ∧ residual ⊆ allowed ∧
      SourceTemplates.ClauseModes clauses table ∧
      Declarations operations policy contracts world environment residual effect answer clauses table := by
  cases source with
  | stable summary => cases summary
  | callable summary => cases summary
  | handler body clauses capabilities coverage unique admitted table modes declarations =>
      exact ⟨_, _, table, _, rfl, rfl, body, clauses, capabilities, coverage, unique, admitted, modes, declarations⟩

namespace Examples
open SourceCallableExamples (operations policy effect clauses table function functionType body bodyRequirements
  operation_known body_outward)

/-- A literal resuming clause works at any handler residual. Its unused
closing interface remains independent of that residual. -/
theorem resume_offer (contracts : Contracts) (environment : Environment)
    (allowed : List Instance) (held : Bool) :
    Offer operations policy contracts [] environment allowed 1 9 .unit .unit .unit allowed []
      (.resume 9 .unit) held false (some []) := by
  apply Offer.available (fun _ => rfl) (by intro impossible; cases impossible)
  intro owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
  have known : (contracts.insert owner contract) owner = some contract := by simp [Owners.Contracts.insert]
  have operand : Expression operations policy (contracts.insert owner contract) [] allowed (.ticket 9 owner)
      (environment.extend 1 .unit) .unit contract.input [] (.request [] []) := inputSame.symm ▸ .stable .unit
  have resumed := Expression.resume (binder := 9) known (by simp [Execution.Scope.resolve]) (by rfl) operand
    (resumeSame.symm ▸ List.Subset.refl allowed)
    (answerSame.symm ▸ (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources]))
  exact .typed (answerSame ▸ resumed) ClauseRowAdmission.resume_rows

theorem declaration (contracts : Contracts) (environment : Environment) :
    Declarations operations policy contracts [] environment [] effect .unit clauses table := by
  have family : ∀ held, Offer operations policy contracts [] environment [] 1 9 .unit .unit .unit [] [] (.resume 9 .unit) held false (some []) := by
    intro held
    apply Offer.available (fun _ => rfl) (fun _ => rfl)
    intro owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
    have known : (contracts.insert owner contract) owner = some contract := by simp [Owners.Contracts.insert]
    have operand : Expression operations policy (contracts.insert owner contract) [] [] (.ticket 9 owner)
        (environment.extend 1 .unit) .unit contract.input [] (.request [] []) := inputSame.symm ▸ .stable .unit
    have resumed := Expression.resume (binder := 9) known (by simp [Execution.Scope.resolve]) (by rfl) operand
      (resumeSame.symm ▸ List.Subset.refl [])
      (answerSame.symm ▸ (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources]))
    exact .typed (answerSame ▸ resumed) ClauseRowAdmission.resume_rows
  exact .cons operation_known (family false) (family true) .nil

theorem body_source (contracts : Contracts) (environment : Environment) :
    Expression operations policy contracts [] [] .none environment body .unit [] bodyRequirements := by
  have clausePorts : ScopedPorts.ClausesTyped operations.ports [] environment.ports effect .unit [] clauses :=
    .cons (port_lookup operation_known)
      (.resume .unit (List.Subset.refl []) (by simp [ScopedPorts.InWorld, ScopedPorts.Port.resources])) .nil
  have coverage : ScopedPorts.Covers operations.ports effect clauses := by
    intro operation input output known
    by_cases same : operation = 0
    · simp [same, clauses, ScopedTyping.clauseKeys]
    · simp [Operations.ports, operations, same] at known
  exact .handler (.perform operation_known List.mem_cons_self (.stable .unit)
      (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources]))
    clausePorts (.cons (.resume rfl .unit) .nil) coverage (by decide) (List.Subset.refl []) table
    (.cons (by intro impossible; cases impossible) .nil) (declaration contracts environment)

theorem function_source (contracts : Contracts) (environment : Environment) (scope : Execution.Scope) :
    Expression operations policy contracts [] [] scope environment function functionType [] (.request [] []) :=
  .lambda (body_source contracts _) body_outward (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])

theorem nested_declaration (contracts : Contracts) (environment : Environment) :
    Declarations operations policy contracts [] environment [] effect functionType
      SourceClauseDeclarations.Examples.clauses SourceClauseDeclarations.Examples.table := by
  have family : ∀ held, Offer operations policy contracts [] environment [] 2 9 .unit .unit functionType [] []
      SourceClauseDeclarations.Examples.body held false (some []) := by
    intro held
    apply Offer.available (fun _ => rfl) (fun _ => rfl)
    intro owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
    have known : (contracts.insert owner contract) owner = some contract := by simp [Owners.Contracts.insert]
    have operand : Expression operations policy (contracts.insert owner contract) [] [] (.ticket 9 owner)
        (environment.extend 2 .unit) .unit contract.input [] (.request [] []) := inputSame.symm ▸ .stable .unit
    have resumed := Expression.resume (binder := 9) known (by simp [Execution.Scope.resolve]) (by rfl) operand
      (resumeSame.symm ▸ List.Subset.refl [])
      (answerSame.symm ▸ (by simp [ScopedPorts.InWorld, functionType, Value.port, ScopedPorts.Port.resources]))
    exact .typed (Expression.bind resumed (function_source _ _ _)) ClauseRowAdmission.resume_then_value_rows
  exact .cons operation_known (family false) (family true) .nil

end Examples

end Ash.OneShot.DeclaredSources
#print axioms Ash.OneShot.DeclaredSources.expression_erase
#print axioms Ash.OneShot.DeclaredSources.Callable.to_generic
#print axioms Ash.OneShot.DeclaredSources.Callable.from_generic
#print axioms Ash.OneShot.DeclaredSources.Callable.erase
#print axioms Ash.OneShot.DeclaredSources.lambda_body
#print axioms Ash.OneShot.DeclaredSources.Offer.erase
#print axioms Ash.OneShot.DeclaredSources.Declarations.erase
#print axioms Ash.OneShot.DeclaredSources.Body.erase
#print axioms Ash.OneShot.DeclaredSources.selected_body
#print axioms Ash.OneShot.DeclaredSources.handler_parts
#print axioms Ash.OneShot.DeclaredSources.Examples.declaration
#print axioms Ash.OneShot.DeclaredSources.Examples.body_source
#print axioms Ash.OneShot.DeclaredSources.Examples.function_source
#print axioms Ash.OneShot.DeclaredSources.Examples.nested_declaration

#print axioms Ash.OneShot.DeclaredSources.Examples.resume_offer
