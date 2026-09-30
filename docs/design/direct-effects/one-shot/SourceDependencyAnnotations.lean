import DeclaredSources

/-! Hereditary dependency annotations on the existing direct source calculus.
The old value, requirement and owner indices are preserved by erasure. Cleanup
retains its callback requirements and body separately; function types retain the
body annotation used at application. These are structural source annotations,
not yet a capture-admission judgment or a complete progress theorem. -/
namespace Ash.OneShot.SourceDependencyAnnotations
open ScopedExpressions ScopedExecution ProtectionContracts
open RecursiveRequirements (Requirements Key)

/-- This is checking data, not a computation grammar. Clause annotations are
families over the fresh owner; resource annotations are families over the fresh
resource identity, as in the existing hereditary source judgment. -/
inductive Dependencies where
  | pure
  | request : Instance → Nat → Dependencies
  | invoke : Key → Dependencies
  | sequence : Dependencies → Dependencies → Dependencies
  | choice : Dependencies → Dependencies → Dependencies
  | handler : Instance → List (Nat × ClauseContract) →
      List (Nat × (Option (Nat → Dependencies) × Option (Nat → Dependencies))) →
      Dependencies → Dependencies
  | cleanup : List Instance → Dependencies → Dependencies → Dependencies
  | resource : (Nat → Dependencies) → Dependencies

inductive Value where
  | unit | boolean | integer
  | reference : Nat → Value
  | pair : Value → Value → Value
  | function : Value → Value → List Instance → Footprint → Dependencies → Value

def Value.erase : Value → CoherentSourceTypes.Value
  | .unit => .unit
  | .boolean => .boolean
  | .integer => .integer
  | .reference identity => .reference identity
  | .pair left right => .pair left.erase right.erase
  | .function input output requests latent _ => .function input.erase output.erase requests latent

abbrev Environment := Nat → Option Value
def Environment.empty : Environment := fun _ => none
def Environment.extend (environment : Environment) (name : Nat) (value : Value) : Environment :=
  fun other => if other = name then some value else environment other
def Environment.erase (environment : Environment) : CoherentSourceTypes.Environment :=
  fun name => (environment name).map Value.erase

theorem environment_erase_extend (environment : Environment) :
    (environment.extend name value).erase = environment.erase.extend name value.erase := by
  funext other
  by_cases same : other = name <;>
    simp [Environment.extend, Environment.erase, CoherentSourceTypes.Environment.extend, same]

abbrev Operations := Instance → Nat → Option (Value × Value)
def Operations.erase (operations : Operations) : CoherentSourceTypes.Operations :=
  fun effect operation => (operations effect operation).map (fun pair => (pair.1.erase, pair.2.erase))

theorem operation_erase (known : operations effect operation = some (input, output)) :
    Operations.erase operations effect operation = some (input.erase, output.erase) := by
  simp [Operations.erase, known]

structure Contract where
  input : Value
  answer : Value
  held : Bool
  resumeDemand : List Nat
  resumeRow : Footprint
  closeDemand : List Nat
  closeRow : Option Footprint
  resumeEffects : List Instance
  closeEffects : List Instance

def Contract.erase (contract : Contract) : CoherentSourceTypes.Owners.Contract :=
  ⟨contract.input.erase, contract.answer.erase, contract.held, contract.resumeDemand,
    contract.resumeRow, contract.closeDemand, contract.closeRow, contract.resumeEffects, contract.closeEffects⟩

abbrev Contracts := Nat → Option Contract
def Contracts.insert (contracts : Contracts) (owner : Nat) (contract : Contract) : Contracts :=
  fun other => if other = owner then some contract else contracts other
def Contracts.erase (contracts : Contracts) : CoherentSourceTypes.Owners.Contracts :=
  fun owner => (contracts owner).map Contract.erase

theorem contracts_erase_insert (contracts : Contracts) :
    (contracts.insert owner contract).erase = contracts.erase.insert owner contract.erase := by
  funext other
  by_cases same : other = owner <;>
    simp [Contracts.insert, Contracts.erase, CoherentSourceTypes.Owners.Contracts.insert, same]

theorem contract_erase_known (known : contracts owner = some contract) :
    Contracts.erase contracts owner = some contract.erase := by
  simp [Contracts.erase, known]

abbrev ClauseDependencies := List (Nat × (Option (Nat → Dependencies) × Option (Nat → Dependencies)))

mutual
inductive Expression (operations : Operations) (policy : Syntax.TicketPolicy) :
    Contracts → List Nat → List Instance → Execution.Scope → Environment → Code → Value →
      (demand : List Nat) → Requirements demand → Dependencies → Prop where
  | unit : Expression operations policy contracts world allowed scope environment .unit .unit [] (.request [] []) .pure
  | boolean : Expression operations policy contracts world allowed scope environment (.boolean value) .boolean [] (.request [] []) .pure
  | integer : Expression operations policy contracts world allowed scope environment (.integer value) .integer [] (.request [] []) .pure
  | reference (issued : identity ∈ world) :
      Expression operations policy contracts world allowed scope environment (.resourceRef (.activation identity))
        (.reference identity) [] (.request [] []) .pure
  | variable (known : environment name = some value) (formed : ScopedPorts.InWorld world value.erase.port) :
      Expression operations policy contracts world allowed scope environment (.variable name) value [] (.request [] []) .pure
  | lambda (body : Expression operations policy contracts world requests .none
        (environment.extend parameter input) code output bodyDemand bodyRequirements dependencies)
      (outward : RecursiveOutward.Outward bodyRequirements (some latent))
      (formed : ScopedPorts.InWorld world (CoherentSourceTypes.Value.function input.erase output.erase requests latent).port)
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
      (formed : ScopedPorts.InWorld world output.erase.port) :
      Expression operations policy contracts world allowed scope environment (.perform (Instantiation.freezeEffect effect) operation value)
        output operandDemand (.emitAfter operandReq [] [⟨effect, operation, false⟩])
        (.sequence operandDep (.request effect operation))
  | handler (body : Expression operations policy contracts world (effect :: residual) scope environment
        code answer demand requirements dependencies)
      (clauses : ScopedPorts.ClausesTyped operations.erase.ports world environment.erase.ports effect answer.erase.port residual arms)
      (capabilities : ClausesUse policy arms)
      (coverage : ScopedPorts.Covers operations.erase.ports effect arms)
      (unique : (ScopedTyping.clauseKeys arms).Nodup) (admitted : residual ⊆ allowed)
      (table : List (Nat × ClauseContract)) (modes : SourceTemplates.ClauseModes arms table)
      (declarations : Declarations operations policy contracts world environment residual effect answer arms table clauseDeps) :
      Expression operations policy contracts world allowed scope environment
        (.handle (Instantiation.freezeEffect effect) code arms) answer demand
        (requirements.prepend [.ordinary (.handler effect 0 table)]) (.handler effect table clauseDeps dependencies)
  | resume (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner)
      (permission : (policy binder).resume = true)
      (operand : Expression operations policy contracts world allowed scope environment value contract.input operandDemand operandReq operandDep)
      (admitted : contract.resumeEffects ⊆ allowed) (formed : ScopedPorts.InWorld world contract.answer.erase.port) :
      Expression operations policy contracts world allowed scope environment (.resume binder value) contract.answer
        (operandDemand ++ owner :: contract.resumeDemand) (.sequence operandReq (.invoke ⟨owner, .resume⟩ contract.resumeDemand []))
        (.sequence operandDep (.invoke ⟨owner, .resume⟩))
  | discard (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner)
      (permission : (policy binder).dispose = true) (unprotected : contract.held = false)
      (admitted : contract.closeEffects ⊆ allowed) :
      Expression operations policy contracts world allowed scope environment (.discard binder) .unit
        (owner :: contract.closeDemand) (.invoke ⟨owner, .dispose⟩ contract.closeDemand []) (.invoke ⟨owner, .dispose⟩)
  | cleanup (callback : Expression operations policy contracts world allowed scope environment action
        (.function .unit .unit requests latent callbackBody) callbackDemand callbackReq callbackDep)
      (body : Expression operations policy contracts world allowed scope environment code output bodyDemand bodyReq bodyDep)
      (admitted : requests ⊆ allowed) :
      Expression operations policy contracts world allowed scope environment (.cleanup action code) output
        (callbackDemand ++ bodyDemand) (.emitAfter (.sequence callbackReq bodyReq) [] (qualify true latent))
        (.sequence callbackDep (.cleanup requests callbackBody bodyDep))
  | resource {bodyRequirements : Nat → Requirements bodyDemand} {bodyDependencies : Nat → Dependencies}
      (initializer : Expression operations policy contracts world allowed scope environment initial .integer initialDemand initialRequirements initialDep)
      (body : ∀ identity, identity ∉ world → Expression operations policy contracts (world ++ [identity])
        (.cell identity :: residual) scope environment
        (code.instantiate (Instantiation.Environment.empty.bind binder identity)) output bodyDemand (bodyRequirements identity) (bodyDependencies identity))
      (formed : ScopedPorts.InWorld world output.erase.port)
      (effectsBound : residual.flatMap Instance.resources ⊆ world) (admitted : residual ⊆ allowed)
      (hidden : ∀ identity, identity ∉ world → ResourceRequirements.Hides identity (bodyRequirements identity) outward) :
      Expression operations policy contracts world allowed scope environment (.resource binder initial code)
        output (initialDemand ++ bodyDemand) (.sequence initialRequirements outward)
        (.sequence initialDep (.resource bodyDependencies))

inductive Body (operations : Operations) (policy : Syntax.TicketPolicy) :
    Contracts → List Nat → List Instance → Execution.Scope → Environment → Code → Value → ClauseRowAdmission.Header → Dependencies → Prop where
  | typed (source : Expression operations policy contracts world allowed scope environment code answer demand requirements dependencies)
      (rows : ClauseRowAdmission.Rows header requirements (ClauseRowAdmission.SourceStore operations.erase header.owner header.contract)) :
      Body operations policy contracts world allowed scope environment code answer header dependencies
  | annotated (source : Expression operations policy contracts world allowed scope environment code answer demand normal dependencies)
      (annotation : RowAnnotation normal checkedRequirements)
      (rows : ClauseRowAdmission.Rows header checkedRequirements (ClauseRowAdmission.SourceStore operations.erase header.owner header.contract)) :
      Body operations policy contracts world allowed scope environment code answer header dependencies

inductive Offer (operations : Operations) (policy : Syntax.TicketPolicy) :
    Contracts → List Nat → Environment → List Instance → Nat → Nat → Value → Value → Value →
      List Instance → List Instance → Code → Bool → Bool → Option Footprint → Option (Nat → Dependencies) → Prop where
  | unavailable : Offer operations policy contracts world environment allowed parameter binder argument input answer
      resumeEffects closeEffects code held disposes none none
  | available
      (resumeInterface : code.requiredActions.resume = true → resumeEffects = allowed)
      (closeInterface : code.requiredActions.dispose = true → closeEffects = allowed)
      (source : ∀ owner (contract : Contract), contracts owner = none →
        contract.input = input → contract.answer = answer →
        contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
        contract.held = held → contract.closeDemand.Perm contract.resumeDemand →
        Body operations policy (contracts.insert owner contract) world allowed (.ticket binder owner)
          (environment.extend parameter argument) code answer ⟨owner, contract.erase, disposes, row⟩ (dependencies owner)) :
      Offer operations policy contracts world environment allowed parameter binder argument input answer
        resumeEffects closeEffects code held disposes (some row) (some dependencies)

inductive Declarations (operations : Operations) (policy : Syntax.TicketPolicy) :
    Contracts → List Nat → Environment → List Instance → Instance → Value → Clauses →
      List (Nat × ClauseContract) → ClauseDependencies → Prop where
  | nil : Declarations operations policy contracts world environment allowed requested answer .nil [] []
  | cons (known : operations requested operation = some (argument, input))
      (ordinary : Offer operations policy contracts world environment allowed parameter binder argument input answer
        resumeEffects closeEffects body false dispose ordinaryRow ordinaryDeps)
      (protectedMode : Offer operations policy contracts world environment allowed parameter binder argument input answer
        resumeEffects closeEffects body true dispose protectedRow protectedDeps)
      (rest : Declarations operations policy contracts world environment allowed requested answer clauses table remainingDeps) :
      Declarations operations policy contracts world environment allowed requested answer
        (.cons operation parameter binder body clauses)
        ((operation, ⟨dispose, ordinaryRow, protectedRow⟩) :: table)
        ((operation, ordinaryDeps, protectedDeps) :: remainingDeps)
end

/-- Expose the checked annotation retained by this actual source body.
Ordinary bodies use their original tree; annotated bodies retain both trees. -/
theorem Body.row_annotation
    (body : Body operations policy contracts world allowed scope environment code answer header dependencies) :
    ∃ demand, ∃ normal annotated : Requirements demand,
      Expression operations policy contracts world allowed scope environment code answer demand normal dependencies ∧
      RowAnnotation normal annotated ∧
      ClauseRowAdmission.Rows header annotated (ClauseRowAdmission.SourceStore operations.erase header.owner header.contract) := by
  cases body with
  | typed source rows => exact ⟨_, _, _, source, .original, rows⟩
  | annotated source annotation rows => exact ⟨_, _, _, source, annotation, rows⟩

/-- Legacy consumers may project the normal row without selecting a different
source derivation. Source transport retains the additional annotation itself. -/
theorem Body.normal_rows
    (body : Body operations policy contracts world allowed scope environment code answer header dependencies) :
    ∃ demand, ∃ requirements : Requirements demand,
      Expression operations policy contracts world allowed scope environment code answer demand requirements dependencies ∧
      ClauseRowAdmission.Rows header requirements (ClauseRowAdmission.SourceStore operations.erase header.owner header.contract) := by
  obtain ⟨demand, normal, annotated, source, annotation, rows⟩ := body.row_annotation
  exact ⟨demand, normal, source, annotation.rows rows⟩

/-- Lift an arbitrary old continuation contract at the fixed input and answer
annotations. This is needed to erase the whole offered clause family, not just
one chosen capture. -/
def Contract.refine (contract : CoherentSourceTypes.Owners.Contract) (input answer : Value) : Contract :=
  ⟨input, answer, contract.held, contract.resumeDemand, contract.resumeRow,
    contract.closeDemand, contract.closeRow, contract.resumeEffects, contract.closeEffects⟩

theorem contract_refine_erase (inputSame : contract.input = input.erase)
    (answerSame : contract.answer = answer.erase) : (Contract.refine contract input answer).erase = contract := by
  cases contract
  cases inputSame
  cases answerSame
  rfl

/-- Reuse the complete hereditary type, clause-row and owner-requirement
judgments. Erasure preserves every existing index; it does not discard or
recompute the demand or requirement tree. -/
theorem expression_erase
    (source : Expression operations policy contracts world allowed scope environment code value demand requirements dependencies) :
    DeclaredSources.Expression operations.erase policy contracts.erase world allowed scope environment.erase code value.erase demand requirements := by
  induction source using Expression.rec
      (motive_2 := fun contracts world allowed scope environment code value header dependencies _ =>
        DeclaredSources.Body operations.erase policy contracts.erase world allowed scope environment.erase code value.erase header)
      (motive_3 := fun contracts world environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row dependencies _ =>
        DeclaredSources.Offer operations.erase policy contracts.erase world environment.erase allowed parameter binder argument.erase input.erase answer.erase
          resumeEffects closeEffects code held disposes row)
      (motive_4 := fun contracts world environment allowed requested answer clauses table dependencies _ =>
        DeclaredSources.Declarations operations.erase policy contracts.erase world environment.erase allowed requested answer.erase clauses table) with
  | unit => exact .stable .unit
  | boolean => exact .stable .boolean
  | integer => exact .stable .integer
  | reference issued => exact .stable (.reference issued)
  | «variable» known formed => exact .stable (.variable (by simp [Environment.erase, known]) formed)
  | lambda body outward formed latentBound ih => exact .lambda (by simpa only [environment_erase_extend] using ih) outward formed
  | purePair left right ihLeft ihRight => exact .purePair ihLeft ihRight
  | pair left right ihLeft ihRight => exact .pair ihLeft ihRight
  | app function argument admitted ihFunction ihArgument => exact .app ihFunction ihArgument admitted
  | bind initializer body ihInit ihBody => exact .bind ihInit (by simpa only [environment_erase_extend] using ihBody)
  | branch condition yes no same ihCondition ihYes ihNo => exact .branch ihCondition ihYes ihNo same
  | perform known admitted operand formed ih => exact .perform (operation_erase known) admitted ih formed
  | handler body clauses capabilities coverage unique admitted table modes declarations ihBody ihDecl =>
      exact .handler ihBody clauses capabilities coverage unique admitted table modes ihDecl
  | resume known resolved permission operand admitted formed ih =>
      exact .resume (contract_erase_known known) resolved permission ih admitted formed
  | discard known resolved permission unprotected admitted =>
      exact .discard (contract_erase_known known) resolved permission unprotected admitted
  | cleanup callback body admitted ihCallback ihBody => exact .cleanup ihCallback ihBody admitted
  | resource initializer body formed effectsBound admitted hidden ihInit ihBody =>
      exact .scopedResource ihInit ihBody formed effectsBound admitted hidden
  | typed source rows ih => exact .typed ih rows
  | annotated source annotation rows ih => exact .typed ih (annotation.rows rows)
  | unavailable => exact .unavailable
  | available resumeInterface closeInterface source ih =>
      apply DeclaredSources.Offer.available resumeInterface closeInterface
      intro owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
      have result := ih owner (Contract.refine contract _ _) (Option.map_eq_none_iff.mp fresh) rfl rfl resumeSame closeSame heldSame balance
      simpa only [contracts_erase_insert, environment_erase_extend, contract_refine_erase inputSame answerSame] using result
  | nil => exact .nil
  | cons known ordinary protectedMode rest ihOrdinary ihProtected ihRest =>
      exact .cons (operation_erase known) ihOrdinary ihProtected ihRest

/-- Every source cleanup retains the dependency annotation supplied by its
callback's function type and the annotation of the body that can capture it.
There is no flat-summary constructor that bypasses this rule. -/
theorem cleanup_dependencies
    (source : Expression operations policy contracts world allowed scope environment (.cleanup action code)
      output demand requirements dependencies) :
    ∃ requests latent callbackBody callbackDemand callbackReq callbackDep bodyDemand bodyReq bodyDep,
      Expression operations policy contracts world allowed scope environment action
        (.function .unit .unit requests latent callbackBody) callbackDemand callbackReq callbackDep ∧
      Expression operations policy contracts world allowed scope environment code output bodyDemand bodyReq bodyDep ∧
      dependencies = .sequence callbackDep (.cleanup requests callbackBody bodyDep) := by
  cases source with
  | cleanup callback body admitted => exact ⟨_, _, _, _, _, _, _, _, _, callback, body, rfl⟩

/-- Application uses the same latent annotation retained in the function
value type. It cannot substitute only the ordinary outward effect row. -/
theorem application_dependencies
    (source : Expression operations policy contracts world allowed scope environment (.app function argument)
      output demand requirements dependencies) :
    ∃ input requests latent body functionDemand functionReq functionDep argumentDemand argumentReq argumentDep,
      Expression operations policy contracts world allowed scope environment function
        (.function input output requests latent body) functionDemand functionReq functionDep ∧
      Expression operations policy contracts world allowed scope environment argument input argumentDemand argumentReq argumentDep ∧
      dependencies = .sequence functionDep (.sequence argumentDep body) := by
  cases source with
  | app function argument admitted => exact ⟨_, _, _, _, _, _, _, _, _, _, function, argument, rfl⟩

/-- A lambda's latent annotation has a source derivation for its actual body
at the very same input and output annotations. -/
theorem lambda_dependencies
    (source : Expression operations policy contracts world allowed scope environment (.lambda parameter code)
      (.function input output requests latent dependencies) demand requirements current) :
    ∃ bodyDemand bodyReq,
      Expression operations policy contracts world requests .none (environment.extend parameter input)
        code output bodyDemand bodyReq dependencies ∧ RecursiveOutward.Outward bodyReq (some latent) := by
  cases source with
  | lambda body outward formed latentBound => exact ⟨_, _, body, outward⟩

/-- Latent rows cannot advertise effects outside their function's declared
interface. This is a finite source rule, independent of continuation use. -/
theorem lambda_latent_bound
    (source : Expression operations policy contracts world allowed scope environment (.lambda parameter code)
      (.function input output requests latent dependencies) demand requirements current) :
    ∀ request ∈ latent, request.effect ∈ requests := by
  cases source with
  | lambda body outward formed latentBound => exact latentBound

/-- No source derivation may erase a cleanup's dependency node to pure. -/
theorem cleanup_not_pure :
    ¬ Expression operations policy contracts world allowed scope environment (.cleanup action code)
      output demand requirements .pure := by
  intro source
  cases source

/-- The same rejection holds beneath a function boundary, where the old
outward effect row alone could not retain the cleanup/body association. -/
theorem lambda_cleanup_not_flat :
    ¬ Expression operations policy contracts world allowed scope environment (.lambda parameter (.cleanup action code))
      (.function input output requests latent .pure) demand requirements current := by
  intro source
  obtain ⟨bodyDemand, bodyReq, body, outward⟩ := lambda_dependencies source
  exact cleanup_not_pure body

namespace Examples

def effectF : Instance := .user 92 []
def effectE : Instance := .user 91 []
def operations : Operations := fun _ _ => some (.unit, .unit)
def contracts : Contracts := fun _ => none
def policy : Syntax.TicketPolicy := fun _ => ⟨true, true⟩
def allowed : List Instance := [effectF, effectE]
def noRequirements : Requirements [] := .request [] []
def requestRequirements (effect : Instance) : Requirements [] := .emitAfter noRequirements [] [⟨effect, 0, false⟩]
def requestDependencies (effect : Instance) : Dependencies := .sequence .pure (.request effect 0)
def callback : Code := .lambda 0 (.perform (Instantiation.freezeEffect effectF) 0 .unit)
def cleanupBody : Code := .cleanup callback (.perform (Instantiation.freezeEffect effectE) 0 .unit)
def cleanupRequirements : Requirements [] :=
  .emitAfter (.sequence noRequirements (requestRequirements effectE)) [] [⟨effectF, 0, true⟩]
def cleanupDependencies : Dependencies :=
  .sequence .pure (.cleanup [effectF] (requestDependencies effectF) (requestDependencies effectE))
def cleanupRow : Footprint := [⟨effectE, 0, false⟩, ⟨effectF, 0, true⟩]
def functionType : Value := .function .unit .unit allowed cleanupRow cleanupDependencies

theorem cleanup_source (environment : Environment) :
    Expression operations policy contracts [] allowed .none environment cleanupBody .unit [] cleanupRequirements cleanupDependencies := by
  have callbackSource : Expression operations policy contracts [] allowed .none environment callback
      (.function .unit .unit [effectF] [⟨effectF, 0, false⟩] (requestDependencies effectF)) [] noRequirements .pure :=
    .lambda (.perform rfl (by simp) .unit
      (by simp [Value.erase, ScopedPorts.InWorld, CoherentSourceTypes.Value.port, ScopedPorts.Port.resources]))
      (.emitAfter (layers := []) (.request (layers := [])))
      (by simp [Value.erase, ScopedPorts.InWorld, CoherentSourceTypes.Value.port, ScopedPorts.Port.resources, effectF, Instance.resources])
      (by intro request member; cases List.mem_singleton.mp member; exact List.mem_cons_self)
  exact .cleanup callbackSource (.perform rfl (by simp [allowed]) .unit
    (by simp [Value.erase, ScopedPorts.InWorld, CoherentSourceTypes.Value.port, ScopedPorts.Port.resources]))
    (by simp [allowed])

theorem cleanup_outward : RecursiveOutward.Outward cleanupRequirements (some cleanupRow) :=
  .emitAfter (layers := []) (.sequence (.request (layers := [])) (.emitAfter (layers := []) (.request (layers := []))))

def functionCode : Code := .lambda 3 cleanupBody

theorem function_source : Expression operations policy contracts [] allowed .none Environment.empty
    functionCode functionType [] noRequirements .pure :=
  .lambda (cleanup_source _) cleanup_outward
    (by simp [Value.erase, ScopedPorts.InWorld, CoherentSourceTypes.Value.port,
      ScopedPorts.Port.resources, allowed, effectE, effectF, Instance.resources])
    (by intro request member; simp [cleanupRow] at member; rcases member with rfl | rfl <;> simp [allowed])

/-- The ordinary function type forgets the additional annotation. This is why
an erasure proof cannot, on its own, justify dropping the new source layer. -/
theorem same_erased_function_type : functionType.erase =
    (Value.function .unit .unit allowed cleanupRow .pure).erase := rfl

def invokedRequirements : Requirements [] := .emitAfter (.sequence noRequirements noRequirements) [] cleanupRow
def boundProgram : Code := .bind 7 functionCode (.app (.variable 7) .unit)
def boundDependencies : Dependencies := .sequence .pure (.sequence .pure (.sequence .pure cleanupDependencies))

theorem bound_function_retains_cleanup : Expression operations policy contracts [] allowed .none Environment.empty
    boundProgram .unit [] (.sequence noRequirements invokedRequirements) boundDependencies := by
  apply Expression.bind function_source
  exact .app (.variable (by simp [Environment.extend, functionType])
      (by simp [Value.erase, ScopedPorts.InWorld, CoherentSourceTypes.Value.port,
        ScopedPorts.Port.resources, allowed, effectE, effectF, Instance.resources])) .unit (List.Subset.refl _)

/-- Reuse the old source theorem rather than rebuild its ordinary and owner
proofs for the higher-order example. No handler is installed in this open term;
acceptance under a caller remains a separate dependency-checking obligation. -/
theorem bound_function_old_source :
    DeclaredSources.Expression operations.erase policy contracts.erase [] allowed .none Environment.empty.erase
      boundProgram .unit [] (.sequence noRequirements invokedRequirements) := expression_erase bound_function_retains_cleanup

end Examples

end Ash.OneShot.SourceDependencyAnnotations

#print axioms Ash.OneShot.SourceDependencyAnnotations.environment_erase_extend
#print axioms Ash.OneShot.SourceDependencyAnnotations.operation_erase
#print axioms Ash.OneShot.SourceDependencyAnnotations.contracts_erase_insert
#print axioms Ash.OneShot.SourceDependencyAnnotations.contract_refine_erase
#print axioms Ash.OneShot.SourceDependencyAnnotations.expression_erase

#print axioms Ash.OneShot.SourceDependencyAnnotations.contract_erase_known

#print axioms Ash.OneShot.SourceDependencyAnnotations.cleanup_dependencies

#print axioms Ash.OneShot.SourceDependencyAnnotations.application_dependencies

#print axioms Ash.OneShot.SourceDependencyAnnotations.lambda_dependencies
#print axioms Ash.OneShot.SourceDependencyAnnotations.lambda_latent_bound

#print axioms Ash.OneShot.SourceDependencyAnnotations.Examples.cleanup_source

#print axioms Ash.OneShot.SourceDependencyAnnotations.Examples.cleanup_outward

#print axioms Ash.OneShot.SourceDependencyAnnotations.Examples.function_source

#print axioms Ash.OneShot.SourceDependencyAnnotations.Examples.same_erased_function_type

#print axioms Ash.OneShot.SourceDependencyAnnotations.Examples.bound_function_retains_cleanup

#print axioms Ash.OneShot.SourceDependencyAnnotations.Examples.bound_function_old_source

#print axioms Ash.OneShot.SourceDependencyAnnotations.cleanup_not_pure

#print axioms Ash.OneShot.SourceDependencyAnnotations.lambda_cleanup_not_flat

#print axioms Ash.OneShot.SourceDependencyAnnotations.Body.row_annotation
#print axioms Ash.OneShot.SourceDependencyAnnotations.Body.normal_rows
