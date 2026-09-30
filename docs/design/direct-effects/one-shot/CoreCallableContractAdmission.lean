import CoreCallableContractRegistries

/-! Experimental authenticated contract source. Exact global operation contracts,
execution scope, scalar requirements, actual declaration plans and contextual
rows are separate indices. This is not legacy Auth or M4 admission. -/
namespace Ash.OneShot.CoreCallableContractAdmission
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceDependencyAnnotations (Dependencies)
open RecursiveRequirements (Requirements)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open CoreCallableContractSource (Contract Environment sequenceRows choiceRows)
open CoreCallableContractRegistries (Registry OwnerContract Owners)
open CoreCallableRootRefinement (Refines RootTransport)
open SourceDependencyAnnotations (RowAnnotation)
open RecursiveRequirements (Checked)
open SourceScheduledCleanupInterfaces.Lexical.Recursive (annotateDisposals)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourcePlannedChecks (Certified DeclarationPolicy)

/-- Fixed registry and owner policy shared by every recursive constructor.
Owner endpoints are mutable source indices; operations and policy are fixed. -/
structure Globals where
  operations : Instance → Nat → Option (Contract × Contract)
  policy : Syntax.TicketPolicy
  owners : Owners

def Globals.registry (globals : Globals) : Registry := ⟨globals.operations, globals.policy⟩
def Globals.withOwner (globals : Globals) (owner : Nat) (contract : OwnerContract) : Globals :=
  { globals with owners := globals.owners.insert owner contract }
@[simp] theorem Globals.registry_withOwner {globals : Globals} {owner : Nat} {contract : OwnerContract} : (globals.withOwner owner contract).registry = globals.registry := rfl

def Globals.ports (globals : Globals) : ScopedPorts.Signature :=
  fun effect operation => (globals.operations effect operation).map (fun pair => (pair.1.port, pair.2.port))

section
variable [DeclarationPolicy]

/-- Each lambda recursively authenticates its private body. Public-plan
certification is static declaration evidence, independent of port formation;
application cannot infer it from a function's immediate pure plan. -/
inductive IndexedSource (registry : Registry) (outward : List Instance) :
    Owners → List Nat → List Instance → Execution.Scope → Environment → Code → Contract →
    (demand : List Nat) → Requirements demand → {dependencies : Dependencies} →
    (plan : Plan dependencies) → Rows (signature plan) → Prop where
  | unit : IndexedSource registry outward owners world allowed scope environment .unit .unit [] (.request [] []) .pure Rows.pure
  | boolean : IndexedSource registry outward owners world allowed scope environment (.boolean value) .boolean [] (.request [] []) .pure Rows.pure
  | integer : IndexedSource registry outward owners world allowed scope environment (.integer value) .integer [] (.request [] []) .pure Rows.pure
  | reference (issued : identity ∈ world) :
      IndexedSource registry outward owners world allowed scope environment (.resourceRef (.activation identity)) (.reference identity) [] (.request [] []) .pure Rows.pure
  | variable (known : environment name = some contract) (formed : ScopedPorts.InWorld world contract.port) :
      IndexedSource registry outward owners world allowed scope environment (.variable name) contract [] (.request [] []) .pure Rows.pure
  | lambda {contractDependencies : Dependencies} {contractPlan : Plan contractDependencies}
      {contractRows : Rows (signature contractPlan)}
      (body : IndexedSource registry outward owners world requests .none (environment.extend parameter input) code output bodyDemand bodyReq actualPlan actualRows)
      (refinement : Refines contractRows actualRows)
      (bodyOutward : RecursiveOutward.Outward bodyReq (some latent))
      (latentBound : ∀ request ∈ latent, request.effect ∈ requests)
      (publicCertified : Certified outward world contractPlan)
      (formed : ScopedPorts.InWorld world (Contract.function input output requests latent contractPlan contractRows).port) :
      IndexedSource registry outward owners world allowed scope environment (.lambda parameter code)
        (Contract.function input output requests latent contractPlan contractRows) [] (.request [] []) .pure Rows.pure
  | purePair (left : IndexedSource registry outward owners world allowed scope environment a first [] (.request [] []) .pure Rows.pure)
      (right : IndexedSource registry outward owners world allowed scope environment b second [] (.request [] []) .pure Rows.pure) :
      IndexedSource registry outward owners world allowed scope environment (.pair a b) (.pair first second) [] (.request [] []) .pure Rows.pure
  | pair (left : IndexedSource registry outward owners world allowed scope environment a first leftDemand leftReq leftPlan leftRows)
      (right : IndexedSource registry outward owners world allowed scope environment b second rightDemand rightReq rightPlan rightRows) :
      IndexedSource registry outward owners world allowed scope environment (.pair a b) (.pair first second)
        (leftDemand ++ rightDemand) (.sequence leftReq rightReq) (.sequence leftPlan rightPlan) (sequenceRows leftRows rightRows)
  | app (function : IndexedSource registry outward owners world allowed scope environment f
        (Contract.function input output requests latent contractPlan contractRows) functionDemand functionReq functionPlan functionRows)
      (argument : IndexedSource registry outward owners world allowed scope environment a input argumentDemand argumentReq argumentPlan argumentRows)
      (admitted : requests ⊆ allowed)
      (publicCertified : Certified outward world contractPlan) :
      IndexedSource registry outward owners world allowed scope environment (.app f a) output
        (functionDemand ++ argumentDemand) (.emitAfter (.sequence functionReq argumentReq) [] latent)
        (.sequence functionPlan (.sequence argumentPlan contractPlan)) (sequenceRows functionRows (sequenceRows argumentRows contractRows))
  | bind (initializer : IndexedSource registry outward owners world allowed scope environment a input initialDemand initialReq initialPlan initialRows)
      (body : IndexedSource registry outward owners world allowed scope (environment.extend parameter input) b output bodyDemand bodyReq bodyPlan bodyRows) :
      IndexedSource registry outward owners world allowed scope environment (.bind parameter a b) output
        (initialDemand ++ bodyDemand) (.sequence initialReq bodyReq) (.sequence initialPlan bodyPlan) (sequenceRows initialRows bodyRows)
  | branch (condition : IndexedSource registry outward owners world allowed scope environment test .boolean conditionDemand conditionReq conditionPlan conditionRows)
      (yes : IndexedSource registry outward owners world allowed scope environment a output yesDemand yesReq yesPlan yesRows)
      (no : IndexedSource registry outward owners world allowed scope environment b output noDemand noReq noPlan noRows)
      (same : yesDemand.Perm noDemand) :
      IndexedSource registry outward owners world allowed scope environment (.branch test a b) output
        (conditionDemand ++ yesDemand) (.sequence conditionReq (.choice yesReq noReq same))
        (.sequence conditionPlan (.choice yesPlan noPlan)) (sequenceRows conditionRows (choiceRows yesRows noRows))
  | perform (known : registry.operations effect operation = some (input, output)) (admitted : effect ∈ allowed)
      (operand : IndexedSource registry outward owners world allowed scope environment value input operandDemand operandReq operandPlan operandRows)
      (formed : ScopedPorts.InWorld world output.port) :
      IndexedSource registry outward owners world allowed scope environment (.perform (Instantiation.freezeEffect effect) operation value) output
        operandDemand (.emitAfter operandReq [] [⟨effect, operation, false⟩])
        (.sequence operandPlan (.request (effect := effect) (operation := operation))) (sequenceRows operandRows Rows.request)


  | resume (known : owners owner = some contract) (resolved : scope.resolve binder = some owner)
      (permission : (registry.policy binder).resume = true)
      (operand : IndexedSource registry outward owners world allowed scope environment value contract.input operandDemand operandReq operandPlan operandRows)
      (admitted : contract.resumeEffects ⊆ allowed) (formed : ScopedPorts.InWorld world contract.answer.port) :
      IndexedSource registry outward owners world allowed scope environment (.resume binder value) contract.answer
        (operandDemand ++ owner :: contract.resumeDemand) (.sequence operandReq (.invoke ⟨owner, .resume⟩ contract.resumeDemand []))
        (.sequence operandPlan (.invoke (key := ⟨owner, .resume⟩))) (sequenceRows operandRows Rows.invoke)
  | discard (known : owners owner = some contract) (resolved : scope.resolve binder = some owner)
      (permission : (registry.policy binder).dispose = true) (unprotected : contract.held = false)
      (admitted : contract.closeEffects ⊆ allowed) :
      IndexedSource registry outward owners world allowed scope environment (.discard binder) .unit
        (owner :: contract.closeDemand) (.invoke ⟨owner, .dispose⟩ contract.closeDemand []) (.invoke (key := ⟨owner, .dispose⟩)) Rows.invoke

/-- Compatibility view: the immutable registry is a parameter; owner table
and historical world are genuine recursive indices. -/
abbrev Source (globals : Globals) (outward : List Instance) (world : List Nat) :=
  IndexedSource globals.registry outward globals.owners world

abbrev Source.unit := @IndexedSource.unit
abbrev Source.boolean := @IndexedSource.boolean
abbrev Source.integer := @IndexedSource.integer
abbrev Source.reference := @IndexedSource.reference
abbrev Source.variable := @IndexedSource.variable
abbrev Source.lambda := @IndexedSource.lambda
abbrev Source.purePair := @IndexedSource.purePair
abbrev Source.pair := @IndexedSource.pair
abbrev Source.app := @IndexedSource.app
abbrev Source.bind := @IndexedSource.bind
abbrev Source.branch := @IndexedSource.branch
abbrev Source.perform := @IndexedSource.perform
abbrev Source.resume := @IndexedSource.resume
abbrev Source.discard := @IndexedSource.discard

/-- Actual-plan declaration certification follows structural derivation;
application separately checks its exposed plan, and lambda bodies stay recursive. -/
theorem IndexedSource.certified (source : IndexedSource registry outward owners world allowed scope environment code contract demand requirements plan rows) :
    Certified outward world plan := by
  induction source with
  | unit | boolean | integer | reference | «variable» | lambda | purePair => exact .pure
  | pair left right ihL ihR | bind left right ihL ihR => exact .sequence ihL ihR
  | app function argument admitted publicCertified ihF ihA => exact .sequence ihF (.sequence ihA publicCertified)
  | branch condition yes no same ihC ihY ihN => exact .sequence ihC (.choice ihY ihN)
  | perform known admitted operand formed ih => exact .sequence ih .request
  | resume known resolved permission operand admitted formed ih => exact .sequence ih .invoke
  | discard => exact .invoke


abbrev Source.certified := @IndexedSource.certified

theorem IndexedSource.erase_at (source : IndexedSource registry outward owners world allowed scope environment code contract demand requirements plan rows)
    (scopeTyped : ScopedPorts.EffectScope owners.lower.ports scope ticket) :
    ScopedPorts.Typed registry.ports world environment.ports ticket allowed code contract.port := by
  induction source generalizing ticket with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference issued => exact .reference issued
  | «variable» known formed => exact .variable (by simp [Environment.ports, known]) formed
  | lambda body refinement bodyOutward latentBound publicCertified formed ih =>
      exact .lambda (by simpa only [Environment.ports_extend, Contract.port] using ih ScopedPorts.EffectScope.none) formed
  | purePair left right ihL ihR | pair left right ihL ihR => exact .pair (ihL scopeTyped) (ihR scopeTyped)
  | app function argument admitted publicCertified ihF ihA => exact .app (ihF scopeTyped) (ihA scopeTyped) admitted
  | bind initial body ihI ihB => exact .bind (ihI scopeTyped) (by simpa using ihB scopeTyped)
  | branch condition yes no same ihC ihY ihN => exact .branch (ihC scopeTyped) (ihY scopeTyped) (ihN scopeTyped)
  | perform known admitted operand formed ih => exact .perform (by simp only [Registry.ports, known, Option.map_some]) admitted (ih scopeTyped) formed

  | resume known resolved permission operand admitted formed ih =>
      have same := CoherentSourceTypes.Owners.scope_resolved scopeTyped (CoreCallableContractRegistries.Owners.known_lower known) resolved
      subst ticket
      exact .resume (ih scopeTyped) admitted formed
  | discard known resolved permission unprotected admitted =>
      have same := CoherentSourceTypes.Owners.scope_resolved scopeTyped (CoreCallableContractRegistries.Owners.known_lower known) resolved
      subst ticket
      exact .discard admitted

abbrev Source.erase_at := @IndexedSource.erase_at

/-- Owner-free execution scope erases to the empty ticket interface. -/
theorem IndexedSource.erase (source : IndexedSource registry outward owners world allowed .none environment code contract demand requirements plan rows) :
    ScopedPorts.Typed registry.ports world environment.ports .none allowed code contract.port :=
  source.erase_at .none

abbrev Source.erase := @IndexedSource.erase

theorem IndexedSource.environment_congr (source : IndexedSource registry outward owners world allowed scope environment code contract demand requirements plan rows)
    (agree : ∀ name, Syntax.Dependency.variable name ∈ code.dependencies → environment name = destination name) :
    IndexedSource registry outward owners world allowed scope destination code contract demand requirements plan rows := by
  induction source generalizing destination with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference issued => exact .reference issued
  | «variable» known formed => exact .variable ((agree _ (by simp [Code.dependencies])).symm.trans known) formed
  | lambda body refinement bodyOutward latentBound publicCertified formed ih =>
      rename_i parameter contractDependencies contractPlan contractRows
      apply Source.lambda (ih ?_) refinement bodyOutward latentBound publicCertified formed
      intro name member
      by_cases same : name = parameter
      · subst name; simp [Environment.extend]
      · simp only [Environment.extend, same, ↓reduceIte]
        exact agree name (Syntax.mem_without.mpr ⟨member, by simpa using same⟩)
  | purePair left right ihL ihR =>
      exact .purePair (ihL (fun name member => agree name (List.mem_append_left _ member)))
        (ihR (fun name member => agree name (List.mem_append_right _ member)))
  | pair left right ihL ihR =>
      exact .pair (ihL (fun name member => agree name (List.mem_append_left _ member)))
        (ihR (fun name member => agree name (List.mem_append_right _ member)))
  | app function argument admitted publicCertified ihF ihA =>
      exact .app (ihF (fun name member => agree name (List.mem_append_left _ member)))
        (ihA (fun name member => agree name (List.mem_append_right _ member))) admitted publicCertified
  | bind initial body ihI ihB =>
      rename_i parameter b output bodyDemand bodyReq bodyDependencies bodySignature bodyRows
      apply Source.bind (ihI (fun name member => agree name (List.mem_append_left _ member))) (ihB ?_)
      intro name member
      by_cases same : name = parameter
      · subst name; simp [Environment.extend]
      · simp only [Environment.extend, same, ↓reduceIte]
        exact agree name (List.mem_append_right _ (Syntax.mem_without.mpr ⟨member, by simpa using same⟩))
  | branch condition yes no sameDemand ihC ihY ihN =>
      exact .branch
        (ihC (fun name member => agree name (List.mem_append_left _ (List.mem_append_left _ member))))
        (ihY (fun name member => agree name (List.mem_append_left _ (List.mem_append_right _ member))))
        (ihN (fun name member => agree name (List.mem_append_right _ member))) sameDemand

  | perform known admitted operand formed ih =>
      exact .perform known admitted (ih (fun name member => agree name (List.mem_append_right _ member))) formed

  | resume known resolved permission operand admitted formed ih =>
      exact .resume known resolved permission (ih (fun name member => agree name (List.mem_cons_of_mem _ member))) admitted formed
  | discard known resolved permission unprotected admitted => exact .discard known resolved permission unprotected admitted


abbrev Source.environment_congr := @IndexedSource.environment_congr

theorem IndexedSource.closed_environment (source : IndexedSource registry outward owners world allowed scope environment value contract [] (.request [] []) .pure Rows.pure)
    (closed : ClosedValue value) (destination : Environment) : IndexedSource registry outward owners world allowed scope destination value contract [] (.request [] []) .pure Rows.pure :=
  source.environment_congr (fun _ member => False.elim (ScopedTyping.closedValue_no_variable closed member))


abbrev Source.closed_environment := @IndexedSource.closed_environment

/-- Closed values retain their public contract when the caller's allowed row
changes. The private lambda body continues under its own declared requests. -/
theorem IndexedSource.value_allowed (source : IndexedSource registry outward owners world allowed scope environment value contract demand requirements plan rows)
    (valueIsValue : value.IsValue) (next : List Instance) (nextScope : Execution.Scope) : IndexedSource registry outward owners world next nextScope environment value contract demand requirements plan rows := by
  induction source with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference issued => exact .reference issued
  | lambda body refinement bodyOutward latentBound publicCertified formed ih => exact .lambda body refinement bodyOutward latentBound publicCertified formed
  | purePair left right ihL ihR => exact .purePair (ihL valueIsValue.1) (ihR valueIsValue.2)
  | pair left right ihL ihR => exact .pair (ihL valueIsValue.1) (ihR valueIsValue.2)
  | «variable» | app | bind | branch | perform | resume | discard => cases valueIsValue


abbrev Source.value_allowed := @IndexedSource.value_allowed

/-- Normalize only immediate checking rows of a value. The public contract
and each lambda's private recursive body/refinement remain unchanged. -/
theorem IndexedSource.value_summary (source : IndexedSource registry outward owners world allowed scope environment value contract demand requirements plan rows)
    (valueIsValue : value.IsValue) : IndexedSource registry outward owners world allowed scope environment value contract [] (.request [] []) .pure Rows.pure := by
  induction source with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference issued => exact .reference issued
  | lambda body refinement bodyOutward latentBound publicCertified formed ih => exact .lambda body refinement bodyOutward latentBound publicCertified formed
  | purePair left right ihL ihR | pair left right ihL ihR =>
      exact .purePair (ihL valueIsValue.1) (ihR valueIsValue.2)
  | «variable» | app | bind | branch | perform | resume | discard => cases valueIsValue


abbrev Source.value_summary := @IndexedSource.value_summary

/-- Compositional substitution for this contract judgment. It preserves the
same exposed contract and rows, including private lambda-body refinements. -/
theorem IndexedSource.substitution_at (source : IndexedSource registry outward owners world allowed scope sourceEnvironment code result demand requirements plan rows) :
    ∀ environment name input value, sourceEnvironment = environment.extend name input →
      IndexedSource registry outward owners world allowed scope environment value input [] (.request [] []) .pure Rows.pure → ClosedValue value →
      IndexedSource registry outward owners world allowed scope environment (code.subst name value) result demand requirements plan rows := by
  induction source with
  | unit | boolean | integer | reference =>
      intro environment name input value same replacement closed
      cases same
      first | exact .unit | exact .boolean | exact .integer | apply Source.reference; assumption
  | «variable» known formed =>
      intro environment name input value same replacement closed
      cases same
      simp only [Code.subst]
      split
      · rename_i equal
        subst name
        simp only [Environment.extend, ↓reduceIte] at known
        cases Option.some.inj known
        exact replacement
      · rename_i different
        exact .variable (by simpa [Environment.extend, Ne.symm different] using known) formed
  | lambda body refinement bodyOutward latentBound publicCertified formed ih =>
      intro environment name input value same replacement closed
      cases same
      simp only [Code.subst]
      apply Source.lambda _ refinement bodyOutward latentBound publicCertified formed
      split
      · rename_i equal
        subst name
        simpa only [Environment.extend_shadow] using body
      · rename_i different
        exact ih _ name input value (Environment.extend_commute environment name _ input _ different)
          ((replacement.value_allowed closed.1 _ .none).closed_environment closed _) closed
  | purePair left right ihL ihR =>
      intro environment name input value same replacement closed
      cases same
      exact .purePair (ihL environment name input value rfl replacement closed) (ihR environment name input value rfl replacement closed)
  | pair left right ihL ihR =>
      intro environment name input value same replacement closed
      cases same
      exact .pair (ihL environment name input value rfl replacement closed) (ihR environment name input value rfl replacement closed)
  | app function argument admitted publicCertified ihF ihA =>
      intro environment name input value same replacement closed
      cases same
      exact .app (ihF environment name input value rfl replacement closed) (ihA environment name input value rfl replacement closed) admitted publicCertified
  | bind initial body ihI ihB =>
      intro environment name input value same replacement closed
      cases same
      simp only [Code.subst]
      apply Source.bind (ihI environment name input value rfl replacement closed)
      split
      · rename_i equal
        subst name
        simpa only [Environment.extend_shadow] using body
      · rename_i different
        exact ihB _ name input value (Environment.extend_commute environment name _ input _ different)
          (replacement.closed_environment closed _) closed
  | branch condition yes no sameDemand ihC ihY ihN =>
      intro environment name input value same replacement closed
      cases same
      exact .branch (ihC environment name input value rfl replacement closed)
        (ihY environment name input value rfl replacement closed) (ihN environment name input value rfl replacement closed) sameDemand

  | perform known admitted operand formed ih =>
      intro environment name input value same replacement closed
      cases same
      simpa only [Code.subst] using Source.perform known admitted
        (ih environment name input value rfl replacement closed) formed

  | resume known resolved permission operand admitted formed ih =>
      intro environment name input value same replacement closed
      cases same
      simpa only [Code.subst] using IndexedSource.resume known resolved permission
        (ih environment name input value rfl replacement closed) admitted formed
  | discard known resolved permission unprotected admitted =>
      intro environment name input value same replacement closed
      cases same
      exact .discard known resolved permission unprotected admitted


abbrev Source.substitution_at := @IndexedSource.substitution_at

theorem IndexedSource.substitution
    (source : IndexedSource registry outward owners world allowed scope (environment.extend name input) code result demand requirements plan rows)
    (replacement : IndexedSource registry outward owners world allowed scope environment value input [] (.request [] []) .pure Rows.pure) (closed : ClosedValue value) :
    IndexedSource registry outward owners world allowed scope environment (code.subst name value) result demand requirements plan rows :=
  source.substitution_at environment name input value rfl replacement closed


abbrev Source.substitution := @IndexedSource.substitution

/-- Closed products as well as primitive and callable values may substitute;
only their immediate value-checking rows are normalized. -/
theorem IndexedSource.closed_substitution
    (source : IndexedSource registry outward owners world allowed scope (environment.extend name input) code result demand requirements plan rows)
    (replacement : IndexedSource registry outward owners world allowed scope environment value input replacementDemand replacementRequirements replacementPlan replacementRows) (closed : ClosedValue value) :
    IndexedSource registry outward owners world allowed scope environment (code.subst name value) result demand requirements plan rows :=
  source.substitution (replacement.value_summary closed.1) closed


abbrev Source.closed_substitution := @IndexedSource.closed_substitution

/-- Actual values have no immediate continuation invocation demand, even
when their private callable body has an owner-sensitive plan. -/
theorem IndexedSource.value_demand
    (source : IndexedSource registry outward owners world allowed scope environment code contract demand requirements plan rows)
    (isValue : code.IsValue) : demand = [] := by
  induction source with
  | unit | boolean | integer | reference | «variable» | lambda | purePair => rfl
  | pair left right ihL ihR => simp [ihL isValue.1, ihR isValue.2]
  | app | bind | branch | perform | resume | discard => cases isValue

abbrev Source.value_demand := @IndexedSource.value_demand

/-- Independent support authenticates actual dependencies against finite
lexical value-support entries and the issued world, never port resources. -/
structure Supported (globals : Globals) (outward : List Instance) (world : List Nat)
    (allowed : List Instance) (scope : Execution.Scope) (environment : Environment)
    (supportEnvironment : ScopedPorts.Support.Env) (code : Code) (contract : Contract)
    (demand : List Nat) (requirements : Requirements demand)
    {dependencies : Dependencies} (plan : Plan dependencies) (rows : Rows (signature plan)) (bound : List Nat) : Prop where
  source : Source globals outward world allowed scope environment code contract demand requirements plan rows
  support : SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.Bounds supportEnvironment code.dependencies bound
  issued : bound ⊆ world

namespace Supported
open SourceScheduledCleanupInterfaces.Lexical.Recursive
open ScopedPorts.Support (evaluate extend)
theorem canonical (source : Source globals outward world allowed scope environment code contract demand requirements plan rows)
    (supportEnvironment : ScopedPorts.Support.Env) (issued : evaluate supportEnvironment code.dependencies ⊆ world) :
    Supported globals outward world allowed scope environment supportEnvironment code contract demand requirements plan rows
      (evaluate supportEnvironment code.dependencies) := ⟨source, SourceSupport.Bounds.canonical _ _, issued⟩

theorem substitution
    (body : Supported globals outward world allowed scope (environment.extend name input)
      (extend supportEnvironment name valueBound) code output demand requirements plan rows bodyBound)
    (replacement : Supported globals outward world allowed scope environment replacementEnvironment value input
      replacementDemand replacementRequirements replacementPlan replacementRows valueBound)
    (closed : ClosedValue value) :
    Supported globals outward world allowed scope environment supportEnvironment (code.subst name value)
      output demand requirements plan rows bodyBound := by
  refine ⟨IndexedSource.closed_substitution body.source replacement.source closed, ?_, body.issued⟩
  apply SourceSupport.bounds_iff.mpr
  exact (ScopedPorts.Support.substitution_support_bound code name closed replacement.support.resources).trans
    (SourceSupport.bounds_iff.mp body.support)
end Supported

/-- Recovered private body includes scalar outward authentication and actual
certification. No desired successor or legacy exact-body typing is supplied. -/
theorem IndexedSource.lambda_body
    (source : IndexedSource registry outward owners world allowed scope environment (.lambda parameter body)
      (Contract.function input output requests latent contractPlan contractRows) [] (.request [] []) .pure Rows.pure) :
    ∃ (bodyDemand : List Nat) (bodyReq : Requirements bodyDemand) (actualDependencies : Dependencies)
      (actualPlan : Plan actualDependencies) (actualRows : Rows (signature actualPlan)),
      IndexedSource registry outward owners world requests .none (environment.extend parameter input) body output bodyDemand bodyReq actualPlan actualRows ∧
      Refines contractRows actualRows ∧ RecursiveOutward.Outward bodyReq (some latent) ∧
      Certified outward world actualPlan ∧ Certified outward world contractPlan := by
  cases source with
  | lambda body refinement bodyOutward latentBound publicCertified formed =>
      exact ⟨_, _, _, _, _, body, refinement, bodyOutward, body.certified, publicCertified⟩


abbrev Source.lambda_body := @IndexedSource.lambda_body

theorem IndexedSource.beta
    (function : IndexedSource registry outward owners world allowed scope environment (.lambda parameter body)
      (Contract.function input output requests latent contractPlan contractRows) [] (.request [] []) .pure Rows.pure)
    (argument : IndexedSource registry outward owners world requests .none environment value input argumentDemand argumentReq argumentPlan argumentRows)
    (closed : ClosedValue value) (closureReady : ClosedValue (.lambda parameter body)) (stack : Stack) :
    ∃ (bodyDemand : List Nat) (bodyReq : Requirements bodyDemand) (actualDependencies : Dependencies)
      (actualPlan : Plan actualDependencies) (actualRows : Rows (signature actualPlan)),
      IndexedSource registry outward owners world requests .none environment (body.subst parameter value) output bodyDemand bodyReq actualPlan actualRows ∧
      Certified outward world actualPlan ∧ Refines contractRows actualRows ∧ RecursiveOutward.Outward bodyReq (some latent) ∧
      RawStep ⟨.app (.lambda parameter body) value, scope, stack⟩ ⟨body.subst parameter value, .none, stack⟩ [] [] := by
  obtain ⟨demand, requirements, dependencies, plan, rows, actualBody, refinement, bodyOutward, actualCertified, publicCertified⟩ := function.lambda_body
  exact ⟨demand, requirements, dependencies, plan, rows, actualBody.closed_substitution argument closed,
    actualCertified, refinement, bodyOutward, .beta parameter body value scope stack closed closureReady⟩


abbrev Source.beta := @IndexedSource.beta

/-- Request inversion uses the same fixed operation table for input and result. -/
theorem IndexedSource.request_contract
    (source : IndexedSource registry outward owners world allowed scope environment
      (.perform (Instantiation.freezeEffect effect) operation value) output demand requirements plan rows) :
    ∃ input, registry.operations effect operation = some (input, output) := by
  generalize equation : Code.perform (Instantiation.freezeEffect effect) operation value = code at source
  cases source <;> try { cases equation }
  case perform =>
    rename_i actual operationActual input valueActual deps operandPlan operandRows admitted known formed operandReq operand
    simp only [Code.perform.injEq] at equation
    obtain ⟨sameEffect, sameOperation, sameValue⟩ := equation
    have same : effect = actual := Instantiation.effect_realization_unique
      (Instantiation.frozen_effect_realizes Instantiation.Environment.empty effect)
      (by rw [sameEffect]; exact Instantiation.frozen_effect_realizes Instantiation.Environment.empty actual)
    subst actual
    subst operationActual
    exact ⟨input, known⟩


abbrev Source.request_contract := @IndexedSource.request_contract

/-- Operand authentication and result contract come from one exact global key. -/
theorem IndexedSource.request_operand
    (source : IndexedSource registry outward owners world allowed scope environment
      (.perform (Instantiation.freezeEffect effect) operation value) output demand requirements plan rows) :
    ∃ (input : Contract) (operandDemand : List Nat) (operandReq : Requirements operandDemand)
      (operandDependencies : Dependencies) (operandPlan : Plan operandDependencies) (operandRows : Rows (signature operandPlan)),
      registry.operations effect operation = some (input, output) ∧
      IndexedSource registry outward owners world allowed scope environment value input operandDemand operandReq operandPlan operandRows := by
  generalize equation : Code.perform (Instantiation.freezeEffect effect) operation value = code at source
  cases source <;> try { cases equation }
  case perform =>
    rename_i actual operationActual input valueActual deps operandPlan operandRows admitted known formed operandReq operand
    simp only [Code.perform.injEq] at equation
    obtain ⟨sameEffect, sameOperation, sameValue⟩ := equation
    have same : effect = actual := Instantiation.effect_realization_unique
      (Instantiation.frozen_effect_realizes Instantiation.Environment.empty effect)
      (by rw [sameEffect]; exact Instantiation.frozen_effect_realizes Instantiation.Environment.empty actual)
    subst actual
    subst operationActual
    subst valueActual
    exact ⟨input, _, operandReq, deps, operandPlan, operandRows, known, operand⟩


abbrev Source.request_operand := @IndexedSource.request_operand

/-- Recover actual effectful body and declaration certification while transporting
only current certificates/accounting. Scalar body requirements and contextual
root demand are separate existential/indexed data, not equated. -/
theorem IndexedSource.beta_current
    (function : IndexedSource registry outward owners world allowed runtimeScope environment (.lambda parameter body)
      (Contract.function input output requests latent contractPlan contractRows) [] (.request [] []) .pure Rows.pure)
    (argument : IndexedSource registry outward owners world requests .none environment value input argumentDemand argumentReq argumentPlan argumentRows)
    (closed : ClosedValue value) (closureReady : ClosedValue (.lambda parameter body))
    (stack : Stack)
    (installations ambient : List Nat) (actions : Syntax.UsageTickets)
    (phases : OwnerPhaseTransitions.Phases) (budget : Footprint)
    {scope : SourceDependencyCapture.Scope} {hints : SourceDependencyChecks.Lexical.ReturnHints scope}
    (context : Context hints)
    (certificate : SourceAdmission.Code outward actions budget phases world installations contractRows context)
    (certificateChecked : InstallationSupport.CodeChecked ambient outward certificate)
    (root annotated : Requirements demand)
    (run : Accounting.Run world installations contractRows context root)
    (entries : RecursiveRequirements.Store) (receiving : OwnerPhases.Context) (row : Footprint)
    (annotation : RowAnnotation root annotated)
    (check : Checked entries receiving phases (annotateDisposals annotated) row) (bounded : row ⊆ budget) :
    ∃ (actualDependencies : Dependencies) (actualPlan : Plan actualDependencies)
      (actualRows : Rows (signature actualPlan)),
      ∃ (bodyDemand : List Nat) (bodyReq : Requirements bodyDemand),
      IndexedSource registry outward owners world requests .none environment (body.subst parameter value) output bodyDemand bodyReq actualPlan actualRows ∧
      Certified outward world actualPlan ∧
      RawStep ⟨.app (.lambda parameter body) value, runtimeScope, stack⟩
        ⟨body.subst parameter value, .none, stack⟩ [] [] ∧
      ∃ actualCertificate : SourceAdmission.Code outward actions budget phases world installations actualRows context,
        InstallationSupport.CodeChecked ambient outward actualCertificate ∧
        ∃ actualRoot actualAnnotated : Requirements demand, ∃ actualRow : Footprint,
          Accounting.Run world installations actualRows context actualRoot ∧
          RootTransport root actualRoot ∧ RowAnnotation actualRoot actualAnnotated ∧
          Checked entries receiving phases (annotateDisposals actualAnnotated) actualRow ∧ actualRow ⊆ budget := by
  obtain ⟨bodyDemand, bodyReq, dependencies, plan, rows, bodySource, actualCertified, refinement, bodyOutward, raw⟩ :=
    function.beta argument closed closureReady stack
  let actualCertificate := refinement.code outward actions budget phases world installations context certificate
  obtain ⟨actualRoot, actualAnnotated, actualRow, actualRun, transport, actualAnnotation, actualCheck, actualBound⟩ :=
    CoreCallableRootRefinement.checked_accounting refinement world installations context root annotated run
      entries receiving phases budget row annotation check bounded
  exact ⟨dependencies, plan, rows, bodyDemand, bodyReq, bodySource, actualCertified, raw, actualCertificate,
    refinement.checked ambient outward actions budget phases world installations context certificate certificateChecked,
    actualRoot, actualAnnotated, actualRow, actualRun, transport, actualAnnotation, actualCheck, actualBound⟩


abbrev Source.beta_current := @IndexedSource.beta_current

/-- Bind substitution comes from the same structural source derivation. -/
theorem IndexedSource.bind_step
    (source : IndexedSource registry outward owners world allowed scope environment (.bind parameter value body) output
      demand (.sequence (.request [] []) bodyReq) (.sequence .pure bodyPlan) (sequenceRows Rows.pure bodyRows))
    (closed : ClosedValue value) (ready : ClosedExcept parameter body) (stack : Stack) :
    IndexedSource registry outward owners world allowed scope environment (body.subst parameter value) output demand bodyReq bodyPlan bodyRows ∧
      Certified outward world bodyPlan ∧
      RawStep ⟨.bind parameter value body, scope, stack⟩ ⟨body.subst parameter value, scope, stack⟩ [] [] := by
  cases source with
  | bind initializer bodySource =>
      exact ⟨bodySource.substitution initializer closed, bodySource.certified, .bind parameter value body scope stack closed ready⟩

abbrev Source.bind_step := @IndexedSource.bind_step

#print axioms Globals.registry_withOwner
#print axioms Source.bind_step
#print axioms Source.beta_current
#print axioms Source.certified
#print axioms Source.erase
#print axioms Source.environment_congr
#print axioms Source.value_summary
#print axioms Source.closed_substitution
#print axioms Source.value_demand
#print axioms Source.erase_at
#print axioms Supported.substitution
#print axioms Source.lambda_body
#print axioms Source.beta
#print axioms Source.request_operand
#print axioms Source.request_contract
end
end Ash.OneShot.CoreCallableContractAdmission
