import CoreCallableStaticFiniteData

/-! Finite constructor annotations retain their exact full contracts and literal
plans. Their fields are syntax and structural tags, never Source/Auth proofs.
The checker constructs those judgments as outputs. Unsupported source forms
remain explicit full-fragment obligations. -/
namespace Ash.OneShot.CoreCallableStaticProducer
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract Environment sequenceRows choiceRows)
open CoreCallableReceiverRefinement (LexicalBounds)
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceDependencyAnnotations (Dependencies)
open SourceScheduledCleanupInterfaces.Lexical.Recursive
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open CoreCallableContractAdmission
open CoreCallableContractRegistries (Owners OwnerContract)

/-- Typed constructor data fix literal source indices. Lookup paths and recipe
instructions are finite data; successful checking will produce the judgments.
Unimplemented constructors have a named failure and remain acceptance items. -/
inductive Annotation (entries : OperationEntries) (owners : Owners) : Bindings → Code → Contract →
    (demand : List Nat) → RecursiveRequirements.Requirements demand →
    {dependencies : Dependencies} → (plan : Plan dependencies) → Rows (signature plan) → Type where
  | unit : Annotation entries owners bindings .unit .unit [] (.request [] []) .pure Rows.pure
  | boolean (value : Bool) : Annotation entries owners bindings (.boolean value) .boolean [] (.request [] []) .pure Rows.pure
  | integer (value : Int) : Annotation entries owners bindings (.integer value) .integer [] (.request [] []) .pure Rows.pure
  | reference (identity : Nat) : Annotation entries owners bindings (.resourceRef (.activation identity)) (.reference identity)
      [] (.request [] []) .pure Rows.pure
  | variable (reference : BindingRef bindings name contract) :
      Annotation entries owners bindings (.variable name) contract [] (.request [] []) .pure Rows.pure
  | pair (first : Annotation entries owners bindings a left firstDemand firstReq firstPlan firstRows)
      (second : Annotation entries owners bindings b right secondDemand secondReq secondPlan secondRows) :
      Annotation entries owners bindings (.pair a b) (.pair left right) (firstDemand ++ secondDemand)
        (.sequence firstReq secondReq) (.sequence firstPlan secondPlan) (sequenceRows firstRows secondRows)
  | bind (initializer : Annotation entries owners bindings a input firstDemand firstReq firstPlan firstRows)
      (body : Annotation entries owners ((parameter,input) :: bindings) b output secondDemand secondReq secondPlan secondRows) :
      Annotation entries owners bindings (.bind parameter a b) output (firstDemand ++ secondDemand)
        (.sequence firstReq secondReq) (.sequence firstPlan secondPlan) (sequenceRows firstRows secondRows)
  | app (function : Annotation entries owners bindings f (.function input output requests latent publicPlan publicRows)
        functionDemand functionReq functionPlan functionRows)
      (argument : Annotation entries owners bindings a input argumentDemand argumentReq argumentPlan argumentRows)
      (recipe : RecipeTag publicPlan) :
      Annotation entries owners bindings (.app f a) output (functionDemand ++ argumentDemand)
        (.emitAfter (.sequence functionReq argumentReq) [] latent)
        (.sequence functionPlan (.sequence argumentPlan publicPlan))
        (sequenceRows functionRows (sequenceRows argumentRows publicRows))
  | perform (reference : OperationRef entries effect operation input output)
      (operand : Annotation entries owners bindings value input operandDemand operandReq operandPlan operandRows) :
      Annotation entries owners bindings (.perform (Instantiation.freezeEffect effect) operation value) output
        operandDemand (.emitAfter operandReq [] [⟨effect,operation,false⟩])
        (.sequence operandPlan (.request (effect := effect) (operation := operation))) (sequenceRows operandRows Rows.request)
  | resume (reference : OwnerRef owners owner ownerContract)
      (operand : Annotation entries owners bindings value ownerContract.input operandDemand operandReq operandPlan operandRows) :
      Annotation entries owners bindings (.resume binder value) ownerContract.answer
        (operandDemand ++ owner :: ownerContract.resumeDemand)
        (.sequence operandReq (.invoke ⟨owner, .resume⟩ ownerContract.resumeDemand []))
        (.sequence operandPlan (.invoke (key := ⟨owner, .resume⟩))) (sequenceRows operandRows Rows.invoke)
  | discard (reference : OwnerRef owners owner ownerContract) :
      Annotation entries owners bindings (.discard binder) .unit (owner :: ownerContract.closeDemand)
        (.invoke ⟨owner, .dispose⟩ ownerContract.closeDemand []) (.invoke (key := ⟨owner, .dispose⟩)) Rows.invoke
  | cleanup (callback : Annotation entries owners bindings action
        (.function .unit .unit requests latent publicPlan publicRows)
        callbackDemand callbackReq callbackActualPlan callbackActualRows)
      (body : Annotation entries owners bindings code output bodyDemand bodyReq bodyPlan bodyRows)
      (recipe : RecipeTag publicPlan) :
      Annotation entries owners bindings (.cleanup action code) output (callbackDemand ++ bodyDemand)
        (.emitAfter (.sequence callbackReq bodyReq) [] (qualify true latent))
        (.sequence callbackActualPlan (.cleanup (needs := requests) publicPlan bodyPlan))
        (by simpa only [signature] using (Rows.sequence callbackActualRows (Rows.cleanup (needs := requests) latent publicRows bodyRows)))
  | branch (condition : Annotation entries owners bindings test .boolean conditionDemand conditionReq conditionPlan conditionRows)
      (yes : Annotation entries owners bindings a output yesDemand yesReq yesPlan yesRows)
      (no : Annotation entries owners bindings b output noDemand noReq noPlan noRows)
      (same : DemandPermutation yesDemand noDemand) :
      Annotation entries owners bindings (.branch test a b) output (conditionDemand ++ yesDemand)
        (.sequence conditionReq (.choice yesReq noReq same.sound))
        (.sequence conditionPlan (.choice yesPlan noPlan)) (sequenceRows conditionRows (choiceRows yesRows noRows))
  | lambda (body : Annotation entries owners ((parameter,input) :: bindings) code output bodyDemand bodyReq bodyPlan bodyRows)
      (recipe : RecipeTag publicPlan) (refinement : RefinementTag publicRows bodyRows) :
      Annotation entries owners bindings (.lambda parameter code) (.function input output requests latent publicPlan publicRows)
        [] (.request [] []) .pure Rows.pure
  | unsupported (constructor : String) : Annotation entries owners bindings code contract demand requirements plan rows


section
local instance : SourcePlannedChecks.DeclarationPolicy := declarationPolicy

/-- Internal output provenance for the constructor checker. This carrier is
built from successful recursive checks; it is not an annotation input. -/
inductive StaticTree (registry : CoreCallableContractRegistries.Registry) (outward : List Instance) :
    {owners : CoreCallableContractRegistries.Owners} → {world : List Nat} → {allowed : List Instance} →
    {scope : Execution.Scope} → {environment : Environment} → {code : Code} → {contract : Contract} →
    {demand : List Nat} → {requirements : RecursiveRequirements.Requirements demand} → {dependencies : Dependencies} →
    {plan : Plan dependencies} → {rows : Rows (signature plan)} →
    IndexedSource registry outward owners world allowed scope environment code contract demand requirements plan rows → Prop where
  | unit : StaticTree registry outward IndexedSource.unit
  | boolean : StaticTree registry outward IndexedSource.boolean
  | integer : StaticTree registry outward IndexedSource.integer
  | reference : StaticTree registry outward (IndexedSource.reference issued)
  | variable : StaticTree registry outward (IndexedSource.variable known formed)
  | pair (left : StaticTree registry outward leftSource) (right : StaticTree registry outward rightSource) :
      StaticTree registry outward (IndexedSource.pair leftSource rightSource)
  | bind (initial : StaticTree registry outward initialSource) (body : StaticTree registry outward bodySource) :
      StaticTree registry outward (IndexedSource.bind initialSource bodySource)
  | app (function : StaticTree registry outward functionSource) (argument : StaticTree registry outward argumentSource) :
      StaticTree registry outward (IndexedSource.app functionSource argumentSource admitted publicCertified)
  | resume (operand : StaticTree registry outward operandSource) :
      StaticTree registry outward (IndexedSource.resume known resolved permission operandSource admitted formed)
  | discard {owners : Owners} {scope : Execution.Scope} {contract : OwnerContract}
      {world : List Nat} {environment : Environment}
      (known : owners owner = some contract) (resolved : scope.resolve binder = some owner)
      (permission : (registry.policy binder).dispose = true) (unprotected : contract.held = false)
      (admitted : contract.closeEffects ⊆ allowed) :
      StaticTree registry outward (IndexedSource.discard (registry := registry) (outward := outward)
        (world := world) (environment := environment) known resolved permission unprotected admitted)
  | cleanup (callback : StaticTree registry outward callbackSource) (body : StaticTree registry outward bodySource) :
      StaticTree registry outward (IndexedSource.cleanup callbackSource bodySource admitted publicCertified)
  | perform (operand : StaticTree registry outward operandSource) :
      StaticTree registry outward (IndexedSource.perform known admitted operandSource formed)
  | branch (condition : StaticTree registry outward conditionSource)
      (yes : StaticTree registry outward yesSource) (no : StaticTree registry outward noSource) :
      StaticTree registry outward (IndexedSource.branch conditionSource yesSource noSource sameDemand)
  | lambda (body : StaticTree registry outward bodySource) :
      StaticTree registry outward (IndexedSource.lambda bodySource refinement bodyOutward latentBound publicCertified formed)
  /-- All fresh opened trees retain the source's complete total checking families. -/
  | resource {code : Code} {environment : Environment}
      {bodyRequirements : Nat → RecursiveRequirements.Requirements bodyDemand}
      {bodyDependencies : Nat → Dependencies}
      {bodyPlans : ∀ identity, Plan (bodyDependencies identity)}
      {bodyRows : ∀ identity, Rows (signature (bodyPlans identity))}
      {initialSource : IndexedSource registry outward owners world allowed scope environment
        initial .integer initialDemand initialRequirements initialPlan initialRows}
      {bodySource : ∀ identity, identity ∉ world →
        IndexedSource registry outward owners (world ++ [identity]) (.cell identity :: residual)
          scope environment (code.instantiate (Instantiation.Environment.empty.bind binder identity))
          output bodyDemand (bodyRequirements identity) (bodyPlans identity) (bodyRows identity)}
      {outwardRequirements : RecursiveRequirements.Requirements bodyDemand}
      {formed : ScopedPorts.InWorld world output.port}
      {effectsBound : residual.flatMap Instance.resources ⊆ world} {admitted : residual ⊆ allowed}
      {hidden : ∀ identity, identity ∉ world →
        ResourceRequirements.Hides identity (bodyRequirements identity) outwardRequirements}
      (initial : StaticTree registry outward initialSource)
      (body : ∀ identity (fresh : identity ∉ world),
        StaticTree registry outward (bodySource identity fresh)) :
      StaticTree registry outward
        (IndexedSource.resource initialSource bodySource formed effectsBound admitted hidden)
  | receiverLambda
      {publicDependencies : Dependencies} {publicPlan : Plan publicDependencies} {publicRows : Rows (signature publicPlan)}
      {valueEnvironment : Environment}
      {bodySource : IndexedSource registry outward owners world requests .none (valueEnvironment.extend parameter input)
        code output bodyDemand bodyReq bodyPlan bodyRows}
      {latent : Footprint} {bodyOutward : RecursiveOutward.Outward bodyReq (some latent)}
      {latentBound : ∀ request ∈ latent, request.effect ∈ requests}
      {publicCertified : SourcePlannedChecks.Certified outward world publicPlan}
      {formed : ScopedPorts.InWorld world (Contract.function input output requests latent publicPlan publicRows).port}
      (body : StaticTree registry outward bodySource)
      (refinement : CoreCallableRootRefinement.Refines publicRows bodyRows) :
      StaticTree registry outward (IndexedSource.receiverLambda (contractPlan := publicPlan) (contractRows := publicRows)
        (privatePlans := fun _ _ => bodyPlan) (privateRows := fun _ _ => bodyRows)
        (fun _ call => bodySource.world_weaken call.worldExtended)
        bodyOutward latentBound publicCertified formed)

private theorem known_sublist (included : first ⊆ second)
    (known : CoreCallableContractAdmission.LexicalBounds.Known lexical second) :
    CoreCallableContractAdmission.LexicalBounds.Known lexical first :=
  fun name member => known name (included member)

private theorem bounds_sublist {supportEnvironment : ScopedPorts.Support.Env} (included : first ⊆ second) (bounds : SourceSupport.Bounds supportEnvironment second receiver) :
    SourceSupport.Bounds supportEnvironment first receiver := by
  apply SourceSupport.bounds_iff.mpr
  intro identity member
  obtain ⟨dependency, member, retained⟩ := List.mem_flatMap.mp member
  exact SourceSupport.bounds_iff.mp bounds (List.mem_flatMap.mpr ⟨dependency,included member,retained⟩)

private theorem known_left (known : CoreCallableContractAdmission.LexicalBounds.Known lexical (first ++ second)) :
    CoreCallableContractAdmission.LexicalBounds.Known lexical first :=
  known_sublist (fun _ member => List.mem_append_left _ member) known
private theorem known_right (known : CoreCallableContractAdmission.LexicalBounds.Known lexical (first ++ second)) :
    CoreCallableContractAdmission.LexicalBounds.Known lexical second :=
  known_sublist (fun _ member => List.mem_append_right _ member) known
private theorem bounds_left {supportEnvironment : ScopedPorts.Support.Env}
    (bounds : SourceSupport.Bounds supportEnvironment (first ++ second) receiver) :
    SourceSupport.Bounds supportEnvironment first receiver :=
  bounds_sublist (fun _ member => List.mem_append_left _ member) bounds
private theorem bounds_right {supportEnvironment : ScopedPorts.Support.Env}
    (bounds : SourceSupport.Bounds supportEnvironment (first ++ second) receiver) :
    SourceSupport.Bounds supportEnvironment second receiver :=
  bounds_sublist (fun _ member => List.mem_append_right _ member) bounds

private theorem known_extend {lexical : LexicalBounds}
    (known : CoreCallableContractAdmission.LexicalBounds.Known lexical (Syntax.without (.variable parameter) dependencies)) :
    CoreCallableContractAdmission.LexicalBounds.Known (lexical.extend parameter argument) dependencies := by
  intro name member
  by_cases same : name = parameter
  · subst name
    exact ⟨argument, by simp [LexicalBounds.lookup, LexicalBounds.extend]⟩
  · obtain ⟨support, located⟩ := known name (Syntax.mem_without.mpr ⟨member, by simpa using same⟩)
    exact ⟨support, by simpa [LexicalBounds.lookup, LexicalBounds.extend, same] using located⟩

private theorem bounds_extend {lexical : LexicalBounds}
    (bounds : SourceSupport.Bounds lexical.environment (Syntax.without (.variable parameter) dependencies) receiver)
    (argumentBound : argument ⊆ receiver) :
    SourceSupport.Bounds (lexical.extend parameter argument).environment dependencies receiver := by
  apply SourceSupport.bounds_iff.mpr
  intro identity member
  obtain ⟨dependency, present, retained⟩ := List.mem_flatMap.mp member
  by_cases same : dependency = .variable parameter
  · subst dependency
    have included : identity ∈ argument := by
      simpa [ScopedPorts.Support.evaluate, LexicalBounds.environment_extend, ScopedPorts.Support.extend] using retained
    exact argumentBound included
  · have ordinary : dependency ∈ Syntax.without (.variable parameter) dependencies := Syntax.mem_without.mpr ⟨present,same⟩
    apply SourceSupport.bounds_iff.mp bounds
    apply List.mem_flatMap.mpr
    refine ⟨dependency,ordinary,?_⟩
    cases dependency with
    | resource | ticket => exact retained
    | «variable» name =>
      have different : name ≠ parameter := by simpa using same
      simpa [ScopedPorts.Support.evaluate, LexicalBounds.environment_extend, ScopedPorts.Support.extend, different] using retained

/-- Reconstruct hereditary authentication for every actual lexical receiver
from the same checked structural body, including future call worlds. -/
theorem StaticTree.authenticate_world {actualRegistry : CoreCallableContractRegistries.Registry}
    {source : IndexedSource actualRegistry outward owners world allowed scope valueEnvironment code contract demand requirements plan rows}
    (tree : StaticTree actualRegistry outward source) (larger : world ⊆ later)
    {lexical : LexicalBounds} {receiver : List Nat}
    (known : CoreCallableContractAdmission.LexicalBounds.Known lexical code.dependencies)
    (bounds : SourceSupport.Bounds lexical.environment code.dependencies receiver) :
    Authenticated actualRegistry outward (source.world_weaken larger) lexical receiver := by
  induction tree generalizing later lexical receiver with
  | unit => exact .checked bounds .unit
  | boolean => exact .checked bounds .boolean
  | integer => exact .checked bounds .integer
  | reference =>
      exact .checked bounds (.reference (issued := by apply larger; assumption))
  | «variable» =>
      exact .checked bounds (.variable (known := by assumption)
        (formed := ScopedPorts.in_world_mono (by assumption) larger) (known _ (by simp [Code.dependencies])))
  | pair left right ihL ihR =>
      exact .checked bounds (.pair (ihL larger (known_left known) (bounds_left bounds))
        (ihR larger (known_right known) (bounds_right bounds)))
  | bind initial body ihI ihB =>
      exact .checked bounds (.bind (ihI larger (known_left known) (bounds_left bounds))
        (ihB larger (known_extend (known_right known)) (bounds_extend (bounds_right bounds) (List.Subset.refl _))))
  | app function argument ihF ihA =>
      exact .checked bounds (.app (admitted := by assumption)
        (publicCertified := CoreCallableContractAdmission.certified_world (by assumption) larger)
        (ihF larger (known_left known) (bounds_left bounds))
        (ihA larger (known_right known) (bounds_right bounds)))
  | resume operand ih =>
      exact .checked bounds (.resume (known := by assumption) (resolved := by assumption)
        (permission := by assumption) (admitted := by assumption)
        (formed := ScopedPorts.in_world_mono (by assumption) larger)
        (ih larger
          (known_sublist (by intro dependency member; exact List.mem_cons_of_mem _ member) known)
          (bounds_sublist (by intro dependency member; exact List.mem_cons_of_mem _ member) bounds)))
  | discard =>
      exact .checked bounds (.discard (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  | cleanup callback body ihC ihB =>
      exact .checked bounds (.cleanup (admitted := by assumption)
        (publicCertified := CoreCallableContractAdmission.certified_world (by assumption) larger)
        (ihC larger (known_left known) (bounds_left bounds))
        (ihB larger (known_right known) (bounds_right bounds)))
  | perform operand ih =>
      exact .checked bounds (.perform (known := by assumption) (admitted := by assumption)
        (formed := ScopedPorts.in_world_mono (by assumption) larger)
        (ih larger (known_right known) (bounds_right bounds)))
  | branch condition yes no ihC ihY ihN =>
      exact .checked bounds (.branch (sameDemand := by assumption)
        (ihC larger (known_left (known_left known)) (bounds_left (bounds_left bounds)))
        (ihY larger (known_right (known_left known)) (bounds_right (bounds_left bounds)))
        (ihN larger (known_right known) (bounds_right bounds)))
  | lambda body ih =>
      apply Authenticated.checked bounds
      refine Hereditary.lambda (bodySource := IndexedSource.world_weaken (by assumption) larger) (refinement := by assumption) (bodyOutward := by assumption)
        (latentBound := by assumption) (publicCertified := CoreCallableContractAdmission.certified_world (by assumption) larger)
        (formed := ScopedPorts.in_world_mono (by assumption) larger) known ?_
      intro nextLexical call capturedKnown capturedReceived
      exact ih (larger.trans call.worldExtended) (known_extend capturedKnown)
        (bounds_extend (SourceSupport.bounds_iff.mpr capturedReceived) call.argumentReceived)
  | @resource bodyDemand owners0 world0 allowed0 scope0 initial0 initialDemand initialRequirements
      initialDependencies initialPlan initialRows residual binder output code0 environment0
      bodyRequirements bodyDependencies bodyPlans bodyRows initialSource bodySource outwardRequirements
      formed effectsBound admitted hidden initial body ihI ihB =>
      apply Authenticated.checked bounds
      have extension : ∀ identity, world0 ++ [identity] ⊆ later ++ [identity] := by
        intro identity
        exact List.append_subset.mpr
          ⟨fun _ present => List.mem_append_left _ (larger present),
            fun _ present => List.mem_append_right _ present⟩
      refine Hereditary.resource
        (bodySource := fun identity fresh =>
          (bodySource identity (fun present => fresh (larger present))).world_weaken
            (extension identity))
        (formed := ScopedPorts.in_world_mono formed larger)
        (effectsBound := effectsBound.trans larger) (admitted := admitted)
        (hidden := fun identity fresh => hidden identity (fun present => fresh (larger present)))
        (ihI larger (known_left known) (bounds_left bounds)) ?_
      intro identity fresh
      have oldFresh : identity ∉ world0 := fun present => fresh (larger present)
      have extended : world0 ++ [identity] ⊆ later ++ [identity] :=
        List.append_subset.mpr ⟨fun _ present => List.mem_append_left _ (larger present),
          fun _ present => List.mem_append_right _ present⟩
      apply ihB identity oldFresh extended
      · intro name member
        rcases List.mem_append.mp
          (ScopedExpressions.acquisition_dependency_bound _ _ _ member) with original | extra
        · exact known_right known name original
        · simp at extra
      · apply SourceSupport.bounds_iff.mpr
        intro value member
        obtain ⟨dependency,present,retained⟩ := List.mem_flatMap.mp member
        rcases List.mem_append.mp
          (ScopedExpressions.acquisition_dependency_bound _ _ _ present) with original | extra
        · exact List.mem_cons_of_mem _ (SourceSupport.bounds_iff.mp (bounds_right bounds)
            (List.mem_flatMap.mpr ⟨dependency,original,retained⟩))
        · have same : dependency = Syntax.Dependency.resource identity := by simpa using extra
          subst dependency
          exact List.mem_cons.mpr (Or.inl (by simpa [ScopedPorts.Support.evaluate] using retained))
  | receiverLambda body refinement ih =>
      apply Authenticated.checked bounds
      refine Hereditary.receiverLambda
        (bodySource := fun _ call => IndexedSource.world_weaken (by assumption) (larger.trans call.worldExtended))
        (bodyOutward := by assumption) (latentBound := by assumption)
        (publicCertified := CoreCallableContractAdmission.certified_world (by assumption) larger)
        (formed := ScopedPorts.in_world_mono (by assumption) larger) known ?_ ?_
      · intro nextLexical call capturedKnown capturedReceived
        exact ih (larger.trans call.worldExtended) (known_extend capturedKnown)
          (bounds_extend (SourceSupport.bounds_iff.mpr capturedReceived) call.argumentReceived)
      · intro nextLexical call _known _received
        exact CoreCallableReceiverRefinement.ReceiverRefines.of_universal refinement _ _

theorem StaticTree.outward {outward : List Instance}
    {source : IndexedSource actualRegistry outward owners world allowed scope valueEnvironment code contract demand requirements plan rows}
    (tree : StaticTree actualRegistry outward source) (normal : scope = .none) :
    ∃ row, RecursiveOutward.Outward requirements row := by
  induction tree with
  | unit | boolean | integer | reference | «variable» | lambda | receiverLambda => exact ⟨_, .request (layers := [])⟩
  | pair left right ihL ihR | bind left right ihL ihR =>
      obtain ⟨a, first⟩ := ihL normal
      obtain ⟨b, second⟩ := ihR normal
      exact ⟨_, .sequence first second⟩
  | app function argument ihF ihA =>
      obtain ⟨a, first⟩ := ihF normal
      obtain ⟨b, second⟩ := ihA normal
      exact ⟨_, .emitAfter (layers := []) (.sequence first second)⟩
  | cleanup callback body ihC ihB =>
      obtain ⟨a, first⟩ := ihC normal
      obtain ⟨b, second⟩ := ihB normal
      exact ⟨_, .emitAfter (layers := []) (.sequence first second)⟩
  | branch condition yes no ihC ihY ihN =>
      obtain ⟨a, first⟩ := ihC normal
      obtain ⟨b, second⟩ := ihY normal
      obtain ⟨c, third⟩ := ihN normal
      exact ⟨_, .sequence first (.choice second third)⟩
  | @resource bodyDemand owners0 world0 allowed0 scope0 initial0 initialDemand initialRequirements
      initialDependencies initialPlan initialRows residual binder output code0 environment0
      bodyRequirements bodyDependencies bodyPlans bodyRows initialSource bodySource outwardRequirements
      formed effectsBound admitted hidden initial body ihI ihB =>
      obtain ⟨firstRow,first⟩ := ihI normal
      obtain ⟨identity,fresh⟩ := ScopedTyping.fresh_world_name _
      obtain ⟨bodyRow,opened⟩ := ihB identity fresh normal
      obtain ⟨closedRow,closed⟩ := RecursiveOutward.hidden (hidden identity fresh) opened
      exact ⟨_,.sequence first closed⟩
  | resume | discard =>
      cases normal
      simp_all [Execution.Scope.resolve]
  | perform operand ih =>
      obtain ⟨row, current⟩ := ih normal
      exact ⟨_, .emitAfter (layers := []) current⟩

private theorem StaticTree.checked_outward {outward : List Instance}
    {source : IndexedSource actualRegistry outward owners world allowed scope valueEnvironment code contract demand requirements plan rows}
    (tree : StaticTree actualRegistry outward source)
    (normal : scope = .none) (checked : RecursiveRequirements.evaluate [] [] OwnerPhaseTransitions.empty requirements = some latent) :
    RecursiveOutward.Outward requirements (some latent) := by
  obtain ⟨row, actual⟩ := tree.outward normal
  have same : row = some latent := (RecursiveOutward.isolated_evaluation actual).symm.trans checked
  cases same
  exact actual

/-- This is the checker output, with exact literal source indices. -/
structure Result (entries : OperationEntries) (policy : Syntax.TicketPolicy) (outward : List Instance)
    (owners : CoreCallableContractRegistries.Owners) (world : List Nat) (allowed : List Instance)
    (scope : Execution.Scope) (bindings : Bindings) (code : Code) (contract : Contract)
    (demand : List Nat) (requirements : RecursiveRequirements.Requirements demand)
    {dependencies : Dependencies} (plan : Plan dependencies) (rows : Rows (signature plan))
    (lexical : LexicalBounds) (receiver : List Nat) : Type where
  source : IndexedSource (registry entries policy) outward owners world allowed scope
    (environment bindings) code contract demand requirements plan rows
  authenticated : Authenticated (registry entries policy) outward source lexical receiver
  receivingIssued : receiver ⊆ world
  tree : StaticTree (registry entries policy) outward source

private def finish
    (source : IndexedSource (registry entries policy) outward owners world allowed scope
      (environment bindings) code contract demand requirements plan rows)
    (tree : StaticTree (registry entries policy) outward source) :
    Except Error (Result entries policy outward owners world allowed scope bindings code contract demand requirements plan rows lexical receiver) :=
  if issued : CoreCallableGraphAnnotationChecks.subsetB receiver world = true then
    if valid : CoreCallableGraphAnnotationChecks.subsetB
        (ScopedPorts.Support.evaluate lexical.environment code.dependencies) receiver = true then
      if known : CoreCallableGraphAnnotationChecks.knownB lexical code.dependencies = true then
        .ok ⟨source, tree.authenticate_world (List.Subset.refl _) (CoreCallableGraphAnnotationChecks.knownB_sound known)
          (SourceSupport.bounds_iff.mpr (CoreCallableGraphAnnotationChecks.subsetB_sound valid)),
          CoreCallableGraphAnnotationChecks.subsetB_sound issued, tree⟩
      else .error .missingLexicalSupport
    else .error .support
  else .error .unissuedPort

/-- Execute the finite recursive constructor checks. Every recursive call builds
actual source/authentication from child annotation data. Unsupported branches
return explicit errors; they do not admit a reduced language fragment. -/
def check (annotation : Annotation entries owners bindings code contract demand requirements plan rows)
    (policy : Syntax.TicketPolicy) (outward : List Instance) (world : List Nat) (allowed : List Instance) (scope : Execution.Scope)
    (lexical : LexicalBounds) (receiver : List Nat) :
    Except Error (Result entries policy outward owners world allowed scope bindings code contract demand requirements plan rows lexical receiver) :=
  match annotation with
  | .unit => finish .unit .unit
  | .boolean _ => finish .boolean .boolean
  | .integer _ => finish .integer .integer
  | .reference identity =>
    if issued : decide (identity ∈ world) = true then
      finish (.reference (of_decide_eq_true issued)) (.reference (issued := of_decide_eq_true issued))
    else .error .unissuedPort
  | @Annotation.variable _ _ bindings name contract reference =>
    if located : reference.check = true then
      if formed : CoreCallableGraphAnnotationChecks.subsetB contract.port.resources world = true then
        if _known : CoreCallableGraphAnnotationChecks.knownB lexical [Syntax.Dependency.variable name] = true then
          finish (.variable (reference.sound located) (CoreCallableGraphAnnotationChecks.subsetB_sound formed))
            (.variable (known := reference.sound located) (formed := CoreCallableGraphAnnotationChecks.subsetB_sound formed))
        else .error .missingLexicalSupport
      else .error .unissuedPort
    else .error .lexicalShadowing
  | .pair first second => do
    let a ← check first policy outward world allowed scope lexical receiver
    let b ← check second policy outward world allowed scope lexical receiver
    finish (.pair a.source b.source) (.pair a.tree b.tree)
  | .bind (parameter := parameter) initializer body => do
    let a ← check initializer policy outward world allowed scope lexical receiver
    let b ← check body policy outward world allowed scope (lexical.extend parameter receiver) receiver
    finish (.bind a.source b.source) (.bind a.tree b.tree)
  | .app (requests := requests) function argument recipe => do
    let f ← check function policy outward world allowed scope lexical receiver
    let a ← check argument policy outward world allowed scope lexical receiver
    if admitted : CoreCallableGraphAnnotationChecks.subsetB requests allowed = true then
      if accepted : recipe.check = true then
        finish (.app f.source a.source (CoreCallableGraphAnnotationChecks.subsetB_sound admitted) (recipe.sound accepted).certified)
          (.app (admitted := CoreCallableGraphAnnotationChecks.subsetB_sound admitted)
            (publicCertified := (recipe.sound accepted).certified) f.tree a.tree)
      else .error .unsupportedRecipe
    else .error .unavailableEffect
  | .perform (effect := effect) (output := output) reference operand => do
    let a ← check operand policy outward world allowed scope lexical receiver
    if known : reference.check = true then
      if admitted : decide (effect ∈ allowed) = true then
        if formed : CoreCallableGraphAnnotationChecks.subsetB output.port.resources world = true then
          finish (.perform (reference.sound known) (of_decide_eq_true admitted) a.source
            (CoreCallableGraphAnnotationChecks.subsetB_sound formed)) (.perform (known := reference.sound known) (admitted := of_decide_eq_true admitted)
              (formed := CoreCallableGraphAnnotationChecks.subsetB_sound formed) a.tree)
        else .error .unissuedPort
      else .error .unavailableEffect
    else .error .operationShadowing
  | .resume (owner := owner) (ownerContract := ownerContract) (binder := binder) reference operand => do
    let value ← check operand policy outward world allowed scope lexical receiver
    if located : reference.check = true then
      if resolved : decide (scope.resolve binder = some owner) = true then
        if permitted : (policy binder).resume = true then
          if admitted : CoreCallableGraphAnnotationChecks.subsetB ownerContract.resumeEffects allowed = true then
            if formed : CoreCallableGraphAnnotationChecks.subsetB ownerContract.answer.port.resources world = true then
              finish (.resume (reference.sound located) (of_decide_eq_true resolved) permitted value.source
                (CoreCallableGraphAnnotationChecks.subsetB_sound admitted) (CoreCallableGraphAnnotationChecks.subsetB_sound formed))
                (.resume (known := reference.sound located) (resolved := of_decide_eq_true resolved)
                  (permission := permitted) (admitted := CoreCallableGraphAnnotationChecks.subsetB_sound admitted)
                  (formed := CoreCallableGraphAnnotationChecks.subsetB_sound formed) value.tree)
            else .error .unissuedPort
          else .error .unavailableEffect
        else .error .capability
      else .error .ownerScope
    else .error .ownerShadowing
  | .discard (owner := owner) (ownerContract := ownerContract) (binder := binder) reference =>
    if located : reference.check = true then
      if resolved : decide (scope.resolve binder = some owner) = true then
        if permitted : (policy binder).dispose = true then
          if unprotected : ownerContract.held = false then
            if admitted : CoreCallableGraphAnnotationChecks.subsetB ownerContract.closeEffects allowed = true then
              finish (.discard (reference.sound located) (of_decide_eq_true resolved) permitted unprotected
                (CoreCallableGraphAnnotationChecks.subsetB_sound admitted))
                (.discard (reference.sound located) (of_decide_eq_true resolved) permitted unprotected (CoreCallableGraphAnnotationChecks.subsetB_sound admitted))
            else .error .unavailableEffect
          else .error .protectedOwner
        else .error .capability
      else .error .ownerScope
    else .error .ownerShadowing
  | .cleanup (requests := requests) callback body recipe => do
    let action ← check callback policy outward world allowed scope lexical receiver
    let current ← check body policy outward world allowed scope lexical receiver
    if admitted : CoreCallableGraphAnnotationChecks.subsetB requests allowed = true then
      if accepted : recipe.check = true then
        finish (.cleanup action.source current.source (CoreCallableGraphAnnotationChecks.subsetB_sound admitted) (recipe.sound accepted).certified)
          (.cleanup (admitted := CoreCallableGraphAnnotationChecks.subsetB_sound admitted)
            (publicCertified := (recipe.sound accepted).certified) action.tree current.tree)
      else .error .unsupportedRecipe
    else .error .unavailableEffect
  | .branch condition yes no same => do
    let tested ← check condition policy outward world allowed scope lexical receiver
    let first ← check yes policy outward world allowed scope lexical receiver
    let second ← check no policy outward world allowed scope lexical receiver
    finish (.branch tested.source first.source second.source same.sound)
      (.branch (sameDemand := same.sound) tested.tree first.tree second.tree)
  | .lambda (parameter := parameter) (input := input) (output := output) (requests := requests)
      (latent := latent) (publicPlan := publicPlan) (publicRows := publicRows) (bodyReq := bodyReq) (bodyPlan := bodyPlan) (bodyRows := bodyRows) body recipe refinement => do
    let actual ← check body policy outward world requests .none (lexical.extend parameter receiver) receiver
    if accepted : recipe.check = true then
      if admitted : latent.all (fun request => decide (request.effect ∈ requests)) = true then
        if formed : CoreCallableGraphAnnotationChecks.subsetB
            (Contract.function input output requests latent publicPlan publicRows).port.resources world = true then
          if summary : decide (RecursiveRequirements.evaluate [] [] OwnerPhaseTransitions.empty bodyReq = some latent) = true then
            let source := IndexedSource.receiverLambda
              (privatePlans := fun _ _ => bodyPlan) (privateRows := fun _ _ => bodyRows)
              (fun _ call => actual.source.world_weaken call.worldExtended)
              (actual.tree.checked_outward rfl (of_decide_eq_true summary))
              (fun request member => of_decide_eq_true ((List.all_eq_true.mp admitted) request member))
              (recipe.sound accepted).certified (CoreCallableGraphAnnotationChecks.subsetB_sound formed)
            finish source (.receiverLambda
              (bodyOutward := actual.tree.checked_outward rfl (of_decide_eq_true summary))
              (latentBound := fun request member => of_decide_eq_true ((List.all_eq_true.mp admitted) request member))
              (publicCertified := (recipe.sound accepted).certified)
              (formed := CoreCallableGraphAnnotationChecks.subsetB_sound formed) actual.tree refinement.sound)
          else .error .latentSummary
        else .error .unissuedPort
      else .error .latentAllowance
    else .error .unsupportedRecipe
  | .unsupported constructor => .error (.unsupported constructor)
/-- The ordinary recursive evidence is connected to one actual graph origin.
Shape is checked on the entire finite arena; literal code agreement uses the
existing translator comparison, never an erased signature. -/
structure GraphResult (graph : CoreSyntax.Graph) (site : Nat) (maps : CoreTranslation.OwnerMap)
    (resources : Instantiation.Environment) (entries : OperationEntries) (policy : Syntax.TicketPolicy)
    (outward : List Instance) (owners : CoreCallableContractRegistries.Owners)
    (world : List Nat) (allowed : List Instance) (scope : Execution.Scope) (bindings : Bindings)
    (code : Code) (contract : Contract) (demand : List Nat) (requirements : RecursiveRequirements.Requirements demand)
    {dependencies : Dependencies} (plan : Plan dependencies) (rows : Rows (signature plan))
    (lexical : LexicalBounds) (receiver : List Nat) : Type where
  current : Result entries policy outward owners world allowed scope bindings code contract demand requirements plan rows lexical receiver
  node : CoreSyntax.Node
  raw : Code
  shape : CoreSyntax.ShapeChecked graph
  siteKnown : graph.node site = some node
  metadata : SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphAdmission.Metadata
    resources node contract.value (node.effects.map (fun effect => effect.instantiate resources))
  declaredEffects : (node.effects.map (fun effect => effect.instantiate resources)) ⊆
    SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphAdmission.allowanceEffects allowed
  translated : CoreTranslation.translateFuel graph (graph.nodes.length + 1) maps site = .ok raw
  literalCode : raw.instantiate resources = code

def checkGraph (graph : CoreSyntax.Graph) (site : Nat) (maps : CoreTranslation.OwnerMap)
    (resources : Instantiation.Environment)
    (annotation : Annotation entries owners bindings code contract demand requirements plan rows)
    (policy : Syntax.TicketPolicy) (outward : List Instance) (world : List Nat) (allowed : List Instance) (scope : Execution.Scope)
    (lexical : LexicalBounds) (receiver : List Nat) :
    Except Error (GraphResult graph site maps resources entries policy outward owners world allowed scope
      bindings code contract demand requirements plan rows lexical receiver) :=
  match checkedShape : CoreSyntax.checkShape graph with
  | .error error => .error (.graphShape error)
  | .ok () => match found : graph.node site with
    | none => .error .graphNode
    | some node =>
      if typed : CoreCallableGraphAnnotationChecks.typeB resources node.type contract = true then
        if effects : CoreCallableGraphAnnotationChecks.subsetB (node.effects.map (fun effect => effect.instantiate resources))
            (SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphAdmission.allowanceEffects allowed) = true then
          match translated : CoreTranslation.translateFuel graph (graph.nodes.length + 1) maps site with
          | .error error => .error (.graphTranslation error)
          | .ok raw =>
            if same : CoreCallableChecks.codeEq (raw.instantiate resources) code = true then do
              let current ← check annotation policy outward world allowed scope lexical receiver
              pure ⟨current,node,raw,checkedShape,found,⟨CoreCallableGraphAnnotationChecks.typeB_sound typed, fun _ => Iff.rfl⟩,
                CoreCallableGraphAnnotationChecks.subsetB_sound effects,translated,CoreCallableChecks.codeEq_sound _ _ same⟩
            else .error .graphCode
        else .error .graphMetadata
      else .error .graphMetadata
end

end Ash.OneShot.CoreCallableStaticProducer

#print axioms Ash.OneShot.CoreCallableStaticProducer.BindingRef.sound
#print axioms Ash.OneShot.CoreCallableStaticProducer.RecipeTag.sound
#print axioms Ash.OneShot.CoreCallableStaticProducer.PureTag.sound
#print axioms Ash.OneShot.CoreCallableStaticProducer.RefinementTag.sound
#print axioms Ash.OneShot.CoreCallableStaticProducer.OperationRef.sound
#print axioms Ash.OneShot.CoreCallableStaticProducer.DemandPermutation.sound
#print axioms Ash.OneShot.CoreCallableStaticProducer.StaticTree.authenticate_world
#print axioms Ash.OneShot.CoreCallableStaticProducer.StaticTree.outward
#print axioms Ash.OneShot.CoreCallableStaticProducer.StaticTree.checked_outward
#print axioms Ash.OneShot.CoreCallableStaticProducer.check
#print axioms Ash.OneShot.CoreCallableStaticProducer.checkGraph

#print axioms Ash.OneShot.CoreCallableStaticProducer.OwnerRef.sound
