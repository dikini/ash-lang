import CoreCallableStaticFiniteData

/-! The existing complete constructor output carrier and its original generic
proofs live below the producer. Annotation/checker inputs remain unchanged. -/
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

end

end Ash.OneShot.CoreCallableStaticProducer
