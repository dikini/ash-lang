import CoreCallableOuterLambdaOrigins
namespace Ash.OneShot.CoreCallableOrdinaryRuntimeOrigins
open ScopedExpressions ScopedExecution ProtectionContracts CoreValueRelation
open CoreCallableContractAdmission CoreCallableContractSource CoreCallablePairedOrigin
open CoreCallableCapturedLambdaConstructor
open CoreCallableReceiverRefinement (LexicalBounds)
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceDependencyAnnotations (Dependencies)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
local instance : SourcePlannedChecks.DeclarationPolicy :=
  SourceScheduledCleanupInterfaces.Lexical.Recursive.declarationPolicy

/-- Produced finite replacement data; no judgments or future state fields. -/
structure Replacement where
  name : Nat
  code : Code
  frozen : CoreCallableReturnStorageProducer.Annotation

def closeCode : List Replacement → Code → Code
  | [], code => code
  | replacement :: rest, code => closeCode rest (code.subst replacement.name replacement.code)

def closeTree : List Replacement → Code → CoreCallableReturnStorageProducer.Annotation →
    CoreCallableReturnStorageProducer.Annotation
  | [], _, annotation => annotation
  | replacement :: rest, code, annotation =>
      closeTree rest (code.subst replacement.name replacement.code)
        (CoreCallableCapturedRecipes.substitute code annotation replacement.name replacement.frozen)

def closeBody : List Replacement → Nat → Code → Code
  | [], _, body => body
  | replacement :: rest, formal, body =>
      closeBody rest formal (if replacement.name = formal then body else body.subst replacement.name replacement.code)

theorem closeCode_lambda (replacements : List Replacement) (formal : Nat) (body : Code) :
    closeCode replacements (.lambda formal body) = .lambda formal (closeBody replacements formal body) := by
  induction replacements generalizing body with
  | nil => rfl
  | cons replacement rest ih =>
    simp only [closeCode,closeBody,Code.subst]
    split <;> exact ih _

/-- This output receipt records past produced replacements and actual values. -/
inductive ProducedBindings (registry : CoreCallableContractRegistries.Registry)
    (declarations : Instantiation.DeclarationRegistry) (outward : List Instance)
    (owners : CoreCallableContractRegistries.Owners) (world : List Nat) (allowed : List Instance)
    (scope : Execution.Scope) (receiver : List Nat) (graph : CoreSyntax.Graph)
    (coreOwners : CoreTranslation.OwnerMap) (heap : CoreMachine.Heap) :
    List Replacement → CoreCallableStaticProducer.Bindings → CoreCallableReturnStorageProducer.Bindings →
    LexicalBounds → MEnv → Prop where
  | empty : ProducedBindings registry declarations outward owners world allowed scope receiver graph coreOwners heap [] [] [] [] .empty
  | bind
      (previous : ProducedBindings registry declarations outward owners world allowed scope receiver graph coreOwners heap replacements rich storage lexical saved)
      (source : IndexedSource registry outward owners world allowed scope Environment.empty valueCode richInput [] (.request [] []) .pure Rows.pure)
      (authenticated : Authenticated registry outward source [] receiver)
      (finite : CoreCallableReturnStorageProducer.check [] valueCode frozen = some storageInput)
      (bounded : storageInput.storageOf ⊆ receiver)
      (related : ValueRel graph coreOwners heap value valueCode) :
      ProducedBindings registry declarations outward owners world allowed scope receiver graph coreOwners heap
        ({name := name,code := valueCode,frozen := frozen} :: replacements)
        ((name,richInput)::rich) (CoreCallableReturnStorageProducer.extend storage name storageInput)
        (lexical.extend name receiver) (.binding name value saved)

theorem ProducedBindings.closes
    (produced : ProducedBindings registry declarations outward owners world allowed scope receiver graph coreOwners heap replacements rich storage lexical saved)
    (code : Code) : EnvCloses graph coreOwners heap saved code (closeCode replacements code) := by
  induction produced generalizing code with
  | empty => exact .empty
  | bind previous source authenticated finite bounded related ih => exact .binding related (ih _)

theorem ProducedBindings.finite
    (produced : ProducedBindings registry declarations outward owners world allowed scope receiver graph coreOwners heap replacements rich storage lexical saved)
    (accepted : CoreCallableReturnStorageProducer.check storage code annotation = some result) :
    CoreCallableReturnStorageProducer.check [] (closeCode replacements code) (closeTree replacements code annotation) = some result := by
  induction produced generalizing code annotation with
  | empty => exact accepted
  | bind previous source authenticated finite bounded related ih =>
    exact ih (CoreCallableCapturedRecipes.check_substitute accepted finite related.closed)

/-- Each link retains the exact private family constructor receipt. -/
inductive ConstructorChain
    (registry : CoreCallableContractRegistries.Registry) (outward : List Instance)
    (owners : CoreCallableContractRegistries.Owners) (world : List Nat) (allowed : List Instance)
    (scope : Execution.Scope) :
    (stable : SubstitutionPolicyStable outward) →
    (formal : Nat) → (input output : Contract) → (requests : List Instance) → (latent : Footprint) →
    {publicDependencies : Dependencies} → (publicPlan : Plan publicDependencies) → (publicRows : Rows (signature publicPlan)) →
    (replacements : List Replacement) → (bindings : CoreCallableStaticProducer.Bindings) → (body : Code) →
    IndexedSource registry outward owners world allowed scope (CoreCallableStaticProducer.environment bindings)
      (.lambda formal body) (.function input output requests latent publicPlan publicRows) [] (.request [] []) .pure Rows.pure →
    (final : Code) → Family registry outward owners world Environment.empty formal final input output requests latent publicPlan publicRows → Prop where
  | empty
      (source : IndexedSource registry outward owners world allowed scope Environment.empty
        (.lambda formal body) (.function input output requests latent publicPlan publicRows) [] (.request [] []) .pure Rows.pure)
      (family : Family registry outward owners world Environment.empty formal body input output requests latent publicPlan publicRows)
      (origin : Origin source family) :
      ConstructorChain registry outward owners world allowed scope @stable formal input output requests latent publicPlan publicRows [] [] body source body family
  | bind
      (source : IndexedSource registry outward owners world allowed scope (CoreCallableStaticProducer.environment ((name,richInput)::bindings))
        (.lambda formal body) (.function input output requests latent publicPlan publicRows) [] (.request [] []) .pure Rows.pure)
      (nextFamily : Family registry outward owners world (CoreCallableStaticProducer.environment bindings) formal nextBody input output requests latent publicPlan publicRows)
      (replacement : IndexedSource registry outward owners world allowed scope
        (CoreCallableStaticProducer.environment bindings) valueCode richInput [] (.request [] []) .pure Rows.pure)
      (closed : ClosedValue valueCode)
      (receipt : Receipt source replacement stable closed nextBody nextFamily)
      (tail : ConstructorChain registry outward owners world allowed scope @stable formal input output requests latent publicPlan publicRows
        rest bindings nextBody nextFamily.whole final family) :
      ConstructorChain registry outward owners world allowed scope @stable formal input output requests latent publicPlan publicRows
        ({name := name,code := valueCode,frozen := frozen} :: rest) ((name,richInput)::bindings) body source final family

/-- Reconstruct from original authentication, never a chosen final family. -/
theorem ProducedBindings.close_lambda
    (produced : ProducedBindings registry declarations outward owners world allowed scope receiver graph coreOwners heap replacements rich storage lexical saved)
    (source : IndexedSource registry outward owners world allowed scope (CoreCallableStaticProducer.environment rich)
      (.lambda formal body) (.function input output requests latent publicPlan publicRows) [] (.request [] []) .pure Rows.pure)
    (authenticated : Authenticated registry outward source lexical receiver)
    (stable : SubstitutionPolicyStable outward) :
    ∃ family : Family registry outward owners world Environment.empty formal (closeBody replacements formal body) input output requests latent publicPlan publicRows,
      ConstructorChain registry outward owners world allowed scope @stable formal input output requests latent publicPlan publicRows
        replacements rich body source (closeBody replacements formal body) family ∧
      Authenticated registry outward (family.whole (allowed := allowed) (scope := scope)) [] receiver := by
  induction produced generalizing body with
  | empty =>
    obtain ⟨family,origin,authentic,known⟩ := extract authenticated
    have auth : Authenticated registry outward (family.whole (allowed := allowed) (scope := scope)) [] receiver := by
      exact .checked authenticated.current_support
        (.receiverLambda family.bodyOutward family.latentBound family.publicCertified family.formed known authentic.1 authentic.2)
    exact ⟨family,.empty source family origin,auth⟩
  | @bind replacements rich storage lexical saved valueCode richInput frozen storageInput value name previous replacement replacementAuth finite bounded related ih =>
    let retargeted := replacement.closed_environment related.closed (CoreCallableStaticProducer.environment rich)
    have retargetedAuth : Authenticated registry outward retargeted lexical receiver :=
      (replacementAuth.closed_environment related.closed _).lexical_congr
        (fun _ member => False.elim (ScopedTyping.closedValue_no_variable related.closed member))
    have resources : Syntax.resourceDependencies valueCode.dependencies ⊆ receiver :=
      (CoreCallableCapturedRecipes.checked_value_support finite related.closed).trans bounded
    obtain ⟨nextBody,nextFamily,receipt,computed,nextAuth⟩ :=
      reconstruct authenticated stable retargeted related.closed resources retargetedAuth
    have shape : nextBody = if name = formal then body else body.subst name valueCode := by
      simp only [Code.subst] at computed
      split at computed <;> simp_all
    subst nextBody
    obtain ⟨family,chain,finalAuth⟩ := ih nextFamily.whole nextAuth
    exact ⟨family,ConstructorChain.bind (frozen := frozen) source nextFamily retargeted related.closed receipt chain,finalAuth⟩
/-- Empty lexical authentication plus full storage constructs logical closure. -/
theorem empty_lambda_closed
    (source : IndexedSource registry outward owners world allowed scope Environment.empty
      (.lambda formal body) (.function input output requests latent publicPlan publicRows) [] (.request [] []) .pure Rows.pure)
    (auth : Authenticated registry outward source [] receiver)
    (stored : CallableContracts.Derives declarations environment world .none (.lambda formal body) result) :
    ClosedValue (.lambda formal body) := by
  obtain ⟨family,origin,authentic,known⟩ := extract auth
  refine ⟨by trivial,CallableContracts.resource_closed stored,?_⟩
  intro dependency member
  cases dependency with
  | resource identity => trivial
  | «variable» name =>
    obtain ⟨resources,found⟩ := known name member
    simp [CoreCallableReceiverRefinement.LexicalBounds.lookup] at found
  | ticket owner => exact CoreCallableOuterLambdaOrigins.lambda_no_ticket stored owner member

/-- Original finite template/map attachment. Closure freezes this selected
specialization before substitution; it never reinterprets it in a later map. -/
structure StorageAttachment (bindings : CoreCallableReturnStorageProducer.Bindings)
    (annotation : CoreCallableReturnStorageProducer.Annotation) where
  originalMap : Instantiation.Environment
  originalRecipe : CoreCallableStorageRecipes.Recipe
  specialized : CoreCallableStorageRecipes.specialize bindings originalMap originalRecipe = some annotation

/-- Only literal original graph/path guards. No runtime relation, returned
value, execution history, or future environment is an input field. -/
inductive GraphPrefix (graph : CoreSyntax.Graph) (coreOwners : CoreTranslation.OwnerMap)
    (fuel rootSite : Nat) (receiver : List Nat)
    (entries : CoreCallableStaticProducer.OperationEntries) (owners : CoreCallableContractRegistries.Owners)
    (policy : Syntax.TicketPolicy) (declarations : Instantiation.DeclarationRegistry)
    (outward : List Instance) (world : List Nat) (allowed : List Instance) (scope : Execution.Scope)
    {rootCode rootContract rootDemand rootReq rootDeps} {rootPlan : Plan rootDeps} {rootRows}
    (root : CoreCallableStaticProducer.Annotation entries owners [] rootCode rootContract rootDemand rootReq rootPlan rootRows) :
    {bindings : CoreCallableStaticProducer.Bindings} → {code : Code} → {contract : Contract} →
    {demand : List Nat} → {requirements : RecursiveRequirements.Requirements demand} →
    {dependencies : Dependencies} → {plan : Plan dependencies} → {rows : Rows (signature plan)} →
    {body : CoreCallableStaticProducer.Annotation entries owners bindings code contract demand requirements plan rows} →
    {storage : CoreCallableReturnStorageProducer.Bindings} → {lexical : LexicalBounds} →
    {records : List CoreCallableReturnStorageProducer.BindingAnnotation} →
    BindPath receiver entries owners root body storage lexical records → Nat → Prop where
  | here (translated : CoreTranslation.translateFuel graph fuel coreOwners rootSite = .ok rootCode) :
      GraphPrefix graph coreOwners fuel rootSite receiver entries owners policy declarations outward world allowed scope root .here rootSite
  | bind
      {initial : CoreCallableStaticProducer.Annotation entries owners bindings (.lambda formal initialBody)
        (.function input output requests latent publicPlan publicRows) [] (.request [] []) .pure Rows.pure}
      {body : CoreCallableStaticProducer.Annotation entries owners ((binder.id,.function input output requests latent publicPlan publicRows)::bindings)
        bodyCode bodyContract bodyDemand bodyReq bodyPlan bodyRows}
      {preceding : BindPath receiver entries owners root (.bind (parameter := binder.id) initial body) storage lexical records}
      (previous : GraphPrefix graph coreOwners fuel rootSite receiver entries owners policy declarations outward world allowed scope root preceding bindSite)
      (known : graph.node bindSite = some node) (kind : node.kind = .bind binder initializerSite bodySite)
      (initialTranslation : CoreTranslation.translateFuel graph fuel coreOwners initializerSite = .ok (.lambda formal initialBody))
      (bodyTranslation : CoreTranslation.translateFuel graph fuel coreOwners bodySite = .ok bodyCode)
      (initialAccepted : ∃ actual : CoreCallableStaticProducer.Result entries policy outward owners world allowed scope bindings
        (.lambda formal initialBody) (.function input output requests latent publicPlan publicRows) [] (.request [] []) .pure Rows.pure lexical receiver,
        CoreCallableStaticProducer.check initial policy outward world allowed scope lexical receiver = .ok actual)
      (storageAccepted : CoreCallableReturnStorageProducer.check storage (.lambda formal initialBody) storageAnnotation = some storageInput)
      (bounded : storageInput.storageOf ⊆ receiver)
      (attachment : StorageAttachment storage storageAnnotation)
      (callableAccepted : ∃ certificate, CoreCallableChecks.checkAmbient graph initializerSite coreOwners = .ok certificate) :
      GraphPrefix graph coreOwners fuel rootSite receiver entries owners policy declarations outward world allowed scope root
        (BindPath.bind preceding storageAnnotation storageInput) bodySite

/-- Positive counted actual Core execution; each ordinary installation adds
entry, checked lambda evaluation, and saved bind return. -/
inductive Steps (graph : CoreSyntax.Graph) : Nat → CoreMachine.State → CoreMachine.State → Prop where
  | zero : Steps graph 0 state state
  | step (actual : CoreMachine.next graph before = .stepped next) (rest : Steps graph count next after) :
      Steps graph (count + 1) before after

theorem Steps.append (first : Steps graph a before middle) (last : Steps graph b middle after) :
    Steps graph (a + b) before after := by
  induction first with
  | zero => simpa using last
  | step actual rest ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Steps.step actual (ih last)

/-- Counted execution retains each actual checked value witness, its strict
rank decrease, and the saved environment installed by the matching bind return. -/
inductive Evaluations (graph : CoreSyntax.Graph) (coreOwners : CoreTranslation.OwnerMap) :
    List Replacement → CoreMachine.State → CoreMachine.State → Prop where
  | empty : Evaluations graph coreOwners [] state state
  | bind (previous : Evaluations graph coreOwners replacements start before)
      (entry : CoreMachine.next graph before = .stepped entered)
      (witness : CoreAdministrativeSteps.ValueWitness graph coreOwners entered evaluated valueCode)
      (finish : CoreMachine.next graph evaluated = .stepped completed)
      (beforeControl : before.control = .evaluate bindSite saved)
      (enteredControl : entered.control = .evaluate initializerSite saved)
      (enteredFrames : entered.frames = .bind name bodySite saved :: before.frames)
      (returned : evaluated.control = .returned value)
      (completedControl : completed.control = .evaluate bodySite (.binding name value saved))
      (completedFrames : completed.frames = before.frames) :
      Evaluations graph coreOwners ({name := name,code := valueCode,frozen := frozen} :: replacements) start completed

/-- Original initializer/private-family association retained for every path
extension, indexed by the actual computed finite replacement data. -/
inductive InitializerLineage (receiver : List Nat)
    (entries : CoreCallableStaticProducer.OperationEntries) (owners : CoreCallableContractRegistries.Owners)
    (policy : Syntax.TicketPolicy) (declarations : Instantiation.DeclarationRegistry)
    (outward : List Instance) (world : List Nat) (allowed : List Instance) (scope : Execution.Scope)
    (stable : SubstitutionPolicyStable outward)
    {rootCode rootContract rootDemand rootReq rootDeps} {rootPlan : Plan rootDeps} {rootRows}
    (root : CoreCallableStaticProducer.Annotation entries owners [] rootCode rootContract rootDemand rootReq rootPlan rootRows) :
    {bindings : CoreCallableStaticProducer.Bindings} → {code : Code} → {contract : Contract} →
    {demand : List Nat} → {requirements : RecursiveRequirements.Requirements demand} →
    {dependencies : Dependencies} → {plan : Plan dependencies} → {rows : Rows (signature plan)} →
    {body : CoreCallableStaticProducer.Annotation entries owners bindings code contract demand requirements plan rows} →
    {storage : CoreCallableReturnStorageProducer.Bindings} → {lexical : LexicalBounds} →
    {records : List CoreCallableReturnStorageProducer.BindingAnnotation} →
    BindPath receiver entries owners root body storage lexical records → List Replacement → Prop where
  | here : InitializerLineage receiver entries owners policy declarations outward world allowed scope @stable root .here []
  | bind
      {initial : CoreCallableStaticProducer.Annotation entries owners bindings (.lambda formal initialBody)
        (.function input output requests latent publicPlan publicRows) [] (.request [] []) .pure Rows.pure}
      {body : CoreCallableStaticProducer.Annotation entries owners ((name,.function input output requests latent publicPlan publicRows)::bindings)
        bodyCode bodyContract bodyDemand bodyReq bodyPlan bodyRows}
      {preceding : BindPath receiver entries owners root (.bind (parameter := name) initial body) storage lexical records}
      (previous : InitializerLineage receiver entries owners policy declarations outward world allowed scope @stable root preceding replacements)
      (actual : CoreCallableStaticProducer.Result entries policy outward owners world allowed scope bindings
        (.lambda formal initialBody) (.function input output requests latent publicPlan publicRows) [] (.request [] []) .pure Rows.pure lexical receiver)
      (accepted : CoreCallableStaticProducer.check initial policy outward world allowed scope lexical receiver = .ok actual)
      (family : Family (CoreCallableStaticProducer.registry entries policy) outward owners world Environment.empty
        formal (closeBody replacements formal initialBody) input output requests latent publicPlan publicRows)
      (chain : ConstructorChain (CoreCallableStaticProducer.registry entries policy) outward owners world allowed scope @stable
        formal input output requests latent publicPlan publicRows replacements bindings initialBody actual.source
        (closeBody replacements formal initialBody) family) :
      InitializerLineage receiver entries owners policy declarations outward world allowed scope @stable root
        (BindPath.bind preceding storageAnnotation storageInput)
        ({name := name,code := closeCode replacements (.lambda formal initialBody),
          frozen := closeTree replacements (.lambda formal initialBody) storageAnnotation} :: replacements)

structure Prefix
    {root : CoreCallableStaticProducer.Annotation entries owners [] rootCode rootContract rootDemand rootReq rootPlan rootRows}
    {body : CoreCallableStaticProducer.Annotation entries owners rich code contract demand requirements plan rows}
    (path : BindPath receiver entries owners root body storage lexical records)
    (graph : CoreSyntax.Graph) (coreOwners : CoreTranslation.OwnerMap) (rootSite site : Nat)
    (base after : CoreMachine.State) (saved : MEnv) (replacements : List Replacement)
    (policy : Syntax.TicketPolicy) (declarations : Instantiation.DeclarationRegistry)
    (outward : List Instance) (world : List Nat) (allowed : List Instance) (scope : Execution.Scope)
    (stable : SubstitutionPolicyStable outward) : Prop where
  rootChecked : ∃ actual, CoreCallableStaticProducer.check root policy outward world allowed scope [] receiver = .ok actual
  graphOrigin : ∃ fuel, GraphPrefix graph coreOwners fuel rootSite receiver entries owners policy declarations outward world allowed scope root path site
  evaluations : Evaluations graph coreOwners replacements {base with control := .evaluate rootSite .empty} after
  origins : Origins (CoreCallableStaticProducer.registry entries policy) declarations outward owners world allowed scope receiver
    rootCode code rich storage lexical records
  produced : ProducedBindings (CoreCallableStaticProducer.registry entries policy) declarations outward owners world allowed scope receiver
    graph coreOwners base.heap replacements rich storage lexical saved
  lineage : InitializerLineage receiver entries owners policy declarations outward world allowed scope @stable root path replacements
  steps : Steps graph (3 * records.length) {base with control := .evaluate rootSite .empty} after
  control : after.control = .evaluate site saved
  heap : after.heap = base.heap
  frames : after.frames = base.frames

/-- Recursively construct the exact original static/runtime prefix from empty.
Executable original checks are input guards; execution and closure are outputs. -/
theorem ordinary_runtime_origins
    {root : CoreCallableStaticProducer.Annotation entries owners [] rootCode rootContract rootDemand rootReq rootPlan rootRows}
    {body : CoreCallableStaticProducer.Annotation entries owners rich code contract demand requirements plan rows}
    {path : BindPath receiver entries owners root body storage lexical records}
    (graphPath : GraphPrefix graph coreOwners fuel rootSite receiver entries owners policy declarations outward world allowed scope root path site)
    (rootAccepted : ∃ actual, CoreCallableStaticProducer.check root policy outward world allowed scope [] receiver = .ok actual)
    (stable : SubstitutionPolicyStable outward) (base : CoreMachine.State) :
    ∃ after saved replacements,
      Prefix path graph coreOwners rootSite site base after saved replacements policy declarations outward world allowed scope @stable := by
  induction graphPath with
  | here translated =>
    exact ⟨{base with control := .evaluate rootSite .empty},.empty,[],
      ⟨rootAccepted,⟨fuel,.here translated⟩,.empty,.initial,.empty,.here,.zero,rfl,rfl,rfl⟩⟩
  | bind previous known kind it bt accepted stored bounded attachment checked ih =>
    rename_i bindings formal initialBody input output requests latent publicDependencies publicPlan publicRows bodyCode bodyContract bodyDemand bodyReq bodyDependencies bodyPlan bodyRows beforeStorage beforeLexical beforeRecords bindSite node binder initializerSite bodySite storageAnnotation storageInput initial bodyAnn preceding
    obtain ⟨previousState,saved,replacements,prior⟩ := ih
    obtain ⟨actual,actualAccepted⟩ := accepted
    obtain ⟨certificate,callableAccepted⟩ := checked
    obtain ⟨family,chain,auth⟩ := prior.produced.close_lambda actual.source actual.authenticated @stable
    have finite := prior.produced.finite stored
    rw [closeCode_lambda] at finite
    have logicalClosed := empty_lambda_closed family.whole auth
      (CoreCallableReturnStorageProducer.check_sound (declarations := declarations) (world := world) (ticket := .none) finite)
    have closing : EnvCloses graph coreOwners previousState.heap saved (.lambda formal initialBody)
        (.lambda formal (closeBody replacements formal initialBody)) := by
      rw [prior.heap]
      simpa only [closeCode_lambda] using prior.produced.closes (.lambda formal initialBody)
    have rawSame := CoreCallableOuterLambdaOrigins.checked_raw_lambda it callableAccepted
    rw [rawSame] at closing
    let entered : CoreMachine.State := {previousState with
      control := .evaluate initializerSite saved,
      frames := .bind binder.id bodySite saved :: previousState.frames,
      observations := previousState.observations ++ [.entered bindSite]}
    let evaluated : CoreMachine.State := {entered with
      control := .returned (.closure certificate.parameter certificate.body saved),
      observations := entered.observations ++ [.entered initializerSite]}
    let completed : CoreMachine.State := {evaluated with
      control := .evaluate bodySite (.binding binder.id (.closure certificate.parameter certificate.body saved) saved),
      frames := previousState.frames}
    have entry : CoreMachine.next graph previousState = .stepped entered := by
      simp only [CoreMachine.next,prior.control,known,kind]
      rfl
    obtain ⟨witness,_⟩ := CoreCallableChecks.checked_lambda_evaluate (base := entered) callableAccepted closing logicalClosed
      (.bind binder.id bodySite saved :: previousState.frames)
    change CoreAdministrativeSteps.ValueWitness graph coreOwners entered evaluated
      (.lambda formal (closeBody replacements formal initialBody)) at witness
    obtain ⟨value,returned,related⟩ := witness.returned
    have valueSame : value = .closure certificate.parameter certificate.body saved := by
      injection returned.symm
    subst value
    have relatedBase : ValueRel graph coreOwners base.heap (.closure certificate.parameter certificate.body saved)
        (.lambda formal (closeBody replacements formal initialBody)) := by
      simpa only [evaluated,entered,prior.heap] using related
    have finish : CoreMachine.next graph evaluated = .stepped completed := by rfl
    have three : Steps graph 3 previousState completed :=
      .step entry (.step witness.core (.step finish .zero))
    have allSteps := prior.steps.append three
    have produced := ProducedBindings.bind (name := binder.id) prior.produced family.whole auth finite bounded relatedBase
    have originalLineage := InitializerLineage.bind (storageAnnotation := storageAnnotation) (storageInput := storageInput)
      prior.lineage actual actualAccepted family chain
    rw [closeCode_lambda] at originalLineage
    refine ⟨completed,.binding binder.id (.closure certificate.parameter certificate.body saved) saved,
      {name := binder.id,code := .lambda formal (closeBody replacements formal initialBody),
        frozen := closeTree replacements (.lambda formal initialBody) storageAnnotation} :: replacements,?_⟩
    refine ⟨rootAccepted,⟨fuel,.bind previous known kind it bt ⟨actual,actualAccepted⟩ stored bounded attachment ⟨certificate,callableAccepted⟩⟩,
      Evaluations.bind prior.evaluations entry witness finish prior.control rfl rfl rfl rfl rfl,
      .bind prior.origins actual.source actual.authenticated
      (CoreCallableReturnStorageProducer.check_sound stored) bounded,produced,originalLineage,?_,rfl,?_,?_⟩
    · simpa only [List.length_cons,Nat.mul_add,Nat.mul_one] using allSteps
    · exact prior.heap
    · exact prior.frames
/-- Consume the produced prefix at the SAME next original literal lambda. -/
theorem Prefix.evaluate_lambda
    {root : CoreCallableStaticProducer.Annotation entries owners [] rootCode rootContract rootDemand rootReq rootPlan rootRows}
    {body : CoreCallableStaticProducer.Annotation entries owners rich (.lambda formal originalBody)
      (.function input output requests latent publicPlan publicRows) [] (.request [] []) .pure Rows.pure}
    {path : BindPath receiver entries owners root body storage lexical records}
    (current : Prefix path graph coreOwners rootSite site base before saved replacements policy declarations outward world allowed scope @stable)
    (actual : CoreCallableStaticProducer.Result entries policy outward owners world allowed scope rich (.lambda formal originalBody)
      (.function input output requests latent publicPlan publicRows) [] (.request [] []) .pure Rows.pure lexical receiver)
    (accepted : CoreCallableStaticProducer.check body policy outward world allowed scope lexical receiver = .ok actual)
    (stored : CoreCallableReturnStorageProducer.check storage (.lambda formal originalBody) annotation = some storageResult)
    (attachment : StorageAttachment storage annotation)
    (translated : CoreTranslation.translateFuel graph fuel coreOwners site = .ok (.lambda formal originalBody))
    (checked : CoreCallableChecks.checkAmbient graph site coreOwners = .ok certificate) :
    ∃ family : Family (CoreCallableStaticProducer.registry entries policy) outward owners world Environment.empty
      formal (closeBody replacements formal originalBody) input output requests latent publicPlan publicRows,
    ∃ after,
      CoreCallableStaticProducer.check body policy outward world allowed scope lexical receiver = .ok actual ∧
      CoreCallableStorageRecipes.specialize storage attachment.originalMap attachment.originalRecipe = some annotation ∧
      ConstructorChain (CoreCallableStaticProducer.registry entries policy) outward owners world allowed scope @stable
        formal input output requests latent publicPlan publicRows replacements rich originalBody actual.source
        (closeBody replacements formal originalBody) family ∧
      Authenticated (CoreCallableStaticProducer.registry entries policy) outward (family.whole (allowed := allowed) (scope := scope)) [] receiver ∧
      CoreCallableReturnStorageProducer.check [] (closeCode replacements (.lambda formal originalBody))
        (closeTree replacements (.lambda formal originalBody) annotation) = some storageResult ∧
      CallableContracts.Derives declarations CallableContracts.Environment.empty world .none
        (closeCode replacements (.lambda formal originalBody)) storageResult ∧
      EnvCloses graph coreOwners before.heap saved (.lambda formal originalBody) (closeCode replacements (.lambda formal originalBody)) ∧
      ClosedValue (closeCode replacements (.lambda formal originalBody)) ∧
      CoreAdministrativeSteps.ValueWitness graph coreOwners before after (closeCode replacements (.lambda formal originalBody)) ∧
      after.control = .returned (.closure certificate.parameter certificate.body saved) := by
  obtain ⟨family,chain,auth⟩ := current.produced.close_lambda actual.source actual.authenticated @stable
  have finite := current.produced.finite stored
  have derived := CoreCallableReturnStorageProducer.check_sound (declarations := declarations) (world := world) (ticket := .none) finite
  have logicalClosed : ClosedValue (closeCode replacements (.lambda formal originalBody)) := by
    rw [closeCode_lambda]
    exact empty_lambda_closed family.whole auth (by simpa only [closeCode_lambda] using derived)
  have closing : EnvCloses graph coreOwners before.heap saved (.lambda formal originalBody) (closeCode replacements (.lambda formal originalBody)) := by
    rw [current.heap]
    exact current.produced.closes _
  have originalClosing := closing
  have rawSame := CoreCallableOuterLambdaOrigins.checked_raw_lambda translated checked
  have checkedClosing : EnvCloses graph coreOwners before.heap saved (.lambda certificate.parameter certificate.rawBody) (closeCode replacements (.lambda formal originalBody)) := by
    rw [← rawSame]
    exact closing
  let after : CoreMachine.State := {before with
    control := .returned (.closure certificate.parameter certificate.body saved),
    observations := before.observations ++ [.entered site]}
  obtain ⟨witness,_⟩ := CoreCallableChecks.checked_lambda_evaluate (base := before) checked checkedClosing logicalClosed before.frames
  have sameStart : {before with control := .evaluate site saved,frames := before.frames} = before := by
    rw [← current.control]
  rw [sameStart] at witness
  change CoreAdministrativeSteps.ValueWitness graph coreOwners before after (closeCode replacements (.lambda formal originalBody)) at witness
  exact ⟨family,after,accepted,attachment.specialized,chain,auth,finite,derived,originalClosing,logicalClosed,witness,rfl⟩

def ordinaryDepth : MEnv → Nat
  | .empty => 0
  | .binding _ _ saved => ordinaryDepth saved + 1
  | .resource _ _ _ | .functionTemplate _ _ _ _ => 0

theorem ProducedBindings.depth
    (produced : ProducedBindings registry declarations outward owners world allowed scope receiver graph coreOwners heap replacements rich storage lexical saved) :
    ordinaryDepth saved = replacements.length := by
  induction produced with
  | empty => rfl
  | bind previous source auth finite bounded related ih => simpa [ordinaryDepth] using ih

theorem InitializerLineage.count
    {root : CoreCallableStaticProducer.Annotation entries owners [] rootCode rootContract rootDemand rootReq rootPlan rootRows}
    {body : CoreCallableStaticProducer.Annotation entries owners rich code contract demand requirements plan rows}
    {path : BindPath receiver entries owners root body storage lexical records}
    (lineage : InitializerLineage receiver entries owners policy declarations outward world allowed scope @stable root path replacements) :
    replacements.length = records.length := by
  induction lineage with
  | here => rfl
  | bind previous actual accepted family chain ih => simpa using ih

theorem Prefix.depth
    (current : Prefix (records := records) path graph coreOwners rootSite site base after saved replacements policy declarations outward world allowed scope @stable) :
    ordinaryDepth saved = records.length := current.produced.depth.trans current.lineage.count

/-- Actual nearest lookup is tied to the produced logical replacement and
saved MEnv, rather than joined to original static records by a name search. -/
theorem ProducedBindings.nearest
    (produced : ProducedBindings registry declarations outward owners world allowed scope receiver graph coreOwners heap
      (replacement :: rest) rich storage lexical saved) :
    ∃ value tail, saved = .binding replacement.name value tail ∧
      saved.lookup replacement.name = some value ∧ ValueRel graph coreOwners heap value replacement.code := by
  cases produced with
  | bind previous source auth finite bounded related =>
    exact ⟨_,_,rfl,by simp [CoreMachine.Environment.lookup],related⟩

theorem Prefix.nearest
    (current : Prefix path graph coreOwners rootSite site base after saved (replacement :: rest) policy declarations outward world allowed scope @stable) :
    ∃ value tail, saved = .binding replacement.name value tail ∧
      saved.lookup replacement.name = some value ∧ ValueRel graph coreOwners after.heap value replacement.code := by
  rw [current.heap]
  exact current.produced.nearest

/-- Generic counterevidence against reusing original-ClosedValue producers. -/
theorem original_open (different : captured ≠ formal) :
    ¬ ClosedValue (.lambda formal (.variable captured)) := by
  intro closed
  have member : Syntax.Dependency.variable captured ∈ (Code.lambda formal (.variable captured)).dependencies := by
    simp [Code.dependencies,Syntax.without,different]
  exact closed.2.2 _ member

/-- The producer handles an original open initializer after two installations,
with actual six-step execution and two saved ordinary values. No input runtime
relation or original closedness is supplied. -/
theorem two_open_prefix
    {record : CoreCallableReturnStorageProducer.BindingAnnotation}
    {root : CoreCallableStaticProducer.Annotation entries owners [] rootCode rootContract rootDemand rootReq rootPlan rootRows}
    {body : CoreCallableStaticProducer.Annotation entries owners rich code contract demand requirements plan rows}
    {path : BindPath receiver entries owners root body storage lexical (record :: records)}
    (graphPath : GraphPrefix graph coreOwners fuel rootSite receiver entries owners policy declarations outward world allowed scope root path site)
    (rootAccepted : ∃ actual, CoreCallableStaticProducer.check root policy outward world allowed scope [] receiver = .ok actual)
    (stable : SubstitutionPolicyStable outward) (base : CoreMachine.State)
    (count : records.length = 1) (same : record.initializer = .lambda formal (.variable captured))
    (different : captured ≠ formal) :
    ¬ ClosedValue record.initializer ∧ ∃ after saved replacements,
      Prefix path graph coreOwners rootSite site base after saved replacements policy declarations outward world allowed scope @stable ∧
      Steps graph 6 {base with control := .evaluate rootSite .empty} after ∧ ordinaryDepth saved = 2 := by
  refine ⟨same ▸ original_open different,?_⟩
  obtain ⟨after,saved,replacements,current⟩ := ordinary_runtime_origins graphPath rootAccepted @stable base
  exact ⟨after,saved,replacements,current,by simpa [count] using current.steps,by simpa [count] using current.depth⟩

/-- Closed replacements survive all older substitutions, including duplicate
binder names. The nearest generated binding is selected before its tail. -/
theorem closeCode_closed (closed : ClosedValue code) (replacements : List Replacement) :
    closeCode replacements code = code := by
  induction replacements with
  | nil => rfl
  | cons replacement rest ih =>
    simp only [closeCode,ScopedTyping.subst_absent code replacement.name replacement.code (ScopedTyping.closedValue_no_variable closed),ih]

theorem nearest_shadow (closed : ClosedValue newest.code) (older : List Replacement) :
    closeCode (newest :: older) (.variable newest.name) = newest.code := by
  simp only [closeCode,Code.subst]
  exact closeCode_closed closed older

theorem formal_shadow (frozen : CoreCallableReturnStorageProducer.Annotation) :
    closeCode [{name := formal,code := value,frozen := frozen}] (.lambda formal body) = .lambda formal body := by
  simp [closeCode,Code.subst]

/-- The body of an outer ordinary bind may itself be a bind, which cannot be
fed to the earlier immediate-outer-lambda checker. -/
theorem nested_bind_not_callable (known : graph.node site = some node)
    (kind : node.kind = .bind binder initializer body) :
    CoreCallableChecks.checkAmbient graph site coreOwners ≠ .ok certificate := by
  intro checked
  obtain ⟨actualBinder,actualNode,present,function,parameter⟩ :=
    (CoreCallableChecks.checkFunction_sound (CoreCallableChecks.checkAmbient_sound checked).1).2.1
  have same := Option.some.inj (known.symm.trans present)
  subst actualNode
  rw [kind] at function
  contradiction

end Ash.OneShot.CoreCallableOrdinaryRuntimeOrigins

#print axioms Ash.OneShot.CoreCallableOrdinaryRuntimeOrigins.closeCode_lambda
#print axioms Ash.OneShot.CoreCallableOrdinaryRuntimeOrigins.ProducedBindings.closes
#print axioms Ash.OneShot.CoreCallableOrdinaryRuntimeOrigins.ProducedBindings.finite
#print axioms Ash.OneShot.CoreCallableOrdinaryRuntimeOrigins.ProducedBindings.close_lambda
#print axioms Ash.OneShot.CoreCallableOrdinaryRuntimeOrigins.empty_lambda_closed
#print axioms Ash.OneShot.CoreCallableOrdinaryRuntimeOrigins.Steps.append
#print axioms Ash.OneShot.CoreCallableOrdinaryRuntimeOrigins.ordinary_runtime_origins
#print axioms Ash.OneShot.CoreCallableOrdinaryRuntimeOrigins.Prefix.evaluate_lambda
#print axioms Ash.OneShot.CoreCallableOrdinaryRuntimeOrigins.ProducedBindings.depth
#print axioms Ash.OneShot.CoreCallableOrdinaryRuntimeOrigins.InitializerLineage.count
#print axioms Ash.OneShot.CoreCallableOrdinaryRuntimeOrigins.Prefix.depth
#print axioms Ash.OneShot.CoreCallableOrdinaryRuntimeOrigins.original_open
#print axioms Ash.OneShot.CoreCallableOrdinaryRuntimeOrigins.two_open_prefix
#print axioms Ash.OneShot.CoreCallableOrdinaryRuntimeOrigins.closeCode_closed
#print axioms Ash.OneShot.CoreCallableOrdinaryRuntimeOrigins.nearest_shadow
#print axioms Ash.OneShot.CoreCallableOrdinaryRuntimeOrigins.formal_shadow
#print axioms Ash.OneShot.CoreCallableOrdinaryRuntimeOrigins.nested_bind_not_callable
#print axioms Ash.OneShot.CoreCallableOrdinaryRuntimeOrigins.ProducedBindings.nearest
#print axioms Ash.OneShot.CoreCallableOrdinaryRuntimeOrigins.Prefix.nearest
