import CoreCallableFiniteResourceTemplate
import CoreCallableFiniteRegistryBridge
namespace Ash.OneShot.CoreCallableCompositionalResourceBody
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract sequenceRows)
open CoreCallableContractAdmission CoreCallableReceiverRefinement
open CoreCallableStaticProducer (Bindings StaticTree RecipeTag)
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceDependencyAnnotations (Dependencies)
open RecursiveRequirements (Requirements)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
local instance : SourcePlannedChecks.DeclarationPolicy :=
  SourceScheduledCleanupInterfaces.Lexical.Recursive.declarationPolicy

/-- Finite symbolic cell effects and unchanged original user effects. -/
inductive EffectName where
  | cell : Instantiation.ResourceName → EffectName
  | closed : Instance → EffectName
  deriving DecidableEq

def EffectName.value (identity : Nat) : EffectName → Instance
  | .cell name => .cell (CoreCallableFiniteResourceTemplate.nameValue identity name)
  | .closed effect => effect

def EffectName.check (binder : Nat) (world : List Nat) : EffectName → Bool
  | .cell name => CoreCallableFiniteResourceTemplate.nameCheck binder world name
  | .closed effect => CoreCallableGraphAnnotationChecks.subsetB effect.resources world

def EffectName.outside : EffectName → Bool
  | .cell (.bound _) => false
  | _ => true

structure RequestName where
  effect : EffectName
  operation : Nat
  held : Bool := false
  deriving DecidableEq

def RequestName.value (identity : Nat) (request : RequestName) : ProtectionContracts.Demand :=
  ⟨request.effect.value identity,request.operation,request.held⟩

/-- Full checking data is retained. Closed recipe tags are finite data, never
Certified or Source/Auth premises. New identity families are structural. -/
inductive Checking where
  | pure
  | embedded (body : CoreCallableFiniteResourceTemplate.Body context code pattern)
  | request (effect : EffectName) (operation : Nat)
  | sequence : Checking → Checking → Checking
  | choice : Checking → Checking → Checking
  | closed {dependencies : Dependencies} (plan : Plan dependencies)
      (rows : Rows (signature plan)) (recipe : RecipeTag plan)

def Checking.dependencies (identity : Nat) : Checking → Dependencies
  | .pure => .pure
  | .embedded body => body.dependencies identity
  | .request effect operation => .request (effect.value identity) operation
  | .sequence first second => .sequence (first.dependencies identity) (second.dependencies identity)
  | .choice first second => .choice (first.dependencies identity) (second.dependencies identity)
  | @Checking.closed dependencies _ _ _ => dependencies

def Checking.plan (identity : Nat) : (checking : Checking) → Plan (checking.dependencies identity)
  | .pure => .pure
  | .embedded body => body.plan identity
  | .request _ _ => .request
  | .sequence first second => .sequence (first.plan identity) (second.plan identity)
  | .choice first second => .choice (first.plan identity) (second.plan identity)
  | .closed plan _ _ => plan

def Checking.rows (identity : Nat) : (checking : Checking) → Rows (signature (checking.plan identity))
  | .pure => Rows.pure
  | .embedded body => body.rows identity
  | .request _ _ => Rows.request
  | .sequence first second => sequenceRows (first.rows identity) (second.rows identity)
  | .choice first second => CoreCallableContractSource.choiceRows (first.rows identity) (second.rows identity)
  | .closed _ rows _ => rows

def oldRecipe (identity : Nat) : (body : CoreCallableFiniteResourceTemplate.Body context code pattern) →
    RecipeTag (body.plan identity)
  | .unit | .boolean _ | .integer _ | .reference _ | .variable _ => .pure
  | .pair first second | .bind first second => .sequence (oldRecipe identity first) (oldRecipe identity second)
  | .read operand | .write operand => .sequence (oldRecipe identity operand) .request

 theorem oldRecipe_check (body : CoreCallableFiniteResourceTemplate.Body context code pattern) (identity : Nat) :
    (oldRecipe identity body).check = true := by
  induction body with
  | unit | boolean | integer | reference | «variable» => rfl
  | pair first second ihF ihS | bind first second ihF ihS =>
      simp [oldRecipe,RecipeTag.check,ihF,ihS]
  | read operand ih | write operand ih => simp [oldRecipe,RecipeTag.check,ih]

def Checking.recipe (identity : Nat) : (checking : Checking) → RecipeTag (checking.plan identity)
  | .pure => .pure
  | .embedded body => oldRecipe identity body
  | .request _ _ => .request
  | .sequence first second => .sequence (first.recipe identity) (second.recipe identity)
  | .choice first second => .choice (first.recipe identity) (second.recipe identity)
  | .closed _ _ recipe => recipe

def Checking.check : Checking → Bool
  | .pure | .embedded _ | .request _ _ => true
  | .sequence first second | .choice first second => first.check && second.check
  | .closed _ _ recipe => recipe.check

 theorem Checking.recipe_check (checking : Checking) (identity : Nat) :
    (checking.recipe identity).check = checking.check := by
  induction checking with
  | pure | request | closed => rfl
  | embedded body => exact oldRecipe_check body identity
  | sequence first second ihF ihS | choice first second ihF ihS =>
      simp only [Checking.recipe,RecipeTag.check,Checking.check,ihF,ihS]

/-- Requirements and their exact empty-owner isolated summaries are generated
from the same finite tree, including branch choices and call latent rows. -/
inductive Need where
  | empty
  | embedded (body : CoreCallableFiniteResourceTemplate.Body context code pattern)
  | emit : Need → List RequestName → Need
  | sequence : Need → Need → Need
  | choice : Need → Need → Need

def Need.requirements (identity : Nat) : Need → Requirements []
  | .empty => .request [] []
  | .embedded body => body.requirements identity
  | .emit body requests => .emitAfter (body.requirements identity) [] (requests.map (RequestName.value identity))
  | .sequence first second => .sequence (first.requirements identity) (second.requirements identity)
  | .choice first second => .choice (first.requirements identity) (second.requirements identity) (List.Perm.refl [])

def oldSummary : CoreCallableFiniteResourceTemplate.Body context code pattern → List RequestName
  | .unit | .boolean _ | .integer _ | .reference _ | .variable _ => []
  | .pair first second | .bind first second => oldSummary first ++ oldSummary second
  | .read (name := name) operand => oldSummary operand ++ [⟨.cell name,0,false⟩]
  | .write (name := name) operand => oldSummary operand ++ [⟨.cell name,1,false⟩]

def Need.summary : Need → List RequestName
  | .empty => []
  | .embedded body => oldSummary body
  | .emit body requests => body.summary ++ requests
  | .sequence first second | .choice first second => first.summary ++ second.summary

/-- New functions retain full computed checking data. Original contracts remain
opaque exact data, including higher-order private checking rows. -/
inductive Pattern where
  | old : CoreCallableFiniteResourceTemplate.ContractPattern → Pattern
  | closed : Contract → Pattern
  | pair : Pattern → Pattern → Pattern
  | function (input output : Pattern) (requests : List EffectName)
      (latent : List RequestName) (checking : Checking)

def Pattern.value (original : Bindings) (identity : Nat) : Pattern → Contract
  | .old pattern => pattern.value original identity
  | .closed contract => contract
  | .pair first second => .pair (first.value original identity) (second.value original identity)
  | .function input output requests latent checking =>
      .function (input.value original identity) (output.value original identity)
        (requests.map (EffectName.value identity)) (latent.map (RequestName.value identity))
        (checking.plan identity) (checking.rows identity)

abbrev Context := List (Nat × Pattern)
def bindings (original : Bindings) (identity : Nat) : Context → Bindings
  | [] => []
  | (name,pattern)::rest => (name,pattern.value original identity)::bindings original identity rest

inductive Ref : Context → Nat → Pattern → Type where
  | head : Ref ((name,pattern)::rest) name pattern
  | tail : Ref rest name pattern → Ref ((bound,value)::rest) name pattern

def Ref.check : Ref context name pattern → Bool
  | .head => true
  | .tail (bound := bound) next => decide (name ≠ bound) && next.check

def Ref.realize (original : Bindings) (identity : Nat) : Ref context name pattern →
    CoreCallableStaticProducer.BindingRef (bindings original identity context) name (pattern.value original identity)
  | .head => .head
  | .tail next => .tail (next.realize original identity)

 theorem Ref.realize_check (ref : Ref context name pattern) (original : Bindings) (identity : Nat) :
    (ref.realize original identity).check = ref.check := by
  induction ref with
  | head => rfl
  | tail next ih => simp [Ref.realize,CoreCallableStaticProducer.BindingRef.check,Ref.check,ih]

/-- The existing embedded factory has only these strict ordinary cases. -/
inductive Basic : Code → Prop where
  | unit : Basic .unit
  | boolean : Basic (.boolean value)
  | integer : Basic (.integer value)
  | reference : Basic (.resourceRef name)
  | variable : Basic (.variable name)
  | pair : Basic first → Basic second → Basic (.pair first second)
  | bind : Basic first → Basic second → Basic (.bind name first second)
  | perform : Basic operand → Basic (.perform (.cell (.activation identity)) operation operand)

def performed : Code → List Instance
  | .pair first second | .bind _ first second => performed first ++ performed second
  | .perform (.cell (.activation identity)) _ operand => .cell identity :: performed operand
  | _ => []

/-- Only current syntactic requests and exact dependency lookup agreement are
used to transport an already produced embedded tree. No desired next state. -/
theorem StaticTree.rebase_basic
    {source : IndexedSource registry outward owners world allowed scope environment code contract demand requirements plan rows}
    (tree : StaticTree registry outward source) (plain : Basic code)
    (agree : ∀ name, Syntax.Dependency.variable name ∈ code.dependencies → environment name = destination name)
    (admitted : performed code ⊆ nextAllowed) :
    ∃ next : IndexedSource registry outward owners world nextAllowed scope destination code contract demand requirements plan rows,
      StaticTree registry outward next := by
  induction tree generalizing destination nextAllowed with
  | unit => exact ⟨.unit,.unit⟩
  | boolean => exact ⟨.boolean,.boolean⟩
  | integer => exact ⟨.integer,.integer⟩
  | reference => exact ⟨.reference (by assumption),.reference (issued := by assumption)⟩
  | @«variable» owner allowed0 scope0 env name value known world0 formed =>
      have same := agree name (by simp [Code.dependencies])
      exact ⟨.variable (same.symm.trans (by assumption)) (by assumption),
        .variable (known := same.symm.trans (by assumption)) (formed := by assumption)⟩
  | pair left right ihL ihR =>
      cases plain with
      | pair pL pR =>
          obtain ⟨l,lt⟩ := ihL pL (fun n m => agree n (List.mem_append_left _ m))
            (fun _ m => admitted (List.mem_append_left _ m))
          obtain ⟨r,rt⟩ := ihR pR (fun n m => agree n (List.mem_append_right _ m))
            (fun _ m => admitted (List.mem_append_right _ m))
          exact ⟨.pair l r,.pair lt rt⟩
  | @bind owner world0 allowed0 scope0 env first input dI qI depsI planI rowsI sourceI parameter second output dB qB depsB planB rowsB sourceB initial body ihI ihB =>
      cases plain with
      | bind pI pB =>
          obtain ⟨i,it⟩ := ihI pI (fun n m => agree n (List.mem_append_left _ m))
            (fun _ m => admitted (List.mem_append_left _ m))
          obtain ⟨b,bt⟩ := ihB pB (destination := destination.extend parameter input) (by
            intro n m
            by_cases same : n = parameter
            · simp [CoreCallableContractSource.Environment.extend,same]
            · simp only [CoreCallableContractSource.Environment.extend,if_neg same]
              exact agree n (List.mem_append_right _ (Syntax.mem_without.mpr ⟨m,by simpa using same⟩)))
            (fun _ m => admitted (List.mem_append_right _ m))
          exact ⟨.bind i b,.bind it bt⟩
  | @perform owner world0 allowed0 scope0 env code0 input d q deps actualPlan actualRows source0 effect operation output known oldAdmitted formed operand ih =>
      cases effect with
      | user family arguments => cases plain
      | cell identity =>
          cases plain with
          | perform p =>
              obtain ⟨o,ot⟩ := ih p (fun n m => agree n (by simpa [Code.dependencies] using m))
                (fun _ m => admitted (List.mem_cons_of_mem _ m))
              have current : Instance.cell identity ∈ nextAllowed := admitted List.mem_cons_self
              exact ⟨.perform known current o formed,.perform (known := known) (admitted := current) (formed := formed) ot⟩
  | app | cleanup | branch | lambda | receiverLambda | resume | discard | resource => cases plain

/-- Full closed function slots are selected by literal original list position. -/
inductive FunctionSlot : Bindings → Nat → Contract → Contract → List Instance → Footprint →
    {dependencies : Dependencies} → (plan : Plan dependencies) → Rows (signature plan) → Type where
  | head : FunctionSlot ((name,.function input output requests latent plan rows)::rest) 0 input output requests latent plan rows
  | tail : FunctionSlot rest index input output requests latent plan rows →
      FunctionSlot ((name,value)::rest) (index+1) input output requests latent plan rows

 theorem FunctionSlot.exact (slot : FunctionSlot original index input output requests latent plan rows) :
    CoreCallableFiniteResourceTemplate.slotContract original index = .function input output requests latent plan rows := by
  induction slot with
  | head => rfl
  | tail next ih => simpa [CoreCallableFiniteResourceTemplate.slotContract] using ih

def closedRequests (requests : Footprint) : List RequestName :=
  requests.map fun request => ⟨.closed request.effect,request.operation,request.held⟩

/-- Each constructor computes its entire family indices from finite children. -/
inductive Body (original : Bindings) : Context → Code → Pattern → Checking → Need → Type where
  | embedded (old : CoreCallableFiniteResourceTemplate.Body oldContext code pattern) :
      Body original context code (.old pattern) (.embedded old) (.embedded old)
  | variable (ref : Ref context name pattern) : Body original context (.variable name) pattern .pure .empty
  | slotCallable (ref : Ref context name (.old (.slot index)))
      (slot : FunctionSlot original index input output requests latent plan rows) (recipe : RecipeTag plan) :
      Body original context (.variable name)
        (.function (.closed input) (.closed output) (requests.map EffectName.closed) (closedRequests latent) (.closed plan rows recipe)) .pure .empty
  | pair (first : Body original context a input checkingA needsA) (second : Body original context b output checkingB needsB) :
      Body original context (.pair a b) (.pair input output) (.sequence checkingA checkingB) (.sequence needsA needsB)
  | bind (first : Body original context a input checkingA needsA)
      (second : Body original ((parameter,input)::context) b output checkingB needsB) :
      Body original context (.bind parameter a b) output (.sequence checkingA checkingB) (.sequence needsA needsB)
  | lambda (input : Pattern) (requests : List EffectName)
      (body : Body original ((parameter,input)::context) code output checking needs) :
      Body original context (.lambda parameter code) (.function input output requests needs.summary checking) .pure .empty
  | app (function : Body original context f (.function input output requests latent exposed) checkingF needsF)
      (argument : Body original context a input checkingA needsA) :
      Body original context (.app f a) output (.sequence checkingF (.sequence checkingA exposed))
        (.emit (.sequence needsF needsA) latent)
  | branch (condition : Body original context test (.old .boolean) checkingC needsC)
      (yes : Body original context a output checkingA needsA) (no : Body original context b output checkingB needsB) :
      Body original context (.branch test a b) output (.sequence checkingC (.choice checkingA checkingB))
        (.sequence needsC (.choice needsA needsB))

def lookup : Context → Nat → Option Pattern
  | [],_ => none
  | (name,pattern)::rest,wanted => if wanted = name then some pattern else lookup rest wanted

def oldLookup : CoreCallableFiniteResourceTemplate.Context → Nat → Option CoreCallableFiniteResourceTemplate.ContractPattern
  | [],_ => none
  | (name,pattern)::rest,wanted => if wanted = name then some pattern else oldLookup rest wanted

def sameOld (old : CoreCallableFiniteResourceTemplate.Context) (current : Context) (name : Nat) : Bool :=
  match oldLookup old name,lookup current name with
  | none,none => true
  | some first,some (.old second) => decide (first = second)
  | _,_ => false

def embeddingCheck (old : CoreCallableFiniteResourceTemplate.Context) (current : Context) (code : Code) : Bool :=
  code.dependencies.all fun dependency => match dependency with
    | .variable name => sameOld old current name
    | _ => true

def Pattern.check (original : Bindings) (binder : Nat) (world : List Nat) : Pattern → Bool
  | .old pattern => pattern.check original binder world
  | .closed value => CoreCallableGraphAnnotationChecks.subsetB value.port.resources world
  | .pair first second => first.check original binder world && second.check original binder world
  | .function input output requests latent _ =>
      input.check original binder world && output.check original binder world &&
      requests.all (EffectName.check binder world) && latent.all (fun request => request.effect.check binder world)

def Checking.isClosed : Checking → Bool
  | .pure | .closed _ _ _ => true
  | .request effect _ => effect.outside
  | .sequence first second | .choice first second => first.isClosed && second.isClosed
  | .embedded body => (oldSummary body).all (fun request => request.effect.outside)

def Pattern.isClosed : Pattern → Bool
  | .old pattern => pattern.closed
  | .closed _ => true
  | .pair first second => first.isClosed && second.isClosed
  | .function input output requests latent checking =>
      input.isClosed && output.isClosed && requests.all EffectName.outside &&
      latent.all (fun request => request.effect.outside) && checking.isClosed

def EffectName.canonical : EffectName → EffectName
  | .closed (.cell identity) => .cell (.activation identity)
  | other => other

def effectsSubset (first second : List EffectName) : Bool :=
  first.all fun effect => decide (effect.canonical ∈ second.map EffectName.canonical)

def Body.check (original : Bindings) (binder : Nat) (world : List Nat) (residual : List Instance)
    (allowed : List EffectName) : Body original context code pattern checking needs → Bool
  | .embedded (oldContext := oldContext) old =>
      old.check original binder world residual && embeddingCheck oldContext context code &&
      effectsSubset ((oldSummary old).map RequestName.effect) allowed
  | .variable ref => ref.check && pattern.check original binder world
  | .slotCallable ref _ recipe => ref.check && pattern.check original binder world && recipe.check
  | .pair first second | .bind first second =>
      first.check original binder world residual allowed && second.check original binder world residual allowed
  | .lambda (output := output) (checking := privateChecking) (needs := privateNeeds) input requests body =>
      body.check original binder world residual requests &&
      (Pattern.function input output requests privateNeeds.summary privateChecking).check original binder world && privateChecking.check &&
      effectsSubset (privateNeeds.summary.map RequestName.effect) requests
  | .app (requests := requests) (exposed := exposed) function argument =>
      function.check original binder world residual allowed && argument.check original binder world residual allowed &&
      effectsSubset requests allowed && exposed.check
  | .branch condition yes no =>
      condition.check original binder world residual allowed && yes.check original binder world residual allowed &&
      no.check original binder world residual allowed

 theorem EffectName.canonical_value (effect : EffectName) (identity : Nat) :
    effect.canonical.value identity = effect.value identity := by
  cases effect with
  | cell name => rfl
  | closed effect => cases effect <;> rfl

 theorem effectsSubset_sound (first second : List EffectName) (accepted : effectsSubset first second = true) :
    first.map (EffectName.value identity) ⊆ second.map (EffectName.value identity) := by
  intro effect member
  obtain ⟨name,locatedName,rfl⟩ := List.mem_map.mp member
  have selected : name.canonical ∈ second.map EffectName.canonical :=
    of_decide_eq_true ((List.all_eq_true.mp accepted) name locatedName)
  obtain ⟨other,located,same⟩ := List.mem_map.mp selected
  apply List.mem_map.mpr
  refine ⟨other,located,?_⟩
  simpa only [EffectName.canonical_value] using congrArg (EffectName.value identity) same

 theorem EffectName.issued (effect : EffectName) (accepted : effect.check binder world = true) :
    (effect.value identity).resources ⊆ world ++ [identity] := by
  cases effect with
  | cell name =>
      have member := CoreCallableFiniteResourceTemplate.name_issued (identity := identity) accepted
      intro resource retained
      have same : resource = CoreCallableFiniteResourceTemplate.nameValue identity name := by
        simpa [EffectName.value,Instance.resources] using retained
      subst resource
      exact member
  | closed effect =>
      exact (CoreCallableGraphAnnotationChecks.subsetB_sound accepted).trans (List.subset_append_left _ _)

 theorem Pattern.formed (pattern : Pattern) (accepted : pattern.check original binder world = true) :
    ScopedPorts.InWorld (world ++ [identity]) (pattern.value original identity).port := by
  induction pattern with
  | old pattern => exact CoreCallableFiniteResourceTemplate.ContractPattern.formed accepted
  | closed value =>
      exact (CoreCallableGraphAnnotationChecks.subsetB_sound accepted).trans (List.subset_append_left _ _)
  | pair first second ihF ihS =>
      obtain ⟨a,b⟩ : first.check original binder world = true ∧ second.check original binder world = true :=
        by simpa [Pattern.check] using accepted
      simpa [Pattern.value,ScopedPorts.InWorld,Contract.port,Contract.value,
        SourcePlannedTyping.Value.erase,SourceDependencyAnnotations.Value.erase,CoherentSourceTypes.Value.port,
        ScopedPorts.Port.resources] using List.append_subset.mpr ⟨ihF a,ihS b⟩
  | function input output requests latent checking ihI ihO =>
      obtain ⟨⟨⟨a,b⟩,c⟩,_⟩ : ((input.check original binder world = true ∧ output.check original binder world = true) ∧
          requests.all (EffectName.check binder world) = true) ∧ _ := by simpa [Pattern.check,Bool.and_eq_true] using accepted
      have formedRequests : (requests.map (EffectName.value identity)).flatMap Instance.resources ⊆ world ++ [identity] := by
        intro resource member
        obtain ⟨effect,located,retained⟩ := List.mem_flatMap.mp member
        obtain ⟨name,selected,rfl⟩ := List.mem_map.mp located
        exact name.issued ((List.all_eq_true.mp c) name selected) retained
      simpa [Pattern.value,ScopedPorts.InWorld,Contract.port,Contract.value,
        SourcePlannedTyping.Value.erase,SourceDependencyAnnotations.Value.erase,CoherentSourceTypes.Value.port,
        ScopedPorts.Port.resources] using List.append_subset.mpr ⟨List.append_subset.mpr ⟨ihI a,ihO b⟩,formedRequests⟩

 theorem Need.outward (needs : Need) (identity : Nat) :
    RecursiveOutward.Outward (needs.requirements identity) (some (needs.summary.map (RequestName.value identity))) := by
  induction needs with
  | empty => exact .request (layers := [])
  | embedded body =>
      induction body with
      | unit | boolean | integer | reference | «variable» => exact .request (layers := [])
      | pair first second ihF ihS | bind first second ihF ihS =>
          simpa [Need.requirements,Need.summary,oldSummary,CoreCallableFiniteResourceTemplate.Body.requirements,
            List.map_append,ProtectionResiduals.merge] using RecursiveOutward.Outward.sequence ihF ihS
      | read operand ih | write operand ih =>
          simpa [Need.requirements,Need.summary,oldSummary,CoreCallableFiniteResourceTemplate.Body.requirements,
            List.map_append,RequestName.value,EffectName.value,ProtectionResiduals.merge,ProtectionResiduals.residualize]
            using RecursiveOutward.Outward.emitAfter (layers := []) ih
  | sequence first second ihF ihS =>
      simpa [Need.requirements,Need.summary,List.map_append,ProtectionResiduals.merge] using RecursiveOutward.Outward.sequence ihF ihS
  | choice first second ihF ihS =>
      simpa [Need.requirements,Need.summary,List.map_append,ProtectionResiduals.merge] using
        RecursiveOutward.Outward.choice (same := List.Perm.refl []) ihF ihS
  | emit body requests ih =>
      simpa [Need.requirements,Need.summary,List.map_append,ProtectionResiduals.merge,ProtectionResiduals.residualize] using
        RecursiveOutward.Outward.emitAfter (layers := []) (raw := requests.map (RequestName.value identity)) ih

 theorem lookup_value (context : Context) (name identity : Nat) (original : Bindings) :
    CoreCallableStaticProducer.environment (bindings original identity context) name =
      (lookup context name).map (Pattern.value original identity) := by
  induction context with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨bound,pattern⟩
      simp only [bindings,CoreCallableStaticProducer.environment,CoreCallableContractSource.Environment.extend,lookup]
      split <;> simp_all

 theorem oldLookup_value (context : CoreCallableFiniteResourceTemplate.Context) (name identity : Nat) (original : Bindings) :
    CoreCallableStaticProducer.environment (CoreCallableFiniteResourceTemplate.bindings original identity context) name =
      (oldLookup context name).map (CoreCallableFiniteResourceTemplate.ContractPattern.value original identity) := by
  induction context with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨bound,pattern⟩
      simp only [CoreCallableFiniteResourceTemplate.bindings,CoreCallableStaticProducer.environment,
        CoreCallableContractSource.Environment.extend,oldLookup]
      split <;> simp_all

 theorem sameOld_sound (accepted : sameOld old current name = true) :
    CoreCallableStaticProducer.environment (CoreCallableFiniteResourceTemplate.bindings original identity old) name =
      CoreCallableStaticProducer.environment (bindings original identity current) name := by
  rw [oldLookup_value,lookup_value]
  cases a : oldLookup old name with
  | none =>
      cases b : lookup current name with
      | none => rfl
      | some pattern => simp [sameOld,a,b] at accepted
  | some oldPattern =>
      cases b : lookup current name with
      | none => simp [sameOld,a,b] at accepted
      | some pattern =>
          cases pattern with
          | old selected =>
              have same : oldPattern = selected := of_decide_eq_true (by simpa [sameOld,a,b] using accepted)
              subst selected
              rfl
          | closed | pair | function => simp [sameOld,a,b] at accepted

 theorem embeddingCheck_sound (accepted : embeddingCheck old current code = true)
    (member : Syntax.Dependency.variable name ∈
      (code.instantiate (Instantiation.Environment.empty.bind binder identity)).dependencies) :
    CoreCallableStaticProducer.environment (CoreCallableFiniteResourceTemplate.bindings original identity old) name =
      CoreCallableStaticProducer.environment (bindings original identity current) name := by
  have included := acquisition_dependency_bound binder identity code member
  rcases List.mem_append.mp included with original | extra
  · exact sameOld_sound ((List.all_eq_true.mp accepted) _ original)
  · simp at extra

 theorem oldBasic (body : CoreCallableFiniteResourceTemplate.Body context code pattern)
    (accepted : body.check original binder world residual = true) :
    Basic (code.instantiate (Instantiation.Environment.empty.bind binder identity)) := by
  induction body with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference => exact .reference
  | «variable» => exact .variable
  | pair first second ihF ihS | bind first second ihF ihS =>
      obtain ⟨a,b⟩ : first.check original binder world residual = true ∧ second.check original binder world residual = true :=
        by simpa [CoreCallableFiniteResourceTemplate.Body.check] using accepted
      first | exact .pair (ihF a) (ihS b) | exact .bind (ihF a) (ihS b)
  | read operand ih | write operand ih =>
      obtain ⟨⟨a,n⟩,_⟩ : (operand.check original binder world residual = true ∧
          CoreCallableFiniteResourceTemplate.nameCheck binder world _ = true) ∧ _ :=
        by simpa [CoreCallableFiniteResourceTemplate.Body.check,Bool.and_eq_true] using accepted
      have realized := CoreCallableFiniteResourceTemplate.name_instantiates (identity := identity) n
      simpa [Code.instantiate,Instantiation.Effect.instantiate,Instantiation.freezeEffect,realized]
        using Basic.perform (operation := _) (ih a)

 theorem oldPerformed (body : CoreCallableFiniteResourceTemplate.Body context code pattern)
    (accepted : body.check original binder world residual = true) :
    performed (code.instantiate (Instantiation.Environment.empty.bind binder identity)) ⊆
      ((oldSummary body).map RequestName.effect).map (EffectName.value identity) := by
  induction body with
  | unit | boolean | integer | reference | «variable» => exact List.nil_subset _
  | pair first second ihF ihS | bind first second ihF ihS =>
      obtain ⟨a,b⟩ : first.check original binder world residual = true ∧ second.check original binder world residual = true :=
        by simpa [CoreCallableFiniteResourceTemplate.Body.check] using accepted
      simpa [performed,Code.instantiate,oldSummary,List.map_append] using List.append_subset.mpr
        ⟨(ihF a).trans (List.subset_append_left _ _),(ihS b).trans (List.subset_append_right _ _)⟩
  | read operand ih | write operand ih =>
      obtain ⟨⟨a,n⟩,_⟩ : (operand.check original binder world residual = true ∧
          CoreCallableFiniteResourceTemplate.nameCheck binder world _ = true) ∧ _ :=
        by simpa [CoreCallableFiniteResourceTemplate.Body.check,Bool.and_eq_true] using accepted
      have realized := CoreCallableFiniteResourceTemplate.name_instantiates (identity := identity) n
      simp only [Code.instantiate,Instantiation.Effect.instantiate,realized,performed,
        oldSummary,List.map_append,List.map_cons,List.map_nil,EffectName.value]
      intro effect member
      rcases List.mem_cons.mp member with same | previous
      · subst effect
        exact List.mem_append_right _ (List.mem_cons_self)
      · exact List.mem_append_left _ (ih a previous)

 theorem closedRequests_value (requests : Footprint) (identity : Nat) :
    (closedRequests requests).map (RequestName.value identity) = requests := by
  rw [closedRequests,List.map_map]
  have same : (RequestName.value identity ∘ fun request : Demand =>
      ⟨.closed request.effect,request.operation,request.held⟩) = id := by
    funext request
    cases request
    rfl
  rw [same,List.map_id]


structure Derived (api : CoreCallableFiniteCellRegistry.CellApi) (entries : CoreCallableStaticProducer.OperationEntries)
    (policy : Syntax.TicketPolicy) (outward : List Instance) (owners : CoreCallableContractRegistries.Owners)
    (world : List Nat) (scope : Execution.Scope) (original : Bindings) (binder identity : Nat)
    (allowed : List EffectName) (body : Body original context code pattern checking needs) where
  source : IndexedSource (CoreCallableFiniteCellRegistry.registry (some api) entries policy) outward owners
    (world ++ [identity]) (allowed.map (EffectName.value identity)) scope
    (CoreCallableStaticProducer.environment (bindings original identity context))
    (code.instantiate (Instantiation.Environment.empty.bind binder identity))
    (pattern.value original identity) [] (needs.requirements identity) (checking.plan identity) (checking.rows identity)
  tree : StaticTree _ outward source

 theorem Body.derive (body : Body original context code pattern checking needs)
    (apiValid : api.check = true) (accepted : body.check original binder world residual allowed = true) :
    Derived api entries policy outward owners world scope original binder identity allowed body := by
  induction body generalizing scope allowed with
  | embedded old =>
      obtain ⟨⟨valid,aligned⟩,effects⟩ : (old.check original binder world residual = true ∧ embeddingCheck _ _ _ = true) ∧
          effectsSubset ((oldSummary old).map RequestName.effect) allowed = true := by
        simpa [Body.check,Bool.and_eq_true] using accepted
      let derived := old.derive (entries := entries) (policy := policy) (outward := outward) (owners := owners)
        (scope := scope) (identity := identity) apiValid valid
      obtain ⟨source,tree⟩ := StaticTree.rebase_basic derived.tree (oldBasic old valid)
        (fun _ member => embeddingCheck_sound aligned member)
        ((oldPerformed old valid).trans (effectsSubset_sound (identity := identity) _ _ effects))
      exact ⟨source,tree⟩
  | @«variable» ctx name localPattern ref =>
      obtain ⟨located,formed⟩ : ref.check = true ∧ localPattern.check original binder world = true :=
        by simpa [Body.check] using accepted
      have known := (ref.realize original identity).sound (by simpa only [Ref.realize_check] using located)
      exact ⟨.variable known (localPattern.formed formed),.variable (known := known) (formed := localPattern.formed formed)⟩
  | @slotCallable ctx name index input output requests latent deps plan rows ref slot recipe =>
      obtain ⟨⟨located,formed⟩,_⟩ : (ref.check = true ∧ Pattern.check original binder world _ = true) ∧ recipe.check = true :=
        by simpa [Body.check,Bool.and_eq_true] using accepted
      have known := (ref.realize original identity).sound (by simpa only [Ref.realize_check] using located)
      have exactSlot := slot.exact
      simp only [Pattern.value,CoreCallableFiniteResourceTemplate.ContractPattern.value] at known
      rw [exactSlot] at known
      let callable := Pattern.function (.closed input) (.closed output) (requests.map EffectName.closed) (closedRequests latent) (.closed plan rows recipe)
      have exactCallable : callable.value original identity = .function input output requests latent plan rows := by
        simp [callable,Pattern.value,Checking.dependencies,Checking.plan,Checking.rows,List.map_map,Function.comp_def,EffectName.value,closedRequests_value]
      have nextKnown : CoreCallableStaticProducer.environment (bindings original identity ctx) name = some (callable.value original identity) :=
        known.trans (congrArg some exactCallable.symm)
      exact ⟨.variable nextKnown (Pattern.formed _ formed),.variable (known := nextKnown) (formed := Pattern.formed _ formed)⟩
  | pair first second ihF ihS | bind first second ihF ihS =>
      obtain ⟨a,b⟩ : first.check original binder world residual allowed = true ∧ second.check original binder world residual allowed = true :=
        by simpa [Body.check] using accepted
      let f := ihF (scope := scope) a
      let t := ihS (scope := scope) b
      first
      | exact ⟨by simpa [Code.instantiate,Pattern.value,Checking.dependencies,Checking.plan,Checking.rows,Need.requirements] using IndexedSource.pair f.source t.source,
          by simpa [Code.instantiate,Pattern.value,Checking.dependencies,Checking.plan,Checking.rows,Need.requirements] using StaticTree.pair f.tree t.tree⟩
      | exact ⟨by simpa [Code.instantiate,bindings,CoreCallableStaticProducer.environment,Checking.dependencies,Checking.plan,Checking.rows,Need.requirements] using IndexedSource.bind f.source t.source,
          by simpa [Code.instantiate,bindings,CoreCallableStaticProducer.environment,Checking.dependencies,Checking.plan,Checking.rows,Need.requirements] using StaticTree.bind f.tree t.tree⟩
  | @lambda parameter ctx bodyCode output privateChecking privateNeeds input requests body ih =>
      obtain ⟨⟨⟨valid,formed⟩,certified⟩,bounded⟩ :
          ((body.check original binder world residual requests = true ∧ Pattern.check original binder world _ = true) ∧
            Checking.check _ = true) ∧ effectsSubset _ requests = true := by
        simpa [Body.check,Bool.and_eq_true] using accepted
      let actual := ih (scope := .none) valid
      have publicCertified := (Checking.recipe identity privateChecking).sound (by simpa only [Checking.recipe_check] using certified)
      have latentBound : ∀ request ∈ privateNeeds.summary.map (RequestName.value identity), request.effect ∈ requests.map (EffectName.value identity) := by
        intro request member
        obtain ⟨name,located,rfl⟩ := List.mem_map.mp member
        exact effectsSubset_sound (identity := identity) _ _ bounded (List.mem_map.mpr ⟨name.effect,List.mem_map.mpr ⟨name,located,rfl⟩,rfl⟩)
      let source := IndexedSource.lambda (allowed := allowed.map (EffectName.value identity)) (scope := scope) actual.source (.identity (Checking.rows identity privateChecking)) (Need.outward privateNeeds identity)
        latentBound publicCertified.certified (Pattern.formed _ formed)
      exact ⟨by simpa [Code.instantiate,Pattern.value,Checking.dependencies,Checking.plan,Checking.rows,Need.requirements,
          bindings,CoreCallableStaticProducer.environment] using source,
        by simpa [Code.instantiate,Pattern.value,Checking.dependencies,Checking.plan,Checking.rows,Need.requirements,
          bindings,CoreCallableStaticProducer.environment] using (StaticTree.lambda (refinement := CoreCallableRootRefinement.Refines.identity _)
          (bodyOutward := Need.outward privateNeeds identity) (latentBound := latentBound) (publicCertified := publicCertified.certified)
          (formed := Pattern.formed _ formed) actual.tree)⟩
  | app function argument ihF ihA =>
      obtain ⟨⟨⟨a,b⟩,admitted⟩,certified⟩ : ((function.check original binder world residual allowed = true ∧
          argument.check original binder world residual allowed = true) ∧ effectsSubset _ allowed = true) ∧ Checking.check _ = true := by
        simpa [Body.check,Bool.and_eq_true] using accepted
      let f := ihF (scope := scope) a
      let v := ihA (scope := scope) b
      have publicCertified := (Checking.recipe identity _).sound (by simpa only [Checking.recipe_check] using certified)
      have current := effectsSubset_sound (identity := identity) _ _ admitted
      exact ⟨by simpa [Code.instantiate,Pattern.value,Checking.dependencies,Checking.plan,Checking.rows,Need.requirements] using
          IndexedSource.app f.source v.source current publicCertified.certified,
        by simpa [Code.instantiate,Pattern.value,Checking.dependencies,Checking.plan,Checking.rows,Need.requirements] using
          StaticTree.app (admitted := current) (publicCertified := publicCertified.certified) f.tree v.tree⟩
  | branch condition yes no ihC ihY ihN =>
      obtain ⟨⟨c,a⟩,b⟩ : (condition.check original binder world residual allowed = true ∧ yes.check original binder world residual allowed = true) ∧
          no.check original binder world residual allowed = true := by simpa [Body.check,Bool.and_eq_true] using accepted
      let tested := ihC (scope := scope) c
      let first := ihY (scope := scope) a
      let second := ihN (scope := scope) b
      exact ⟨by simpa [Code.instantiate,Pattern.value,CoreCallableFiniteResourceTemplate.ContractPattern.value,
          Checking.dependencies,Checking.plan,Checking.rows,Need.requirements] using IndexedSource.branch tested.source first.source second.source (List.Perm.refl []),
        by simpa [Code.instantiate,Pattern.value,CoreCallableFiniteResourceTemplate.ContractPattern.value,
          Checking.dependencies,Checking.plan,Checking.rows,Need.requirements] using StaticTree.branch (sameDemand := List.Perm.refl []) tested.tree first.tree second.tree⟩

abbrev CheckingValue := (dependencies : Dependencies) × (plan : Plan dependencies) × Rows (signature plan)
def Checking.value (identity : Nat) (checking : Checking) : CheckingValue :=
  ⟨checking.dependencies identity,checking.plan identity,checking.rows identity⟩
def sequenceValue (first second : CheckingValue) : CheckingValue :=
  ⟨.sequence first.1 second.1,.sequence first.2.1 second.2.1,sequenceRows first.2.2 second.2.2⟩
def choiceValue (first second : CheckingValue) : CheckingValue :=
  ⟨.choice first.1 second.1,.choice first.2.1 second.2.1,CoreCallableContractSource.choiceRows first.2.2 second.2.2⟩

 theorem EffectName.constant (effect : EffectName) (closed : effect.outside = true) :
    effect.value first = effect.value second := by
  cases effect with
  | closed effect => rfl
  | cell name => cases name <;> simp_all [EffectName.outside,EffectName.value,CoreCallableFiniteResourceTemplate.nameValue]

 theorem oldChecking_constant (body : CoreCallableFiniteResourceTemplate.Body context code pattern)
    (closed : (oldSummary body).all (fun request => request.effect.outside) = true) :
    (Checking.embedded body).value first = (Checking.embedded body).value second := by
  induction body with
  | unit | boolean | integer | reference | «variable» => rfl
  | pair left right ihL ihR | bind left right ihL ihR =>
      obtain ⟨a,b⟩ : (oldSummary left).all (fun request => request.effect.outside) = true ∧
          (oldSummary right).all (fun request => request.effect.outside) = true := by
        simpa [oldSummary,List.all_append] using closed
      change sequenceValue (Checking.value first (.embedded left)) (Checking.value first (.embedded right)) =
        sequenceValue (Checking.value second (.embedded left)) (Checking.value second (.embedded right))
      rw [ihL a,ihR b]
  | @read ctx code name operand ih | @write ctx code name operand ih =>
      obtain ⟨a,b⟩ : (oldSummary operand).all (fun request => request.effect.outside) = true ∧
          EffectName.outside (.cell _) = true := by simpa [oldSummary,List.all_append] using closed
      first
      | change sequenceValue (Checking.value first (.embedded operand)) (Checking.value first (.request (.cell _) 0)) =
          sequenceValue (Checking.value second (.embedded operand)) (Checking.value second (.request (.cell _) 0))
        rw [ih a]
        cases name with
        | activation => rfl
        | bound => simp [EffectName.outside] at b
      | change sequenceValue (Checking.value first (.embedded operand)) (Checking.value first (.request (.cell _) 1)) =
          sequenceValue (Checking.value second (.embedded operand)) (Checking.value second (.request (.cell _) 1))
        rw [ih a]
        cases name with
        | activation => rfl
        | bound => simp [EffectName.outside] at b

 theorem Checking.constant (checking : Checking) (closed : checking.isClosed = true) :
    checking.value first = checking.value second := by
  induction checking with
  | pure | closed => rfl
  | embedded body => exact oldChecking_constant body closed
  | request effect operation =>
      cases effect with
      | closed => rfl
      | cell name =>
          cases name with
          | activation => rfl
          | bound => simp [Checking.isClosed,EffectName.outside] at closed
  | sequence left right ihL ihR | choice left right ihL ihR =>
      obtain ⟨a,b⟩ : left.isClosed = true ∧ right.isClosed = true := by simpa [Checking.isClosed] using closed
      first
      | change sequenceValue (Checking.value first left) (Checking.value first right) =
          sequenceValue (Checking.value second left) (Checking.value second right)
        rw [ihL a,ihR b]
      | change choiceValue (Checking.value first left) (Checking.value first right) =
          choiceValue (Checking.value second left) (Checking.value second right)
        rw [ihL a,ihR b]

 theorem RequestName.constant (request : RequestName) (closed : request.effect.outside = true) :
    request.value first = request.value second := by
  simp only [RequestName.value,request.effect.constant closed (first := first) (second := second)]

 theorem requests_constant (requests : List EffectName) (closed : requests.all EffectName.outside = true) :
    requests.map (EffectName.value first) = requests.map (EffectName.value second) := by
  apply List.map_congr_left
  intro name member
  exact name.constant ((List.all_eq_true.mp closed) name member)

 theorem latent_constant (requests : List RequestName)
    (closed : requests.all (fun request => request.effect.outside) = true) :
    requests.map (RequestName.value first) = requests.map (RequestName.value second) := by
  apply List.map_congr_left
  intro name member
  exact name.constant ((List.all_eq_true.mp closed) name member)

def functionValue (input output : Contract) (requests : List Instance) (latent : Footprint) (checking : CheckingValue) : Contract :=
  .function input output requests latent checking.2.1 checking.2.2

 theorem Pattern.constant (pattern : Pattern) (closed : pattern.isClosed = true) :
    pattern.value original first = pattern.value original second := by
  induction pattern with
  | old pattern => exact CoreCallableFiniteResourceTemplate.ContractPattern.constant closed
  | closed value => rfl
  | pair left right ihL ihR =>
      obtain ⟨a,b⟩ : left.isClosed = true ∧ right.isClosed = true := by simpa [Pattern.isClosed] using closed
      simp only [Pattern.value,ihL a,ihR b]
  | function input output requests latent checking ihI ihO =>
      obtain ⟨⟨⟨⟨a,b⟩,c⟩,d⟩,e⟩ : (((input.isClosed = true ∧ output.isClosed = true) ∧ requests.all EffectName.outside = true) ∧
          latent.all (fun request => request.effect.outside) = true) ∧ checking.isClosed = true := by
        simpa [Pattern.isClosed,Bool.and_eq_true] using closed
      change functionValue (input.value original first) (output.value original first) (requests.map (EffectName.value first))
          (latent.map (RequestName.value first)) (Checking.value first checking) =
        functionValue (input.value original second) (output.value original second) (requests.map (EffectName.value second))
          (latent.map (RequestName.value second)) (Checking.value second checking)
      rw [ihI a,ihO b,requests_constant requests c,latent_constant latent d,Checking.constant checking e]

private theorem andTrue {first second : Bool} (accepted : (first && second) = true) : first = true ∧ second = true := by
  simpa only [Bool.and_eq_true] using accepted

 theorem oldOutput_valid (body : CoreCallableFiniteResourceTemplate.Body context code pattern)
    (accepted : body.check original binder world residual = true) : pattern.check original binder world = true := by
  induction body with
  | unit | boolean | integer | read | write => rfl
  | reference name => exact accepted
  | «variable» ref => exact (andTrue accepted).2
  | pair first second ihF ihS =>
      obtain ⟨a,b⟩ := andTrue accepted
      simp only [CoreCallableFiniteResourceTemplate.ContractPattern.check,ihF a,ihS b,Bool.and_self]
  | bind first second ihF ihS => exact ihS (andTrue accepted).2

 theorem Body.output_valid (body : Body original context code pattern checking needs)
    (accepted : body.check original binder world residual allowed = true) : pattern.check original binder world = true := by
  induction body with
  | embedded old => exact oldOutput_valid old (andTrue (andTrue accepted).1).1
  | «variable» ref => exact (andTrue accepted).2
  | slotCallable => exact (andTrue (andTrue accepted).1).2
  | pair first second ihF ihS =>
      obtain ⟨a,b⟩ := andTrue accepted
      simp only [Pattern.check,ihF a,ihS b,Bool.and_self]
  | bind first second ihF ihS => exact ihS (andTrue accepted).2
  | lambda => exact (andTrue (andTrue (andTrue accepted).1).1).2
  | app function argument ihF ihA =>
      have f := ihF (andTrue (andTrue (andTrue accepted).1).1).1
      exact (andTrue (andTrue (andTrue f).1).1).2
  | branch condition yes no ihC ihY ihN => exact ihY (andTrue (andTrue accepted).1).2

def Need.valid (original : Bindings) (binder : Nat) (world : List Nat) (residual : List Instance) : Need → Bool
  | .empty => true
  | .embedded body => body.check original binder world residual
  | .sequence first second | .choice first second => first.valid original binder world residual && second.valid original binder world residual
  | .emit body requests => body.valid original binder world residual && requests.all (fun request => request.effect.check binder world)

 theorem Body.needs_valid (body : Body original context code pattern checking needs)
    (accepted : body.check original binder world residual allowed = true) : needs.valid original binder world residual = true := by
  induction body with
  | embedded => exact (andTrue (andTrue accepted).1).1
  | «variable» | slotCallable | lambda => rfl
  | pair first second ihF ihS | bind first second ihF ihS =>
      obtain ⟨a,b⟩ := andTrue accepted
      simp only [Need.valid,ihF a,ihS b,Bool.and_self]
  | app function argument ihF ihA =>
      obtain ⟨a,b⟩ := andTrue (andTrue (andTrue accepted).1).1
      have latent := (andTrue (function.output_valid a)).2
      simp only [Need.valid,ihF a,ihA b,latent,Bool.and_self]
  | branch condition yes no ihC ihY ihN =>
      obtain ⟨⟨a,b⟩,c⟩ := (by simpa only [Body.check,Bool.and_eq_true] using accepted)
      simp only [Need.valid,ihC a,ihY b,ihN c,Bool.and_self]

def outsideRequests (requests : List RequestName) : Footprint :=
  (requests.filter fun request => request.effect.outside).map (RequestName.value 0)

 theorem RequestName.outside_exact (request : RequestName)
    (valid : request.effect.check binder world = true) (fresh : identity ∉ world) :
    CallableProtection.outsideCell identity [request.value identity] = outsideRequests [request] := by
  cases request with
  | mk effect operation held =>
      cases effect with
      | cell name =>
          cases name with
          | bound name => simp [CallableProtection.outsideCell,outsideRequests,RequestName.value,EffectName.value,
              EffectName.outside,CoreCallableFiniteResourceTemplate.nameValue]
          | activation value =>
              have different : value ≠ identity := by
                intro same
                subst value
                exact fresh (of_decide_eq_true valid)
              simp [CallableProtection.outsideCell,outsideRequests,RequestName.value,EffectName.value,
                EffectName.outside,CoreCallableFiniteResourceTemplate.nameValue,different]
      | closed effect =>
          cases effect with
          | user => simp [CallableProtection.outsideCell,outsideRequests,RequestName.value,EffectName.value,EffectName.outside]
          | cell value =>
              have member : value ∈ world := (CoreCallableGraphAnnotationChecks.subsetB_sound valid) (by simp [Instance.resources])
              have different : value ≠ identity := by intro same; subst value; exact fresh member
              simp [CallableProtection.outsideCell,outsideRequests,RequestName.value,EffectName.value,EffectName.outside,different]

 theorem requests_outside_exact (requests : List RequestName)
    (valid : requests.all (fun request => request.effect.check binder world) = true) (fresh : identity ∉ world) :
    CallableProtection.outsideCell identity (requests.map (RequestName.value identity)) = outsideRequests requests := by
  induction requests with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨a,b⟩ : head.effect.check binder world = true ∧ rest.all (fun request => request.effect.check binder world) = true := by
        simpa only [List.all_cons,Bool.and_eq_true] using valid
      have h := head.outside_exact a fresh
      have t := ih b
      have both : CallableProtection.outsideCell identity [head.value identity] ++
          CallableProtection.outsideCell identity (rest.map (RequestName.value identity)) =
          outsideRequests [head] ++ outsideRequests rest := by rw [h,t]
      cases outside : head.effect.outside <;>
        cases kept : (head.value identity).effect != Instance.cell identity <;>
        simpa [CallableProtection.outsideCell,outsideRequests,outside,kept] using both


def Need.outsideRequirements : Need → Requirements []
  | .empty => .request [] []
  | .embedded body => body.outsideRequirements
  | .sequence first second => .sequence first.outsideRequirements second.outsideRequirements
  | .choice first second => .choice first.outsideRequirements second.outsideRequirements (List.Perm.refl [])
  | .emit body requests => .emitAfter body.outsideRequirements [] (outsideRequests requests)

 theorem Need.hides (needs : Need) (valid : needs.valid original binder world residual = true) (fresh : identity ∉ world) :
    ResourceRequirements.Hides identity (needs.requirements identity) needs.outsideRequirements := by
  induction needs with
  | empty => exact .request
  | embedded body => exact body.hides valid fresh
  | sequence first second ihF ihS | choice first second ihF ihS =>
      obtain ⟨a,b⟩ := andTrue valid
      first | exact .sequence (ihF a) (ihS b) | exact .choice (ihF a) (ihS b)
  | emit body requests ih =>
      obtain ⟨a,b⟩ := andTrue valid
      simpa only [Need.requirements,Need.outsideRequirements,requests_outside_exact requests b fresh] using
        ResourceRequirements.Hides.emitAfter (raw := requests.map (RequestName.value identity)) (ih a)

theorem EffectName.issued_closed (effect : EffectName)
    (valid : effect.check binder world = true) (closed : effect.outside = true) :
    (effect.value identity).resources ⊆ world := by
  cases effect with
  | closed effect => exact CoreCallableGraphAnnotationChecks.subsetB_sound valid
  | cell name =>
      cases name with
      | bound name => simp [EffectName.outside] at closed
      | activation value =>
          have member : value ∈ world := of_decide_eq_true valid
          simpa [EffectName.value,CoreCallableFiniteResourceTemplate.nameValue,Instance.resources] using member

theorem Pattern.formed_closed (pattern : Pattern)
    (valid : pattern.check original binder world = true) (closed : pattern.isClosed = true) :
    ScopedPorts.InWorld world (pattern.value original identity).port := by
  induction pattern with
  | old pattern => exact CoreCallableFiniteResourceTemplate.ContractPattern.formed_closed valid closed
  | closed value => exact CoreCallableGraphAnnotationChecks.subsetB_sound valid
  | pair first second ihF ihS =>
      obtain ⟨a,b⟩ := andTrue valid
      obtain ⟨c,d⟩ := andTrue closed
      simpa [Pattern.value,ScopedPorts.InWorld,Contract.port,Contract.value,
        SourcePlannedTyping.Value.erase,SourceDependencyAnnotations.Value.erase,CoherentSourceTypes.Value.port,
        ScopedPorts.Port.resources] using List.append_subset.mpr ⟨ihF a c,ihS b d⟩
  | function input output requests latent checking ihI ihO =>
      obtain ⟨⟨⟨a,b⟩,c⟩,_⟩ : ((input.check original binder world = true ∧ output.check original binder world = true) ∧
          requests.all (EffectName.check binder world) = true) ∧ _ := by simpa [Pattern.check,Bool.and_eq_true] using valid
      obtain ⟨⟨⟨⟨d,e⟩,f⟩,_⟩,_⟩ : (((input.isClosed = true ∧ output.isClosed = true) ∧
          requests.all EffectName.outside = true) ∧ _) ∧ _ := by simpa [Pattern.isClosed,Bool.and_eq_true] using closed
      have issued : (requests.map (EffectName.value identity)).flatMap Instance.resources ⊆ world := by
        intro resource member
        obtain ⟨effect,located,retained⟩ := List.mem_flatMap.mp member
        obtain ⟨name,selected,rfl⟩ := List.mem_map.mp located
        exact name.issued_closed ((List.all_eq_true.mp c) name selected) ((List.all_eq_true.mp f) name selected) retained
      simpa [Pattern.value,ScopedPorts.InWorld,Contract.port,Contract.value,
        SourcePlannedTyping.Value.erase,SourceDependencyAnnotations.Value.erase,CoherentSourceTypes.Value.port,
        ScopedPorts.Port.resources] using List.append_subset.mpr ⟨List.append_subset.mpr ⟨ihI a d,ihO b e⟩,issued⟩

def oldContext : Context → Option CoreCallableFiniteResourceTemplate.Context
  | [] => some []
  | (name,.old pattern)::rest => (oldContext rest).map ((name,pattern)::·)
  | _ => none

def aligned (original : Bindings) (context : Context) : Bool :=
  match oldContext context with
  | some old => CoreCallableFiniteResourceTemplate.aligned original old
  | none => false

theorem oldContext_bindings (same : oldContext context = some old) :
    bindings original identity context = CoreCallableFiniteResourceTemplate.bindings original identity old := by
  induction context generalizing old with
  | nil => cases same; rfl
  | cons head rest ih =>
      rcases head with ⟨name,pattern⟩
      cases pattern <;> try simp [oldContext] at same
      rename_i pattern
      cases tail : oldContext rest with
      | none => simp [tail] at same
      | some oldTail =>
          have equal : (name,pattern)::oldTail = old := by simpa [oldContext,tail] using same
          subst old
          simp only [bindings,Pattern.value,CoreCallableFiniteResourceTemplate.bindings]
          rw [ih tail]

theorem aligned_original (valid : aligned original context = true) : bindings original identity context = original := by
  cases same : oldContext context with
  | none => simp [aligned,same] at valid
  | some old =>
      have accepted : CoreCallableFiniteResourceTemplate.aligned original old = true := by simpa [aligned,same] using valid
      exact (oldContext_bindings same).trans (CoreCallableFiniteResourceTemplate.aligned_original accepted)

#print axioms Checking.recipe_check
#print axioms Ref.realize_check
#print axioms StaticTree.rebase_basic
#print axioms FunctionSlot.exact
#print axioms effectsSubset_sound
#print axioms Pattern.formed
#print axioms Need.outward
#print axioms embeddingCheck_sound
#print axioms Body.derive
#print axioms Checking.constant
#print axioms Pattern.constant
#print axioms Body.output_valid
#print axioms Body.needs_valid
#print axioms requests_outside_exact
#print axioms Need.hides
#print axioms Pattern.formed_closed
#print axioms aligned_original

end Ash.OneShot.CoreCallableCompositionalResourceBody
