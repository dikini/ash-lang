import CoreCallableStaticFiniteData

/-! Existing finite resource indices are shared below the producer. These are
relocated declarations with their original full indices and Boolean guards. -/
namespace Ash.OneShot.CoreCallableFiniteResourceTemplate
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract sequenceRows)
open CoreCallableContractAdmission CoreCallableReceiverRefinement
open CoreCallableStaticProducer (Bindings BindingRef RecipeTag)
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceDependencyAnnotations (Dependencies)
open RecursiveRequirements (Requirements)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
local instance : SourcePlannedChecks.DeclarationPolicy :=
  SourceScheduledCleanupInterfaces.Lexical.Recursive.declarationPolicy

def nameValue (identity : Nat) : Instantiation.ResourceName → Nat
  | .activation value => value
  | .bound _ => identity

def nameCheck (binder : Nat) (world : List Nat) : Instantiation.ResourceName → Bool
  | .activation value => decide (value ∈ world)
  | .bound name => decide (name = binder)

/-- Slots select a literal original list position, not a name-only join. -/
inductive ContractPattern where
  | unit | boolean | integer
  | reference : Instantiation.ResourceName → ContractPattern
  | pair : ContractPattern → ContractPattern → ContractPattern
  | slot : Nat → ContractPattern
  deriving DecidableEq, Repr

def slotContract (original : Bindings) (index : Nat) : Contract :=
  ((original[index]?).map Prod.snd).getD .unit

def ContractPattern.value (original : Bindings) (identity : Nat) : ContractPattern → Contract
  | .unit => .unit
  | .boolean => .boolean
  | .integer => .integer
  | .reference name => .reference (nameValue identity name)
  | .pair left right => .pair (left.value original identity) (right.value original identity)
  | .slot index => slotContract original index

def ContractPattern.check (original : Bindings) (binder : Nat) (world : List Nat) : ContractPattern → Bool
  | .unit | .boolean | .integer => true
  | .reference name => nameCheck binder world name
  | .pair left right => left.check original binder world && right.check original binder world
  | .slot index => decide (index < original.length) &&
      CoreCallableGraphAnnotationChecks.subsetB (slotContract original index).port.resources world

def ContractPattern.closed : ContractPattern → Bool
  | .reference (.bound _) => false
  | .pair left right => left.closed && right.closed
  | _ => true

abbrev Context := List (Nat × ContractPattern)

def bindings (original : Bindings) (identity : Nat) : Context → Bindings
  | [] => []
  | (name,pattern) :: rest => (name,pattern.value original identity) :: bindings original identity rest

def contextClosed (context : Context) : Bool := context.all (fun entry => entry.2.closed)

/-- Exact original ordinary names and positional slots, in original shadow
order. Only recursive Body.bind extends this list during the check. -/
def aligned (original : Bindings) (context : Context) (index : Nat := 0) : Bool :=
  match original,context with
  | [],[] => true
  | (name,_) :: rest,(selected,pattern) :: tail =>
      decide (selected = name) && decide (pattern = .slot index) && aligned rest tail (index+1)
  | _,_ => false

/-- Finite exact-position view of all original ordinary bindings. -/
def contextTemplate (original : Bindings) (index : Nat := 0) : Context :=
  match original with
  | [] => []
  | (name,_) :: rest => (name,.slot index) :: contextTemplate rest (index+1)

inductive LocalRef : Context → Nat → ContractPattern → Type where
  | head : LocalRef ((name,pattern) :: rest) name pattern
  | tail (next : LocalRef rest name pattern) : LocalRef ((bound,value) :: rest) name pattern

def LocalRef.check : LocalRef context name pattern → Bool
  | .head => true
  | .tail (bound := bound) next => decide (name ≠ bound) && next.check

def LocalRef.realize (reference : LocalRef context name pattern) :
    BindingRef (bindings original identity context) name (pattern.value original identity) :=
  match reference with
  | .head => .head
  | .tail next => .tail next.realize

/-- A resource handle is an ordinary bind; this tree records its exact shadow
order. The bound resource name lives in the independent resource namespace. -/
inductive Body : Context → Code → ContractPattern → Type where
  | unit : Body context .unit .unit
  | boolean (value : Bool) : Body context (.boolean value) .boolean
  | integer (value : Int) : Body context (.integer value) .integer
  | reference (name : Instantiation.ResourceName) : Body context (.resourceRef name) (.reference name)
  | variable (reference : LocalRef context name pattern) : Body context (.variable name) pattern
  | pair (left : Body context first a) (right : Body context second b) : Body context (.pair first second) (.pair a b)
  | bind (initial : Body context first input) (body : Body ((parameter,input) :: context) second output) :
      Body context (.bind parameter first second) output
  | read (operand : Body context code (.reference name)) : Body context (.perform (.cell name) 0 code) .integer
  | write (operand : Body context code (.pair (.reference name) .integer)) : Body context (.perform (.cell name) 1 code) .unit

/-- The allowed-effect check is finite: bound names denote this fresh cell;
already closed cell names must be present in the original residual allowance. -/
def allowedName (binder : Nat) (residual : List Instance) : Instantiation.ResourceName → Bool
  | .bound name => decide (name = binder)
  | .activation value => decide (.cell value ∈ residual)

def Body.check (original : Bindings) (binder : Nat) (world : List Nat) (residual : List Instance) :
    Body context code pattern → Bool
  | .unit | .boolean _ | .integer _ => true
  | .reference name => nameCheck binder world name
  | .variable ref => ref.check && pattern.check original binder world
  | .pair left right | .bind left right => left.check original binder world residual && right.check original binder world residual
  | .read (name := name) operand | .write (name := name) operand =>
      operand.check original binder world residual && nameCheck binder world name && allowedName binder residual name

def Body.dependencies (body : Body context code pattern) (identity : Nat) : Dependencies :=
  match body with
  | .unit | .boolean _ | .integer _ | .reference _ | .variable _ => .pure
  | .pair left right | .bind left right => .sequence (left.dependencies identity) (right.dependencies identity)
  | .read (name := name) operand => .sequence (operand.dependencies identity) (.request (.cell (nameValue identity name)) 0)
  | .write (name := name) operand => .sequence (operand.dependencies identity) (.request (.cell (nameValue identity name)) 1)

def Body.plan (body : Body context code pattern) (identity : Nat) : Plan (body.dependencies identity) :=
  match body with
  | .unit | .boolean _ | .integer _ | .reference _ | .variable _ => .pure
  | .pair left right | .bind left right => .sequence (left.plan identity) (right.plan identity)
  | .read operand | .write operand => .sequence (operand.plan identity) .request

def Body.rows (body : Body context code pattern) (identity : Nat) : Rows (signature (body.plan identity)) :=
  match body with
  | .unit | .boolean _ | .integer _ | .reference _ | .variable _ => Rows.pure
  | .pair left right | .bind left right => sequenceRows (left.rows identity) (right.rows identity)
  | .read operand | .write operand => sequenceRows (operand.rows identity) Rows.request

def Body.requirements (body : Body context code pattern) (identity : Nat) : Requirements [] :=
  match body with
  | .unit | .boolean _ | .integer _ | .reference _ | .variable _ => .request [] []
  | .pair left right | .bind left right => .sequence (left.requirements identity) (right.requirements identity)
  | .read (name := name) operand => .emitAfter (operand.requirements identity) [] [⟨.cell (nameValue identity name),0,false⟩]
  | .write (name := name) operand => .emitAfter (operand.requirements identity) [] [⟨.cell (nameValue identity name),1,false⟩]

/-- Residual requirements are computed from the SAME literal name tags. -/
def outsideName (operation : Nat) : Instantiation.ResourceName → Footprint
  | .bound _ => []
  | .activation value => [⟨.cell value,operation,false⟩]

def Body.outsideRequirements (body : Body context code pattern) : Requirements [] :=
  match body with
  | .unit | .boolean _ | .integer _ | .reference _ | .variable _ => .request [] []
  | .pair left right | .bind left right => .sequence left.outsideRequirements right.outsideRequirements
  | .read (name := name) operand => .emitAfter operand.outsideRequirements [] (outsideName 0 name)
  | .write (name := name) operand => .emitAfter operand.outsideRequirements [] (outsideName 1 name)

def Body.resourcePlan (body : Body context code pattern) :
    Plan (.sequence .pure (.resource (fun identity => body.dependencies identity))) :=
  .sequence .pure (.resource (fun identity => body.plan identity))

def Body.resourceRows (body : Body context code pattern) : Rows (signature body.resourcePlan) :=
  sequenceRows Rows.pure (Rows.resource (fun identity => body.rows identity))

end Ash.OneShot.CoreCallableFiniteResourceTemplate

namespace Ash.OneShot.CoreCallableCompositionalResourceBody
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract sequenceRows)
open CoreCallableContractAdmission CoreCallableReceiverRefinement
open CoreCallableStaticProducer (Bindings BindingRef RecipeTag)
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

/-- Full closed function slots are selected by literal original list position. -/
inductive FunctionSlot : Bindings → Nat → Contract → Contract → List Instance → Footprint →
    {dependencies : Dependencies} → (plan : Plan dependencies) → Rows (signature plan) → Type where
  | head : FunctionSlot ((name,.function input output requests latent plan rows)::rest) 0 input output requests latent plan rows
  | tail : FunctionSlot rest index input output requests latent plan rows →
      FunctionSlot ((name,value)::rest) (index+1) input output requests latent plan rows

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

abbrev CheckingValue := (dependencies : Dependencies) × (plan : Plan dependencies) × Rows (signature plan)

def Checking.value (identity : Nat) (checking : Checking) : CheckingValue :=
  ⟨checking.dependencies identity,checking.plan identity,checking.rows identity⟩

def sequenceValue (first second : CheckingValue) : CheckingValue :=
  ⟨.sequence first.1 second.1,.sequence first.2.1 second.2.1,sequenceRows first.2.2 second.2.2⟩

def choiceValue (first second : CheckingValue) : CheckingValue :=
  ⟨.choice first.1 second.1,.choice first.2.1 second.2.1,CoreCallableContractSource.choiceRows first.2.2 second.2.2⟩

def functionValue (input output : Contract) (requests : List Instance) (latent : Footprint) (checking : CheckingValue) : Contract :=
  .function input output requests latent checking.2.1 checking.2.2

def Need.valid (original : Bindings) (binder : Nat) (world : List Nat) (residual : List Instance) : Need → Bool
  | .empty => true
  | .embedded body => body.check original binder world residual
  | .sequence first second | .choice first second => first.valid original binder world residual && second.valid original binder world residual
  | .emit body requests => body.valid original binder world residual && requests.all (fun request => request.effect.check binder world)

def outsideRequests (requests : List RequestName) : Footprint :=
  (requests.filter fun request => request.effect.outside).map (RequestName.value 0)

def Need.outsideRequirements : Need → Requirements []
  | .empty => .request [] []
  | .embedded body => body.outsideRequirements
  | .sequence first second => .sequence first.outsideRequirements second.outsideRequirements
  | .choice first second => .choice first.outsideRequirements second.outsideRequirements (List.Perm.refl [])
  | .emit body requests => .emitAfter body.outsideRequirements [] (outsideRequests requests)

def oldContext : Context → Option CoreCallableFiniteResourceTemplate.Context
  | [] => some []
  | (name,.old pattern)::rest => (oldContext rest).map ((name,pattern)::·)
  | _ => none

def aligned (original : Bindings) (context : Context) : Bool :=
  match oldContext context with
  | some old => CoreCallableFiniteResourceTemplate.aligned original old
  | none => false

end Ash.OneShot.CoreCallableCompositionalResourceBody
