import CoreCallableFiniteClauseTemplate
namespace Ash.OneShot.CoreCallableFiniteHandlerSource
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract Environment sequenceRows choiceRows)
open CoreCallableContractRegistries (Owners OwnerContract)
open CoreCallableContractAdmission CoreCallableStaticProducer CoreCallableFiniteClauseTemplate
open CoreCallableReceiverRefinement (LexicalBounds)
open SourceDeclarationPlans (Plan ModePlans ClausePlans)
open SourceDependencyAnnotations (Dependencies ClauseDependencies)
open SourcePlanSignatures (signature modeSignatures clauseSignatures)
open SourceScheduledCleanupInterfaces.Lexical.Recursive
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
local instance : SourcePlannedChecks.DeclarationPolicy := declarationPolicy

structure OfferReceipt (entries : OperationEntries) (policy : Syntax.TicketPolicy)
    (outward : List Instance) (owners : Owners) (world : List Nat) (allowed : List Instance)
    (bindings : Bindings) (parameter binder : Nat) (argument input answer : Contract)
    (resumeEffects closeEffects : List Instance) (code : Code) (held disposes : Bool) (row : Footprint)
    (data : Template input answer binder ((parameter,argument) :: bindings) code)
    (lexical : LexicalBounds) (receiver : List Nat) : Type where
  source : SourceOffer (registry entries policy) outward owners world (environment bindings) allowed parameter binder argument input answer
    resumeEffects closeEffects code held disposes (some row) (.available data.plan) (.available data.rows)
  authenticated : OfferAuthentication (registry entries policy) outward source lexical receiver

/-- Available offers are computed from one finite template. Both full-compatible
owner modes specialize the exact same code/contract/map and private families. -/
def checkOffer (data : Template input answer binder ((parameter,argument) :: bindings) code)
    (entries : OperationEntries) (policy : Syntax.TicketPolicy) (outward : List Instance)
    (owners : Owners) (world : List Nat) (allowed resumeEffects closeEffects : List Instance)
    (held disposes : Bool) (row : Footprint) (lexical : LexicalBounds) (receiver : List Nat) :
    Except Error (OfferReceipt entries policy outward owners world allowed bindings parameter binder argument input answer
      resumeEffects closeEffects code held disposes row data lexical receiver) := do
  if same : resumeEffects = allowed then
    if noDispose : code.requiredActions.dispose = false then
      let checked ← data.check entries policy outward owners world allowed lexical receiver
      let bodies := fun owner contract (a : contract.input = input) (b : contract.answer = answer)
          (c : contract.resumeEffects = resumeEffects) (_d : contract.closeEffects = closeEffects)
          (_e : contract.held = held) (_balanced : contract.closeDemand.Perm contract.resumeDemand) =>
        SourceBody.typed (checked.specialize owner contract a b (c.trans same)).source
          (data.normal owner contract disposes row) (data.protectedRows owner contract disposes row)
      let resumeInterface := fun (_required : code.requiredActions.resume = true) => same
      let closeInterface := fun (required : code.requiredActions.dispose = true) => by
        rw [noDispose] at required
        cases required
      .ok ⟨SourceOffer.available resumeInterface closeInterface bodies,
        OfferAuthentication.available (bodySource := bodies) resumeInterface closeInterface
          (fun owner contract a b c _d _e _balanced =>
            .typed (normal := data.normal owner contract disposes row)
              (closing := data.protectedRows owner contract disposes row)
              (checked.specialize owner contract a b (c.trans same)).authenticated)⟩
    else .error .capability
  else .error .unavailableEffect

def modeFamily (data : Template input answer binder bindings code) (offered : Option Footprint) : Option (Nat → Dependencies) :=
  offered.map (fun _ => data.dependencies)

def modePlan (data : Template input answer binder bindings code) (offered : Option Footprint) : ModePlans (modeFamily data offered) :=
  match offered with | none => .unavailable | some _ => .available data.plan

def modeRows (data : Template input answer binder bindings code) (offered : Option Footprint) : ModeRows (modeSignatures (modePlan data offered)) :=
  match offered with | none => .unavailable | some _ => .available data.rows

structure ModeReceipt (entries : OperationEntries) (policy : Syntax.TicketPolicy)
    (outward : List Instance) (owners : Owners) (world : List Nat) (allowed : List Instance)
    (bindings : Bindings) (parameter binder : Nat) (argument input answer : Contract)
    (resumeEffects closeEffects : List Instance) (code : Code) (held disposes : Bool) (offered : Option Footprint)
    (data : Template input answer binder ((parameter,argument) :: bindings) code)
    (lexical : LexicalBounds) (receiver : List Nat) : Type where
  source : SourceOffer (registry entries policy) outward owners world (environment bindings) allowed parameter binder argument input answer
    resumeEffects closeEffects code held disposes offered (modePlan data offered) (modeRows data offered)
  authenticated : OfferAuthentication (registry entries policy) outward source lexical receiver

def checkMode (data : Template input answer binder ((parameter,argument) :: bindings) code)
    (offered : Option Footprint) (entries : OperationEntries) (policy : Syntax.TicketPolicy) (outward : List Instance)
    (owners : Owners) (world : List Nat) (allowed resumeEffects closeEffects : List Instance)
    (held disposes : Bool) (lexical : LexicalBounds) (receiver : List Nat) :
    Except Error (ModeReceipt entries policy outward owners world allowed bindings parameter binder argument input answer
      resumeEffects closeEffects code held disposes offered data lexical receiver) :=
  match offered with
  | none => .ok ⟨.unavailable,.unavailable⟩
  | some row => do
    let checked ← checkOffer data entries policy outward owners world allowed resumeEffects closeEffects held disposes row lexical receiver
    .ok ⟨checked.source,checked.authenticated⟩

/-- Declaration instructions retain the original exact operation record and
clause syntax, finite mode choices and original support bound. -/
inductive Declarations (entries : OperationEntries) (requested : Instance) (answer : Contract) (bindings : Bindings) : Clauses → Type where
  | nil : Declarations entries requested answer bindings .nil
  | cons (reference : OperationRef entries requested operation argument input)
      (data : Template input answer binder ((parameter,argument) :: bindings) code)
      (supportBound : List Nat) (ordinary protectedMode : Option Footprint)
      (resumeEffects closeEffects : List Instance)
      (rest : Declarations entries requested answer bindings clauses) :
      Declarations entries requested answer bindings (.cons operation parameter binder code clauses)

def Declarations.table (data : Declarations entries requested answer bindings clauses) : List (Nat × ClauseContract) :=
  match data with
  | .nil => []
  | .cons (operation := operation) _ _ _ ordinary protectedMode _ _ rest =>
      (operation,⟨false,ordinary,protectedMode⟩) :: rest.table

def Declarations.families (data : Declarations entries requested answer bindings clauses) : ClauseDependencies :=
  match data with
  | .nil => []
  | .cons (operation := operation) _ body _ ordinary protectedMode _ _ rest =>
      (operation,modeFamily body ordinary,modeFamily body protectedMode) :: rest.families

def Declarations.plans (data : Declarations entries requested answer bindings clauses) : ClausePlans clauses data.families :=
  match data with
  | .nil => .nil
  | .cons _ body _ ordinary protectedMode _ _ rest => .cons (modePlan body ordinary) (modePlan body protectedMode) rest.plans

def Declarations.rows (data : Declarations entries requested answer bindings clauses) : ClauseRows (clauseSignatures data.plans) :=
  match data with
  | .nil => .nil
  | .cons _ body supportBound ordinary protectedMode _ _ rest =>
      .cons (modeRows body ordinary) (modeRows body protectedMode) rest.rows supportBound

private def canonical (input answer : Contract) (allowed : List Instance) : OwnerContract :=
  ⟨input,answer,false,[],[],[],some [],allowed,allowed⟩

private theorem clause_typed {entries : OperationEntries} {policy : Syntax.TicketPolicy}
    {outward : List Instance} {owners : Owners} {world : List Nat} {allowed : List Instance}
    {input answer : Contract} {binder : Nat} {bindings : Bindings} {code : Code}
    {data : Template input answer binder bindings code} {lexical : LexicalBounds} {receiver : List Nat}
    (checked : Receipt entries policy outward owners world allowed data lexical receiver) :
    ScopedPorts.Typed (registry entries policy).ports world (environment bindings).ports
      (.bound binder input.port answer.port allowed allowed) allowed code answer.port := by
  let contract := canonical input answer allowed
  have source := (checked.specialize 0 contract rfl rfl rfl).source
  have known := CoherentSourceTypes.Owners.ports_lookup (Owners.known_lower
    (owners := owners.insert 0 contract) (owner := 0) (contract := contract) Owners.insert_here)
  exact source.erase_at (.bound known)

structure DeclarationReceipt (entries : OperationEntries) (policy : Syntax.TicketPolicy)
    (outward : List Instance) (owners : Owners) (world : List Nat) (allowed : List Instance)
    (data : Declarations entries requested answer bindings clauses) (lexical : LexicalBounds) (receiver : List Nat) : Type where
  source : SourceDeclarations (registry entries policy) outward owners world (environment bindings) allowed requested answer
    clauses data.table data.plans data.rows
  authenticated : DeclarationAuthentication (registry entries policy) outward source lexical receiver
  modes : SourceTemplates.ClauseModes clauses data.table
  capabilities : ClausesUse policy clauses
  recipes : ClauseDeclarations outward clauses data.families []
  typed : ScopedPorts.ClausesTyped (registry entries policy).ports world (environment bindings).ports requested answer.port allowed clauses

def checkDeclarations (data : Declarations entries requested answer bindings clauses)
    (policy : Syntax.TicketPolicy) (outward : List Instance) (owners : Owners) (world : List Nat) (allowed : List Instance)
    (lexical : LexicalBounds) (receiver : List Nat) :
    Except Error (DeclarationReceipt entries policy outward owners world allowed data lexical receiver) :=
  match data with
  | .nil => .ok ⟨.nil,.nil,.nil,.nil,.nil,.nil⟩
  | .cons (operation := operation) (parameter := parameter) (binder := binder) (code := code) (argument := argument) (input := input) reference body supportBound ordinary protectedMode resumeEffects closeEffects rest => do
    if located : reference.check = true then
      if _useValid : currentUse policy (.ticket binder (policy binder)) .available code = some .consumed then
      if supported : body.supported = true then
        if permission : (policy binder).resume = true then
          if required : code.requiredActions.resume = true then
            if noDispose : code.requiredActions.dispose = false then
              if stored : CoreCallableGraphAnnotationChecks.subsetB supportBound receiver = true then
                if bounded : CoreCallableGraphAnnotationChecks.subsetB
                    (ScopedPorts.Support.evaluate (lexical.extend parameter receiver).environment code.dependencies) supportBound = true then
                  let checked ← body.check entries policy outward owners world allowed (lexical.extend parameter receiver) receiver
                  let a ← checkMode body ordinary entries policy outward owners world allowed resumeEffects closeEffects false false (lexical.extend parameter receiver) receiver
                  let b ← checkMode body protectedMode entries policy outward owners world allowed resumeEffects closeEffects true false (lexical.extend parameter receiver) receiver
                  let tail ← checkDeclarations rest policy outward owners world allowed lexical receiver
                  let known := reference.sound located
                  let source := SourceDeclarations.cons supportBound known a.source b.source tail.source
                  let ordinaryRecipe : DeclarationModes outward code.requiredActions [] (modeFamily body ordinary) := by
                    cases ordinary with
                    | none => exact .unavailable
                    | some row => exact .available (.existing (body.recipe supported required).erase)
                  let protectedRecipe : DeclarationModes outward code.requiredActions [] (modeFamily body protectedMode) := by
                    cases protectedMode with
                    | none => exact .unavailable
                    | some row => exact .available (.existing (body.recipe supported required).erase)
                  .ok ⟨source,
                    .cons known (SourceSupport.bounds_iff.mpr (CoreCallableGraphAnnotationChecks.subsetB_sound bounded))
                      (CoreCallableGraphAnnotationChecks.subsetB_sound stored) a.authenticated b.authenticated tail.authenticated,
                    .cons (by intro impossible; rw [noDispose] at impossible; cases impossible) tail.modes,
                    .cons (body.use supported permission) tail.capabilities,
                    by simpa [Declarations.families] using (ClauseDeclarations.cons ordinaryRecipe protectedRecipe tail.recipes),
                    .cons (input := argument.port) (output := input.port) (by simp [CoreCallableContractRegistries.Registry.ports,registry,known])
                      (by simpa [environment,CoreCallableContractSource.Environment.ports_extend] using clause_typed checked) tail.typed⟩
                else .error .support
              else .error .support
            else .error .capability
          else .error .capability
        else .error .capability
      else .error (.unsupported "clause template")
      else .error .capability
    else .error .operationShadowing

def operationKeys : OperationEntries → Instance → List Nat
  | [], _ => []
  | (effect,operation,_,_) :: rest, requested =>
      if requested = effect then operation :: operationKeys rest requested else operationKeys rest requested

/-- Symmetric finite coverage and unique literal clause keys. Extra clauses
are checked against the SAME registry, independently of indexed references. -/
def clauseKeysCheck (entries : OperationEntries) (requested : Instance) (clauses : Clauses) : Bool :=
  CoreCallableGraphAnnotationChecks.subsetB (operationKeys entries requested) (ScopedTyping.clauseKeys clauses) &&
  CoreCallableGraphAnnotationChecks.subsetB (ScopedTyping.clauseKeys clauses) (operationKeys entries requested) &&
  decide (ScopedTyping.clauseKeys clauses).Nodup

private theorem known_key (known : operations entries requested operation = some pair) :
    operation ∈ operationKeys entries requested := by
  induction entries with
  | nil => cases known
  | cons entry rest ih =>
    obtain ⟨effect,key,input,output⟩ := entry
    simp only [operations] at known
    by_cases same : requested = effect ∧ operation = key
    · simp only [if_pos same] at known
      simp [operationKeys,same.1,same.2]
    · simp only [if_neg same] at known
      by_cases effectSame : requested = effect
      · simp only [operationKeys,if_pos effectSame,List.mem_cons]
        exact Or.inr (ih known)
      · simpa [operationKeys,effectSame] using ih known

private theorem coverage (valid : CoreCallableGraphAnnotationChecks.subsetB (operationKeys entries requested) (ScopedTyping.clauseKeys clauses) = true) :
    ScopedPorts.Covers (registry entries policy).ports requested clauses := by
  intro operation input output known
  change (operations entries requested operation).map (fun pair => (pair.1.port,pair.2.port)) = some (input,output) at known
  cases actual : operations entries requested operation with
  | none => simp [actual] at known
  | some pair => exact CoreCallableGraphAnnotationChecks.subsetB_sound valid (known_key actual)


/-- Public bridge for the same full original registry coverage proof moved below the checker. -/
theorem coverage_from_keys
    (valid : CoreCallableGraphAnnotationChecks.subsetB (operationKeys entries requested) (ScopedTyping.clauseKeys clauses) = true) :
    ScopedPorts.Covers (registry entries policy).ports requested clauses := coverage valid

/-- Full operation coverage is derived from the existing symmetric key check;
this output does not replace the exact selected operation records. -/
theorem checked_coverage
    (valid : clauseKeysCheck entries requested clauses = true) :
    ScopedPorts.Covers (registry entries policy).ports requested clauses := by
  obtain ⟨⟨first,_second⟩,_unique⟩ :
      (CoreCallableGraphAnnotationChecks.subsetB (operationKeys entries requested) (ScopedTyping.clauseKeys clauses) = true ∧
       CoreCallableGraphAnnotationChecks.subsetB (ScopedTyping.clauseKeys clauses) (operationKeys entries requested) = true) ∧
      decide (ScopedTyping.clauseKeys clauses).Nodup = true := by
    simpa only [clauseKeysCheck, Bool.and_eq_true] using valid
  exact coverage first

/-- Exact-current bounds retain every literal declaration bound, including
unused support. The formal receives the SAME receiver and shadows outer names. -/
def Declarations.currentBounds (data : Declarations entries requested answer bindings clauses)
    (lexical : LexicalBounds) (receiver : List Nat) : Prop :=
  match data with
  | .nil => True
  | .cons (operation := operation) (argument := argument) (input := input) (parameter := parameter) (code := code) _ _ supportBound _ _ _ _ rest =>
      operations entries requested operation = some (argument, input) ∧
      SourceSupport.Bounds (lexical.extend parameter receiver).environment code.dependencies supportBound ∧
      supportBound ⊆ receiver ∧ rest.currentBounds lexical receiver

def Declarations.currentBoundsCheck (data : Declarations entries requested answer bindings clauses)
    (lexical : LexicalBounds) (receiver : List Nat) : Bool :=
  match data with
  | .nil => true
  | .cons (parameter := parameter) (code := code) reference _ supportBound _ _ _ _ rest =>
      reference.check &&
      CoreCallableGraphAnnotationChecks.subsetB
        (ScopedPorts.Support.evaluate (lexical.extend parameter receiver).environment code.dependencies) supportBound &&
      CoreCallableGraphAnnotationChecks.subsetB supportBound receiver && rest.currentBoundsCheck lexical receiver

theorem Declarations.currentBoundsCheck_sound
    (data : Declarations entries requested answer bindings clauses)
    (accepted : data.currentBoundsCheck lexical receiver = true) :
    data.currentBounds lexical receiver := by
  induction data with
  | nil => exact True.intro
  | cons reference body supportBound ordinary protectedMode resumeEffects closeEffects rest ih =>
      simp only [Declarations.currentBoundsCheck, Bool.and_eq_true] at accepted
      obtain ⟨⟨⟨located,bounded⟩,stored⟩,tail⟩ := accepted
      exact ⟨reference.sound located,
        SourceSupport.bounds_iff.mpr (CoreCallableGraphAnnotationChecks.subsetB_sound bounded),
        CoreCallableGraphAnnotationChecks.subsetB_sound stored,ih tail⟩

/-- This additional carrier is OUTPUT of the existing finite checker. Its
provenance and all rich judgments are constructed, never annotation fields. -/
structure CurrentDeclarationReceipt (entries : OperationEntries) (policy : Syntax.TicketPolicy)
    (outward : List Instance) (owners : Owners) (world : List Nat) (allowed : List Instance)
    (data : Declarations entries requested answer bindings clauses) (lexical : LexicalBounds) (receiver : List Nat) : Type where
  checked : DeclarationReceipt entries policy outward owners world allowed data lexical receiver
  bounds : data.currentBounds lexical receiver

def checkCurrentDeclarations (data : Declarations entries requested answer bindings clauses)
    (policy : Syntax.TicketPolicy) (outward : List Instance) (owners : Owners) (world : List Nat) (allowed : List Instance)
    (lexical : LexicalBounds) (receiver : List Nat) :
    Except Error (CurrentDeclarationReceipt entries policy outward owners world allowed data lexical receiver) := do
  let checked ← checkDeclarations data policy outward owners world allowed lexical receiver
  if accepted : data.currentBoundsCheck lexical receiver = true then
    .ok ⟨checked,data.currentBoundsCheck_sound accepted⟩
  else .error .support

#print axioms coverage_from_keys
#print axioms checked_coverage
#print axioms Declarations.currentBoundsCheck
#print axioms Declarations.currentBoundsCheck_sound
#print axioms checkCurrentDeclarations

end Ash.OneShot.CoreCallableFiniteHandlerSource
