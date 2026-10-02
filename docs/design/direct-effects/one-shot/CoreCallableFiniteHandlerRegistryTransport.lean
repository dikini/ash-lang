import CoreCallableFiniteHandlerRegistryCoverage
import CoreCallableFiniteRegistryBridge
namespace Ash.OneShot.CoreCallableFiniteHandlerRegistryTransport
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract Environment sequenceRows choiceRows)
open CoreCallableContractRegistries (Owners OwnerContract)
open CoreCallableContractAdmission CoreCallableStaticProducer CoreCallableFiniteClauseTemplate CoreCallableFiniteHandlerSource
open CoreCallableFiniteCellRegistry (CellApi)
open CoreCallableReceiverRefinement (LexicalBounds)
open SourceDeclarationPlans (Plan ModePlans ClausePlans)
open SourceDependencyAnnotations (Dependencies ClauseDependencies)
open SourcePlanSignatures (signature modeSignatures clauseSignatures)
open SourceScheduledCleanupInterfaces.Lexical.Recursive
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
local instance : SourcePlannedChecks.DeclarationPolicy := declarationPolicy

/-- Structural stable-operand reconstruction preserves opaque full slots. -/
theorem pure_transfer (data : Pure bindings code annotatedContract)
    {demand : List Nat} {requirements : RecursiveRequirements.Requirements demand}
    {dependencies : Dependencies} {plan : Plan dependencies} {rows : Rows (signature plan)}
    {source : IndexedSource (registry entries policy) outward owners world allowed scope valueEnvironment
      code contract demand requirements plan rows}
    (auth : Authenticated (registry entries policy) outward source lexical receiver) :
    ∃ next : IndexedSource (CoreCallableFiniteCellRegistry.registry (some api) entries policy) outward owners world allowed scope
      valueEnvironment code contract demand requirements plan rows,
      Authenticated (CoreCallableFiniteCellRegistry.registry (some api) entries policy) outward next lexical receiver := by
  induction data generalizing owners scope demand dependencies valueEnvironment contract with
  | unit =>
      cases auth with | checked bounds hereditary =>
        cases hereditary
        exact ⟨.unit,.checked bounds .unit⟩
  | boolean =>
      cases auth with | checked bounds hereditary =>
        cases hereditary
        exact ⟨.boolean,.checked bounds .boolean⟩
  | integer =>
      cases auth with | checked bounds hereditary =>
        cases hereditary
        exact ⟨.integer,.checked bounds .integer⟩
  | «variable» reference =>
      cases auth with | checked bounds hereditary =>
        cases hereditary with | «variable» knownSupport =>
          exact ⟨.variable (by assumption) (by assumption),.checked bounds (.variable (known := by assumption) (formed := by assumption) knownSupport)⟩
  | pair left right ihL ihR =>
      cases auth with | checked bounds hereditary =>
        cases hereditary with
        | purePair a b =>
          obtain ⟨l,la⟩ := ihL a
          obtain ⟨r,ra⟩ := ihR b
          exact ⟨.purePair l r,.checked bounds (.purePair la ra)⟩
        | pair a b =>
          obtain ⟨l,la⟩ := ihL a
          obtain ⟨r,ra⟩ := ihR b
          exact ⟨.pair l r,.checked bounds (.pair la ra)⟩

/-- Reconstruct only the supported finite clause grammar. No operation lookup
or future-receiver proof is required for its pure prefixes and current resume. -/
theorem template_transfer (data : Template input answer binder bindings code)
    (supported : data.supported = true)
    {demand : List Nat} {requirements : RecursiveRequirements.Requirements demand}
    {dependencies : Dependencies} {plan : Plan dependencies} {rows : Rows (signature plan)}
    {source : IndexedSource (registry entries policy) outward owners world allowed scope valueEnvironment
      code answer demand requirements plan rows}
    (auth : Authenticated (registry entries policy) outward source lexical receiver) :
    ∃ next : IndexedSource (CoreCallableFiniteCellRegistry.registry (some api) entries policy) outward owners world allowed scope
      valueEnvironment code answer demand requirements plan rows,
      Authenticated (CoreCallableFiniteCellRegistry.registry (some api) entries policy) outward next lexical receiver := by
  induction data generalizing lexical demand dependencies valueEnvironment with
  | unsupported reason => cases supported
  | resume operand =>
      cases auth with | checked bounds hereditary =>
        cases hereditary with | resume value =>
          obtain ⟨v,va⟩ := pure_transfer operand value
          exact ⟨.resume (by assumption) (by assumption) (by assumption) v (by assumption) (by assumption),
            .checked bounds (.resume (known := by assumption) (resolved := by assumption)
              (permission := by assumption) (admitted := by assumption) (formed := by assumption) va)⟩
  | bind initial body ih =>
      cases auth with | checked bounds hereditary =>
        cases hereditary with | bind a b =>
          obtain ⟨v,va⟩ := pure_transfer initial a
          obtain ⟨r,ra⟩ := ih supported b
          exact ⟨.bind v r,.checked bounds (.bind va ra)⟩
  | branch condition yes no ihY ihN =>
      obtain ⟨y,n⟩ : yes.supported = true ∧ no.supported = true := by
        simpa only [Template.supported,Bool.and_eq_true] using supported
      cases auth with | checked bounds hereditary =>
        cases hereditary with | branch c a b =>
          obtain ⟨v,va⟩ := pure_transfer condition c
          obtain ⟨r,ra⟩ := ihY y a
          obtain ⟨t,ta⟩ := ihN n b
          exact ⟨.branch v r t (by assumption),.checked bounds (.branch (sameDemand := by assumption) va ra ta)⟩

structure TargetSpecialization (api : CellApi) (entries : OperationEntries) (policy : Syntax.TicketPolicy)
    (outward : List Instance) (owners : Owners) (world : List Nat) (allowed : List Instance)
    (data : Template input answer binder bindings code) (owner : Nat) (contract : OwnerContract)
    (lexical : LexicalBounds) (receiver : List Nat) : Type where
  source : IndexedSource (CoreCallableFiniteCellRegistry.registry (some api) entries policy) outward
    (owners.insert owner contract) world allowed (.ticket binder owner) (environment bindings) code answer
    (data.demand owner contract) (data.requirements owner contract) (data.plan owner) (data.rows owner)
  authenticated : Authenticated (CoreCallableFiniteCellRegistry.registry (some api) entries policy) outward source lexical receiver

def specialize (data : Template input answer binder bindings code) (supported : data.supported = true)
    (checked : Receipt entries policy outward owners world allowed data lexical receiver)
    (owner : Nat) (contract : OwnerContract) (a : contract.input = input) (b : contract.answer = answer)
    (c : contract.resumeEffects = allowed) :
    TargetSpecialization api entries policy outward owners world allowed data owner contract lexical receiver := by
  let original := checked.specialize owner contract a b c
  have produced := template_transfer (api := api) data supported original.authenticated
  exact ⟨Classical.choose produced,Classical.choose_spec produced⟩

structure TargetMode (api : CellApi) (entries : OperationEntries) (policy : Syntax.TicketPolicy)
    (outward : List Instance) (owners : Owners) (world : List Nat) (allowed : List Instance)
    (data : Template input answer binder ((parameter,argument) :: bindings) code)
    (resumeEffects closeEffects : List Instance) (held : Bool) (offered : Option Footprint)
    (lexical : LexicalBounds) (receiver : List Nat) : Type where
  source : SourceOffer (CoreCallableFiniteCellRegistry.registry (some api) entries policy) outward owners world
    (environment bindings) allowed parameter binder argument input answer resumeEffects closeEffects code held false offered
    (modePlan data offered) (modeRows data offered)
  authenticated : OfferAuthentication (CoreCallableFiniteCellRegistry.registry (some api) entries policy) outward source lexical receiver

/-- Original finite checks run internally; all-owner source families are output. -/
def checkTargetMode (api : CellApi)
    (data : Template input answer binder ((parameter,argument) :: bindings) code)
    (offered : Option Footprint) (entries : OperationEntries) (policy : Syntax.TicketPolicy)
    (outward : List Instance) (owners : Owners) (world : List Nat) (allowed resumeEffects closeEffects : List Instance)
    (held : Bool) (lexical : LexicalBounds) (receiver : List Nat) :
    Except Error (TargetMode api entries policy outward owners world allowed data resumeEffects closeEffects held offered lexical receiver) :=
  match offered with
  | none => .ok ⟨.unavailable,.unavailable⟩
  | some row => do
    if supported : data.supported = true then
      if same : resumeEffects = allowed then
        if noDispose : code.requiredActions.dispose = false then
          let checked ← data.check entries policy outward owners world allowed lexical receiver
          let bodies := fun owner contract (a : contract.input = input) (b : contract.answer = answer)
              (c : contract.resumeEffects = resumeEffects) (_d : contract.closeEffects = closeEffects)
              (_e : contract.held = held) (_balanced : contract.closeDemand.Perm contract.resumeDemand) =>
            SourceBody.typed (specialize (api := api) data supported checked owner contract a b (c.trans same)).source
              (data.normal owner contract false row) (data.protectedRows owner contract false row)
          let resumeInterface := fun (_required : code.requiredActions.resume = true) => same
          let closeInterface := fun (required : code.requiredActions.dispose = true) => by
            rw [noDispose] at required
            cases required
          .ok ⟨SourceOffer.available resumeInterface closeInterface bodies,
            .available (bodySource := bodies) resumeInterface closeInterface
              (fun owner contract a b c _d _e _balanced =>
                .typed (normal := data.normal owner contract false row)
                  (closing := data.protectedRows owner contract false row)
                  (specialize (api := api) data supported checked owner contract a b (c.trans same)).authenticated)⟩
        else .error .capability
      else .error .unavailableEffect
    else .error (.unsupported "clause template")

structure TargetDeclarations (api : CellApi) (entries : OperationEntries) (policy : Syntax.TicketPolicy)
    (outward : List Instance) (owners : Owners) (world : List Nat) (allowed : List Instance)
    (data : Declarations entries requested answer bindings clauses) (lexical : LexicalBounds) (receiver : List Nat) : Type where
  source : SourceDeclarations (CoreCallableFiniteCellRegistry.registry (some api) entries policy) outward owners world
    (environment bindings) allowed requested answer clauses data.table data.plans data.rows
  authenticated : DeclarationAuthentication (CoreCallableFiniteCellRegistry.registry (some api) entries policy) outward source lexical receiver

/-- Internal reconstruction consumes only provenance computed by the original
finite declaration check. Literal support leaves and both modes stay exact. -/
def rebuild (api : CellApi) (data : Declarations entries requested answer bindings clauses)
    (policy : Syntax.TicketPolicy) (outward : List Instance) (owners : Owners) (world : List Nat) (allowed : List Instance)
    (lexical : LexicalBounds) (receiver : List Nat)
    (compatible : CoreCallableFiniteRegistryCompatibility.compatible api entries = true)
    (bounds : data.currentBounds lexical receiver) :
    Except Error (TargetDeclarations api entries policy outward owners world allowed data lexical receiver) :=
  match data with
  | .nil => .ok ⟨.nil,.nil⟩
  | .cons (parameter := parameter) _reference body supportBound ordinary protectedMode resumeEffects closeEffects rest => do
      let a ← checkTargetMode api body ordinary entries policy outward owners world allowed resumeEffects closeEffects false (lexical.extend parameter receiver) receiver
      let b ← checkTargetMode api body protectedMode entries policy outward owners world allowed resumeEffects closeEffects true (lexical.extend parameter receiver) receiver
      let tail ← rebuild api rest policy outward owners world allowed lexical receiver compatible bounds.2.2.2
      let known := CoreCallableFiniteRegistryCompatibility.selected_lookup_preserved (policy := policy) compatible bounds.1
      .ok ⟨.cons supportBound known a.source b.source tail.source,
        .cons known bounds.2.1 bounds.2.2.1 a.authenticated b.authenticated tail.authenticated⟩

structure Result (api : CellApi) (entries : OperationEntries) (policy : Syntax.TicketPolicy)
    (outward : List Instance) (owners : Owners) (world : List Nat) (allowed : List Instance)
    (data : Declarations entries requested answer bindings clauses) (lexical : LexicalBounds) (receiver : List Nat) : Type where
  original : CurrentDeclarationReceipt entries policy outward owners world allowed data lexical receiver
  target : TargetDeclarations api entries policy outward owners world allowed data lexical receiver
  coverage : CoreCallableFiniteHandlerRegistryCoverage.CoverageReceipt api entries policy requested clauses

inductive CheckError where
  | coverage : CoreCallableFiniteHandlerRegistryCoverage.Error → CheckError
  | declaration : CoreCallableStaticProducer.Error → CheckError
  deriving Repr

/-- No Source/Auth or success-family is an input. This executes original
current declaration checking and full interpreted target coverage. -/
def check (api : CellApi) (data : Declarations entries requested answer bindings clauses)
    (policy : Syntax.TicketPolicy) (outward : List Instance) (owners : Owners) (world : List Nat) (allowed : List Instance)
    (lexical : LexicalBounds) (receiver : List Nat) :
    Except CheckError (Result api entries policy outward owners world allowed data lexical receiver) := do
  let covered ← (CoreCallableFiniteHandlerRegistryCoverage.check api entries policy requested clauses).mapError CheckError.coverage
  let original ← (checkCurrentDeclarations data policy outward owners world allowed lexical receiver).mapError CheckError.declaration
  let target ← (rebuild api data policy outward owners world allowed lexical receiver covered.down.compatibility original.bounds).mapError CheckError.declaration
  .ok ⟨original,target,covered.down⟩

#print axioms pure_transfer
#print axioms template_transfer
#print axioms specialize
#print axioms checkTargetMode
#print axioms rebuild
#print axioms check
end Ash.OneShot.CoreCallableFiniteHandlerRegistryTransport
