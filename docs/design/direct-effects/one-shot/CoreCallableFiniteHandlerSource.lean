import CoreCallableFiniteHandlerDeclarations
import CoreCallableStaticProducer
import CoreCallableRestoredSupport
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

structure HandlerReceipt (entries : OperationEntries) (policy : Syntax.TicketPolicy)
    (outward : List Instance) (owners : Owners) (world : List Nat) (allowed residual : List Instance)
    (scope : Execution.Scope) (bindings : Bindings) (code : Code) (answer : Contract)
    (demand : List Nat) (requirements : RecursiveRequirements.Requirements demand)
    {dependencies : Dependencies} (bodyPlan : Plan dependencies) (bodyRows : Rows (signature bodyPlan))
    (data : Declarations entries requested answer bindings clauses) (lexical : LexicalBounds) (receiver : List Nat) : Type where
  source : IndexedSource (registry entries policy) outward owners world allowed scope (environment bindings)
    (.handle (Instantiation.freezeEffect requested) code clauses) answer demand
    (requirements.prepend [.ordinary (.handler requested 0 data.table)])
    (.handler (effect := requested) (table := data.table) [] data.plans bodyPlan)
    (by simpa only [signature] using (@Rows.handler data.families (clauseSignatures data.plans) _ (signature bodyPlan)
      requested data.table [] data.rows bodyRows))
  authenticated : Authenticated (registry entries policy) outward source lexical receiver

/-- SAME checked body and finite original declarations. Coverage is checked
against the entire exact original operation registry, not requested ports only. -/
def check (annotation : Annotation entries owners bindings code answer demand requirements bodyPlan bodyRows)
    (data : Declarations entries requested answer bindings clauses) (policy : Syntax.TicketPolicy)
    (outward : List Instance) (world : List Nat) (allowed residual : List Instance) (scope : Execution.Scope)
    (lexical : LexicalBounds) (receiver : List Nat) :
    Except Error (HandlerReceipt entries policy outward owners world allowed residual scope bindings code answer demand requirements bodyPlan bodyRows data lexical receiver) := do
  let declarations ← checkDeclarations data policy outward owners world residual lexical receiver
  if _exactKeys : clauseKeysCheck entries requested clauses = true then
   if covered : CoreCallableGraphAnnotationChecks.subsetB (operationKeys entries requested) (ScopedTyping.clauseKeys clauses) = true then
     if unique : (ScopedTyping.clauseKeys clauses).Nodup then
       if admitted : CoreCallableGraphAnnotationChecks.subsetB residual allowed = true then
         let body ← CoreCallableStaticProducer.check annotation policy outward world (requested :: residual) scope lexical receiver
         let cover := coverage_from_keys (policy := policy) covered
         let permitted := CoreCallableGraphAnnotationChecks.subsetB_sound admitted
         let source := IndexedSource.handler body.source declarations.typed declarations.capabilities cover unique permitted
           data.table declarations.modes declarations.source declarations.recipes
         if bounded : CoreCallableGraphAnnotationChecks.subsetB
             (ScopedPorts.Support.evaluate lexical.environment
               (Code.handle (Instantiation.freezeEffect requested) code clauses).dependencies) receiver = true then
           .ok ⟨source,.checked (SourceSupport.bounds_iff.mpr (CoreCallableGraphAnnotationChecks.subsetB_sound bounded))
             (.handler declarations.typed declarations.capabilities cover unique permitted declarations.modes declarations.recipes
               body.authenticated declarations.authenticated)⟩
         else .error .support
       else .error .unavailableEffect
     else .error (.unsupported "duplicate operation clause")
   else .error (.unsupported "missing operation clause")
  else .error (.unsupported "clause coverage/uniqueness")


/-- World transport uses the ACTUAL checked handler source/authentication at
fixed lexical receiver. No restored rows or future receiver is substituted. -/
theorem HandlerReceipt.world_weaken_current
    {requested : Instance} {clauses : Clauses} {dependencies : Dependencies}
    {bodyPlan : Plan dependencies} {bodyRows : Rows (signature bodyPlan)}
    {data : Declarations entries requested answer bindings clauses}
    (checked : HandlerReceipt entries policy outward owners world allowed residual scope bindings code answer
      demand requirements bodyPlan bodyRows data lexical receiver)
    (larger : world ⊆ nextWorld) :
    ∃ nextSource : IndexedSource (registry entries policy) outward owners nextWorld allowed scope (environment bindings)
      (.handle (Instantiation.freezeEffect requested) code clauses) answer demand
      (requirements.prepend [.ordinary (.handler requested 0 data.table)])
      (.handler (effect := requested) (table := data.table) [] data.plans bodyPlan)
      (by simpa only [signature] using (@Rows.handler data.families (clauseSignatures data.plans) _ (signature bodyPlan)
        requested data.table [] data.rows bodyRows)),
      Authenticated (registry entries policy) outward nextSource lexical receiver :=
  ⟨checked.source.world_weaken larger,checked.authenticated.world_weaken larger⟩

#print axioms HandlerReceipt.world_weaken_current

#print axioms checkOffer
#print axioms checkMode
#print axioms Declarations.plans
#print axioms Declarations.rows
#print axioms checkDeclarations
#print axioms check
#print axioms clauseKeysCheck
end Ash.OneShot.CoreCallableFiniteHandlerSource
