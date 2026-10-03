import CoreCallableSelectedDomainDeclarationTransfer
import CoreCallableContractCaptureConnection
namespace Ash.OneShot.CoreCallableDomainHandlerAuthentication
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract Environment)
open CoreCallableContractRegistries (Owners Registry)
open CoreCallableContractAdmission CoreCallableStaticProducer CoreCallableFiniteHandlerSource
open CoreCallableClauseActualSupport CoreCallableSelectedDomainDeclarationTransfer
open CoreCallableReceiverRefinement (LexicalBounds)
open SourceDeclarationPlans (Plan ClausePlans)
open SourcePlanSignatures (signature clauseSignatures)
open SourceScheduledCleanupInterfaces.Lexical.Recursive
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
local instance : SourcePlannedChecks.DeclarationPolicy := declarationPolicy

/-- Selection changes one formal domain; all other formals remain conservative.
Both modes and every owner-indexed private source stay in the same full indices. -/
theorem DeclarationAuthenticationAt.selected_domain
    {registry : Registry} {environment : Environment}
    {source : SourceDeclarations registry outward owners world environment allowed requested answer clauses table plans rows}
    (authenticated : DeclarationAuthenticationAt registry outward source lexical receiver
      (selected clauses operation (CoreCallableContractOperandDomain.domainSupport argument receiver) receiver))
    (selectedKnown : registry.operations requested operation = some (argument,input)) :
    DomainDeclarationAuthentication registry outward source lexical receiver := by
  generalize same : selected clauses operation (CoreCallableContractOperandDomain.domainSupport argument receiver) receiver = assignment at authenticated
  induction authenticated with
  | nil => exact .domainNil
  | cons known bounded received stored ordinary protectedMode rest ih =>
    simp only [selected] at same
    cases same
    apply DomainDeclarationAuthentication.domainCons known ?_ received bounded stored ordinary protectedMode (ih selectedKnown rfl)
    rename_i key supportBound currentReceiver currentLexical currentEnvironment ordinarySource protectedSource restSource
    by_cases equal : key = operation
    · subst key
      have contracts := Prod.mk.inj (Option.some.inj (known.symm.trans selectedKnown))
      rw [contracts.1]
      simp
    · simpa only [if_neg equal] using CoreCallableContractOperandDomain.domainSupport_received

/-- The static prerequisite supplies the missing generic declaration input. -/
theorem SelectedDomainReceipt.domain_authentication
    {reference : OperationRef entries requested operation argument input}
    {data : Declarations entries requested answer bindings clauses}
    (initial : SelectedDomainReceipt reference api held data policy outward owners world allowed lexical receiver) :
    DomainDeclarationAuthentication (registry entries policy) outward initial.receiving.checked.source lexical receiver := by
  exact DeclarationAuthenticationAt.selected_domain initial.receiving.checked.authenticated initial.known

/-- The new kernel case consumes actual checked body and domain declarations;
it retains the original full handler source, coverage, modes and recipes. -/
theorem handler_authentication
    {registry : Registry} {environment : Environment}
    {bodySource : IndexedSource registry outward owners world (effect :: residual) scope environment
      code answer demand requirements bodyPlan bodyRows}
    {declarationSource : SourceDeclarations registry outward owners world environment residual effect answer arms table plans declarationRows}
    (clauses : ScopedPorts.ClausesTyped registry.ports world environment.ports effect answer.port residual arms)
    (capabilities : ClausesUse registry.policy arms)
    (coverage : ScopedPorts.Covers registry.ports effect arms)
    (unique : (ScopedTyping.clauseKeys arms).Nodup) (admitted : residual ⊆ allowed)
    (modes : SourceTemplates.ClauseModes arms table)
    (recipes : declarationPolicy.accepts outward required plans)
    (body : Authenticated registry outward bodySource lexical receiver)
    (declarations : DomainDeclarationAuthentication registry outward declarationSource lexical receiver)
    (bounded : SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.Bounds lexical.environment
      (Code.handle (Instantiation.freezeEffect effect) code arms).dependencies receiver) :
    Authenticated registry outward
      (IndexedSource.handler bodySource clauses capabilities coverage unique admitted table modes declarationSource recipes)
      lexical receiver :=
  .checked bounded (.handlerDomain clauses capabilities coverage unique admitted modes recipes body declarations)

/-- Successful static acceptance installs domain evidence over its SAME original
source/table/full private rows; it never manufactures whole-before evidence. -/
theorem SelectedDomainReceipt.installed_source
    {reference : OperationRef entries handler.effectInst operation argument input}
    {data : Declarations entries handler.effectInst answer [] handler.clauses}
    (initial : SelectedDomainReceipt reference api held data policy outward owners world allowed lexical receiver)
    (_accepted : checkSelectedDomainDeclarations reference api held data policy outward owners world allowed lexical receiver = .ok initial)
    (empty : lexical.environment = ScopedPorts.Support.empty)
    (annotation : ScopedPorts.eraseType handler.answer = answer.port) :
    CoreCallableContractExecution.HandlerSource ⟨operations entries,policy,owners⟩ outward world allowed handler answer
      data.table data.plans data.rows receiver := by
  apply CoreCallableContractExecution.HandlerSource.of_domain (globals := ⟨operations entries,policy,owners⟩) annotation initial.receiving.checked.modes initial.receiving.checked.source
  exact ⟨lexical,empty,SelectedDomainReceipt.domain_authentication initial⟩

#print axioms DeclarationAuthenticationAt.selected_domain
#print axioms SelectedDomainReceipt.domain_authentication
#print axioms handler_authentication
#print axioms SelectedDomainReceipt.installed_source
end Ash.OneShot.CoreCallableDomainHandlerAuthentication
