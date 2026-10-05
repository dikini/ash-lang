import CoreCallableRichRegistryOrigins
import CoreCallableRichContextTicketDomain
import CoreCallableContractCaptureConnection

/-! Source-only C3 increment: derive actual counter freshness from registry
origins and the same full rich Site, then retain the existing capture result.
This is not Core CaptureInput selection synchronization or Core-event closure. -/
namespace Ash.OneShot.CoreCallableRichCaptureOrigin
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceDependencyAnnotations (Dependencies)
open SourceScheduledCleanupInterfaces.Lexical.Recursive
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourceDependencyChecks.Lexical (ReturnHints)
open CoreCallableContractRegistries (OwnerContract)
open CoreCallableContractAdmission
open CoreCallableContractExecution (Site)
open CoreCallableGeneratedChronology
open CoreCallableRichAdmittedCurrentOrigins (Current)
open CoreCallableRichRegistryOrigins (RegistryOrigin)
open SourcePlannedChecks (DeclarationPolicy)

section
variable [evidence : DeclarationPolicy]

/-- The same current Site and retained registry origin provide all three
freshness premises of the rich capture consumer at the actual Core counter. -/
theorem current_counter_fresh
    (site : Site globals outward world allowed actions phases budget ambient installations
      expression runtimeScope stack result final context root)
    (current : Current program endpoint site)
    (origin : RegistryOrigin program current.input endpoint globals.owners actions) :
    globals.owners endpoint.state.nextOwner = none ∧
      actions endpoint.state.nextOwner = none ∧
      endpoint.state.nextOwner ∉ context.ticketNames := by
  refine ⟨origin.owner_fresh, origin.action_fresh, ?_⟩
  intro present
  obtain ⟨contract, known⟩ := CoreCallableRichContextTicketDomain.site_ticket_domain site
    endpoint.state.nextOwner present
  rw [origin.owner_fresh] at known
  cases known

/-- Preserve the full existing rich capture existential, private family, Plans,
Rows, accounting and RawStep; derive its freshness at the current counter.
The added origin continuation inserts this selected full contract and code rights;
it does not synchronize a supplied current CaptureInput with rich selection. -/
theorem capture_at_actual_counter
    {receiving : SourceDependencyCapture.Scope} {hints : ReturnHints receiving} {context : Context hints}
    (stable : SubstitutionPolicyStable outward)
    (site : CoreCallableContractExecution.Site globals outward world allowed actions phases budget ambient installations
      (.perform (Instantiation.freezeEffect requested) operation operand) runtimeScope whole result final context root)
    (current : Current program endpoint site)
    (origin : RegistryOrigin program current.input endpoint globals.owners actions)
    (closed : ClosedValue operand)
    (physical : HandlerCut requested whole cap tail handler)
    (ready : ∀ parameter binder code, ClauseAt operation handler.clauses parameter binder code → ClosedExcept parameter code)
    (checkedRequest : CorePayloadReceiver.CheckedRequest requestTable requestPort)
    (origins : CorePayloadReceiver.ActivationOrigins)
    (dependencies : ∀ identity, identity ∈ ScopedPorts.Support.evaluate ScopedPorts.Support.empty operand.dependencies →
      identity ∉ ambient → ∃ origin, CorePayloadReceiver.originAt origins identity = some origin ∧
        origin ∈ checkedRequest.record.dependencyOrigins)
    (crossed : CorePayloadReceiver.CapturedRealizes checkedRequest origins cap ambient)
    (resumeDemand : List Nat) (resumeRow : Footprint) (closeRow : Option Footprint) :
    ∃ captured outside : Packed,
    ∃ answer residual parameter binder code resumeEffects closeEffects,
    ∃ family : Nat → Dependencies, ∃ bodies : ∀ localOwner, Plan (family localOwner),
    ∃ bodyRows : ∀ localOwner, Rows (signature (bodies localOwner)),
    let allocated : OwnerContract := ⟨result, answer, captured.scope.held, resumeDemand, resumeRow,
      resumeDemand, closeRow, resumeEffects, closeEffects⟩
    ∃ nextDemand, ∃ nextRoot : RecursiveRequirements.Requirements nextDemand,
    ∃ next : CoreCallableContractExecution.Site (globals.withOwner endpoint.state.nextOwner allocated) outward world residual
      (actions.insert endpoint.state.nextOwner code.requiredActions) (OwnerPhaseTransitions.introduce phases endpoint.state.nextOwner) budget ambient installations
      (code.subst parameter operand) (.ticket binder endpoint.state.nextOwner)
      (.live endpoint.state.nextOwner (CoreCallableContractExecution.runtimeType result) handler.answer cap handler.scope tail)
      answer final (Context.live (owner := endpoint.state.nextOwner) (resumeDemand := resumeDemand) captured.context outside.context) nextRoot,
      ClauseAt operation handler.clauses parameter binder code ∧
      SourceDependencyChecks.Lexical.Capture receiving requested operation ∧
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, runtimeScope, whole⟩
        ⟨code.subst parameter operand, .ticket binder endpoint.state.nextOwner,
          .live endpoint.state.nextOwner (CoreCallableContractExecution.runtimeType result) handler.answer cap handler.scope tail⟩ [.ticket endpoint.state.nextOwner] [] ∧
      next.dependencies = family endpoint.state.nextOwner ∧
      HEq next.plan (CoreCallablePlanSubstitution.plan code (bodies endpoint.state.nextOwner) parameter operand) ∧
      HEq (signature next.plan) (signature (bodies endpoint.state.nextOwner)) ∧ HEq next.rows (bodyRows endpoint.state.nextOwner) ∧
      ∀ input : CaptureInput endpoint,
        RegistryOrigin program current.input (capture_result input).after
          (globals.owners.insert endpoint.state.nextOwner allocated)
          (actions.insert endpoint.state.nextOwner code.requiredActions) := by
  obtain ⟨freshOwner, freshAction, absent⟩ := current_counter_fresh site current origin
  obtain ⟨captured, outside, answer, residual, parameter, binder, code, resumeEffects,
    closeEffects, family, bodies, bodyRows, nextDemand, nextRoot, next, located, guarded,
    step, exactDependencies, exactPlan, exactSignature, exactRows⟩ :=
    CoreCallableContractCaptureConnection.capture stable site closed physical ready
      checkedRequest origins dependencies crossed endpoint.state.nextOwner freshOwner freshAction
      absent resumeDemand resumeRow closeRow
  exact ⟨captured, outside, answer, residual, parameter, binder, code, resumeEffects,
    closeEffects, family, bodies, bodyRows, nextDemand, nextRoot, next, located, guarded,
    step, exactDependencies, exactPlan, exactSignature, exactRows,
    fun input => origin.capture_insert input _ code.requiredActions⟩

end
#check current_counter_fresh
#check capture_at_actual_counter
#print axioms current_counter_fresh
#print axioms capture_at_actual_counter
end Ash.OneShot.CoreCallableRichCaptureOrigin
