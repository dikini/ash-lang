import SourceAnnotatedStoredRegistries
import SourceBoundHandlerAdmission
import SourceAnnotatedRuntimeState

/-! The runtime invariant retains joint source typing at the actual installed
packet stack. It projects to the existing state, preserving all current source,
ownership, scheduling, callback and completion checks. -/
namespace Ash.OneShot.SourceAnnotatedRuntimeState
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Operations Contracts Value)
open SourceAnnotatedSources (Expression)
open SourceAnnotatedCode (Term)
open SourceDependencyAnnotations (Dependencies)
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceRetainedPlans (Forest)
open SourceScheduledSavedPlans (Annotations)
open SourcePlannedFrames (DeclarationEvidence recipeEvidence)
open SourceConsumingStoredBounds (StackBounds)

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]

inductive AtPackets [admission : SourceScheduledChecks.DeclarationPolicy] [certification : SourcePlannedChecks.DeclarationPolicy] (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (families : SourceDependencyFrames.Families)
    (required : SourceContextualRechecking.Required) (actions : Syntax.UsageTickets) (annotations : Annotations)
    (world : List Nat) (outward : List Instance) (outside : ProtectionContracts.Context)
    (scope : Execution.Scope) (code : Term) (stack : SourceAnnotatedRuntime.Stack)
    {dependencies : Dependencies} (plan : Plan dependencies)
    {receiving : SourceDependencyCapture.Scope} {hints : SourceContextualHints.Hints receiving} (forest : Forest hints)
    (output : Value) (demand : List Nat) (row : Footprint) (stored : StackBounds families stack)
    (evidence : DeclarationEvidence := recipeEvidence) : Prop where
  | checked
      (current : Expression operations policy contracts world allowed scope (fun _ => none)
        code input currentDemand currentRequirements (signature plan))
      (scopeTyped : ScopedPorts.EffectScope contracts.erase.erase.ports scope ticket)
      (pending : SourceAnnotatedStoredTyping.Segment (evidence := evidence) operations policy contracts tables families required actions outward
        (OwnerPhaseTransitions.available (ownedTickets stack.erase)) world
        stack input output pendingDemand pendingRequirements resumes forest .nil allowed [] stored)
      (closing : DeclaredSourceClosing.Records operations.erase.erase policy contracts.erase.erase tables world stack.erase disposals)
      (templates : SourceAnnotatedClosingRecords.Records operations policy contracts tables annotations world stack disposals)
      (matched : SourceScheduledSavedPlans.Matches annotations forest)
      (contextual : SourceScheduledChecks.Local outward actions (OwnerPhaseTransitions.available (ownedTickets stack.erase)) world plan forest)
      (unique : (ownedTickets stack.erase).Nodup)
      (evaluated : RecursiveRequirements.Checked (resumes ++ disposals) [] (OwnerPhaseTransitions.available (ownedTickets stack.erase))
        (.sequence (currentRequirements.prepend (OwnerPhases.ofStack tables stack.erase)) pendingRequirements) row)
      (accepted : checkFootprint outside row = true)
      (accounting : demand = currentDemand ++ pendingDemand) :
      AtPackets operations policy contracts tables families required actions annotations world outward outside scope code stack plan forest output demand row stored evidence


/-- The stronger state reuses the original source, owner and closing invariant. -/
theorem AtPackets.atPlan
    (state : AtPackets operations policy contracts tables families required actions annotations world outward outside
      scope code stack plan forest output demand row stored evidence) :
    AtPlan operations policy contracts tables families required actions annotations world outward outside
      scope code stack plan forest output demand row evidence := by
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting =>
      exact .checked current scopeTyped pending.forget closing templates matched contextual unique evaluated accepted accounting

/-- An empty pending stack has no installed declaration packets to authenticate. -/
theorem AtPlan.empty_packets
    (state : AtPlan operations policy contracts tables families required actions annotations world outward outside
      scope code .nil plan forest output demand row evidence) :
    AtPackets operations policy contracts tables families required actions annotations world outward outside
      scope code .nil plan forest output demand row .nil evidence := by
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting =>
      cases pending with
      | nil bound =>
        exact .checked current scopeTyped (.nil bound) closing templates matched contextual unique evaluated accepted accounting

end Ash.OneShot.SourceAnnotatedRuntimeState

namespace Ash.OneShot.SourceConsumingStoredBounds
open SourceScheduledHandlers (register)

/-- Installation transports existing declaration evidence at the recorded plan. -/
theorem HandlerBounds.installed_evidence (handler : SourceAnnotatedRuntime.Handler)
    (plans : SourceDeclarationPlans.ClausePlans handler.clauses.erase clauseFamilies)
    (bounds : SourceConsumingClauseAnnotations.ClauseBounds plans) (route : DeclarationRoute)
    (checked : evidence needed plans) :
    (evidence : SourcePlannedFrames.DeclarationEvidence) needed
      (HandlerBounds.installed (families := families) handler plans bounds route).plans := by
  exact HandlerBounds.registries_congr_evidence
    (show HandlerBounds (fun _ => clauseFamilies) handler from ⟨plans, bounds, route⟩)
    (by simp only [register, SourceAnnotatedRuntime.Handler.erase, if_true]) checked

end Ash.OneShot.SourceConsumingStoredBounds

namespace Ash.OneShot.SourcePlanBounds
open SourceDeclarationPlans (Plan ClausePlans)

theorem Annotation.handlerPacket_evidence (handler : SourceAnnotatedRuntime.Handler)
    {checking : ClausePlans checkingClauses clauseFamilies} {body : Plan dependencies}
    (bounds : Annotation world (.handler (effect := effect) (table := table) required checking body))
    (actual : ClausePlans handler.clauses.erase clauseFamilies)
    (checked : evidence needed actual) :
    (evidence : SourcePlannedFrames.DeclarationEvidence) needed
      (bounds.handlerPacket (families := families) handler actual).plans := by
  unfold Annotation.handlerPacket
  cases bounds.handlerBounds <;> exact SourceConsumingStoredBounds.HandlerBounds.installed_evidence handler actual _ _ checked

end Ash.OneShot.SourcePlanBounds

namespace Ash.OneShot.SourceBoundSnapshots
open SourceDeclarationPlans (ClausePlans)
open SourceConsumingStoredBounds (HandlerBounds)
open SourceScheduledHandlers (register)

theorem HandlerPacketFrom.evidence {evidence : SourcePlannedFrames.DeclarationEvidence} {before : Snapshot world}
    {actual : ClausePlans handler.clauses.erase clauseFamilies}
    {packet : HandlerBounds (register families handler.activation clauseFamilies) handler}
    (origin : HandlerPacketFrom handler table required actual before packet)
    (checked : evidence needed actual) :
    (evidence : SourcePlannedFrames.DeclarationEvidence) needed packet.plans := by
  cases origin with
  | step bounds remaining same => exact bounds.handlerPacket_evidence handler actual checked

theorem HandlerPacketFrom.admitted [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]
    (transport : ∀ {before after families required}
      {first : ClausePlans before families} {second : ClausePlans after families},
      nested.accepts required first → SourcePlanSignatures.clauseSignatures first = SourcePlanSignatures.clauseSignatures second →
        nested.accepts required second)
    {before : Snapshot world} {actual : ClausePlans handler.clauses.erase clauseFamilies}
    {packet : HandlerBounds (register families handler.activation clauseFamilies) handler}
    (origin : HandlerPacketFrom handler table required actual before packet)
    (admitted : before.Admitted) :
    packet.Admitted world (register requirements handler.activation required) := by
  cases origin with
  | step bounds remaining same => exact admitted.1.handler_packet transport handler actual same

end Ash.OneShot.SourceBoundSnapshots

#print axioms Ash.OneShot.SourceAnnotatedRuntimeState.AtPackets.atPlan
#print axioms Ash.OneShot.SourceConsumingStoredBounds.HandlerBounds.installed_evidence
#print axioms Ash.OneShot.SourcePlanBounds.Annotation.handlerPacket_evidence
#print axioms Ash.OneShot.SourceBoundSnapshots.HandlerPacketFrom.evidence
#print axioms Ash.OneShot.SourceBoundSnapshots.HandlerPacketFrom.admitted

#print axioms Ash.OneShot.SourceAnnotatedRuntimeState.AtPlan.empty_packets
