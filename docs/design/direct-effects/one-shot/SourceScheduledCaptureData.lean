import SourceScheduledInterfaces
import SourceScheduledSavedPlans

/-! The shared allocator retains joint source witnesses at its exact requirement
indices. Rebuilding the live segment uses fresh registry/phase transport and the
same refined answer as the selected clause, not equality inferred after erasure. -/
namespace Ash.OneShot.SourceScheduledCaptureData

variable [admission : SourceScheduledChecks.DeclarationPolicy] [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Value Operations Contracts)
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceContextualHints (Hints)
open SourceContextualHintChecking (Matches)
open SourceScheduledChecks (Local)
open SourceRetainedPlans (Forest)
open SourceScheduledSavedPlans (Annotations)
open SourceScheduledFrames (Segment)
open SourcePlannedSources (Body ValueSummary refineContract)
open SourceScheduledAllocationData (TypedClauseData)
open SourcePlannedAllocationData (ClauseData)
open SourceDependencyAnnotations (Dependencies)
open RecursiveRequirements (Requirements Store)
abbrev Receiving := SourceDependencyCapture.Scope

inductive CaptureData [admission : SourceScheduledChecks.DeclarationPolicy] [certification : SourcePlannedChecks.DeclarationPolicy] (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (families : SourceDependencyCapture.Families)
    (required : SourceContextualRechecking.Required) (actions : Syntax.UsageTickets)
    (outward : List Instance) (world : List Nat) (whole capture tail : Stack) (handler : HandlerData)
    (owner parameter binder : Nat) (code : Code) (argument input output : Value)
    (offered : ClauseContract) (row : Footprint) (records : Store) (incoming outgoing : List Instance) (annotations : Annotations)
    (savedEvidence : {scope : Receiving} → {hints : Hints scope} → Forest hints → Prop) :
    SourceDependencyAnnotations.Value → List Instance → (Nat → Dependencies) → Receiving → Receiving →
      List Instance → List Instance → (capDemand tailDemand : List Nat) → Requirements capDemand → Requirements tailDemand →
      (evidence : optParam SourcePlannedFrames.DeclarationEvidence SourcePlannedFrames.recipeEvidence) → Prop where
  | checked {answer : Value} {savedHints : Hints capScope} {waitingHints : Hints tailScope}
      {savedForest : Forest savedHints} {waitingForest : Forest waitingHints}
      (annotation : answer.erase.erase.port = ScopedPorts.eraseType handler.answer)
      (scopeKnown : ScopedPorts.EffectScopeKnown contracts.erase.erase.ports handler.scope)
      (saved : Segment (evidence := evidence) operations policy contracts tables families required actions outward
        (OwnerPhaseTransitions.available (ownedTickets whole)) world capture input answer capDemand capReq capRecords savedForest
        (waitingForest.append .nil) incoming residual)
      (waiting : Segment (evidence := evidence) operations policy contracts tables families required actions outward
        (OwnerPhaseTransitions.available (ownedTickets whole)) world tail answer output tailDemand tailReq tailRecords waitingForest .nil residual outgoing)
      (recordSplit : records = capRecords ++ tailRecords)
      (resume : code.requiredActions.resume = true → resumeEffects = residual)
      (close : code.requiredActions.dispose = true → closeEffects = residual)
      (data : TypedClauseData operations policy contracts tables families required
        (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail)
        world outward (actions.insert owner code.requiredActions)
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole)) owner)
        owner parameter binder code argument input offered row answer residual family savedForest waitingForest resumeEffects closeEffects)
      (kept : savedEvidence savedForest)
      (savedMatched : SourceScheduledSavedPlans.Matches annotations savedForest)
      (waitingMatched : SourceScheduledSavedPlans.Matches annotations waitingForest) :
      CaptureData (evidence := evidence) operations policy contracts tables families required actions outward world whole capture tail handler
        owner parameter binder code argument input output offered row records incoming outgoing annotations savedEvidence
        answer.erase residual family capScope tailScope resumeEffects closeEffects capDemand tailDemand capReq tailReq

theorem CaptureData.erase
    (source : CaptureData operations policy contracts tables families required actions outward world whole capture tail handler
      owner parameter binder code argument input output offered row records incoming outgoing annotations savedEvidence
      oldAnswer residual family capScope tailScope resumeEffects closeEffects capDemand tailDemand capReq tailReq) :
    SourcePlannedCheckedAllocationData.CaptureData operations policy contracts tables families required actions outward world whole capture tail handler
      owner parameter binder code argument input output offered row records incoming outgoing
      oldAnswer residual family capScope tailScope resumeEffects closeEffects capDemand tailDemand capReq tailReq := by
  cases source with
  | checked annotation scopeKnown saved waiting recordSplit resume close data kept savedMatched waitingMatched =>
      exact .checked annotation scopeKnown saved.source waiting.source recordSplit resume close data.erase

theorem CaptureData.clause
    (source : CaptureData (evidence := evidence) operations policy contracts tables families required actions outward world whole capture tail handler
      owner parameter binder code argument input output offered row records incoming outgoing annotations savedEvidence
      oldAnswer residual family capScope tailScope resumeEffects closeEffects capDemand tailDemand capReq tailReq) :
    ClauseData operations policy contracts tables families required
      (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail)
      world outward (actions.insert owner code.requiredActions)
      (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole)) owner)
      owner parameter binder code argument input offered row oldAnswer residual family capScope tailScope resumeEffects closeEffects := by
  cases source with | checked annotation scopeKnown saved waiting records resume close data kept savedMatched waitingMatched => exact ⟨_, rfl, data.erase⟩

theorem CaptureData.allocated
    (source : CaptureData (evidence := evidence) operations policy contracts tables families required actions outward world whole capture tail handler
      owner parameter binder code argument input output offered row records incoming outgoing annotations savedEvidence
      oldAnswer residual family capScope tailScope resumeEffects closeEffects capDemand tailDemand capReq tailReq)
    (allocated : SourceDependencyAnnotations.Contract)
    (fresh : contracts owner = none) (freshAction : actions owner = none) (freshAnnotation : annotations owner = none)
    (inputSame : allocated.input = input.erase) (answerSame : allocated.answer = oldAnswer)
    (resumeSame : allocated.resumeEffects = resumeEffects) (closeSame : allocated.closeEffects = closeEffects)
    (heldSame : allocated.held = capScope.held) (resumeDemandSame : allocated.resumeDemand = capDemand)
    (balance : allocated.closeDemand.Perm allocated.resumeDemand)
    (payload : ValueSummary operations policy contracts world (fun _ => none) payloadAllowed operand argument)
    (closed : ClosedValue operand) :
    ∃ answer : Value, ∃ bodies : ∀ owner, Plan (family owner), ∃ (savedHints : Hints capScope) (waitingHints : Hints tailScope),
    ∃ (savedForest : Forest savedHints) (waitingForest : Forest waitingHints),
      answer.erase = oldAnswer ∧ (refineContract allocated input answer).erase = allocated ∧
      savedEvidence savedForest ∧
      SourceScheduledSavedPlans.Matches (annotations.insert owner ⟨capScope, savedHints, savedForest⟩)
        (.live (owner := owner) savedForest waitingForest) ∧
      Local outward (actions.insert owner code.requiredActions)
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole)) owner) world
        (bodies owner) (.live (owner := owner) savedForest waitingForest) ∧
      Body operations policy (contracts.insert owner (refineContract allocated input answer)) world residual (.ticket binder owner)
        (fun _ => none) (code.subst parameter operand) answer ⟨owner, allocated.erase, offered.dispose, row⟩ (signature (bodies owner)) ∧
      Segment (evidence := evidence) operations policy (contracts.insert owner (refineContract allocated input answer)) tables families required
        (actions.insert owner code.requiredActions) outward
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole)) owner) world
        (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail)
        answer output tailDemand (.sequence (.spent owner) tailReq)
        ((⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: records) (.live (owner := owner) savedForest waitingForest) .nil residual outgoing := by
  cases resumeDemandSame
  cases source with
  | checked annotation scopeKnown saved waiting recordSplit resume close data kept savedMatched waitingMatched =>
      rename_i capRecords tailRecords answer savedHints savedForest waitingHints waitingForest
      obtain ⟨bodies, exactErasure, matched, checked, pending, body⟩ :=
        data.allocated_body allocated fresh inputSame answerSame resumeSame closeSame heldSame balance payload closed
      refine ⟨answer, bodies, savedHints, waitingHints, savedForest, waitingForest, rfl, exactErasure, kept,
        .live (by simp [Annotations.insert])
          (savedMatched.transport (SourceScheduledSavedPlans.insert_extends freshAnnotation))
          (waitingMatched.transport (SourceScheduledSavedPlans.insert_extends freshAnnotation)),
        checked, body, ?_⟩
      let contract := refineContract allocated input answer
      have extension := SourcePlannedTyping.insert_extends (contract := contract) contracts fresh
      have permissions := Syntax.fresh_usage_insert_extends (rights := code.requiredActions) freshAction
      have ports := CoherentSourceTypes.Owners.port_contracts_extension
        (SourceDependencyFrames.erased_contract_extension (SourcePlannedCheckedFrames.erased_extension extension))
      have known : (contracts.insert owner contract) owner = some contract := by simp [Contracts.insert]
      have actionKnown : (actions.insert owner code.requiredActions) owner = some code.requiredActions := by simp [Syntax.UsageTickets.insert]
      rw [recordSplit]
      apply Segment.live known actionKnown (ScopedPorts.erase_embed_port _).symm annotation
        (ScopedPorts.effect_scope_known_extension scopeKnown ports)
      · exact heldSame.trans saved.source.source.matches.realizes.held
      · exact (saved.input_weaken (List.nil_subset _)).transport extension SourceDependencySchemes.introduce_extends permissions
      · intro used; simpa only [contract, refineContract, resumeSame, resume used] using List.Subset.refl residual
      · exact waiting.transport extension SourceDependencySchemes.introduce_extends permissions
      · intro used; simpa only [contract, refineContract, resumeSame, resume used] using List.Subset.refl residual
      · intro used; simpa only [contract, refineContract, closeSame, close used] using List.Subset.refl residual
      · exact List.Subset.refl _

end Ash.OneShot.SourceScheduledCaptureData

#print axioms Ash.OneShot.SourceScheduledCaptureData.CaptureData.clause
#print axioms Ash.OneShot.SourceScheduledCaptureData.CaptureData.allocated

#print axioms Ash.OneShot.SourceScheduledCaptureData.CaptureData.erase
