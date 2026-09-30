import SourcePlannedCheckedTransport

/-! The shared allocator retains joint source witnesses at its exact requirement
indices. Rebuilding the live segment uses fresh registry/phase transport and the
same refined answer as the selected clause, not equality inferred after erasure. -/
namespace Ash.OneShot.SourcePlannedCheckedAllocationData

open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Value Operations Contracts)
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceContextualHints (Hints)
open SourceContextualHintChecking (Matches)
open SourcePlannedChecks (Local)
open SourcePlannedCheckedFrames (Segment)
open SourcePlannedSources (Body ValueSummary refineContract)
open SourcePlannedAllocationData (TypedClauseData ClauseData)
open SourceDependencyAnnotations (Dependencies)
open RecursiveRequirements (Requirements Store)
abbrev Receiving := SourceDependencyCapture.Scope

/-- At a fixed dependency scope and actual stack, the required handler hints
are determined. This aligns retained clause checks with the joint saved source. -/
private theorem matched_hints_heq {first : Hints firstScope} {second : Hints secondScope}
    (matched : Matches tables families required first stack)
    (other : Matches tables families required second stack)
    (same : firstScope = secondScope) : HEq first second := by
  induction matched generalizing secondScope with
  | nil => cases other; rfl
  | plain rest ih => cases other with | plain tail => cases same; cases ih tail rfl; rfl
  | handler rest ih => cases other with | handler tail => cases same; cases ih tail rfl; rfl
  | cell rest ih => cases other with | cell tail => cases same; cases ih tail rfl; rfl
  | cleanup rest ih => cases other with | cleanup tail => cases same; cases ih tail rfl; rfl
  | running rest ih => cases other with | running tail => cases same; cases ih tail rfl; rfl
  | unwinding rest ih => cases other with | unwinding tail => cases same; cases ih tail rfl; rfl
  | closing rest ih => cases other with | closing tail => cases same; cases ih tail rfl; rfl
  | retiring rest ih => cases other with | retiring tail => cases same; cases ih tail rfl; rfl
  | live saved rest ihSaved ihRest => cases other with
    | live inside tail => cases same; cases ihSaved inside rfl; cases ihRest tail rfl; rfl
  | spent rest ih => cases other with | spent tail => cases same; cases ih tail rfl; rfl

theorem matched_hints_unique {first second : Hints scope}
    (matched : Matches tables families required first stack)
    (other : Matches tables families required second stack) : first = second :=
  eq_of_heq (matched_hints_heq matched other rfl)

variable [certification : SourcePlannedChecks.DeclarationPolicy]

inductive CaptureData [certification : SourcePlannedChecks.DeclarationPolicy] (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (families : SourceDependencyCapture.Families)
    (required : SourceContextualRechecking.Required) (actions : Syntax.UsageTickets)
    (outward : List Instance) (world : List Nat) (whole capture tail : Stack) (handler : HandlerData)
    (owner parameter binder : Nat) (code : Code) (argument input output : Value)
    (offered : ClauseContract) (row : Footprint) (records : Store) (incoming outgoing : List Instance) :
    SourceDependencyAnnotations.Value → List Instance → (Nat → Dependencies) → Receiving → Receiving →
      List Instance → List Instance → (capDemand tailDemand : List Nat) → Requirements capDemand → Requirements tailDemand → Prop where
  | checked {answer : Value} {savedHints : Hints capScope} {waitingHints : Hints tailScope}
      (annotation : answer.erase.erase.port = ScopedPorts.eraseType handler.answer)
      (scopeKnown : ScopedPorts.EffectScopeKnown contracts.erase.erase.ports handler.scope)
      (saved : Segment operations policy contracts tables families required actions outward
        (OwnerPhaseTransitions.available (ownedTickets whole)) world capture input answer capDemand capReq capRecords savedHints
        (waitingHints.append .nil) incoming residual)
      (waiting : Segment operations policy contracts tables families required actions outward
        (OwnerPhaseTransitions.available (ownedTickets whole)) world tail answer output tailDemand tailReq tailRecords waitingHints .nil residual outgoing)
      (recordSplit : records = capRecords ++ tailRecords)
      (resume : code.requiredActions.resume = true → resumeEffects = residual)
      (close : code.requiredActions.dispose = true → closeEffects = residual)
      (data : TypedClauseData operations policy contracts tables families required
        (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail)
        world outward (actions.insert owner code.requiredActions)
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole)) owner)
        owner parameter binder code argument input offered row answer residual family capScope tailScope resumeEffects closeEffects) :
      CaptureData operations policy contracts tables families required actions outward world whole capture tail handler
        owner parameter binder code argument input output offered row records incoming outgoing
        answer.erase residual family capScope tailScope resumeEffects closeEffects capDemand tailDemand capReq tailReq

theorem CaptureData.clause
    (source : CaptureData operations policy contracts tables families required actions outward world whole capture tail handler
      owner parameter binder code argument input output offered row records incoming outgoing
      oldAnswer residual family capScope tailScope resumeEffects closeEffects capDemand tailDemand capReq tailReq) :
    ClauseData operations policy contracts tables families required
      (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail)
      world outward (actions.insert owner code.requiredActions)
      (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole)) owner)
      owner parameter binder code argument input offered row oldAnswer residual family capScope tailScope resumeEffects closeEffects := by
  cases source with | checked annotation scopeKnown saved waiting records resume close data => exact ⟨_, rfl, data⟩

theorem CaptureData.allocated
    (source : CaptureData operations policy contracts tables families required actions outward world whole capture tail handler
      owner parameter binder code argument input output offered row records incoming outgoing
      oldAnswer residual family capScope tailScope resumeEffects closeEffects capDemand tailDemand capReq tailReq)
    (allocated : SourceDependencyAnnotations.Contract)
    (fresh : contracts owner = none) (freshAction : actions owner = none)
    (inputSame : allocated.input = input.erase) (answerSame : allocated.answer = oldAnswer)
    (resumeSame : allocated.resumeEffects = resumeEffects) (closeSame : allocated.closeEffects = closeEffects)
    (heldSame : allocated.held = capScope.held) (resumeDemandSame : allocated.resumeDemand = capDemand)
    (balance : allocated.closeDemand.Perm allocated.resumeDemand)
    (payload : ValueSummary operations policy contracts world (fun _ => none) payloadAllowed operand argument)
    (closed : ClosedValue operand) :
    ∃ answer : Value, ∃ bodies : ∀ owner, Plan (family owner), ∃ (savedHints : Hints capScope) (waitingHints : Hints tailScope),
      answer.erase = oldAnswer ∧ (refineContract allocated input answer).erase = allocated ∧
      Local outward (actions.insert owner code.requiredActions)
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole)) owner) world
        (bodies owner) (.live (owner := owner) savedHints waitingHints) ∧
      Body operations policy (contracts.insert owner (refineContract allocated input answer)) world residual (.ticket binder owner)
        (fun _ => none) (code.subst parameter operand) answer ⟨owner, allocated.erase, offered.dispose, row⟩ (signature (bodies owner)) ∧
      Segment operations policy (contracts.insert owner (refineContract allocated input answer)) tables families required
        (actions.insert owner code.requiredActions) outward
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole)) owner) world
        (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail)
        answer output tailDemand (.sequence (.spent owner) tailReq)
        ((⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: records) (.live (owner := owner) savedHints waitingHints) .nil residual outgoing := by
  cases resumeDemandSame
  cases source with
  | checked annotation scopeKnown saved waiting recordSplit resume close data =>
      rename_i capRecords tailRecords answer savedHints waitingHints
      obtain ⟨bodies, actualSaved, actualWaiting, exactErasure, matched, checked, pending, body⟩ :=
        data.allocated_body allocated fresh inputSame answerSame resumeSame closeSame heldSame balance payload closed
      have hintsSame := matched_hints_unique matched (.live saved.source.matches waiting.source.matches)
      rw [hintsSame] at checked
      refine ⟨answer, bodies, savedHints, waitingHints, rfl, exactErasure, checked, body, ?_⟩
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
      · exact heldSame.trans saved.source.matches.realizes.held
      · exact (saved.input_weaken (List.nil_subset _)).transport extension SourceDependencySchemes.introduce_extends permissions
      · intro used; simpa only [contract, refineContract, resumeSame, resume used] using List.Subset.refl residual
      · exact waiting.transport extension SourceDependencySchemes.introduce_extends permissions
      · intro used; simpa only [contract, refineContract, resumeSame, resume used] using List.Subset.refl residual
      · intro used; simpa only [contract, refineContract, closeSame, close used] using List.Subset.refl residual
      · exact List.Subset.refl _

end Ash.OneShot.SourcePlannedCheckedAllocationData

#print axioms Ash.OneShot.SourcePlannedCheckedAllocationData.matched_hints_unique
#print axioms Ash.OneShot.SourcePlannedCheckedAllocationData.CaptureData.clause
#print axioms Ash.OneShot.SourcePlannedCheckedAllocationData.CaptureData.allocated
