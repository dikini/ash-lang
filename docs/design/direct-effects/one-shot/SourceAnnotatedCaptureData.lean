import SourceAnnotatedCaptureInterfaces

/-! The shared allocator retains joint source witnesses at its exact requirement
indices. Rebuilding the live segment uses fresh registry/phase transport and the
same refined answer as the selected clause, not equality inferred after erasure. -/
namespace Ash.OneShot.SourceAnnotatedCaptureData

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
open SourceAnnotatedRuntimeTyping (Segment)
open SourceAnnotatedSources (Body ValueSummary)
open SourcePlannedSources (refineContract)
open SourceAnnotatedAllocationData (TypedClauseDataAtPlan ClauseEvidence noClauseEvidence)
open SourcePlannedAllocationData (ClauseData)
open SourceDependencyAnnotations (Dependencies)
open RecursiveRequirements (Requirements Store)
abbrev Receiving := SourceDependencyCapture.Scope

inductive CaptureData [admission : SourceScheduledChecks.DeclarationPolicy] [certification : SourcePlannedChecks.DeclarationPolicy] (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (families : SourceDependencyCapture.Families)
    (required : SourceContextualRechecking.Required) (actions : Syntax.UsageTickets)
    (outward : List Instance) (world : List Nat) (whole capture tail : SourceAnnotatedRuntime.Stack) (handler : SourceAnnotatedRuntime.Handler)
    (owner parameter binder : Nat) (code : SourceAnnotatedCode.Term) (argument input output : Value)
    (offered : ClauseContract) (row : Footprint) (records : Store) (incoming outgoing : List Instance) (annotations : Annotations)
    (savedEvidence : {scope : Receiving} → {hints : Hints scope} → Forest hints → Prop) :
    SourceDependencyAnnotations.Value → List Instance → (Nat → Dependencies) → Receiving → Receiving →
      List Instance → List Instance → (capDemand tailDemand : List Nat) → Requirements capDemand → Requirements tailDemand →
      (evidence : optParam SourcePlannedFrames.DeclarationEvidence SourcePlannedFrames.recipeEvidence) →
      (currentEvidence : optParam ClauseEvidence noClauseEvidence) → Prop where
  | checked {answer : Value} {savedHints : Hints capScope} {waitingHints : Hints tailScope}
      {savedForest : Forest savedHints} {waitingForest : Forest waitingHints}
      (annotation : answer.erase.erase.port = ScopedPorts.eraseType handler.answer)
      (scopeKnown : ScopedPorts.EffectScopeKnown contracts.erase.erase.ports handler.scope)
      (saved : Segment (evidence := evidence) operations policy contracts tables families required actions outward
        (OwnerPhaseTransitions.available (ownedTickets whole.erase)) world capture input answer capDemand capReq capRecords savedForest
        (waitingForest.append .nil) incoming residual)
      (waiting : Segment (evidence := evidence) operations policy contracts tables families required actions outward
        (OwnerPhaseTransitions.available (ownedTickets whole.erase)) world tail answer output tailDemand tailReq tailRecords waitingForest .nil residual outgoing)
      (recordSplit : records = capRecords ++ tailRecords)
      (resume : code.erase.requiredActions.resume = true → resumeEffects = residual)
      (close : code.erase.requiredActions.dispose = true → closeEffects = residual)
      (data : TypedClauseDataAtPlan operations policy contracts tables families required
        (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail)
        world outward (actions.insert owner code.erase.requiredActions)
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner)
        owner parameter binder code argument input offered row answer residual family savedForest waitingForest resumeEffects closeEffects bodies)
      (kept : savedEvidence savedForest)
      (savedMatched : SourceScheduledSavedPlans.Matches annotations savedForest)
      (waitingMatched : SourceScheduledSavedPlans.Matches annotations waitingForest)
      (clauseKept : currentEvidence (bodies owner) (.live (owner := owner) savedForest waitingForest)) :
      CaptureData (evidence := evidence) (currentEvidence := currentEvidence) operations policy contracts tables families required actions outward world whole capture tail handler
        owner parameter binder code argument input output offered row records incoming outgoing annotations savedEvidence
        answer.erase residual family capScope tailScope resumeEffects closeEffects capDemand tailDemand capReq tailReq

omit [SourceScheduledChecks.DeclarationProjection admission certification] in
theorem CaptureData.erase
    (source : CaptureData (evidence := evidence) (currentEvidence := currentEvidence) operations policy contracts tables families required actions outward world whole capture tail handler
      owner parameter binder code argument input output offered row records incoming outgoing annotations savedEvidence
      oldAnswer residual family capScope tailScope resumeEffects closeEffects capDemand tailDemand capReq tailReq) :
    SourceScheduledCaptureData.CaptureData (evidence := evidence) operations policy contracts tables families required actions outward world whole.erase capture.erase tail.erase handler.erase
      owner parameter binder code.erase argument input output offered row records incoming outgoing annotations savedEvidence
      oldAnswer residual family capScope tailScope resumeEffects closeEffects capDemand tailDemand capReq tailReq := by
  cases source with
  | checked annotation scopeKnown saved waiting recordSplit resume close data kept savedMatched waitingMatched clauseKept =>
      exact .checked annotation scopeKnown saved.erase waiting.erase recordSplit resume close data.forget.erase kept savedMatched waitingMatched

omit [SourceScheduledChecks.DeclarationProjection admission certification] in
/-- Erasure to the compatibility interface discards only the extra clause
fact, retaining the exact typed witness and saved-source certificate. -/
theorem CaptureData.forget_clause_evidence
    (source : CaptureData (evidence := evidence) (currentEvidence := currentEvidence) operations policy contracts tables families required actions outward world whole capture tail handler
      owner parameter binder code argument input output offered row records incoming outgoing annotations savedEvidence
      oldAnswer residual family capScope tailScope resumeEffects closeEffects capDemand tailDemand capReq tailReq) :
    CaptureData (evidence := evidence) operations policy contracts tables families required actions outward world whole capture tail handler
      owner parameter binder code argument input output offered row records incoming outgoing annotations savedEvidence
      oldAnswer residual family capScope tailScope resumeEffects closeEffects capDemand tailDemand capReq tailReq := by
  cases source with
  | checked annotation scopeKnown saved waiting recordSplit resume close data kept savedMatched waitingMatched clauseKept =>
      exact .checked annotation scopeKnown saved waiting recordSplit resume close data kept savedMatched waitingMatched trivial

theorem CaptureData.clause
    (source : CaptureData (evidence := evidence) (currentEvidence := currentEvidence) operations policy contracts tables families required actions outward world whole capture tail handler
      owner parameter binder code argument input output offered row records incoming outgoing annotations savedEvidence
      oldAnswer residual family capScope tailScope resumeEffects closeEffects capDemand tailDemand capReq tailReq) :
    ClauseData operations policy contracts tables families required
      (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture.erase handler.scope tail.erase)
      world outward (actions.insert owner code.erase.requiredActions)
      (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner)
      owner parameter binder code.erase argument input offered row oldAnswer residual family capScope tailScope resumeEffects closeEffects := by
  exact source.erase.clause

theorem CaptureData.allocated_retaining
    (source : CaptureData (evidence := evidence) (currentEvidence := currentEvidence) operations policy contracts tables families required actions outward world whole capture tail handler
      owner parameter binder code argument input output offered row records incoming outgoing annotations savedEvidence
      oldAnswer residual family capScope tailScope resumeEffects closeEffects capDemand tailDemand capReq tailReq)
    (allocated : SourceDependencyAnnotations.Contract)
    (fresh : contracts owner = none) (freshAction : actions owner = none) (freshAnnotation : annotations owner = none)
    (inputSame : allocated.input = input.erase) (answerSame : allocated.answer = oldAnswer)
    (resumeSame : allocated.resumeEffects = resumeEffects) (closeSame : allocated.closeEffects = closeEffects)
    (heldSame : allocated.held = capScope.held) (resumeDemandSame : allocated.resumeDemand = capDemand)
    (balance : allocated.closeDemand.Perm allocated.resumeDemand)
    (payload : ValueSummary operations policy contracts world (fun _ => none) payloadAllowed operand argument)
    (closed : ClosedValue operand.erase) :
    ∃ answer : Value, ∃ bodies : ∀ owner, Plan (family owner), ∃ (savedHints : Hints capScope) (waitingHints : Hints tailScope),
    ∃ (savedForest : Forest savedHints) (waitingForest : Forest waitingHints),
      answer.erase = oldAnswer ∧ (refineContract allocated input answer).erase = allocated ∧
      savedEvidence savedForest ∧
      SourceScheduledSavedPlans.Matches (annotations.insert owner ⟨capScope, savedHints, savedForest⟩)
        (.live (owner := owner) savedForest waitingForest) ∧
      Local outward (actions.insert owner code.erase.requiredActions)
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner) world
        (bodies owner) (.live (owner := owner) savedForest waitingForest) ∧
      Body operations policy (contracts.insert owner (refineContract allocated input answer)) world residual (.ticket binder owner)
        (fun _ => none) (code.subst parameter operand) answer ⟨owner, allocated.erase, offered.dispose, row⟩ (signature (bodies owner)) ∧
      Segment (evidence := evidence) operations policy (contracts.insert owner (refineContract allocated input answer)) tables families required
        (actions.insert owner code.erase.requiredActions) outward
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner) world
        (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail)
        answer output tailDemand (.sequence (.spent owner) tailReq)
        ((⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: records) (.live (owner := owner) savedForest waitingForest) .nil residual outgoing ∧
      currentEvidence (bodies owner) (.live (owner := owner) savedForest waitingForest) := by
  cases resumeDemandSame
  cases source with
  | checked annotation scopeKnown saved waiting recordSplit resume close data kept savedMatched waitingMatched clauseKept =>
      rename_i capRecords tailRecords answer bodies savedHints savedForest waitingHints waitingForest
      obtain ⟨exactErasure, matched, checked, pending, body⟩ :=
        data.allocated_body allocated fresh inputSame answerSame resumeSame closeSame heldSame balance payload closed
      refine ⟨answer, bodies, savedHints, waitingHints, savedForest, waitingForest, rfl, exactErasure, kept,
        .live (by simp [Annotations.insert])
          (savedMatched.transport (SourceScheduledSavedPlans.insert_extends freshAnnotation))
          (waitingMatched.transport (SourceScheduledSavedPlans.insert_extends freshAnnotation)),
        checked, body, ?_, clauseKept⟩
      let contract := refineContract allocated input answer
      have extension := SourcePlannedTyping.insert_extends (contract := contract) contracts fresh
      have permissions := Syntax.fresh_usage_insert_extends (rights := code.erase.requiredActions) freshAction
      have ports := CoherentSourceTypes.Owners.port_contracts_extension
        (SourceDependencyFrames.erased_contract_extension (SourcePlannedCheckedFrames.erased_extension extension))
      have known : (contracts.insert owner contract) owner = some contract := by simp [Contracts.insert]
      have actionKnown : (actions.insert owner code.erase.requiredActions) owner = some code.erase.requiredActions := by simp [Syntax.UsageTickets.insert]
      rw [recordSplit]
      apply Segment.live known actionKnown (ScopedPorts.erase_embed_port _).symm annotation
        (ScopedPorts.effect_scope_known_extension scopeKnown ports)
      · exact heldSame.trans saved.erase.source.source.matches.realizes.held
      · exact (saved.input_weaken (List.nil_subset _)).transport extension SourceDependencySchemes.introduce_extends permissions
      · intro used; simpa only [contract, refineContract, resumeSame, resume used] using List.Subset.refl residual
      · exact waiting.transport extension SourceDependencySchemes.introduce_extends permissions
      · intro used; simpa only [contract, refineContract, resumeSame, resume used] using List.Subset.refl residual
      · intro used; simpa only [contract, refineContract, closeSame, close used] using List.Subset.refl residual
      · exact List.Subset.refl _

theorem CaptureData.allocated
    (source : CaptureData (evidence := evidence) (currentEvidence := currentEvidence) operations policy contracts tables families required actions outward world whole capture tail handler
      owner parameter binder code argument input output offered row records incoming outgoing annotations savedEvidence
      oldAnswer residual family capScope tailScope resumeEffects closeEffects capDemand tailDemand capReq tailReq)
    (allocated : SourceDependencyAnnotations.Contract)
    (fresh : contracts owner = none) (freshAction : actions owner = none) (freshAnnotation : annotations owner = none)
    (inputSame : allocated.input = input.erase) (answerSame : allocated.answer = oldAnswer)
    (resumeSame : allocated.resumeEffects = resumeEffects) (closeSame : allocated.closeEffects = closeEffects)
    (heldSame : allocated.held = capScope.held) (resumeDemandSame : allocated.resumeDemand = capDemand)
    (balance : allocated.closeDemand.Perm allocated.resumeDemand)
    (payload : ValueSummary operations policy contracts world (fun _ => none) payloadAllowed operand argument)
    (closed : ClosedValue operand.erase) :
    ∃ answer : Value, ∃ bodies : ∀ owner, Plan (family owner), ∃ (savedHints : Hints capScope) (waitingHints : Hints tailScope),
    ∃ (savedForest : Forest savedHints) (waitingForest : Forest waitingHints),
      answer.erase = oldAnswer ∧ (refineContract allocated input answer).erase = allocated ∧
      savedEvidence savedForest ∧
      SourceScheduledSavedPlans.Matches (annotations.insert owner ⟨capScope, savedHints, savedForest⟩)
        (.live (owner := owner) savedForest waitingForest) ∧
      Local outward (actions.insert owner code.erase.requiredActions)
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner) world
        (bodies owner) (.live (owner := owner) savedForest waitingForest) ∧
      Body operations policy (contracts.insert owner (refineContract allocated input answer)) world residual (.ticket binder owner)
        (fun _ => none) (code.subst parameter operand) answer ⟨owner, allocated.erase, offered.dispose, row⟩ (signature (bodies owner)) ∧
      Segment (evidence := evidence) operations policy (contracts.insert owner (refineContract allocated input answer)) tables families required
        (actions.insert owner code.erase.requiredActions) outward
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner) world
        (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture handler.scope tail)
        answer output tailDemand (.sequence (.spent owner) tailReq)
        ((⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: records) (.live (owner := owner) savedForest waitingForest) .nil residual outgoing := by
  obtain ⟨answer, bodies, savedHints, waitingHints, saved, waiting, sameAnswer, sameContract, kept, matched, localCheck, body, segment, _⟩ :=
    source.allocated_retaining allocated fresh freshAction freshAnnotation inputSame answerSame resumeSame closeSame heldSame
      resumeDemandSame balance payload closed
  exact ⟨answer, bodies, savedHints, waitingHints, saved, waiting, sameAnswer, sameContract, kept, matched, localCheck, body, segment⟩

end Ash.OneShot.SourceAnnotatedCaptureData

#print axioms Ash.OneShot.SourceAnnotatedCaptureData.CaptureData.clause
#print axioms Ash.OneShot.SourceAnnotatedCaptureData.CaptureData.allocated

#print axioms Ash.OneShot.SourceAnnotatedCaptureData.CaptureData.erase

#print axioms Ash.OneShot.SourceAnnotatedCaptureData.CaptureData.allocated_retaining

#print axioms Ash.OneShot.SourceAnnotatedCaptureData.CaptureData.forget_clause_evidence
