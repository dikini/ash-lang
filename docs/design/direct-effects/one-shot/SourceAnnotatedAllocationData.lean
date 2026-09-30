import SourceAnnotatedCaptureSources
import SourceAnnotatedRuntimeTransport
import SourceScheduledCaptureAnnotations

/-! Retain the selected clause and its exact saved/waiting plan forests through
contract refinement and closed payload substitution. Erasure reuses the shared
allocator's earlier clause certificate. -/
namespace Ash.OneShot.SourceAnnotatedAllocationData
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations (Dependencies)
open SourcePlannedTyping (Value Environment Operations Contract Contracts)
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceContextualHintChecking (Matches)
open SourceScheduledChecks (Local Pending)
open SourceAnnotatedSources (Body ValueSummary)
open SourcePlannedSources (refineContract)

/-- A parameter for transporting already established facts about the actual
clause plan and receiving forest. It is not an additional admission rule. -/
abbrev ClauseEvidence := {dependencies : Dependencies} → {scope : SourceDependencyCapture.Scope} →
  {hints : Hints scope} → Plan dependencies → Forest hints → Prop

def noClauseEvidence : ClauseEvidence := fun _ _ => True

section
variable [admission : SourceScheduledChecks.DeclarationPolicy] [certification : SourcePlannedChecks.DeclarationPolicy]

inductive TypedClauseData [admission : SourceScheduledChecks.DeclarationPolicy] [certification : SourcePlannedChecks.DeclarationPolicy] (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (families : SourceDependencyCapture.Families)
    (required : SourceContextualRechecking.Required) (stack : SourceAnnotatedRuntime.Stack)
    (world : List Nat) (outward : List Instance) (actions : Syntax.UsageTickets)
    (phases : OwnerPhaseTransitions.Phases) (owner parameter binder : Nat) (code : SourceAnnotatedCode.Term)
    (argument input : Value) (offered : ClauseContract) (row : Footprint) :
    Value → List Instance → (Nat → Dependencies) →
      {captured tail : SourceDependencyCapture.Scope} → {savedHints : Hints captured} → {waitingHints : Hints tail} →
      Forest savedHints → Forest waitingHints → List Instance → List Instance → Prop where
  | checked {bodies : ∀ owner, Plan (family owner)} {savedHints : Hints captured} {waitingHints : Hints tail}
      {saved : Forest savedHints} {waiting : Forest waitingHints}
      (matched : Matches tables families required (.live (owner := owner) savedHints waitingHints) stack.erase)
      (current : Local outward actions phases world (bodies owner) (.live (owner := owner) saved waiting))
      (pending : Pending outward actions phases world (.live (owner := owner) saved waiting) .nil)
      (source : ∀ (contract : Contract), contracts owner = none →
        contract.input = input → contract.answer = answer →
        contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
        contract.held = captured.held → contract.closeDemand.Perm contract.resumeDemand →
        Body operations policy (contracts.insert owner contract) world allowed (.ticket binder owner)
          (Environment.extend (fun _ => none) parameter argument) code answer
          ⟨owner, contract.erase.erase, offered.dispose, row⟩ (signature (bodies owner))) :
      TypedClauseData operations policy contracts tables families required stack world outward actions phases owner parameter binder code argument input offered row
        answer allowed family saved waiting resumeEffects closeEffects

/-- Typed capture data retain the actual selected checking plan as an index. -/
inductive TypedClauseDataAtPlan [admission : SourceScheduledChecks.DeclarationPolicy] [certification : SourcePlannedChecks.DeclarationPolicy] (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (families : SourceDependencyCapture.Families)
    (required : SourceContextualRechecking.Required) (stack : SourceAnnotatedRuntime.Stack)
    (world : List Nat) (outward : List Instance) (actions : Syntax.UsageTickets)
    (phases : OwnerPhaseTransitions.Phases) (owner parameter binder : Nat) (code : SourceAnnotatedCode.Term)
    (argument input : Value) (offered : ClauseContract) (row : Footprint) :
    Value → List Instance → (family : Nat → Dependencies) →
      {captured tail : SourceDependencyCapture.Scope} → {savedHints : Hints captured} → {waitingHints : Hints tail} →
      Forest savedHints → Forest waitingHints → List Instance → List Instance → ((owner : Nat) → Plan (family owner)) → Prop where
  | checked {bodies : ∀ owner, Plan (family owner)} {savedHints : Hints captured} {waitingHints : Hints tail}
      {saved : Forest savedHints} {waiting : Forest waitingHints}
      (matched : Matches tables families required (.live (owner := owner) savedHints waitingHints) stack.erase)
      (current : Local outward actions phases world (bodies owner) (.live (owner := owner) saved waiting))
      (pending : Pending outward actions phases world (.live (owner := owner) saved waiting) .nil)
      (source : ∀ (contract : Contract), contracts owner = none →
        contract.input = input → contract.answer = answer →
        contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
        contract.held = captured.held → contract.closeDemand.Perm contract.resumeDemand →
        Body operations policy (contracts.insert owner contract) world allowed (.ticket binder owner)
          (Environment.extend (fun _ => none) parameter argument) code answer
          ⟨owner, contract.erase.erase, offered.dispose, row⟩ (signature (bodies owner))) :
      TypedClauseDataAtPlan operations policy contracts tables families required stack world outward actions phases owner parameter binder code argument input offered row
        answer allowed family saved waiting resumeEffects closeEffects bodies

/-- The legacy existential interface is a projection of exact-plan data. -/
theorem TypedClauseDataAtPlan.forget {savedHints : Hints captured} {waitingHints : Hints tail}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (data : TypedClauseDataAtPlan operations policy contracts tables families required stack world outward actions phases
      owner parameter binder code argument input offered row answer allowed family saved waiting resumeEffects closeEffects bodies) :
    TypedClauseData operations policy contracts tables families required stack world outward actions phases
      owner parameter binder code argument input offered row answer allowed family saved waiting resumeEffects closeEffects := by
  cases data with
  | checked matched current pending source => exact .checked matched current pending source

/-- Recover the original constructor's exact plan without choosing a second
source derivation. This supports legacy callers at the certificate boundary. -/
theorem TypedClauseData.at_plan {savedHints : Hints captured} {waitingHints : Hints tail}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (data : TypedClauseData operations policy contracts tables families required stack world outward actions phases
      owner parameter binder code argument input offered row answer allowed family saved waiting resumeEffects closeEffects) :
    ∃ bodies, TypedClauseDataAtPlan operations policy contracts tables families required stack world outward actions phases
      owner parameter binder code argument input offered row answer allowed family saved waiting resumeEffects closeEffects bodies := by
  cases data with
  | checked matched current pending source => exact ⟨_, .checked matched current pending source⟩

theorem TypedClauseData.erase {savedHints : Hints captured} {waitingHints : Hints tail}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (data : TypedClauseData operations policy contracts tables families required stack world outward actions phases
      owner parameter binder code argument input offered row answer allowed family saved waiting resumeEffects closeEffects) :
    SourceScheduledAllocationData.TypedClauseData operations policy contracts tables families required stack.erase world outward actions phases
      owner parameter binder code.erase argument input offered row answer allowed family saved waiting resumeEffects closeEffects := by
  cases data with
  | checked matched current pending source =>
      exact .checked matched current pending (fun contract fresh inputSame answerSame resumeSame closeSame heldSame balance =>
        (source contract fresh inputSame answerSame resumeSame closeSame heldSame balance).erase)

theorem TypedClauseDataAtPlan.allocated_body {savedHints : Hints captured} {waitingHints : Hints tail}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (data : TypedClauseDataAtPlan operations policy contracts tables families required stack world outward actions phases owner parameter binder code argument input offered row
      answer allowed family saved waiting resumeEffects closeEffects bodies)
    (allocated : SourceDependencyAnnotations.Contract)
    (fresh : contracts owner = none) (inputSame : allocated.input = input.erase)
    (answerSame : allocated.answer = answer.erase)
    (resumeSame : allocated.resumeEffects = resumeEffects) (closeSame : allocated.closeEffects = closeEffects)
    (heldSame : allocated.held = captured.held) (balance : allocated.closeDemand.Perm allocated.resumeDemand)
    (payload : ValueSummary operations policy contracts world (fun _ => none) payloadAllowed operand argument)
    (closed : ClosedValue operand.erase) :
      (refineContract allocated input answer).erase = allocated ∧
      Matches tables families required (.live (owner := owner) savedHints waitingHints) stack.erase ∧
      Local outward actions phases world (bodies owner) (.live (owner := owner) saved waiting) ∧
      Pending outward actions phases world (.live (owner := owner) saved waiting) .nil ∧
      Body operations policy (contracts.insert owner (refineContract allocated input answer)) world allowed (.ticket binder owner)
        (fun _ => none) (code.subst parameter operand) answer ⟨owner, allocated.erase, offered.dispose, row⟩
        (signature (bodies owner)) := by
  cases data with
  | checked matched current pending source =>
      have exactErasure := SourcePlannedSources.refine_contract_erase inputSame answerSame
      have body := source (refineContract allocated input answer) fresh rfl rfl resumeSame closeSame heldSame balance
      have substituted := SourceAnnotatedCaptureSources.body_substitution body
        (SourceAnnotatedCaptureSources.fresh_payload payload closed fresh) closed
      exact ⟨exactErasure, matched, current, pending,
        by simpa only [exactErasure] using substituted⟩

/-- The original capture step, owner equation and substitution theorem apply
at the retained exact plan after the allocator refines its contract. -/
theorem TypedClauseDataAtPlan.capture_step {savedHints : Hints captured} {waitingHints : Hints tail}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (data : TypedClauseDataAtPlan operations policy contracts tables families required stack world outward actions phases owner parameter binder code argument input offered row
      answer allowed family saved waiting resumeEffects closeEffects bodies)
    (allocated : SourceDependencyAnnotations.Contract)
    (fresh : contracts owner = none) (inputSame : allocated.input = input.erase)
    (answerSame : allocated.answer = answer.erase)
    (resumeSame : allocated.resumeEffects = resumeEffects) (closeSame : allocated.closeEffects = closeEffects)
    (heldSame : allocated.held = captured.held) (balance : allocated.closeDemand.Perm allocated.resumeDemand)
    (payload : ValueSummary operations policy contracts world (fun _ => none) payloadAllowed operand argument)
    (closed : ClosedValue operand.erase)
    (cut : SourceAnnotatedRuntime.HandlerCut requested whole capture tailStack handler)
    (selected : SourceAnnotatedRuntime.ClauseAt operation handler.clauses parameter binder code)
    (unique : (ownedTickets whole.erase).Nodup) (absent : owner ∉ ownedTickets whole.erase) :
    (refineContract allocated input answer).erase = allocated ∧
    RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand.erase, caller, whole.erase⟩
      ⟨code.erase.subst parameter operand.erase, .ticket binder owner,
        .live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture.erase handler.scope tailStack.erase⟩ [.ticket owner] [] ∧
    ownedTickets (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture.erase handler.scope tailStack.erase) =
      owner :: ownedTickets whole.erase ∧
    (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture.erase handler.scope tailStack.erase)).Nodup ∧
    OwnerPhaseTransitions.available
      (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer capture.erase handler.scope tailStack.erase)) =
      OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner ∧
    Body operations policy (contracts.insert owner (refineContract allocated input answer)) world allowed (.ticket binder owner)
      (fun _ => none) (code.subst parameter operand) answer ⟨owner, allocated.erase, offered.dispose, row⟩
      (signature (bodies owner)) := by
  cases data with
  | checked matched current pending source =>
      have exactErasure := SourcePlannedSources.refine_contract_erase inputSame answerSame
      have body := source (refineContract allocated input answer) fresh rfl rfl resumeSame closeSame heldSame balance
      have known : (contracts.insert owner (refineContract allocated input answer)) owner =
          some (refineContract allocated input answer) := by simp [SourcePlannedTyping.Contracts.insert]
      have step := SourceAnnotatedCaptureSources.body_step (caller := caller) body known
        (SourceAnnotatedCaptureSources.fresh_payload payload closed fresh) closed cut selected unique absent
      have refinedInput : (refineContract allocated input answer).input = input := rfl
      exact ⟨exactErasure, by simpa only [exactErasure, refinedInput] using step⟩

theorem TypedClauseData.allocated_body {savedHints : Hints captured} {waitingHints : Hints tail}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (data : TypedClauseData operations policy contracts tables families required stack world outward actions phases owner parameter binder code argument input offered row
      answer allowed family saved waiting resumeEffects closeEffects)
    (allocated : SourceDependencyAnnotations.Contract)
    (fresh : contracts owner = none) (inputSame : allocated.input = input.erase)
    (answerSame : allocated.answer = answer.erase)
    (resumeSame : allocated.resumeEffects = resumeEffects) (closeSame : allocated.closeEffects = closeEffects)
    (heldSame : allocated.held = captured.held) (balance : allocated.closeDemand.Perm allocated.resumeDemand)
    (payload : ValueSummary operations policy contracts world (fun _ => none) payloadAllowed operand argument)
    (closed : ClosedValue operand.erase) :
    ∃ bodies : ∀ owner, Plan (family owner),
      (refineContract allocated input answer).erase = allocated ∧
      Matches tables families required (.live (owner := owner) savedHints waitingHints) stack.erase ∧
      Local outward actions phases world (bodies owner) (.live (owner := owner) saved waiting) ∧
      Pending outward actions phases world (.live (owner := owner) saved waiting) .nil ∧
      Body operations policy (contracts.insert owner (refineContract allocated input answer)) world allowed (.ticket binder owner)
        (fun _ => none) (code.subst parameter operand) answer ⟨owner, allocated.erase, offered.dispose, row⟩
        (signature (bodies owner)) := by
  cases data with
  | checked matched current pending source =>
      exact ⟨_, (TypedClauseDataAtPlan.checked matched current pending source).allocated_body allocated fresh
        inputSame answerSame resumeSame closeSame heldSame balance payload closed⟩

theorem capture_typed_data_exact [SourceScheduledChecks.DeclarationProjection admission certification] {hints : Hints scope} {forest : Forest hints}
    {plans : SourceDeclarationPlans.ClausePlans handler.clauses.erase (families handler.erase)}
    (physical : SourceAnnotatedRuntime.HandlerCut requested whole captured tail handler)
    (matched : Matches tables families required hints whole.erase)
    (source : SourceAnnotatedSources.Declarations operations policy contracts world (fun _ => none) allowed requested answer
      handler.clauses (tables handler.erase) plans)
    (selected : SourceAnnotatedRuntime.ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler.erase) = some offered)
    (rowAvailable : offered.row (ProtectionContexts.protectedMode captured.erase.erase) = some row)
    (declared : SourceDependencyCapture.lookupDependencies operation (families handler.erase) = some modes)
    (request : Local outward actions (OwnerPhaseTransitions.available (ownedTickets whole.erase)) world
      (.request (effect := requested) (operation := operation)) forest)
    (retained : Pending outward actions (OwnerPhaseTransitions.available (ownedTickets whole.erase)) world forest .nil)
    (fresh : actions owner = none) (absent : owner ∉ ownedTickets whole.erase)
    (operationKnown : operations requested operation = some (argument, input))
    (requirementsAtCapture : ∀ {capturedScope tailScope}
      {savedHints : Hints capturedScope} {waitingHints : Hints tailScope}
      (saved : Forest savedHints) (waiting : Forest waitingHints),
      SourceScheduledNeutral.Cut requested operation offered modes forest saved waiting →
      ∀ {family : Nat → Dependencies} {bodies : ∀ owner, Plan (family owner)},
      SourcePlannedRecipeDeclarations.Selected operation capturedScope.held plans parameter binder code.erase bodies →
      SourceScheduledRequirements.Satisfied outward (actions.insert owner code.erase.requiredActions)
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner) world
        (bodies owner) (.live (owner := owner) saved waiting)) :
    ∃ capturedScope tailScope resumeEffects closeEffects family,
      ∃ savedHints : Hints capturedScope, ∃ waitingHints : Hints tailScope,
      ∃ savedForest : Forest savedHints, ∃ waitingForest : Forest waitingHints,
      scope = capturedScope.append tailScope ∧ HEq hints (savedHints.append waitingHints) ∧ HEq forest (savedForest.append waitingForest) ∧
      SourceDependencyCapture.select requested operation scope = some (.handler capturedScope tailScope offered modes) ∧
      (code.erase.requiredActions.resume = true → resumeEffects = allowed) ∧
      (code.erase.requiredActions.dispose = true → closeEffects = allowed) ∧
      (SourceDependencyCapture.lookupDependencies operation (families handler.erase)).bind
        (SourceDependencyCapture.modeDependencies capturedScope.held) = some family ∧
      SourceScheduledNeutral.Cut requested operation offered modes forest savedForest waitingForest ∧
      ∃ bodies : ∀ owner, Plan (family owner),
      SourcePlannedRecipeDeclarations.Selected operation capturedScope.held plans parameter binder code.erase bodies ∧
      TypedClauseDataAtPlan operations policy contracts tables families required
        (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer captured handler.scope tail)
        world outward (actions.insert owner code.erase.requiredActions)
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner)
        owner parameter binder code argument input offered row answer allowed family
        savedForest waitingForest resumeEffects closeEffects bodies := by
  obtain ⟨capturedScope, tailScope, saved, waiting, cut, inside, outside, supplied⟩ :=
    SourcePlannedRuntimeCuts.matched_cut physical.erase matched found declared
  obtain ⟨savedForest, waitingForest, plannedCut⟩ := SourceScheduledNeutral.of_cut cut forest
  have rowAtScope : offered.row capturedScope.held = some row := by
    rw [inside.realizes.held]
    exact rowAvailable
  have consumed : OwnerPhaseTransitions.available (ownedTickets whole.erase) owner = .consumed := by
    simp [OwnerPhaseTransitions.available, absent]
  obtain ⟨actualArgument, actualInput, resumeEffects, closeEffects, family, bodies, known, resume, close,
    chosen, offeredFamily, checked, pending, body⟩ :=
    SourceAnnotatedCaptureSources.capture_body_from_requirements source selected found rowAtScope declared plannedCut
      request retained fresh consumed (requirementsAtCapture savedForest waitingForest plannedCut)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (operationKnown.symm.trans known))
  exact ⟨capturedScope, tailScope, resumeEffects, closeEffects, family, saved, waiting, savedForest, waitingForest, cut.reconstruct_scope, cut.hints, plannedCut.forest, cut.lookup, resume, close,
    chosen.lookup, plannedCut, bodies, chosen, .checked (.live inside outside) checked pending body⟩

theorem capture_typed_data [SourceScheduledChecks.DeclarationProjection admission certification] {hints : Hints scope} {forest : Forest hints}
    {plans : SourceDeclarationPlans.ClausePlans handler.clauses.erase (families handler.erase)}
    (physical : SourceAnnotatedRuntime.HandlerCut requested whole captured tail handler)
    (matched : Matches tables families required hints whole.erase)
    (source : SourceAnnotatedSources.Declarations operations policy contracts world (fun _ => none) allowed requested answer
      handler.clauses (tables handler.erase) plans)
    (selected : SourceAnnotatedRuntime.ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler.erase) = some offered)
    (rowAvailable : offered.row (ProtectionContexts.protectedMode captured.erase.erase) = some row)
    (declared : SourceDependencyCapture.lookupDependencies operation (families handler.erase) = some modes)
    (request : Local outward actions (OwnerPhaseTransitions.available (ownedTickets whole.erase)) world
      (.request (effect := requested) (operation := operation)) forest)
    (retained : Pending outward actions (OwnerPhaseTransitions.available (ownedTickets whole.erase)) world forest .nil)
    (fresh : actions owner = none) (absent : owner ∉ ownedTickets whole.erase)
    (operationKnown : operations requested operation = some (argument, input))
    (requirementsAtCapture : ∀ {capturedScope tailScope}
      {savedHints : Hints capturedScope} {waitingHints : Hints tailScope}
      (saved : Forest savedHints) (waiting : Forest waitingHints),
      SourceScheduledNeutral.Cut requested operation offered modes forest saved waiting →
      ∀ {family : Nat → Dependencies} {bodies : ∀ owner, Plan (family owner)},
      SourcePlannedRecipeDeclarations.Selected operation capturedScope.held plans parameter binder code.erase bodies →
      SourceScheduledRequirements.Satisfied outward (actions.insert owner code.erase.requiredActions)
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner) world
        (bodies owner) (.live (owner := owner) saved waiting)) :
    ∃ capturedScope tailScope resumeEffects closeEffects family,
      ∃ savedHints : Hints capturedScope, ∃ waitingHints : Hints tailScope,
      ∃ savedForest : Forest savedHints, ∃ waitingForest : Forest waitingHints,
      scope = capturedScope.append tailScope ∧ HEq hints (savedHints.append waitingHints) ∧ HEq forest (savedForest.append waitingForest) ∧
      SourceDependencyCapture.select requested operation scope = some (.handler capturedScope tailScope offered modes) ∧
      (code.erase.requiredActions.resume = true → resumeEffects = allowed) ∧
      (code.erase.requiredActions.dispose = true → closeEffects = allowed) ∧
      (SourceDependencyCapture.lookupDependencies operation (families handler.erase)).bind
        (SourceDependencyCapture.modeDependencies capturedScope.held) = some family ∧
      TypedClauseData operations policy contracts tables families required
        (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer captured handler.scope tail)
        world outward (actions.insert owner code.erase.requiredActions)
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner)
        owner parameter binder code argument input offered row answer allowed family
        savedForest waitingForest resumeEffects closeEffects := by
  obtain ⟨capturedScope, tailScope, resumeEffects, closeEffects, family, saved, waiting, savedForest, waitingForest,
    scopeSame, hintsSame, forestSame, lookup, resume, close, familyKnown, _, bodies, _, data⟩ :=
    capture_typed_data_exact physical matched source selected found rowAvailable declared request retained fresh absent
      operationKnown requirementsAtCapture
  exact ⟨capturedScope, tailScope, resumeEffects, closeEffects, family, saved, waiting, savedForest, waitingForest,
    scopeSame, hintsSame, forestSame, lookup, resume, close, familyKnown, data.forget⟩

end

/-- A single structural annotation for the actual selected clause supplies
the allocation obligation. General source typing and the existing capture,
refinement and payload-substitution proofs remain authoritative. -/
theorem capture_typed_data_from_annotation {hints : Hints scope} {forest : Forest hints}
    {plans : SourceDeclarationPlans.ClausePlans handler.clauses.erase (families handler.erase)}
    (physical : SourceAnnotatedRuntime.HandlerCut requested whole captured tail handler)
    (matched : Matches tables families required hints whole.erase)
    (source : SourceAnnotatedSources.Declarations operations policy contracts world (fun _ => none) allowed requested answer
      handler.clauses (tables handler.erase) plans)
    (selected : SourceAnnotatedRuntime.ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler.erase) = some offered)
    (rowAvailable : offered.row (ProtectionContexts.protectedMode captured.erase.erase) = some row)
    (declared : SourceDependencyCapture.lookupDependencies operation (families handler.erase) = some modes)
    (request : Local outward actions (OwnerPhaseTransitions.available (ownedTickets whole.erase)) world
      (.request (effect := requested) (operation := operation)) forest)
    (retained : Pending outward actions (OwnerPhaseTransitions.available (ownedTickets whole.erase)) world forest .nil)
    (fresh : actions owner = none) (absent : owner ∉ ownedTickets whole.erase)
    (operationKnown : operations requested operation = some (argument, input))
    (admission : SourceScheduledCaptureAnnotations.Capture world owner requested operation offered modes
      plans parameter binder code.erase forest)
    (validated : admission.Valid outward actions (OwnerPhaseTransitions.available (ownedTickets whole.erase))) :
    ∃ capturedScope tailScope resumeEffects closeEffects family,
      ∃ savedHints : Hints capturedScope, ∃ waitingHints : Hints tailScope,
      ∃ savedForest : Forest savedHints, ∃ waitingForest : Forest waitingHints,
      scope = capturedScope.append tailScope ∧ HEq hints (savedHints.append waitingHints) ∧ HEq forest (savedForest.append waitingForest) ∧
      SourceDependencyCapture.select requested operation scope = some (.handler capturedScope tailScope offered modes) ∧
      (code.erase.requiredActions.resume = true → resumeEffects = allowed) ∧
      (code.erase.requiredActions.dispose = true → closeEffects = allowed) ∧
      (SourceDependencyCapture.lookupDependencies operation (families handler.erase)).bind
        (SourceDependencyCapture.modeDependencies capturedScope.held) = some family ∧
      TypedClauseData operations policy contracts tables families required
        (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer captured handler.scope tail)
        world outward (actions.insert owner code.erase.requiredActions)
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner)
        owner parameter binder code argument input offered row answer allowed family
        savedForest waitingForest resumeEffects closeEffects := by
  apply capture_typed_data physical matched source selected found rowAvailable declared request retained fresh absent operationKnown
  intro actualCaptured actualTail actualSavedHints actualWaitingHints actualSaved actualWaiting actualCut actualFamily actualBodies chosen
  exact admission.requirements validated actualCut chosen

section
variable [admission : SourceScheduledChecks.DeclarationPolicy] [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]

theorem capture_typed_data_at_cut {hints : Hints scope} {forest : Forest hints}
    {plans : SourceDeclarationPlans.ClausePlans handler.clauses.erase (families handler.erase)}
    (physical : SourceAnnotatedRuntime.HandlerCut requested whole captured tail handler)
    (matched : Matches tables families required hints whole.erase)
    (source : SourceAnnotatedSources.Declarations operations policy contracts world (fun _ => none) allowed requested answer
      handler.clauses (tables handler.erase) plans)
    (selected : SourceAnnotatedRuntime.ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler.erase) = some offered)
    (rowAvailable : offered.row (ProtectionContexts.protectedMode captured.erase.erase) = some row)
    (declared : SourceDependencyCapture.lookupDependencies operation (families handler.erase) = some modes)
    (request : Local outward actions (OwnerPhaseTransitions.available (ownedTickets whole.erase)) world
      (.request (effect := requested) (operation := operation)) forest)
    (retained : Pending outward actions (OwnerPhaseTransitions.available (ownedTickets whole.erase)) world forest .nil)
    (fresh : actions owner = none) (absent : owner ∉ ownedTickets whole.erase)
    (operationKnown : operations requested operation = some (argument, input))
    (requirementsAtCapture : ∀ {capturedScope tailScope}
      {savedHints : Hints capturedScope} {waitingHints : Hints tailScope}
      (saved : Forest savedHints) (waiting : Forest waitingHints),
      SourceScheduledNeutral.Cut requested operation offered modes forest saved waiting →
      ∀ {family : Nat → Dependencies} {bodies : ∀ owner, Plan (family owner)},
      SourcePlannedRecipeDeclarations.Selected operation capturedScope.held plans parameter binder code.erase bodies →
      SourceScheduledRequirements.Satisfied outward (actions.insert owner code.erase.requiredActions)
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner) world
        (bodies owner) (.live (owner := owner) saved waiting))
    {actualSavedHints : Hints actualSavedScope} {actualWaitingHints : Hints actualWaitingScope}
    {actualSaved : Forest actualSavedHints} {actualWaiting : Forest actualWaitingHints}
    (actualCut : SourceScheduledNeutral.Cut requested operation offered modes forest actualSaved actualWaiting)
    (actualSelected : SourcePlannedRecipeDeclarations.Selected operation actualSavedScope.held plans
      parameter binder code.erase bodies) :
    ∃ resumeEffects closeEffects,
      (code.erase.requiredActions.resume = true → resumeEffects = allowed) ∧
      (code.erase.requiredActions.dispose = true → closeEffects = allowed) ∧
      TypedClauseDataAtPlan operations policy contracts tables families required
        (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer captured handler.scope tail)
        world outward (actions.insert owner code.erase.requiredActions)
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner)
        owner parameter binder code argument input offered row answer allowed _ actualSaved actualWaiting
        resumeEffects closeEffects bodies := by
  obtain ⟨capturedScope, tailScope, resumeEffects, closeEffects, family, savedHints, waitingHints, savedForest, waitingForest,
    scopeSame, hintsSame, forestSame, lookup, resume, close, familyKnown, plannedCut, chosenBodies, chosen, data⟩ :=
    capture_typed_data_exact physical matched source selected found rowAvailable declared request retained fresh absent operationKnown
      requirementsAtCapture
  cases Option.some.inj (plannedCut.erase.lookup.symm.trans actualCut.erase.lookup)
  obtain ⟨rfl, rfl⟩ := plannedCut.erase.unique actualCut.erase.hints
  obtain ⟨rfl, rfl⟩ := Forest.append_injective (eq_of_heq (plannedCut.forest.symm.trans actualCut.forest))
  obtain ⟨rfl, same⟩ := SourceScheduledClauseHandlers.selected_unique chosen actualSelected
  cases same
  exact ⟨resumeEffects, closeEffects, resume, close, data⟩

end

theorem capture_typed_data_at_selected {hints : Hints scope} {forest : Forest hints}
    {plans : SourceDeclarationPlans.ClausePlans handler.clauses.erase (families handler.erase)}
    (physical : SourceAnnotatedRuntime.HandlerCut requested whole captured tail handler)
    (matched : Matches tables families required hints whole.erase)
    (source : SourceAnnotatedSources.Declarations operations policy contracts world (fun _ => none) allowed requested answer
      handler.clauses (tables handler.erase) plans)
    (selected : SourceAnnotatedRuntime.ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler.erase) = some offered)
    (rowAvailable : offered.row (ProtectionContexts.protectedMode captured.erase.erase) = some row)
    (declared : SourceDependencyCapture.lookupDependencies operation (families handler.erase) = some modes)
    (request : Local outward actions (OwnerPhaseTransitions.available (ownedTickets whole.erase)) world
      (.request (effect := requested) (operation := operation)) forest)
    (retained : Pending outward actions (OwnerPhaseTransitions.available (ownedTickets whole.erase)) world forest .nil)
    (fresh : actions owner = none) (absent : owner ∉ ownedTickets whole.erase)
    (operationKnown : operations requested operation = some (argument, input))
    {actualSavedHints : Hints actualSavedScope} {actualWaitingHints : Hints actualWaitingScope}
    {actualSaved : Forest actualSavedHints} {actualWaiting : Forest actualWaitingHints}
    (actualCut : SourceScheduledNeutral.Cut requested operation offered modes forest actualSaved actualWaiting)
    (actualSelected : SourcePlannedRecipeDeclarations.Selected operation actualSavedScope.held plans
      parameter binder code.erase bodies)
    (annotation : SourceScheduledCapabilityAnnotations.Code world (bodies owner) (.live (owner := owner) actualSaved actualWaiting))
    (validated : annotation.Valid outward (actions.insert owner code.erase.requiredActions)
      (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner)) :
    ∃ resumeEffects closeEffects,
      (code.erase.requiredActions.resume = true → resumeEffects = allowed) ∧
      (code.erase.requiredActions.dispose = true → closeEffects = allowed) ∧
      TypedClauseDataAtPlan operations policy contracts tables families required
        (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer captured handler.scope tail)
        world outward (actions.insert owner code.erase.requiredActions)
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner)
        owner parameter binder code argument input offered row answer allowed _ actualSaved actualWaiting
        resumeEffects closeEffects bodies := by
  let admission : SourceScheduledCaptureAnnotations.Capture world owner requested operation offered modes
      plans parameter binder code.erase forest := .site actualCut actualSelected annotation
  apply capture_typed_data_at_cut physical matched source selected found rowAvailable declared request retained fresh absent
    operationKnown _ actualCut actualSelected
  intro savedScope waitingScope savedHints waitingHints saved waiting cut family bodies chosen
  exact admission.requirements validated cut chosen

end Ash.OneShot.SourceAnnotatedAllocationData


#print axioms Ash.OneShot.SourceAnnotatedAllocationData.TypedClauseData.erase

#print axioms Ash.OneShot.SourceAnnotatedAllocationData.TypedClauseData.allocated_body

#print axioms Ash.OneShot.SourceAnnotatedAllocationData.capture_typed_data

#print axioms Ash.OneShot.SourceAnnotatedAllocationData.capture_typed_data_from_annotation

#print axioms Ash.OneShot.SourceAnnotatedAllocationData.TypedClauseDataAtPlan.forget
#print axioms Ash.OneShot.SourceAnnotatedAllocationData.TypedClauseDataAtPlan.allocated_body
#print axioms Ash.OneShot.SourceAnnotatedAllocationData.capture_typed_data_exact

#print axioms Ash.OneShot.SourceAnnotatedAllocationData.capture_typed_data_at_selected

#print axioms Ash.OneShot.SourceAnnotatedAllocationData.capture_typed_data_at_cut

#print axioms Ash.OneShot.SourceAnnotatedAllocationData.TypedClauseDataAtPlan.capture_step

#print axioms Ash.OneShot.SourceAnnotatedAllocationData.TypedClauseData.at_plan
