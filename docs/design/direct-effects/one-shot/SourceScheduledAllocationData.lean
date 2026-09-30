import SourceScheduledClauses
import SourceScheduledCaptureClosing

/-! Retain the selected clause and its exact saved/waiting plan forests through
contract refinement and closed payload substitution. Erasure reuses the shared
allocator's earlier clause certificate. -/
namespace Ash.OneShot.SourceScheduledAllocationData
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations (Dependencies)
open SourcePlannedTyping (Value Environment Operations Contract Contracts)
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceContextualHintChecking (Matches)
open SourceScheduledChecks (Local Pending)
open SourcePlannedSources (Body ValueSummary refineContract)

section
variable [admission : SourceScheduledChecks.DeclarationPolicy] [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]

inductive TypedClauseData [admission : SourceScheduledChecks.DeclarationPolicy] [certification : SourcePlannedChecks.DeclarationPolicy] (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (families : SourceDependencyCapture.Families)
    (required : SourceContextualRechecking.Required) (stack : Stack)
    (world : List Nat) (outward : List Instance) (actions : Syntax.UsageTickets)
    (phases : OwnerPhaseTransitions.Phases) (owner parameter binder : Nat) (code : Code)
    (argument input : Value) (offered : ClauseContract) (row : Footprint) :
    Value → List Instance → (Nat → Dependencies) →
      {captured tail : SourceDependencyCapture.Scope} → {savedHints : Hints captured} → {waitingHints : Hints tail} →
      Forest savedHints → Forest waitingHints → List Instance → List Instance → Prop where
  | checked {bodies : ∀ owner, Plan (family owner)} {savedHints : Hints captured} {waitingHints : Hints tail}
      {saved : Forest savedHints} {waiting : Forest waitingHints}
      (matched : Matches tables families required (.live (owner := owner) savedHints waitingHints) stack)
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

theorem TypedClauseData.erase {savedHints : Hints captured} {waitingHints : Hints tail}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (data : TypedClauseData operations policy contracts tables families required stack world outward actions phases
      owner parameter binder code argument input offered row answer allowed family saved waiting resumeEffects closeEffects) :
    SourcePlannedAllocationData.TypedClauseData operations policy contracts tables families required stack world outward actions phases
      owner parameter binder code argument input offered row answer allowed family captured tail resumeEffects closeEffects := by
  cases data with
  | checked matched current pending source => exact .checked matched current.erase pending.erase source

omit [SourceScheduledChecks.DeclarationProjection admission certification] in
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
    (closed : ClosedValue operand) :
    ∃ bodies : ∀ owner, Plan (family owner),
      (refineContract allocated input answer).erase = allocated ∧
      Matches tables families required (.live (owner := owner) savedHints waitingHints) stack ∧
      Local outward actions phases world (bodies owner) (.live (owner := owner) saved waiting) ∧
      Pending outward actions phases world (.live (owner := owner) saved waiting) .nil ∧
      Body operations policy (contracts.insert owner (refineContract allocated input answer)) world allowed (.ticket binder owner)
        (fun _ => none) (code.subst parameter operand) answer ⟨owner, allocated.erase, offered.dispose, row⟩
        (signature (bodies owner)) := by
  cases data with
  | checked matched current pending source =>
      rename_i bodies
      have exactErasure := SourcePlannedSources.refine_contract_erase inputSame answerSame
      have body := source (refineContract allocated input answer) fresh rfl rfl resumeSame closeSame heldSame balance
      have substituted := SourcePlannedCaptureSubstitution.body_substitution body
        (SourcePlannedCaptureSubstitution.fresh_payload payload closed fresh) closed
      exact ⟨bodies, exactErasure, matched, current, pending,
        by simpa only [exactErasure] using substituted⟩

theorem capture_typed_data {hints : Hints scope} {forest : Forest hints}
    {plans : SourceDeclarationPlans.ClausePlans handler.clauses (families handler)}
    (physical : HandlerCut requested whole captured tail handler)
    (matched : Matches tables families required hints whole)
    (source : SourcePlannedSources.Declarations operations policy contracts world (fun _ => none) allowed requested answer
      handler.clauses (tables handler) plans)
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler) = some offered)
    (rowAvailable : offered.row (ProtectionContexts.protectedMode captured.erase) = some row)
    (declared : SourceDependencyCapture.lookupDependencies operation (families handler) = some modes)
    (request : Local outward actions (OwnerPhaseTransitions.available (ownedTickets whole)) world
      (.request (effect := requested) (operation := operation)) forest)
    (retained : Pending outward actions (OwnerPhaseTransitions.available (ownedTickets whole)) world forest .nil)
    (fresh : actions owner = none) (absent : owner ∉ ownedTickets whole)
    (operationKnown : operations requested operation = some (argument, input))
    (requirementsAtCapture : ∀ {capturedScope tailScope}
      {savedHints : Hints capturedScope} {waitingHints : Hints tailScope}
      (saved : Forest savedHints) (waiting : Forest waitingHints),
      SourceScheduledNeutral.Cut requested operation offered modes forest saved waiting →
      ∀ {family : Nat → Dependencies} {bodies : ∀ owner, Plan (family owner)},
      SourcePlannedRecipeDeclarations.Selected operation capturedScope.held plans parameter binder code bodies →
      SourceScheduledRequirements.Satisfied outward (actions.insert owner code.requiredActions)
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole)) owner) world
        (bodies owner) (.live (owner := owner) saved waiting)) :
    ∃ capturedScope tailScope resumeEffects closeEffects family,
      ∃ savedHints : Hints capturedScope, ∃ waitingHints : Hints tailScope,
      ∃ savedForest : Forest savedHints, ∃ waitingForest : Forest waitingHints,
      scope = capturedScope.append tailScope ∧ HEq hints (savedHints.append waitingHints) ∧ HEq forest (savedForest.append waitingForest) ∧
      SourceDependencyCapture.select requested operation scope = some (.handler capturedScope tailScope offered modes) ∧
      (code.requiredActions.resume = true → resumeEffects = allowed) ∧
      (code.requiredActions.dispose = true → closeEffects = allowed) ∧
      (SourceDependencyCapture.lookupDependencies operation (families handler)).bind
        (SourceDependencyCapture.modeDependencies capturedScope.held) = some family ∧
      TypedClauseData operations policy contracts tables families required
        (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer captured handler.scope tail)
        world outward (actions.insert owner code.requiredActions)
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole)) owner)
        owner parameter binder code argument input offered row answer allowed family
        savedForest waitingForest resumeEffects closeEffects := by
  obtain ⟨capturedScope, tailScope, saved, waiting, cut, inside, outside, supplied⟩ :=
    SourcePlannedRuntimeCuts.matched_cut physical matched found declared
  obtain ⟨savedForest, waitingForest, plannedCut⟩ := SourceScheduledNeutral.of_cut cut forest
  have rowAtScope : offered.row capturedScope.held = some row := by
    rw [inside.realizes.held]
    exact rowAvailable
  have consumed : OwnerPhaseTransitions.available (ownedTickets whole) owner = .consumed := by
    simp [OwnerPhaseTransitions.available, absent]
  obtain ⟨actualArgument, actualInput, resumeEffects, closeEffects, family, bodies, known, resume, close,
    chosen, offeredFamily, checked, pending, body⟩ :=
    SourceScheduledClauses.capture_body_from_requirements source selected found rowAtScope declared plannedCut
      request retained fresh consumed (requirementsAtCapture savedForest waitingForest plannedCut)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (operationKnown.symm.trans known))
  exact ⟨capturedScope, tailScope, resumeEffects, closeEffects, family, saved, waiting, savedForest, waitingForest, cut.reconstruct_scope, cut.hints, plannedCut.forest, cut.lookup, resume, close,
    chosen.lookup, .checked (.live inside outside) checked pending body⟩

end

/- The established recipe judgment discharges the contextual requirements
at an authenticated capture. This bridge is reusable by entry and allocation;
it does not restrict the general allocation theorem to recipe-shaped clauses. -/
section
variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]

theorem capture_requirements_from_recipe_with {hints : Hints scope} {forest : Forest hints}
    (admitRecipe : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      SourcePlannedRecipeDeclarations.Declarations required plans → admission.accepts outward required plans)
    (certifyRecipe : ∀ {world clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      SourcePlannedRecipeDeclarations.Declarations required plans →
      SourcePlannedChecks.CertifiedClauses (evidence := certification) outward world plans)
    {plans : SourceDeclarationPlans.ClausePlans handler.clauses (families handler)}
    (physical : HandlerCut requested whole captured tail handler)
    (matched : Matches tables families required hints whole)
    (recipes : SourcePlannedRecipeDeclarations.Declarations (required handler) plans)
    (clauseModes : SourceTemplates.ClauseModes handler.clauses (tables handler))
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler) = some offered)
    (declared : SourceDependencyCapture.lookupDependencies operation (families handler) = some modes)
    (request : Local outward actions (OwnerPhaseTransitions.available (ownedTickets whole)) world
      (.request (effect := requested) (operation := operation)) forest)
    (retained : Pending outward actions (OwnerPhaseTransitions.available (ownedTickets whole)) world forest .nil)
    (compatible : SourceContextualHintChecking.Compatible hints .nil)
    (fresh : actions owner = none) (absent : owner ∉ ownedTickets whole)
    {savedHints : Hints capturedScope} {waitingHints : Hints tailScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (cut : SourceScheduledNeutral.Cut requested operation offered modes forest saved waiting)
    {family : Nat → Dependencies} {bodies : ∀ owner, Plan (family owner)}
    (chosen : SourcePlannedRecipeDeclarations.Selected operation capturedScope.held plans parameter binder code bodies) :
    SourceScheduledRequirements.Satisfied outward (actions.insert owner code.requiredActions)
      (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole)) owner) world
      (bodies owner) (.live (owner := owner) saved waiting) := by
  obtain ⟨actualScope, actualTail, actualSaved, actualWaiting, actualCut, inside, outside, supplied⟩ :=
    SourcePlannedRuntimeCuts.matched_cut physical matched found declared
  cases Option.some.inj (actualCut.lookup.symm.trans cut.erase.lookup)
  obtain ⟨actual, actualFound, disposalPermission⟩ := SourceTemplates.selected_clause_mode selected clauseModes
  cases Option.some.inj (found.symm.trans actualFound)
  have consumed : OwnerPhaseTransitions.available (ownedTickets whole) owner = .consumed := by
    simp [OwnerPhaseTransitions.available, absent]
  obtain ⟨familySame, checked, pending⟩ := SourceScheduledClauses.declaration_capture_with admitRecipe certifyRecipe recipes chosen declared cut
    request retained compatible fresh consumed disposalPermission (supplied compatible)
  intro requirement atWorld atScope atHints atForest site
  exact SourceScheduledRequirements.necessary checked site

end

theorem capture_requirements_from_recipe {hints : Hints scope} {forest : Forest hints}
    {plans : SourceDeclarationPlans.ClausePlans handler.clauses (families handler)}
    (physical : HandlerCut requested whole captured tail handler)
    (matched : Matches tables families required hints whole)
    (recipes : SourcePlannedRecipeDeclarations.Declarations (required handler) plans)
    (clauseModes : SourceTemplates.ClauseModes handler.clauses (tables handler))
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler) = some offered)
    (declared : SourceDependencyCapture.lookupDependencies operation (families handler) = some modes)
    (request : Local outward actions (OwnerPhaseTransitions.available (ownedTickets whole)) world
      (.request (effect := requested) (operation := operation)) forest)
    (retained : Pending outward actions (OwnerPhaseTransitions.available (ownedTickets whole)) world forest .nil)
    (compatible : SourceContextualHintChecking.Compatible hints .nil)
    (fresh : actions owner = none) (absent : owner ∉ ownedTickets whole)
    {savedHints : Hints capturedScope} {waitingHints : Hints tailScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (cut : SourceScheduledNeutral.Cut requested operation offered modes forest saved waiting)
    {family : Nat → Dependencies} {bodies : ∀ owner, Plan (family owner)}
    (chosen : SourcePlannedRecipeDeclarations.Selected operation capturedScope.held plans parameter binder code bodies) :
    SourceScheduledRequirements.Satisfied outward (actions.insert owner code.requiredActions)
      (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole)) owner) world
      (bodies owner) (.live (owner := owner) saved waiting) :=
  capture_requirements_from_recipe_with (fun checked => checked) (fun checked => checked.certified)
    physical matched recipes clauseModes selected found declared request retained compatible fresh absent cut chosen

end Ash.OneShot.SourceScheduledAllocationData

#print axioms Ash.OneShot.SourceScheduledAllocationData.TypedClauseData.erase
#print axioms Ash.OneShot.SourceScheduledAllocationData.TypedClauseData.allocated_body
#print axioms Ash.OneShot.SourceScheduledAllocationData.capture_typed_data

#print axioms Ash.OneShot.SourceScheduledAllocationData.capture_requirements_from_recipe

#print axioms Ash.OneShot.SourceScheduledAllocationData.capture_requirements_from_recipe_with
