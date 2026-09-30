import SourcePlannedCaptureEntry

/-! Retain the selected synchronized clause through the shared allocation
proof. Its indices fix the answer, family, scopes and effect interfaces. The
allocator's contract is refined without changing any ownership or row field. -/
namespace Ash.OneShot.SourcePlannedAllocationData
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations (Dependencies)
open SourcePlannedTyping (Value Environment Operations Contract Contracts)
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceContextualHints (Hints)
open SourceContextualHintChecking (Matches)
open SourcePlannedChecks (Local Pending)
open SourcePlannedSources (Body ValueSummary refineContract)

theorem body_erase {checking : SourcePlanSignatures.Signature dependencies}
    (source : Body operations policy contracts world allowed scope environment code answer header checking) :
    SourceDependencyAnnotations.Body operations.erase policy contracts.erase world allowed scope environment.erase
      code answer.erase header dependencies := by
  cases source with
  | typed expression rows closingRows => exact .typed (SourcePlannedSources.expression_erase expression) rows

section
variable [certification : SourcePlannedChecks.DeclarationPolicy]

/-- These are retained source and checking witnesses, not a new admission rule.
The constructor retains the same actual plan for its source body and checks. -/
inductive TypedClauseData [certification : SourcePlannedChecks.DeclarationPolicy] (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (families : SourceDependencyCapture.Families)
    (required : SourceContextualRechecking.Required) (stack : Stack)
    (world : List Nat) (outward : List Instance) (actions : Syntax.UsageTickets)
    (phases : OwnerPhaseTransitions.Phases) (owner parameter binder : Nat) (code : Code)
    (argument input : Value) (offered : ClauseContract) (row : Footprint) :
    Value → List Instance → (Nat → Dependencies) →
      SourceDependencyCapture.Scope → SourceDependencyCapture.Scope → List Instance → List Instance → Prop where
  | checked {bodies : ∀ owner, Plan (family owner)} {saved : Hints captured} {waiting : Hints tail}
      (matched : Matches tables families required (.live (owner := owner) saved waiting) stack)
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
        answer allowed family captured tail resumeEffects closeEffects

/-- The legacy allocator sees an erased answer. Its certificate retains the
exact refined answer and the corresponding typed clause data together. -/
def ClauseData (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (families : SourceDependencyCapture.Families)
    (required : SourceContextualRechecking.Required) (stack : Stack)
    (world : List Nat) (outward : List Instance) (actions : Syntax.UsageTickets)
    (phases : OwnerPhaseTransitions.Phases) (owner parameter binder : Nat) (code : Code)
    (argument input : Value) (offered : ClauseContract) (row : Footprint)
    (oldAnswer : SourceDependencyAnnotations.Value) (allowed : List Instance) (family : Nat → Dependencies)
    (captured tail : SourceDependencyCapture.Scope) (resumeEffects closeEffects : List Instance) : Prop :=
  ∃ answer : Value, answer.erase = oldAnswer ∧
    TypedClauseData operations policy contracts tables families required stack world outward actions phases
      owner parameter binder code argument input offered row answer allowed family captured tail resumeEffects closeEffects

end

/-- Construct retained allocation data from the actual cut and structural
source admission. The source-body family comes from the selected declaration. -/
theorem capture_typed_data {hints : Hints scope}
    {plans : SourceDeclarationPlans.ClausePlans handler.clauses (families handler)}
    (physical : HandlerCut requested whole captured tail handler)
    (matched : Matches tables families required hints whole)
    (source : SourcePlannedSources.Declarations operations policy contracts world (fun _ => none) allowed requested answer
      handler.clauses (tables handler) plans)
    (recipes : SourcePlannedRecipeDeclarations.Declarations (required handler) plans)
    (clauseModes : SourceTemplates.ClauseModes handler.clauses (tables handler))
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler) = some offered)
    (rowAvailable : offered.row (ProtectionContexts.protectedMode captured.erase) = some row)
    (declared : SourceDependencyCapture.lookupDependencies operation (families handler) = some modes)
    (request : Local outward actions (OwnerPhaseTransitions.available (ownedTickets whole)) world
      (.request (effect := requested) (operation := operation)) hints)
    (retained : Pending outward actions (OwnerPhaseTransitions.available (ownedTickets whole)) world hints .nil)
    (compatible : SourceContextualHintChecking.Compatible hints .nil)
    (fresh : actions owner = none) (absent : owner ∉ ownedTickets whole)
    (operationKnown : operations requested operation = some (argument, input)) :
    ∃ capturedScope tailScope resumeEffects closeEffects family,
      scope = capturedScope.append tailScope ∧
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
        capturedScope tailScope resumeEffects closeEffects := by
  obtain ⟨capturedScope, tailScope, saved, waiting, cut, inside, outside, supplied⟩ :=
    SourcePlannedRuntimeCuts.matched_cut physical matched found declared
  have rowAtScope : offered.row capturedScope.held = some row := by
    rw [inside.realizes.held]
    exact rowAvailable
  have consumed : OwnerPhaseTransitions.available (ownedTickets whole) owner = .consumed := by
    simp [OwnerPhaseTransitions.available, absent]
  obtain ⟨actualArgument, actualInput, resumeEffects, closeEffects, family, bodies, known, resume, close,
    chosen, offeredFamily, checked, pending, body⟩ :=
    SourcePlannedSelectedSources.capture_body source recipes clauseModes selected found rowAtScope declared cut
      request retained compatible fresh consumed (supplied compatible)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (operationKnown.symm.trans known))
  exact ⟨capturedScope, tailScope, resumeEffects, closeEffects, family, cut.reconstruct_scope, cut.lookup, resume, close,
    chosen.lookup, .checked (.live inside outside) checked pending body⟩

theorem capture_data {hints : Hints scope}
    {plans : SourceDeclarationPlans.ClausePlans handler.clauses (families handler)}
    (physical : HandlerCut requested whole captured tail handler)
    (matched : Matches tables families required hints whole)
    (source : SourcePlannedSources.Declarations operations policy contracts world (fun _ => none) allowed requested answer
      handler.clauses (tables handler) plans)
    (recipes : SourcePlannedRecipeDeclarations.Declarations (required handler) plans)
    (clauseModes : SourceTemplates.ClauseModes handler.clauses (tables handler))
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler) = some offered)
    (rowAvailable : offered.row (ProtectionContexts.protectedMode captured.erase) = some row)
    (declared : SourceDependencyCapture.lookupDependencies operation (families handler) = some modes)
    (request : Local outward actions (OwnerPhaseTransitions.available (ownedTickets whole)) world
      (.request (effect := requested) (operation := operation)) hints)
    (retained : Pending outward actions (OwnerPhaseTransitions.available (ownedTickets whole)) world hints .nil)
    (compatible : SourceContextualHintChecking.Compatible hints .nil)
    (fresh : actions owner = none) (absent : owner ∉ ownedTickets whole)
    (operationKnown : operations requested operation = some (argument, input)) :
    ∃ capturedScope tailScope resumeEffects closeEffects family,
      scope = capturedScope.append tailScope ∧
      SourceDependencyCapture.select requested operation scope = some (.handler capturedScope tailScope offered modes) ∧
      (code.requiredActions.resume = true → resumeEffects = allowed) ∧
      (code.requiredActions.dispose = true → closeEffects = allowed) ∧
      (SourceDependencyCapture.lookupDependencies operation (families handler)).bind
        (SourceDependencyCapture.modeDependencies capturedScope.held) = some family ∧
      ClauseData operations policy contracts tables families required
        (.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer captured handler.scope tail)
        world outward (actions.insert owner code.requiredActions)
        (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole)) owner)
        owner parameter binder code argument input offered row answer.erase allowed family
        capturedScope tailScope resumeEffects closeEffects := by
  obtain ⟨capturedScope, tailScope, resumeEffects, closeEffects, family, same, located, resume, close, chosen, data⟩ :=
    capture_typed_data physical matched source recipes clauseModes selected found rowAvailable declared
      request retained compatible fresh absent operationKnown
  exact ⟨capturedScope, tailScope, resumeEffects, closeEffects, family, same, located, resume, close, chosen,
    answer, rfl, data⟩

section
variable [certification : SourcePlannedChecks.DeclarationPolicy]

/-- The older interface can instantiate its exact contract by refining only
the selected value annotations. Erasure is equality, not a weaker simulation. -/
theorem ClauseData.erase_checks
    (data : ClauseData operations policy contracts tables families required stack world outward actions phases owner parameter binder code argument input offered row
      oldAnswer allowed family captured tail resumeEffects closeEffects) :
    SourceDependencySchemes.Checked outward actions phases world (family owner) (.live owner captured tail) ∧
    SourceDependencySchemes.Retained outward actions phases world (.live owner captured tail) .nil := by
  obtain ⟨answer, same, data⟩ := data
  cases data with
  | checked matched current pending source => exact ⟨current.erase, pending.erase⟩

theorem ClauseData.erase_body
    (data : ClauseData operations policy contracts tables families required stack world outward actions phases owner parameter binder code argument input offered row
      oldAnswer allowed family captured tail resumeEffects closeEffects)
    (allocated : SourceDependencyAnnotations.Contract)
    (fresh : contracts.erase owner = none) (inputSame : allocated.input = input.erase)
    (answerSame : allocated.answer = oldAnswer)
    (resumeSame : allocated.resumeEffects = resumeEffects) (closeSame : allocated.closeEffects = closeEffects)
    (heldSame : allocated.held = captured.held) (balance : allocated.closeDemand.Perm allocated.resumeDemand) :
    SourceDependencyAnnotations.Body operations.erase policy (contracts.erase.insert owner allocated) world allowed (.ticket binder owner)
      (SourceDependencyAnnotations.Environment.empty.extend parameter argument.erase) code oldAnswer
      ⟨owner, allocated.erase, offered.dispose, row⟩ (family owner) := by
  obtain ⟨answer, rfl, data⟩ := data
  cases data with
  | checked matched current pending source =>
      rename_i bodies saved waiting
      have absent : contracts owner = none := by
        cases known : contracts owner with
        | none => rfl
        | some contract => simp [Contracts.erase, known] at fresh
      have exactErasure := SourcePlannedSources.refine_contract_erase inputSame answerSame
      have body := source (refineContract allocated input answer) absent rfl rfl resumeSame closeSame heldSame balance
      have erased := body_erase body
      have emptyErasure : Environment.erase (fun _ => none) = SourceDependencyAnnotations.Environment.empty := rfl
      rw [SourcePlannedTyping.contracts_erase_insert, exactErasure,
        SourcePlannedTyping.environment_erase_extend, emptyErasure] at erased
      exact erased

/-- Refine the contract actually returned by allocation. Every owner demand,
effect interface and row is unchanged, and the closed payload is substituted
into the original synchronized clause at its retained plan signature. -/
theorem TypedClauseData.allocated_body
    (data : TypedClauseData operations policy contracts tables families required stack world outward actions phases owner parameter binder code argument input offered row
      answer allowed family captured tail resumeEffects closeEffects)
    (allocated : SourceDependencyAnnotations.Contract)
    (fresh : contracts owner = none) (inputSame : allocated.input = input.erase)
    (answerSame : allocated.answer = answer.erase)
    (resumeSame : allocated.resumeEffects = resumeEffects) (closeSame : allocated.closeEffects = closeEffects)
    (heldSame : allocated.held = captured.held) (balance : allocated.closeDemand.Perm allocated.resumeDemand)
    (payload : ValueSummary operations policy contracts world (fun _ => none) payloadAllowed operand argument)
    (closed : ClosedValue operand) :
    ∃ bodies : ∀ owner, Plan (family owner), ∃ (saved : Hints captured) (waiting : Hints tail),
      (refineContract allocated input answer).erase = allocated ∧
      Matches tables families required (.live (owner := owner) saved waiting) stack ∧
      Local outward actions phases world (bodies owner) (.live (owner := owner) saved waiting) ∧
      Pending outward actions phases world (.live (owner := owner) saved waiting) .nil ∧
      Body operations policy (contracts.insert owner (refineContract allocated input answer)) world allowed (.ticket binder owner)
        (fun _ => none) (code.subst parameter operand) answer ⟨owner, allocated.erase, offered.dispose, row⟩
        (signature (bodies owner)) := by
  cases data with
  | checked matched current pending source =>
      rename_i bodies saved waiting
      have exactErasure := SourcePlannedSources.refine_contract_erase inputSame answerSame
      have body := source (refineContract allocated input answer) fresh rfl rfl resumeSame closeSame heldSame balance
      have substituted := SourcePlannedCaptureSubstitution.body_substitution body
        (SourcePlannedCaptureSubstitution.fresh_payload payload closed fresh) closed
      exact ⟨bodies, saved, waiting, exactErasure, matched, current, pending,
        by simpa only [exactErasure] using substituted⟩

theorem ClauseData.allocated_body
    (data : ClauseData operations policy contracts tables families required stack world outward actions phases owner parameter binder code argument input offered row
      oldAnswer allowed family captured tail resumeEffects closeEffects)
    (allocated : SourceDependencyAnnotations.Contract)
    (fresh : contracts owner = none) (inputSame : allocated.input = input.erase)
    (answerSame : allocated.answer = oldAnswer)
    (resumeSame : allocated.resumeEffects = resumeEffects) (closeSame : allocated.closeEffects = closeEffects)
    (heldSame : allocated.held = captured.held) (balance : allocated.closeDemand.Perm allocated.resumeDemand)
    (payload : ValueSummary operations policy contracts world (fun _ => none) payloadAllowed operand argument)
    (closed : ClosedValue operand) :
    ∃ answer : Value, ∃ bodies : ∀ owner, Plan (family owner), ∃ (saved : Hints captured) (waiting : Hints tail),
      answer.erase = oldAnswer ∧ (refineContract allocated input answer).erase = allocated ∧
      Matches tables families required (.live (owner := owner) saved waiting) stack ∧
      Local outward actions phases world (bodies owner) (.live (owner := owner) saved waiting) ∧
      Pending outward actions phases world (.live (owner := owner) saved waiting) .nil ∧
      Body operations policy (contracts.insert owner (refineContract allocated input answer)) world allowed (.ticket binder owner)
        (fun _ => none) (code.subst parameter operand) answer ⟨owner, allocated.erase, offered.dispose, row⟩
        (signature (bodies owner)) := by
  obtain ⟨answer, rfl, data⟩ := data
  obtain ⟨bodies, saved, waiting, exactErasure, matched, current, pending, body⟩ :=
    data.allocated_body allocated fresh inputSame answerSame resumeSame closeSame heldSame balance payload closed
  exact ⟨answer, bodies, saved, waiting, rfl, exactErasure, matched, current, pending, body⟩

end

end Ash.OneShot.SourcePlannedAllocationData

#print axioms Ash.OneShot.SourcePlannedAllocationData.body_erase
#print axioms Ash.OneShot.SourcePlannedAllocationData.capture_data
#print axioms Ash.OneShot.SourcePlannedAllocationData.ClauseData.erase_checks
#print axioms Ash.OneShot.SourcePlannedAllocationData.ClauseData.erase_body
#print axioms Ash.OneShot.SourcePlannedAllocationData.ClauseData.allocated_body

#print axioms Ash.OneShot.SourcePlannedAllocationData.capture_typed_data
#print axioms Ash.OneShot.SourcePlannedAllocationData.TypedClauseData.allocated_body
