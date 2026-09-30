import SourceAnnotatedRuntimeCaptureSplitting

/-! Exact clause selection retains annotated source at the same actual plan.
Existing structural scheduling, contract extension and substitution proofs
supply capture preparation; no successor source is independently assumed. -/
namespace Ash.OneShot.SourceAnnotatedCaptureSources
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations (Dependencies)
open SourceDeclarationPlans (Plan ClausePlans)
open SourcePlanSignatures (signature)
open SourcePlannedRecipeDeclarations (Selected)
open SourcePlannedTyping (Environment Contract)
open SourceDependencyCapture (lookupDependencies modeDependencies)
open SourceContextualHints (Hints checkRequirements)
open SourceContextualHintChecking (Compatible)
open SourceRetainedPlans (Forest)
open SourceScheduledChecks (Local Pending)
open OwnerPhaseTransitions (introduce)
open SourceAnnotatedSources (Body ValueSummary)

theorem selected_body {plans : ClausePlans clauses.erase families}
    (source : SourceAnnotatedSources.Declarations operations policy contracts world environment allowed requested answer clauses table plans)
    (selected : SourceAnnotatedRuntime.ClauseAt operation clauses parameter binder code)
    (found : lookup operation table = some offered)
    (available : offered.row held = some row) :
    ∃ argument input resumeEffects closeEffects, ∃ (family : Nat → Dependencies) (bodies : ∀ owner, Plan (family owner)),
      operations requested operation = some (argument, input) ∧
      (code.erase.requiredActions.resume = true → resumeEffects = allowed) ∧
      (code.erase.requiredActions.dispose = true → closeEffects = allowed) ∧
      Selected operation held plans parameter binder code.erase bodies ∧
      ∀ owner (contract : Contract), contracts owner = none →
        contract.input = input → contract.answer = answer →
        contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
        contract.held = held → contract.closeDemand.Perm contract.resumeDemand →
        SourceAnnotatedSources.Body operations policy (contracts.insert owner contract) world allowed (.ticket binder owner)
          (environment.extend parameter argument) code answer ⟨owner, contract.erase.erase, offered.dispose, row⟩
          (signature (bodies owner)) := by
  induction selected generalizing table families with
  | hit => cases source with
    | cons known ordinary protectedMode rest =>
        simp only [lookup, if_true] at found
        cases Option.some.inj found
        cases held with
        | false =>
            simp [ClauseContract.row] at available
            cases available ▸ ordinary with
            | available resumeInterface closeInterface body =>
                exact ⟨_, _, _, _, _, _, known, resumeInterface, closeInterface, .ordinary, body⟩
        | true =>
            simp [ClauseContract.row] at available
            cases available ▸ protectedMode with
            | available resumeInterface closeInterface body =>
                exact ⟨_, _, _, _, _, _, known, resumeInterface, closeInterface, .protectedMode, body⟩
  | pass different next ih => cases source with
    | cons known ordinary protectedMode rest =>
        obtain ⟨argument, input, resumeEffects, closeEffects, family, bodies, known, resume, close, chosen, body⟩ :=
          ih rest (by simpa only [lookup, if_neg different] using found)
        exact ⟨argument, input, resumeEffects, closeEffects, family, bodies, known, resume, close,
          .pass different chosen, body⟩

/-- The actual source-selected plan may use every constructor. Its explicit
site obligations are checked at the captured forest; no restricted recipe or
complete successor-state premise occurs in this rule. Deriving the obligations
at each source request remains a separate admission obligation. -/
theorem capture_body_from_requirements
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    [SourceScheduledChecks.DeclarationProjection admission certification] {plans : ClausePlans clauses.erase families}
    {hints : Hints scope} {savedHints : Hints captured} {waitingHints : Hints tail}
    {forest : Forest hints} {saved : Forest savedHints} {waiting : Forest waitingHints}
    (source : SourceAnnotatedSources.Declarations operations policy contracts world environment allowed requested answer clauses table plans)
    (selected : SourceAnnotatedRuntime.ClauseAt operation clauses parameter binder code)
    (found : lookup operation table = some offered)
    (available : offered.row captured.held = some row)
    (declared : lookupDependencies operation families = some modes)
    (cut : SourceScheduledNeutral.Cut requested operation offered modes forest saved waiting)
    (request : Local outward actions phases world (.request (effect := requested) (operation := operation)) forest)
    (retained : Pending outward actions phases world forest .nil)
    (fresh : actions owner = none) (consumed : phases owner = .consumed)
    (supplied : ∀ {family : Nat → Dependencies} {bodies : ∀ owner, Plan (family owner)},
      Selected operation captured.held plans parameter binder code.erase bodies →
      SourceScheduledRequirements.Satisfied outward (actions.insert owner code.erase.requiredActions)
        (introduce phases owner) world (bodies owner) (.live (owner := owner) saved waiting)) :
    ∃ argument input resumeEffects closeEffects, ∃ (family : Nat → Dependencies) (bodies : ∀ owner, Plan (family owner)),
      operations requested operation = some (argument, input) ∧
      (code.erase.requiredActions.resume = true → resumeEffects = allowed) ∧
      (code.erase.requiredActions.dispose = true → closeEffects = allowed) ∧
      Selected operation captured.held plans parameter binder code.erase bodies ∧
      modeDependencies captured.held modes = some family ∧
      Local outward (actions.insert owner code.erase.requiredActions) (introduce phases owner) world
        (bodies owner) (.live (owner := owner) saved waiting) ∧
      Pending outward (actions.insert owner code.erase.requiredActions) (introduce phases owner) world
        (.live (owner := owner) saved waiting) .nil ∧
      ∀ (contract : Contract), contracts owner = none →
        contract.input = input → contract.answer = answer →
        contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
        contract.held = captured.held → contract.closeDemand.Perm contract.resumeDemand →
        SourceAnnotatedSources.Body operations policy (contracts.insert owner contract) world allowed (.ticket binder owner)
          (environment.extend parameter argument) code answer ⟨owner, contract.erase.erase, offered.dispose, row⟩
          (signature (bodies owner)) := by
  obtain ⟨argument, input, resumeEffects, closeEffects, family, bodies, known, resume, close, chosen, body⟩ :=
    selected_body source selected found available
  obtain ⟨live, inside, outside, disposal⟩ :=
    SourceScheduledCapturePrep.captured_checks cut request retained fresh consumed
  have offeredFamily : modeDependencies captured.held modes = some family := by
    simpa only [declared, Option.bind_some] using chosen.lookup
  exact ⟨argument, input, resumeEffects, closeEffects, family, bodies, known, resume, close,
    chosen, offeredFamily, SourceScheduledRequirements.compile _ _ _ (supplied chosen), live, body owner⟩

/-- Source typing and execution checking now select the same actual clause
plan. This is a capture component, before clause substitution and runtime-store
integration; it does not assert preservation of an entire runtime state. -/
theorem capture_body {plans : ClausePlans clauses.erase families}
    {hints : Hints scope} {savedHints : Hints captured} {waitingHints : Hints tail}
    {forest : Forest hints} {saved : Forest savedHints} {waiting : Forest waitingHints}
    (source : SourceAnnotatedSources.Declarations operations policy contracts world environment allowed requested answer clauses table plans)
    (recipes : SourcePlannedRecipeDeclarations.Declarations required plans)
    (clauseModes : SourceTemplates.ClauseModes clauses.erase table)
    (selected : SourceAnnotatedRuntime.ClauseAt operation clauses parameter binder code)
    (found : lookup operation table = some offered)
    (available : offered.row captured.held = some row)
    (declared : lookupDependencies operation families = some modes)
    (cut : SourceScheduledNeutral.Cut requested operation offered modes forest saved waiting)
    (request : Local outward actions phases world (.request (effect := requested) (operation := operation)) forest)
    (retained : Pending outward actions phases world forest .nil)
    (compatible : Compatible hints .nil)
    (fresh : actions owner = none) (consumed : phases owner = .consumed)
    (supplied : checkRequirements tail required = true) :
    ∃ argument input resumeEffects closeEffects, ∃ (family : Nat → Dependencies) (bodies : ∀ owner, Plan (family owner)),
      operations requested operation = some (argument, input) ∧
      (code.erase.requiredActions.resume = true → resumeEffects = allowed) ∧
      (code.erase.requiredActions.dispose = true → closeEffects = allowed) ∧
      Selected operation captured.held plans parameter binder code.erase bodies ∧
      modeDependencies captured.held modes = some family ∧
      Local outward (actions.insert owner code.erase.requiredActions) (introduce phases owner) world
        (bodies owner) (.live (owner := owner) saved waiting) ∧
      Pending outward (actions.insert owner code.erase.requiredActions) (introduce phases owner) world
        (.live (owner := owner) saved waiting) .nil ∧
      ∀ (contract : Contract), contracts owner = none →
        contract.input = input → contract.answer = answer →
        contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
        contract.held = captured.held → contract.closeDemand.Perm contract.resumeDemand →
        SourceAnnotatedSources.Body operations policy (contracts.insert owner contract) world allowed (.ticket binder owner)
          (environment.extend parameter argument) code answer ⟨owner, contract.erase.erase, offered.dispose, row⟩
          (signature (bodies owner)) := by
  apply capture_body_from_requirements source selected found available declared cut request retained fresh consumed
  intro family bodies chosen
  obtain ⟨actual, actualFound, disposalPermission⟩ := SourceTemplates.selected_clause_mode selected.erase clauseModes
  cases Option.some.inj (found.symm.trans actualFound)
  obtain ⟨offeredFamily, checked, pending⟩ := SourceScheduledClauses.declaration_capture recipes chosen declared cut request retained compatible fresh consumed
    disposalPermission supplied
  exact SourceScheduledRequirements.necessary checked

theorem body_substitution
    (source : Body operations policy contracts world allowed scope (environment.extend parameter argument)
      code answer header checking)
    (payload : ValueSummary operations policy contracts world environment allowed operand argument)
    (closed : ClosedValue operand.erase) :
    Body operations policy contracts world allowed scope environment
      (code.subst parameter operand) answer header checking := by
  cases source with
  | typed expression rows closingRows => exact .typed (SourceAnnotatedSources.substitution expression payload closed) rows closingRows

theorem fresh_payload
    (payload : ValueSummary operations policy contracts world environment payloadAllowed operand argument)
    (closed : ClosedValue operand.erase) (fresh : contracts owner = none) :
    ValueSummary operations policy (contracts.insert owner contract) world environment allowed operand argument :=
  SourceAnnotatedSources.Values.extension (SourceAnnotatedSources.Values.change_allowed payload closed.1 allowed)
    (SourcePlannedTyping.insert_extends contracts fresh)

/-- Lexical readiness follows from the synchronized source derivation through
its existing port-typing projection. It is not a separate capture assumption. -/
theorem body_ready
    (source : Body operations policy contracts world allowed (.ticket binder owner)
      (Environment.extend (fun _ => none) parameter argument) code answer header checking)
    (known : contracts owner = some contract) : ClosedExcept parameter code.erase :=
  SourcePlannedCaptureSubstitution.body_ready source.erase known

/-- The existing raw capture and owner equation apply to the same substituted
source body. Freshness is explicit here; deriving it from the shared runtime
registry remains the allocation invariant's responsibility. -/
theorem body_step
    (source : Body operations policy contracts world allowed (.ticket binder owner)
      (Environment.extend (fun _ => none) parameter argument) code answer header checking)
    (known : contracts owner = some contract)
    (payload : ValueSummary operations policy contracts world (fun _ => none) allowed operand argument)
    (closed : ClosedValue operand.erase)
    (cut : SourceAnnotatedRuntime.HandlerCut requested whole capture tail handler)
    (selected : SourceAnnotatedRuntime.ClauseAt operation handler.clauses parameter binder code)
    (unique : (ownedTickets whole.erase).Nodup) (absent : owner ∉ ownedTickets whole.erase) :
    RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand.erase, caller, whole.erase⟩
      ⟨code.erase.subst parameter operand.erase, .ticket binder owner,
        .live owner (ScopedPorts.embedPort contract.input.erase.erase.port) handler.answer capture.erase handler.scope tail.erase⟩ [.ticket owner] [] ∧
    ownedTickets (.live owner (ScopedPorts.embedPort contract.input.erase.erase.port) handler.answer capture.erase handler.scope tail.erase) =
      owner :: ownedTickets whole.erase ∧
    (ownedTickets (.live owner (ScopedPorts.embedPort contract.input.erase.erase.port) handler.answer capture.erase handler.scope tail.erase)).Nodup ∧
    OwnerPhaseTransitions.available
      (ownedTickets (.live owner (ScopedPorts.embedPort contract.input.erase.erase.port) handler.answer capture.erase handler.scope tail.erase)) =
      introduce (OwnerPhaseTransitions.available (ownedTickets whole.erase)) owner ∧
    Body operations policy contracts world allowed (.ticket binder owner) (fun _ => none)
      (code.subst parameter operand) answer header checking := by
  refine ⟨RawStep.capture requested operation parameter binder owner operand.erase code.erase caller whole.erase capture.erase tail.erase handler.erase
    (ScopedPorts.embedPort contract.input.erase.erase.port) cut.erase selected.erase closed (body_ready source known),
    RecursiveCapture.capture_owned cut.erase, ?_, OwnerPhaseTransitions.capture_map cut.erase, body_substitution source payload closed⟩
  have owned : ownedTickets (.live owner (ScopedPorts.embedPort contract.input.erase.erase.port) handler.answer capture.erase handler.scope tail.erase) =
      owner :: ownedTickets whole.erase := RecursiveCapture.capture_owned cut.erase
  rw [owned]
  exact List.nodup_cons.mpr ⟨absent, unique⟩

end Ash.OneShot.SourceAnnotatedCaptureSources

#print axioms Ash.OneShot.SourceAnnotatedCaptureSources.selected_body

#print axioms Ash.OneShot.SourceAnnotatedCaptureSources.capture_body_from_requirements

#print axioms Ash.OneShot.SourceAnnotatedCaptureSources.capture_body

#print axioms Ash.OneShot.SourceAnnotatedCaptureSources.body_substitution

#print axioms Ash.OneShot.SourceAnnotatedCaptureSources.fresh_payload

#print axioms Ash.OneShot.SourceAnnotatedCaptureSources.body_ready

#print axioms Ash.OneShot.SourceAnnotatedCaptureSources.body_step
