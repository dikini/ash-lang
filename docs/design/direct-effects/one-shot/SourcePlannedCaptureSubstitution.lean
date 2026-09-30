import SourcePlannedSelectedSources
import SourcePlannedSourceSubstitution

/-! Capture substitutes a closed payload into the synchronized selected body.
The existing substitution proof retains its signature and row judgment; fresh
registry extension transports the payload without changing its refined type. -/
namespace Ash.OneShot.SourcePlannedCaptureSubstitution
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations (Dependencies)
open SourceDeclarationPlans (Plan ClausePlans)
open SourcePlanSignatures (signature)
open SourcePlannedTyping (Environment Contract)
open SourcePlannedSources (Body ValueSummary)
open SourcePlannedRecipeDeclarations (Selected)
open SourceDependencyCapture (lookupDependencies modeDependencies)
open SourceContextualHints (Hints checkRequirements)
open SourcePlannedChecks (Local Pending)
open SourceContextualHintChecking (Compatible)
open OwnerPhaseTransitions (introduce)

theorem body_substitution
    (source : Body operations policy contracts world allowed scope (environment.extend parameter argument)
      code answer header checking)
    (payload : ValueSummary operations policy contracts world environment allowed operand argument)
    (closed : ClosedValue operand) :
    Body operations policy contracts world allowed scope environment
      (code.subst parameter operand) answer header checking := by
  cases source with
  | typed expression rows closingRows => exact .typed (SourcePlannedSources.substitution expression payload closed) rows closingRows

theorem fresh_payload
    (payload : ValueSummary operations policy contracts world environment payloadAllowed operand argument)
    (closed : ClosedValue operand) (fresh : contracts owner = none) :
    ValueSummary operations policy (contracts.insert owner contract) world environment allowed operand argument :=
  SourcePlannedSources.Values.extension (SourcePlannedSources.Values.change_allowed payload closed.1 allowed)
    (SourcePlannedTyping.insert_extends contracts fresh)

/-- Lexical readiness follows from the synchronized source derivation through
its existing port-typing projection. It is not a separate capture assumption. -/
theorem body_ready
    (source : Body operations policy contracts world allowed (.ticket binder owner)
      (Environment.extend (fun _ => none) parameter argument) code answer header checking)
    (known : contracts owner = some contract) : ClosedExcept parameter code := by
  cases source with
  | typed expression rows closingRows =>
      have erased := DeclaredSources.expression_erase
        (SourceDependencyAnnotations.expression_erase (SourcePlannedSources.expression_erase expression))
      have erasedKnown : contracts.erase.erase owner = some contract.erase.erase := by
        simp [SourcePlannedTyping.Contracts.erase, SourceDependencyAnnotations.Contracts.erase, known]
      have typed := SourceTemplates.expression_ports erased
        (.bound (CoherentSourceTypes.Owners.ports_lookup erasedKnown))
      rw [SourcePlannedTyping.environment_erase_extend, SourceDependencyAnnotations.environment_erase_extend,
        CoherentSourceTypes.ports_extend] at typed
      exact ScopedPorts.typed_suffix_ready typed

/-- The existing raw capture and owner equation apply to the same substituted
source body. Freshness is explicit here; deriving it from the shared runtime
registry remains the allocation invariant's responsibility. -/
theorem body_step
    (source : Body operations policy contracts world allowed (.ticket binder owner)
      (Environment.extend (fun _ => none) parameter argument) code answer header checking)
    (known : contracts owner = some contract)
    (payload : ValueSummary operations policy contracts world (fun _ => none) allowed operand argument)
    (closed : ClosedValue operand)
    (cut : HandlerCut requested whole capture tail handler)
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (unique : (ownedTickets whole).Nodup) (absent : owner ∉ ownedTickets whole) :
    RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, caller, whole⟩
      ⟨code.subst parameter operand, .ticket binder owner,
        .live owner (ScopedPorts.embedPort contract.input.erase.erase.port) handler.answer capture handler.scope tail⟩ [.ticket owner] [] ∧
    ownedTickets (.live owner (ScopedPorts.embedPort contract.input.erase.erase.port) handler.answer capture handler.scope tail) =
      owner :: ownedTickets whole ∧
    (ownedTickets (.live owner (ScopedPorts.embedPort contract.input.erase.erase.port) handler.answer capture handler.scope tail)).Nodup ∧
    OwnerPhaseTransitions.available
      (ownedTickets (.live owner (ScopedPorts.embedPort contract.input.erase.erase.port) handler.answer capture handler.scope tail)) =
      introduce (OwnerPhaseTransitions.available (ownedTickets whole)) owner ∧
    Body operations policy contracts world allowed (.ticket binder owner) (fun _ => none)
      (code.subst parameter operand) answer header checking := by
  refine ⟨RawStep.capture requested operation parameter binder owner operand code caller whole capture tail handler
    (ScopedPorts.embedPort contract.input.erase.erase.port) cut selected closed (body_ready source known),
    RecursiveCapture.capture_owned cut, ?_, OwnerPhaseTransitions.capture_map cut, body_substitution source payload closed⟩
  rw [RecursiveCapture.capture_owned cut]
  exact List.nodup_cons.mpr ⟨absent, unique⟩

/-- The payload and selected operation use the same refined argument type.
The resulting body is the actual substituted clause, at the retained signature. -/
theorem capture_substitution {plans : ClausePlans clauses families}
    {hints : Hints scope} {saved : Hints captured} {waiting : Hints tail}
    (source : SourcePlannedSources.Declarations operations policy contracts world environment allowed requested answer clauses table plans)
    (recipes : SourcePlannedRecipeDeclarations.Declarations required plans)
    (clauseModes : SourceTemplates.ClauseModes clauses table)
    (selected : ClauseAt operation clauses parameter binder code)
    (found : lookup operation table = some offered)
    (available : offered.row captured.held = some row)
    (declared : lookupDependencies operation families = some modes)
    (cut : SourcePlannedCuts.Cut requested operation offered modes hints saved waiting)
    (request : Local outward actions phases world (.request (effect := requested) (operation := operation)) hints)
    (retained : Pending outward actions phases world hints .nil)
    (compatible : Compatible hints .nil)
    (fresh : actions owner = none) (consumed : phases owner = .consumed)
    (supplied : checkRequirements tail required = true)
    (operationKnown : operations requested operation = some (argument, input))
    (payload : ValueSummary operations policy contracts world environment payloadAllowed operand argument)
    (closed : ClosedValue operand) :
    ∃ resumeEffects closeEffects, ∃ (family : Nat → Dependencies) (bodies : ∀ owner, Plan (family owner)),
      (code.requiredActions.resume = true → resumeEffects = allowed) ∧
      (code.requiredActions.dispose = true → closeEffects = allowed) ∧
      Selected operation captured.held plans parameter binder code bodies ∧
      modeDependencies captured.held modes = some family ∧
      Local outward (actions.insert owner code.requiredActions) (introduce phases owner) world
        (bodies owner) (.live (owner := owner) saved waiting) ∧
      Pending outward (actions.insert owner code.requiredActions) (introduce phases owner) world
        (.live (owner := owner) saved waiting) .nil ∧
      ∀ (contract : Contract), contracts owner = none →
        contract.input = input → contract.answer = answer →
        contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
        contract.held = captured.held → contract.closeDemand.Perm contract.resumeDemand →
        Body operations policy (contracts.insert owner contract) world allowed (.ticket binder owner)
          environment (code.subst parameter operand) answer ⟨owner, contract.erase.erase, offered.dispose, row⟩
          (signature (bodies owner)) := by
  obtain ⟨actualArgument, actualInput, resumeEffects, closeEffects, family, bodies, known, resume, close,
    chosen, offeredFamily, checked, pending, body⟩ :=
    SourcePlannedSelectedSources.capture_body source recipes clauseModes selected found available declared cut
      request retained compatible fresh consumed supplied
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (operationKnown.symm.trans known))
  refine ⟨resumeEffects, closeEffects, family, bodies, resume, close, chosen, offeredFamily, checked, pending, ?_⟩
  intro contract absent inputSame answerSame resumeSame closeSame heldSame balance
  exact body_substitution (body contract absent inputSame answerSame resumeSame closeSame heldSame balance)
    (fresh_payload payload closed absent) closed

end Ash.OneShot.SourcePlannedCaptureSubstitution

#print axioms Ash.OneShot.SourcePlannedCaptureSubstitution.body_substitution
#print axioms Ash.OneShot.SourcePlannedCaptureSubstitution.fresh_payload
#print axioms Ash.OneShot.SourcePlannedCaptureSubstitution.body_ready
#print axioms Ash.OneShot.SourcePlannedCaptureSubstitution.body_step
#print axioms Ash.OneShot.SourcePlannedCaptureSubstitution.capture_substitution
