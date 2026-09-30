import SourcePlannedRuntimeCuts

/-! Capture entry joins actual runtime selection, synchronized clause source,
structural recipe admission, retained hints and ownership accounting. The
matching continuation contract is supplied by allocation; this component does
not yet construct or preserve the complete runtime store. -/
namespace Ash.OneShot.SourcePlannedCaptureEntry
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations (Dependencies)
open SourceDeclarationPlans (Plan ClausePlans)
open SourcePlanSignatures (signature)
open SourcePlannedTyping (Contract)
open SourcePlannedSources (Body ValueSummary)
open SourcePlannedRecipeDeclarations (Selected)
open SourceContextualHints (Hints)
open SourceContextualHintChecking (Matches Compatible)
open SourcePlannedChecks (Local Pending)
open SourceDependencyCapture (lookupDependencies modeDependencies)
open OwnerPhaseTransitions (available)

theorem capture_entry {hints : Hints scope}
    {plans : ClausePlans handler.clauses (families handler)}
    (physical : HandlerCut requested whole captured tail handler)
    (matched : Matches tables families required hints whole)
    (source : SourcePlannedSources.Declarations operations policy contracts world (fun _ => none) allowed requested answer
      handler.clauses (tables handler) plans)
    (recipes : SourcePlannedRecipeDeclarations.Declarations (required handler) plans)
    (clauseModes : SourceTemplates.ClauseModes handler.clauses (tables handler))
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler) = some offered)
    (rowAvailable : offered.row (ProtectionContexts.protectedMode captured.erase) = some row)
    (declared : lookupDependencies operation (families handler) = some modes)
    (request : Local outward actions (available (ownedTickets whole)) world (.request (effect := requested) (operation := operation)) hints)
    (retained : Pending outward actions (available (ownedTickets whole)) world hints .nil)
    (compatible : Compatible hints .nil)
    (fresh : actions owner = none) (absent : owner ∉ ownedTickets whole) (unique : (ownedTickets whole).Nodup)
    (operationKnown : operations requested operation = some (argument, input))
    (payload : ValueSummary operations policy contracts world (fun _ => none) payloadAllowed operand argument)
    (closed : ClosedValue operand) :
    let next := Stack.live owner (ScopedPorts.embedPort input.erase.erase.port) handler.answer captured handler.scope tail
    ∃ capturedScope tailScope, ∃ (saved : Hints capturedScope) (waiting : Hints tailScope),
    ∃ resumeEffects closeEffects, ∃ (family : Nat → Dependencies) (bodies : ∀ owner, Plan (family owner)),
      SourcePlannedCuts.Cut requested operation offered modes hints saved waiting ∧
      Matches tables families required (.live (owner := owner) saved waiting) next ∧
      Selected operation capturedScope.held plans parameter binder code bodies ∧
      modeDependencies capturedScope.held modes = some family ∧
      Local outward (actions.insert owner code.requiredActions) (available (ownedTickets next)) world
        (bodies owner) (.live (owner := owner) saved waiting) ∧
      Pending outward (actions.insert owner code.requiredActions) (available (ownedTickets next)) world
        (.live (owner := owner) saved waiting) .nil ∧
      ownedTickets next = owner :: ownedTickets whole ∧ (ownedTickets next).Nodup ∧
      ∀ (contract : Contract), contracts owner = none →
        contract.input = input → contract.answer = answer →
        contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
        contract.held = capturedScope.held → contract.closeDemand.Perm contract.resumeDemand →
        RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, caller, whole⟩
          ⟨code.subst parameter operand, .ticket binder owner, next⟩ [.ticket owner] [] ∧
        Body operations policy (contracts.insert owner contract) world allowed (.ticket binder owner)
          (fun _ => none) (code.subst parameter operand) answer ⟨owner, contract.erase.erase, offered.dispose, row⟩
          (signature (bodies owner)) := by
  dsimp only
  obtain ⟨capturedScope, tailScope, saved, waiting, cut, inside, outside, supplied⟩ :=
    SourcePlannedRuntimeCuts.matched_cut physical matched found declared
  have rowAtScope : offered.row capturedScope.held = some row := by
    rw [inside.realizes.held]
    exact rowAvailable
  have consumed : available (ownedTickets whole) owner = .consumed := by simp [available, absent]
  obtain ⟨actualArgument, actualInput, resumeEffects, closeEffects, family, bodies, known, resume, close,
    chosen, offeredFamily, checked, pending, body⟩ :=
    SourcePlannedSelectedSources.capture_body source recipes clauseModes selected found rowAtScope declared cut
      request retained compatible fresh consumed (supplied compatible)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (operationKnown.symm.trans known))
  refine ⟨capturedScope, tailScope, saved, waiting, resumeEffects, closeEffects, family, bodies,
    cut, .live inside outside, chosen, offeredFamily, ?_, ?_, RecursiveCapture.capture_owned physical, ?_, ?_⟩
  · simpa only [OwnerPhaseTransitions.capture_map physical] using checked
  · simpa only [OwnerPhaseTransitions.capture_map physical] using pending
  · rw [RecursiveCapture.capture_owned physical]
    exact List.nodup_cons.mpr ⟨absent, unique⟩
  · intro contract freshContract inputSame answerSame resumeSame closeSame heldSame balance
    have instantiated := body contract freshContract inputSame answerSame resumeSame closeSame heldSame balance
    have inserted : (contracts.insert owner contract) owner = some contract := by simp [SourcePlannedTyping.Contracts.insert]
    obtain ⟨step, _, _, _, substituted⟩ := SourcePlannedCaptureSubstitution.body_step instantiated inserted
      (SourcePlannedCaptureSubstitution.fresh_payload payload closed freshContract) closed physical selected unique absent
    exact ⟨by simpa only [inputSame] using step, substituted⟩

end Ash.OneShot.SourcePlannedCaptureEntry

#print axioms Ash.OneShot.SourcePlannedCaptureEntry.capture_entry
