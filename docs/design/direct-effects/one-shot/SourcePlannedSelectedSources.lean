import SourcePlannedRecipeDeclarations
import SourcePlannedSources

/-! Select the synchronized source body at the exact retained plan. This uses
the established selected-body induction with the stronger source indices, then
joins structural recipe checking to the same witness. -/
namespace Ash.OneShot.SourcePlannedSelectedSources
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations (Dependencies)
open SourceDeclarationPlans (Plan ClausePlans)
open SourcePlanSignatures (signature)
open SourcePlannedRecipeDeclarations (Selected)
open SourcePlannedTyping (Contract)
open SourceDependencyCapture (lookupDependencies modeDependencies)
open SourceContextualHints (Hints checkRequirements)
open SourcePlannedChecks (Local Pending)
open SourceContextualHintChecking (Compatible)
open OwnerPhaseTransitions (introduce)

theorem selected_body {plans : ClausePlans clauses families}
    (source : SourcePlannedSources.Declarations operations policy contracts world environment allowed requested answer clauses table plans)
    (selected : ClauseAt operation clauses parameter binder code)
    (found : lookup operation table = some offered)
    (available : offered.row held = some row) :
    ∃ argument input resumeEffects closeEffects, ∃ (family : Nat → Dependencies) (bodies : ∀ owner, Plan (family owner)),
      operations requested operation = some (argument, input) ∧
      (code.requiredActions.resume = true → resumeEffects = allowed) ∧
      (code.requiredActions.dispose = true → closeEffects = allowed) ∧
      Selected operation held plans parameter binder code bodies ∧
      ∀ owner (contract : Contract), contracts owner = none →
        contract.input = input → contract.answer = answer →
        contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
        contract.held = held → contract.closeDemand.Perm contract.resumeDemand →
        SourcePlannedSources.Body operations policy (contracts.insert owner contract) world allowed (.ticket binder owner)
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

/-- Source typing and execution checking now select the same actual clause
plan. This is a capture component, before clause substitution and runtime-store
integration; it does not assert preservation of an entire runtime state. -/
theorem capture_body {plans : ClausePlans clauses families}
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
    (supplied : checkRequirements tail required = true) :
    ∃ argument input resumeEffects closeEffects, ∃ (family : Nat → Dependencies) (bodies : ∀ owner, Plan (family owner)),
      operations requested operation = some (argument, input) ∧
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
        SourcePlannedSources.Body operations policy (contracts.insert owner contract) world allowed (.ticket binder owner)
          (environment.extend parameter argument) code answer ⟨owner, contract.erase.erase, offered.dispose, row⟩
          (signature (bodies owner)) := by
  obtain ⟨argument, input, resumeEffects, closeEffects, family, bodies, known, resume, close, chosen, body⟩ :=
    selected_body source selected found available
  obtain ⟨actual, actualFound, disposalPermission⟩ := SourceTemplates.selected_clause_mode selected clauseModes
  cases Option.some.inj (found.symm.trans actualFound)
  obtain ⟨offeredFamily, checked, pending⟩ := recipes.capture chosen declared cut request retained compatible fresh consumed
    disposalPermission supplied
  exact ⟨argument, input, resumeEffects, closeEffects, family, bodies, known, resume, close,
    chosen, offeredFamily, checked, pending, body owner⟩

end Ash.OneShot.SourcePlannedSelectedSources

#print axioms Ash.OneShot.SourcePlannedSelectedSources.selected_body
#print axioms Ash.OneShot.SourcePlannedSelectedSources.capture_body
