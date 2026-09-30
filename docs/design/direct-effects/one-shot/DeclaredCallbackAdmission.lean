import SourceOwnerClosure
import ClosingBudgetGap

/-! Check the source-derived closing footprint in its actual surviving
interpretations. Full callback bodies retain hereditary declarations. This
does not infer the check at every future capture from initial source typing. -/
namespace Ash.OneShot.DeclaredCallbackAdmission
open ScopedExpressions ScopedExecution CoherentSourceTypes ProtectionContracts ProtectionResiduals
open RecursiveRequirements (Requirements)
open DeclaredSourceClosing (PlanTemplate)

/-- The combined budget is an exported row, so compare after interpreting
the actual plan footprint through the surviving stack. -/
def checkClosing (receiving outside : ProtectionContracts.Context) (raw budget : Footprint) : Bool :=
  match residualize receiving raw with
  | none => false
  | some row => checkFootprint outside row && decide (row ⊆ budget)

theorem check_closing_iff : checkClosing receiving outside raw budget = true ↔
    ∃ row, residualize receiving raw = some row ∧
      checkFootprint outside row = true ∧ EffectBounds.Covers budget row := by
  unfold checkClosing
  cases exported : residualize receiving raw with
  | none => simp
  | some row => simp [EffectBounds.Covers, Bool.and_eq_true]

/-- Existing retirement and template evaluation discharge the owner-phase
premises. The finite check supplies the exact export and its combined bound. -/
theorem checked_template
    (template : PlanTemplate operations policy contracts tables world scope plan raw requirements)
    (built : makePlan capture = some plan)
    (unique : (ownedTickets (.live owner input answer capture caller fixed)).Nodup)
    (accepted : checkClosing (CallableProtectionFrames.contextOf tables fixed) outside raw budget = true) :
    ∃ row,
      RecursiveRequirements.evaluate store (OwnerPhases.ofStack tables fixed)
        (OwnerPhaseTransitions.spend
          (OwnerPhaseTransitions.available (ownedTickets (.live owner input answer capture caller fixed))) owner)
        requirements = some row ∧
      checkFootprint outside row = true ∧ EffectBounds.Covers budget row ∧
      checkFootprint (CallableProtectionFrames.contextOf tables fixed ++ outside) raw = true := by
  obtain ⟨row, exported, admitted, covered⟩ := check_closing_iff.mp accepted
  exact ⟨row, RecursivePlanAdmission.captured_evaluation
      (DeclaredSourceClosing.template_erase template) built unique exported,
    admitted, covered, residual_admitted_iff.mpr ⟨row, exported, admitted⟩⟩

/-- Extract the actual callback occurrence and remaining plan suffix. This
uses the same residual equations as the older readiness proof, while retaining
the full hereditary callable judgment instead of erasing handler bodies. -/
theorem invocation_source
    (template : PlanTemplate operations policy contracts tables world scope plan raw requirements)
    (accepted : checkFootprint outside raw = true)
    (position : ScopedPorts.InvocationAt action plan suffix) :
    ∃ latent,
      DeclaredSourceValues.ValueSummary operations policy contracts world Environment.empty []
        action.action (.function .unit .unit action.requests latent) ∧
      checkFootprint ((.barrier true :: DisposalProtection.planContext suffix) ++ outside) latent = true := by
  induction template generalizing action suffix with
  | nil => cases position
  | release rest ih | retire known rest ih => cases position with
      | later position => exact ih accepted position
  | invoke callback rest ih =>
      rw [check_footprint_append, Bool.and_eq_true] at accepted
      cases position with
      | here => exact ⟨_, callback, (DisposalProtection.callback_residual_check _ _ _).symm.trans accepted.1⟩
      | later position => exact ih accepted.2 position

/-- Expand the callback at the actual protected closing position. Existing
canonical forms, substitution, source grouping and outward evaluation supply
the beta body and its requirement check; no new source-reduction induction. -/
theorem invocation_body
    (template : PlanTemplate operations policy contracts tables world planScope plan raw requirements)
    (accepted : checkFootprint (CallableProtectionFrames.contextOf tables fixed ++ outside) raw = true)
    (position : ScopedPorts.InvocationAt action plan suffix) (scope : Scope) :
    let runtime := Stack.push (.running { action with scope := scope, answer := .unit }
      .unit ScopedExecution.Examples.unit_closed) ((closeControl scope suffix).append fixed)
    ∃ body, ∃ bodyRequirements : Requirements [], ∃ shape : ScopedRequirementShapes.Shape bodyRequirements,
      DeclaredSources.Expression operations policy contracts world action.requests .none Environment.empty
        body .unit [] bodyRequirements ∧
      ScopedRequirementShapes.Describes body shape ∧
      ConfigurationUsage policy tickets ⟨body, .none, .nil⟩ ∧
      RawStep ⟨.app action.action .unit, .none, runtime⟩ ⟨body, .none, runtime⟩ [] [] ∧
      ∃ row,
        RecursiveRequirements.Checked store (OwnerPhases.ofStack tables runtime)
          (OwnerPhaseTransitions.available (ownedTickets runtime)) bodyRequirements row ∧
        checkFootprint outside row = true := by
  dsimp only
  let runtime := Stack.push (.running { action with scope := scope, answer := .unit }
    .unit ScopedExecution.Examples.unit_closed) ((closeControl scope suffix).append fixed)
  obtain ⟨latent, callback, admitted⟩ := invocation_source template accepted position
  have ports := (DeclaredSourceValues.erase callback).ports .none
  obtain ⟨parameter, code, functionSame⟩ := ScopedPorts.typed_function_value ports action.closed.1
  have closure : ClosedValue (.lambda parameter code) := functionSame ▸ action.closed
  have function := CallableSourceShapes.enrich
    (DeclaredSourceValues.change_allowed callback action.closed.1 action.requests)
  rw [functionSame] at function
  obtain ⟨bodyRequirements, shape, source, described, outward, evaluated⟩ :=
    CallableSourceShapes.application_shape function CallableSources.Summary.summaryUnit
      ScopedExecution.Examples.unit_closed (List.Subset.refl _)
  have context : CallableProtectionFrames.contextOf tables runtime =
      .barrier true :: (DisposalProtection.planContext suffix ++ CallableProtectionFrames.contextOf tables fixed) := by
    change .barrier true :: CallableProtectionFrames.contextOf tables ((closeControl scope suffix).append fixed) = _
    rw [ProtectionResiduals.context_append, DisposalProtection.plan_context_realizes]
  have checked : checkFootprint (CallableProtectionFrames.contextOf tables runtime ++ outside) latent = true := by
    simpa only [context, List.cons_append, List.append_assoc] using admitted
  obtain ⟨row, exported, acceptedRow⟩ := residual_admitted_iff.mp checked
  have ready : ∀ owner ∈ activeTickets runtime,
      OwnerPhaseTransitions.available (ownedTickets runtime) owner = .available := by
    intro owner present
    exact if_pos (active_tickets_owned runtime present)
  have bodyChecked : RecursiveRequirements.Checked store (OwnerPhases.ofStack tables runtime)
      (OwnerPhaseTransitions.available (ownedTickets runtime)) bodyRequirements row := by
    apply RecursiveRequirements.evaluate_sound
    have result := evaluated store (OwnerPhases.ofStack tables runtime)
      (OwnerPhaseTransitions.available (ownedTickets runtime))
    rw [RecursivePlanAdmission.caller_export ready] at result
    exact result.trans exported
  refine ⟨code.subst parameter .unit, bodyRequirements, shape, source, described,
    SourceOwnerClosure.initial_usage source, ?_, row, bodyChecked, acceptedRow⟩
  exact (congrArg (fun function : Code => RawStep ⟨.app function .unit, .none, runtime⟩
    ⟨code.subst parameter .unit, .none, runtime⟩ [] []) functionSame).mpr
    (RawStep.beta parameter code .unit .none runtime ScopedExecution.Examples.unit_closed closure)

namespace Examples
open ClosingBudgetGap

def outside : ProtectionContracts.Context :=
  [.handler SourceCallableExamples.effect 99 SourceCallableExamples.table]

/-- Reuse the counterexample with an inner and outer interpretation. The
correct combined budget admits its nonempty closing row; resume-only does not. -/
theorem combined_budget_distinguishes :
    checkClosing (CallableProtectionFrames.contextOf tables fixed) outside forwarded (forwarded ++ []) = true ∧
    checkClosing (CallableProtectionFrames.contextOf tables fixed) outside forwarded [] = false := by decide

def handlerAction : ActionData :=
  ⟨101, SourceCallableExamples.function, DeclaredSourceSubstitution.Examples.function_closed,
    .none, .unit, []⟩

/-- This plan retains a callback with a handler in its body. Reuse the
existing proof that the older stable summary cannot express that callback. -/
theorem handler_callback_admitted :
    ∃ requirements,
      PlanTemplate SourceCallableExamples.operations SourceCallableExamples.policy SourceCallableExamples.contracts
        (fun _ => []) [] .none [.invoke handlerAction] [] requirements ∧
      checkClosing [] [] [] [] = true ∧
      ¬ Summary SourceCallableExamples.operations [] Environment.empty [] handlerAction.action
        SourceCallableExamples.functionType [] := by
  exact ⟨_, .invoke (action := handlerAction) (latent := [])
      DeclaredSourceSubstitution.Examples.function_value .nil, rfl,
    SourceCallableExamples.legacy_summary_rejects⟩

end Examples
end Ash.OneShot.DeclaredCallbackAdmission

#print axioms Ash.OneShot.DeclaredCallbackAdmission.check_closing_iff
#print axioms Ash.OneShot.DeclaredCallbackAdmission.checked_template
#print axioms Ash.OneShot.DeclaredCallbackAdmission.invocation_source
#print axioms Ash.OneShot.DeclaredCallbackAdmission.invocation_body
#print axioms Ash.OneShot.DeclaredCallbackAdmission.Examples.combined_budget_distinguishes
#print axioms Ash.OneShot.DeclaredCallbackAdmission.Examples.handler_callback_admitted
