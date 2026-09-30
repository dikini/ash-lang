import DeclaredSharedValues

/-! The existing source regression also has a connected normal interface.
Even supplying its entire callback row to closing cannot preserve a handler
removed by the plan. This is a local source-state separation, not a reachable
initial-program counterexample or a reason to reject resume-only clauses.
-/
namespace Ash.OneShot.DeclaredClosingRouteGap
open ScopedExpressions ScopedExecution CoherentSourceTypes
open RecursiveRequirements (Requirements)
open SourceCallableExamples (operations policy effect operation_known)
open ClosingBudgetGap (contracts)
open ResumeOnlyCapture.Examples

private theorem callback_typed : ScopedPorts.Typed operations.ports [] ScopedPorts.TypeEnv.empty
    .none [] action.action (.function .unit .unit action.requests) :=
  CoherentSourceTypes.port_typing callback_source .none

theorem normal_connected : ScopedActionInterfaces.Connected operations.ports contracts.ports
    actions [] whole [effect] [] := by
  have outerFrame : ScopedPorts.EffectFrame operations.ports contracts.ports []
      (.handler handler) [effect] [] := by
    refine .handler ⟨.none, .none⟩
      (.cons (port_lookup operation_known)
        (.resume .unit (List.Subset.refl []) (by
          simp [handler, ClosingBudgetGap.shadow, ScopedPorts.InWorld, ScopedPorts.eraseType,
            ScopedPorts.Port.resources])) .nil) ?_ (by decide)
    cases ClosingBudgetGap.shadow_typed with
    | handler scope clauses coverage unique => exact coverage
  have innerFrame : ScopedPorts.EffectFrame operations.ports contracts.ports []
      (.handler localHandler) [callbackEffect, effect] [effect] := by
    refine .handler ⟨.none, .none⟩ .nil ?_ (by decide)
    cases local_handler_typed with
    | handler scope clauses coverage unique => exact coverage
  exact .push (.armed ⟨.none, .none⟩ callback_typed (by simp [action]))
    (.push innerFrame (.push outerFrame (.nil (List.Subset.refl [])) (List.Subset.refl _))
      (List.Subset.refl _)) (by simp)

/-- The current source derivation and its caller use the same allowed row. -/
theorem shared_source : DeclaredSourceInterfaces.State operations policy contracts tables actions
    [] [] .none request whole .unit [] [] := by
  have current : DeclaredSources.Expression operations policy contracts [] [effect] .none Environment.empty
      request .unit [] (.emitAfter empty [] [⟨effect, 0, false⟩]) :=
    .perform operation_known List.mem_cons_self (.stable .unit)
      (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])
  exact .checked current .none pending_source (.push (.push (.push .nil)))
    (by decide) (RecursiveRequirements.evaluate_sound (by
      simp only [wholeRequirements, middleRequirements, outerRequirements, empty,
        Requirements.prepend, RecursiveRequirements.evaluate, RecursiveRequirements.evaluateFuel]
      decide)) rfl rfl normal_connected

/-- The complete declared callback row suffices for plan effect typing. -/
theorem closing_effects_ready : ScopedPorts.PlanTyped operations.ports [] [callbackEffect] plan :=
  .invoke callback_typed (List.Subset.refl _) .nil

/-- No outward row can repair the loss of this locally selected handler. -/
theorem no_open_closing (outward : List Instance) :
    ¬ Admission.OpenCloses whole.erase .nil .nil (Admission.outsideResources whole.erase)
      outward (plan.map CloseEntry.erase) := by
  intro closing
  cases closing with
  | bind frame rest original surviving resources outward suffix kind next => cases kind
  | handler frame effect activation rest original surviving resources outward suffix kind next => cases kind
  | armed frame identity rest original surviving resources outward suffix kind ticketClosed access requests next =>
      cases requests with
      | localTarget request rest target before after next => cases after
      | outside request rest before after declared next => contradiction

theorem no_certificate (record : Owners.Record) :
    ¬ Nonempty (DeclaredClosingInvariant.Certificate operations.ports [] record whole) := by
  rintro ⟨certificate⟩
  have same : certificate.plan = plan := Option.some.inj (certificate.built.symm.trans closing_rejected.1)
  exact no_open_closing record.annotation.closeEffects (same ▸ certificate.closing)

end Ash.OneShot.DeclaredClosingRouteGap

#print axioms Ash.OneShot.DeclaredClosingRouteGap.normal_connected
#print axioms Ash.OneShot.DeclaredClosingRouteGap.shared_source
#print axioms Ash.OneShot.DeclaredClosingRouteGap.closing_effects_ready
#print axioms Ash.OneShot.DeclaredClosingRouteGap.no_open_closing
#print axioms Ash.OneShot.DeclaredClosingRouteGap.no_certificate
