import SourceScheduledCallbackInterfaces
import SourceScheduledClauses

/-! Callback interfaces can include internal disposal without requiring an
outer resumptive interpretation. The existing local-handler proof supplies
source scheduling, and the same interface compiler constructs the closing
schedule under running protection. These are plan-admission examples, not a
complete initial-program admission theorem. -/
namespace Ash.OneShot.SourceScheduledInternalCallbacks
open SourceDeclarationPlans
open SourcePlanSignatures (signature)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledChecks (Local Pending)
open SourceRequestFootprints (Footprint)
open SourceScheduledCallbackInterfaces (Interfaces)
open SourceScheduledClosingCallbacks (Callbacks)

/-- The callback itself arms another cleanup; both its cleanup branch and its
choice branches handle requests internally and dispose their own captures. -/
def callback (effect : Instance) (operation : Nat) :=
  Plan.cleanup (needs := []) (HandledRequest.plan effect operation)
    (.choice (.sequence .pure (HandledRequest.plan effect operation))
      (HandledRequest.plan effect operation))

theorem callback_interface : Footprint (signature (callback effect operation)) [] :=
  .cleanup .handledRequest (.choice (.sequence .pure .handledRequest) .handledRequest)

/-- Declaration evidence is syntax-directed and independent of receiving
scope. The existing internal disposer supplies its own clause annotation. -/
theorem internal_declarations :
    SourceScheduledSourceInterfaces.Declared world (signature (HandledRequest.plan effect operation)) :=
  .handler SourcePlannedRecipeDeclarations.handled_request_declarations (.sequence .pure .request)

theorem callback_declarations :
    SourceScheduledSourceInterfaces.Declared world (signature (callback effect operation)) :=
  .cleanup internal_declarations (.choice (.sequence .pure internal_declarations) internal_declarations)

/-- No external interpretation or previously successful whole callback is a
premise. The direct compiler consumes its structural source annotations. -/
theorem callback_source {hints : Hints scope} {forest : Forest hints} :
    Local outward actions phases world (callback effect operation) forest :=
  SourceScheduledSourceInterfaces.compile callback_interface callback_declarations rfl

def saved (effect : Instance) (operation : Nat) :=
  Forest.cleanup (needs := []) (callback effect operation) .nil

def interfaces (effect : Instance) (operation : Nat) : Interfaces (saved effect operation) :=
  .cleanup .nil [] callback_interface .nil

/-- Actual callback admission under the protection introduced by closing.
Each inner handler lies inside that boundary, so its selected capture contains
no running marker and its independent disposal check succeeds. -/
theorem compiled_callbacks {hints : Hints scope} {outside : Forest hints} :
    Callbacks outward actions phases world (saved effect operation) (.running outside) := by
  exact (interfaces effect operation).compile_declared (.cleanup callback_declarations .nil) rfl

theorem closing_schedule {hints : Hints scope} {outside : Forest hints} :
    Pending outward actions phases world (saved effect operation).forClosing (.running outside) :=
  compiled_callbacks.schedule

/-- The internal handler is a disposer, so the older resumptive-only operation
capability is intentionally insufficient to justify this accepted interface. -/
theorem disposer_is_not_a_resumptive_capability :
    SourceContextualHints.checkCapability
      (.handler effect (HandledRequest.table operation) (HandledRequest.families operation) .nil)
      effect operation = false := by
  simp [SourceContextualHints.checkCapability, SourceDependencyCapture.select,
    HandledRequest.table, HandledRequest.families, ProtectionContracts.lookup,
    SourceDependencyCapture.lookupDependencies]

/-- Admitting a handler's internal disposal never grants permission to invoke
an arbitrary outside owner. Operation interfaces still cannot hide such a use. -/
theorem direct_disposal_requires_its_own_capability :
    ¬ Footprint (.invoke (key := ⟨owner, .dispose⟩)) required := by
  intro footprint
  exact footprint.no_invocation rfl

end Ash.OneShot.SourceScheduledInternalCallbacks

#print axioms Ash.OneShot.SourceScheduledInternalCallbacks.callback_interface
#print axioms Ash.OneShot.SourceScheduledInternalCallbacks.callback_source
#print axioms Ash.OneShot.SourceScheduledInternalCallbacks.compiled_callbacks
#print axioms Ash.OneShot.SourceScheduledInternalCallbacks.closing_schedule
#print axioms Ash.OneShot.SourceScheduledInternalCallbacks.disposer_is_not_a_resumptive_capability
#print axioms Ash.OneShot.SourceScheduledInternalCallbacks.direct_disposal_requires_its_own_capability

#print axioms Ash.OneShot.SourceScheduledInternalCallbacks.internal_declarations
#print axioms Ash.OneShot.SourceScheduledInternalCallbacks.callback_declarations
