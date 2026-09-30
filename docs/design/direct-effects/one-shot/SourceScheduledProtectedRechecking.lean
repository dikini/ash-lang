import SourceScheduledSourceRechecking
import SourceScheduledHandlerRequests

/-! Requests that cross a running callback cannot dispose of that capture.
Their source rechecking needs only the actual protected mode, not a reusable
capability offering both modes or a new recursively closing source. -/
namespace Ash.OneShot.SourceDependencyCapture

theorem held_running_suffix (front : Scope) : (front.append (.running rest)).held = true := by
  induction front <;> simp_all [Scope.append, Scope.held]

/-- The existing capture guard rules out disposal when the actual selected
segment contains a running boundary. No handler-mode convention is assumed. -/
theorem protected_capture_non_disposing
    (checked : checkCapture outward scope effect operation = true)
    (found : select effect operation scope = some (.handler saved waiting contract modes))
    (held : saved.held = true) : contract.dispose = false := by
  cases permission : contract.dispose with
  | false => rfl
  | true =>
      have unprotected := (disposing_capture checked found permission).1
      rw [held] at unprotected
      cases unprotected

/-- At this exact cut, only the protected row and body are required. The
ordinary mode may be absent; independent nearest lookup remains unchanged. -/
theorem protected_capture_check
    (found : select effect operation scope = some (.handler saved waiting contract modes))
    (held : saved.held = true) :
    checkCapture outward scope effect operation = true ↔
      contract.dispose = false ∧ contract.protectedRow.isSome = true ∧ modes.2.isSome = true := by
  simp only [checkCapture, found, held, ProtectionContracts.modeCheck,
    ProtectionContracts.ClauseContract.row, modeDependencies]
  cases contract.dispose <;> simp

end Ash.OneShot.SourceDependencyCapture

namespace Ash.OneShot.SourceScheduledSourceRechecking
open SourceDependencyCapture (Scope)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledCapabilityAnnotations (Code DeclarationPolicy)

variable [DeclarationPolicy]

/-- Protected selection discharges the no-disposal premise of the local
source rule. No original or target closing annotation is needed. -/
theorem Expression.protected_request
    {beforeHints : Hints beforeScope} {afterHints : Hints afterScope}
    {before : Forest beforeHints} {after : Forest afterHints}
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    {source : Code world (.request (effect := effect) (operation := operation)) before}
    (cut : SourceScheduledNeutral.Cut effect operation contract modes after saved waiting)
    (checked : SourceDependencyCapture.checkCapture outward afterScope effect operation = true)
    (held : savedScope.held = true) : Expression outward actions phases source after :=
  .nonDisposing cut checked
    (SourceDependencyCapture.protected_capture_non_disposing checked cut.erase.lookup held)

/-- Any prefix bypassed by the request may precede the running boundary.
The existing prefix-cut theorem authenticates the selected saved/waiting pieces;
running protection then eliminates a fresh disposal obligation across it. -/
theorem Expression.crosses_cleanup
    {beforeHints : Hints beforeScope} {before : Forest beforeHints}
    {source : Code world (.request (effect := effect) (operation := operation)) before}
    {frontHints : Hints frontScope} (front : Forest frontHints)
    {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (passed : SourceHandlerRequirements.reaches effect frontScope = true)
    (cut : SourceScheduledNeutral.Cut effect operation contract modes outside saved waiting)
    (checked : SourceDependencyCapture.checkCapture outward
      (frontScope.append (.running outsideScope)) effect operation = true) :
    Expression outward actions phases source (front.append (.running outside)) :=
  .protected_request (SourceScheduledHandlerRequests.cut_prefix front passed (.running cut)) checked
    (SourceDependencyCapture.held_running_suffix frontScope)

/-- Source contract fields derive the protected guard at any bypassed prefix.
No target check is supplied, and the selected handler need not offer an ordinary
mode. Continuation permissions are still checked independently. -/
theorem Expression.crosses_cleanup_from_contract
    {beforeHints : Hints beforeScope} {before : Forest beforeHints}
    {source : Code world (.request (effect := effect) (operation := operation)) before}
    {frontHints : Hints frontScope} (front : Forest frontHints)
    {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (passed : SourceHandlerRequirements.reaches effect frontScope = true)
    (cut : SourceScheduledNeutral.Cut effect operation contract modes outside saved waiting)
    (noDisposal : contract.dispose = false)
    (row : contract.protectedRow.isSome = true)
    (body : modes.2.isSome = true) :
    Expression outward actions phases source (front.append (.running outside)) := by
  apply Expression.crosses_cleanup front passed cut
  exact (SourceDependencyCapture.protected_capture_check
    (SourceScheduledHandlerRequests.cut_prefix front passed (.running cut)).erase.lookup
    (SourceDependencyCapture.held_running_suffix frontScope)).mpr ⟨noDisposal, row, body⟩

end Ash.OneShot.SourceScheduledSourceRechecking

#print axioms Ash.OneShot.SourceDependencyCapture.held_running_suffix
#print axioms Ash.OneShot.SourceDependencyCapture.protected_capture_non_disposing
#print axioms Ash.OneShot.SourceDependencyCapture.protected_capture_check
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.Expression.protected_request
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.Expression.crosses_cleanup
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.Expression.crosses_cleanup_from_contract
