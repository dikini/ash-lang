import SourceScheduledRetainedInterfaces
import SourceScheduledCallbackInterfaces
import SourceScheduledScopedInvocations

/-! Invocation admission from source interfaces. The selected owner, its
permission, its phase and the disposal route stay independent of operation
requirements. Retained-code scheduling and compatibility are derived. -/
namespace Ash.OneShot.SourceScheduledInvocationInterfaces
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledChecks (Local Pending)
open SourceScheduledNeutral (OwnerCut)
open SourceScheduledRetainedInterfaces (Interfaces)
open SourceScheduledScopedInvocations
open OwnerPhaseTransitions (spend)

variable {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
  {savedHints : Hints savedScope} {tailHints : Hints tailScope}
  {whole : Forest wholeHints} {front : Forest frontHints}
  {saved : Forest savedHints} {tail : Forest tailHints}

/-- Resume under an arbitrary actual caller prefix. The three finite checks
use the post-consumption composition; no old or target Pending is assumed. -/
theorem resume_from_interfaces (cut : OwnerCut owner whole front saved tail)
    (known : actions owner = some rights) (permission : rights.resume = true)
    (available : phases owner = .available)
    (inside : Interfaces world saved) (before : Interfaces world front) (after : Interfaces world tail)
    (savedCheck : inside.check (frontScope.append (.spent owner tailScope)) = true)
    (frontCheck : before.check (.spent owner tailScope) = true)
    (tailCheck : after.check .nil = true) :
    Local outward actions phases world (.invoke (key := ⟨owner, .resume⟩)) whole := by
  have savedSchedule : Pending outward actions (spend phases owner) world
      saved (front.append (.spent (owner := owner) tail)) := inside.compile savedCheck
  have frontSchedule : Pending outward actions (spend phases owner) world
      front (.spent (owner := owner) tail) := before.compile frontCheck
  have tailSchedule : Pending outward actions (spend phases owner) world tail .nil := after.compile tailCheck
  exact resume_from_parts cut known permission available savedSchedule frontSchedule tailSchedule
    (pending_resume_iff.mpr ⟨savedSchedule, frontSchedule, tailSchedule⟩).compatible

/-- Dispose using only actual saved callbacks, while retaining the complete
caller and waiting tail. Closing order and running protection come from the
existing callback compiler; the finite route check is separately sound. -/
theorem dispose_from_interfaces (cut : OwnerCut owner whole front saved tail)
    (known : actions owner = some rights) (permission : rights.dispose = true)
    (available : phases owner = .available) (unprotected : savedScope.held = false)
    (route : SourceDependencyCapture.checkClosing outward savedScope.shape [] [] = true)
    (callbacks : SourceScheduledCallbackInterfaces.Interfaces saved)
    (declared : SourceScheduledCallbackInterfaces.Declared world callbacks)
    (before : Interfaces world front) (after : Interfaces world tail)
    (callbackCheck : callbacks.check (.running (frontScope.append (.spent owner tailScope))) = true)
    (frontCheck : before.check (.spent owner tailScope) = true)
    (tailCheck : after.check .nil = true) :
    Local outward actions phases world (.invoke (key := ⟨owner, .dispose⟩)) whole := by
  have closingSchedule : Pending outward actions (spend phases owner) world
      saved.forClosing (.running (front.append (.spent (owner := owner) tail))) :=
    (callbacks.compile_declared declared callbackCheck).schedule
  have frontSchedule : Pending outward actions (spend phases owner) world
      front (.spent (owner := owner) tail) := before.compile frontCheck
  have tailSchedule : Pending outward actions (spend phases owner) world tail .nil := after.compile tailCheck
  exact dispose_from_parts cut known permission available unprotected
    (SourceDependencyCapture.check_closing_iff.mp route) closingSchedule frontSchedule tailSchedule
    (pending_dispose_iff.mpr ⟨closingSchedule, frontSchedule, tailSchedule⟩).compatible

end Ash.OneShot.SourceScheduledInvocationInterfaces

#print axioms Ash.OneShot.SourceScheduledInvocationInterfaces.resume_from_interfaces
#print axioms Ash.OneShot.SourceScheduledInvocationInterfaces.dispose_from_interfaces
