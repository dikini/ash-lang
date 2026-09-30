import SourceScheduledPendingSites
import SourceScheduledScopedInvocations

/-! Scheduled invocation transport reuses exact owner cuts and retained-code
sites. The local transformer is the remaining recursive proof obligation,
not an opaque source annotation or a replacement Pending certificate. -/
namespace Ash.OneShot.SourceScheduledHandlerInvocations
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open SourceDependencyCapture (Scope)
open SourceScheduledChecks (Local Pending)
open SourceScheduledNeutral (OwnerCut)
open SourceScheduledInterpretationInsertion (Insertion Split)
open SourceScheduledPendingSites (Site pending_handler_inside)
open SourceScheduledScopedInvocations (resume_iff dispose_iff pending_resume_iff pending_dispose_iff)

variable {beforeHints : Hints beforeScope} {afterHints : Hints afterScope}
  {frontHints : Hints frontScope} {savedHints : Hints savedScope} {tailHints : Hints tailScope}
  {nextFrontHints : Hints nextFrontScope} {nextTailHints : Hints nextTailScope}
  {before : Forest beforeHints} {after : Forest afterHints}
  {front : Forest frontHints} {saved : Forest savedHints} {tail : Forest tailHints}
  {nextFront : Forest nextFrontHints} {nextTail : Forest nextTailHints}

/-- Complete the resume case once affected retained-code sites are
transported at the spent phase. Unaffected code is reused by the site theorem. -/
theorem resume_transport
    (beforeCut : OwnerCut owner before front saved tail)
    (afterCut : OwnerCut owner after nextFront saved nextTail)
    (pieces : Split (.handler effect table families required) front tail nextFront nextTail)
    (checked : Local outward actions phases world (.invoke (key := ⟨owner, .resume⟩)) before)
    (supplied : SourceHandlerInvocations.Interface effect table families required .nil
      (savedHints.append (frontHints.append (.spent (owner := owner) tailHints)))
      (savedHints.append (nextFrontHints.append (.spent (owner := owner) nextTailHints))))
    (transfer : ∀ {dependencies oldScope targetScope} {plan : Plan dependencies}
      {oldHints : Hints oldScope} {targetHints : Hints targetScope}
      (old : Forest oldHints) (target : Forest targetHints),
      Site (saved.append (front.append (.spent (owner := owner) tail))) .nil plan old →
      Insertion (.handler effect table families required) old target →
      Local outward actions (OwnerPhaseTransitions.spend phases owner) world plan old →
      Local outward actions (OwnerPhaseTransitions.spend phases owner) world plan target) :
    Local outward actions phases world (.invoke (key := ⟨owner, .resume⟩)) after := by
  obtain ⟨access, inside, caller, waiting⟩ := (resume_iff beforeCut).mp checked
  have original := pending_resume_iff.mpr ⟨inside, caller, waiting⟩
  have restored := pending_handler_inside original (pieces.resumed saved) supplied transfer
  have nextAccess := SourceHandlerInvocations.resume_admitted beforeCut.found afterCut.found access supplied
  exact .resume afterCut.found nextAccess afterCut.forest restored

/-- Disposal uses the same selected saved plan's closing forest and the
existing running boundary. Its original guard, owner permissions and source
schedule all come from the old invocation derivation. -/
theorem dispose_transport
    (beforeCut : OwnerCut owner before front saved tail)
    (afterCut : OwnerCut owner after nextFront saved nextTail)
    (pieces : Split (.handler effect table families required) front tail nextFront nextTail)
    (checked : Local outward actions phases world (.invoke (key := ⟨owner, .dispose⟩)) before)
    (supplied : SourceHandlerInvocations.Interface effect table families required .nil
      ((SourceContextualInvocationHints.forClosing savedHints).append
        (.running (frontHints.append (.spent (owner := owner) tailHints))))
      ((SourceContextualInvocationHints.forClosing savedHints).append
        (.running (nextFrontHints.append (.spent (owner := owner) nextTailHints)))))
    (transfer : ∀ {dependencies oldScope targetScope} {plan : Plan dependencies}
      {oldHints : Hints oldScope} {targetHints : Hints targetScope}
      (old : Forest oldHints) (target : Forest targetHints),
      Site (saved.forClosing.append (.running (front.append (.spent (owner := owner) tail)))) .nil plan old →
      Insertion (.handler effect table families required) old target →
      Local outward actions (OwnerPhaseTransitions.spend phases owner) world plan old →
      Local outward actions (OwnerPhaseTransitions.spend phases owner) world plan target) :
    Local outward actions phases world (.invoke (key := ⟨owner, .dispose⟩)) after := by
  obtain ⟨access, closing, caller, waiting⟩ := (dispose_iff beforeCut).mp checked
  have original := pending_dispose_iff.mpr ⟨closing, caller, waiting⟩
  have scheduled := pending_handler_inside original (pieces.disposed saved) supplied transfer
  have nextAccess := SourceHandlerInvocations.dispose_admitted beforeCut.found afterCut.found (pieces.owner savedHints) access supplied
  exact .dispose afterCut.found nextAccess afterCut.forest scheduled

end Ash.OneShot.SourceScheduledHandlerInvocations

#print axioms Ash.OneShot.SourceScheduledHandlerInvocations.resume_transport
#print axioms Ash.OneShot.SourceScheduledHandlerInvocations.dispose_transport
