import CoreStrictPotential
import CoreAdministrativeTransport
import CoreCleanupFrames
import SourceResourceRoutes

/-! Running cleanup retains an authenticated projected physical tail and the
original lexical handler scopes. Ordinary work is interpreted above this tail;
there is no opaque related suffix or callback-success premise. -/
namespace Ash.OneShot.CoreCleanupRunFrames
open ScopedExpressions ScopedExecution CoreValueRelation CoreStrictStack CoreStrictPotential CoreCleanupFrames

inductive RunningTail (graph : CoreSyntax.Graph) (heap : Heap) : List CoreMachine.Frame → Stack → Prop where
  | projected
      (captured : PushedWithMaps graph heap
        ((pendingOwners,pending) :: (savedOwners,.cleanupBoundary action environment data.identity) :: retainedMaps)
        (.push (.plain pendingPlain) (.push (.armed data) retainedTarget)))
      (delayed : CleanupRel graph savedOwners heap (.cleanupBoundary action environment data.identity) data)
      (retained : PushedWithMaps graph heap retainedMaps retainedTarget)
      (outside : PushedWithMaps graph heap outsideMaps outsideTarget)
      (projection : CoreMachine.closeFuel
        (CoreMachine.framesMass (pending :: .cleanupBoundary action environment data.identity :: framesOf retainedMaps) + 1)
        (pending :: .cleanupBoundary action environment data.identity :: framesOf retainedMaps) =
        .ok (.cleanupBoundary action environment data.identity :: closing,[])) :
      RunningTail graph heap
        (.cleanupCompletion data.identity .unit :: closing ++ .closeCompletion closeIdentity :: framesOf outsideMaps)
        (.push (.unwinding data) (retainedTarget.append (.push (.closing closeIdentity closeScope) outsideTarget)))

theorem RunningTail.heap_weaken (related : RunningTail graph heap physical lexical)
    (extension : HeapExtends heap larger) : RunningTail graph larger physical lexical := by
  cases related with
  | projected captured delayed retained outside projection =>
      exact .projected (captured.heap_weaken extension) (delayed.heap_weaken extension)
        (retained.heap_weaken extension) (outside.heap_weaken extension) projection

def isolate (state : CoreMachine.State) (annotations : List MappedFrame) : CoreMachine.State :=
  { state with frames := framesOf annotations }

def attach (target : Configuration) (tail : Stack) : Configuration :=
  { target with stack := target.stack.append tail }

/-- Only existing bounded ordinary families can authorize a same-target step.
The witness interprets the isolated prefix and preserves one literal target. -/
inductive Administrative (graph : CoreSyntax.Graph) (beforeOwners afterOwners : CoreTranslation.OwnerMap)
    (beforeMaps afterMaps : List MappedFrame) (before after : CoreMachine.State) (target : Configuration) : Prop where
  | traversal (witness : SilentMapped graph beforeOwners afterOwners beforeMaps afterMaps
      (isolate before beforeMaps) (isolate after afterMaps) target)
      (heap : after.heap = before.heap) : Administrative graph beforeOwners afterOwners beforeMaps afterMaps before after target
  | value (witness : CoreAdministrativeTransport.TransportMapped graph beforeOwners afterOwners beforeMaps afterMaps
      (isolate before beforeMaps) (isolate after afterMaps) target)
      (heap : after.heap = before.heap) : Administrative graph beforeOwners afterOwners beforeMaps afterMaps before after target

theorem Administrative.components (witness : Administrative graph bo ao bm am before after target) :
    ComponentMapped graph bo bm (isolate before bm) target ∧
    ComponentMapped graph ao am (isolate after am) target ∧ after.heap = before.heap ∧
    potential graph (isolate after am) < potential graph (isolate before bm) := by
  cases witness with
  | traversal proof heap | value proof heap => exact ⟨proof.current,proof.successor,heap,proof.decreasing⟩

theorem potential_splice (beforeFrames : before.frames = framesOf bm ++ physical)
    (afterFrames : after.frames = framesOf am ++ physical)
    (decreasing : potential graph (isolate after am) < potential graph (isolate before bm)) :
    potential graph after < potential graph before := by
  simp only [potential,isolate] at decreasing ⊢
  rw [beforeFrames,afterFrames]
  simp only [List.map_append,List.sum_append]
  omega

#print axioms RunningTail.heap_weaken
#print axioms Administrative.components
#print axioms potential_splice
end Ash.OneShot.CoreCleanupRunFrames
