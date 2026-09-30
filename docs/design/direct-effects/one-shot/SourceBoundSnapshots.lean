import SourcePlanBounds

/-! Persistent source-bound data for current and queued plans. The snapshot
is separate from the proof of source typing; its indices keep those proofs
attached to the same actual plans. Installed handler packets remain in the
existing StackBounds data. No future execution check is stored here. -/
namespace Ash.OneShot.SourceBoundSnapshots
open SourceDependencyAnnotations (Dependencies)
open SourceDeclarationPlans (Plan)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourcePlanBounds (Annotation)

inductive Retained (world : List Nat) : {scope : SourceDependencyCapture.Scope} →
    {hints : Hints scope} → Forest hints → Type where
  | nil : Retained world .nil
  | plain (code : Annotation world plan) : Retained world rest → Retained world (.plain plan rest)
  | handler : Retained world rest →
      Retained world (.handler (effect := effect) (table := table) (families := families) (required := required) rest)
  | cell : Retained world rest → Retained world (.cell (identity := identity) rest)
  | cleanup (code : Annotation world callback) : Retained world rest → Retained world (.cleanup (needs := needs) callback rest)
  | running : Retained world rest → Retained world (.running rest)
  | live : Retained world saved → Retained world rest → Retained world (.live (owner := owner) saved rest)
  | spent : Retained world rest → Retained world (.spent (owner := owner) rest)

def Retained.absent {hints : Hints scope} (forest : Forest hints) : Retained world forest :=
  match forest with
  | .nil => .nil
  | .plain _ rest => .plain .absent (absent rest)
  | .handler rest => .handler (absent rest)
  | .cell rest => .cell (absent rest)
  | .cleanup _ rest => .cleanup .absent (absent rest)
  | .running rest => .running (absent rest)
  | .live saved rest => .live (absent saved) (absent rest)
  | .spent rest => .spent (absent rest)

def Retained.ofCapability [SourceScheduledCapabilityAnnotations.DeclarationPolicy]
    {hints : Hints scope} {outsideHints : Hints outsideScope} {forest : Forest hints} {outside : Forest outsideHints}
    (source : SourceScheduledCapabilityAnnotations.Retained world forest outside) : Retained world forest :=
  match source with
  | .operations _ => .absent forest
  | .plain code tail => .plain (SourcePlanBounds.ofCode code) (ofCapability tail)
  | .handler tail => .handler (ofCapability tail)
  | .cell tail => .cell (ofCapability tail)
  | .cleanup code tail => .cleanup (SourcePlanBounds.ofCode code) (ofCapability tail)
  | .running tail => .running (ofCapability tail)
  | .live saved tail => .live (ofCapability saved) (ofCapability tail)
  | .spent tail => .spent (ofCapability tail)

structure Snapshot (world : List Nat) where
  dependencies : Dependencies
  plan : Plan dependencies
  current : Annotation world plan
  scope : SourceDependencyCapture.Scope
  hints : Hints scope
  forest : Forest hints
  pending : Retained world forest

def Snapshot.initial [SourceScheduledCapabilityAnnotations.DeclarationPolicy]
    {plan : Plan initialDependencies}
    (annotation : SourceScheduledCapabilityAnnotations.Code world plan .nil) : Snapshot world :=
  ⟨_, plan, SourcePlanBounds.ofCode annotation, _, .nil, .nil, .nil⟩

/-- Focusing physically queues the original pending-plan metadata. The
remaining queue is the original value, not a newly chosen annotation. -/
def Snapshot.focus (source : Snapshot world) (child : Plan childDependencies) (rest : Plan restDependencies)
    (childBounds : Annotation world child) (restBounds : Annotation world rest) : Snapshot world :=
  ⟨_, child, childBounds, _, .plain source.hints, .plain rest source.forest, .plain restBounds source.pending⟩

/-- Returning to a queued context removes exactly its metadata frame. The
recomposed current plan and bounds are supplied by source recomposition. -/
def Snapshot.returned {hints : Hints receivingScope} {tail : Forest hints} {context : Plan contextDependencies}
    (pending : Retained world (.plain context tail))
    (plan : Plan nextDependencies) (bounds : Annotation world plan) : Snapshot world :=
  match pending with
  | .plain _ remaining => ⟨_, plan, bounds, _, hints, tail, remaining⟩

theorem Snapshot.focus_pending (source : Snapshot world) (child : Plan childDependencies) (rest : Plan restDependencies)
    (childBounds : Annotation world child) (restBounds : Annotation world rest) :
    (source.focus child rest childBounds restBounds).pending = .plain restBounds source.pending := rfl

theorem Snapshot.returned_pending {hints : Hints receivingScope} {tail : Forest hints} {context : Plan contextDependencies}
    (queued : Annotation world context) (remaining : Retained world tail)
    (plan : Plan nextDependencies) (bounds : Annotation world plan) :
    (Snapshot.returned (.plain queued remaining) plan bounds).pending = remaining := rfl

end Ash.OneShot.SourceBoundSnapshots

#print axioms Ash.OneShot.SourceBoundSnapshots.Snapshot.focus_pending
#print axioms Ash.OneShot.SourceBoundSnapshots.Snapshot.returned_pending
