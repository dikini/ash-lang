import SourceBoundReturns

/-! Leaving a completed boundary retains the exact remaining metadata.
The returned value uses the existing pure checking plan. Callable latent
admission remains a separate source obligation. -/
namespace Ash.OneShot.SourcePlanBounds
open SourceDeclarationPlans (Plan)

def Annotation.cleanupBody {callback : Plan callbackDependencies} {body : Plan bodyDependencies} :
    Annotation world (.cleanup (needs := needs) callback body) → Annotation world body
  | .absent => .absent
  | .cleanup body _ => body

def Annotation.cleanupCallback {callback : Plan callbackDependencies} {body : Plan bodyDependencies} :
    Annotation world (.cleanup (needs := needs) callback body) → Annotation world callback
  | .absent => .absent
  | .cleanup _ callback => callback

theorem Annotation.cleanupBody_lookup {callback : Plan callbackDependencies} {body : Plan bodyDependencies}
    (bounds : Annotation world (.cleanup (needs := needs) callback body)) :
    bounds.cleanupBody.lookup path operation held = bounds.lookup (.body path) operation held := by
  cases bounds <;> rfl

theorem Annotation.cleanupCallback_lookup {callback : Plan callbackDependencies} {body : Plan bodyDependencies}
    (bounds : Annotation world (.cleanup (needs := needs) callback body)) :
    bounds.cleanupCallback.lookup path operation held = bounds.lookup (.callback path) operation held := by
  cases bounds <;> rfl

end Ash.OneShot.SourcePlanBounds

namespace Ash.OneShot.SourceBoundSnapshots
open SourceDeclarationPlans (Plan)
open SourcePlanBounds (Annotation)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)

/-- A returned value with the original retained queue. -/
def Snapshot.value {hints : Hints receivingScope} {forest : Forest hints}
    (pending : Retained world forest) : Snapshot world :=
  ⟨_, .pure, .absent, _, hints, forest, pending⟩

theorem Snapshot.value_pending {hints : Hints receivingScope} {forest : Forest hints}
    (pending : Retained world forest) : (Snapshot.value pending).pending = pending := rfl

inductive Boundary where
  | handler | cell | running | spent

inductive Exited : Boundary → Snapshot world → Snapshot world → Prop where
  | handler {current : Plan currentDependencies} {hints : Hints scope} {forest : Forest hints}
      (bounds : Annotation world current) (remaining : Retained world forest) :
      Exited .handler
        ⟨_, current, bounds, _, _,
          .handler (effect := effect) (table := table) (families := families) (required := required) forest, .handler remaining⟩
        (Snapshot.value remaining)
  | cell {current : Plan currentDependencies} {hints : Hints scope} {forest : Forest hints}
      (bounds : Annotation world current) (remaining : Retained world forest) :
      Exited .cell ⟨_, current, bounds, _, _, .cell (identity := identity) forest, .cell remaining⟩
        (Snapshot.value remaining)
  | running {current : Plan currentDependencies} {hints : Hints scope} {forest : Forest hints}
      (bounds : Annotation world current) (remaining : Retained world forest) :
      Exited .running ⟨_, current, bounds, _, _, .running forest, .running remaining⟩
        (Snapshot.value remaining)
  | spent {current : Plan currentDependencies} {hints : Hints scope} {forest : Forest hints}
      (bounds : Annotation world current) (remaining : Retained world forest) :
      Exited .spent ⟨_, current, bounds, _, _, .spent (owner := owner) forest, .spent remaining⟩
        (Snapshot.value remaining)

/-- Only the completed boundary disappears. No queued code or dormant saved
branch is replaced, and no bound packet is invented for the returned value. -/
theorem Exited.current {before after : Snapshot world} (step : Exited boundary before after) :
    after.current.lookup path operation held = none := by cases step <;> rfl

/-- Invoke the saved callback under the existing running marker. The two pure
prefixes are exactly the existing application checking signature. -/
def Snapshot.startCleanup {callback : Plan callbackDependencies}
    {hints : Hints receivingScope} {forest : Forest hints}
    (queued : Annotation world callback) (remaining : Retained world forest) : Snapshot world :=
  ⟨_, .sequence .pure (.sequence .pure callback), .sequence .absent (.sequence .absent queued),
    _, .running hints, .running forest, .running remaining⟩

inductive StartedCleanup : Snapshot world → Snapshot world → Prop where
  | step {current : Plan currentDependencies} {callback : Plan callbackDependencies}
      {hints : Hints scope} {forest : Forest hints}
      (bounds : Annotation world current) (queued : Annotation world callback) (remaining : Retained world forest) :
      StartedCleanup
        ⟨_, current, bounds, _, _, .cleanup (needs := needs) callback forest, .cleanup queued remaining⟩
        (Snapshot.startCleanup queued remaining)

theorem Snapshot.startCleanup_lookup {callback : Plan callbackDependencies}
    {hints : Hints receivingScope} {forest : Forest hints}
    (queued : Annotation world callback) (remaining : Retained world forest) :
    (Snapshot.startCleanup queued remaining).current.lookup (.second (.second path)) operation held =
      queued.lookup path operation held := rfl

/-- Cleanup installation keeps the source body current and queues the exact
latent callback packet above the unchanged remaining annotations. -/
inductive EnteredCleanup : Snapshot world → Snapshot world → Prop where
  | step {initial : Plan initialDependencies} {callback : Plan callbackDependencies} {body : Plan bodyDependencies}
      {hints : Hints scope} {forest : Forest hints}
      (bounds : Annotation world (.sequence initial (.cleanup (needs := needs) callback body)))
      (remaining : Retained world forest) :
      EnteredCleanup ⟨_, _, bounds, _, hints, forest, remaining⟩
        ⟨_, body, bounds.second.cleanupBody, _, _, .cleanup (needs := needs) callback forest,
          .cleanup bounds.second.cleanupCallback remaining⟩

theorem EnteredCleanup.body_lookup {before after : Snapshot world} (step : EnteredCleanup before after) :
    after.current.lookup path operation held = before.current.lookup (.second (.body path)) operation held := by
  cases step
  simp only [SourcePlanBounds.Annotation.cleanupBody_lookup, SourcePlanBounds.Annotation.second_lookup]

end Ash.OneShot.SourceBoundSnapshots

#print axioms Ash.OneShot.SourceBoundSnapshots.Exited.current

#print axioms Ash.OneShot.SourceBoundSnapshots.Snapshot.startCleanup_lookup

#print axioms Ash.OneShot.SourceBoundSnapshots.Snapshot.value_pending

#print axioms Ash.OneShot.SourcePlanBounds.Annotation.cleanupBody_lookup
#print axioms Ash.OneShot.SourcePlanBounds.Annotation.cleanupCallback_lookup
#print axioms Ash.OneShot.SourceBoundSnapshots.EnteredCleanup.body_lookup
