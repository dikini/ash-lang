import SourceBoundAdmission

/-! Handler entry exposes the actual clause-plan witness while retaining the
original body and pending annotations. Installed runtime packets are connected
separately, avoiding a dependency on later runtime-stack proof modules. -/
namespace Ash.OneShot.SourcePlanBounds
open SourceDeclarationPlans (Plan ClausePlans)

theorem Annotation.handlerBody_lookup {plans : ClausePlans clauses families} {body : Plan dependencies}
    (bounds : Annotation world (.handler (effect := effect) (table := table) required plans body)) :
    bounds.handlerBody.lookup path operation held = bounds.lookup (.body path) operation held := by
  cases bounds <;> rfl

theorem Annotation.handlerBounds_lookup {plans : ClausePlans clauses families} {body : Plan dependencies}
    (bounds : Annotation world (.handler (effect := effect) (table := table) required plans body)) :
    bounds.handlerBounds.map (fun recorded => recorded.lookup operation held) = bounds.lookup .here operation held := by
  cases bounds <;> rfl

end Ash.OneShot.SourcePlanBounds

namespace Ash.OneShot.SourceBoundSnapshots
open SourceDeclarationPlans (Plan ClausePlans)
open SourcePlanBounds (Annotation)
open SourcePlanSignatures (clauseSignatures)
open SourceContextualHints (Hints Requirement)
open SourceRetainedPlans (Forest)

inductive EnteredHandler (effect : Instance) (table : List (Nat × ProtectionContracts.ClauseContract))
    (required : List Requirement) {clauses families} (actual : ClausePlans clauses families) :
    Snapshot world → Snapshot world → Prop where
  | step {checking : ClausePlans checkingClauses families} {body : Plan dependencies}
      {hints : Hints scope} {forest : Forest hints}
      (bounds : Annotation world (.handler (effect := effect) (table := table) required checking body))
      (remaining : Retained world forest) (same : clauseSignatures checking = clauseSignatures actual) :
      EnteredHandler effect table required actual ⟨_, _, bounds, _, hints, forest, remaining⟩
        ⟨_, body, bounds.handlerBody, _, _,
          .handler (effect := effect) (table := table) (families := families) (required := required) forest,
          .handler remaining⟩

theorem EnteredHandler.body_lookup {before after : Snapshot world}
    (step : EnteredHandler effect table required actual before after) :
    after.current.lookup path operation held = before.current.lookup (.body path) operation held := by
  cases step
  exact Annotation.handlerBody_lookup _

theorem EnteredHandler.admitted [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]
    {before after : Snapshot world} (step : EnteredHandler effect table required actual before after)
    (admitted : before.Admitted) : after.Admitted := by
  cases step
  exact ⟨admitted.1.handler_body, .handler admitted.2⟩

end Ash.OneShot.SourceBoundSnapshots

#print axioms Ash.OneShot.SourcePlanBounds.Annotation.handlerBody_lookup
#print axioms Ash.OneShot.SourcePlanBounds.Annotation.handlerBounds_lookup
#print axioms Ash.OneShot.SourceBoundSnapshots.EnteredHandler.body_lookup
#print axioms Ash.OneShot.SourceBoundSnapshots.EnteredHandler.admitted
