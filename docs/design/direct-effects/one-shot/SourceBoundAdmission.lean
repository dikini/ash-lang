import SourceBoundResources
import SourceBoundComputation
import SourceConsumingBoundCongruence

/-! Structural admission of the exact retained annotation data. Recorded
bounds require their own consuming declaration derivation. Missing bounds use
the existing recipe evidence; absence cannot invent a bounded declaration. -/
namespace Ash.OneShot.SourcePlanBounds
open SourceDeclarationPlans (Plan ClausePlans)
open SourcePlanSignatures (signature clauseSignatures)
open SourceScheduledSourceInterfaces (Declared)
open SourceConsumingClauseAnnotations (Declarations Bounded)

variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]

inductive Annotation.Admitted : {world : List Nat} →
    {dependencies : SourceDependencyAnnotations.Dependencies} →
    {plan : Plan dependencies} → Annotation world plan → Prop where
  | absent (source : Declared world (signature plan)) : Admitted (.absent (world := world) (plan := plan))
  | sequence {left : Annotation world firstPlan} {right : Annotation world secondPlan} :
      Admitted left → Admitted right → Admitted (.sequence left right)
  | choice {left : Annotation world firstPlan} {right : Annotation world secondPlan} :
      Admitted left → Admitted right → Admitted (.choice left right)
  | inherited {code : Annotation world bodyPlan}
      (declarations : SourcePlannedRecipeDeclarations.Declarations required plans)
      (body : Admitted code) :
      Admitted (.handler (effect := effect) (table := table) (required := required) (plans := plans) none code)
  | bounded {code : Annotation world bodyPlan}
      (source : Declarations world plans) (checked : Bounded bounds source required)
      (body : Admitted code) :
      Admitted (.handler (effect := effect) (table := table) (required := required) (plans := plans) (some bounds) code)
  | cleanup {body : Annotation world bodyPlan} {callback : Annotation world callbackPlan} :
      Admitted body → Admitted callback →
      Admitted (.cleanup body callback : Annotation world (.cleanup (needs := needs) callbackPlan bodyPlan))
  | resource {dependencies : Nat → SourceDependencyAnnotations.Dependencies}
      {plans : ∀ identity, Plan (dependencies identity)}
      {code : ∀ identity, identity ∉ world → Annotation (world ++ [identity]) (plans identity)}
      (body : ∀ identity fresh, Admitted (code identity fresh)) : Admitted (.resource code)

omit nested in
theorem declared_handler_parts {plans : ClausePlans clauses families} {body : Plan dependencies}
    (source : Declared world (signature (.handler (effect := effect) (table := table) required plans body))) :
    SourcePlannedRecipeDeclarations.Declarations required plans ∧ Declared world (signature body) := by
  dsimp only [signature] at source
  generalize same : clauseSignatures plans = checking at source
  cases source with
  | handler declarations body => exact ⟨declarations.signature_congr same.symm, body⟩

theorem Annotation.Admitted.first {first : Plan firstDependencies} {second : Plan secondDependencies}
    {bounds : Annotation world (.sequence first second)} (admitted : bounds.Admitted) :
    bounds.first.Admitted := by
  cases admitted with
  | absent source => cases source with | sequence first second => exact .absent first
  | sequence first second => exact first

theorem Annotation.Admitted.second {first : Plan firstDependencies} {second : Plan secondDependencies}
    {bounds : Annotation world (.sequence first second)} (admitted : bounds.Admitted) :
    bounds.second.Admitted := by
  cases admitted with
  | absent source => cases source with | sequence first second => exact .absent second
  | sequence first second => exact second

theorem Annotation.Admitted.left {first : Plan firstDependencies} {second : Plan secondDependencies}
    {bounds : Annotation world (.choice first second)} (admitted : bounds.Admitted) :
    bounds.left.Admitted := by
  cases admitted with
  | absent source => cases source with | choice first second => exact .absent first
  | choice first second => exact first

theorem Annotation.Admitted.right {first : Plan firstDependencies} {second : Plan secondDependencies}
    {bounds : Annotation world (.choice first second)} (admitted : bounds.Admitted) :
    bounds.right.Admitted := by
  cases admitted with
  | absent source => cases source with | choice first second => exact .absent second
  | choice first second => exact second

def Annotation.handlerBody {plans : ClausePlans clauses families} {body : Plan dependencies} :
    Annotation world (.handler (effect := effect) (table := table) required plans body) → Annotation world body
  | .absent => .absent
  | .handler _ body => body

theorem Annotation.Admitted.handler_body {plans : ClausePlans clauses families} {body : Plan dependencies}
    {bounds : Annotation world (.handler (effect := effect) (table := table) required plans body)}
    (admitted : bounds.Admitted) : bounds.handlerBody.Admitted := by
  cases admitted with
  | absent source => exact .absent (declared_handler_parts source).2
  | inherited declarations body => exact body
  | bounded source checked body => exact body

/-- The route is determined by the retained data. A present packet supplies
admission for those exact bounds, not an unrelated existential bound choice. -/
theorem Annotation.Admitted.handler_declaration {plans : ClausePlans clauses families} {body : Plan dependencies}
    {bounds : Annotation world (.handler (effect := effect) (table := table) required plans body)}
    (admitted : bounds.Admitted) :
    match bounds.handlerBounds with
    | none => SourcePlannedRecipeDeclarations.Declarations required plans
    | some recorded => ∃ source : Declarations world plans, Bounded recorded source required := by
  cases admitted with
  | absent source => exact (declared_handler_parts source).1
  | inherited declarations body => exact declarations
  | bounded source checked body => exact ⟨source, checked⟩

theorem Annotation.Admitted.cleanup_body {callback : Plan callbackDependencies} {body : Plan bodyDependencies}
    {bounds : Annotation world (.cleanup (needs := needs) callback body)} (admitted : bounds.Admitted) :
    bounds.cleanupBody.Admitted := by
  cases admitted with
  | absent source => cases source with | cleanup callback body => exact .absent body
  | cleanup body callback => exact body

theorem Annotation.Admitted.cleanup_callback {callback : Plan callbackDependencies} {body : Plan bodyDependencies}
    {bounds : Annotation world (.cleanup (needs := needs) callback body)} (admitted : bounds.Admitted) :
    bounds.cleanupCallback.Admitted := by
  cases admitted with
  | absent source => cases source with | cleanup callback body => exact .absent callback
  | cleanup body callback => exact callback

theorem Annotation.Admitted.resource_body {dependencies : Nat → SourceDependencyAnnotations.Dependencies}
    {body : (identity : Nat) → Plan (dependencies identity)} {bounds : Annotation world (.resource body)}
    (admitted : bounds.Admitted) (fresh : identity ∉ world) : (bounds.resourceBody fresh).Admitted := by
  cases admitted with
  | absent source => cases source with | resource body => exact .absent (body identity fresh)
  | resource body => exact body identity fresh

theorem Annotation.Admitted.world_weaken {plan : Plan dependencies} {bounds : Annotation world plan}
    (admitted : bounds.Admitted) (larger : world ⊆ nextWorld) : (bounds.world_weaken larger).Admitted := by
  induction admitted generalizing nextWorld with
  | absent source => exact .absent (source.world_weaken larger)
  | sequence first second ihFirst ihSecond => exact .sequence (ihFirst larger) (ihSecond larger)
  | choice first second ihFirst ihSecond => exact .choice (ihFirst larger) (ihSecond larger)
  | inherited declarations body ih => exact .inherited declarations (ih larger)
  | bounded source checked body ih => exact .bounded (source.world_weaken larger) (checked.world_weaken larger) (ih larger)
  | cleanup body callback ihBody ihCallback => exact .cleanup (ihBody larger) (ihCallback larger)
  | resource body ih => exact .resource (fun identity fresh =>
      ih identity (fun member => fresh (larger member)) (ScopedExpressions.append_subset larger (List.Subset.refl _)))

end Ash.OneShot.SourcePlanBounds

namespace Ash.OneShot.SourceBoundSnapshots
variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]

inductive Retained.Admitted : {scope : SourceDependencyCapture.Scope} →
    {hints : SourceContextualHints.Hints scope} → {forest : SourceRetainedPlans.Forest hints} →
    Retained world forest → Prop where
  | nil : Admitted .nil
  | plain : SourcePlanBounds.Annotation.Admitted code → Admitted rest → Admitted (.plain code rest)
  | handler : Admitted rest → Admitted (.handler rest)
  | cell : Admitted rest → Admitted (.cell rest)
  | cleanup : SourcePlanBounds.Annotation.Admitted code → Admitted rest → Admitted (.cleanup code rest)
  | running : Admitted rest → Admitted (.running rest)
  | live : Admitted saved → Admitted rest → Admitted (.live saved rest)
  | spent : Admitted rest → Admitted (.spent rest)

def Snapshot.Admitted (snapshot : Snapshot world) : Prop :=
  snapshot.current.Admitted ∧ snapshot.pending.Admitted

theorem Retained.Admitted.world_weaken {pending : Retained world forest}
    (admitted : pending.Admitted) (larger : world ⊆ nextWorld) : (pending.world_weaken larger).Admitted := by
  induction admitted with
  | nil => exact .nil
  | plain code rest ih => exact .plain (code.world_weaken larger) ih
  | handler rest ih => exact .handler ih
  | cell rest ih => exact .cell ih
  | cleanup code rest ih => exact .cleanup (code.world_weaken larger) ih
  | running rest ih => exact .running ih
  | live saved rest ihSaved ihRest => exact .live ihSaved ihRest
  | spent rest ih => exact .spent ih

end Ash.OneShot.SourceBoundSnapshots

namespace Ash.OneShot.SourcePlanBounds.AdmissionExamples
open SourcePlanSignatures.Examples (plans)
open SourceConsumingClauseAnnotations (ClauseBounds Bounded)
open SourceConsumingClauseAnnotations.CongruenceExamples (bounds annotation admitted)

def valid : Annotation [] (.handler (effect := .user 92 []) (table := []) [] plans .pure) :=
  .handler (some bounds) .absent

theorem valid_admitted : valid.Admitted := .bounded annotation admitted (.absent .pure)

def missingRequirement : ClauseBounds plans :=
  .cons (.available ⟨[(.user 93 [], 0)], []⟩) .unavailable .nil

def invalid : Annotation [] (.handler (effect := .user 92 []) (table := []) [] plans .pure) :=
  .handler (some missingRequirement) .absent

/-- A resumption bound containing an unprovided operation cannot be admitted
merely because its data fit the checking plan. -/
theorem missing_requirement_rejected : ¬ invalid.Admitted := by
  intro accepted
  obtain ⟨source, checked⟩ := accepted.handler_declaration
  obtain ⟨contract, needed, body, found, sourceChecked, included⟩ :=
    checked.selected (owner := 9) .ordinary
  change some ⟨[(.user 93 [], 0)], []⟩ = some contract at found
  cases Option.some.inj found
  cases body
  have impossible : [(Instance.user 93 [], 0)] ⊆ [] := sourceChecked.resume_requirements.trans included
  exact List.not_mem_nil (impossible List.mem_cons_self)

end Ash.OneShot.SourcePlanBounds.AdmissionExamples

#print axioms Ash.OneShot.SourcePlanBounds.declared_handler_parts
#print axioms Ash.OneShot.SourcePlanBounds.Annotation.Admitted.first
#print axioms Ash.OneShot.SourcePlanBounds.Annotation.Admitted.second
#print axioms Ash.OneShot.SourcePlanBounds.Annotation.Admitted.left
#print axioms Ash.OneShot.SourcePlanBounds.Annotation.Admitted.right
#print axioms Ash.OneShot.SourcePlanBounds.Annotation.Admitted.handler_body
#print axioms Ash.OneShot.SourcePlanBounds.Annotation.Admitted.handler_declaration
#print axioms Ash.OneShot.SourcePlanBounds.Annotation.Admitted.cleanup_body
#print axioms Ash.OneShot.SourcePlanBounds.Annotation.Admitted.cleanup_callback
#print axioms Ash.OneShot.SourcePlanBounds.Annotation.Admitted.resource_body
#print axioms Ash.OneShot.SourcePlanBounds.Annotation.Admitted.world_weaken
#print axioms Ash.OneShot.SourceBoundSnapshots.Retained.Admitted.world_weaken

#print axioms Ash.OneShot.SourcePlanBounds.AdmissionExamples.valid_admitted
#print axioms Ash.OneShot.SourcePlanBounds.AdmissionExamples.missing_requirement_rejected
