import SourceConsumingAdmissionWorld
import SourceConsumingGeneratedSource

/-! Structural source rechecking at the point of one-shot consumption. The
original saved/closing source remains fixed while clause constructors accumulate
the caller. Dormant source need not validate at intermediate receiver prefixes. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open SourceConsumingClauseAnnotations (Body Generated ContinuationBounds)
open SourceScheduledCapabilityAnnotations (Code Retained DeclarationPolicy DeclarationLaws)
open SourceScheduledRetainedInterfaces (Interfaces)
open SourceScheduledNeutral (OwnerCut)
open SourceScheduledSourceRechecking (ReceiverChange)
open OwnerPhaseTransitions (spend)

variable [declarations : DeclarationPolicy]

/-- Mapping original source into a larger world maps its exact continuation
snapshot; no receiver change or recompilation occurs in this operation. -/
theorem Context.world_weaken_continuationBounds
    {context : Context world owner outward actions phases whole front saved waiting}
    (larger : world ⊆ next) :
    (context.world_weaken larger).continuationBounds = context.continuationBounds.world_weaken larger := by
  simp only [Context.world_weaken, Context.continuationBounds, ContinuationBounds.world_weaken,
    Retained.ofCapability_world_weaken]

/-- Rules follow the consuming clause, retaining original source as evidence.
Only consumption asks for structural receiver rechecking. Primitive clause
requirements, rights and phase checks remain in the independent BoundCheck. -/
inductive AtUse [declarations : DeclarationPolicy] (outward : List Instance)
    (actions : Syntax.UsageTickets) (phases : OwnerPhaseTransitions.Phases) :
    {world : List Nat} → {owner : Nat} →
    {baseScope baseFrontScope savedScope waitingScope : SourceDependencyCapture.Scope} →
    {baseHints : Hints baseScope} → {baseFrontHints : Hints baseFrontScope} →
    {savedHints : Hints savedScope} → {waitingHints : Hints waitingScope} →
    {base : Forest baseHints} → {baseFront : Forest baseFrontHints} →
    {saved : Forest savedHints} → {waiting : Forest waitingHints} →
    Context world owner outward actions phases base baseFront saved waiting →
    {dependencies : SourceDependencyAnnotations.Dependencies} → {plan : Plan dependencies} →
    Body world owner plan → {frontScope : SourceDependencyCapture.Scope} →
    {frontHints : Hints frontScope} → Forest frontHints → Prop where
  | resume {world : List Nat} {owner : Nat}
      {baseScope baseFrontScope savedScope waitingScope frontScope : SourceDependencyCapture.Scope}
      {baseHints : Hints baseScope} {baseFrontHints : Hints baseFrontScope}
      {savedHints : Hints savedScope} {waitingHints : Hints waitingScope} {frontHints : Hints frontScope}
      {base : Forest baseHints} {baseFront : Forest baseFrontHints}
      {saved : Forest savedHints} {waiting : Forest waitingHints} {front : Forest frontHints}
      {context : Context world owner outward actions phases base baseFront saved waiting}
      (resumption : ∀ permission, ReceiverChange outward actions (spend phases owner)
        (context.resumption permission).val (front.append (.spent (owner := owner) waiting))) :
      AtUse outward actions phases context .resume front
  | dispose {world : List Nat} {owner : Nat}
      {baseScope baseFrontScope savedScope waitingScope frontScope : SourceDependencyCapture.Scope}
      {baseHints : Hints baseScope} {baseFrontHints : Hints baseFrontScope}
      {savedHints : Hints savedScope} {waitingHints : Hints waitingScope} {frontHints : Hints frontScope}
      {base : Forest baseHints} {baseFront : Forest baseFrontHints}
      {saved : Forest savedHints} {waiting : Forest waitingHints} {front : Forest frontHints}
      {context : Context world owner outward actions phases base baseFront saved waiting}
      (closing : ∀ permission, ReceiverChange outward actions (spend phases owner)
        (context.closing permission).val (.running (front.append (.spent (owner := owner) waiting)))) :
      AtUse outward actions phases context .dispose front
  | sequence {world : List Nat} {owner : Nat}
      {baseScope baseFrontScope savedScope waitingScope frontScope : SourceDependencyCapture.Scope}
      {baseHints : Hints baseScope} {baseFrontHints : Hints baseFrontScope}
      {savedHints : Hints savedScope} {waitingHints : Hints waitingScope} {frontHints : Hints frontScope}
      {base : Forest baseHints} {baseFront : Forest baseFrontHints}
      {saved : Forest savedHints} {waiting : Forest waitingHints} {front : Forest frontHints}
      {context : Context world owner outward actions phases base baseFront saved waiting}
      {body : Body world owner plan} {prefixCode : Plan prefixDependencies}
      {required : List SourceContextualHints.Requirement}
      {footprint : SourceScheduledAdaptationCompilation.RequestFootprint prefixCode required}
      {declared : SourceScheduledSourceInterfaces.Declared world (SourcePlanSignatures.signature prefixCode)}
      (rest : AtUse outward actions phases context body front) :
      AtUse outward actions phases context (.sequence required footprint declared body) front
  | choice {world : List Nat} {owner : Nat}
      {baseScope baseFrontScope savedScope waitingScope frontScope : SourceDependencyCapture.Scope}
      {baseHints : Hints baseScope} {baseFrontHints : Hints baseFrontScope}
      {savedHints : Hints savedScope} {waitingHints : Hints waitingScope} {frontHints : Hints frontScope}
      {base : Forest baseHints} {baseFront : Forest baseFrontHints}
      {saved : Forest savedHints} {waiting : Forest waitingHints} {front : Forest frontHints}
      {context : Context world owner outward actions phases base baseFront saved waiting}
      {first : Body world owner firstPlan} {second : Body world owner secondPlan}
      (left : AtUse outward actions phases context first front)
      (right : AtUse outward actions phases context second front) :
      AtUse outward actions phases context (.choice first second) front
  | handler {world : List Nat} {owner : Nat}
      {baseScope baseFrontScope savedScope waitingScope frontScope : SourceDependencyCapture.Scope}
      {baseHints : Hints baseScope} {baseFrontHints : Hints baseFrontScope}
      {savedHints : Hints savedScope} {waitingHints : Hints waitingScope} {frontHints : Hints frontScope}
      {base : Forest baseHints} {baseFront : Forest baseFrontHints}
      {saved : Forest savedHints} {waiting : Forest waitingHints} {front : Forest frontHints}
      {context : Context world owner outward actions phases base baseFront saved waiting}
      {body : Body world owner plan} {plans : SourceDeclarationPlans.ClausePlans clauses families}
      {bounds : SourceConsumingClauseAnnotations.ClauseBounds plans}
      {declared : declarations.accepts required plans}
      (inner : AtUse outward actions phases context body
        (.handler (effect := effect) (table := table) (families := families) (required := required) front)) :
      AtUse outward actions phases context
        (.handler (effect := effect) (table := table) (families := families) (required := required) bounds declared body) front
  | cleanup {world : List Nat} {owner : Nat}
      {baseScope baseFrontScope savedScope waitingScope frontScope : SourceDependencyCapture.Scope}
      {baseHints : Hints baseScope} {baseFrontHints : Hints baseFrontScope}
      {savedHints : Hints savedScope} {waitingHints : Hints waitingScope} {frontHints : Hints frontScope}
      {base : Forest baseHints} {baseFront : Forest baseFrontHints}
      {saved : Forest savedHints} {waiting : Forest waitingHints} {front : Forest frontHints}
      {context : Context world owner outward actions phases base baseFront saved waiting}
      {body : Body world owner plan} {callback : Plan callbackDependencies}
      {required : List SourceContextualHints.Requirement}
      {footprint : SourceScheduledAdaptationCompilation.RequestFootprint callback required}
      {declared : SourceScheduledSourceInterfaces.Declared world (SourcePlanSignatures.signature callback)}
      (covered : ∀ request ∈ required, request.1 ∈ needs)
      (inner : AtUse outward actions phases context body (.cleanup (needs := needs) callback front)) :
      AtUse outward actions phases context (.cleanup (needs := needs) (callback := callback) required footprint declared body) front
  | resource {world : List Nat} {owner : Nat}
      {baseScope baseFrontScope savedScope waitingScope frontScope : SourceDependencyCapture.Scope}
      {baseHints : Hints baseScope} {baseFrontHints : Hints baseFrontScope}
      {savedHints : Hints savedScope} {waitingHints : Hints waitingScope} {frontHints : Hints frontScope}
      {base : Forest baseHints} {baseFront : Forest baseFrontHints}
      {saved : Forest savedHints} {waiting : Forest waitingHints} {front : Forest frontHints}
      {context : Context world owner outward actions phases base baseFront saved waiting}
      {families : Nat → SourceDependencyAnnotations.Dependencies}
      {plans : ∀ identity, Plan (families identity)}
      {body : ∀ identity, identity ∉ world → Body (world ++ [identity]) owner (plans identity)}
      (each : ∀ identity fresh, AtUse outward actions phases
        (context.world_weaken (List.subset_append_left world [identity])) (body identity fresh) (.cell (identity := identity) front)) :
      AtUse outward actions phases context (.resource body) front

/-- Original annotations, rather than a new compiler choice, are transported
when resource worlds grow in more than one step. -/
theorem Context.world_weaken_trans
    (context : Context world owner outward actions phases base baseFront saved waiting)
    (first : world ⊆ middle) (second : middle ⊆ next) :
    (context.world_weaken first).world_weaken second = context.world_weaken (first.trans second) := by
  cases context
  simp only [Context.world_weaken, Interfaces.world_weaken_trans, Retained.world_weaken_trans]

/-- An already derived leaf judgment survives independent world allocation.
Actual receiver rechecking reuses its existing world-transport theorem. -/
theorem AtUse.world_weaken
    {context : Context world owner outward actions phases base baseFront saved waiting}
    {body : Body world owner plan} {front : Forest frontHints}
    (source : AtUse outward actions phases context body front) (larger : world ⊆ next) :
    AtUse outward actions phases (context.world_weaken larger) (body.world_weaken larger) front := by
  induction source generalizing next with
  | resume resumption => exact .resume (fun permission => (resumption permission).world_weaken larger)
  | dispose closing => exact .dispose (fun permission => (closing permission).world_weaken larger)
  | sequence source ih => exact .sequence (ih larger)
  | choice left right ihLeft ihRight => exact .choice (ihLeft larger) (ihRight larger)
  | handler source ih => exact .handler (ih larger)
  | cleanup covered source ih => exact .cleanup covered (ih larger)
  | resource each ih =>
      apply AtUse.resource
      intro identity fresh
      have oldFresh := fun member => fresh (larger member)
      have kept := ih identity oldFresh (ScopedExpressions.append_subset larger (List.Subset.refl [identity]))
      simpa only [Context.world_weaken_trans] using kept

/-- Inserting a builtin provider in the caller preserves every consuming
leaf, including rich saved callbacks and calls to outside owners. The original
source checks come from the context; receiver transport reuses the existing
provider proof and does not inspect a future execution. -/
theorem AtUse.provide
    {context : Context world owner outward actions phases base baseFront saved waiting}
    {body : Body world owner plan} {front : Forest frontHints}
    {nextHints : Hints nextScope} {next : Forest nextHints}
    (source : AtUse outward actions phases context body front)
    (inserted : SourceScheduledProviders.Insertion identity front next) :
    AtUse outward actions phases context body next := by
  induction source generalizing nextScope with
  | @resume world owner baseScope baseFrontScope savedScope waitingScope frontScope
      baseHints baseFrontHints savedHints waitingHints frontHints base baseFront saved waiting front context resumption =>
      exact .resume (fun permission => .provide (context.resumption permission).property
        (resumption permission) (inserted.suffix (.spent (owner := owner) waiting)))
  | @dispose world owner baseScope baseFrontScope savedScope waitingScope frontScope
      baseHints baseFrontHints savedHints waitingHints frontHints base baseFront saved waiting front context closing =>
      exact .dispose (fun permission => .provide (context.closing permission).property
        (closing permission) (.running (inserted.suffix (.spent (owner := owner) waiting))))
  | sequence source ih => exact .sequence (ih inserted)
  | choice left right ihLeft ihRight => exact .choice (ihLeft inserted) (ihRight inserted)
  | handler source ih => exact .handler (ih (.handler inserted))
  | cleanup covered source ih => exact .cleanup covered (ih (.cleanup inserted))
  | resource each ih => exact .resource (fun identity fresh => ih identity fresh (.cell inserted))

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]

/-- Reuse the existing receiver compiler at leaves; the structural traversal
assembles the clause and its Generated correspondence. Original waiting source
is retained exactly, and resource extension commutes with all three snapshots. -/
theorem AtUse.generate_source
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {baseHints : Hints baseScope} {baseFrontHints : Hints baseFrontScope}
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope} {frontHints : Hints frontScope}
    {base : Forest baseHints} {baseFront : Forest baseFrontHints}
    {saved : Forest savedHints} {waiting : Forest waitingHints} {front : Forest frontHints}
    {context : Context world owner outward actions phases base baseFront saved waiting}
    {body : Body world owner plan}
    (source : AtUse outward actions phases context body front)
    {wholeHints : Hints wholeScope} {whole : Forest wholeHints}
    (cut : OwnerCut owner whole front saved waiting) (before : Interfaces world front)
    (checked : body.BoundCheck resumeRequired closeRequired actions phases wholeScope waitingScope before) :
    ∃ annotation : Code world plan whole,
      annotation.Valid outward actions phases ∧ Generated actions context.continuationBounds body annotation := by
  induction source generalizing wholeScope with
  | @resume world owner baseScope baseFrontScope savedScope waitingScope frontScope baseHints baseFrontHints savedHints waitingHints frontHints base baseFront saved waiting front context resumption =>
      obtain ⟨inside, valid, kept⟩ := (resumption checked.1).compile_retaining laws project
        (context.resumption checked.1).property
      exact ⟨.resume cut inside (.operations before) context.after,
        ⟨checked.1, checked.2.1, valid, checked.2.2.2, context.tailReady⟩,
        .resume checked.1 kept rfl⟩
  | @dispose world owner baseScope baseFrontScope savedScope waitingScope frontScope baseHints baseFrontHints savedHints waitingHints frontHints base baseFront saved waiting front context closing =>
      obtain ⟨inside, valid, kept⟩ := (closing checked.1).compile_retaining laws project
        (context.closing checked.1).property
      exact ⟨.dispose cut inside (.operations before) context.after,
        ⟨checked.1, checked.2.1, (context.disposal checked.1).1, (context.disposal checked.1).2,
          valid, checked.2.2.2, context.tailReady⟩,
        .dispose checked.1 kept rfl⟩
  | sequence source ih =>
      obtain ⟨code, valid, generated⟩ := ih cut before checked.2
      refine ⟨.sequence (.operations _ _ _) code, ?_, .sequence generated⟩
      exact ⟨checked.1, valid⟩
  | choice left right ihLeft ihRight =>
      obtain ⟨leftCode, leftValid, leftGenerated⟩ := ihLeft cut before checked.1
      obtain ⟨rightCode, rightValid, rightGenerated⟩ := ihRight cut before checked.2
      exact ⟨.choice leftCode rightCode, ⟨leftValid, rightValid⟩, .choice leftGenerated rightGenerated⟩
  | handler source ih =>
      obtain ⟨code, valid, generated⟩ := ih (.handler cut) (.handler _ before) checked.2
      refine ⟨.handler _ code (some _), ?_, .handler generated⟩
      exact ⟨checked.1, valid⟩
  | cleanup covered source ih =>
      obtain ⟨code, valid, generated⟩ := ih (.cleanup cut) (.cleanup _ _ _ _ before) checked.1
      refine ⟨.cleanup code (.operations _ _ _), ?_, .cleanup generated⟩
      exact ⟨valid, checked.2⟩
  | resource each ih =>
      have result := fun identity fresh => ih identity fresh (.cell cut)
        (.cell (before.world_weaken (List.subset_append_left _ _))) (checked identity fresh)
      refine ⟨.resource (fun identity fresh => Classical.choose (result identity fresh)), ?_, .resource ?_⟩
      · exact fun identity fresh => (Classical.choose_spec (result identity fresh)).1
      · intro identity fresh
        simpa only [Context.world_weaken_continuationBounds] using (Classical.choose_spec (result identity fresh)).2

/-- Initial structural admission supplies the independent clause checks;
rich source rechecking remains the explicit structural leaf derivation. -/
theorem AtUse.initial_source
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    {context : Context world owner outward actions phases base baseFront saved waiting}
    {body : Body world owner plan}
    (source : AtUse outward actions phases context body .nil)
    (admitted : SourceConsumingClauseAnnotations.Admitted rights resumeRequired closeRequired body required)
    (known : actions owner = some rights) (available : phases owner = .available)
    (supplied : SourceContextualHints.checkRequirements waitingScope required = true) :
    ∃ annotation : Code world plan (.live (owner := owner) saved waiting),
      annotation.Valid outward actions phases ∧ Generated actions context.continuationBounds body annotation :=
  source.generate_source laws project .hit .nil (admitted.at_capture known available supplied)

end Ash.OneShot.SourceConsumingCleanupAdmission

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.world_weaken_continuationBounds
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.AtUse.generate_source

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.AtUse.initial_source

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.world_weaken_trans
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.AtUse.world_weaken

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.AtUse.provide
