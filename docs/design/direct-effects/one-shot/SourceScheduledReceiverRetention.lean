import SourceBoundSnapshots
import SourceScheduledCapabilityReconstruction

/-! Shared metadata retention for receiver transformations. The laws describe
proved transport theorems for a relation, not additional source-admission
premises. Neutral expansion and provider insertion instantiate this same proof. -/
namespace Ash.OneShot.SourceScheduledCapabilityAnnotations
open SourceContextualHints (Hints checkRequirements)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open SourcePlanBounds (ofCode)
open SourceBoundSnapshots.Retained (ofCapability)

abbrev ReceiverRelation := {first second : SourceDependencyCapture.Scope} →
  {beforeHints : Hints first} → {afterHints : Hints second} → Forest beforeHints → Forest afterHints → Prop

structure ReceiverLaws [DeclarationPolicy] (relation : ReceiverRelation)
    (outward : List Instance) (actions : Syntax.UsageTickets) (phases : OwnerPhaseTransitions.Phases) : Prop where
  requirements {beforeHints : Hints first} {afterHints : Hints second}
      {before : Forest beforeHints} {after : Forest afterHints} :
    relation before after → checkRequirements first required = true → checkRequirements second required = true
  transport {world : List Nat} {plan : Plan dependencies} {beforeHints : Hints first} {afterHints : Hints second}
      {before : Forest beforeHints} {after : Forest afterHints} (source : Code world plan before) :
    source.Valid outward actions phases → relation before after → ∃ next : Code world plan after, next.Valid outward actions phases
  plain {before : Forest beforeHints} {after : Forest afterHints} :
    relation before after → relation (.plain plan before) (.plain plan after)
  handler {before : Forest beforeHints} {after : Forest afterHints} :
    relation before after → relation (.handler (effect := effect) (table := table) (families := families) (required := required) before) (.handler (effect := effect) (table := table) (families := families) (required := required) after)
  cell {before : Forest beforeHints} {after : Forest afterHints} :
    relation before after → relation (.cell (identity := identity) before) (.cell (identity := identity) after)
  cleanup {before : Forest beforeHints} {after : Forest afterHints} :
    relation before after → relation (.cleanup (needs := needs) plan before) (.cleanup (needs := needs) plan after)
  running {before : Forest beforeHints} {after : Forest afterHints} :
    relation before after → relation (.running before) (.running after)
  live {before : Forest beforeHints} {after : Forest afterHints} :
    relation before after → relation (.live (owner := owner) saved before) (.live (owner := owner) saved after)
  spent {before : Forest beforeHints} {after : Forest afterHints} :
    relation before after → relation (.spent (owner := owner) before) (.spent (owner := owner) after)

variable [DeclarationPolicy]

/-- Prefix closure follows from the same per-frame receiver laws. -/
theorem ReceiverLaws.prefix (laws : ReceiverLaws relation outward actions phases)
    (front : Forest hints) (changed : relation before after) :
    relation (front.append before) (front.append after) := by
  induction front with
  | nil => exact changed
  | plain plan rest ih => exact laws.plain ih
  | handler rest ih => exact laws.handler ih
  | cell rest ih => exact laws.cell ih
  | cleanup plan rest ih => exact laws.cleanup ih
  | running rest ih => exact laws.running ih
  | live saved rest ihSaved ih => exact laws.live ih
  | spent rest ih => exact laws.spent ih

/-- The existing current-syntax retention induction, parameterized by proved
receiver transport and primitive requirement preservation. -/
theorem Code.receiver_retaining
    (laws : ReceiverLaws relation outward actions phases)
    {beforeHints : Hints beforeScope} {before : Forest beforeHints} {plan : Plan dependencies}
    (source : Code world plan before) (ready : source.Valid outward actions phases)
    {afterHints : Hints afterScope} {after : Forest afterHints} (changed : relation before after) :
    ∃ annotation : Code world plan after, annotation.Valid outward actions phases ∧
      ofCode annotation = ofCode source := by
  revert afterScope
  revert ready
  apply Code.rec
    (motive_1 := fun world {dependencies scope hints} plan before source =>
      source.Valid outward actions phases → ∀ {afterScope} {afterHints : Hints afterScope} (after : Forest afterHints),
        relation before after → ∃ annotation : Code world plan after,
          annotation.Valid outward actions phases ∧ ofCode annotation = ofCode source)
    (motive_2 := fun _ {_ _ _ _} _ _ _ => True)
    (t := source)
  all_goals intros
  all_goals first
    | trivial
    | (rename_i required footprint declared ready afterScope afterHints after changed
       refine ⟨.operations required footprint declared, ?_, rfl⟩
       change SourceContextualHints.checkRequirements _ required = true
       exact laws.requirements changed ready)
    | (rename_i cut bounded closing ih ready afterScope afterHints after changed
       obtain ⟨annotation, valid⟩ := laws.transport (Code.selected cut bounded closing) ready changed
       refine ⟨annotation, valid, ?_⟩
       cases annotation <;> rfl)
    | (rename_i cut inside before tail ihInside ihBefore ihTail ready afterScope afterHints after changed
       obtain ⟨annotation, valid⟩ := laws.transport (Code.resume cut inside before tail) ready changed
       refine ⟨annotation, valid, ?_⟩
       cases annotation <;> rfl)
    | (rename_i cut closing before tail ihClosing ihBefore ihTail ready afterScope afterHints after changed
       obtain ⟨annotation, valid⟩ := laws.transport (Code.dispose cut closing before tail) ready changed
       refine ⟨annotation, valid, ?_⟩
       cases annotation <;> rfl)
    | (rename_i first second ihFirst ihSecond ready afterScope afterHints after changed
       obtain ⟨first, firstReady, firstBounds⟩ := ihFirst ready.1 _ (laws.plain changed)
       obtain ⟨second, secondReady, secondBounds⟩ := ihSecond ready.2 _ changed
       exact ⟨.sequence first second, ⟨firstReady, secondReady⟩,
         by simp only [ofCode, firstBounds, secondBounds]⟩)
    | (rename_i first second ihFirst ihSecond ready afterScope afterHints after changed
       obtain ⟨first, firstReady, firstBounds⟩ := ihFirst ready.1 _ changed
       obtain ⟨second, secondReady, secondBounds⟩ := ihSecond ready.2 _ changed
       exact ⟨.choice first second, ⟨firstReady, secondReady⟩,
         by simp only [ofCode, firstBounds, secondBounds]⟩)
    | (rename_i declared body bounds ih ready afterScope afterHints after changed
       obtain ⟨body, bodyReady, bodyBounds⟩ := ih ready.2 _ (laws.handler changed)
       exact ⟨.handler declared body bounds, ⟨laws.requirements changed ready.1, bodyReady⟩,
         congrArg (SourcePlanBounds.Annotation.handler bounds) bodyBounds⟩)
    | (rename_i body completion ihBody ihCompletion ready afterScope afterHints after changed
       obtain ⟨body, bodyReady, bodyBounds⟩ := ihBody ready.1 _ (laws.cleanup changed)
       obtain ⟨completion, completionReady, completionBounds⟩ := ihCompletion ready.2 _ (laws.running changed)
       exact ⟨.cleanup body completion, ⟨bodyReady, completionReady⟩,
         by simp only [ofCode, bodyBounds, completionBounds]⟩)
    | (rename_i body ih ready afterScope afterHints after changed
       have generated := fun identity fresh => ih identity fresh (ready identity fresh) _ (laws.cell changed)
       refine ⟨.resource (fun identity fresh => Classical.choose (generated identity fresh)),
         (fun identity fresh => (Classical.choose_spec (generated identity fresh)).1), ?_⟩
       exact congrArg SourcePlanBounds.Annotation.resource
         (funext fun identity => funext fun fresh => (Classical.choose_spec (generated identity fresh)).2))

private def forestOf {forest : Forest hints} (_ : Retained world forest outside) : Forest hints := forest

/-- The existing retained-syntax induction keeps the forest fixed and prefixes
receiver changes through callbacks and dormant saved code. -/
theorem Retained.receiver_retaining
    (laws : ReceiverLaws relation outward actions phases)
    {hints : Hints scope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints}
    (source : Retained world forest outside) (ready : source.Valid outward actions phases)
    {nextHints : Hints nextScope} {next : Forest nextHints} (changed : relation outside next) :
    ∃ annotation : Retained world forest next, annotation.Valid outward actions phases ∧
      ofCapability annotation = ofCapability source := by
  revert nextScope
  revert ready
  apply Retained.rec
    (motive_1 := fun _ {_ _ _} _ _ _ => True)
    (motive_2 := fun world {scope outsideScope hints outsideHints} forest outside source =>
      source.Valid outward actions phases → ∀ {nextScope} {nextHints : Hints nextScope} (next : Forest nextHints),
        relation outside next → ∃ annotation : Retained world forest next,
          annotation.Valid outward actions phases ∧ ofCapability annotation = ofCapability source)
    (t := source)
  all_goals intros
  all_goals first
    | trivial
    | (rename_i interfaces ready nextScope nextHints next changed
       refine ⟨.operations interfaces, ?_, rfl⟩
       exact interfaces.check_transport ready (laws.requirements changed (interfaces.exposed_requirements ready)))
    | (rename_i code tail ihCode ihTail ready nextScope nextHints next changed
       obtain ⟨code, codeReady, codeKept⟩ := code.receiver_retaining laws ready.1 (laws.prefix _ changed)
       obtain ⟨tail, tailReady, tailKept⟩ := ihTail ready.2 _ changed
       refine ⟨.plain code tail, ⟨codeReady, tailReady⟩, ?_⟩
       simp only [ofCapability, codeKept, tailKept])
    | (rename_i tail ih ready nextScope nextHints next changed
       have supplied := laws.requirements (laws.prefix (forestOf tail) changed) ready.1
       obtain ⟨tail, tailReady, tailKept⟩ := ih ready.2 _ changed
       exact ⟨.handler tail, ⟨supplied, tailReady⟩, congrArg SourceBoundSnapshots.Retained.handler tailKept⟩)
    | (rename_i tail ih ready nextScope nextHints next changed
       obtain ⟨tail, tailReady, tailKept⟩ := ih ready _ changed
       exact ⟨.cell tail, tailReady, congrArg SourceBoundSnapshots.Retained.cell tailKept⟩)
    | (rename_i code tail ihCode ihTail ready nextScope nextHints next changed
       obtain ⟨code, codeReady, codeKept⟩ := code.receiver_retaining laws ready.1 (laws.running (laws.prefix _ changed))
       obtain ⟨tail, tailReady, tailKept⟩ := ihTail ready.2 _ changed
       refine ⟨.cleanup code tail, ⟨codeReady, tailReady⟩, ?_⟩
       simp only [ofCapability, codeKept, tailKept])
    | (rename_i tail ih ready nextScope nextHints next changed
       obtain ⟨tail, tailReady, tailKept⟩ := ih ready _ changed
       exact ⟨.running tail, tailReady, congrArg SourceBoundSnapshots.Retained.running tailKept⟩)
    | (rename_i saved tail ihSaved ihTail ready nextScope nextHints next changed
       obtain ⟨saved, savedReady, savedKept⟩ := ihSaved ready.1 _ (laws.prefix _ changed)
       obtain ⟨tail, tailReady, tailKept⟩ := ihTail ready.2 _ changed
       refine ⟨.live saved tail, ⟨savedReady, tailReady⟩, ?_⟩
       simp only [ofCapability, savedKept, tailKept])
    | (rename_i tail ih ready nextScope nextHints next changed
       obtain ⟨tail, tailReady, tailKept⟩ := ih ready _ changed
       exact ⟨.spent tail, tailReady, congrArg SourceBoundSnapshots.Retained.spent tailKept⟩)

end Ash.OneShot.SourceScheduledCapabilityAnnotations

#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.ReceiverLaws.prefix
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.receiver_retaining
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Retained.receiver_retaining
