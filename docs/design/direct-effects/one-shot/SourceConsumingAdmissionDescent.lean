import SourceConsumingCleanupAdmission

/-! Inversion of contextual source admission. The child retains its actual
physical owner cut and caller interface, even when the parent admission used
alternative annotation witnesses. No transition or target validity is assumed.
Sequence descent is syntactic: execution of its prefix requires additional
world and phase transport. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission
open SourceContextualHints (Hints)
open SourceDependencyCapture (Scope)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceConsumingClauseAnnotations (Body)
open SourceScheduledCapabilityAnnotations (DeclarationPolicy DeclarationLaws)
open SourceScheduledRetainedInterfaces (Interfaces)

variable [declarations : DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]

/-- The immediate source children, with exact entered physical contexts.
This definition inspects source syntax; it adds no admission premise. -/
def Descendants
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {world : List Nat} {owner : Nat} {plan : Plan dependencies} (body : Body world owner plan)
    {wholeScope frontScope savedScope waitingScope : Scope}
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (context : Context world owner outward actions phases whole front saved waiting) : Prop :=
  match body with
  | .resume | .dispose => True
  | .sequence _ _ _ rest => At laws (@project) rest context
  | .choice first second => At laws (@project) first context ∧ At laws (@project) second context
  | .handler (effect := effect) (table := table) (required := required) (families := families) _ _ inner =>
      ∃ child : Context world owner outward actions phases
        (.handler (effect := effect) (table := table) (families := families) (required := required) whole)
        (.handler (effect := effect) (table := table) (families := families) (required := required) front) saved waiting,
        child.before = Interfaces.handler front context.before ∧ At laws (@project) inner child
  | .cleanup (needs := needs) (callback := callback) required footprint declared inner =>
      ∃ child : Context world owner outward actions phases
        (.cleanup (needs := needs) callback whole) (.cleanup (needs := needs) callback front) saved waiting,
        child.before = Interfaces.cleanup front required footprint declared context.before ∧ At laws (@project) inner child
  | .resource inner => ∀ identity fresh,
      ∃ child : Context (world ++ [identity]) owner outward actions phases
        (.cell (identity := identity) whole) (.cell (identity := identity) front) saved waiting,
        child.before = Interfaces.cell (context.before.world_weaken (List.subset_append_left _ _)) ∧
        At laws (@project) (inner identity fresh) child

/-- Immediate children also retain their parent continuation metadata. -/
def ExactDescendants
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {world : List Nat} {owner : Nat} {plan : Plan dependencies} (body : Body world owner plan)
    {wholeScope frontScope savedScope waitingScope : Scope}
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (context : Context world owner outward actions phases whole front saved waiting) : Prop :=
  match body with
  | .resume | .dispose => True
  | .sequence _ _ _ rest => At laws (@project) rest context
  | .choice first second => At laws (@project) first context ∧ At laws (@project) second context
  | .handler (effect := effect) (table := table) (required := required) (families := families) _ _ inner =>
      ∃ child : Context world owner outward actions phases
        (.handler (effect := effect) (table := table) (families := families) (required := required) whole)
        (.handler (effect := effect) (table := table) (families := families) (required := required) front) saved waiting,
        child.before = Interfaces.handler front context.before ∧ context.BoundsAgree child ∧ At laws (@project) inner child
  | .cleanup (needs := needs) (callback := callback) required footprint declared inner =>
      ∃ child : Context world owner outward actions phases
        (.cleanup (needs := needs) callback whole) (.cleanup (needs := needs) callback front) saved waiting,
        child.before = Interfaces.cleanup front required footprint declared context.before ∧ context.BoundsAgree child ∧ At laws (@project) inner child
  | .resource inner => ∀ identity fresh,
      ∃ child : Context (world ++ [identity]) owner outward actions phases
        (.cell (identity := identity) whole) (.cell (identity := identity) front) saved waiting,
        child.before = Interfaces.cell (context.before.world_weaken (List.subset_append_left _ _)) ∧
        (context.resource laws (@project) identity).BoundsAgree child ∧ At laws (@project) (inner identity fresh) child

variable {laws : DeclarationLaws declarations admission certification outward}
  {project : ∀ {clauses families required} {plans : ClausePlans clauses families},
    admission.accepts outward required plans → declarations.accepts required plans}
  {wholeScope frontScope savedScope waitingScope : Scope}
  {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
  {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
  {whole : Forest wholeHints} {front : Forest frontHints}
  {saved : Forest savedHints} {waiting : Forest waitingHints}
  {plan : Plan dependencies} {body : Body world owner plan}
  {original current : Context world owner outward actions phases whole front saved waiting}

/-- Descent permits different witnesses with equal caller interfaces and retained
metadata. Physical indices remain identical. -/
theorem Descendants.sameReceiver (caller : original.before = current.before)
    (metadata : original.BoundsAgree current)
    (children : Descendants laws project body original) : Descendants laws project body current := by
  cases body with
  | resume | dispose => trivial
  | sequence => exact .sameReceiver caller metadata children
  | choice => exact ⟨.sameReceiver caller metadata children.1, .sameReceiver caller metadata children.2⟩
  | handler | cleanup =>
      obtain ⟨child, before, admitted⟩ := children
      exact ⟨child, by simpa only [caller] using before, admitted⟩
  | resource =>
      intro identity fresh
      obtain ⟨child, before, admitted⟩ := children identity fresh
      exact ⟨child, by simpa only [caller] using before, admitted⟩

/-- Neutral source changes retain immediate children at their actual entered
contexts. Each child reuses its own original retained-source evidence. -/
theorem Descendants.neutral
    {nextWholeHints : Hints nextWholeScope} {nextFrontHints : Hints nextFrontScope}
    {nextWhole : Forest nextWholeHints} {nextFront : Forest nextFrontHints}
    {current : Context world owner outward actions phases nextWhole nextFront saved waiting}
    (receiver : SourceScheduledNeutral.Expansion whole nextWhole)
    (caller : SourceScheduledNeutral.Expansion front nextFront)
    (metadata : original.BoundsAgree current)
    (children : Descendants laws project body original) : Descendants laws project body current := by
  cases body with
  | resume | dispose => trivial
  | sequence => exact .neutral receiver caller metadata children
  | choice => exact ⟨.neutral receiver caller metadata children.1, .neutral receiver caller metadata children.2⟩
  | handler =>
      obtain ⟨child, before, admitted⟩ := children
      exact ⟨child.neutral laws project (.handler current.cut) (.handler _ current.before) (.handler caller),
        rfl, .neutral (.handler receiver) (.handler caller) (child.neutral_bounds laws project _ _ _) admitted⟩
  | cleanup required footprint declared inner =>
      obtain ⟨child, before, admitted⟩ := children
      exact ⟨child.neutral laws project (.cleanup current.cut)
        (.cleanup _ required footprint declared current.before) (.cleanup caller),
        rfl, .neutral (.cleanup receiver) (.cleanup caller) (child.neutral_bounds laws project _ _ _) admitted⟩
  | resource =>
      intro identity fresh
      obtain ⟨child, before, admitted⟩ := children identity fresh
      exact ⟨child.neutral laws project (.cell current.cut)
        (.cell (current.before.world_weaken (List.subset_append_left _ _))) (.cell caller),
        rfl, .neutral (.cell receiver) (.cell caller) (child.neutral_bounds laws project _ _ _) admitted⟩

omit admission certification [SourceScheduledChecks.DeclarationProjection admission certification] in
theorem Context.BoundsAgree.symm
    {original : Context world owner outward actions phases whole front saved waiting}
    {current : Context world owner outward actions phases nextWhole nextFront saved waiting}
    (metadata : original.BoundsAgree current) : current.BoundsAgree original :=
  ⟨fun permission => (metadata.resumption permission).symm,
    fun permission => (metadata.closing permission).symm, metadata.tail.symm⟩

omit [SourceScheduledChecks.DeclarationProjection admission certification] in
theorem Context.BoundsAgree.resource
    {original : Context world owner outward actions phases whole front saved waiting}
    {current : Context world owner outward actions phases nextWhole nextFront saved waiting}
    (metadata : original.BoundsAgree current) (identity : Nat) :
    (original.resource laws project identity).BoundsAgree (current.resource laws project identity) := by
  constructor
  · intro permission
    simp only [Context.resource_resumption_bounds]
    exact congrArg (fun bounds => bounds.world_weaken (List.subset_append_left _ [identity])) (metadata.resumption permission)
  · intro permission
    simp only [Context.resource_closing_bounds]
    exact congrArg (fun bounds => bounds.world_weaken (List.subset_append_left _ [identity])) (metadata.closing permission)
  · simp only [Context.resource_tail_bounds]
    exact congrArg (fun bounds => bounds.world_weaken (List.subset_append_left _ [identity])) metadata.tail

theorem ExactDescendants.erase (children : ExactDescendants laws project body current) :
    Descendants laws project body current := by
  cases body with
  | resume | dispose => trivial
  | sequence | choice => exact children
  | handler | cleanup => obtain ⟨child, before, metadata, source⟩ := children; exact ⟨child, before, source⟩
  | resource =>
      intro identity fresh
      obtain ⟨child, before, metadata, source⟩ := children identity fresh
      exact ⟨child, before, source⟩

theorem ExactDescendants.sameReceiver (caller : original.before = current.before)
    (metadata : original.BoundsAgree current)
    (children : ExactDescendants laws project body original) : ExactDescendants laws project body current := by
  cases body with
  | resume | dispose => trivial
  | sequence => exact .sameReceiver caller metadata children
  | choice => exact ⟨.sameReceiver caller metadata children.1, .sameReceiver caller metadata children.2⟩
  | handler | cleanup =>
      obtain ⟨child, before, kept, source⟩ := children
      exact ⟨child, by simpa only [caller] using before, metadata.symm.trans kept, source⟩
  | resource =>
      intro identity fresh
      obtain ⟨child, before, kept, source⟩ := children identity fresh
      exact ⟨child, by simpa only [caller] using before, (metadata.resource identity).symm.trans kept, source⟩

theorem ExactDescendants.neutral
    {nextWholeHints : Hints nextWholeScope} {nextFrontHints : Hints nextFrontScope}
    {nextWhole : Forest nextWholeHints} {nextFront : Forest nextFrontHints}
    {current : Context world owner outward actions phases nextWhole nextFront saved waiting}
    (receiver : SourceScheduledNeutral.Expansion whole nextWhole)
    (caller : SourceScheduledNeutral.Expansion front nextFront)
    (metadata : original.BoundsAgree current)
    (children : ExactDescendants laws project body original) : ExactDescendants laws project body current := by
  cases body with
  | resume | dispose => trivial
  | sequence => exact .neutral receiver caller metadata children
  | choice => exact ⟨.neutral receiver caller metadata children.1, .neutral receiver caller metadata children.2⟩
  | handler =>
      obtain ⟨child, before, kept, source⟩ := children
      let moved := child.neutral laws project (.handler current.cut) (.handler _ current.before) (.handler caller)
      have changed : child.BoundsAgree moved := child.neutral_bounds laws project _ _ _
      exact ⟨moved, rfl, metadata.symm.trans (kept.trans changed),
        .neutral (.handler receiver) (.handler caller) changed source⟩
  | cleanup required footprint declared inner =>
      obtain ⟨child, before, kept, source⟩ := children
      let moved := child.neutral laws project (.cleanup current.cut)
        (.cleanup _ required footprint declared current.before) (.cleanup caller)
      have changed : child.BoundsAgree moved := child.neutral_bounds laws project _ _ _
      exact ⟨moved, rfl, metadata.symm.trans (kept.trans changed),
        .neutral (.cleanup receiver) (.cleanup caller) changed source⟩
  | resource =>
      intro identity fresh
      obtain ⟨child, before, kept, source⟩ := children identity fresh
      let moved := child.neutral laws project (.cell current.cut)
        (.cell (current.before.world_weaken (List.subset_append_left _ _))) (.cell caller)
      have changed : child.BoundsAgree moved := child.neutral_bounds laws project _ _ _
      exact ⟨moved, rfl, (metadata.resource identity).symm.trans (kept.trans changed),
        .neutral (.cell receiver) (.cell caller) changed source⟩

/-- Waiting-tail descent reuses the actual target parent's tail. The original
child's exact metadata agreement supplies its tail provenance. -/
theorem ExactDescendants.waitingNeutral
    {nextWholeHints : Hints nextWholeScope} {nextFrontHints : Hints nextFrontScope}
    {nextWaitingHints : Hints nextWaitingScope}
    {nextWhole : Forest nextWholeHints} {nextFront : Forest nextFrontHints} {nextWaiting : Forest nextWaitingHints}
    {current : Context world owner outward actions phases nextWhole nextFront saved nextWaiting}
    (receiver : SourceScheduledNeutral.Expansion whole nextWhole)
    (caller : SourceScheduledNeutral.Expansion front nextFront)
    (waitingChange : SourceScheduledNeutral.Expansion waiting nextWaiting)
    (metadata : original.SavedAgree current)
    (tail : SourceBoundSnapshots.Retained.Neutral world (SourceBoundSnapshots.Retained.ofCapability original.after)
      (SourceBoundSnapshots.Retained.ofCapability current.after))
    (children : ExactDescendants laws project body original) : ExactDescendants laws project body current := by
  cases body with
  | resume | dispose => trivial
  | sequence => exact .waitingNeutral receiver caller waitingChange metadata tail children
  | choice => exact ⟨.waitingNeutral receiver caller waitingChange metadata tail children.1,
      .waitingNeutral receiver caller waitingChange metadata tail children.2⟩
  | handler =>
      obtain ⟨child, before, kept, source⟩ := children
      let moved := child.neutral_tail laws project (.handler current.cut) (.handler _ current.before)
        (.handler caller) waitingChange current.after current.tailReady
      have changed : child.SavedAgree moved := child.neutral_tail_saved laws project _ _ _ _ _ _
      have childTail : SourceBoundSnapshots.Retained.Neutral world (SourceBoundSnapshots.Retained.ofCapability child.after)
          (SourceBoundSnapshots.Retained.ofCapability moved.after) := by
        change SourceBoundSnapshots.Retained.Neutral world (SourceBoundSnapshots.Retained.ofCapability child.after)
          (SourceBoundSnapshots.Retained.ofCapability current.after)
        rw [kept.tail]
        exact tail
      exact ⟨moved, rfl, (metadata.symm.trans (kept.saved_agreement.trans changed)).with_tail rfl,
        .waitingNeutral (.handler receiver) (.handler caller) waitingChange changed childTail source⟩
  | cleanup required footprint declared inner =>
      obtain ⟨child, before, kept, source⟩ := children
      let moved := child.neutral_tail laws project (.cleanup current.cut)
        (.cleanup _ required footprint declared current.before) (.cleanup caller) waitingChange current.after current.tailReady
      have changed : child.SavedAgree moved := child.neutral_tail_saved laws project _ _ _ _ _ _
      have childTail : SourceBoundSnapshots.Retained.Neutral world (SourceBoundSnapshots.Retained.ofCapability child.after)
          (SourceBoundSnapshots.Retained.ofCapability moved.after) := by
        change SourceBoundSnapshots.Retained.Neutral world (SourceBoundSnapshots.Retained.ofCapability child.after)
          (SourceBoundSnapshots.Retained.ofCapability current.after)
        rw [kept.tail]
        exact tail
      exact ⟨moved, rfl, (metadata.symm.trans (kept.saved_agreement.trans changed)).with_tail rfl,
        .waitingNeutral (.cleanup receiver) (.cleanup caller) waitingChange changed childTail source⟩
  | resource =>
      intro identity fresh
      obtain ⟨child, before, kept, source⟩ := children identity fresh
      let target := current.resource laws project identity
      let moved := child.neutral_tail laws project (.cell current.cut)
        (.cell (current.before.world_weaken (List.subset_append_left _ _))) (.cell caller)
        waitingChange target.after target.tailReady
      have changed : child.SavedAgree moved := child.neutral_tail_saved laws project _ _ _ _ _ _
      have childTail : SourceBoundSnapshots.Retained.Neutral (world ++ [identity])
          (SourceBoundSnapshots.Retained.ofCapability child.after)
          (SourceBoundSnapshots.Retained.ofCapability moved.after) := by
        change SourceBoundSnapshots.Retained.Neutral (world ++ [identity])
          (SourceBoundSnapshots.Retained.ofCapability child.after)
          (SourceBoundSnapshots.Retained.ofCapability (current.resource laws project identity).after)
        rw [kept.tail]
        simpa only [Context.resource_tail_bounds] using tail.world_weaken (List.subset_append_left _ [identity])
      exact ⟨moved, rfl, ((metadata.resource laws project identity).symm.trans (kept.saved_agreement.trans changed)).with_tail rfl,
        .waitingNeutral (.cell receiver) (.cell caller) waitingChange changed childTail source⟩

/-- Structural descent keeps exact saved, closing and waiting metadata at
nested entries, including after neutral receiver changes. -/
theorem At.descendants_exact (admitted : At laws project body current) :
    ExactDescendants laws project body current := by
  induction admitted with
  | resume | dispose => trivial
  | sequence body ih => exact body
  | choice first second ihFirst ihSecond => exact ⟨first, second⟩
  | handler bounds declared resumption closing body ih =>
      exact ⟨_, rfl, Context.handler_bounds laws project _ _ _ _ _ _ _, body⟩
  | cleanupSource covered resumption closing body ih =>
      exact ⟨_, rfl, Context.cleanupSource_bounds laws project _ _ _ _ _ _, body⟩
  | resource body ih => exact fun identity fresh => ⟨_, rfl, Context.BoundsAgree.refl _, body identity fresh⟩
  | sameReceiver caller metadata source ih => exact ih.sameReceiver caller metadata
  | neutral receiver caller metadata source ih => exact ih.neutral receiver caller metadata
  | waitingNeutral receiver caller waitingChange metadata tail source ih =>
      exact ih.waitingNeutral receiver caller waitingChange metadata tail

/-- Preserve the original child API as a projection of exact descent. -/
theorem At.descendants (admitted : At laws project body current) :
    Descendants laws project body current := admitted.descendants_exact.erase

/-- Syntactic sequencing exposes the rest at the current receiver. This does
not transport admission across execution of the prefix. -/
theorem At.sequence_rest
    {footprint : SourceScheduledAdaptationCompilation.RequestFootprint initial required}
    {declared : SourceScheduledSourceInterfaces.Declared world (SourcePlanSignatures.signature initial)}
    (admitted : At laws project (.sequence required footprint declared body) current) :
    At laws project body current := admitted.descendants

theorem At.choice_branches {second : Body world owner secondPlan}
    (admitted : At laws project (.choice body second) current) :
    At laws project body current ∧ At laws project second current := admitted.descendants

/-- Handler entry inherits the child's structural derivation and finite bound
check. The existential retains the actual source-derived context witness. -/
theorem At.handler_body
    {plans : ClausePlans clauses families}
    {bounds : SourceConsumingClauseAnnotations.ClauseBounds plans}
    {declared : declarations.accepts required plans}
    (admitted : At laws project (.handler (effect := effect) (table := table) bounds declared body) current)
    (checked : (Body.handler (effect := effect) (table := table) bounds declared body).BoundCheck
      resumeRequired closeRequired actions phases wholeScope waitingScope current.before) :
    ∃ child : Context world owner outward actions phases
      (.handler (effect := effect) (table := table) (families := families) (required := required) whole)
      (.handler (effect := effect) (table := table) (families := families) (required := required) front) saved waiting,
      child.before = Interfaces.handler front current.before ∧ At laws project body child ∧
      body.BoundCheck resumeRequired closeRequired actions phases
        (.handler effect table families wholeScope) waitingScope child.before := by
  obtain ⟨child, before, source⟩ := admitted.descendants
  exact ⟨child, before, source, by rw [before]; exact checked.2⟩

/-- Structural cleanup exposes its body interface and inherits
its finite checks; the callback's completion check remains separate. -/
theorem At.cleanup_body
    {callback : Plan callbackDependencies}
    {footprint : SourceScheduledAdaptationCompilation.RequestFootprint callback required}
    {declared : SourceScheduledSourceInterfaces.Declared world (SourcePlanSignatures.signature callback)}
    (admitted : At laws project (.cleanup (needs := needs) required footprint declared body) current)
    (checked : (Body.cleanup (needs := needs) required footprint declared body).BoundCheck
      resumeRequired closeRequired actions phases wholeScope waitingScope current.before) :
    ∃ child : Context world owner outward actions phases
      (.cleanup (needs := needs) callback whole) (.cleanup (needs := needs) callback front) saved waiting,
      child.before = Interfaces.cleanup front required footprint declared current.before ∧ At laws project body child ∧
      body.BoundCheck resumeRequired closeRequired actions phases
        (.cleanup needs callbackDependencies wholeScope) waitingScope child.before := by
  obtain ⟨child, before, source⟩ := admitted.descendants
  exact ⟨child, before, source, by rw [before]; exact checked.1⟩

/-- Resource descent specializes the already universally admitted source body
at the actual fresh identity. No fresh body-admission premise is required. -/
theorem At.resource_body
    {families : Nat → SourceDependencyAnnotations.Dependencies}
    {plans : ∀ identity, Plan (families identity)}
    {code : ∀ identity, identity ∉ world → Body (world ++ [identity]) owner (plans identity)}
    (admitted : At laws project (.resource code) current)
    (checked : (Body.resource code).BoundCheck resumeRequired closeRequired actions phases
      wholeScope waitingScope current.before) (fresh : identity ∉ world) :
    ∃ child : Context (world ++ [identity]) owner outward actions phases
      (.cell (identity := identity) whole) (.cell (identity := identity) front) saved waiting,
      child.before = Interfaces.cell (current.before.world_weaken (List.subset_append_left _ _)) ∧
      At laws project (code identity fresh) child ∧
      (code identity fresh).BoundCheck resumeRequired closeRequired actions phases
        (.cell identity wholeScope) waitingScope child.before := by
  obtain ⟨child, before, source⟩ := admitted.descendants identity fresh
  exact ⟨child, before, source, by rw [before]; exact checked identity fresh⟩

end Ash.OneShot.SourceConsumingCleanupAdmission

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Descendants.sameReceiver
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.descendants

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.sequence_rest
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.choice_branches
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.handler_body
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.cleanup_body
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.resource_body

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Descendants.neutral

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.BoundsAgree.symm
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.BoundsAgree.resource
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ExactDescendants.erase
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ExactDescendants.sameReceiver
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ExactDescendants.neutral
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.descendants_exact

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ExactDescendants.waitingNeutral
