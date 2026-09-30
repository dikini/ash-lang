import SourceConsumingAdmissionDescent
import SourceConsumingReceiverMetadata
import SourceConsumingQueuedAdmission

/-! Structural receiver obligations for reusing an original consuming source
body at a changed caller. The obligations retain only the nested entry checks:
original source admission supplies cleanup coverage and child derivations.
Neither a target At derivation nor target Code.Valid is an input. Runtime
preservation must separately derive these obligations for its actual change. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission
open SourceContextualHints (Hints)
open SourceDependencyCapture (Scope)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceConsumingClauseAnnotations (Body)
open SourceScheduledCapabilityAnnotations (DeclarationPolicy DeclarationLaws)
open SourceScheduledSourceRechecking (ReceiverChange)
open OwnerPhaseTransitions (spend)

variable [declarations : DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]

/-- Entry-specific obligations at the new receiver. Ordinary sequencing and
branching add no new interference evidence. Resource bodies retain the existing
fresh-identity quantification. No constructor contains a target source judgment. -/
inductive ReceiverChecks
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    (actions : Syntax.UsageTickets) (phases : OwnerPhaseTransitions.Phases) :
    {world : List Nat} → {owner : Nat} → {dependencies : SourceDependencyAnnotations.Dependencies} →
    {plan : Plan dependencies} → Body world owner plan →
    {wholeScope frontScope savedScope waitingScope : Scope} →
    {wholeHints : Hints wholeScope} → {frontHints : Hints frontScope} →
    {savedHints : Hints savedScope} → {waitingHints : Hints waitingScope} →
    {whole : Forest wholeHints} → {front : Forest frontHints} →
    {saved : Forest savedHints} → {waiting : Forest waitingHints} →
    Context world owner outward actions phases whole front saved waiting → Prop where
  | resume : ReceiverChecks laws (@project) actions phases .resume context
  | dispose : ReceiverChecks laws (@project) actions phases .dispose context
  | sequence : ReceiverChecks laws (@project) actions phases body context →
      ReceiverChecks laws (@project) actions phases (.sequence required footprint declared body) context
  | choice : ReceiverChecks laws (@project) actions phases first context →
      ReceiverChecks laws (@project) actions phases second context →
      ReceiverChecks laws (@project) actions phases (.choice first second) context
  | handler {world : List Nat} {owner : Nat} {plans : ClausePlans clauses families}
      {bounds : SourceConsumingClauseAnnotations.ClauseBounds plans}
      {declared : declarations.accepts required plans} {body : Body world owner plan}
      {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
      {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
      {whole : Forest wholeHints} {front : Forest frontHints}
      {saved : Forest savedHints} {waiting : Forest waitingHints}
      {context : Context world owner outward actions phases whole front saved waiting}
      (resumption : ∀ permission, ReceiverChange outward actions (spend phases owner)
        (context.resumption permission).val
        (.handler (effect := effect) (table := table) (families := families) (required := required)
          (front.append (.spent (owner := owner) waiting))))
      (closing : ∀ permission, ReceiverChange outward actions (spend phases owner)
        (context.closing permission).val
        (.running (.handler (effect := effect) (table := table) (families := families) (required := required)
          (front.append (.spent (owner := owner) waiting)))))
      (inner : ReceiverChecks laws (@project) actions phases body
        (context.handler laws project effect table families required resumption closing)) :
      ReceiverChecks laws (@project) actions phases (.handler (effect := effect) (table := table) bounds declared body) context
  | cleanup {world : List Nat} {owner : Nat} {body : Body world owner plan}
      {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
      {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
      {whole : Forest wholeHints} {front : Forest frontHints}
      {saved : Forest savedHints} {waiting : Forest waitingHints}
      {context : Context world owner outward actions phases whole front saved waiting}
      {footprint : SourceScheduledAdaptationCompilation.RequestFootprint callback required}
      {declared : SourceScheduledSourceInterfaces.Declared world (SourcePlanSignatures.signature callback)}
      (resumption : ∀ permission, ReceiverChange outward actions (spend phases owner)
        (context.resumption permission).val
        (.cleanup (needs := needs) callback (front.append (.spent (owner := owner) waiting))))
      (closing : ∀ permission, ReceiverChange outward actions (spend phases owner)
        (context.closing permission).val
        (.running (.cleanup (needs := needs) callback (front.append (.spent (owner := owner) waiting)))))
      (inner : ReceiverChecks laws (@project) actions phases body
        (context.cleanupSource laws project footprint declared needs resumption closing)) :
      ReceiverChecks laws (@project) actions phases (.cleanup (needs := needs) required footprint declared body) context
  | sameReceiver {world : List Nat} {owner : Nat} {body : Body world owner plan}
      {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
      {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
      {whole : Forest wholeHints} {front : Forest frontHints}
      {saved : Forest savedHints} {waiting : Forest waitingHints}
      {original current : Context world owner outward actions phases whole front saved waiting}
      (caller : original.before = current.before) (metadata : original.BoundsAgree current)
      (checks : ReceiverChecks laws (@project) actions phases body original) :
      ReceiverChecks laws (@project) actions phases body current
  | neutral {world : List Nat} {owner : Nat} {body : Body world owner plan}
      {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
      {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
      {whole : Forest wholeHints} {front : Forest frontHints}
      {saved : Forest savedHints} {waiting : Forest waitingHints}
      {nextWholeHints : Hints nextWholeScope} {nextFrontHints : Hints nextFrontScope}
      {nextWhole : Forest nextWholeHints} {nextFront : Forest nextFrontHints}
      {original : Context world owner outward actions phases whole front saved waiting}
      {current : Context world owner outward actions phases nextWhole nextFront saved waiting}
      (receiver : SourceScheduledNeutral.Expansion whole nextWhole)
      (caller : SourceScheduledNeutral.Expansion front nextFront) (metadata : original.BoundsAgree current)
      (checks : ReceiverChecks laws (@project) actions phases body original) :
      ReceiverChecks laws (@project) actions phases body current
  | waitingNeutral {world : List Nat} {owner : Nat} {body : Body world owner plan}
      {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
      {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
      {whole : Forest wholeHints} {front : Forest frontHints}
      {saved : Forest savedHints} {waiting : Forest waitingHints}
      {nextWaitingHints : Hints nextWaitingScope}
      {nextWaiting : Forest nextWaitingHints}
      {nextWholeHints : Hints nextWholeScope} {nextFrontHints : Hints nextFrontScope}
      {nextWhole : Forest nextWholeHints} {nextFront : Forest nextFrontHints}
      {original : Context world owner outward actions phases whole front saved waiting}
      {current : Context world owner outward actions phases nextWhole nextFront saved nextWaiting}
      (receiver : SourceScheduledNeutral.Expansion whole nextWhole)
      (caller : SourceScheduledNeutral.Expansion front nextFront) (waitingChange : SourceScheduledNeutral.Expansion waiting nextWaiting)
      (metadata : original.SavedAgree current)
      (tail : SourceBoundSnapshots.Retained.Neutral world (SourceBoundSnapshots.Retained.ofCapability original.after)
        (SourceBoundSnapshots.Retained.ofCapability current.after))
      (checks : ReceiverChecks laws (@project) actions phases body original) :
      ReceiverChecks laws (@project) actions phases body current
  | resource {world : List Nat} {owner : Nat}
      {families : Nat → SourceDependencyAnnotations.Dependencies} {plans : ∀ identity, Plan (families identity)}
      {body : ∀ identity, identity ∉ world → Body (world ++ [identity]) owner (plans identity)}
      {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
      {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
      {whole : Forest wholeHints} {front : Forest frontHints}
      {saved : Forest savedHints} {waiting : Forest waitingHints}
      {context : Context world owner outward actions phases whole front saved waiting}
      (inner : ∀ identity fresh, ReceiverChecks laws (@project) actions phases (body identity fresh)
        (context.resource laws project identity)) :
      ReceiverChecks laws (@project) actions phases (.resource body) context

variable {laws : DeclarationLaws declarations admission certification outward}
  {project : ∀ {clauses families required} {plans : ClausePlans clauses families},
    admission.accepts outward required plans → declarations.accepts required plans}

/-- Rebuild every source constructor at the changed physical context. The
induction reuses original descendants and cleanup coverage; the target nested
contexts are generated by the existing receiver-only compilers. -/
theorem ReceiverChecks.reconstruct
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    {current : Context world owner outward actions phases whole front saved waiting}
    {body : Body world owner plan}
    (checks : ReceiverChecks laws (@project) actions phases body current) :
    ∀ {oldWholeScope oldFrontScope oldSavedScope oldWaitingScope}
      {oldWholeHints : Hints oldWholeScope} {oldFrontHints : Hints oldFrontScope}
      {oldSavedHints : Hints oldSavedScope} {oldWaitingHints : Hints oldWaitingScope}
      {oldWhole : Forest oldWholeHints} {oldFront : Forest oldFrontHints}
      {oldSaved : Forest oldSavedHints} {oldWaiting : Forest oldWaitingHints}
      {original : Context world owner outward actions phases oldWhole oldFront oldSaved oldWaiting},
      At laws project body original → At laws project body current := by
  induction checks with
  | resume => intros; exact .resume
  | dispose => intros; exact .dispose
  | sequence inner ih => intros; apply At.sequence; apply ih; exact At.sequence_rest ‹_›
  | choice first second ihFirst ihSecond =>
      intros
      have parts := At.choice_branches ‹_›
      exact .choice (ihFirst parts.1) (ihSecond parts.2)
  | handler resumption closing inner ih =>
      intros
      obtain ⟨child, caller, source⟩ := At.descendants ‹_›
      exact .handler _ _ resumption closing (ih source)
  | cleanup resumption closing inner ih =>
      intros
      have covered := At.cleanup_dependencies ‹_›
      obtain ⟨child, caller, source⟩ := At.descendants ‹_›
      exact .cleanupSource covered resumption closing (ih source)
  | sameReceiver caller metadata checks ih =>
      intros
      exact .sameReceiver caller metadata (ih ‹_›)
  | neutral receiver caller metadata checks ih =>
      intros
      exact .neutral receiver caller metadata (ih ‹_›)
  | waitingNeutral receiver caller waitingChange metadata tail checks ih =>
      intros
      exact .waitingNeutral receiver caller waitingChange metadata tail (ih ‹_›)
  | resource inner ih =>
      intros
      rename_i originalSource
      apply At.resource
      intro identity fresh
      obtain ⟨child, caller, source⟩ := originalSource.descendants identity fresh
      exact ih identity fresh source

/-- Existing source admission already contains the receiver obligations for
its original context. Extract them through all constructors, including changes
of annotation witnesses at the same physical receiver. -/
theorem At.receiver_checks
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    {context : Context world owner outward actions phases whole front saved waiting}
    {body : Body world owner plan} (source : At laws project body context) :
    ReceiverChecks laws (@project) actions phases body context := by
  induction source with
  | resume => exact .resume
  | dispose => exact .dispose
  | sequence body ih => exact .sequence ih
  | choice first second ihFirst ihSecond => exact .choice ihFirst ihSecond
  | handler bounds declared resumption closing body ih => exact .handler resumption closing ih
  | cleanupSource covered resumption closing body ih => exact .cleanup resumption closing ih
  | sameReceiver caller metadata source ih => exact .sameReceiver caller metadata ih
  | neutral receiver caller metadata source ih => exact .neutral receiver caller metadata ih
  | waitingNeutral receiver caller waitingChange metadata tail source ih =>
      exact .waitingNeutral receiver caller waitingChange metadata tail ih
  | resource body ih => exact .resource ih

variable {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
  {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
  {whole : Forest wholeHints} {front : Forest frontHints}
  {saved : Forest savedHints} {waiting : Forest waitingHints}
  {nextWholeHints : Hints nextWholeScope} {nextFrontHints : Hints nextFrontScope}
  {nextWhole : Forest nextWholeHints} {nextFront : Forest nextFrontHints}
  {original : Context world owner outward actions phases whole front saved waiting}
  {current : Context world owner outward actions phases nextWhole nextFront saved waiting}

/-- The changed caller produces a source judgment and valid code whose bound
continuation still has the ORIGINAL saved/closing/waiting metadata. Finite
operation/phase checks remain separate from receiver interference. -/
theorem ReceiverChecks.generate {body : Body world owner plan}
    (checks : ReceiverChecks laws (@project) actions phases body current)
    (source : At laws project body original) (metadata : original.BoundsAgree current)
    (checked : body.BoundCheck resumeRequired closeRequired actions phases
      nextWholeScope waitingScope current.before) :
    At laws project body current ∧
    ∃ annotation : SourceScheduledCapabilityAnnotations.Code world plan nextWhole,
      annotation.Valid outward actions phases ∧
      SourceConsumingClauseAnnotations.Generated actions original.continuationBounds body annotation := by
  have next := checks.reconstruct source
  obtain ⟨annotation, ready, generated⟩ := next.generate_source checked
  exact ⟨next, annotation, ready, by simpa only [metadata.continuationBounds_eq] using generated⟩

/-- Activate the same queued source body at its new physical context. The
result retains its identity, original bound annotation and continuation
metadata. Source-independent finite checks are explicit; none is inferred from
record movement or from bound agreement alone. -/
def QueuedBody.recheck {bounds : SourcePlanBounds.Annotation world plan}
    (queued : QueuedBody laws project resumeRequired closeRequired original bounds)
    (metadata : original.BoundsAgree current)
    (checks : ReceiverChecks laws (@project) actions phases queued.body current)
    (checked : queued.body.BoundCheck resumeRequired closeRequired actions phases
      nextWholeScope waitingScope current.before) :
    { next : QueuedBody laws project resumeRequired closeRequired current bounds //
      next.body = queued.body ∧ original.BoundsAgree current } :=
  ⟨⟨queued.body, queued.origin, checks.reconstruct queued.source, queued.nested, checked⟩, rfl, metadata⟩

end Ash.OneShot.SourceConsumingCleanupAdmission

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ReceiverChecks.reconstruct
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ReceiverChecks.generate

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.receiver_checks
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.QueuedBody.recheck
