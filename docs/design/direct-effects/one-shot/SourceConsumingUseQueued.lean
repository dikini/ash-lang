import SourceConsumingUseAdmission
import SourceConsumingQueuedAdmission
import SourceBoundNormalizedRecords

/-! Queued consuming source with its original captured annotations separate
from its actual caller. The record can inhabit an intermediate masking scope;
only the consuming leaves need structural rechecking there. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission
open SourceContextualHints (Hints Requirement)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceConsumingClauseAnnotations (Body Generated)
open SourceScheduledCapabilityAnnotations (Code DeclarationPolicy DeclarationLaws)
open SourceScheduledRetainedInterfaces (Interfaces)
open SourceScheduledNeutral (OwnerCut)
open SourcePlanBounds (Annotation)
open SourceBoundSnapshots (Snapshot Returned)

variable [declarations : DeclarationPolicy]

/-- The original context retains the saved/closing evidence and waiting source.
The explicit current cut/caller need not make that dormant source valid before
its actual use. The record stores syntax and structural proofs, not future code. -/
structure UseQueuedBody (resumeRequired closeRequired : List Requirement)
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (original : Context world owner outward actions phases base baseFront saved waiting)
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    (cut : OwnerCut owner whole front saved waiting) (before : Interfaces world front)
    {plan : Plan dependencies} (bounds : Annotation world plan) where
  body : Body world owner plan
  origin : bounds = body.boundAnnotation
  source : AtUse outward actions phases original body front
  nested : body.Nested
  checked : body.BoundCheck resumeRequired closeRequired actions phases wholeScope waitingScope before

variable
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    {original : Context world owner outward actions phases base baseFront saved waiting}
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    {cut : OwnerCut owner whole front saved waiting} {before : Interfaces world front}

/-- Source inversion follows the constructor directly; it does not infer the
child from its bound projection. -/
theorem AtUse.sequence_rest
    {body : Body world owner plan}
    {footprint : SourceScheduledAdaptationCompilation.RequestFootprint first required}
    {declared : SourceScheduledSourceInterfaces.Declared world (SourcePlanSignatures.signature first)}
    (source : AtUse outward actions phases original (.sequence required footprint declared body) front) :
    AtUse outward actions phases original body front := by
  cases source with | sequence rest => exact rest

/-- Reuse the existing value-prefix syntax reconstruction. -/
theorem AtUse.plug {body : Body world owner plan}
    (source : AtUse outward actions phases original body front)
    (position : SourceAnnotatedCode.Context) :
    AtUse outward actions phases original (body.plug position) front := by
  cases position <;> first | exact .sequence source | exact .sequence (.sequence source)

def UseQueuedBody.plug {bounds : Annotation world plan}
    (queued : UseQueuedBody resumeRequired closeRequired original cut before bounds)
    (position : SourceAnnotatedCode.Context) :
    UseQueuedBody resumeRequired closeRequired original cut before (bounds.plug position).2.2 := by
  rcases queued with ⟨body, rfl, source, nested, checked⟩
  refine ⟨body.plug position, (body.plug_bounds position).symm, source.plug position, nested.plug position, ?_⟩
  cases position <;> first | exact ⟨rfl, checked⟩ | exact ⟨rfl, rfl, checked⟩

/-- Actual snapshot return uses the retained record and produces its successor
source. No new admission of the plugged body is an input. -/
theorem UseQueuedBody.returned {bounds : Annotation world plan}
    (queued : UseQueuedBody resumeRequired closeRequired original cut before bounds)
    (position : SourceAnnotatedCode.Context)
    {currentPlan : Plan currentDependencies} (currentBounds : Annotation world currentPlan)
    (pending : SourceBoundSnapshots.Retained world whole) {next : Snapshot world}
    (step : Returned position
      ⟨_, currentPlan, currentBounds, _, _, .plain plan whole, .plain bounds pending⟩ next) :
    ∃ nextQueued : UseQueuedBody resumeRequired closeRequired original cut before (bounds.plug position).2.2,
      next = ⟨_, _, nextQueued.body.boundAnnotation, _, _, whole, pending⟩ := by
  refine ⟨queued.plug position, ?_⟩
  cases step
  rw [← (queued.plug position).origin]
  rfl

/-- The source compiler generates the actual current receiver's annotation,
with exact queued bounds and original continuation correspondence. -/
theorem UseQueuedBody.generate
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {bounds : Annotation world plan}
    (queued : UseQueuedBody resumeRequired closeRequired original cut before bounds) :
    ∃ annotation : Code world plan whole, annotation.Valid outward actions phases ∧
      SourcePlanBounds.ofCode annotation = bounds ∧
      Generated actions original.continuationBounds queued.body annotation ∧ bounds.Admitted := by
  obtain ⟨annotation, ready, generated⟩ := queued.source.generate_source laws project cut before queued.checked
  exact ⟨annotation, ready, generated.current_bounds.trans queued.origin.symm,
    generated, queued.origin.symm ▸ queued.nested.boundAnnotation_admitted⟩

/-- Neutral receiver expansion for a current child reuses the existing code
transport theorem, preserving its current bounds. It does not claim that this
alone reconstructs source admission at arbitrary changed receivers. -/
theorem UseQueuedBody.generate_expanding
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    [SourceScheduledChecks.DeclarationProjection admission certification]
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {bounds : Annotation world plan}
    (queued : UseQueuedBody resumeRequired closeRequired original cut before bounds)
    {nextHints : Hints nextScope} {next : Forest nextHints}
    (changed : SourceScheduledNeutral.Expansion whole next) :
    ∃ annotation : Code world plan next, annotation.Valid outward actions phases ∧
      SourcePlanBounds.ofCode annotation = bounds := by
  obtain ⟨code, valid, kept, _⟩ := queued.generate laws project
  obtain ⟨annotation, ready, same⟩ := code.expand_retaining laws project valid changed
  exact ⟨annotation, ready, same.trans kept⟩

/-- Use the existing focus split: an operation-prefix child queues the
consuming source; a pure pending frame leaves that source current. -/
inductive UseFocusedSource (resumeRequired closeRequired : List Requirement)
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (original : Context world owner outward actions phases base baseFront saved waiting)
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    (cut : OwnerCut owner whole front saved waiting) (before : Interfaces world front) :
    {childDependencies restDependencies : SourceDependencyAnnotations.Dependencies} →
    {child : Plan childDependencies} → {rest : Plan restDependencies} →
    Annotation world child → Annotation world rest → Prop where
  | queued {rest : Plan restDependencies} {restBounds : Annotation world rest}
      (footprint : SourceScheduledAdaptationCompilation.RequestFootprint child required)
      (declared : SourceScheduledSourceInterfaces.Declared world (SourcePlanSignatures.signature child))
      (supplied : SourceContextualHints.checkRequirements (.plain restDependencies wholeScope) required = true)
      (source : UseQueuedBody resumeRequired closeRequired original cut before restBounds) :
      UseFocusedSource resumeRequired closeRequired original cut before (.absent (plan := child)) restBounds
  | current {child : Plan childDependencies} {childBounds : Annotation world child}
      (source : UseQueuedBody resumeRequired closeRequired original cut before childBounds) :
      UseFocusedSource resumeRequired closeRequired original cut before childBounds (.absent (plan := .pure))

/-- Focus derives the actual child's or queued body's source from the parent
record. It never reconstructs a source judgment from metadata alone. -/
theorem UseQueuedBody.focused {bounds : Annotation world plan}
    (queued : UseQueuedBody resumeRequired closeRequired original cut before bounds)
    {child : Plan childDependencies} {rest : Plan restDependencies}
    {childBounds : Annotation world child} {restBounds : Annotation world rest}
    (step : SourcePlanBounds.Focused world bounds childBounds restBounds) :
    UseFocusedSource resumeRequired closeRequired original cut before childBounds restBounds := by
  rcases queued with ⟨body, rfl, source, nested, checked⟩
  cases step with
  | pure => cases body
  | sequence =>
      cases body with
      | sequence required footprint declared rest =>
          cases nested with
          | sequence inner =>
              exact .queued footprint declared checked.1 ⟨rest, rfl, source.sequence_rest, inner, checked.2⟩
  | pairRight =>
      cases body with
      | sequence required footprint declared rest =>
          cases nested with
          | sequence inner => exact .current ⟨rest, rfl, source.sequence_rest, inner, checked.2⟩
  | appArgument =>
      cases body with
      | sequence functionRequired functionFootprint functionDeclared remaining =>
          cases remaining with
          | sequence argumentRequired argumentFootprint argumentDeclared rest =>
              cases nested with
              | sequence inner => cases inner with
                | sequence inner =>
                    exact .queued argumentFootprint argumentDeclared checked.2.1
                      ⟨rest, rfl, source.sequence_rest.sequence_rest, inner, checked.2.2⟩

theorem UseFocusedSource.queued_body
    {child : Plan childDependencies} {rest : Plan restDependencies}
    {childBounds : Annotation world child} {restBounds : Annotation world rest}
    (focused : UseFocusedSource resumeRequired closeRequired original cut before childBounds restBounds)
    (restBody : Body world owner rest) :
    Nonempty (UseQueuedBody resumeRequired closeRequired original cut before restBounds) := by
  cases focused with
  | queued footprint declared supplied source => exact ⟨source⟩
  | current source => cases restBody

theorem UseFocusedSource.current_body
    {child : Plan childDependencies} {childBounds : Annotation world child}
    (focused : UseFocusedSource resumeRequired closeRequired original cut before
      childBounds (.absent (plan := .pure))) :
    Nonempty (UseQueuedBody resumeRequired closeRequired original cut before childBounds) := by
  cases focused with
  | queued footprint declared supplied source => cases source.body
  | current source => exact ⟨source⟩

/-- Current-child compilation reuses neutral code expansion. Both alternatives
produce source at the actual receiver with the selected bound annotation. -/
theorem UseFocusedSource.child_valid
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    [SourceScheduledChecks.DeclarationProjection admission certification]
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {child : Plan childDependencies} {rest : Plan restDependencies}
    {childBounds : Annotation world child} {restBounds : Annotation world rest}
    (focused : UseFocusedSource resumeRequired closeRequired original cut before childBounds restBounds) :
    ∃ annotation : Code world child (.plain rest whole),
      annotation.Valid outward actions phases ∧ SourcePlanBounds.ofCode annotation = childBounds := by
  cases focused with
  | queued footprint declared supplied source => exact ⟨.operations _ footprint declared, supplied, rfl⟩
  | current source => exact source.generate_expanding laws project (.extra .refl)

end Ash.OneShot.SourceConsumingCleanupAdmission

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.AtUse.sequence_rest
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.AtUse.plug
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedBody.plug
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedBody.returned
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedBody.generate
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedBody.generate_expanding

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedBody.focused
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseFocusedSource.queued_body
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseFocusedSource.current_body
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseFocusedSource.child_valid

namespace Ash.OneShot.SourceBoundSnapshots
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceConsumingCleanupAdmission (Context UseQueuedBody)
open SourceScheduledCapabilityAnnotations (Code DeclarationLaws)
open SourcePlanBounds (Annotation ofCode)

variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    {original : Context world owner outward actions phases base baseFront saved waiting}
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    {cut : SourceScheduledNeutral.OwnerCut owner whole front saved waiting}
    {before : SourceScheduledRetainedInterfaces.Interfaces world front}
    {plan : Plan dependencies} {bounds : Annotation world plan}

/-- Canonical record indices retain the actual original source payload when
pure value prefixes are reconstructed on return. -/
def CanonicalPayload.plug_use_queued
    (record : CanonicalPayload (fun bounds => UseQueuedBody resumeRequired closeRequired original cut before bounds) bounds)
    (position : SourceAnnotatedCode.Context) :
    CanonicalPayload (fun bounds => UseQueuedBody resumeRequired closeRequired original cut before bounds)
      (bounds.plug position).2.2 := by
  have source := record.source.plug position
  cases position <;> refine ⟨_, source, ?_⟩ <;>
    simp only [Annotation.plug, Annotation.normalize, Annotation.empty, record.alignment]

/-- Generate at the recorded current cut, then reuse existing normalization.
Source payloads are not inferred from canonicalized bounds. -/
theorem CanonicalPayload.generate_use_queued
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    [SourceScheduledChecks.DeclarationProjection admission certification]
    (laws : DeclarationLaws nested admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → nested.accepts required plans)
    (record : CanonicalPayload (fun bounds => UseQueuedBody resumeRequired closeRequired original cut before bounds) bounds) :
    ∃ annotation : Code world plan whole, annotation.Valid outward actions phases ∧
      ofCode annotation = bounds ∧ annotation.Expanded ∧ bounds.Admitted := by
  obtain ⟨originalCode, originalReady, origin, _, admitted⟩ := record.source.generate laws project
  obtain ⟨annotation, ready, normalized, expanded⟩ :=
    Code.normalize (fun recipes => project (laws.legacyAdmission recipes)) originalReady
  have aligned := normalized.trans ((congrArg Annotation.normalize origin).trans record.alignment)
  exact ⟨annotation, ready, aligned, expanded, record.alignment ▸ admitted.normalize⟩

/-- Actual normalized return recomposes from the retained source payload.
Compilation supplies successor validity and exact canonical current bounds. -/
theorem CanonicalPayload.returned_use_queued
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    [SourceScheduledChecks.DeclarationProjection admission certification]
    (laws : DeclarationLaws nested admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → nested.accepts required plans)
    (record : CanonicalPayload (fun bounds => UseQueuedBody resumeRequired closeRequired original cut before bounds) bounds)
    (position : SourceAnnotatedCode.Context)
    {currentPlan : Plan currentDependencies} (current : Annotation world currentPlan)
    (pending : Retained world whole) {next : Snapshot world}
    (step : Returned position
      ⟨_, currentPlan, current, _, _, .plain plan whole, .plain bounds pending⟩ next) :
    ∃ annotation : Code world next.plan next.forest, annotation.Valid outward actions phases ∧
      ofCode annotation = next.current ∧ annotation.Expanded ∧ next.current.Admitted := by
  cases step
  exact (record.plug_use_queued position).generate_use_queued laws project

end Ash.OneShot.SourceBoundSnapshots

#print axioms Ash.OneShot.SourceBoundSnapshots.CanonicalPayload.plug_use_queued
#print axioms Ash.OneShot.SourceBoundSnapshots.CanonicalPayload.generate_use_queued
#print axioms Ash.OneShot.SourceBoundSnapshots.CanonicalPayload.returned_use_queued
