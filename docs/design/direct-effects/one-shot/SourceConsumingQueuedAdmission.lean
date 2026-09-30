import SourceConsumingAdmissionDescent
import SourceConsumingReceiverGeneration
import SourceAnnotatedBoundFocus
import SourceBoundReturns

/-! Source derivations retained beside queued bound data. Focus distinguishes
an operation-interface child with a consuming queued body from a consuming
child under a pure frame. Return uses the retained derivation; it never infers
contextual admission from bound metadata alone. -/
namespace Ash.OneShot.SourceConsumingClauseAnnotations
open SourceDeclarationPlans (Plan)

variable [SourceScheduledCapabilityAnnotations.DeclarationPolicy]

/-- Recompose a queued consuming body with the value prefixes prescribed by
the existing runtime context grammar. -/
def Body.plug {plan : Plan dependencies} (body : Body world owner plan)
    (position : SourceAnnotatedCode.Context) : Body world owner (body.boundAnnotation.plug position).2.1 := by
  cases position <;> first
    | exact .sequence (before := Plan.pure) [] .pure .pure body
    | exact .sequence (before := Plan.pure) [] .pure .pure
        (.sequence (before := Plan.pure) [] .pure .pure body)

theorem Body.plug_bounds {plan : Plan dependencies} (body : Body world owner plan)
    (position : SourceAnnotatedCode.Context) :
    (body.plug position).boundAnnotation = (body.boundAnnotation.plug position).2.2 := by
  cases position <;> rfl

theorem Body.Nested.plug {body : Body world owner plan} (nested : body.Nested)
    (position : SourceAnnotatedCode.Context) : (body.plug position).Nested := by
  cases position <;> first | exact .sequence nested | exact .sequence (.sequence nested)

end Ash.OneShot.SourceConsumingClauseAnnotations

namespace Ash.OneShot.SourceConsumingCleanupAdmission
open SourceContextualHints (Hints Requirement checkRequirements)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceConsumingClauseAnnotations (Body)
open SourceScheduledCapabilityAnnotations (Code DeclarationPolicy DeclarationLaws)
open SourcePlanBounds (Annotation)
open SourceBoundSnapshots (Snapshot Returned)
open SourceScheduledAdaptationCompilation (RequestFootprint)
open SourceScheduledSourceInterfaces (Declared)
open SourcePlanSignatures (signature)

variable [declarations : DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]

/-- The queued source witness is indexed by the actual annotation on its plain
frame and its receiving context. It contains original structural derivations,
not a proposition about a future execution or a successful future check. -/
structure QueuedBody
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    (resumeRequired closeRequired : List Requirement)
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (context : Context world owner outward actions phases whole front saved waiting)
    {plan : Plan dependencies} (bounds : Annotation world plan) where
  body : Body world owner plan
  origin : bounds = body.boundAnnotation
  source : At laws project body context
  nested : body.Nested
  checked : body.BoundCheck resumeRequired closeRequired actions phases wholeScope waitingScope context.before

variable {laws : DeclarationLaws declarations admission certification outward}
  {project : ∀ {clauses families required} {plans : ClausePlans clauses families},
    admission.accepts outward required plans → declarations.accepts required plans}
  {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
  {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
  {whole : Forest wholeHints} {front : Forest frontHints}
  {saved : Forest savedHints} {waiting : Forest waitingHints}
  {context : Context world owner outward actions phases whole front saved waiting}

theorem At.plug {body : Body world owner plan} (source : At laws project body context)
    (position : SourceAnnotatedCode.Context) : At laws project (body.plug position) context := by
  cases position <;> first | exact .sequence source | exact .sequence (.sequence source)

/-- Return adds pure value prefixes. Their operation requirements are empty;
the original independent continuation checks are unchanged. -/
def QueuedBody.plug {bounds : Annotation world plan}
    (queued : QueuedBody laws project resumeRequired closeRequired context bounds)
    (position : SourceAnnotatedCode.Context) :
    QueuedBody laws project resumeRequired closeRequired context (bounds.plug position).2.2 := by
  rcases queued with ⟨body, rfl, source, nested, checked⟩
  refine ⟨body.plug position, (body.plug_bounds position).symm, source.plug position,
    nested.plug position, ?_⟩
  cases position <;> first | exact ⟨rfl, checked⟩ | exact ⟨rfl, rfl, checked⟩

/-- Plain return selects exactly this queued source record. Recomposition
constructs admission; it does not ask for it at the successor. -/
theorem QueuedBody.returned {bounds : Annotation world plan}
    (queued : QueuedBody laws project resumeRequired closeRequired context bounds)
    (position : SourceAnnotatedCode.Context)
    {currentPlan : Plan currentDependencies} (currentBounds : Annotation world currentPlan)
    (pending : SourceBoundSnapshots.Retained world whole) {next : Snapshot world}
    (step : Returned position
      ⟨_, currentPlan, currentBounds, _, _, .plain plan whole, .plain bounds pending⟩ next) :
    ∃ nextQueued : QueuedBody laws project resumeRequired closeRequired context (bounds.plug position).2.2,
      next = ⟨_, _, nextQueued.body.boundAnnotation, _, _, whole, pending⟩ := by
  refine ⟨queued.plug position, ?_⟩
  cases step
  rw [← (queued.plug position).origin]
  rfl

/-- A focus step either runs an operation interface and queues a consuming
body, or runs the consuming body under one additional pure pending frame.
The latter keeps its original context explicitly; it does not assert an At
derivation at the expanded receiver. -/
inductive FocusedSource
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    (resumeRequired closeRequired : List Requirement)
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (context : Context world owner outward actions phases whole front saved waiting) :
    {childDependencies restDependencies : SourceDependencyAnnotations.Dependencies} →
    {child : Plan childDependencies} → {rest : Plan restDependencies} →
    Annotation world child → Annotation world rest → Prop where
  | queued {rest : Plan restDependencies} {restBounds : Annotation world rest}
      (footprint : RequestFootprint child required)
      (declared : Declared world (signature child))
      (supplied : checkRequirements (.plain restDependencies wholeScope) required = true)
      (source : QueuedBody laws project resumeRequired closeRequired context restBounds) :
      FocusedSource laws project resumeRequired closeRequired context (.absent (plan := child)) restBounds
  | current {child : Plan childDependencies} {childBounds : Annotation world child}
      (source : QueuedBody laws project resumeRequired closeRequired context childBounds) :
      FocusedSource laws project resumeRequired closeRequired context childBounds (.absent (plan := .pure))

/-- All existing focus-bound splits are covered. The pure-plan alternative is
impossible for a consuming body; pair-right is the explicit current-body case. -/
theorem At.focused {body : Body world owner plan}
    (source : At laws project body context) (nested : body.Nested)
    (checked : body.BoundCheck resumeRequired closeRequired actions phases wholeScope waitingScope context.before)
    {child : Plan childDependencies} {rest : Plan restDependencies}
    {childBounds : Annotation world child} {restBounds : Annotation world rest}
    (step : SourcePlanBounds.Focused world body.boundAnnotation childBounds restBounds) :
    FocusedSource laws project resumeRequired closeRequired context childBounds restBounds := by
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

/-- If the rest has consuming syntax, focus must have retained its source
record. The supplied body only rules out the pure rest; its admission is not
a premise, and the returned record comes from the focus result. -/
theorem FocusedSource.queued_body
    {child : Plan childDependencies} {rest : Plan restDependencies}
    {childBounds : Annotation world child} {restBounds : Annotation world rest}
    (focused : FocusedSource laws project resumeRequired closeRequired context childBounds restBounds)
    (restBody : Body world owner rest) :
    Nonempty (QueuedBody laws project resumeRequired closeRequired context restBounds) := by
  cases focused with
  | queued footprint declared supplied source => exact ⟨source⟩
  | current source => cases restBody

/-- A pure queued plan cannot hold a consuming source. In this case the
original contextual record belongs to the current child instead. -/
theorem FocusedSource.current_body
    {child : Plan childDependencies} {childBounds : Annotation world child}
    (focused : FocusedSource laws project resumeRequired closeRequired context
      childBounds (.absent (plan := .pure))) :
    Nonempty (QueuedBody laws project resumeRequired closeRequired context childBounds) := by
  cases focused with
  | queued footprint declared supplied source => cases source.body
  | current source => exact ⟨source⟩

/-- The retained source evidence generates valid code at the actual child
receiver. The consuming-current case reuses neutral expansion and does not
silently identify the original and expanded contextual judgments. -/
theorem FocusedSource.child_valid
    {child : Plan childDependencies} {rest : Plan restDependencies}
    {childBounds : Annotation world child} {restBounds : Annotation world rest}
    (focused : FocusedSource laws project resumeRequired closeRequired context childBounds restBounds) :
    ∃ annotation : Code world child (.plain rest whole),
      annotation.Valid outward actions phases ∧ SourcePlanBounds.ofCode annotation = childBounds := by
  cases focused with
  | queued footprint declared supplied source => exact ⟨.operations _ footprint declared, supplied, rfl⟩
  | current source =>
      obtain ⟨annotation, valid, same⟩ := source.source.generate_expanding source.checked (.extra .refl)
      exact ⟨annotation, valid, same.trans source.origin.symm⟩

end Ash.OneShot.SourceConsumingCleanupAdmission

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Body.plug_bounds
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Body.Nested.plug
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.plug
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.QueuedBody.plug
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.QueuedBody.returned
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.focused
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.FocusedSource.queued_body
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.FocusedSource.current_body
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.FocusedSource.child_valid
