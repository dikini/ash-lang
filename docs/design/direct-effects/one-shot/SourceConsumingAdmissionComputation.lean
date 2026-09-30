import SourceConsumingAdmissionDescent
import SourceBoundComputation

/-! Ordinary computation selects an existing consuming source subtree. The
bound-snapshot transition determines that subtree; successor admission is
derived from the original structural judgment, not supplied by the event.
This covers computation at an unchanged receiver, not the intervening execution
of an effectful prefix or its capture and restoration under a changed receiver. -/
namespace Ash.OneShot.SourceConsumingClauseAnnotations
open SourceDeclarationPlans (Plan)
open SourcePlanBounds (ComputationRule Annotation)

variable [SourceScheduledCapabilityAnnotations.DeclarationPolicy]

/-- The four ordinary reductions select source subtrees without changing any
continuation context. Prefix operation interfaces have already been evaluated
when the corresponding runtime reduction occurs. -/
inductive Body.Reduction : ComputationRule →
    {beforeDependencies afterDependencies : SourceDependencyAnnotations.Dependencies} →
    {before : Plan beforeDependencies} → {after : Plan afterDependencies} →
    Body world owner before → Body world owner after → Prop where
  | bind : Reduction .bind (.sequence required footprint declared body) body
  | beta : Reduction .beta
      (.sequence functionRequired functionFootprint functionDeclared
        (.sequence argumentRequired argumentFootprint argumentDeclared body)) body
  | ifTrue : Reduction .ifTrue
      (.sequence required footprint declared (.choice yes no)) yes
  | ifFalse : Reduction .ifFalse
      (.sequence required footprint declared (.choice yes no)) no

/-- Source reduction retains the exact bound annotation selected by the
existing computation relation. -/
theorem Body.Reduction.bounds {before : Body world owner beforePlan} {after : Body world owner afterPlan}
    (step : before.Reduction rule after) :
    SourcePlanBounds.Reduced world rule before.boundAnnotation after.boundAnnotation := by
  cases step
  · exact .bind _
  · exact .beta _
  · exact .ifTrue _
  · exact .ifFalse _

/-- Every surviving handler keeps the same declaration-admission derivation.
This is source evidence, stronger than validity of the projected bounds alone. -/
theorem Body.Reduction.nested {before : Body world owner beforePlan} {after : Body world owner afterPlan}
    (step : before.Reduction rule after) (admitted : before.Nested) : after.Nested := by
  cases step with
  | bind => cases admitted with | sequence rest => exact rest
  | beta => cases admitted with | sequence rest => cases rest with | sequence inner => exact inner
  | ifTrue => cases admitted with | sequence rest => cases rest with | choice yes no => exact yes
  | ifFalse => cases admitted with | sequence rest => cases rest with | choice yes no => exact no

/-- Invert the actual bound reduction to recover its source subtree. No source
reduction witness is requested separately from the runtime's selected bounds. -/
theorem Body.reduced_source {plan : Plan dependencies} (body : Body world owner plan)
    {nextPlan : Plan nextDependencies} {nextBounds : Annotation world nextPlan}
    (step : SourcePlanBounds.Reduced world rule body.boundAnnotation nextBounds) :
    ∃ next : Body world owner nextPlan,
      body.Reduction rule next ∧ nextBounds = next.boundAnnotation := by
  cases step with
  | bind =>
      cases body with
      | sequence required footprint declared rest => exact ⟨rest, .bind, rfl⟩
  | beta =>
      cases body with
      | sequence required footprint declared rest =>
          cases rest with
          | sequence argumentRequired argumentFootprint argumentDeclared inner => exact ⟨inner, .beta, rfl⟩
  | ifTrue =>
      cases body with
      | sequence required footprint declared rest =>
          cases rest with
          | choice yes no => exact ⟨yes, .ifTrue, rfl⟩
  | ifFalse =>
      cases body with
      | sequence required footprint declared rest =>
          cases rest with
          | choice yes no => exact ⟨no, .ifFalse, rfl⟩

end Ash.OneShot.SourceConsumingClauseAnnotations

namespace Ash.OneShot.SourceConsumingCleanupAdmission
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceConsumingClauseAnnotations (Body)
open SourceScheduledCapabilityAnnotations (DeclarationPolicy DeclarationLaws)
open SourceBoundSnapshots (Snapshot Computed)

variable [declarations : DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]
  {laws : DeclarationLaws declarations admission certification outward}
  {project : ∀ {clauses families required} {plans : ClausePlans clauses families},
    admission.accepts outward required plans → declarations.accepts required plans}
  {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
  {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
  {whole : Forest wholeHints} {front : Forest frontHints}
  {saved : Forest savedHints} {waiting : Forest waitingHints}
  {plan : Plan dependencies} {body : Body world owner plan}
  {current : Context world owner outward actions phases whole front saved waiting}

/-- The original source admission and finite check derive both successor
judgments for all four ordinary rules. The context, including its saved and
closing source derivations, is the same value. -/
theorem At.reduce {next : Body world owner nextPlan}
    (admitted : At laws project body current)
    (checked : body.BoundCheck resumeRequired closeRequired actions phases wholeScope waitingScope current.before)
    (step : body.Reduction rule next) :
    At laws project next current ∧
    next.BoundCheck resumeRequired closeRequired actions phases wholeScope waitingScope current.before := by
  cases step with
  | bind => exact ⟨admitted.sequence_rest, checked.2⟩
  | beta => exact ⟨admitted.sequence_rest.sequence_rest, checked.2.2⟩
  | ifTrue => exact ⟨admitted.sequence_rest.choice_branches.1, checked.2.1⟩
  | ifFalse => exact ⟨admitted.sequence_rest.choice_branches.2, checked.2.2⟩

/-- A supplied computation event fixes the successor snapshot. Recover the
source subtree from that event and retain the full original contextual proof.
No successor source, validity or scheduling check occurs among the premises. -/
theorem At.computed
    (admitted : At laws project body current)
    (checked : body.BoundCheck resumeRequired closeRequired actions phases wholeScope waitingScope current.before)
    (pending : SourceBoundSnapshots.Retained world whole) {next : Snapshot world}
    (step : Computed rule ⟨_, plan, body.boundAnnotation, _, _, whole, pending⟩ next) :
    ∃ nextDependencies, ∃ nextPlan : Plan nextDependencies, ∃ nextBody : Body world owner nextPlan,
      At laws project nextBody current ∧
      nextBody.BoundCheck resumeRequired closeRequired actions phases wholeScope waitingScope current.before ∧
      body.Reduction rule nextBody ∧
      next = ⟨_, nextPlan, nextBody.boundAnnotation, _, _, whole, pending⟩ := by
  cases step with
  | step source nextBounds selected =>
      obtain ⟨nextBody, reduced, same⟩ := body.reduced_source selected
      obtain ⟨nextSource, nextChecked⟩ := admitted.reduce checked reduced
      exact ⟨_, _, nextBody, nextSource, nextChecked, reduced, by cases same; rfl⟩

end Ash.OneShot.SourceConsumingCleanupAdmission

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Body.Reduction.bounds
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Body.Reduction.nested
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Body.reduced_source
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.reduce
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.computed
