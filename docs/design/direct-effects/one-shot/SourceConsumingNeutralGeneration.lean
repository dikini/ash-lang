import SourceConsumingNeutralContext

/-! Contextual source admission through neutral caller changes. The source rule
is sound by the general generation induction in SourceConsumingCleanupAdmission. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceConsumingClauseAnnotations (Body Generated)
open SourceScheduledCapabilityAnnotations (Code DeclarationPolicy DeclarationLaws)

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

/-- No restriction on saved code or handler requirements is needed. -/
theorem At.pure_frame {body : Body world owner plan}
    {context : Context world owner outward actions phases whole front saved waiting}
    (source : At laws project body context) :
    At laws project body (context.pure_frame laws project) :=
  .neutral (.extra .refl) (.extra .refl) context.pure_frame_bounds source

/-- Construct the full source record at a pure focus frame from its original
record. Saved pending code, cleanup callbacks and handler requirements remain
unrestricted. The finite checks are derived independently. -/
noncomputable def QueuedBody.focus_neutral
    {context : Context world owner outward actions phases whole front saved waiting}
    {bounds : SourcePlanBounds.Annotation world plan}
    (queued : QueuedBody laws project resumeRequired closeRequired context bounds) :
    QueuedBody laws project resumeRequired closeRequired (context.pure_frame laws project) bounds :=
  ⟨queued.body, queued.origin, queued.source.pure_frame, queued.nested,
    context.pure_frame_checked queued.checked⟩

theorem QueuedBody.focus_neutral_body
    {context : Context world owner outward actions phases whole front saved waiting}
    {bounds : SourcePlanBounds.Annotation world plan}
    (queued : QueuedBody laws project resumeRequired closeRequired context bounds) :
    queued.focus_neutral.body = queued.body := rfl

/-- An actual focus split supplies the original child; neutral admission now
constructs its record at the entered receiver for every saved forest. -/
theorem FocusedSource.current_neutral
    {context : Context world owner outward actions phases whole front saved waiting}
    {child : Plan childDependencies} {childBounds : SourcePlanBounds.Annotation world child}
    (focused : FocusedSource laws project resumeRequired closeRequired context
      childBounds (.absent (plan := Plan.pure))) :
    Nonempty (QueuedBody laws project resumeRequired closeRequired
      (context.pure_frame laws project) childBounds) := by
  obtain ⟨original⟩ := focused.current_body
  exact ⟨original.focus_neutral⟩

theorem QueuedBody.focus_neutral_generated
    {context : Context world owner outward actions phases whole front saved waiting}
    {bounds : SourcePlanBounds.Annotation world plan}
    (queued : QueuedBody laws project resumeRequired closeRequired context bounds) :
    ∃ annotation : Code world plan (.plain Plan.pure whole),
      annotation.Valid outward actions phases ∧
      Generated actions context.continuationBounds queued.body annotation := by
  obtain ⟨annotation, ready, generated⟩ := queued.focus_neutral.source.generate_source queued.focus_neutral.checked
  exact ⟨annotation, ready, by
    simpa only [queued.focus_neutral_body,
      (context.pure_frame_bounds (laws := laws) (project := project)).continuationBounds_eq] using generated⟩

end Ash.OneShot.SourceConsumingCleanupAdmission

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.pure_frame
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.QueuedBody.focus_neutral
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.QueuedBody.focus_neutral_body
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.FocusedSource.current_neutral
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.QueuedBody.focus_neutral_generated
