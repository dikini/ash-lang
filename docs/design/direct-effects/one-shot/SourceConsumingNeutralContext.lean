import SourceConsumingReceiverAdmission
import SourceConsumingNeutralBoundCheck
import SourceScheduledNeutralBoundRetention

/-! Construct the actual context under a pure focus frame. Original retained
source transport preserves nonempty saved/closing metadata as well as empty
forests. The finite clause checks are derived independently. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceConsumingClauseAnnotations (Body)
open SourceScheduledCapabilityAnnotations (DeclarationPolicy DeclarationLaws neutral_receiver_laws)

variable [declarations : DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]
  {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
  {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
  {whole : Forest wholeHints} {front : Forest frontHints}
  {saved : Forest savedHints} {waiting : Forest waitingHints}

/-- Reuse original source transport, including dormant saved branches. No
source validity or new metadata is requested at the expanded receiver. -/
noncomputable def Context.pure_frame
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    (context : Context world owner outward actions phases whole front saved waiting) :
    Context world owner outward actions phases (.plain Plan.pure whole) (.plain Plan.pure front) saved waiting :=
  context.neutral laws project (.plain context.cut) (.plain front [] .pure .pure context.before) (.extra .refl)

variable {laws : DeclarationLaws declarations admission certification outward}
  {project : ∀ {clauses families required} {plans : ClausePlans clauses families},
    admission.accepts outward required plans → declarations.accepts required plans}

theorem Context.pure_frame_bounds
    (context : Context world owner outward actions phases whole front saved waiting) :
    context.BoundsAgree (context.pure_frame laws project) :=
  context.neutral_bounds laws project _ _ _

/-- The same source body passes its finite checks at the expanded caller. This
holds for any saved forest and does not assert contextual source admission. -/
theorem Context.pure_frame_checked
    (context : Context world owner outward actions phases whole front saved waiting)
    {body : Body world owner plan}
    (checked : body.BoundCheck resumeRequired closeRequired actions phases wholeScope waitingScope context.before) :
    body.BoundCheck resumeRequired closeRequired actions phases (.plain .pure wholeScope) waitingScope
      (context.pure_frame laws project).before :=
  body.boundCheck_neutral (receivingHints := wholeHints) waitingHints (.extra .refl) (.extra .refl) rfl checked

end Ash.OneShot.SourceConsumingCleanupAdmission

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.pure_frame_bounds
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.Context.pure_frame_checked
