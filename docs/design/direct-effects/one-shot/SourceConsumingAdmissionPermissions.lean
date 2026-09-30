import SourceConsumingAdmissionPhases

/-! Permission extension preserves contextual source admission. Existing
entries retain their rights; the bound owner's entry stays fixed so extension
cannot invent its saved-resumption or closing evidence. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission
open SourceContextualHints (Hints)
open SourceDependencyCapture (Scope)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceConsumingClauseAnnotations (Body)
open SourceScheduledCapabilityAnnotations (DeclarationPolicy DeclarationLaws)

variable [declarations : DeclarationPolicy]
  {wholeScope frontScope savedScope waitingScope : Scope}
  {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
  {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
  {whole : Forest wholeHints} {front : Forest frontHints}
  {saved : Forest savedHints} {waiting : Forest waitingHints}

/-- Original annotations are unchanged. The established joint capability
transport supplies their validity in the extended permission registry. -/
def Context.extend_permissions
    (context : Context world owner outward actions phases whole front saved waiting)
    (permissions : Syntax.UsageExtension actions nextActions) (same : actions owner = nextActions owner) :
    Context world owner outward nextActions phases whole front saved waiting where
  cut := context.cut
  before := context.before
  resumption := fun permission =>
    let original := context.resumption (by simpa only [same] using permission)
    ⟨original.val, original.val.valid_transport original.property permissions (fun _ _ ready => ready)⟩
  closing := fun permission =>
    let original := context.closing (by simpa only [same] using permission)
    ⟨original.val, original.val.valid_transport original.property permissions (fun _ _ ready => ready)⟩
  disposal := fun permission => context.disposal (by simpa only [same] using permission)
  after := context.after
  tailReady := context.after.valid_transport context.tailReady permissions (fun _ _ ready => ready)

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]
  {laws : DeclarationLaws declarations admission certification outward}
  {project : ∀ {clauses families required} {plans : ClausePlans clauses families},
    admission.accepts outward required plans → declarations.accepts required plans}
  {plan : Plan dependencies} {body : Body world owner plan}
  {context : Context world owner outward actions phases whole front saved waiting}

/-- Reuse structural rechecking transport through handler and cleanup entry.
The body, caller, phases and resource world remain unchanged. -/
theorem At.extend_permissions (admitted : At laws project body context)
    (permissions : Syntax.UsageExtension actions nextActions) (same : actions owner = nextActions owner) :
    At laws project body (context.extend_permissions permissions same) := by
  induction admitted with
  | resume => exact .resume
  | dispose => exact .dispose
  | sequence body ih => exact .sequence (ih same)
  | choice first second ihFirst ihSecond => exact .choice (ihFirst same) (ihSecond same)
  | handler bounds declared resumption closing body ih =>
      rename_i current
      apply At.handler (context := current.extend_permissions permissions same) bounds declared
        (fun permission => (resumption (by simpa only [same] using permission)).transport permissions (fun _ _ ready => ready))
        (fun permission => (closing (by simpa only [same] using permission)).transport permissions (fun _ _ ready => ready))
      refine At.sameReceiver
        (original := (current.handler laws project _ _ _ _ resumption closing).extend_permissions permissions same)
        rfl ?_ (ih same)
      constructor <;> (first | intro permission | skip) <;>
        simp only [Context.extend_permissions, Context.handler_resumption_bounds, Context.handler_closing_bounds, Context.handler_tail_bounds]

  | cleanupSource covered resumption closing body ih =>
      rename_i current footprint declared
      apply At.cleanupSource (context := current.extend_permissions permissions same) covered
        (fun permission => (resumption (by simpa only [same] using permission)).transport permissions (fun _ _ ready => ready))
        (fun permission => (closing (by simpa only [same] using permission)).transport permissions (fun _ _ ready => ready))
      refine At.sameReceiver
        (original := (current.cleanupSource laws project footprint declared _ resumption closing).extend_permissions permissions same)
        rfl ?_ (ih same)
      constructor <;> (first | intro permission | skip) <;>
        simp only [Context.extend_permissions, Context.cleanupSource_resumption_bounds, Context.cleanupSource_closing_bounds, Context.cleanupSource_tail_bounds]

  | sameReceiver caller metadata source ih =>
      refine .sameReceiver caller ?_ (ih same)
      exact ⟨fun permission => metadata.resumption _, fun permission => metadata.closing _, metadata.tail⟩
  | neutral receiver caller metadata source ih =>
      refine .neutral receiver caller ?_ (ih same)
      exact ⟨fun permission => metadata.resumption _, fun permission => metadata.closing _, metadata.tail⟩
  | waitingNeutral receiver caller waitingChange metadata tail source ih =>
      refine .waitingNeutral receiver caller waitingChange ?_ tail (ih same)
      exact ⟨fun permission => metadata.resumption _, fun permission => metadata.closing _⟩
  | resource body ih =>
      rename_i current
      apply At.resource
      intro identity fresh
      refine At.sameReceiver
        (original := (current.resource laws project identity).extend_permissions permissions same)
        rfl ?_ (ih identity fresh same)

      constructor <;> (first | intro permission | skip) <;>
        simp only [Context.extend_permissions, Context.resource_resumption_bounds, Context.resource_closing_bounds, Context.resource_tail_bounds]

/-- A checked consuming body has a known permission entry. UsageExtension
therefore supplies the required equality at its owner automatically. -/
theorem At.scheduled_extend_permissions (admitted : At laws project body context)
    (checked : body.BoundCheck resumeRequired closeRequired actions phases wholeScope waitingScope context.before)
    (permissions : Syntax.UsageExtension actions nextActions) :
    SourceScheduledChecks.Local outward nextActions phases world plan whole := by
  obtain ⟨rights, known⟩ := (body.boundCheck_owner checked).1
  have same := known.trans (permissions owner rights known).symm
  exact (admitted.extend_permissions permissions same).scheduled
    (body.boundCheck_owner_transport checked same (fun ready => ready))

/-- Keep a structural derivation, rather than only its scheduling consequence,
when the current owner's permission entry is known before extension. -/
theorem At.extend_known (admitted : At laws project body context)
    (permissions : Syntax.UsageExtension actions nextActions) (known : actions owner = some rights) :
    At laws project body (context.extend_permissions permissions (known.trans (permissions owner rights known).symm)) :=
  admitted.extend_permissions permissions (known.trans (permissions owner rights known).symm)

end Ash.OneShot.SourceConsumingCleanupAdmission

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.extend_permissions
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.scheduled_extend_permissions
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.extend_known
