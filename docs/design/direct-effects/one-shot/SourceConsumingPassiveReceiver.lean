import SourceConsumingReceiverAdmission

/-! Derive receiver-entry obligations for saved forests with no code positions
or handler requirements. The source body retains its full grammar. Operation,
permission and phase checks remain independent; emptiness grants none of them. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceConsumingClauseAnnotations (Body)
open SourceScheduledCapabilityAnnotations (DeclarationPolicy DeclarationLaws)

/-- Saved frames with no code to execute and no handler requirements. A fresh
handler delimiter is included; ordinary pending code and callbacks are not. -/
inductive PassiveSaved : {scope : SourceDependencyCapture.Scope} → {hints : Hints scope} → Forest hints → Prop where
  | nil : PassiveSaved .nil
  | handler : PassiveSaved tail → PassiveSaved
      (.handler (effect := effect) (table := table) (families := families) (required := []) tail)
  | cell : PassiveSaved tail → PassiveSaved (.cell (identity := identity) tail)
  | running : PassiveSaved tail → PassiveSaved (.running tail)
  | live : PassiveSaved saved → PassiveSaved tail → PassiveSaved (.live (owner := owner) saved tail)
  | spent : PassiveSaved tail → PassiveSaved (.spent (owner := owner) tail)

theorem PassiveSaved.append (first : PassiveSaved front) (second : PassiveSaved tail) :
    PassiveSaved (front.append tail) := by
  induction first with
  | nil => exact second
  | handler before ih => exact .handler ih
  | cell before ih => exact .cell ih
  | running before ih => exact .running ih
  | live saved before ihSaved ih => exact .live saved ih
  | spent before ih => exact .spent ih

theorem PassiveSaved.forClosing (passive : PassiveSaved forest) : PassiveSaved forest.forClosing := by
  induction passive with
  | nil => exact .nil
  | handler before ih | spent before ih => exact ih
  | cell before ih => exact .cell ih
  | running before ih => exact .running ih
  | live saved before ihSaved ih => exact ihSaved.append (.running ih)

/-- Every operation interface on these exact forests has no outstanding
requirements, regardless of the chosen receiving suffix. -/
theorem PassiveSaved.interface_check (passive : PassiveSaved forest)
    (source : SourceScheduledRetainedInterfaces.Interfaces world forest) (outside : SourceDependencyCapture.Scope) :
    source.check outside = true := by
  induction passive generalizing outside with
  | nil => cases source; rfl
  | handler before ih => cases source with | handler rest tail => exact ih tail outside
  | cell before ih => cases source with | cell tail => exact ih tail outside
  | running before ih => cases source with | running tail => exact ih tail outside
  | spent before ih => cases source with | spent tail => exact ih tail outside
  | live saved before ihSaved ih => cases source with
    | live rest inside tail => exact Bool.and_eq_true_iff.mpr ⟨ihSaved inside _, ih tail outside⟩

variable [declarations : DeclarationPolicy]

/-- Receiver rechecking is derived for any original capability annotation on
this forest, so existential compiler witnesses need not be unfolded. -/
theorem PassiveSaved.recheck (passive : PassiveSaved forest)
    {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
    (source : SourceScheduledCapabilityAnnotations.Retained world forest outside)
    {nextHints : Hints nextScope} {next : Forest nextHints} :
    SourceScheduledSourceRechecking.ReceiverChange outward actions phases source next := by
  induction passive generalizing outsideScope nextScope with
  | nil => exact .empty
  | handler before ih => cases source with
    | operations interfaces => exact .operations interfaces ((PassiveSaved.handler before).interface_check interfaces _)
    | handler tail => exact .handler rfl (ih tail)
  | cell before ih => cases source with
    | operations interfaces => exact .operations interfaces ((PassiveSaved.cell before).interface_check interfaces _)
    | cell tail => exact .cell (ih tail)
  | running before ih => cases source with
    | operations interfaces => exact .operations interfaces ((PassiveSaved.running before).interface_check interfaces _)
    | running tail => exact .running (ih tail)
  | spent before ih => cases source with
    | operations interfaces => exact .operations interfaces ((PassiveSaved.spent before).interface_check interfaces _)
    | spent tail => exact .spent (ih tail)
  | live saved before ihSaved ih => cases source with
    | operations interfaces => exact .operations interfaces ((PassiveSaved.live saved before).interface_check interfaces _)
    | live inside tail => exact .live (ihSaved inside) (ih tail)

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]
  {laws : DeclarationLaws declarations admission certification outward}
  {project : ∀ {clauses families required} {plans : ClausePlans clauses families},
    admission.accepts outward required plans → declarations.accepts required plans}

omit [SourceScheduledChecks.DeclarationProjection admission certification] in
/-- Derive all nested receiver obligations from the saved forest's structural
shape. The source body itself may contain effects, handlers and cleanup. -/
theorem ReceiverChecks.passive_saved {plan : Plan dependencies} (body : Body world owner plan) :
    ∀ {wholeScope frontScope savedScope waitingScope}
      {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
      {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
      {whole : Forest wholeHints} {front : Forest frontHints}
      {saved : Forest savedHints} {waiting : Forest waitingHints},
      PassiveSaved saved → (context : Context world owner outward actions phases whole front saved waiting) →
      ReceiverChecks laws (@project) actions phases body context := by
  induction body with
  | resume => intros; exact .resume
  | dispose => intros; exact .dispose
  | sequence required footprint declared rest ih => intros; exact .sequence (ih ‹_› _)
  | choice first second ihFirst ihSecond => intros; exact .choice (ihFirst ‹_› _) (ihSecond ‹_› _)
  | handler bounds declared inner ih =>
      intros
      rename_i passive context
      exact .handler (fun permission => passive.recheck (context.resumption permission).val)
        (fun permission => passive.forClosing.recheck (context.closing permission).val) (ih passive _)
  | cleanup required footprint declared inner ih =>
      intros
      rename_i passive context
      exact .cleanup (fun permission => passive.recheck (context.resumption permission).val)
        (fun permission => passive.forClosing.recheck (context.closing permission).val) (ih passive _)
  | resource inner ih =>
      intros
      exact .resource (fun identity fresh => ih identity fresh ‹_› _)

/-- Reuse the general source reconstruction theorem after deriving its
receiver obligations from the actual saved forest. -/
theorem At.recheck_passive_saved
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    {original : Context world owner outward actions phases whole front saved waiting}
    {nextWholeHints : Hints nextWholeScope} {nextFrontHints : Hints nextFrontScope}
    {nextSavedHints : Hints nextSavedScope} {nextWaitingHints : Hints nextWaitingScope}
    {nextWhole : Forest nextWholeHints} {nextFront : Forest nextFrontHints}
    {nextSaved : Forest nextSavedHints} {nextWaiting : Forest nextWaitingHints}
    {current : Context world owner outward actions phases nextWhole nextFront nextSaved nextWaiting}
    {body : Body world owner plan} (source : At laws project body original)
    (passive : PassiveSaved nextSaved) : At laws project body current :=
  (ReceiverChecks.passive_saved body passive current).reconstruct source

end Ash.OneShot.SourceConsumingCleanupAdmission

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.PassiveSaved.append
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.PassiveSaved.forClosing
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.PassiveSaved.interface_check
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.PassiveSaved.recheck
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.ReceiverChecks.passive_saved
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.recheck_passive_saved
