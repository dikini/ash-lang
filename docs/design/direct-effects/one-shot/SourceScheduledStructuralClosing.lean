import SourceScheduledSourceRechecking
import SourceBoundDisposal
import SourceScheduledRetainedSplit

/-! Structural closing of original retained source. The traversal is fixed by
runtime forClosing; callback rechecking uses the existing expression judgment.
No target-validity, target-schedule or arbitrary replacement-metadata premise
is admitted. -/
namespace Ash.OneShot.SourceBoundSnapshots
open SourceRetainedPlans (Forest)

/-- Closing an operation-only snapshot remains operation-only metadata. -/
theorem Retained.absent_forClosing (forest : Forest hints) :
    (Retained.absent forest (world := world)).forClosing = Retained.absent forest.forClosing := by
  induction forest <;> simp_all only [Retained.absent, Retained.forClosing, Forest.forClosing,
    SourceContextualInvocationHints.forClosing, SourceDependencyCapture.Scope.forClosing,
    ← Retained.absent_append]

end Ash.OneShot.SourceBoundSnapshots

namespace Ash.OneShot.SourceScheduledSourceRechecking
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledCapabilityAnnotations (Code Retained DeclarationPolicy DeclarationLaws)
open SourceBoundSnapshots.Retained (ofCapability)

/-- A closing derivation retains cells, callbacks and running frames; drops
ordinary pending code, handlers and spent history; and closes dormant saved
work before its running tail. Only callback receiver changes need Expression. -/
inductive Closing [DeclarationPolicy] (outward : List Instance) (actions : Syntax.UsageTickets)
    (phases : OwnerPhaseTransitions.Phases) :
    {world : List Nat} → {scope outsideScope nextScope : SourceDependencyCapture.Scope} →
    {hints : Hints scope} → {outsideHints : Hints outsideScope} → {nextHints : Hints nextScope} →
    {forest : Forest hints} → {outside : Forest outsideHints} →
    Retained world forest outside → Forest nextHints → Prop where
  | operations {forest : Forest hints} {nextHints : Hints nextScope} {next : Forest nextHints}
      {original : SourceScheduledRetainedInterfaces.Interfaces world forest}
      (interfaces : SourceScheduledRetainedInterfaces.Interfaces world forest.forClosing)
      (supplied : interfaces.check nextScope = true) :
      Closing outward actions phases (.operations (world := world) original) next
  | plain : Closing outward actions phases tail next → Closing outward actions phases (.plain code tail) next
  | handler : Closing outward actions phases tail next →
      Closing outward actions phases (.handler (effect := effect) (table := table) (families := families) (required := required) tail) next
  | cell : Closing outward actions phases tail next → Closing outward actions phases (.cell (identity := identity) tail) next
  | cleanup {rest : Forest restHints} {outside : Forest outsideHints} {next : Forest nextHints}
      {code : Code world plan (.running (rest.append outside))} {tail : Retained world rest outside}
      (callback : Expression outward actions phases code (.running (rest.forClosing.append next))) :
      Closing outward actions phases tail next → Closing outward actions phases (.cleanup (needs := needs) code tail) next
  | running : Closing outward actions phases tail next → Closing outward actions phases (.running tail) next
  | live {rest : Forest restHints} {outside : Forest outsideHints} {next : Forest nextHints}
      {saved : Retained world captured (rest.append outside)} {tail : Retained world rest outside} :
      Closing outward actions phases saved ((Forest.running rest.forClosing).append next) →
      Closing outward actions phases tail next → Closing outward actions phases (.live (owner := owner) saved tail) next
  | spent : Closing outward actions phases tail next → Closing outward actions phases (.spent (owner := owner) tail) next

variable [declarations : DeclarationPolicy]

/-- The restricted closing traversal embeds into existing source rechecking. -/
theorem Closing.rechecking {source : Retained world forest outside}
    (closing : Closing outward actions phases source next) :
    RetainedChange outward actions phases source forest.forClosing next := by
  induction closing with
  | operations interfaces supplied => exact .operations interfaces supplied
  | plain tail ih => exact .dropPlain ih
  | handler tail ih => exact .dropHandler ih
  | cell tail ih => exact .cell ih
  | cleanup callback tail ih => exact .cleanup callback ih
  | running tail ih => exact .running ih
  | live saved tail ihSaved ihTail => exact .closeLive ihSaved ihTail
  | spent tail ih => exact .dropSpent ih

/-- Empty source needs no callback rechecking. -/
theorem Closing.empty {source : Retained world .nil outside} : Closing outward actions phases source next := by
  rw [retained_nil_eq source]
  exact .operations .nil rfl

/-- Closing removes an inserted delimiter, including inside recursively saved
branches. Reuse actual forest equality rather than rechecking callback code. -/
theorem Closing.at_fresh_handler
    {frontHints : Hints frontScope} {outsideHints : Hints outsideScope}
    {front : Forest frontHints} {outside : Forest outsideHints}
    {source : Retained world front originalOutside}
    (closing : Closing outward actions phases source outside) :
    RetainedChange outward actions phases source
      (front.append (.handler (effect := effect) (table := table) (families := families)
        (required := required) .nil)).forClosing outside := by
  apply (SourceScheduledRecomposition.predicate_congr
    (SourceHandlerRequests.forClosing_inserted frontScope)
    (SourceScheduledHandlerRequests.hints_forClosing_inserted frontHints .nil)
    (SourceScheduledHandlerRequests.forest_forClosing_inserted front .nil)
    (fun target => RetainedChange outward actions phases source target outside)).mpr
  apply (SourceScheduledRecomposition.predicate_congr
    (SourceDependencyProjection.scope_append_nil frontScope)
    (SourcePlannedRecomposition.hints_append_nil frontHints)
    (SourceScheduledRecomposition.forest_append_nil front)
    (fun target => RetainedChange outward actions phases source target.forClosing outside)).mpr
  exact closing.rechecking

/-- Fresh capture consumes the standard structural closing traversal of its
original normal prefix. Its new delimiter adds no callback or owner. -/
theorem Expression.fresh_closing
    {frontHints : Hints frontScope} {waitingHints : Hints waitingScope}
    {afterHints : Hints afterScope}
    {front : Forest frontHints} {waiting : Forest waitingHints} {after : Forest afterHints}
    {source : Code world (.request (effect := effect) (operation := operation)) (front.append waiting)}
    (intercepted : SourceScheduledHandlerSelection.Intercept effect operation contract modes table families required
      (front.append waiting) after
      (front.append (.handler (effect := effect) (table := table) (families := families) (required := required) .nil)) waiting)
    (normal : Retained world front waiting)
    (original : contract.dispose = true → normal.Valid outward actions phases)
    (guarded : SourceDependencyCapture.checkCapture outward afterScope effect operation = true)
    (bounded : contract.dispose = true → SourceDependencyOwners.PendingWithin world
      (SourceDependencyOwners.owners (frontScope.append (.handler effect table families .nil)))
      (frontScope.append (.handler effect table families .nil)))
    (closing : ∀ _disposes : contract.dispose = true, Closing outward actions phases normal (.running waiting)) :
    Expression outward actions phases source after :=
  .freshRich intercepted normal original guarded bounded (fun disposes => (closing disposes).at_fresh_handler)

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]

/-- Original source validity and structural closing derive a valid closing
annotation with EXACT canonical runtime metadata. Expression compilation and
ordered retained joins reuse their existing proofs. -/
theorem Closing.compile_retaining
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {source : Retained world forest outside}
    (closing : Closing outward actions phases source next) (ready : source.Valid outward actions phases) :
    ∃ annotation : Retained world forest.forClosing next,
      annotation.Valid outward actions phases ∧ ofCapability annotation = (ofCapability source).forClosing := by
  induction closing with
  | operations interfaces supplied =>
      exact ⟨.operations interfaces, supplied, (SourceBoundSnapshots.Retained.absent_forClosing _).symm⟩
  | plain tail ih => exact ih ready.2
  | handler tail ih => exact ih ready.2
  | cell tail ih =>
      obtain ⟨annotation, valid, kept⟩ := ih ready
      exact ⟨.cell annotation, valid, congrArg SourceBoundSnapshots.Retained.cell kept⟩
  | cleanup callback tail ih =>
      obtain ⟨code, codeReady, codeKept⟩ := callback.compile_retaining laws project ready.1
      obtain ⟨rest, restReady, restKept⟩ := ih ready.2
      refine ⟨.cleanup code rest, ⟨codeReady, restReady⟩, ?_⟩
      simp only [ofCapability, SourceBoundSnapshots.Retained.forClosing, codeKept, restKept,
        Forest.forClosing, SourceContextualInvocationHints.forClosing, SourceDependencyCapture.Scope.forClosing]
  | running tail ih =>
      obtain ⟨annotation, valid, kept⟩ := ih ready
      exact ⟨.running annotation, valid, congrArg SourceBoundSnapshots.Retained.running kept⟩
  | live saved tail ihSaved ihTail =>
      obtain ⟨inside, insideReady, insideKept⟩ := ihSaved ready.1
      obtain ⟨rest, restReady, restKept⟩ := ihTail ready.2
      refine ⟨inside.joinSource (.running rest),
        (inside.joinSource_valid (.running rest)).mpr ⟨insideReady, restReady⟩, ?_⟩
      simpa only [ofCapability, SourceBoundSnapshots.Retained.forClosing, insideKept, restKept,
        Forest.forClosing, SourceContextualInvocationHints.forClosing, SourceDependencyCapture.Scope.forClosing]
        using inside.joinSource_bounds (.running rest)
  | spent tail ih => exact ih ready

/-- Admission follows from the original snapshot's canonical closing theorem. -/
theorem Closing.compile_admitted
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {source : Retained world forest outside}
    (closing : Closing outward actions phases source next) (ready : source.Valid outward actions phases)
    (admitted : (ofCapability source).Admitted) :
    ∃ annotation : Retained world forest.forClosing next,
      annotation.Valid outward actions phases ∧ ofCapability annotation = (ofCapability source).forClosing ∧
      (ofCapability annotation).Admitted := by
  obtain ⟨annotation, valid, kept⟩ := closing.compile_retaining laws project ready
  exact ⟨annotation, valid, kept, kept.symm ▸ admitted.forClosing⟩

end Ash.OneShot.SourceScheduledSourceRechecking

#print axioms Ash.OneShot.SourceBoundSnapshots.Retained.absent_forClosing
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.Closing.rechecking
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.Closing.empty
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.Closing.compile_retaining
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.Closing.compile_admitted

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.Closing.at_fresh_handler
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.Expression.fresh_closing
