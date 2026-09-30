import SourceScheduledCapabilityReconstruction
import SourceBoundResumption

/-! Recompose retained capability annotations while preserving their persistent
bound snapshot. Associativity reuses the existing scope, hint and forest laws;
no scheduling reconstruction chooses replacement bound metadata. -/
namespace Ash.OneShot.SourceScheduledCapabilityAnnotations
open SourceContextualHints (Hints checkRequirements)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open SourceScheduledRetainedInterfaces (Interfaces)
open SourceDependencyChecks (scope_append_assoc)
open SourcePlannedRecomposition (hints_append_assoc)
open SourceScheduledRecomposition (predicate_congr forest_append_assoc)
open SourcePlanBounds (ofCode)

variable [DeclarationPolicy]

private def scopeOf {hints : Hints scope} (_ : Forest hints) : SourceDependencyCapture.Scope := scope

/-- Reassociate a receiving forest, retaining the exact current-code projection. -/
theorem code_assoc_bounds {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {outsideHints : Hints outsideScope} (first : Forest firstHints) (second : Forest secondHints)
    (outside : Forest outsideHints) {plan : Plan dependencies} (bounds : SourcePlanBounds.Annotation world plan) :
    (∃ annotation : Code world plan ((first.append second).append outside),
      annotation.Valid outward actions phases ∧ ofCode annotation = bounds) ↔
    (∃ annotation : Code world plan (first.append (second.append outside)),
      annotation.Valid outward actions phases ∧ ofCode annotation = bounds) :=
  predicate_congr (scope_append_assoc _ _ _) (hints_append_assoc _ _ _) (forest_append_assoc first second outside)
    (fun forest => ∃ annotation : Code world plan forest, annotation.Valid outward actions phases ∧ ofCode annotation = bounds)

theorem running_code_assoc_bounds {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {outsideHints : Hints outsideScope} (first : Forest firstHints) (second : Forest secondHints)
    (outside : Forest outsideHints) {plan : Plan dependencies} (bounds : SourcePlanBounds.Annotation world plan) :
    (∃ annotation : Code world plan (.running ((first.append second).append outside)),
      annotation.Valid outward actions phases ∧ ofCode annotation = bounds) ↔
    (∃ annotation : Code world plan (.running (first.append (second.append outside))),
      annotation.Valid outward actions phases ∧ ofCode annotation = bounds) :=
  predicate_congr (scope_append_assoc _ _ _) (hints_append_assoc _ _ _) (forest_append_assoc first second outside)
    (fun forest => ∃ annotation : Code world plan (.running forest), annotation.Valid outward actions phases ∧ ofCode annotation = bounds)

/-- The saved forest is fixed while its receiver is reassociated; all its
persistent metadata, including dormant branches, remains identical. -/
theorem retained_assoc_bounds {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {outsideHints : Hints outsideScope} (first : Forest firstHints) (second : Forest secondHints)
    (outside : Forest outsideHints) {saved : Forest savedHints} (bounds : SourceBoundSnapshots.Retained world saved) :
    (∃ annotation : Retained world saved ((first.append second).append outside),
      annotation.Valid outward actions phases ∧ SourceBoundSnapshots.Retained.ofCapability annotation = bounds) ↔
    (∃ annotation : Retained world saved (first.append (second.append outside)),
      annotation.Valid outward actions phases ∧ SourceBoundSnapshots.Retained.ofCapability annotation = bounds) :=
  predicate_congr (scope_append_assoc _ _ _) (hints_append_assoc _ _ _) (forest_append_assoc first second outside)
    (fun forest => ∃ annotation : Retained world saved forest,
      annotation.Valid outward actions phases ∧ SourceBoundSnapshots.Retained.ofCapability annotation = bounds)

/-- Unfold operation-only prefix annotations without erasing the general
suffix's bounds. Primitive checks retain their original ordered receivers. -/
theorem prepend_interfaces_retaining {frontHints : Hints frontScope} {tailHints : Hints tailScope}
    {outsideHints : Hints outsideScope} {front : Forest frontHints} {tail : Forest tailHints} {outside : Forest outsideHints}
    (first : Interfaces world front) (second : Retained world tail outside)
    (ready : first.check (tailScope.append outsideScope) = true) (tailReady : second.Valid outward actions phases) :
    ∃ annotation : Retained world (front.append tail) outside, annotation.Valid outward actions phases ∧
      SourceBoundSnapshots.Retained.ofCapability annotation =
        (SourceBoundSnapshots.Retained.absent front).append (SourceBoundSnapshots.Retained.ofCapability second) := by
  induction first with
  | nil => exact ⟨second, tailReady, rfl⟩
  | plain rest required footprint declared next ih =>
      obtain ⟨requests, remaining⟩ := Bool.and_eq_true_iff.mp ready
      obtain ⟨joined, valid, kept⟩ := ih remaining
      refine ⟨.plain (.operations required footprint declared) joined, ⟨?_, valid⟩, ?_⟩
      · change checkRequirements ((scopeOf rest).append (tailScope.append outsideScope)) _ = true at requests
        simpa only [Code.Valid, scopeOf, scope_append_assoc] using requests
      · simpa only [SourceBoundSnapshots.Retained.ofCapability, SourceBoundSnapshots.Retained.absent,
          SourceBoundSnapshots.Retained.append, ofCode, Forest.append, Hints.append, SourceDependencyCapture.Scope.append] using congrArg (SourceBoundSnapshots.Retained.plain .absent) kept
  | handler rest next ih =>
      obtain ⟨requests, remaining⟩ := Bool.and_eq_true_iff.mp ready
      obtain ⟨joined, valid, kept⟩ := ih remaining
      refine ⟨.handler joined, ⟨?_, valid⟩, ?_⟩
      · change checkRequirements ((scopeOf rest).append (tailScope.append outsideScope)) _ = true at requests
        simpa only [scopeOf, scope_append_assoc] using requests
      · exact congrArg SourceBoundSnapshots.Retained.handler kept
  | cell next ih =>
      obtain ⟨joined, valid, kept⟩ := ih ready
      exact ⟨.cell joined, valid, congrArg SourceBoundSnapshots.Retained.cell kept⟩
  | cleanup rest required footprint declared next ih =>
      obtain ⟨requests, remaining⟩ := Bool.and_eq_true_iff.mp ready
      obtain ⟨joined, valid, kept⟩ := ih remaining
      refine ⟨.cleanup (.operations required footprint declared) joined, ⟨?_, valid⟩, ?_⟩
      · change checkRequirements (.running ((scopeOf rest).append (tailScope.append outsideScope))) _ = true at requests
        simpa only [Code.Valid, scopeOf, scope_append_assoc] using requests
      · exact congrArg (SourceBoundSnapshots.Retained.cleanup .absent) kept
  | running next ih =>
      obtain ⟨joined, valid, kept⟩ := ih ready
      exact ⟨.running joined, valid, congrArg SourceBoundSnapshots.Retained.running kept⟩
  | live rest saved next ihSaved ih =>
      obtain ⟨inside, remaining⟩ := Bool.and_eq_true_iff.mp ready
      obtain ⟨joined, valid, kept⟩ := ih remaining
      refine ⟨.live (.operations saved) joined, ⟨?_, valid⟩, ?_⟩
      · change saved.check ((scopeOf rest).append (tailScope.append outsideScope)) = true at inside
        simpa only [Retained.Valid, scopeOf, scope_append_assoc] using inside
      · exact congrArg (SourceBoundSnapshots.Retained.live (.absent _)) kept
  | spent next ih =>
      obtain ⟨joined, valid, kept⟩ := ih ready
      exact ⟨.spent joined, valid, congrArg SourceBoundSnapshots.Retained.spent kept⟩

/-- Join the actual input annotations. The result's persistent snapshot is
exactly the existing snapshot append, including saved and callback branches. -/
theorem retained_append_retaining {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {outsideHints : Hints outsideScope} {first : Forest firstHints} {second : Forest secondHints} {outside : Forest outsideHints}
    (inside : Retained world first (second.append outside)) (tail : Retained world second outside)
    (ready : inside.Valid outward actions phases) (tailReady : tail.Valid outward actions phases) :
    ∃ annotation : Retained world (first.append second) outside, annotation.Valid outward actions phases ∧
      SourceBoundSnapshots.Retained.ofCapability annotation =
        (SourceBoundSnapshots.Retained.ofCapability inside).append (SourceBoundSnapshots.Retained.ofCapability tail) := by
  induction first with
  | nil => cases inside with | operations interfaces => cases interfaces; exact ⟨tail, tailReady, rfl⟩
  | plain plan rest ih => cases inside with
    | operations interfaces => exact prepend_interfaces_retaining interfaces tail ready tailReady
    | plain code next =>
        obtain ⟨joined, valid, kept⟩ := ih next ready.2
        obtain ⟨code, codeReady, codeKept⟩ := (code_assoc_bounds rest second outside _).mpr ⟨code, ready.1, rfl⟩
        refine ⟨.plain code joined, ⟨codeReady, valid⟩, ?_⟩
        simp only [SourceBoundSnapshots.Retained.ofCapability, SourceBoundSnapshots.Retained.append, codeKept, kept, Forest.append, Hints.append, SourceDependencyCapture.Scope.append]
  | handler rest ih => cases inside with
    | operations interfaces => exact prepend_interfaces_retaining interfaces tail ready tailReady
    | handler next =>
        obtain ⟨joined, valid, kept⟩ := ih next ready.2
        refine ⟨.handler joined, ⟨?_, valid⟩, congrArg SourceBoundSnapshots.Retained.handler kept⟩
        simpa only [scope_append_assoc] using ready.1
  | cell rest ih => cases inside with
    | operations interfaces => exact prepend_interfaces_retaining interfaces tail ready tailReady
    | cell next =>
        obtain ⟨joined, valid, kept⟩ := ih next ready
        exact ⟨.cell joined, valid, congrArg SourceBoundSnapshots.Retained.cell kept⟩
  | cleanup plan rest ih => cases inside with
    | operations interfaces => exact prepend_interfaces_retaining interfaces tail ready tailReady
    | cleanup code next =>
        obtain ⟨joined, valid, kept⟩ := ih next ready.2
        obtain ⟨code, codeReady, codeKept⟩ := (running_code_assoc_bounds rest second outside _).mpr ⟨code, ready.1, rfl⟩
        refine ⟨.cleanup code joined, ⟨codeReady, valid⟩, ?_⟩
        simp only [SourceBoundSnapshots.Retained.ofCapability, SourceBoundSnapshots.Retained.append, codeKept, kept, Forest.append, Hints.append, SourceDependencyCapture.Scope.append]
  | running rest ih => cases inside with
    | operations interfaces => exact prepend_interfaces_retaining interfaces tail ready tailReady
    | running next =>
        obtain ⟨joined, valid, kept⟩ := ih next ready
        exact ⟨.running joined, valid, congrArg SourceBoundSnapshots.Retained.running kept⟩
  | live saved rest ihSaved ih => cases inside with
    | operations interfaces => exact prepend_interfaces_retaining interfaces tail ready tailReady
    | live dormant next =>
        obtain ⟨joined, valid, kept⟩ := ih next ready.2
        obtain ⟨dormant, dormantReady, dormantKept⟩ := (retained_assoc_bounds rest second outside _).mpr ⟨dormant, ready.1, rfl⟩
        refine ⟨.live dormant joined, ⟨dormantReady, valid⟩, ?_⟩
        simp only [SourceBoundSnapshots.Retained.ofCapability, SourceBoundSnapshots.Retained.append, dormantKept, kept, Forest.append, Hints.append, SourceDependencyCapture.Scope.append]
  | spent rest ih => cases inside with
    | operations interfaces => exact prepend_interfaces_retaining interfaces tail ready tailReady
    | spent next =>
        obtain ⟨joined, valid, kept⟩ := ih next ready
        exact ⟨.spent joined, valid, congrArg SourceBoundSnapshots.Retained.spent kept⟩

end Ash.OneShot.SourceScheduledCapabilityAnnotations

#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.code_assoc_bounds
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.running_code_assoc_bounds
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.retained_assoc_bounds
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.prepend_interfaces_retaining
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.retained_append_retaining
