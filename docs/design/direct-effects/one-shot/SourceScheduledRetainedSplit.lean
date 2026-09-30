import SourceScheduledRetainedRecomposition

/-! Split actual retained annotations without changing persistent metadata.
The existing source-directed split is strengthened with exact snapshot
recomposition, reusing interface splitting and the bound-preserving associativity laws. -/
namespace Ash.OneShot.SourceBoundSnapshots
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)

theorem Retained.absent_append (first : Forest firstHints) (second : Forest secondHints) :
    (Retained.absent first (world := world)).append (Retained.absent second) = Retained.absent (first.append second) := by
  induction first <;> simp_all only [Retained.absent, Retained.append, Forest.append, Hints.append, SourceDependencyCapture.Scope.append]

end Ash.OneShot.SourceBoundSnapshots

namespace Ash.OneShot.SourceScheduledCapabilityAnnotations
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledRetainedInterfaces (Interfaces)
open SourceDependencyChecks (scope_append_assoc)
open SourceBoundSnapshots.Retained (ofCapability)

variable [DeclarationPolicy]

private theorem operations_split_retaining (first : Forest firstHints) (second : Forest secondHints)
    {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
    (source : Interfaces world (first.append second)) (ready : source.check outsideScope = true) :
    ∃ inside : Retained world first (second.append outside), ∃ tail : Retained world second outside,
      inside.Valid outward actions phases ∧ tail.Valid outward actions phases ∧
      (ofCapability inside).append (ofCapability tail) = ofCapability (Retained.operations (outside := outside) source) := by
  rw [← source.splitAt_append first second, Interfaces.check_append] at ready
  exact ⟨.operations (source.splitAt first second).1, .operations (source.splitAt first second).2,
    (Bool.and_eq_true_iff.mp ready).1, (Bool.and_eq_true_iff.mp ready).2,
    SourceBoundSnapshots.Retained.absent_append first second⟩

/-- Both pieces come from the original source, and their metadata joins to its
exact original snapshot. No successor-validity or replacement-bound premise is used. -/
theorem retained_split_retaining {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {outsideHints : Hints outsideScope} (first : Forest firstHints) (second : Forest secondHints)
    {outside : Forest outsideHints}
    (source : Retained world (first.append second) outside) (ready : source.Valid outward actions phases) :
    ∃ inside : Retained world first (second.append outside), ∃ tail : Retained world second outside,
      inside.Valid outward actions phases ∧ tail.Valid outward actions phases ∧
      (ofCapability inside).append (ofCapability tail) = ofCapability source := by
  induction first with
  | nil => exact ⟨.operations .nil, source, rfl, ready, rfl⟩
  | plain plan rest ih => cases source with
    | operations interfaces => exact operations_split_retaining _ _ interfaces ready
    | plain code next =>
        obtain ⟨inside, tail, insideReady, tailReady, kept⟩ := ih next ready.2
        obtain ⟨code, codeReady, codeKept⟩ := (code_assoc_bounds rest second outside _).mp ⟨code, ready.1, rfl⟩
        refine ⟨.plain code inside, tail, ⟨codeReady, insideReady⟩, tailReady, ?_⟩
        simp only [ofCapability, SourceBoundSnapshots.Retained.append, codeKept, kept,
          Forest.append, Hints.append, SourceDependencyCapture.Scope.append]
  | handler rest ih => cases source with
    | operations interfaces => exact operations_split_retaining _ _ interfaces ready
    | handler next =>
        obtain ⟨inside, tail, insideReady, tailReady, kept⟩ := ih next ready.2
        refine ⟨.handler inside, tail, ⟨?_, insideReady⟩, tailReady, congrArg SourceBoundSnapshots.Retained.handler kept⟩
        simpa only [scope_append_assoc] using ready.1
  | cell rest ih => cases source with
    | operations interfaces => exact operations_split_retaining _ _ interfaces ready
    | cell next =>
        obtain ⟨inside, tail, insideReady, tailReady, kept⟩ := ih next ready
        exact ⟨.cell inside, tail, insideReady, tailReady, congrArg SourceBoundSnapshots.Retained.cell kept⟩
  | cleanup plan rest ih => cases source with
    | operations interfaces => exact operations_split_retaining _ _ interfaces ready
    | cleanup code next =>
        obtain ⟨inside, tail, insideReady, tailReady, kept⟩ := ih next ready.2
        obtain ⟨code, codeReady, codeKept⟩ := (running_code_assoc_bounds rest second outside _).mp ⟨code, ready.1, rfl⟩
        refine ⟨.cleanup code inside, tail, ⟨codeReady, insideReady⟩, tailReady, ?_⟩
        simp only [ofCapability, SourceBoundSnapshots.Retained.append, codeKept, kept,
          Forest.append, Hints.append, SourceDependencyCapture.Scope.append]
  | running rest ih => cases source with
    | operations interfaces => exact operations_split_retaining _ _ interfaces ready
    | running next =>
        obtain ⟨inside, tail, insideReady, tailReady, kept⟩ := ih next ready
        exact ⟨.running inside, tail, insideReady, tailReady, congrArg SourceBoundSnapshots.Retained.running kept⟩
  | live saved rest ihSaved ih => cases source with
    | operations interfaces => exact operations_split_retaining _ _ interfaces ready
    | live dormant next =>
        obtain ⟨inside, tail, insideReady, tailReady, kept⟩ := ih next ready.2
        obtain ⟨dormant, dormantReady, dormantKept⟩ := (retained_assoc_bounds rest second outside _).mp ⟨dormant, ready.1, rfl⟩
        refine ⟨.live dormant inside, tail, ⟨dormantReady, insideReady⟩, tailReady, ?_⟩
        simp only [ofCapability, SourceBoundSnapshots.Retained.append, dormantKept, kept,
          Forest.append, Hints.append, SourceDependencyCapture.Scope.append]
  | spent rest ih => cases source with
    | operations interfaces => exact operations_split_retaining _ _ interfaces ready
    | spent next =>
        obtain ⟨inside, tail, insideReady, tailReady, kept⟩ := ih next ready
        exact ⟨.spent inside, tail, insideReady, tailReady, congrArg SourceBoundSnapshots.Retained.spent kept⟩

/-- Removing the empty suffix changes only the receiving index. -/
theorem retained_receiver_nil_bounds {forest : Forest hints} (outside : Forest outsideHints)
    (bounds : SourceBoundSnapshots.Retained world forest) :
    (∃ annotation : Retained world forest (outside.append .nil),
      annotation.Valid outward actions phases ∧ ofCapability annotation = bounds) ↔
    (∃ annotation : Retained world forest outside,
      annotation.Valid outward actions phases ∧ ofCapability annotation = bounds) :=
  SourceScheduledRecomposition.predicate_congr (SourceDependencyProjection.scope_append_nil _)
    (SourcePlannedRecomposition.hints_append_nil _) (SourceScheduledRecomposition.forest_append_nil outside)
    (fun receiver => ∃ annotation : Retained world forest receiver,
      annotation.Valid outward actions phases ∧ ofCapability annotation = bounds)

/-- The actual handler cut authenticates the metadata split, including its
ordered saved/waiting boundary. The heterogeneous equation retains the original
whole forest rather than silently replacing it with an existential witness. -/
theorem retained_at_cut_retaining {wholeHints : Hints wholeScope} {savedHints : Hints savedScope}
    {waitingHints : Hints waitingScope} {whole : Forest wholeHints}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (cut : SourceScheduledNeutral.Cut effect operation contract modes whole saved waiting)
    (source : Retained world whole .nil) (ready : source.Valid outward actions phases) :
    ∃ inside : Retained world saved waiting, ∃ tail : Retained world waiting .nil,
      inside.Valid outward actions phases ∧ tail.Valid outward actions phases ∧
      HEq ((ofCapability inside).append (ofCapability tail)) (ofCapability source) := by
  obtain ⟨recomposed, valid, original⟩ :=
    (SourceScheduledRecomposition.predicate_congr cut.erase.reconstruct_scope cut.erase.hints cut.forest
      (fun forest => ∃ annotation : Retained world forest .nil, annotation.Valid outward actions phases ∧
        HEq (ofCapability annotation) (ofCapability source))).mp ⟨source, ready, HEq.rfl⟩
  obtain ⟨inside, tail, insideReady, tailReady, kept⟩ := retained_split_retaining saved waiting recomposed valid
  obtain ⟨inside, valid, same⟩ := (retained_receiver_nil_bounds waiting _).mp ⟨inside, insideReady, rfl⟩
  refine ⟨inside, tail, valid, tailReady, ?_⟩
  exact (heq_of_eq ((congrArg (fun part => part.append (ofCapability tail)) same).trans kept)).trans original

end Ash.OneShot.SourceScheduledCapabilityAnnotations

#print axioms Ash.OneShot.SourceBoundSnapshots.Retained.absent_append
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.retained_split_retaining
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.retained_receiver_nil_bounds
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.retained_at_cut_retaining
