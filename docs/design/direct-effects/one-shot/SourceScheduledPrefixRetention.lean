import SourceScheduledPrefixClosing

/-! Exact canonical metadata for partial caller closing. Split the original
snapshot at the same source boundary, close only its prefix, and retain its
suffix with the optional disposal running marker. -/
namespace Ash.OneShot.SourceBoundSnapshots
open SourceDependencyCapture (Scope)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDependencyChecks (scope_append_assoc)
open SourcePlannedRecomposition (hints_append_assoc)
open SourceScheduledRecomposition (forest_append_assoc)

private theorem lift_bounds_heq {shape : Scope → Scope}
    {decorate : ∀ {scope}, Hints scope → Hints (shape scope)}
    {frame : ∀ {scope} {hints : Hints scope}, Forest hints → Forest (decorate hints)}
    {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {first : Forest firstHints} {second : Forest secondHints}
    {before : Retained world first} {after : Retained world second}
    (sameScope : firstScope = secondScope) (sameHints : HEq firstHints secondHints)
    (sameForest : HEq first second) (sameBounds : HEq before after)
    (lift : ∀ {scope} {hints : Hints scope} {forest : Forest hints},
      Retained world forest → Retained world (frame forest)) :
    HEq (lift before) (lift after) := by
  cases sameScope
  cases sameHints
  cases sameForest
  cases sameBounds
  rfl

/-- Snapshot concatenation follows the already proved forest associativity.
Every recorded code bound is carried unchanged; no source is rechecked here. -/
theorem Retained.append_assoc {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {thirdHints : Hints thirdScope} {first : Forest firstHints} {second : Forest secondHints}
    {third : Forest thirdHints} (before : Retained world first) (middle : Retained world second)
    (after : Retained world third) :
    HEq ((before.append middle).append after) (before.append (middle.append after)) := by
  induction before with
  | nil => rfl
  | plain code rest ih =>
      exact lift_bounds_heq (decorate := fun hints => .plain hints)
        (frame := fun forest => .plain _ forest) (scope_append_assoc _ _ _) (hints_append_assoc _ _ _)
        (forest_append_assoc _ _ _) ih (fun bounds => .plain code bounds)
  | handler rest ih =>
      exact lift_bounds_heq (decorate := fun hints => .handler _ hints)
        (frame := fun forest => .handler forest) (scope_append_assoc _ _ _) (hints_append_assoc _ _ _)
        (forest_append_assoc _ _ _) ih (fun bounds => .handler bounds)
  | cell rest ih =>
      exact lift_bounds_heq (decorate := fun hints => .cell hints)
        (frame := fun forest => .cell forest) (scope_append_assoc _ _ _) (hints_append_assoc _ _ _)
        (forest_append_assoc _ _ _) ih (fun bounds => .cell bounds)
  | cleanup code rest ih =>
      exact lift_bounds_heq (decorate := fun hints => .cleanup hints)
        (frame := fun forest => .cleanup _ forest) (scope_append_assoc _ _ _) (hints_append_assoc _ _ _)
        (forest_append_assoc _ _ _) ih (fun bounds => .cleanup code bounds)
  | running rest ih =>
      exact lift_bounds_heq (decorate := fun hints => .running hints)
        (frame := fun forest => .running forest) (scope_append_assoc _ _ _) (hints_append_assoc _ _ _)
        (forest_append_assoc _ _ _) ih (fun bounds => .running bounds)
  | live saved rest ihSaved ih =>
      exact lift_bounds_heq (decorate := fun hints => .live _ hints)
        (frame := fun forest => .live _ forest) (scope_append_assoc _ _ _) (hints_append_assoc _ _ _)
        (forest_append_assoc _ _ _) ih (fun bounds => .live saved bounds)
  | spent rest ih =>
      exact lift_bounds_heq (decorate := fun hints => .spent hints)
        (frame := fun forest => .spent forest) (scope_append_assoc _ _ _) (hints_append_assoc _ _ _)
        (forest_append_assoc _ _ _) ih (fun bounds => .spent bounds)

/-- A partial closing boundary either retains the exact original suffix or
wraps exactly that suffix in the disposal running marker. -/
inductive BoundaryBounds {source : Forest sourceHints} (original : Retained world source) :
    {targetScope : Scope} → {targetHints : Hints targetScope} →
    {target : Forest targetHints} → Retained world target → Prop where
  | same : BoundaryBounds original original
  | protect : BoundaryBounds original (.running original)

/-- Boundary protection preserves admission of the exact original suffix. -/
theorem BoundaryBounds.admitted [SourceScheduledCapabilityAnnotations.DeclarationPolicy]
    {source : Forest sourceHints} {target : Forest targetHints}
    {original : Retained world source} {result : Retained world target}
    (kept : BoundaryBounds original result) (ready : original.Admitted) : result.Admitted := by
  cases kept with
  | same => exact ready
  | protect => exact .running ready

end Ash.OneShot.SourceBoundSnapshots

namespace Ash.OneShot.SourceScheduledSourceRechecking
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledCapabilityAnnotations (Retained DeclarationPolicy DeclarationLaws)
open SourceBoundSnapshots (BoundaryBounds)
open SourceBoundSnapshots.Retained (ofCapability)

variable [declarations : DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]

/-- Compile from original children while retaining the canonical split/close/
append snapshot. Existing child compilers and ordered recomposition do the work;
the only induction is over the structural prefix-closing derivation. -/
theorem PrefixClosing.compile_retaining
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {prefixHints : Hints prefixScope} {suffixHints : Hints suffixScope}
    {targetHints : Hints targetScope} {leading : Forest prefixHints} {suffix : Forest suffixHints}
    {target : Forest targetHints} {source : Retained world (leading.append suffix) outside}
    (closing : PrefixClosing outward actions phases (suffix := suffix) leading source target next)
    (ready : source.Valid outward actions phases) :
    ∃ annotation : Retained world (leading.forClosing.append target) next,
      ∃ boundary : SourceBoundSnapshots.Retained world target,
      annotation.Valid outward actions phases ∧
      BoundaryBounds ((ofCapability source).splitAt leading suffix).2 boundary ∧
      ofCapability annotation =
        ((ofCapability source).splitAt leading suffix).1.forClosing.append boundary := by
  induction closing with
  | nil changed =>
      obtain ⟨annotation, valid, kept⟩ := changed.compile_retaining laws project ready
      exact ⟨annotation, _, valid, .same, kept⟩
  | protect changed =>
      obtain ⟨annotation, valid, kept⟩ := changed.compile_retaining laws project ready
      exact ⟨.running annotation, _, valid, .protect, congrArg SourceBoundSnapshots.Retained.running kept⟩
  | plain tail ih => exact ih ready.2
  | handler tail ih => exact ih ready.2
  | spent tail ih => exact ih ready
  | cell tail ih =>
      obtain ⟨annotation, boundary, valid, origin, kept⟩ := ih ready
      exact ⟨.cell annotation, boundary, valid, origin, congrArg SourceBoundSnapshots.Retained.cell kept⟩
  | running tail ih =>
      obtain ⟨annotation, boundary, valid, origin, kept⟩ := ih ready
      exact ⟨.running annotation, boundary, valid, origin, congrArg SourceBoundSnapshots.Retained.running kept⟩
  | cleanup callback tail ih =>
      obtain ⟨code, codeReady, codeKept⟩ := callback.compile_retaining laws project ready.1
      obtain ⟨annotation, boundary, valid, origin, kept⟩ := ih ready.2
      refine ⟨.cleanup code annotation, boundary, ⟨codeReady, valid⟩, origin, ?_⟩
      simp only [ofCapability, SourceBoundSnapshots.Retained.splitAt, SourceBoundSnapshots.Retained.forClosing,
        SourceBoundSnapshots.Retained.append, codeKept, kept]
      rfl
  | live dormant closing ih =>
      rename_i owner savedHints saved frontHints front suffixHints suffix target next inside tail
      obtain ⟨dormantSource, dormantReady, dormantKept⟩ := dormant.compile_retaining laws project ready.1
      obtain ⟨annotation, boundary, valid, origin, kept⟩ := ih ready.2
      let joined := dormantSource.joinSource (.running annotation)
      have joinedReady := (dormantSource.joinSource_valid (.running annotation)).mpr ⟨dormantReady, valid⟩
      have joinedKept := dormantSource.joinSource_bounds (.running annotation)
      let originalBounds := ((ofCapability (.live (owner := owner) inside tail)).splitAt (.live (owner := owner) saved front) suffix).1.forClosing.append boundary
      have joinedOrigin : HEq (ofCapability joined) originalBounds := by
        rw [joinedKept]
        change HEq ((ofCapability dormantSource).append (.running (ofCapability annotation))) originalBounds
        rw [dormantKept, kept]
        exact (SourceBoundSnapshots.Retained.append_assoc (ofCapability inside).forClosing
          (.running ((ofCapability tail).splitAt front suffix).1.forClosing) boundary).symm
      obtain ⟨result, resultReady, resultOrigin⟩ :=
        (SourceScheduledRecomposition.predicate_congr
          (SourceDependencyChecks.scope_append_assoc _ _ _)
          (SourcePlannedRecomposition.hints_append_assoc _ _ _)
          (SourceScheduledRecomposition.forest_append_assoc saved.forClosing (.running front.forClosing) target)
          (fun forest => ∃ result : Retained _ forest next,
            result.Valid outward actions phases ∧ HEq (ofCapability result) originalBounds)).mpr
          ⟨joined, joinedReady, joinedOrigin⟩
      exact ⟨result, boundary, resultReady, origin, eq_of_heq resultOrigin⟩

/-- Admission follows from the original canonical split and exact output
identity. No independently admitted successor metadata is required. -/
theorem PrefixClosing.compile_retaining_admitted
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {prefixHints : Hints prefixScope} {suffixHints : Hints suffixScope}
    {targetHints : Hints targetScope} {leading : Forest prefixHints} {suffix : Forest suffixHints}
    {target : Forest targetHints} {source : Retained world (leading.append suffix) outside}
    (closing : PrefixClosing outward actions phases (suffix := suffix) leading source target next)
    (ready : source.Valid outward actions phases) (admitted : (ofCapability source).Admitted) :
    ∃ annotation : Retained world (leading.forClosing.append target) next,
      ∃ boundary : SourceBoundSnapshots.Retained world target,
      annotation.Valid outward actions phases ∧
      BoundaryBounds ((ofCapability source).splitAt leading suffix).2 boundary ∧
      ofCapability annotation =
        ((ofCapability source).splitAt leading suffix).1.forClosing.append boundary ∧
      (ofCapability annotation).Admitted := by
  obtain ⟨annotation, boundary, valid, origin, kept⟩ := closing.compile_retaining laws project ready
  have splitReady : (((ofCapability source).splitAt leading suffix).1.append
      ((ofCapability source).splitAt leading suffix).2).Admitted := by
    rw [SourceBoundSnapshots.Retained.splitAt_append]
    exact admitted
  have parts := splitReady.of_append
  exact ⟨annotation, boundary, valid, origin, kept,
    kept.symm ▸ parts.1.forClosing.append (origin.admitted parts.2)⟩

end Ash.OneShot.SourceScheduledSourceRechecking

#print axioms Ash.OneShot.SourceBoundSnapshots.Retained.append_assoc
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.PrefixClosing.compile_retaining

#print axioms Ash.OneShot.SourceBoundSnapshots.BoundaryBounds.admitted
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.PrefixClosing.compile_retaining_admitted
