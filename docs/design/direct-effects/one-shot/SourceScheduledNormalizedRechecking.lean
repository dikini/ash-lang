import SourceScheduledSourceNormalization
import SourceScheduledSourceRechecking
import SourceBoundCapture
import SourceBoundDisposal

/-! Normalize at the original receiver before applying structural rechecking.
Compilation then retains the canonical bound spine exactly, while every
recorded-bound lookup remains equal to the original source's observation. -/
namespace Ash.OneShot.SourceScheduledCapabilityAnnotations
open SourceDeclarationPlans (ClausePlans)
open SourcePlanBounds (ofCode)

variable [declarations : DeclarationPolicy]

noncomputable def Code.normalized
    (source : Code world plan forest)
    (legacy : ∀ {clauses families required} {plans : ClausePlans clauses families},
      SourcePlannedRecipeDeclarations.Declarations required plans → declarations.accepts required plans)
    (ready : source.Valid outward actions phases) : Code world plan forest :=
  Classical.choose (Code.normalize legacy ready)

theorem Code.normalized_valid
    (source : Code world plan forest)
    (legacy : ∀ {clauses families required} {plans : ClausePlans clauses families},
      SourcePlannedRecipeDeclarations.Declarations required plans → declarations.accepts required plans)
    (ready : source.Valid outward actions phases) :
    (source.normalized legacy ready).Valid outward actions phases :=
  (Classical.choose_spec (Code.normalize legacy ready)).1

theorem Code.normalized_bounds
    (source : Code world plan forest)
    (legacy : ∀ {clauses families required} {plans : ClausePlans clauses families},
      SourcePlannedRecipeDeclarations.Declarations required plans → declarations.accepts required plans)
    (ready : source.Valid outward actions phases) :
    ofCode (source.normalized legacy ready) = (ofCode source).normalize :=
  (Classical.choose_spec (Code.normalize legacy ready)).2.1

theorem Code.normalized_expanded
    (source : Code world plan forest)
    (legacy : ∀ {clauses families required} {plans : ClausePlans clauses families},
      SourcePlannedRecipeDeclarations.Declarations required plans → declarations.accepts required plans)
    (ready : source.Valid outward actions phases) :
    (source.normalized legacy ready).Expanded :=
  (Classical.choose_spec (Code.normalize legacy ready)).2.2

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]

/-- The new receiver is checked only by Expression. Normalization is performed
at the old receiver and supplies no successful-target assumption. -/
theorem Code.recheck_normalized
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    (source : Code world plan before) (ready : source.Valid outward actions phases)
    (changed : SourceScheduledSourceRechecking.Expression outward actions phases
      (source.normalized (fun recipes => project (laws.legacyAdmission recipes)) ready) after) :
    ∃ annotation : Code world plan after,
      annotation.Valid outward actions phases ∧
      ofCode annotation = (ofCode source).normalize ∧ annotation.Expanded ∧
      ∀ path operation held,
        (ofCode annotation).lookup path operation held = (ofCode source).lookup path operation held := by
  obtain ⟨compiled, compiledReady, kept⟩ := changed.compile_retaining laws project
    (source.normalized_valid _ ready)
  obtain ⟨annotation, valid, annotationBounds, expanded⟩ :=
    Code.normalize (fun recipes => project (laws.legacyAdmission recipes)) compiledReady
  have compiledBounds := kept.trans (source.normalized_bounds _ ready)
  have normalized := annotationBounds.trans
    ((congrArg SourcePlanBounds.Annotation.normalize compiledBounds).trans (ofCode source).normalize_idempotent)
  exact ⟨annotation, valid, normalized, expanded, fun path operation held =>
    normalized ▸ (ofCode source).normalize_lookup path⟩

end Ash.OneShot.SourceScheduledCapabilityAnnotations

namespace Ash.OneShot.SourceBoundSnapshots

def Snapshot.normalize (source : Snapshot world) : Snapshot world :=
  { source with current := source.current.normalize, pending := source.pending.normalize }

theorem Snapshot.normalize_idempotent (source : Snapshot world) :
    source.normalize.normalize = source.normalize := by
  cases source
  simp only [Snapshot.normalize, SourcePlanBounds.Annotation.normalize_idempotent, Retained.normalize_idempotent]

theorem Retained.normalize_append {first : Retained world front} {second : Retained world tail} :
    (first.append second).normalize = first.normalize.append second.normalize := by
  induction first <;> simp_all only [Retained.append, Retained.normalize] <;> rfl

theorem Retained.normalize_forClosing (source : Retained world forest) :
    source.forClosing.normalize = source.normalize.forClosing := by
  induction source with
  | nil => rfl
  | plain code tail ih | handler tail ih | spent tail ih => exact ih
  | cell tail ih => exact congrArg Retained.cell ih
  | cleanup code tail ih => exact congrArg (Retained.cleanup code.normalize) ih
  | running tail ih => exact congrArg Retained.running ih
  | live saved tail ihSaved ihTail =>
      change (saved.forClosing.append (.running tail.forClosing)).normalize =
        saved.normalize.forClosing.append (.running tail.normalize.forClosing)
      exact (Retained.normalize_append (first := saved.forClosing) (second := .running tail.forClosing)).trans
        ((congrArg (fun bounds => bounds.append (Retained.running tail.forClosing.normalize)) ihSaved).trans
          (congrArg (fun bounds => saved.normalize.forClosing.append (Retained.running bounds)) ihTail))

theorem Snapshot.normalize_value {scope : SourceDependencyCapture.Scope}
    {hints : SourceContextualHints.Hints scope}
    {retained : SourceRetainedPlans.Forest hints} (source : Retained world retained) :
    (Snapshot.value source).normalize = Snapshot.value source.normalize := rfl

/-- Canonicalization commutes with the existing capture metadata movement. -/
theorem Captured.normalize {before after : Snapshot world} (moved : Captured owner before after) :
    Captured owner before.normalize after.normalize := by
  cases moved with
  | cut before after saved tail =>
      simpa only [Snapshot.normalize, Retained.normalize_append, Retained.normalize] using
        (Captured.cut (owner := owner) before.normalize after.normalize saved.normalize tail.normalize)

/-- Resumption still uses the same cut, saved forest and spent owner. -/
theorem Resumed.normalize {before after : Snapshot world} (moved : Resumed owner before after) :
    Resumed owner before.normalize after.normalize := by
  cases moved with
  | cut current front saved tail =>
      dsimp only [Snapshot.normalize, Snapshot.value]
      simp only [Retained.normalize_append, Retained.normalize]
      exact Resumed.cut (owner := owner) current.normalize front.normalize saved.normalize tail.normalize

/-- Closing normalization retains the original ordered callback traversal. -/
theorem Discarded.normalize {before after : Snapshot world} (moved : Discarded owner before after) :
    Discarded owner before.normalize after.normalize := by
  cases moved with
  | cut current front saved tail =>
      dsimp only [Snapshot.normalize, Snapshot.value]
      simp only [Retained.normalize_append, Retained.normalize_forClosing, Retained.normalize]
      exact Discarded.cut (owner := owner) current.normalize front.normalize saved.normalize tail.normalize

variable [declarations : SourceScheduledCapabilityAnnotations.DeclarationPolicy]

theorem Snapshot.Admitted.normalize {source : Snapshot world} (ready : source.Admitted) :
    source.normalize.Admitted := ⟨ready.1.normalize, ready.2.normalize⟩

/-- Prepare current and retained source against one actual normalized snapshot.
Original declaration admission and exact source/snapshot alignment supply all
metadata premises; no target source or replacement snapshot is an input. -/
theorem Snapshot.normalize_source
    (snapshot : Snapshot world) (admitted : snapshot.Admitted)
    (legacy : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      SourcePlannedRecipeDeclarations.Declarations required plans → declarations.accepts required plans)
    (current : SourceScheduledCapabilityAnnotations.Code world snapshot.plan snapshot.forest)
    (pending : SourceScheduledCapabilityAnnotations.Retained world snapshot.forest SourceRetainedPlans.Forest.nil)
    (currentReady : current.Valid outward actions phases) (pendingReady : pending.Valid outward actions phases)
    (currentOrigin : SourcePlanBounds.ofCode current = snapshot.current)
    (pendingOrigin : Retained.ofCapability pending = snapshot.pending) :
    ∃ code : SourceScheduledCapabilityAnnotations.Code world snapshot.plan snapshot.forest,
      ∃ retained : SourceScheduledCapabilityAnnotations.Retained world snapshot.forest SourceRetainedPlans.Forest.nil,
        code.Valid outward actions phases ∧ retained.Valid outward actions phases ∧
        SourcePlanBounds.ofCode code = snapshot.normalize.current ∧
        Retained.ofCapability retained = snapshot.normalize.pending ∧ snapshot.normalize.Admitted ∧
        code.Expanded ∧ retained.Expanded := by
  obtain ⟨code, codeReady, codeBounds, codeExpanded⟩ := SourceScheduledCapabilityAnnotations.Code.normalize legacy currentReady
  obtain ⟨retained, retainedReady, retainedBounds, retainedExpanded⟩ := SourceScheduledCapabilityAnnotations.Retained.normalize legacy pendingReady
  exact ⟨code, retained, codeReady, retainedReady,
    codeBounds.trans (congrArg SourcePlanBounds.Annotation.normalize currentOrigin),
    retainedBounds.trans (congrArg Retained.normalize pendingOrigin), admitted.normalize, codeExpanded, retainedExpanded⟩

end Ash.OneShot.SourceBoundSnapshots

#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.normalized_valid
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.normalized_bounds
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.recheck_normalized
#print axioms Ash.OneShot.SourceBoundSnapshots.Snapshot.Admitted.normalize

#print axioms Ash.OneShot.SourceBoundSnapshots.Retained.normalize_append
#print axioms Ash.OneShot.SourceBoundSnapshots.Retained.normalize_forClosing
#print axioms Ash.OneShot.SourceBoundSnapshots.Snapshot.normalize_value
#print axioms Ash.OneShot.SourceBoundSnapshots.Captured.normalize
#print axioms Ash.OneShot.SourceBoundSnapshots.Resumed.normalize
#print axioms Ash.OneShot.SourceBoundSnapshots.Discarded.normalize
#print axioms Ash.OneShot.SourceBoundSnapshots.Snapshot.normalize_source

#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.normalized_expanded

#print axioms Ash.OneShot.SourceBoundSnapshots.Snapshot.normalize_idempotent
