import SourceScheduledStructuralClosing

/-! Pre-capture source evidence at an actual handler cut. The original split
carries its original validity and exact snapshot origin. Disposal reuses the closing annotation validated at that original request.
Its metadata must be the canonical close of the actual saved snapshot. -/
namespace Ash.OneShot.SourceScheduledCapabilityAnnotations
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledSourceRechecking (Closing)
open SourceBoundSnapshots.Retained (ofCapability)

/-- Source annotations for both pieces before capture. The fixed cut and exact
metadata equation authenticate their saved/waiting boundary. Closing retains
original-request validity and exact canonical metadata, before owner allocation. -/
structure CaptureSource [DeclarationPolicy] (outward : List Instance) (actions : Syntax.UsageTickets)
    (phases : OwnerPhaseTransitions.Phases)
    {wholeHints : Hints wholeScope} {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {whole : Forest wholeHints} {saved : Forest savedHints} {waiting : Forest waitingHints}
    (_cut : SourceScheduledNeutral.Cut effect operation contract modes whole saved waiting)
    (source : Retained world whole .nil) (rights : Syntax.OneShotRights) where
  sourceReady : source.Valid outward actions phases
  guarded : SourceDependencyCapture.CaptureGuard outward wholeScope effect operation
  inside : Retained world saved waiting
  after : Retained world waiting .nil
  insideReady : inside.Valid outward actions phases
  tailReady : after.Valid outward actions phases
  original : HEq ((ofCapability inside).append (ofCapability after)) (ofCapability source)
  closing : rights.dispose = true →
    ∃ annotation : Retained world saved.forClosing (.running waiting),
      annotation.Valid outward actions phases ∧ ofCapability annotation = (ofCapability inside).forClosing

variable [DeclarationPolicy]

/-- A source without disposal has no closing obligation. The existing source
split theorem constructs its pieces; no new split or recomposition proof is used. -/
noncomputable def CaptureSource.without_disposal
    {wholeHints : Hints wholeScope} {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {whole : Forest wholeHints} {saved : Forest savedHints} {waiting : Forest waitingHints}
    (cut : SourceScheduledNeutral.Cut effect operation contract modes whole saved waiting)
    (source : Retained world whole .nil) (ready : source.Valid outward actions phases)
    (guarded : SourceDependencyCapture.CaptureGuard outward wholeScope effect operation)
    (denied : rights.dispose = false) : CaptureSource outward actions phases cut source rights :=
  Classical.choice (by
    obtain ⟨inside, after, insideReady, tailReady, original⟩ := retained_at_cut_retaining cut source ready
    exact ⟨⟨ready, guarded, inside, after, insideReady, tailReady, original,
      fun permission => False.elim (Bool.noConfusion (denied.symm.trans permission))⟩⟩)

/-- Derive both valid source pieces from the original whole source. The
remaining source-admission condition compares metadata only: the closing
annotation of the current request is the canonical close of its actual saved
snapshot. It supplies no validity or rechecking proof for the selected clause. -/
theorem CaptureSource.of_selected
    {wholeHints : Hints wholeScope} {whole : Forest wholeHints}
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (cut : SourceScheduledNeutral.Cut effect operation offered modes whole saved waiting)
    (bounded : offered.dispose = true →
      SourceDependencyOwners.PendingWithin world (SourceDependencyOwners.owners savedScope) savedScope)
    (originalClosing : offered.dispose = true → Retained world saved.forClosing (.running waiting))
    (requested : (SourceScheduledCapabilityAnnotations.Code.selected cut bounded originalClosing).Valid
      outward actions phases)
    (source : Retained world whole .nil) (ready : source.Valid outward actions phases)
    (savedBounds : SourceBoundSnapshots.Retained world saved)
    (waitingBounds : SourceBoundSnapshots.Retained world waiting)
    (original : HEq (savedBounds.append waitingBounds) (ofCapability source))
    (permits : rights.dispose = true → offered.dispose = true)
    (canonical : ∀ permission, ofCapability (originalClosing (permits permission)) = savedBounds.forClosing)
    : ∃ captured : CaptureSource outward actions phases cut source rights,
      ofCapability captured.inside = savedBounds ∧ ofCapability captured.after = waitingBounds := by
  obtain ⟨inside, after, insideReady, afterReady, recomposed⟩ :=
    retained_at_cut_retaining cut source ready
  have joined : (ofCapability inside).append (ofCapability after) = savedBounds.append waitingBounds :=
    eq_of_heq (recomposed.trans original.symm)
  have pieces := congrArg (fun bounds => bounds.splitAt saved waiting) joined
  simp only [SourceBoundSnapshots.Retained.splitAt_join, Prod.mk.injEq] at pieces
  refine ⟨⟨ready, SourceDependencyCapture.check_capture_iff.mp requested.1,
    inside, after, insideReady, afterReady, recomposed, ?_⟩, pieces⟩
  intro permission
  exact ⟨originalClosing (permits permission), requested.2 (permits permission),
    (canonical permission).trans (congrArg SourceBoundSnapshots.Retained.forClosing pieces.1).symm⟩

end Ash.OneShot.SourceScheduledCapabilityAnnotations

#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.CaptureSource.without_disposal

#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.CaptureSource.of_selected
