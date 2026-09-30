import SourceScheduledNeutralRetained

/-! Realize neutral movement at the supplied runtime metadata. The relation
fixes every original annotation, so the result matches the actual destination
rather than a separately generated neutral destination. -/
namespace Ash.OneShot.SourceBoundSnapshots
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)

/-- Neutral movement cannot introduce continuation bounds into an
operation-only forest. This is a property of the structural relation. -/
theorem Retained.Neutral.eq_absent
    {beforeHints : Hints beforeScope} {afterHints : Hints afterScope}
    {before : Forest beforeHints} {after : Forest afterHints}
    {first : Retained world before} {last : Retained world after}
    (changed : Neutral world first last) (origin : first = Retained.absent before) :
    last = Retained.absent after := by
  induction changed with
  | refl => exact origin
  | extra _ ih | completion _ ih | history _ ih =>
      simp only [Retained.absent]
      rw [ih origin]
  | plain _ ih | handler _ ih | cell _ ih | cleanup _ ih | running _ ih | spent _ ih =>
      simp only [Retained.absent] at origin ⊢
      cases origin
      rw [ih rfl]
  | live _ ih =>
      simp only [Retained.absent] at origin ⊢
      cases origin
      rw [ih rfl]

end Ash.OneShot.SourceBoundSnapshots

#print axioms Ash.OneShot.SourceBoundSnapshots.Retained.Neutral.eq_absent

namespace Ash.OneShot.SourceScheduledCapabilityAnnotations
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (ClausePlans)
open SourceScheduledNeutral (Expansion)
open SourceBoundSnapshots.Retained (ofCapability Neutral)

variable [declarations : DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]

omit admission certification [SourceScheduledChecks.DeclarationProjection admission certification] in
private theorem operations_actual
    {beforeHints : Hints beforeScope} {afterHints : Hints afterScope}
    {before : Forest beforeHints} {after : Forest afterHints}
    {first : SourceBoundSnapshots.Retained world before} {last : SourceBoundSnapshots.Retained world after}
    (changed : Neutral world first last)
    {outsideHints : Hints outsideScope} {nextHints : Hints nextScope}
    {outside : Forest outsideHints} {next : Forest nextHints}
    (receiver : Expansion outside next)
    (interfaces : SourceScheduledRetainedInterfaces.Interfaces world before)
    (ready : interfaces.check outsideScope = true)
    (origin : ofCapability (Retained.operations interfaces (outside := outside)) = first) :
    ∃ target : Retained world after next, target.Valid outward actions phases ∧ ofCapability target = last := by
  obtain ⟨target, kept⟩ := interfaces.expand_neutral changed.forest
  refine ⟨.operations target, ?_, (changed.eq_absent origin.symm).symm⟩
  change target.check nextScope = true
  rw [kept next, ← interfaces.check_neutral receiver]
  exact ready

/-- Reuse receiver and code transport while following the given metadata
movement. No validity premise is supplied for the target source. -/
theorem Retained.expand_neutral_at
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {beforeHints : Hints beforeScope} {afterHints : Hints afterScope}
    {before : Forest beforeHints} {after : Forest afterHints}
    {first : SourceBoundSnapshots.Retained world before} {last : SourceBoundSnapshots.Retained world after}
    (changed : Neutral world first last)
    {outsideHints : Hints outsideScope} {nextHints : Hints nextScope}
    {outside : Forest outsideHints} {next : Forest nextHints}
    (receiver : Expansion outside next)
    (source : Retained world before outside) (ready : source.Valid outward actions phases)
    (origin : ofCapability source = first) :
    ∃ target : Retained world after next, target.Valid outward actions phases ∧ ofCapability target = last := by
  induction changed generalizing outsideScope nextScope with
  | refl =>
      obtain ⟨target, valid, kept⟩ := source.receiver_retaining (neutral_receiver_laws laws project) ready receiver
      exact ⟨target, valid, kept.trans origin⟩
  | extra changed ih =>
      obtain ⟨target, valid, kept⟩ := ih receiver source ready origin
      exact ⟨.plain (.operations [] .pure .pure) target, ⟨rfl, valid⟩, congrArg _ kept⟩
  | completion changed ih =>
      obtain ⟨target, valid, kept⟩ := ih receiver source ready origin
      exact ⟨.cleanup (.operations [] .pure .pure) target, ⟨rfl, valid⟩, congrArg _ kept⟩
  | history changed ih =>
      obtain ⟨target, valid, kept⟩ := ih receiver source ready origin
      exact ⟨.spent target, valid, congrArg _ kept⟩
  | plain changed ih =>
      cases source with
      | operations interfaces => exact operations_actual (.plain changed) receiver interfaces ready origin
      | plain code tail =>
          simp only [ofCapability] at origin
          cases origin
          obtain ⟨code, codeReady, codeKept⟩ := code.expand_retaining laws project ready.1 (changed.forest.append receiver)
          obtain ⟨target, valid, kept⟩ := ih receiver tail ready.2 rfl
          refine ⟨.plain code target, ⟨codeReady, valid⟩, ?_⟩
          simp only [ofCapability, codeKept, kept]
  | handler changed ih =>
      cases source with
      | operations interfaces => exact operations_actual (.handler changed) receiver interfaces ready origin
      | handler tail =>
          simp only [ofCapability] at origin
          cases origin
          obtain ⟨target, valid, kept⟩ := ih receiver tail ready.2 rfl
          exact ⟨.handler target, ⟨(changed.forest.append receiver).erase.requirements ▸ ready.1, valid⟩, congrArg _ kept⟩
  | cell changed ih =>
      cases source with
      | operations interfaces => exact operations_actual (.cell changed) receiver interfaces ready origin
      | cell tail =>
          simp only [ofCapability] at origin
          cases origin
          obtain ⟨target, valid, kept⟩ := ih receiver tail ready rfl
          exact ⟨.cell target, valid, congrArg _ kept⟩
  | cleanup changed ih =>
      cases source with
      | operations interfaces => exact operations_actual (.cleanup changed) receiver interfaces ready origin
      | cleanup code tail =>
          simp only [ofCapability] at origin
          cases origin
          obtain ⟨code, codeReady, codeKept⟩ := code.expand_retaining laws project ready.1 (.running (changed.forest.append receiver))
          obtain ⟨target, valid, kept⟩ := ih receiver tail ready.2 rfl
          refine ⟨.cleanup code target, ⟨codeReady, valid⟩, ?_⟩
          simp only [ofCapability, codeKept, kept]
  | running changed ih =>
      cases source with
      | operations interfaces => exact operations_actual (.running changed) receiver interfaces ready origin
      | running tail =>
          simp only [ofCapability] at origin
          cases origin
          obtain ⟨target, valid, kept⟩ := ih receiver tail ready rfl
          exact ⟨.running target, valid, congrArg _ kept⟩
  | live changed ih =>
      cases source with
      | operations interfaces => exact operations_actual (.live changed) receiver interfaces ready origin
      | live saved tail =>
          simp only [ofCapability] at origin
          cases origin
          obtain ⟨saved, savedReady, savedKept⟩ := saved.receiver_retaining
            (neutral_receiver_laws laws project) ready.1 (changed.forest.append receiver)
          obtain ⟨target, valid, kept⟩ := ih receiver tail ready.2 rfl
          refine ⟨.live saved target, ⟨savedReady, valid⟩, ?_⟩
          simp only [ofCapability, savedKept, kept]
  | spent changed ih =>
      cases source with
      | operations interfaces => exact operations_actual (.spent changed) receiver interfaces ready origin
      | spent tail =>
          simp only [ofCapability] at origin
          cases origin
          obtain ⟨target, valid, kept⟩ := ih receiver tail ready rfl
          exact ⟨.spent target, valid, congrArg _ kept⟩

end Ash.OneShot.SourceScheduledCapabilityAnnotations

#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Retained.expand_neutral_at
