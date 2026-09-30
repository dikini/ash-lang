import SourceBoundNeutralExpansion
import SourceScheduledNeutralBoundRetention

/-! Neutral expansion of a retained forest, not only its outside receiver.
Original pending and callback annotations survive at their original positions;
new pure frames receive absent bounds. -/
namespace Ash.OneShot.SourceScheduledRetainedInterfaces
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledNeutral (Expansion)

theorem Interfaces.check_neutral {forest : Forest hints} (source : Interfaces world forest)
    {outsideHints : Hints outsideScope} {nextHints : Hints nextScope}
    {outside : Forest outsideHints} {next : Forest nextHints}
    (changed : Expansion outside next) : source.check outsideScope = source.check nextScope := by
  induction source generalizing outsideScope nextScope with
  | nil => rfl
  | cell source ih | running source ih | spent source ih => exact ih changed
  | plain rest required footprint declared source ih | handler rest source ih =>
      simp only [Interfaces.check]
      exact congr (congrArg Bool.and ((Expansion.refl (forest := rest)).append changed).erase.requirements) (ih changed)
  | cleanup rest required footprint declared source ih =>
      simp only [Interfaces.check]
      exact congr (congrArg Bool.and (Expansion.running ((Expansion.refl (forest := rest)).append changed)).erase.requirements) (ih changed)
  | live rest saved source ihSaved ih =>
      simp only [Interfaces.check]
      exact congr (congrArg Bool.and (ihSaved ((Expansion.refl (forest := rest)).append changed))) (ih changed)

/-- Interface annotations move with their retained plans. All outside checks
remain exactly equal; the theorem does not assume that a check succeeds. -/
theorem Interfaces.expand_neutral
    {beforeHints : Hints beforeScope} {afterHints : Hints afterScope}
    {before : Forest beforeHints} {after : Forest afterHints}
    (changed : Expansion before after) (source : Interfaces world before) :
    ∃ target : Interfaces world after,
      ∀ {outsideScope} {outsideHints : Hints outsideScope} (_outside : Forest outsideHints),
        target.check outsideScope = source.check outsideScope := by
  induction changed with
  | refl => exact ⟨source, fun _ => rfl⟩
  | extra changed ih =>
      obtain ⟨target, kept⟩ := ih source
      exact ⟨.plain _ [] .pure .pure target, fun outside => kept outside⟩
  | completion changed ih =>
      obtain ⟨target, kept⟩ := ih source
      exact ⟨.cleanup _ [] .pure .pure target, fun outside => kept outside⟩
  | history changed ih =>
      obtain ⟨target, kept⟩ := ih source
      exact ⟨.spent target, kept⟩
  | plain changed ih =>
      cases source with
      | plain rest required footprint declared source =>
          obtain ⟨target, kept⟩ := ih source
          refine ⟨.plain _ required footprint declared target, ?_⟩
          intro outsideScope outsideHints outside
          simp only [Interfaces.check]
          exact congr (congrArg Bool.and (changed.append (.refl (forest := outside))).erase.requirements.symm) (kept outside)
  | handler changed ih =>
      cases source with
      | handler rest source =>
          obtain ⟨target, kept⟩ := ih source
          refine ⟨.handler _ target, ?_⟩
          intro outsideScope outsideHints outside
          simp only [Interfaces.check]
          exact congr (congrArg Bool.and (changed.append (.refl (forest := outside))).erase.requirements.symm) (kept outside)
  | cell changed ih => cases source with
      | cell source => obtain ⟨target, kept⟩ := ih source; exact ⟨.cell target, kept⟩
  | cleanup changed ih =>
      cases source with
      | cleanup rest required footprint declared source =>
          obtain ⟨target, kept⟩ := ih source
          refine ⟨.cleanup _ required footprint declared target, ?_⟩
          intro outsideScope outsideHints outside
          simp only [Interfaces.check]
          exact congr (congrArg Bool.and (Expansion.running (changed.append (.refl (forest := outside)))).erase.requirements.symm) (kept outside)
  | running changed ih => cases source with
      | running source => obtain ⟨target, kept⟩ := ih source; exact ⟨.running target, kept⟩
  | live changed ih =>
      cases source with
      | live rest saved source =>
          obtain ⟨target, kept⟩ := ih source
          refine ⟨.live _ saved target, ?_⟩
          intro outsideScope outsideHints outside
          simp only [Interfaces.check]
          exact congr (congrArg Bool.and (saved.check_neutral (changed.append (.refl (forest := outside)))).symm) (kept outside)
  | spent changed ih => cases source with
      | spent source => obtain ⟨target, kept⟩ := ih source; exact ⟨.spent target, kept⟩

end Ash.OneShot.SourceScheduledRetainedInterfaces

#print axioms Ash.OneShot.SourceScheduledRetainedInterfaces.Interfaces.check_neutral
#print axioms Ash.OneShot.SourceScheduledRetainedInterfaces.Interfaces.expand_neutral
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
private theorem operations_neutral
    {beforeHints : Hints beforeScope} {afterHints : Hints afterScope}
    {before : Forest beforeHints} {after : Forest afterHints}
    {outsideHints : Hints outsideScope} {nextHints : Hints nextScope}
    {outside : Forest outsideHints} {next : Forest nextHints}
    (changed : Expansion before after) (receiver : Expansion outside next)
    (interfaces : SourceScheduledRetainedInterfaces.Interfaces world before)
    (ready : interfaces.check outsideScope = true) :
    ∃ target : Retained world after next, target.Valid outward actions phases ∧
      Neutral world (ofCapability (Retained.operations interfaces (outside := outside))) (ofCapability target) := by
  obtain ⟨target, kept⟩ := interfaces.expand_neutral changed
  refine ⟨.operations target, ?_, Neutral.absent changed⟩
  change target.check nextScope = true
  rw [kept next, ← interfaces.check_neutral receiver]
  exact ready

/-- Expand the actual retained forest and its outside receiver together.
Current code reuses metadata-preserving receiver transport; the forest relation
records each inserted pure frame and retains dormant saved metadata exactly. -/
theorem Retained.expand_neutral
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {beforeHints : Hints beforeScope} {afterHints : Hints afterScope}
    {before : Forest beforeHints} {after : Forest afterHints}
    (changed : Expansion before after)
    {outsideHints : Hints outsideScope} {nextHints : Hints nextScope}
    {outside : Forest outsideHints} {next : Forest nextHints}
    (receiver : Expansion outside next)
    (source : Retained world before outside) (ready : source.Valid outward actions phases) :
    ∃ target : Retained world after next, target.Valid outward actions phases ∧
      Neutral world (ofCapability source) (ofCapability target) := by
  induction changed generalizing outsideScope nextScope with
  | refl =>
      obtain ⟨target, valid, kept⟩ := source.receiver_retaining (neutral_receiver_laws laws project) ready receiver
      exact ⟨target, valid, by rw [kept]; exact .refl⟩
  | extra changed ih =>
      obtain ⟨target, valid, kept⟩ := ih receiver source ready
      exact ⟨.plain (.operations [] .pure .pure) target, ⟨rfl, valid⟩, .extra kept⟩
  | completion changed ih =>
      obtain ⟨target, valid, kept⟩ := ih receiver source ready
      exact ⟨.cleanup (.operations [] .pure .pure) target, ⟨rfl, valid⟩, .completion kept⟩
  | history changed ih =>
      obtain ⟨target, valid, kept⟩ := ih receiver source ready
      exact ⟨.spent target, valid, .history kept⟩
  | plain changed ih =>
      cases source with
      | operations interfaces => exact operations_neutral (.plain changed) receiver interfaces ready
      | plain code tail =>
          obtain ⟨code, codeReady, codeKept⟩ := code.expand_retaining laws project ready.1 (changed.append receiver)
          obtain ⟨target, valid, kept⟩ := ih receiver tail ready.2
          refine ⟨.plain code target, ⟨codeReady, valid⟩, ?_⟩
          simpa only [ofCapability, codeKept] using Neutral.plain kept
  | handler changed ih =>
      cases source with
      | operations interfaces => exact operations_neutral (.handler changed) receiver interfaces ready
      | handler tail =>
          obtain ⟨target, valid, kept⟩ := ih receiver tail ready.2
          exact ⟨.handler target, ⟨(changed.append receiver).erase.requirements ▸ ready.1, valid⟩, .handler kept⟩
  | cell changed ih =>
      cases source with
      | operations interfaces => exact operations_neutral (.cell changed) receiver interfaces ready
      | cell tail =>
          obtain ⟨target, valid, kept⟩ := ih receiver tail ready
          exact ⟨.cell target, valid, .cell kept⟩
  | cleanup changed ih =>
      cases source with
      | operations interfaces => exact operations_neutral (.cleanup changed) receiver interfaces ready
      | cleanup code tail =>
          obtain ⟨code, codeReady, codeKept⟩ := code.expand_retaining laws project ready.1 (.running (changed.append receiver))
          obtain ⟨target, valid, kept⟩ := ih receiver tail ready.2
          refine ⟨.cleanup code target, ⟨codeReady, valid⟩, ?_⟩
          simpa only [ofCapability, codeKept] using Neutral.cleanup kept
  | running changed ih =>
      cases source with
      | operations interfaces => exact operations_neutral (.running changed) receiver interfaces ready
      | running tail =>
          obtain ⟨target, valid, kept⟩ := ih receiver tail ready
          exact ⟨.running target, valid, .running kept⟩
  | live changed ih =>
      cases source with
      | operations interfaces => exact operations_neutral (.live changed) receiver interfaces ready
      | live saved tail =>
          obtain ⟨saved, savedReady, savedKept⟩ := saved.receiver_retaining
            (neutral_receiver_laws laws project) ready.1 (changed.append receiver)
          obtain ⟨target, valid, kept⟩ := ih receiver tail ready.2
          refine ⟨.live saved target, ⟨savedReady, valid⟩, ?_⟩
          simpa only [ofCapability, savedKept] using Neutral.live kept
  | spent changed ih =>
      cases source with
      | operations interfaces => exact operations_neutral (.spent changed) receiver interfaces ready
      | spent tail =>
          obtain ⟨target, valid, kept⟩ := ih receiver tail ready
          exact ⟨.spent target, valid, .spent kept⟩

end Ash.OneShot.SourceScheduledCapabilityAnnotations

#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Retained.expand_neutral
