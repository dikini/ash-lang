import SourceScheduledCapabilityReconstruction
import SourceScheduledHandlerAdaptation

/-! Reuse structural receiver adaptation for general capability annotations.
These theorems construct validated annotations of the target plans; they do not
preserve optional bound metadata or assume a target scheduling derivation. -/
namespace Ash.OneShot.SourceScheduledCapabilityAnnotations
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)

section
variable [declarationPolicy : DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]

/-- Neutral receiver changes reuse existing scheduling transport, including
recursive calls to owners outside the saved source. -/
theorem Code.expand_with
    (laws : DeclarationLaws declarationPolicy admission certification outward)
    (declarations : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      admission.accepts outward required plans → declarationPolicy.accepts required plans)
    {beforeHints : Hints first} {afterHints : Hints second} {plan : Plan dependencies}
    {before : Forest beforeHints} {after : Forest afterHints}
    (source : Code world plan before) (checked : source.Valid outward actions phases)
    (changed : SourceScheduledNeutral.Expansion before after) :
    ∃ annotation : Code world plan after, annotation.Valid outward actions phases :=
  (annotate_all_with outward actions declarations).1 _ _ _ _
    (SourceScheduledNeutralChecks.local_transport (source.compile_with laws checked) changed)

theorem Retained.expand_with
    (laws : DeclarationLaws declarationPolicy admission certification outward)
    (declarations : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      admission.accepts outward required plans → declarationPolicy.accepts required plans)
    {beforeHints : Hints first} {afterHints : Hints second}
    {outsideHints : Hints firstOutside} {nextOutsideHints : Hints secondOutside}
    {before : Forest beforeHints} {after : Forest afterHints}
    {outside : Forest outsideHints} {nextOutside : Forest nextOutsideHints}
    (source : Retained world before outside) (checked : source.Valid outward actions phases)
    (inside : SourceScheduledNeutral.Expansion before after)
    (receiver : SourceScheduledNeutral.Expansion outside nextOutside) :
    ∃ annotation : Retained world after nextOutside, annotation.Valid outward actions phases :=
  (annotate_all_with outward actions declarations).2 _ _ _ _
    (SourceScheduledNeutralChecks.pending_transport (source.compile_with laws checked) inside receiver)

/-- Broader declaration evidence is retained by the existing structural
adaptation proof; its only policy premises are source-level declaration laws. -/
theorem Code.adapt_handler_with
    (laws : DeclarationLaws declarationPolicy admission certification outward)
    (declarations : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      admission.accepts outward required plans → declarationPolicy.accepts required plans)
    {beforeHints : Hints first} {afterHints : Hints second} {plan : Plan dependencies}
    {before : Forest beforeHints} {after : Forest afterHints}
    (source : Code world plan before) (checked : source.Valid outward actions phases)
    (changed : SourceScheduledHandlerAdaptation.Adapt outward actions frame phases world plan before after) :
    ∃ annotation : Code world plan after, annotation.Valid outward actions phases :=
  (annotate_all_with outward actions declarations).1 _ _ _ _
    (changed.sound_with laws.legacyAdmission laws.legacyCertification (source.compile_with laws checked))

theorem Retained.adapt_handler_with
    (laws : DeclarationLaws declarationPolicy admission certification outward)
    (declarations : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      admission.accepts outward required plans → declarationPolicy.accepts required plans)
    {beforeHints : Hints first} {afterHints : Hints second}
    {outsideHints : Hints firstOutside} {nextOutsideHints : Hints secondOutside}
    {before : Forest beforeHints} {after : Forest afterHints}
    {outside : Forest outsideHints} {nextOutside : Forest nextOutsideHints}
    (source : Retained world before outside) (checked : source.Valid outward actions phases)
    (changed : SourceScheduledHandlerAdaptation.Retained outward actions frame phases world
      before outside after nextOutside) :
    (∃ annotation : Retained world after nextOutside, annotation.Valid outward actions phases) ∧
      SourceDependencyOwners.owners first = SourceDependencyOwners.owners second :=
  ⟨(annotate_all_with outward actions declarations).2 _ _ _ _
    (changed.sound_with laws.legacyAdmission laws.legacyCertification (source.compile_with laws checked)),
    changed.owners_preserved⟩

end

/-- Handler reinterpretation requires the existing structural adaptation
judgment. This bridge has the same recipe-policy scope as that judgment. -/
theorem Code.adapt_handler
    {beforeHints : Hints first} {afterHints : Hints second} {plan : Plan dependencies}
    {before : Forest beforeHints} {after : Forest afterHints}
    (source : Code world plan before) (checked : source.Valid outward actions phases)
    (changed : SourceScheduledHandlerAdaptation.Adapt outward actions frame phases world plan before after) :
    ∃ annotation : Code world plan after, annotation.Valid outward actions phases :=
  source.adapt_handler_with (recipeLaws outward) (fun checked => checked) checked changed

/-- The adapted retained source keeps the exact owner order and multiplicity.
The ownership fact comes from the existing adaptation theorem. -/
theorem Retained.adapt_handler
    {beforeHints : Hints first} {afterHints : Hints second}
    {outsideHints : Hints firstOutside} {nextOutsideHints : Hints secondOutside}
    {before : Forest beforeHints} {after : Forest afterHints}
    {outside : Forest outsideHints} {nextOutside : Forest nextOutsideHints}
    (source : Retained world before outside) (checked : source.Valid outward actions phases)
    (changed : SourceScheduledHandlerAdaptation.Retained outward actions frame phases world
      before outside after nextOutside) :
    (∃ annotation : Retained world after nextOutside, annotation.Valid outward actions phases) ∧
      SourceDependencyOwners.owners first = SourceDependencyOwners.owners second :=
  source.adapt_handler_with (recipeLaws outward) (fun checked => checked) checked changed

end Ash.OneShot.SourceScheduledCapabilityAnnotations

#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.expand_with
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Retained.expand_with
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.adapt_handler_with
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Retained.adapt_handler_with
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.adapt_handler
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Retained.adapt_handler
