import SourceScheduledCapabilityPhases

/-! Phase restriction preserves the exact recursive capability annotation.
The owner-set and cut lemmas come from existing scheduling transport; unlike
compile/reconstruct transport, this result retains all source and bound data. -/
namespace Ash.OneShot.SourceScheduledCapabilityAnnotations
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open SourceDependencyCapture (Scope OwnerSelection)
open SourceDependencyOwners (owners)
open SourceScheduledPhaseRestriction (AvailableOn owners_closing selected_owner resumed_owners disposed_owners)
open OwnerPhaseTransitions (Phases spend)

theorem resumed_phases
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {whole : Forest wholeHints} {front : Forest frontHints} {saved : Forest savedHints} {tail : Forest tailHints}
    (cut : SourceScheduledNeutral.OwnerCut owner whole front saved tail)
    (extension : AvailableOn (owners wholeScope) before after) :
    AvailableOn (owners (savedScope.append (frontScope.append (.spent owner tailScope))))
      (spend before owner) (spend after owner) :=
  (extension.spend (owner := owner)).weaken (resumed_owners (SourceContextualInvocationHints.selected_cut cut.found))

theorem disposed_phases
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {whole : Forest wholeHints} {front : Forest frontHints} {saved : Forest savedHints} {tail : Forest tailHints}
    (cut : SourceScheduledNeutral.OwnerCut owner whole front saved tail)
    (extension : AvailableOn (owners wholeScope) before after) :
    AvailableOn (owners (savedScope.forClosing.append (.running (frontScope.append (.spent owner tailScope)))))
      (spend before owner) (spend after owner) :=
  (extension.spend (owner := owner)).weaken (disposed_owners (SourceContextualInvocationHints.selected_cut cut.found))

variable [DeclarationPolicy]

/-- Specialize the existing joint permission/phase theorem at unchanged
permissions. This keeps the exact selected bounds and rechecking annotations. -/
theorem restrict_annotation_phases (outward : List Instance) (actions : Syntax.UsageTickets) :
    (∀ world {dependencies scope} {hints : Hints scope} (plan : Plan dependencies) (forest : Forest hints)
      (annotation : Code world plan forest) before after,
      annotation.Valid outward actions before → AvailableOn (owners scope) before after →
      annotation.Valid outward actions after) ∧
    (∀ world {scope outsideScope} {hints : Hints scope} {outsideHints : Hints outsideScope}
      (forest : Forest hints) (outside : Forest outsideHints) (annotation : Retained world forest outside) before after,
      annotation.Valid outward actions before → AvailableOn (owners (scope.append outsideScope)) before after →
      annotation.Valid outward actions after) := by
  constructor
  · intro world dependencies scope hints plan forest annotation before after checked extension
    exact annotation.valid_transport checked (fun _ _ known => known) extension
  · intro world scope outsideScope hints outsideHints forest outside annotation before after checked extension
    exact annotation.valid_transport checked (fun _ _ known => known) extension

theorem Code.restrict_phases {hints : Hints scope} {forest : Forest hints} {plan : Plan dependencies}
    (annotation : Code world plan forest) (checked : annotation.Valid outward actions before)
    (extension : AvailableOn (owners scope) before after) : annotation.Valid outward actions after :=
  (restrict_annotation_phases outward actions).1 _ _ _ annotation before after checked extension

theorem Retained.restrict_phases {hints : Hints scope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints}
    (annotation : Retained world forest outside) (checked : annotation.Valid outward actions before)
    (extension : AvailableOn (owners (scope.append outsideScope)) before after) :
    annotation.Valid outward actions after :=
  (restrict_annotation_phases outward actions).2 _ _ _ annotation before after checked extension

end Ash.OneShot.SourceScheduledCapabilityAnnotations

#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.restrict_annotation_phases
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.restrict_phases
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Retained.restrict_phases

#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.resumed_phases
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.disposed_phases
