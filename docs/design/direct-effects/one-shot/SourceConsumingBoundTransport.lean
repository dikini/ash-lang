import SourceConsumingClauseContracts

/-! Transport of the finite clause-bound check. Resource extension reuses the
existing source/interface weakening operations. Owner changes are observed
only at the bound continuation; this does not transport contextual saved-source
admission, whose recursive invocations can observe other owners. -/
namespace Ash.OneShot.SourceConsumingClauseAnnotations
open SourceDeclarationPlans (Plan)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledRetainedInterfaces (Interfaces)

variable [SourceScheduledCapabilityAnnotations.DeclarationPolicy]

/-- Reuse the existing weakening operations and interface check invariance.
A larger world restricts the future fresh-resource choices. -/
theorem Body.boundCheck_world_weaken {plan : Plan dependencies} (body : Body world owner plan)
    (larger : world ⊆ next)
    {frontHints : Hints frontScope} {front : Forest frontHints} {before : Interfaces world front}
    (checked : body.BoundCheck resumeRequired closeRequired actions phases receiving waiting before) :
    (body.world_weaken larger).BoundCheck resumeRequired closeRequired actions phases receiving waiting
      (before.world_weaken larger) := by
  induction body generalizing receiving frontScope next with
  | resume | dispose =>
      simpa only [Body.world_weaken, Body.BoundCheck, Interfaces.check_world_weaken] using checked
  | sequence required footprint declared rest ih => exact ⟨checked.1, ih larger checked.2⟩
  | choice first second ihFirst ihSecond => exact ⟨ihFirst larger checked.1, ihSecond larger checked.2⟩
  | handler bounds admitted body ih => exact ⟨checked.1, ih larger checked.2⟩
  | cleanup required footprint declared body ih => exact ⟨ih larger checked.1, checked.2⟩
  | resource body ih =>
      intro identity fresh
      have oldFresh := fun member => fresh (larger member)
      have retained := ih identity oldFresh
        (ScopedExpressions.append_subset larger (List.Subset.refl [identity])) (checked identity oldFresh)
      simpa only [Body.world_weaken, Body.BoundCheck, Interfaces.world_weaken, Interfaces.world_weaken_trans] using retained

/-- The finite clause check grants no rights for outside owners. Preserve the
bound owner's permission entry and its availability; all other entries may
change. Saved-source rechecking has separate, stronger obligations. -/
theorem Body.boundCheck_owner_transport {plan : Plan dependencies} (body : Body world owner plan)
    {frontHints : Hints frontScope} {front : Forest frontHints} {before : Interfaces world front}
    (checked : body.BoundCheck resumeRequired closeRequired actions phases receiving waiting before)
    (permissions : actions owner = nextActions owner)
    (available : phases owner = .available → nextPhases owner = .available) :
    body.BoundCheck resumeRequired closeRequired nextActions nextPhases receiving waiting before := by
  induction body generalizing receiving frontScope with
  | resume | dispose =>
      exact ⟨by simpa only [permissions] using checked.1, available checked.2.1, checked.2.2⟩
  | sequence required footprint declared rest ih => exact ⟨checked.1, ih checked.2 permissions available⟩
  | choice first second ihFirst ihSecond => exact ⟨ihFirst checked.1 permissions available, ihSecond checked.2 permissions available⟩
  | handler bounds admitted body ih => exact ⟨checked.1, ih checked.2 permissions available⟩
  | cleanup required footprint declared body ih => exact ⟨ih checked.1 permissions available, checked.2⟩
  | resource body ih => exact fun identity fresh => ih identity fresh (checked identity fresh) permissions available

/-- Every consuming body eventually checks its own available continuation,
including a universally fresh resource body. World weakening cannot hide a
spent owner by removing all fresh choices. -/
theorem Body.boundCheck_owner {plan : Plan dependencies} (body : Body world owner plan)
    {frontHints : Hints frontScope} {front : Forest frontHints} {before : Interfaces world front}
    (checked : body.BoundCheck resumeRequired closeRequired actions phases receiving waiting before) :
    (∃ rights, actions owner = some rights) ∧ phases owner = .available := by
  induction body generalizing receiving frontScope with
  | resume | dispose =>
      refine ⟨?_, checked.2.1⟩
      cases known : actions _ with
      | none => simpa only [known, Option.any_none, Bool.false_eq_true] using checked.1
      | some rights => exact ⟨rights, rfl⟩
  | sequence required footprint declared rest ih => exact ih checked.2
  | choice first second ihFirst ihSecond => exact ihFirst checked.1
  | handler bounds admitted body ih => exact ih checked.2
  | cleanup required footprint declared body ih => exact ih checked.1
  | resource body ih =>
      obtain ⟨identity, fresh⟩ := ScopedTyping.fresh_world_name _
      exact ih identity fresh (checked identity fresh)

/-- Availability is the phase projection of the same independent capability
check; the permission entry is retained for registry-extension proofs. -/
theorem Body.boundCheck_available {plan : Plan dependencies} (body : Body world owner plan)
    {frontHints : Hints frontScope} {front : Forest frontHints} {before : Interfaces world front}
    (checked : body.BoundCheck resumeRequired closeRequired actions phases receiving waiting before) :
    phases owner = .available := (body.boundCheck_owner checked).2

end Ash.OneShot.SourceConsumingClauseAnnotations

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Body.boundCheck_world_weaken
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Body.boundCheck_owner_transport
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Body.boundCheck_available

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Body.boundCheck_owner
