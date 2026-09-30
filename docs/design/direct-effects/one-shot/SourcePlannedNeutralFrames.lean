import SourcePlannedRecomposition
import SourceNeutralScopes

/-! The declaration-aware compatibility layer uses the independent scope
expansion relation. Keeping that relation below declaration recipes permits
reuse by the erased checker without a circular proof dependency. -/
namespace Ash.OneShot.SourcePlannedNeutralFrames
open SourceContextualHints (Hints)
open SourceContextualInvocationHints (findOwner)

theorem Expansion.compatible (changed : Expansion before after)
    (compatible : SourceContextualHintChecking.Compatible before .nil) : SourceContextualHintChecking.Compatible after .nil := by
  apply (SourceContextualHintChecking.check_iff _).mp
  rw [← changed.check (outsideBefore := .nil) .refl]
  exact (SourceContextualHintChecking.check_iff _).mpr compatible

private theorem resume_permissions (access : SourceDependencyCapture.ResumeChecked actions phases owner scope result) :
    ∃ rights, actions owner = some rights ∧ rights.resume = true ∧ phases owner = .available := by
  cases access with | checked located known permission available => exact ⟨_, known, permission, available⟩

private theorem dispose_facts {hints : Hints scope} (found : findOwner owner hints = some selected)
    (access : SourceDependencyCapture.DisposeChecked outward actions phases owner scope result) :
    ∃ rights, actions owner = some rights ∧ rights.dispose = true ∧ phases owner = .available ∧
      selected.scopes.captured.held = false ∧ SourceRecursiveRoutes.Closing outward selected.scopes.captured.shape [] [] := by
  cases access with
  | checked located known permission available unprotected closing =>
      cases Option.some.inj ((SourceContextualInvocationHints.selected_cut found).lookup.symm.trans located.lookup)
      exact ⟨_, known, permission, available, unprotected, closing⟩

/-- Reuse the independent resume judgment at the same owner, permissions
and phase. The restored annotations gain only the corresponding pure frames. -/
theorem Expansion.resume (changed : Expansion before after)
    (admitted : SourceContextualInvocations.Resume actions phases owner before restored) :
    ∃ next, SourceContextualInvocations.Resume actions phases owner after next ∧ Expansion restored.hints next.hints := by
  cases admitted with
  | checked found access compatible =>
      obtain ⟨next, foundNext, related⟩ := changed.find_owner found
      obtain ⟨rights, known, permission, available⟩ := resume_permissions access
      exact ⟨_, .checked foundNext (.checked (SourceContextualInvocationHints.selected_cut foundNext) known permission available)
        (related.resumed.compatible compatible), related.resumed⟩

/-- Added caller frames preserve the selected capture, its protection and
closing route. The same source owner, permissions and phase are checked. -/
theorem Expansion.dispose (changed : Expansion before after)
    (admitted : SourceContextualInvocations.Dispose outward actions phases owner before scheduled) :
    ∃ next, SourceContextualInvocations.Dispose outward actions phases owner after next ∧ Expansion scheduled.hints next.hints := by
  cases admitted with
  | checked found access compatible =>
      rename_i selected
      obtain ⟨next, foundNext, related⟩ := changed.find_owner found
      obtain ⟨rights, known, permission, available, unprotected, closing⟩ := dispose_facts found access
      have savedSame : selected.scopes.captured = next.scopes.captured := by cases related; rfl
      exact ⟨_, .checked foundNext (.checked (SourceContextualInvocationHints.selected_cut foundNext) known permission available
        (savedSame ▸ unprotected) (savedSame ▸ closing))
        (related.disposed.compatible compatible), related.disposed⟩

end Ash.OneShot.SourcePlannedNeutralFrames

#print axioms Ash.OneShot.SourcePlannedNeutralFrames.Expansion.compatible
#print axioms Ash.OneShot.SourcePlannedNeutralFrames.Expansion.resume
#print axioms Ash.OneShot.SourcePlannedNeutralFrames.Expansion.dispose
