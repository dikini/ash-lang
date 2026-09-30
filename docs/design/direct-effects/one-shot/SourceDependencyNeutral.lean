import SourcePlannedCuts
import SourceDependencyChecks

/-! Reuse structural scope expansion at the erased dependency checker. This
layer precedes declaration recipes, so pure cleanup can be admitted by their
structural rules without assuming a successful successor or a clause scheme. -/
namespace Ash.OneShot.SourceDependencyNeutral
open ScopedExpressions ProtectionContracts
open SourceDependencyCapture (Scope ResumeChecked DisposeChecked)
open SourceContextualHints (Hints)
open SourceContextualInvocationHints (Annotated Selection findOwner forClosing)
open SourcePlannedNeutralFrames (Expansion OwnerExpansion)
open SourceDependencyChecks (Local Pending)
open SourceDependencyProjection (project)

/-- Choose no handler requirements when only the underlying scope is needed.
This adds no source admission evidence. -/
def bare : (scope : Scope) → Hints scope
  | .nil => .nil
  | .plain _ rest => .plain (bare rest)
  | .handler _ _ _ rest => .handler [] (bare rest)
  | .cell _ rest => .cell (bare rest)
  | .cleanup _ _ rest => .cleanup (bare rest)
  | .running rest => .running (bare rest)
  | .live _ saved rest => .live (bare saved) (bare rest)
  | .spent _ rest => .spent (bare rest)

def projected : {scope : Scope} → Hints scope → Hints (project scope)
  | _, .nil => .nil
  | _, .plain rest => .plain (projected rest)
  | _, .handler required rest => .handler required (projected rest)
  | _, .cell rest => .cell (projected rest)
  | _, .cleanup rest => .cleanup (projected rest)
  | _, .running rest => .running (projected rest)
  | _, .live saved rest => .live (projected saved) (projected rest)
  | .spent _ restScope, .spent rest => @projected restScope rest

theorem expansion_projected (changed : Expansion before after) : Expansion (projected before) (projected after) := by
  induction changed with
  | refl => exact .refl
  | extra next ih => exact .extra ih
  | completion next ih => exact .completion ih
  | history next ih | spent next ih => exact ih
  | plain next ih => exact .plain ih
  | handler next ih => exact .handler ih
  | cell next ih => exact .cell ih
  | cleanup next ih => exact .cleanup ih
  | running next ih => exact .running ih
  | live next ih => exact .live ih

private theorem annotated_owner {hints : Hints scope}
    (cut : SourceDependencyCapture.OwnerCut owner scope selected) :
    ∃ original, findOwner owner hints = some original ∧ original.scopes = selected := by
  apply Option.map_eq_some_iff.mp
  rw [SourceContextualInvocationHints.find_owner_erases]
  exact cut.lookup

theorem resume_transport {before : Hints first} {after : Hints second}
    (changed : Expansion before after) (access : ResumeChecked actions phases owner first result) :
    ∃ original : Hints result, ∃ nextScope, ∃ next : Hints nextScope,
      ResumeChecked actions phases owner second nextScope ∧ Expansion original next := by
  cases access with
  | checked cut known permission available =>
      obtain ⟨selected, found, same⟩ := annotated_owner (hints := before) cut
      cases same
      obtain ⟨next, foundNext, related⟩ := changed.find_owner found
      exact ⟨(selected.resumed owner).hints, _, (next.resumed owner).hints,
        .checked (SourceContextualInvocationHints.selected_cut foundNext) known permission available, related.resumed⟩

theorem dispose_transport {before : Hints first} {after : Hints second}
    (changed : Expansion before after) (access : DisposeChecked outward actions phases owner first result) :
    ∃ original : Hints result, ∃ nextScope, ∃ next : Hints nextScope,
      DisposeChecked outward actions phases owner second nextScope ∧ Expansion original next := by
  cases access with
  | checked cut known permission available unprotected closing =>
      obtain ⟨selected, found, same⟩ := annotated_owner (hints := before) cut
      cases same
      obtain ⟨next, foundNext, related⟩ := changed.find_owner found
      have savedSame : selected.scopes.captured = next.scopes.captured := by cases related; rfl
      exact ⟨(selected.disposed owner).hints, _, (next.disposed owner).hints,
        .checked (SourceContextualInvocationHints.selected_cut foundNext) known permission available
          (savedSame ▸ unprotected) (savedSame ▸ closing), related.disposed⟩

/-- The existing mutual checking induction transports each stored expression
and callback. Selection, closing routes and owner bounds reuse scope lemmas. -/
theorem local_transport (checked : Local outward actions phases world dependencies scope)
    {hints : Hints scope} {next : Hints nextScope} (changed : Expansion hints next) :
    Local outward actions phases world dependencies nextScope := by
  refine (Local.rec
    (motive_1 := fun phases world dependencies scope _ => ∀ {nextScope}
      (hints : Hints scope) (next : Hints nextScope), Expansion hints next →
      Local outward actions phases world dependencies nextScope)
    (motive_2 := fun phases world scope outside _ => ∀ {nextScope nextOutside}
      (hints : Hints scope) (outsideHints : Hints outside)
      (next : Hints nextScope) (nextOutsideHints : Hints nextOutside),
      Expansion hints next → Expansion outsideHints nextOutsideHints →
      Pending outward actions phases world nextScope nextOutside)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (t := checked)) hints next changed
  · intros; exact .pure
  · intros
    rename_i guard scheduled bounded ih nextScope hints next changed
    cases guard with
    | builtin found =>
        have nextFound := SourcePlannedCuts.builtin_expand changed found
        apply Local.request (.builtin nextFound)
        · intro saved waiting contract modes found disposes
          cases Option.some.inj (nextFound.symm.trans found)
        · intro saved waiting contract modes found disposes
          cases Option.some.inj (nextFound.symm.trans found)
    | handler found permission row body closing =>
        obtain ⟨saved, waiting, cut⟩ := SourcePlannedCuts.of_lookup hints found
        obtain ⟨_, _, nextSaved, nextWaiting, nextCut, inside, outside⟩ := SourcePlannedCuts.expand changed cut
        apply Local.request (.handler nextCut.lookup (inside.held ▸ permission) (inside.held ▸ row) (inside.held ▸ body)
          (fun disposes => SourceDependencyCapture.check_closing_iff.mp (by
            rw [← inside.closing_check]
            exact SourceDependencyCapture.check_closing_iff.mpr (closing disposes))))
        · intro actualSaved actualWaiting contract modes actual disposes
          cases Option.some.inj (nextCut.lookup.symm.trans actual)
          exact ih _ _ _ _ found disposes (projected (forClosing saved)) (projected (.running waiting))
            (projected (forClosing nextSaved)) (projected (.running nextWaiting))
            (expansion_projected inside.forClosing) (expansion_projected (.running outside))
        · intro actualSaved actualWaiting contract modes actual disposes
          cases Option.some.inj (nextCut.lookup.symm.trans actual)
          have owners := inside.pending_owners (bounded _ _ _ _ found disposes)
          rw [inside.owners] at owners
          exact owners
  · intros
    rename_i access restored ih nextScope hints next changed
    obtain ⟨original, _, after, nextAccess, related⟩ := resume_transport changed access
    exact .resume nextAccess (ih (projected original) .nil (projected after) .nil (expansion_projected related) .refl)
  · intros
    rename_i access scheduled ih nextScope hints next changed
    obtain ⟨original, _, after, nextAccess, related⟩ := dispose_transport changed access
    exact .dispose nextAccess (ih (projected original) .nil (projected after) .nil (expansion_projected related) .refl)
  · intros
    rename_i first second ihFirst ihSecond nextScope hints next changed
    exact .sequence (ihFirst (.plain hints) (.plain next) (.plain changed)) (ihSecond hints next changed)
  · intros
    rename_i first second ihFirst ihSecond nextScope hints next changed
    exact .choice (ihFirst hints next changed) (ihSecond hints next changed)
  · intros
    rename_i body ih nextScope hints next changed
    exact .handler (ih (.handler [] hints) (.handler [] next) (.handler changed))
  · intros
    rename_i body completion ihBody ihCompletion nextScope hints next changed
    exact .cleanup (ihBody (.cleanup hints) (.cleanup next) (.cleanup changed))
      (ihCompletion (.running hints) (.running next) (.running changed))
  · intros
    rename_i body ih nextScope hints next changed
    exact .resource (fun identity fresh => ih identity fresh (.cell hints) (.cell next) (.cell changed))
  · intros
    rename_i nextScope nextOutside hints outsideHints next nextOutsideHints changed outsideChanged
    cases hints
    induction next <;> cases changed
    all_goals first
      | exact .nil
      | (rename_i ihExtra extra; exact .plain .pure (ihExtra extra))
      | (rename_i ihHistory history; exact .spent (ihHistory history))
      | (rename_i ihCompletion completion; exact .cleanup .pure (ihCompletion completion))
  · intros
    rename_i code tail ihCode ihTail nextScope nextOutside hints outsideHints next nextOutsideHints changed outsideChanged
    cases hints with | plain rest =>
      induction next <;> cases changed
      all_goals first
        | (rename_i ihExtra extra; exact .plain .pure (ihExtra extra))
        | (rename_i ihHistory history; exact .spent (ihHistory history))
        | (rename_i ihCompletion completion; exact .cleanup .pure (ihCompletion completion))
        | (apply Pending.plain
           · exact ihCode (rest.append outsideHints) _ (Expansion.append (by first | exact .refl | assumption) outsideChanged)
           · exact ihTail rest outsideHints _ nextOutsideHints (by first | exact .refl | assumption) outsideChanged)
  · intros
    rename_i tail ih nextScope nextOutside hints outsideHints next nextOutsideHints changed outsideChanged
    cases hints with | handler required rest =>
      induction next <;> cases changed
      all_goals first
        | (rename_i ihExtra extra; exact .plain .pure (ihExtra extra))
        | (rename_i ihHistory history; exact .spent (ihHistory history))
        | (rename_i ihCompletion completion; exact .cleanup .pure (ihCompletion completion))
        | exact .handler (ih rest outsideHints _ nextOutsideHints (by first | exact .refl | assumption) outsideChanged)
  · intros
    rename_i tail ih nextScope nextOutside hints outsideHints next nextOutsideHints changed outsideChanged
    cases hints with | cell rest =>
      induction next <;> cases changed
      all_goals first
        | (rename_i ihExtra extra; exact .plain .pure (ihExtra extra))
        | (rename_i ihHistory history; exact .spent (ihHistory history))
        | (rename_i ihCompletion completion; exact .cleanup .pure (ihCompletion completion))
        | exact .cell (ih rest outsideHints _ nextOutsideHints (by first | exact .refl | assumption) outsideChanged)
  · intros
    rename_i completion tail ihCompletion ihTail nextScope nextOutside hints outsideHints next nextOutsideHints changed outsideChanged
    cases hints with | cleanup rest =>
      induction next <;> cases changed
      all_goals first
        | (rename_i ihExtra extra; exact .plain .pure (ihExtra extra))
        | (rename_i ihHistory history; exact .spent (ihHistory history))
        | (rename_i ihExtra extra; exact .cleanup .pure (ihExtra extra))
        | (apply Pending.cleanup
           · exact ihCompletion (.running (rest.append outsideHints)) _
               (.running (Expansion.append (by first | exact .refl | assumption) outsideChanged))
           · exact ihTail rest outsideHints _ nextOutsideHints (by first | exact .refl | assumption) outsideChanged)
  · intros
    rename_i tail ih nextScope nextOutside hints outsideHints next nextOutsideHints changed outsideChanged
    cases hints with | running rest =>
      induction next <;> cases changed
      all_goals first
        | (rename_i ihExtra extra; exact .plain .pure (ihExtra extra))
        | (rename_i ihHistory history; exact .spent (ihHistory history))
        | (rename_i ihCompletion completion; exact .cleanup .pure (ihCompletion completion))
        | exact .running (ih rest outsideHints _ nextOutsideHints (by first | exact .refl | assumption) outsideChanged)
  · intros
    rename_i saved tail ihSaved ihTail nextScope nextOutside hints outsideHints next nextOutsideHints changed outsideChanged
    cases hints with | live savedHints rest =>
      induction next <;> cases changed
      all_goals first
        | (rename_i ihExtra extra; exact .plain .pure (ihExtra extra))
        | (rename_i ihHistory history; exact .spent (ihHistory history))
        | (rename_i ihCompletion completion; exact .cleanup .pure (ihCompletion completion))
        | exact .live (ihSaved savedHints (rest.append outsideHints) _ _ .refl
            (Expansion.append (by first | exact .refl | assumption) outsideChanged))
            (ihTail rest outsideHints _ nextOutsideHints (by first | exact .refl | assumption) outsideChanged)
  · intros
    rename_i tail ih nextScope nextOutside hints outsideHints next nextOutsideHints changed outsideChanged
    cases hints with | spent rest =>
      induction next <;> cases changed
      all_goals first
        | (rename_i ihExtra extra; exact .plain .pure (ihExtra extra))
        | (rename_i ihHistory history; exact .spent (ihHistory history))
        | (rename_i ihCompletion completion; exact .cleanup .pure (ihCompletion completion))
        | exact .spent (ih rest outsideHints _ nextOutsideHints (by first | exact .refl | assumption) outsideChanged)

/-- Pure cleanup composes with the lower checker used by declaration erasure. -/
theorem pure_cleanup (body : Local outward actions phases world dependencies scope) :
    Local outward actions phases world (.cleanup [] .pure dependencies) scope :=
  .cleanup (local_transport body (hints := bare scope) (.completion .refl)) .pure

end Ash.OneShot.SourceDependencyNeutral

#print axioms Ash.OneShot.SourceDependencyNeutral.expansion_projected
#print axioms Ash.OneShot.SourceDependencyNeutral.resume_transport
#print axioms Ash.OneShot.SourceDependencyNeutral.dispose_transport
#print axioms Ash.OneShot.SourceDependencyNeutral.local_transport
#print axioms Ash.OneShot.SourceDependencyNeutral.pure_cleanup


namespace Ash.OneShot.SourceDependencyNeutral
open SourceDependencyAnnotations SourceDependencyFrames
open SourceDependencyChecks (Local)

/-- The exact source decomposition supplies the child's check at the waiting
    context and the retained context's check. The only inserted scope not
    already present in sequencing is a pure frame, handled by existing transport. -/
theorem focus_dependencies_checked
    (shape : FocusDependencies whole child rest)
    (checked : Local outward actions phases world whole scope) :
    Local outward actions phases world child (.plain rest scope) ∧
      Local outward actions phases world rest scope := by
  cases shape with
  | direct => exact Local.sequence_iff.mp checked
  | purePair => exact ⟨.pure, .pure⟩
  | leftValue silent =>
      have next := (Local.silent_prefix silent).mp checked
      exact ⟨local_transport next (hints := bare scope) (.extra .refl), .pure⟩
  | functionValue silent => exact Local.sequence_iff.mp ((Local.silent_prefix silent).mp checked)

/-- Plugging an evaluated value requires only the waiting code's existing
    check. Its silent prefix cannot introduce an operation, invocation or cleanup. -/
theorem plug_dependencies_checked
    (shape : FocusDependencies whole child rest) (silent : child.Silent)
    (checked : Local outward actions phases world rest scope) :
    Local outward actions phases world whole scope := by
  cases shape with
  | direct => exact .sequence (.silent silent) checked
  | purePair => exact .pure
  | leftValue valueSilent => exact .sequence (.silent valueSilent) (.silent silent)
  | functionValue valueSilent => exact .sequence (.silent valueSilent) (.sequence (.silent silent) checked)

#print axioms Ash.OneShot.SourceDependencyNeutral.focus_dependencies_checked
#print axioms Ash.OneShot.SourceDependencyNeutral.plug_dependencies_checked
end Ash.OneShot.SourceDependencyNeutral


namespace Ash.OneShot.SourceDependencyNeutral.Lexical
open ScopedExpressions ProtectionContracts
open SourceDependencyCapture (Scope)
open SourceContextualHints (Hints)
open SourceContextualInvocationHints (Selection findOwner)
open SourcePlannedNeutralFrames (Expansion OwnerExpansion)
open SourceDependencyChecks.Lexical (Local Pending Unwind)

private theorem annotated_owner {hints : Hints scope}
    (cut : SourceDependencyCapture.OwnerCut owner scope selected) :
    ∃ original, findOwner owner hints = some original ∧ original.scopes = selected := by
  apply Option.map_eq_some_iff.mp
  rw [SourceContextualInvocationHints.find_owner_erases]
  exact cut.lookup

/-- Reuse neutral-scope expansion for the lexical checks. Disposal transports
    the actual abandoned capture and waiting caller independently, without a
    closing-plan transformation. -/
theorem local_transport (checked : Local outward actions phases world dependencies scope)
    {hints : Hints scope} {next : Hints nextScope} (changed : Expansion hints next) :
    Local outward actions phases world dependencies nextScope := by
  refine (Local.rec
    (motive_1 := fun phases world dependencies scope _ => ∀ {nextScope}
      (hints : Hints scope) (next : Hints nextScope), Expansion hints next →
      Local outward actions phases world dependencies nextScope)
    (motive_2 := fun phases world scope outside _ => ∀ {nextScope nextOutside}
      (hints : Hints scope) (outsideHints : Hints outside)
      (next : Hints nextScope) (nextOutsideHints : Hints nextOutside),
      Expansion hints next → Expansion outsideHints nextOutsideHints →
      Pending outward actions phases world nextScope nextOutside)
    (motive_3 := fun phases world scope outside _ => ∀ {nextScope nextOutside}
      (hints : Hints scope) (outsideHints : Hints outside)
      (next : Hints nextScope) (nextOutsideHints : Hints nextOutside),
      Expansion hints next → Expansion outsideHints nextOutsideHints →
      Unwind outward actions phases world nextScope nextOutside)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (t := checked)) hints next changed
  · intros; exact .pure
  · intros
    rename_i guard callbacks bounded ihCallbacks nextScope hints next changed
    cases guard with
    | builtin found =>
        have nextFound := SourcePlannedCuts.builtin_expand changed found
        apply Local.request (.builtin nextFound)
        all_goals
          intro saved waiting contract modes found disposes
          cases Option.some.inj (nextFound.symm.trans found)
    | handler found permission row body =>
        obtain ⟨saved, waiting, cut⟩ := SourcePlannedCuts.of_lookup hints found
        obtain ⟨_, _, nextSaved, nextWaiting, nextCut, inside, outside⟩ := SourcePlannedCuts.expand changed cut
        apply Local.request (.handler nextCut.lookup (inside.held ▸ permission)
          (inside.held ▸ row) (inside.held ▸ body))
        · intro actualSaved actualWaiting contract modes actual disposes
          cases Option.some.inj (nextCut.lookup.symm.trans actual)
          exact ihCallbacks _ _ _ _ found disposes saved (.running waiting) nextSaved (.running nextWaiting)
            inside (.running outside)
        · intro actualSaved actualWaiting contract modes actual disposes
          cases Option.some.inj (nextCut.lookup.symm.trans actual)
          have owners := inside.pending_owners (bounded _ _ _ _ found disposes)
          rw [inside.owners] at owners
          exact owners
  · intros
    rename_i access restored ih nextScope hints next changed
    obtain ⟨original, _, after, nextAccess, related⟩ := SourceDependencyNeutral.resume_transport changed access
    exact .resume nextAccess (ih original .nil after .nil related .refl)
  · intros
    rename_i located known permission available unprotected callbacks waiting ihCallbacks ihWaiting nextScope hints next changed
    obtain ⟨selected, found, same⟩ := annotated_owner (hints := hints) located
    cases same
    obtain ⟨nextSelected, foundNext, related⟩ := changed.find_owner found
    have savedSame : selected.scopes.captured = nextSelected.scopes.captured := by cases related; rfl
    have savedExpansion : Expansion selected.saved nextSelected.saved := by cases related; exact .refl
    rename_i owner _ _ _ _
    have waitingExpansion : Expansion (selected.front.append (.spent (owner := owner) selected.tail))
        (nextSelected.front.append (.spent (owner := owner) nextSelected.tail)) := by
      cases related with
      | pieces front tail => exact front.append (.spent tail)
    apply Local.dispose (SourceContextualInvocationHints.selected_cut foundNext) known permission available
      (savedSame ▸ unprotected)
    · exact ihCallbacks selected.saved (.running (selected.front.append (.spent selected.tail)))
        nextSelected.saved (.running (nextSelected.front.append (.spent nextSelected.tail)))
        savedExpansion (.running waitingExpansion)
    · exact ihWaiting (selected.front.append (.spent selected.tail)) .nil
        (nextSelected.front.append (.spent nextSelected.tail)) .nil waitingExpansion .refl
  · intros
    rename_i first second ihFirst ihSecond nextScope hints next changed
    exact .sequence (ihFirst (.plain hints) (.plain next) (.plain changed)) (ihSecond hints next changed)
  · intros
    rename_i first second ihFirst ihSecond nextScope hints next changed
    exact .choice (ihFirst hints next changed) (ihSecond hints next changed)
  · intros
    rename_i body ih nextScope hints next changed
    exact .handler (ih (.handler [] hints) (.handler [] next) (.handler changed))
  · intros
    rename_i body completion ihBody ihCompletion nextScope hints next changed
    exact .cleanup (ihBody (.cleanup hints) (.cleanup next) (.cleanup changed))
      (ihCompletion (.running hints) (.running next) (.running changed))
  · intros
    rename_i body ih nextScope hints next changed
    exact .resource (fun identity fresh => ih identity fresh (.cell hints) (.cell next) (.cell changed))
  · intros
    rename_i nextScope nextOutside hints outsideHints next nextOutsideHints changed outsideChanged
    cases hints
    induction next <;> cases changed
    all_goals first
      | exact .nil
      | (rename_i ihExtra extra; exact .plain .pure (ihExtra extra))
      | (rename_i ihHistory history; exact .spent (ihHistory history))
      | (rename_i ihCompletion completion; exact .cleanup .pure (ihCompletion completion))
  · intros
    rename_i code tail ihCode ihTail nextScope nextOutside hints outsideHints next nextOutsideHints changed outsideChanged
    cases hints with | plain rest =>
      induction next <;> cases changed
      all_goals first
        | (rename_i ihExtra extra; exact .plain .pure (ihExtra extra))
        | (rename_i ihHistory history; exact .spent (ihHistory history))
        | (rename_i ihCompletion completion; exact .cleanup .pure (ihCompletion completion))
        | (apply Pending.plain
           · exact ihCode (rest.append outsideHints) _ (Expansion.append (by first | exact .refl | assumption) outsideChanged)
           · exact ihTail rest outsideHints _ nextOutsideHints (by first | exact .refl | assumption) outsideChanged)
  · intros
    rename_i tail ih nextScope nextOutside hints outsideHints next nextOutsideHints changed outsideChanged
    cases hints with | handler required rest =>
      induction next <;> cases changed
      all_goals first
        | (rename_i ihExtra extra; exact .plain .pure (ihExtra extra))
        | (rename_i ihHistory history; exact .spent (ihHistory history))
        | (rename_i ihCompletion completion; exact .cleanup .pure (ihCompletion completion))
        | exact .handler (ih rest outsideHints _ nextOutsideHints (by first | exact .refl | assumption) outsideChanged)
  · intros
    rename_i tail ih nextScope nextOutside hints outsideHints next nextOutsideHints changed outsideChanged
    cases hints with | cell rest =>
      induction next <;> cases changed
      all_goals first
        | (rename_i ihExtra extra; exact .plain .pure (ihExtra extra))
        | (rename_i ihHistory history; exact .spent (ihHistory history))
        | (rename_i ihCompletion completion; exact .cleanup .pure (ihCompletion completion))
        | exact .cell (ih rest outsideHints _ nextOutsideHints (by first | exact .refl | assumption) outsideChanged)
  · intros
    rename_i completion tail ihCompletion ihTail nextScope nextOutside hints outsideHints next nextOutsideHints changed outsideChanged
    cases hints with | cleanup rest =>
      induction next <;> cases changed
      all_goals first
        | (rename_i ihExtra extra; exact .plain .pure (ihExtra extra))
        | (rename_i ihHistory history; exact .spent (ihHistory history))
        | (rename_i ihExtra extra; exact .cleanup .pure (ihExtra extra))
        | (apply Pending.cleanup
           · exact ihCompletion (.running (rest.append outsideHints)) _
               (.running (Expansion.append (by first | exact .refl | assumption) outsideChanged))
           · exact ihTail rest outsideHints _ nextOutsideHints (by first | exact .refl | assumption) outsideChanged)
  · intros
    rename_i tail ih nextScope nextOutside hints outsideHints next nextOutsideHints changed outsideChanged
    cases hints with | running rest =>
      induction next <;> cases changed
      all_goals first
        | (rename_i ihExtra extra; exact .plain .pure (ihExtra extra))
        | (rename_i ihHistory history; exact .spent (ihHistory history))
        | (rename_i ihCompletion completion; exact .cleanup .pure (ihCompletion completion))
        | exact .running (ih rest outsideHints _ nextOutsideHints (by first | exact .refl | assumption) outsideChanged)
  · intros
    rename_i saved tail ihSaved ihTail nextScope nextOutside hints outsideHints next nextOutsideHints changed outsideChanged
    cases hints with | live savedHints rest =>
      induction next <;> cases changed
      all_goals first
        | (rename_i ihExtra extra; exact .plain .pure (ihExtra extra))
        | (rename_i ihHistory history; exact .spent (ihHistory history))
        | (rename_i ihCompletion completion; exact .cleanup .pure (ihCompletion completion))
        | exact .live (ihSaved savedHints (rest.append outsideHints) _ _ .refl
            (Expansion.append (by first | exact .refl | assumption) outsideChanged))
            (ihTail rest outsideHints _ nextOutsideHints (by first | exact .refl | assumption) outsideChanged)
  · intros
    rename_i tail ih nextScope nextOutside hints outsideHints next nextOutsideHints changed outsideChanged
    cases hints with | spent rest =>
      induction next <;> cases changed
      all_goals first
        | (rename_i ihExtra extra; exact .plain .pure (ihExtra extra))
        | (rename_i ihHistory history; exact .spent (ihHistory history))
        | (rename_i ihCompletion completion; exact .cleanup .pure (ihCompletion completion))
        | exact .spent (ih rest outsideHints _ nextOutsideHints (by first | exact .refl | assumption) outsideChanged)

  · intros
    rename_i nextScope nextOutside hints outsideHints next nextOutsideHints changed outsideChanged
    cases hints
    induction next <;> cases changed
    all_goals first
      | exact .nil
      | (rename_i ihExtra extra; exact .plain (ihExtra extra))
      | (rename_i ihHistory history; exact .spent (ihHistory history))
      | (rename_i ihCompletion completion; exact .cleanup .pure (ihCompletion completion))
  · intros
    rename_i tail ih nextScope nextOutside hints outsideHints next nextOutsideHints changed outsideChanged
    cases hints with | plain rest =>
      induction next <;> cases changed
      all_goals first
        | (rename_i ihExtra extra; exact .plain (ihExtra extra))
        | (rename_i ihHistory history; exact .spent (ihHistory history))
        | (rename_i ihCompletion completion; exact .cleanup .pure (ihCompletion completion))
        | exact .plain (ih rest outsideHints _ nextOutsideHints (by first | exact .refl | assumption) outsideChanged)
  · intros
    rename_i tail ih nextScope nextOutside hints outsideHints next nextOutsideHints changed outsideChanged
    cases hints with | handler required rest =>
      induction next <;> cases changed
      all_goals first
        | (rename_i ihExtra extra; exact .plain (ihExtra extra))
        | (rename_i ihHistory history; exact .spent (ihHistory history))
        | (rename_i ihCompletion completion; exact .cleanup .pure (ihCompletion completion))
        | exact .handler (ih rest outsideHints _ nextOutsideHints (by first | exact .refl | assumption) outsideChanged)
  · intros
    rename_i tail ih nextScope nextOutside hints outsideHints next nextOutsideHints changed outsideChanged
    cases hints with | cell rest =>
      induction next <;> cases changed
      all_goals first
        | (rename_i ihExtra extra; exact .plain (ihExtra extra))
        | (rename_i ihHistory history; exact .spent (ihHistory history))
        | (rename_i ihCompletion completion; exact .cleanup .pure (ihCompletion completion))
        | exact .cell (ih rest outsideHints _ nextOutsideHints (by first | exact .refl | assumption) outsideChanged)
  · intros
    rename_i completion tail ihCompletion ihTail nextScope nextOutside hints outsideHints next nextOutsideHints changed outsideChanged
    cases hints with | cleanup rest =>
      induction next <;> cases changed
      all_goals first
        | (rename_i ihExtra extra; exact .plain (ihExtra extra))
        | (rename_i ihHistory history; exact .spent (ihHistory history))
        | (rename_i ihExtra extra; exact .cleanup .pure (ihExtra extra))
        | (apply Unwind.cleanup
           · exact ihCompletion (.running (rest.append outsideHints)) _
               (.running (Expansion.append (by first | exact .refl | assumption) outsideChanged))
           · exact ihTail rest outsideHints _ nextOutsideHints (by first | exact .refl | assumption) outsideChanged)
  · intros
    rename_i tail ih nextScope nextOutside hints outsideHints next nextOutsideHints changed outsideChanged
    cases hints with | running rest =>
      induction next <;> cases changed
      all_goals first
        | (rename_i ihExtra extra; exact .plain (ihExtra extra))
        | (rename_i ihHistory history; exact .spent (ihHistory history))
        | (rename_i ihCompletion completion; exact .cleanup .pure (ihCompletion completion))
        | exact .running (ih rest outsideHints _ nextOutsideHints (by first | exact .refl | assumption) outsideChanged)
  · intros
    rename_i saved tail ihSaved ihTail nextScope nextOutside hints outsideHints next nextOutsideHints changed outsideChanged
    cases hints with | live savedHints rest =>
      induction next <;> cases changed
      all_goals first
        | (rename_i ihExtra extra; exact .plain (ihExtra extra))
        | (rename_i ihHistory history; exact .spent (ihHistory history))
        | (rename_i ihCompletion completion; exact .cleanup .pure (ihCompletion completion))
        | exact .live (ihSaved savedHints (.running (rest.append outsideHints)) _ _ .refl
            (.running (Expansion.append (by first | exact .refl | assumption) outsideChanged)))
            (ihTail rest outsideHints _ nextOutsideHints (by first | exact .refl | assumption) outsideChanged)
  · intros
    rename_i tail ih nextScope nextOutside hints outsideHints next nextOutsideHints changed outsideChanged
    cases hints with | spent rest =>
      induction next <;> cases changed
      all_goals first
        | (rename_i ihExtra extra; exact .plain (ihExtra extra))
        | (rename_i ihHistory history; exact .spent (ihHistory history))
        | (rename_i ihCompletion completion; exact .cleanup .pure (ihCompletion completion))
        | exact .spent (ih rest outsideHints _ nextOutsideHints (by first | exact .refl | assumption) outsideChanged)


open ScopedExecution SourceDependencyAnnotations SourceDependencyFrames
open RecursiveRequirements (Requirements evaluate)

theorem focus_dependencies_checked
    (shape : FocusDependencies whole child rest)
    (checked : Local outward actions phases world whole scope) :
    Local outward actions phases world child (.plain rest scope) ∧
      Local outward actions phases world rest scope := by
  cases shape with
  | direct => exact Local.sequence_iff.mp checked
  | purePair => exact ⟨.pure, .pure⟩
  | leftValue silent =>
      have next := (Local.silent_prefix silent).mp checked
      exact ⟨local_transport next (hints := bare scope) (.extra .refl), .pure⟩
  | functionValue silent => exact Local.sequence_iff.mp ((Local.silent_prefix silent).mp checked)

/-- Plugging an evaluated value requires only the waiting code's existing
    check. Its silent prefix cannot introduce an operation, invocation or cleanup. -/
theorem plug_dependencies_checked
    (shape : FocusDependencies whole child rest) (silent : child.Silent)
    (checked : Local outward actions phases world rest scope) :
    Local outward actions phases world whole scope := by
  cases shape with
  | direct => exact .sequence (.silent silent) checked
  | purePair => exact .pure
  | leftValue valueSilent => exact .sequence (.silent valueSilent) (.silent silent)
  | functionValue valueSilent => exact .sequence (.silent valueSilent) (.sequence (.silent silent) checked)

theorem substitution_preserves_local
    (source : Expression operations policy contracts world allowed lexical (environment.extend name input)
      code result demand requirements dependencies)
    (replacement : ValueSummary operations policy contracts world environment allowed value input)
    (closed : ClosedValue value)
    (checked : Local outward actions phases world dependencies receiving) :
    Expression operations policy contracts world allowed lexical environment (code.subst name value)
      result demand requirements dependencies ∧ Local outward actions phases world dependencies receiving :=
  ⟨SourceDependencyAnnotations.substitution source replacement closed, checked⟩

/-- Bind removes only a silent initializer. The exact remaining source,
contextual check and old requirement evaluation all follow existing lemmas. -/
theorem bind_preserves_local
    (source : Expression operations policy contracts world allowed lexical environment (.bind name value body)
      result demand requirements dependencies)
    (closed : ClosedValue value)
    (checked : Local outward actions phases world dependencies receiving) :
    ∃ (reduced : Requirements demand) (remaining : Dependencies),
      Expression operations policy contracts world allowed lexical environment (body.subst name value)
        result demand reduced remaining ∧ Local outward actions phases world remaining receiving ∧
      (∃ initial, dependencies = .sequence initial remaining ∧ initial.Silent) ∧
      ∀ store context before, evaluate store context before reduced = evaluate store context before requirements := by
  obtain ⟨reduced, remaining, next, ⟨initial, same, silent⟩, evaluation⟩ :=
    SourceDependencyAnnotations.bind_expression source closed
  subst dependencies
  exact ⟨reduced, remaining, next, (Local.silent_prefix silent).mp checked, ⟨initial, rfl, silent⟩, evaluation⟩

/-- Beta exposes the function's retained latent tree. Its function and
argument prefixes are silent; its lexical scope follows the existing rule. -/
theorem beta_preserves_local
    (source : Expression operations policy contracts world allowed lexical environment (.app (.lambda name body) value)
      result demand requirements dependencies)
    (closed : ClosedValue value)
    (checked : Local outward actions phases world dependencies receiving) :
    ∃ (reduced : Requirements demand) (remaining : Dependencies),
      Expression operations policy contracts world allowed .none environment (body.subst name value)
        result demand reduced remaining ∧ Local outward actions phases world remaining receiving ∧
      (∃ function argument, dependencies = .sequence function (.sequence argument remaining) ∧ function.Silent ∧ argument.Silent) ∧
      ∀ store context before, evaluate store context before reduced = evaluate store context before requirements := by
  obtain ⟨reduced, remaining, next, ⟨function, argument, same, functionSilent, argumentSilent⟩, evaluation⟩ :=
    SourceDependencyAnnotations.beta_expression source closed
  subst dependencies
  exact ⟨reduced, remaining, next,
    (Local.silent_prefix argumentSilent).mp ((Local.silent_prefix functionSilent).mp checked), ⟨function, argument, rfl, functionSilent, argumentSilent⟩, evaluation⟩


open RecursiveRequirements (Checked)

/-- Selecting either branch retains its contextual check and owner demand.
The existing choice decomposition supplies the checked row inclusion. -/
theorem branch_preserves_local
    (source : Expression operations policy contracts world allowed lexical environment (.branch (.boolean flag) yes no)
      result demand requirements dependencies)
    (checked : Local outward actions phases world dependencies receiving) :
    ∃ (remaining : List Nat) (reduced : Requirements remaining) (nextDependencies : Dependencies),
      Expression operations policy contracts world allowed lexical environment (if flag then yes else no)
        result remaining reduced nextDependencies ∧ Local outward actions phases world nextDependencies receiving ∧
      demand.Perm remaining ∧
      ∀ store context before row, Checked store context before requirements row →
        ∃ nextRow, Checked store context before reduced nextRow ∧ nextRow.Sublist row := by
  cases source with
  | branch condition yesSource noSource same =>
      cases condition with
      | boolean =>
          obtain ⟨_, branches⟩ := Local.sequence_iff.mp checked
          cases branches with
          | choice yesChecked noChecked =>
              cases flag with
              | false =>
                  refine ⟨_, _, _, noSource, noChecked, same, ?_⟩
                  intro store context before row checkedRow
                  have evaluated := RecursiveRequirements.checked_complete checkedRow
                  rw [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.evaluate_empty,
                    RecursiveRecomposition.merge_empty_left] at evaluated
                  obtain ⟨firstRow, secondRow, left, right, rfl⟩ :=
                    RecursiveExpressions.choice_parts (RecursiveRequirements.evaluate_sound evaluated)
                  exact ⟨secondRow, right, List.sublist_append_right _ _⟩
              | true =>
                  refine ⟨_, _, _, yesSource, yesChecked, .refl _, ?_⟩
                  intro store context before row checkedRow
                  have evaluated := RecursiveRequirements.checked_complete checkedRow
                  rw [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.evaluate_empty,
                    RecursiveRecomposition.merge_empty_left] at evaluated
                  obtain ⟨firstRow, secondRow, left, right, rfl⟩ :=
                    RecursiveExpressions.choice_parts (RecursiveRequirements.evaluate_sound evaluated)
                  exact ⟨firstRow, left, List.sublist_append_left _ _⟩

open SourceDependencySchemes.Closing (Bound)

/-- The same chosen runtime frame retains rich source typing, the lexical
checks and the complete expression/stack annotation. The old annotation remains
an exact subtree, and plain-frame insertion preserves its cleanup source. -/
theorem focus_preserves_source
    (current : Expression operations policy contracts world allowed runtimeScope Environment.empty
      whole input currentDemand currentRequirements dependencies)
    (pending : ModeSource operations policy contracts tables families actions world
      stack (.value input) output pendingDemand pendingRequirements dependencyScope)
    (scopeTyped : ScopedPorts.EffectScope contracts.erase.ports runtimeScope ticket)
    (position : Focus whole child context)
    (checked : Local outward actions phases world dependencies dependencyScope)
    (retained : SourceDependencyChecks.Lexical.ModePending outward actions phases world tables families
      stack dependencyScope .nil .ordinary output.mode)
    (annotationBound : Bound annotations dependencyScope)
    (annotation : RowAnnotation
      (.sequence (currentRequirements.prepend (OwnerPhases.ofStack tables stack)) pendingRequirements)
      annotatedRequirements)
    (rowChecked : RecursiveRequirements.Checked entries receiving before annotatedRequirements row) :
    ∃ (plain : PlainData) (nextInput : Value) (childDemand restDemand : List Nat),
    ∃ childRequirements : Requirements childDemand,
    ∃ nextRequirements : Requirements (restDemand ++ pendingDemand),
    ∃ childDependencies restDependencies,
    ∃ nextAnnotated : Requirements (childDemand ++ (restDemand ++ pendingDemand)), ∃ nextRow,
      plain.context = context ∧ plain.scope = runtimeScope ∧
      Expression operations policy contracts world allowed runtimeScope Environment.empty
        child nextInput childDemand childRequirements childDependencies ∧
      ModeSource operations policy contracts tables families actions world
        (.push (.plain plain) stack) (.value nextInput) output (restDemand ++ pendingDemand)
        nextRequirements (.plain restDependencies dependencyScope) ∧
      currentDemand = childDemand ++ restDemand ∧
      FocusDependencies dependencies childDependencies restDependencies ∧
      RequirementPath childRequirements currentRequirements [] ∧
      (∀ closeDemand (closeRequirements : Requirements closeDemand),
        UnwindSource operations policy contracts tables families world stack closeDemand closeRequirements dependencyScope ↔
        UnwindSource operations policy contracts tables families world (.push (.plain plain) stack)
          closeDemand closeRequirements (.plain restDependencies dependencyScope)) ∧
      RowAnnotation
        (.sequence (childRequirements.prepend (OwnerPhases.ofStack tables (.push (.plain plain) stack))) nextRequirements)
        nextAnnotated ∧
      RequirementPath annotatedRequirements nextAnnotated [] ∧
      RecursiveRequirements.Checked entries receiving before nextAnnotated nextRow ∧
      nextRow ⊆ row ∧
      Local outward actions phases world childDependencies (.plain restDependencies dependencyScope) ∧
      SourceDependencyChecks.Lexical.ModePending outward actions phases world tables families
        (.push (.plain plain) stack) (.plain restDependencies dependencyScope) .nil .ordinary output.mode ∧
      Bound annotations (.plain restDependencies dependencyScope) ∧
      LexicalUnwind.UseTransition (.eval ⟨whole, runtimeScope, stack⟩)
        (.eval ⟨child, runtimeScope, .push (.plain plain) stack⟩) [] [] := by
  obtain ⟨plain, nextInput, childDemand, restDemand, childRequirements, nextRequirements,
    childDependencies, restDependencies, contextSame, scopeSame, childSource, pendingSource,
    sameDemand, shape, path, evaluation, step⟩ := mode_focus_source current pending scopeTyped position
  have aligned : (childDemand ++ (restDemand ++ pendingDemand)).Perm (currentDemand ++ pendingDemand) := by
    simpa only [sameDemand, List.append_assoc] using
      (List.Perm.refl (childDemand ++ (restDemand ++ pendingDemand)))
  obtain ⟨nextAnnotation, previousPath, nextRow, nextCheck, nextBound⟩ :=
    annotation.rebase_checked aligned (evaluation entries receiving before) rowChecked
  obtain ⟨childCheck, restCheck⟩ := focus_dependencies_checked shape checked
  exact ⟨plain, nextInput, childDemand, restDemand, childRequirements, nextRequirements,
    childDependencies, restDependencies, _, nextRow, contextSame, scopeSame, childSource, pendingSource,
    sameDemand, shape, path,
    (fun _ _ => ⟨fun cleanup => .plain cleanup, fun cleanup => by cases cleanup with | plain rest => exact rest⟩),
    nextAnnotation, previousPath, nextCheck, nextBound, childCheck,
    .push (.plain (by simpa only [SourceDependencyProjection.scope_append_nil] using restCheck)) retained,
    .plain annotationBound, step⟩

/-- Returning a value restores the exact waiting source context and retains
the complete expression/stack certificate. Popping the plain frame changes no
cleanup requirement; latent values reuse the existing plug proof. -/
theorem plug_preserves_source
    (current : Expression operations policy contracts world allowed runtimeScope Environment.empty
      value input currentDemand currentRequirements dependencies)
    (pending : ModeSource operations policy contracts tables families actions world
      (.push (.plain plain) tail) (.value input) output pendingDemand pendingRequirements dependencyScope)
    (closed : ClosedValue value)
    (retained : SourceDependencyChecks.Lexical.ModePending outward actions phases world tables families
      (.push (.plain plain) tail) dependencyScope .nil .ordinary output.mode)
    (annotationBound : Bound annotations dependencyScope)
    (annotation : RowAnnotation
      (.sequence (currentRequirements.prepend (OwnerPhases.ofStack tables (.push (.plain plain) tail))) pendingRequirements)
      annotatedRequirements)
    (rowChecked : RecursiveRequirements.Checked entries receiving before annotatedRequirements row) :
    ∃ (nextInput : Value) (frameDemand tailDemand : List Nat),
    ∃ nextRequirements : Requirements frameDemand, ∃ tailRequirements : Requirements tailDemand,
    ∃ nextDependencies restDependencies restScope boundary,
    ∃ nextAnnotated : Requirements (frameDemand ++ tailDemand), ∃ nextRow,
      dependencyScope = .plain restDependencies restScope ∧
      currentDemand = [] ∧ pendingDemand = frameDemand ++ tailDemand ∧
      Expression operations policy contracts world boundary plain.scope Environment.empty
        (plain.context.plug value) nextInput frameDemand nextRequirements nextDependencies ∧
      ModeSource operations policy contracts tables families actions world
        tail (.value nextInput) output tailDemand tailRequirements restScope ∧
      FocusDependencies nextDependencies .pure restDependencies ∧
      (∀ closeDemand (closeRequirements : Requirements closeDemand),
        UnwindSource operations policy contracts tables families world (.push (.plain plain) tail)
          closeDemand closeRequirements dependencyScope ↔
        UnwindSource operations policy contracts tables families world tail closeDemand closeRequirements restScope) ∧
      RowAnnotation
        (.sequence (nextRequirements.prepend (OwnerPhases.ofStack tables tail)) tailRequirements) nextAnnotated ∧
      RequirementPath annotatedRequirements nextAnnotated [] ∧
      RecursiveRequirements.Checked entries receiving before nextAnnotated nextRow ∧
      nextRow ⊆ row ∧
      Local outward actions phases world nextDependencies restScope ∧
      SourceDependencyChecks.Lexical.ModePending outward actions phases world tables families
        tail restScope .nil .ordinary output.mode ∧
      Bound annotations restScope ∧
      LexicalUnwind.UseTransition (.eval ⟨value, runtimeScope, .push (.plain plain) tail⟩)
        (.eval ⟨plain.context.plug value, plain.scope, tail⟩) [] [] := by
  obtain ⟨nextInput, frameDemand, tailDemand, nextRequirements, tailRequirements,
    nextDependencies, restDependencies, restScope, boundary, scopeSame, empty, sameDemand,
    source, suffix, shape, evaluation, step⟩ := mode_plug_source current pending closed
  have aligned : (frameDemand ++ tailDemand).Perm (currentDemand ++ pendingDemand) := by
    simpa only [empty, sameDemand, List.nil_append] using (List.Perm.refl (frameDemand ++ tailDemand))
  obtain ⟨nextAnnotation, previousPath, nextRow, nextCheck, nextBound⟩ :=
    annotation.rebase_checked aligned (evaluation entries receiving before) rowChecked
  subst dependencyScope
  obtain ⟨checkedDependencies, checkedScope, sameScope, waiting, rest⟩ := retained.pop_plain
  cases sameScope
  have checked : Local outward actions phases world nextDependencies restScope :=
    plug_dependencies_checked shape .pure
      (by simpa only [SourceDependencyProjection.scope_append_nil] using waiting)
  exact ⟨nextInput, frameDemand, tailDemand, nextRequirements, tailRequirements,
    nextDependencies, restDependencies, restScope, boundary, _, nextRow, rfl, empty, sameDemand,
    source, suffix, shape,
    (fun _ _ => ⟨(fun cleanup => by cases cleanup with | plain rest => exact rest), fun cleanup => .plain cleanup⟩),
    nextAnnotation, previousPath, nextCheck, nextBound, checked, rest, (by cases annotationBound with | plain bound => exact bound), step⟩

#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.focus_dependencies_checked
#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.plug_dependencies_checked
#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.substitution_preserves_local
#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.bind_preserves_local
#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.beta_preserves_local
#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.branch_preserves_local
#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.focus_preserves_source
#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.plug_preserves_source
#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.local_transport
end Ash.OneShot.SourceDependencyNeutral.Lexical


namespace Ash.OneShot.SourceDependencyNeutral.Lexical
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations SourceDependencyFrames
open SourceDependencyChecks.Lexical (Local Pending ModeFrame ModePending)
open SourceDependencySchemes.Closing (Bound)
open RecursiveRequirements (Requirements)

/-- Changing registries only away from this frame's installed handler keeps
    its rich source and dependency-scope annotation unchanged. -/
theorem source_frame_registries
    (frame : SourceDependencyFrames.Frame operations policy contracts tables families world
      entry input output demand requirements layer incoming outgoing)
    (tableAgree : ∀ handler, handler.activation ∈ entry.erase.activation → tables handler = nextTables handler)
    (familyAgree : ∀ handler, handler.activation ∈ entry.erase.activation → families handler = nextFamilies handler) :
    SourceDependencyFrames.Frame operations policy contracts nextTables nextFamilies world
      entry input output demand requirements layer incoming outgoing := by
  cases frame with
  | plain context scope inputAnnotation outputAnnotation => exact .plain context scope inputAnnotation outputAnnotation
  | handler scope annotation clauses coverage unique declarations capabilities modes =>
      have tableSame := tableAgree _ List.mem_cons_self
      have familySame := familyAgree _ List.mem_cons_self
      simpa only [tableSame, familySame] using
        (SourceDependencyFrames.Frame.handler (tables := nextTables) (families := nextFamilies)
          scope annotation clauses coverage unique
          (by simpa only [tableSame, familySame] using declarations) capabilities
          (by simpa only [tableSame] using modes))
  | cell scope noEscape annotation interface => exact .cell scope noEscape annotation interface
  | armed scope callback annotation interface => exact .armed scope callback annotation interface
  | running scope callback saved annotation interface => exact .running scope callback saved annotation interface
  | closing scope interface => exact .closing scope interface
  | retiring known interface => exact .retiring known interface

/-- Registry transport retains the frame's actual execution mode and its
original source witness, including handlers crossed during unwinding. -/
theorem frame_registries
    (frame : ModeSourceFrame operations policy contracts tables families world
      entry input output demand requirements layer)
    (tableAgree : ∀ handler, handler.activation ∈ entry.erase.activation → tables handler = nextTables handler)
    (familyAgree : ∀ handler, handler.activation ∈ entry.erase.activation → families handler = nextFamilies handler) :
    ModeSourceFrame operations policy contracts nextTables nextFamilies world
      entry input output demand requirements layer := by
  cases frame with
  | ordinary frame => exact .ordinary (source_frame_registries frame tableAgree familyAgree)
  | unwinding callback => exact .unwinding callback
  | closing scope => exact .closing scope
  | retiring => exact .retiring
  | skipped => exact .skipped
  | handler frame =>
      have tableSame := tableAgree _ List.mem_cons_self
      have familySame := familyAgree _ List.mem_cons_self
      have changed := source_frame_registries frame tableAgree familyAgree
      simpa only [tableSame, familySame] using
        (ModeSourceFrame.handler (tables := nextTables) (families := nextFamilies)
          (by simpa only [tableSame, familySame] using changed))
  | cell => exact .cell
  | cleanup callback => exact .cleanup callback

/-- Fresh installation preserves source annotations in both active and dormant
segments. Only tables for installations absent from the stack may change. -/
theorem segment_registries
    (segment : ModeSource operations policy contracts tables families actions world
      stack input output demand requirements dependencyScope)
    (tableAgree : ∀ handler, handler.activation ∈ stack.erase.activations → tables handler = nextTables handler)
    (familyAgree : ∀ handler, handler.activation ∈ stack.erase.activations → families handler = nextFamilies handler) :
    ModeSource operations policy contracts nextTables nextFamilies actions world
      stack input output demand requirements dependencyScope := by
  induction segment with
  | nil => exact .nil
  | push head tail ih =>
      have next := fun handler member => tableAgree handler (List.mem_append_right _ member)
      have same := RecursiveHandlerTables.context_congr next
      have changed := frame_registries head
        (fun handler member => tableAgree handler (List.mem_append_left _ member))
        (fun handler member => familyAgree handler (List.mem_append_left _ member))
      simpa only [same] using ModeSource.push changed
        (ih next (fun handler member => familyAgree handler (List.mem_append_right _ member)))
  | live known actionKnown inputAnnotation answerAnnotation scope held saved answer tail ihSaved ihTail =>
      exact .live known actionKnown inputAnnotation answerAnnotation scope held
        (ihSaved (fun handler member => tableAgree handler (List.mem_append_left _ member))
          (fun handler member => familyAgree handler (List.mem_append_left _ member))) answer
        (ihTail (fun handler member => tableAgree handler (List.mem_append_right _ member))
          (fun handler member => familyAgree handler (List.mem_append_right _ member)))
  | @opening captured savedDemand savedRequirements savedScope rest output tailDemand tailRequirements restScope owner input answer caller saved tail ihSaved ihTail =>
      have next := fun handler member => tableAgree handler (List.mem_append_right _ member)
      have same := RecursiveHandlerTables.context_congr (stack := .push (.retiring owner) rest) next
      simpa only [same] using ModeSource.opening
        (ihSaved (fun handler member => tableAgree handler (List.mem_append_left _ member))
          (fun handler member => familyAgree handler (List.mem_append_left _ member)))
        (ihTail next (fun handler member => familyAgree handler (List.mem_append_right _ member)))
  | spent known annotation scope tail ih => exact .spent known annotation scope (ih tableAgree familyAgree)
  | skippedSpent tail ih => exact .skippedSpent (ih tableAgree familyAgree)

open SourceDependencyChecks.Lexical (ModeFrame ModePending)

/-- Pending code retains the same checked receiving scope after an unrelated
fresh handler installation. -/
theorem mode_frame_registries
    (frame : ModeFrame outward actions phases world tables families outside entry layer input output)
    (tableAgree : ∀ handler, handler.activation ∈ entry.erase.activation → tables handler = nextTables handler)
    (familyAgree : ∀ handler, handler.activation ∈ entry.erase.activation → families handler = nextFamilies handler) :
    ModeFrame outward actions phases world nextTables nextFamilies outside entry layer input output := by
  cases frame with
  | plain code => exact .plain code
  | skipped => exact .skipped
  | handler =>
      have tableSame := tableAgree _ List.mem_cons_self
      have familySame := familyAgree _ List.mem_cons_self
      simpa only [tableSame, familySame] using
        (ModeFrame.handler (outward := outward) (actions := actions) (phases := phases)
          (world := world) (tables := nextTables) (families := nextFamilies) (outside := outside))
  | cell => exact .cell
  | armed callback => exact .armed callback
  | running => exact .running
  | unwinding => exact .unwinding
  | closing => exact .closing
  | retiring => exact .retiring

theorem mode_pending_registries
    (pending : ModePending outward actions phases world tables families stack scope outside input output)
    (tableAgree : ∀ handler, handler.activation ∈ stack.erase.activations → tables handler = nextTables handler)
    (familyAgree : ∀ handler, handler.activation ∈ stack.erase.activations → families handler = nextFamilies handler) :
    ModePending outward actions phases world nextTables nextFamilies stack scope outside input output := by
  induction pending with
  | nil => exact .nil
  | push frame tail ih =>
      exact .push (mode_frame_registries frame
        (fun handler member => tableAgree handler (List.mem_append_left _ member))
        (fun handler member => familyAgree handler (List.mem_append_left _ member)))
        (ih (fun handler member => tableAgree handler (List.mem_append_right _ member))
          (fun handler member => familyAgree handler (List.mem_append_right _ member)))
  | live saved tail ihSaved ihTail | opening saved tail ihSaved ihTail =>
      first
      | exact .live
          (ihSaved (fun handler member => tableAgree handler (List.mem_append_left _ member))
            (fun handler member => familyAgree handler (List.mem_append_left _ member)))
          (ihTail (fun handler member => tableAgree handler (List.mem_append_right _ member))
            (fun handler member => familyAgree handler (List.mem_append_right _ member)))
      | exact .opening
          (ihSaved (fun handler member => tableAgree handler (List.mem_append_left _ member))
            (fun handler member => familyAgree handler (List.mem_append_left _ member)))
          (ihTail (fun handler member => tableAgree handler (List.mem_append_right _ member))
            (fun handler member => familyAgree handler (List.mem_append_right _ member)))
  | spent tail ih => exact .spent (ih tableAgree familyAgree)

/-- Reuse local world weakening; no callback or ordinary-code typing induction
is repeated when a fresh resource is installed. -/
theorem mode_pending_world
    (pending : ModePending outward actions phases world tables families stack scope outside input output)
    (larger : world ⊆ nextWorld) :
    ModePending outward actions phases nextWorld tables families stack scope outside input output := by
  induction pending with
  | nil => exact .nil
  | push frame tail ih =>
      apply ModePending.push (tail := ih)
      cases frame with
      | plain code => exact .plain (code.world_weaken larger)
      | skipped => exact .skipped
      | handler => exact .handler
      | cell => exact .cell
      | armed callback => exact .armed (callback.world_weaken larger)
      | running => exact .running
      | unwinding => exact .unwinding
      | closing => exact .closing
      | retiring => exact .retiring
  | live saved tail ihSaved ihTail => exact .live ihSaved ihTail
  | opening saved tail ihSaved ihTail => exact .opening ihSaved ihTail
  | spent tail ih => exact .spent ih

/-- Invert a checked frame before equating its concrete scope constructor.
This retains the actual mode boundary without assuming annotation uniqueness. -/
theorem mode_pending_pop
    (pending : ModePending outward actions phases world tables families
      (.push entry rest) scope outside input output) :
    ∃ layer restScope middle,
      ModeFrame outward actions phases world tables families (restScope.append outside) entry layer input middle ∧
      ModePending outward actions phases world tables families rest restScope outside middle output ∧
      scope = layer restScope := by
  cases pending with
  | push frame tail => exact ⟨_, _, _, frame, tail, rfl⟩

/-- Register the actual callback value with its rich dependencies and exact
    lexical suffix. The owner identity is chosen here; event freshness remains
    the independent allocation check. -/
theorem enter_cleanup_source
    (current : Expression operations policy contracts world allowed runtimeScope Environment.empty
      (.cleanup callback body) input currentDemand currentRequirements dependencies)
    (pending : ModeSource operations policy contracts tables families actions world
      stack (.value input) output pendingDemand pendingRequirements dependencyScope)
    (scopeTyped : ScopedPorts.EffectScope contracts.erase.ports runtimeScope ticket)
    (isValue : callback.IsValue)
    (checked : Local outward actions phases world dependencies dependencyScope)
    (retained : ModePending outward actions phases world tables families
      stack dependencyScope .nil .ordinary output.mode)
    (annotationBound : Bound annotations dependencyScope)
    (identity : Nat) :
    ∃ (action : ActionData) (bodyDemand : List Nat), ∃ bodyRequirements : Requirements bodyDemand,
    ∃ nextRequirements : Requirements pendingDemand, ∃ bodyDependencies callbackDependencies,
      action.identity = identity ∧ action.action = callback ∧ currentDemand = bodyDemand ∧
      Expression operations policy contracts world allowed runtimeScope Environment.empty
        body input bodyDemand bodyRequirements bodyDependencies ∧
      ModeSource operations policy contracts tables families actions world
        (.push (.armed action) stack) (.value input) output pendingDemand nextRequirements
        (.cleanup action.requests callbackDependencies dependencyScope) ∧
      Local outward actions phases world bodyDependencies
        (.cleanup action.requests callbackDependencies dependencyScope) ∧
      ModePending outward actions phases world tables families
        (.push (.armed action) stack) (.cleanup action.requests callbackDependencies dependencyScope) .nil .ordinary output.mode ∧
      Bound annotations (.cleanup action.requests callbackDependencies dependencyScope) ∧
      LexicalUnwind.UseTransition (.eval ⟨.cleanup callback body, runtimeScope, stack⟩)
        (.eval ⟨body, runtimeScope, .push (.armed action) stack⟩) [.cleanup identity] [] := by
  cases current with
  | cleanup callbackSource bodySource admitted =>
      rename_i requests latent callbackBody callbackDemand callbackReq callbackDep bodyDemand bodyReq bodyDep
      have summary := Values.change_allowed (Values.summary callbackSource isValue) isValue []
      have ports := (DeclaredSourceValues.erase (value_erase summary)).ports .none
      have closed := ScopedPorts.typed_value_closed ports isValue
      have empty := SourceTemplates.expression_value_demand
        (DeclaredSources.expression_erase (expression_erase callbackSource)) isValue
      let action : ActionData := ⟨identity, callback, closed, runtimeScope, ScopedPorts.embedPort input.erase.port, requests⟩
      have frame : SourceDependencyFrames.Frame operations policy contracts tables families world (.armed action) input input []
          (.request [] (qualify true latent)) (.cleanup requests callbackBody) allowed allowed :=
        .armed ⟨_, ScopedPorts.effect_scope_has_types scopeTyped⟩ summary (by simp [action])
          (.armed ⟨_, scopeTyped⟩ ports admitted)
      obtain ⟨bodyChecked, completion⟩ := Local.cleanup_iff.mp
        ((Local.silent_prefix (value_silent callbackSource isValue)).mp checked)
      refine ⟨action, bodyDemand, bodyReq, _, bodyDep, callbackBody, rfl, rfl,
        by simp only [empty, List.nil_append], bodySource,
        .push (.ordinary frame) pending, bodyChecked,
        .push (.armed (by simpa only [SourceDependencyProjection.scope_append_nil] using completion)) retained, .cleanup annotationBound, ?_⟩
      exact .evaluate (.enterCleanup action body stack) trivial

/-- Normal scope exit saves the actual returned value and starts the same
    source callback under running protection. -/
theorem start_normal_cleanup_source
    (current : Expression operations policy contracts world allowed runtimeScope Environment.empty
      value input currentDemand currentRequirements dependencies)
    (pending : ModeSource operations policy contracts tables families actions world
      (.push (.armed action) tail) (.value input) output pendingDemand pendingRequirements dependencyScope)
    (closed : ClosedValue value)
    (retained : ModePending outward actions phases world tables families
      (.push (.armed action) tail) dependencyScope .nil .ordinary output.mode)
    (annotationBound : Bound annotations dependencyScope) :
    ∃ boundary latent callbackDependencies restScope, ∃ nextRequirements : Requirements pendingDemand,
      currentDemand = [] ∧
      Expression operations policy contracts world boundary .none Environment.empty
        (.app action.action .unit) .unit []
        (.emitAfter (.sequence (.request [] []) (.request [] [])) [] latent)
        (.sequence .pure (.sequence .pure callbackDependencies)) ∧
      ModeSource operations policy contracts tables families actions world
        (.push (.running action value closed) tail) (.value .unit) output pendingDemand nextRequirements
        (.running restScope) ∧
      Local outward actions phases world (.sequence .pure (.sequence .pure callbackDependencies)) (.running restScope) ∧
      ModePending outward actions phases world tables families
        (.push (.running action value closed) tail) (.running restScope) .nil .ordinary output.mode ∧
      Bound annotations (.running restScope) ∧
      LexicalUnwind.UseTransition (.eval ⟨value, runtimeScope, .push (.armed action) tail⟩)
        (.eval ⟨.app action.action .unit, .none, .push (.running action value closed) tail⟩) [] [] := by
  have empty := SourceTemplates.expression_value_demand
    (DeclaredSources.expression_erase (expression_erase current)) closed.1
  have summary := Values.change_allowed (Values.summary current closed.1) closed.1 []
  cases pending with
  | push frame rest => cases frame with
    | ordinary frame => cases frame with
      | armed scope callback annotation interface =>
          obtain ⟨_, _, _, checkedFrame, remaining, scopeSame⟩ := mode_pending_pop retained
          cases checkedFrame with
          | armed completion =>
              cases scopeSame
              cases interface with
              | armed savedScope callable admitted =>
                  have savedTyped : ScopedPorts.Typed operations.erase.ports world ScopedPorts.TypeEnv.empty .none []
                      value (ScopedPorts.eraseType action.answer) := by
                    have environmentSame : Environment.empty.erase.ports = ScopedPorts.TypeEnv.empty := by
                      funext name; rfl
                    simpa only [← annotation, environmentSame] using (DeclaredSourceValues.erase (value_erase summary)).ports .none
                  refine ⟨_, _, _, _, _, empty,
                    .app (Values.change_allowed callback action.closed.1 _) .unit admitted,
                    .push (.ordinary (.running scope callback summary annotation
                      (.running savedScope callable savedTyped admitted))) rest,
                    .sequence .pure (.sequence .pure ?_), .push .running remaining, (by cases annotationBound with | cleanup bound => exact .running bound), ?_⟩
                  · simpa only [SourceDependencyProjection.scope_append_nil] using completion
                  · exact .evaluate (.startCleanup action value closed runtimeScope tail)
                      (by cases value <;> first | trivial | cases closed.1)

/-- A completed normal callback restores its saved rich value and lexical
    scope. The remaining caller is recovered from its existing source frame. -/
theorem finish_normal_cleanup_source
    (pending : ModeSource operations policy contracts tables families actions world
      (.push (.running action value closed) tail) (.value input) output pendingDemand pendingRequirements dependencyScope)
    (retained : ModePending outward actions phases world tables families
      (.push (.running action value closed) tail) dependencyScope .nil .ordinary output.mode)
    (annotationBound : Bound annotations dependencyScope) :
    ∃ nextInput boundary restScope, ∃ nextRequirements : Requirements pendingDemand,
      ScopedPorts.EffectScopeKnown contracts.erase.ports action.scope ∧
      Expression operations policy contracts world boundary action.scope Environment.empty
        value nextInput [] (.request [] []) .pure ∧
      ModeSource operations policy contracts tables families actions world
        tail (.value nextInput) output pendingDemand nextRequirements restScope ∧
      ModePending outward actions phases world tables families
        tail restScope .nil .ordinary output.mode ∧
      Bound annotations restScope ∧
      LexicalUnwind.UseTransition (.eval ⟨.unit, runtimeScope, .push (.running action value closed) tail⟩)
        (.eval ⟨value, action.scope, tail⟩) [] [.cleanup action.identity] := by
  cases pending with
  | push frame rest => cases frame with
    | ordinary frame => cases frame with
      | running scope callback saved annotation interface =>
          obtain ⟨_, _, _, checkedFrame, remaining, scopeSame⟩ := mode_pending_pop retained
          cases checkedFrame with
          | running =>
              cases scopeSame
              cases interface with
              | running savedScope callable result admitted =>
                exact ⟨_, _, _, _, savedScope, Values.change_context saved closed.1 [] action.scope,
                  rest, remaining, (by cases annotationBound with | running bound => exact bound), .evaluate (.finishCleanup action value closed runtimeScope tail) trivial⟩

open ProtectionResiduals
open RecursiveRequirements (Checked)

/-- Leaving an interpretation restores the scope carried by its actual
    installation; the returned value retains its latent source annotations. -/
theorem leave_handler_source
    (current : Expression operations policy contracts world allowed runtimeScope Environment.empty
      value input currentDemand currentRequirements dependencies)
    (pending : ModeSource operations policy contracts tables families actions world
      (.push (.handler handler) tail) (.value input) output pendingDemand pendingRequirements dependencyScope)
    (closed : ClosedValue value)
    (retained : ModePending outward actions phases world tables families
      (.push (.handler handler) tail) dependencyScope .nil .ordinary output.mode)
    (annotationBound : Bound annotations dependencyScope)
    (annotation : RowAnnotation
      (.sequence (currentRequirements.prepend (OwnerPhases.ofStack tables (.push (.handler handler) tail))) pendingRequirements)
      annotatedRequirements)
    (rowChecked : Checked entries receiving before annotatedRequirements row) :
    ∃ boundary restScope, ∃ nextRequirements : Requirements pendingDemand,
    ∃ nextAnnotated : Requirements pendingDemand, ∃ nextRow,
      currentDemand = [] ∧ ScopedPorts.EffectScopeKnown contracts.erase.ports handler.scope ∧
      Expression operations policy contracts world boundary handler.scope Environment.empty
        value input [] (.request [] []) .pure ∧
      ModeSource operations policy contracts tables families actions world
        tail (.value input) output pendingDemand nextRequirements restScope ∧
      ModePending outward actions phases world tables families
        tail restScope .nil .ordinary output.mode ∧
      Bound annotations restScope ∧
      (∀ closeDemand (closeRequirements : Requirements closeDemand),
        UnwindSource operations policy contracts tables families world (.push (.handler handler) tail)
          closeDemand closeRequirements dependencyScope ↔
        UnwindSource operations policy contracts tables families world tail closeDemand closeRequirements restScope) ∧
      RowAnnotation
        (.sequence ((Requirements.request [] []).prepend (OwnerPhases.ofStack tables tail)) nextRequirements) nextAnnotated ∧
      RequirementPath annotatedRequirements nextAnnotated [] ∧
      Checked entries receiving before nextAnnotated nextRow ∧ nextRow ⊆ row ∧
      LexicalUnwind.UseTransition (.eval ⟨value, runtimeScope, .push (.handler handler) tail⟩)
        (.eval ⟨value, handler.scope, tail⟩) [] [] := by
  have empty := SourceTemplates.expression_value_demand
    (DeclaredSources.expression_erase (expression_erase current)) closed.1
  have aligned : pendingDemand.Perm (currentDemand ++ pendingDemand) := by
    simpa only [empty, List.nil_append] using (List.Perm.refl pendingDemand)
  obtain ⟨normalRow, normalCheck, normalBound⟩ := annotation.checked rowChecked
  cases pending with
  | push frame rest => cases frame with
    | ordinary frame => cases frame with
      | handler scope answerAnnotation clauses coverage unique declarations capabilities modes =>
          obtain ⟨_, _, _, checkedFrame, remaining, scopeSame⟩ := mode_pending_pop retained
          cases checkedFrame with
          | handler =>
              cases scopeSame
              refine ⟨_, _, _, _, normalRow ++ row, empty, scope,
                Values.change_context (Values.summary current closed.1) closed.1 [] handler.scope,
                rest, remaining, (by cases annotationBound with | handler bound => exact bound),
                ?_, .alternatives .original aligned, .no .here, .choice ?_ rowChecked,
                List.append_subset.mpr ⟨normalBound, List.Subset.refl _⟩,
                .evaluate (.leaveHandler handler value closed runtimeScope tail)
                  (by cases value <;> first | trivial | cases closed.1)⟩
              · intro closeDemand closeRequirements
                constructor
                · intro cleanup
                  cases cleanup with | handler declaration next => exact next
                · intro cleanup
                  exact .handler (SourceDependencyFrames.Frame.handler scope answerAnnotation clauses coverage unique declarations capabilities modes) cleanup
              · apply RecursiveRequirements.evaluate_sound
                simpa only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
                  RecursiveRecomposition.value_evaluation (DeclaredSources.expression_erase (expression_erase current)) closed.1,
                  RecursiveRecomposition.evaluate_empty, OwnerPhaseTransitions.spendAll, empty,
                  List.nil_append, RecursiveRecomposition.merge_empty_left] using
                  RecursiveRequirements.checked_complete normalCheck


open ProtectionResiduals
open RecursiveRequirements (Checked)

/-- Changing registries outside the installed identities preserves the exact
lexical cleanup source, including dormant captures and callback requirements. -/
theorem unwind_source_registries
    (source : UnwindSource operations policy contracts tables families world stack demand requirements dependencyScope)
    (tableAgree : ∀ handler, handler.activation ∈ stack.erase.activations → tables handler = nextTables handler)
    (familyAgree : ∀ handler, handler.activation ∈ stack.erase.activations → families handler = nextFamilies handler) :
    UnwindSource operations policy contracts nextTables nextFamilies world stack demand requirements dependencyScope := by
  induction source with
  | nil => exact .nil
  | plain tail ih => exact .plain (ih tableAgree familyAgree)
  | handler declaration tail ih =>
      have tablesTail := fun handler member => tableAgree handler (List.mem_append_right _ member)
      have familiesTail := fun handler member => familyAgree handler (List.mem_append_right _ member)
      have tableSame := tableAgree _ List.mem_cons_self
      have familySame := familyAgree _ List.mem_cons_self
      have changed := source_frame_registries declaration
        (fun handler member => tableAgree handler (List.mem_append_left _ member))
        (fun handler member => familyAgree handler (List.mem_append_left _ member))
      simpa only [tableSame, familySame] using
        UnwindSource.handler (tables := nextTables) (families := nextFamilies)
          (by simpa only [tableSame, familySame] using changed) (ih tablesTail familiesTail)
  | cell tail ih => exact .cell (ih tableAgree familyAgree)
  | @cleanup latent dependencies rest demand requirements restScope action callback tail ih =>
      have same := RecursiveHandlerTables.context_congr (stack := rest) tableAgree
      simpa only [same] using UnwindSource.cleanup callback (ih tableAgree familyAgree)
  | @live captured savedDemand savedRequirements savedScope rest tailDemand tailRequirements restScope owner input answer caller saved tail ihSaved ihTail =>
      have tablesTail := fun handler member => tableAgree handler (List.mem_append_right _ member)
      have familiesTail := fun handler member => familyAgree handler (List.mem_append_right _ member)
      have same := RecursiveHandlerTables.context_congr (stack := .push (.retiring owner) rest) tablesTail
      simpa only [same] using UnwindSource.live
        (ihSaved (fun handler member => tableAgree handler (List.mem_append_left _ member))
          (fun handler member => familyAgree handler (List.mem_append_left _ member)))
        (ihTail tablesTail familiesTail)
  | spent tail ih => exact .spent (ih tableAgree familyAgree)
  | retiring tail ih => exact .retiring (ih tableAgree familyAgree)


#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.unwind_source_registries

/-- Choose a fresh handler installation and register its exact source clause
    table and families. Existing captures retain their annotations unchanged. -/
theorem enter_handler_source
    (current : Expression operations policy contracts world allowed runtimeScope Environment.empty
      (.handle (Instantiation.freezeEffect effect) body clauses) input currentDemand currentRequirements dependencies)
    (pending : ModeSource operations policy contracts tables families actions world
      stack (.value input) output pendingDemand pendingRequirements dependencyScope)
    (scopeTyped : ScopedPorts.EffectScope contracts.erase.ports runtimeScope ticket)
    (checked : Local outward actions phases world dependencies dependencyScope)
    (retained : ModePending outward actions phases world tables families
      stack dependencyScope .nil .ordinary output.mode)
    (annotationBound : Bound annotations dependencyScope)
    (installed : stack.erase.activations ⊆ history)
    (annotation : RowAnnotation
      (.sequence (currentRequirements.prepend (OwnerPhases.ofStack tables stack)) pendingRequirements)
      annotatedRequirements)
    (rowChecked : Checked entries receiving before annotatedRequirements row) :
    ∃ handler : HandlerData, ∃ nextTables nextFamilies residual table clauseDependencies bodyDependencies,
    ∃ bodyRequirements : Requirements currentDemand, ∃ nextRequirements : Requirements pendingDemand,
    ∃ nextAnnotated : Requirements (currentDemand ++ pendingDemand), ∃ nextRow,
      handler.activation ∉ history ∧ handler.scope = runtimeScope ∧ handler.effectInst = effect ∧ handler.clauses = clauses ∧
      nextTables handler = table ∧ nextFamilies handler = clauseDependencies ∧
      dependencies = .handler effect table clauseDependencies bodyDependencies ∧
      (∀ old, old.activation ∈ stack.erase.activations → tables old = nextTables old ∧ families old = nextFamilies old) ∧
      Expression operations policy contracts world (effect :: residual) runtimeScope Environment.empty
        body input currentDemand bodyRequirements bodyDependencies ∧
      ModeSource operations policy contracts nextTables nextFamilies actions world
        (.push (.handler handler) stack) (.value input) output pendingDemand nextRequirements
        (.handler effect table clauseDependencies dependencyScope) ∧
      Local outward actions phases world bodyDependencies (.handler effect table clauseDependencies dependencyScope) ∧
      ModePending outward actions phases world nextTables nextFamilies
        (.push (.handler handler) stack) (.handler effect table clauseDependencies dependencyScope) .nil .ordinary output.mode ∧
      Bound annotations (.handler effect table clauseDependencies dependencyScope) ∧
      (∀ closeDemand (closeRequirements : Requirements closeDemand),
        UnwindSource operations policy contracts tables families world stack closeDemand closeRequirements dependencyScope ↔
        UnwindSource operations policy contracts nextTables nextFamilies world (.push (.handler handler) stack)
          closeDemand closeRequirements (.handler effect table clauseDependencies dependencyScope)) ∧
      RowAnnotation
        (.sequence (bodyRequirements.prepend (OwnerPhases.ofStack nextTables (.push (.handler handler) stack))) nextRequirements)
        nextAnnotated ∧
      RequirementPath annotatedRequirements nextAnnotated [] ∧
      Checked entries receiving before nextAnnotated nextRow ∧ nextRow ⊆ row ∧
      LexicalUnwind.UseTransition (.eval ⟨.handle (Instantiation.freezeEffect effect) body clauses, runtimeScope, stack⟩)
        (.eval ⟨body, runtimeScope, .push (.handler handler) stack⟩) [] [] := by
  generalize encoded : Instantiation.freezeEffect effect = syntaxEffect at current
  cases current with
  | handler bodySource clausesTyped capabilities coverage unique admitted table modes declarations =>
      cases freeze_effect_injective encoded
      rename_i residual bodyDependencies clauseDependencies bodyRequirements
      obtain ⟨activation, fresh⟩ := ScopedTyping.fresh_world_name history
      let handler : HandlerData := ⟨activation, effect, clauses, runtimeScope,
        ScopedPorts.embedPort input.erase.port, ScopedPorts.clauses_have_ticket_barrier clausesTyped⟩
      let nextTables := RecursiveHandlerTables.register tables activation table
      let nextFamilies : Families := fun old => if old.activation = activation then clauseDependencies else families old
      have tablesAgree : ∀ old, old.activation ∈ stack.erase.activations → tables old = nextTables old :=
        RecursiveHandlerTables.register_agrees (fun member => fresh (installed member))
      have familiesAgree : ∀ old, old.activation ∈ stack.erase.activations → families old = nextFamilies old := by
        intro old member
        have different : old.activation ≠ activation := fun same => fresh (same ▸ installed member)
        simp [nextFamilies, different]
      have tableInstalled : nextTables handler = table := RecursiveHandlerTables.registered_lookup rfl
      have familiesInstalled : nextFamilies handler = clauseDependencies := by simp [nextFamilies, handler]
      have frame : SourceDependencyFrames.Frame operations policy contracts nextTables nextFamilies world
          (.handler handler) input input [] (.request [] [])
          (.handler effect table clauseDependencies) (effect :: residual) residual := by
        have built := SourceDependencyFrames.Frame.handler (operations := operations) (world := world)
          (answer := input) (residual := residual) (tables := nextTables) (families := nextFamilies)
          (handler := handler) ⟨_, scopeTyped⟩ (by simp [handler]) clausesTyped coverage unique
          (by simpa only [tableInstalled, familiesInstalled] using declarations) capabilities
          (by simpa only [tableInstalled] using modes)
        simpa only [tableInstalled, familiesInstalled] using built
      have sameContext := RecursiveHandlerTables.context_congr tablesAgree
      obtain ⟨normalRow, normalCheck, normalBound⟩ := annotation.checked rowChecked
      obtain ⟨bodyRow, tailRow, originalBody, tailCheck, rowSame⟩ :=
        RecursiveRequirements.checked_sequence_parts normalCheck
      have bodyCheck := RecursiveRequirements.checked_prepend_iff.mp
        (RecursiveRequirements.checked_prepend_iff.mp originalBody)
      simp only [List.cons_append, List.nil_append] at bodyCheck
      have relocated := RecursiveHandlerTables.checked_activation bodyCheck
        (front := []) (tail := OwnerPhases.ofStack tables stack ++ receiving) (second := activation) rfl
      have nextBody : Checked entries
          (OwnerPhases.ofStack nextTables (.push (.handler handler) stack) ++ receiving) before bodyRequirements bodyRow := by
        simpa only [List.nil_append, OwnerPhases.ofStack, OwnerPhases.frameEntry,
          tableInstalled, handler, sameContext, List.cons_append] using relocated
      let nextPending : Requirements pendingDemand :=
        .sequence ((Requirements.request [] []).prepend (OwnerPhases.ofStack nextTables stack)) pendingRequirements
      have nextPendingCheck : Checked entries receiving (OwnerPhaseTransitions.spendAll before currentDemand)
          nextPending tailRow :=
        .sequence (firstRow := []) (secondRow := tailRow)
          (.request (by simp [OwnerSource.exportAt, residual_empty])) tailCheck
      let nextNormal : Requirements (currentDemand ++ pendingDemand) :=
        .sequence (bodyRequirements.prepend (OwnerPhases.ofStack nextTables (.push (.handler handler) stack))) nextPending
      have nextNormalCheck : Checked entries receiving before nextNormal (bodyRow ++ tailRow) :=
        .sequence (RecursiveRequirements.checked_prepend_iff.mpr nextBody) nextPendingCheck
      have cleanupSame : ∀ closeDemand (closeRequirements : Requirements closeDemand),
          UnwindSource operations policy contracts tables families world stack closeDemand closeRequirements dependencyScope ↔
          UnwindSource operations policy contracts nextTables nextFamilies world (.push (.handler handler) stack)
            closeDemand closeRequirements (.handler effect table clauseDependencies dependencyScope) := by
        intro closeDemand closeRequirements
        constructor
        · intro old
          simpa only [tableInstalled, familiesInstalled] using
            (UnwindSource.handler (data := handler)
              (by simpa only [tableInstalled, familiesInstalled] using frame)
              (unwind_source_registries old tablesAgree familiesAgree))
        · intro changed
          rw [← tableInstalled, ← familiesInstalled] at changed
          cases changed with
          | handler declaration rest =>
              exact unwind_source_registries rest
                (fun old member => (tablesAgree old member).symm)
                (fun old member => (familiesAgree old member).symm)
      cases checked with
      | handler bodyChecked =>
          refine ⟨handler, nextTables, nextFamilies, residual, table, clauseDependencies, bodyDependencies,
            bodyRequirements, nextPending, .choice nextNormal annotatedRequirements (.refl _),
            (bodyRow ++ tailRow) ++ row, fresh, rfl, rfl, rfl, tableInstalled, familiesInstalled, rfl,
            (fun old member => ⟨tablesAgree old member, familiesAgree old member⟩), bodySource,
            .push (.ordinary frame) (segment_registries pending tablesAgree familiesAgree), bodyChecked, .push (by simpa only [tableInstalled, familiesInstalled] using
              (ModeFrame.handler (tables := nextTables) (families := nextFamilies) (data := handler)))
              (mode_pending_registries retained tablesAgree familiesAgree), .handler annotationBound,
            cleanupSame, .alternatives .original (.refl _), .no .here,
            .choice nextNormalCheck rowChecked,
            List.append_subset.mpr ⟨(rowSame ▸ normalBound), List.Subset.refl _⟩, ?_⟩
          exact .evaluate (.enterHandler handler body stack) trivial


#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.enter_handler_source
#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.frame_registries
#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.segment_registries
#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.start_normal_cleanup_source
#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.finish_normal_cleanup_source
#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.leave_handler_source
#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.enter_cleanup_source
end Ash.OneShot.SourceDependencyNeutral.Lexical


namespace Ash.OneShot.SourceDependencyNeutral.Lexical
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations SourceDependencyFrames
open SourceDependencyChecks.Lexical (Local Pending ModeFrame ModePending)
open SourceDependencySchemes.Closing (Bound)
open RecursiveRequirements (Requirements)

/-- Rich source substitution and physical support use the same operand and
    body. The support premise is a finite environment/dependency calculation,
    independent of the function port and latent effect row. -/
theorem substitution_preserves_source_support
    (source : Expression operations policy contracts world allowed scope (environment.extend name input)
      code result demand requirements dependencies)
    (replacement : ValueSummary operations policy contracts world environment allowed value input)
    (closed : ClosedValue value)
    (checked : Local outward actions phases world dependencies receiving)
    (valueSupport : Syntax.resourceDependencies value.dependencies ⊆ bound)
    (bodySupport : ScopedPorts.Support.evaluate (ScopedPorts.Support.extend supportEnvironment name bound)
      code.dependencies ⊆ available) :
    Expression operations policy contracts world allowed scope environment (code.subst name value)
      result demand requirements dependencies ∧
    Local outward actions phases world dependencies receiving ∧
    ScopedPorts.Support.evaluate supportEnvironment (code.subst name value).dependencies ⊆ available :=
  ⟨SourceDependencyAnnotations.substitution source replacement closed, checked,
    (ScopedPorts.Support.substitution_support_bound code name closed valueSupport).trans bodySupport⟩

/-- The closed instance applies to a selected clause parameter as well as a
    local binding. Reuse the existing parameter-support theorem directly. -/
theorem closed_binding_preserves_source_support
    (source : Expression operations policy contracts world allowed scope (Environment.empty.extend name input)
      code result demand requirements dependencies)
    (replacement : ValueSummary operations policy contracts world Environment.empty allowed value input)
    (closed : ClosedValue value)
    (checked : Local outward actions phases world dependencies receiving)
    (valueSupport : Syntax.resourceDependencies value.dependencies ⊆ bound)
    (bodySupport : ScopedPorts.Support.evaluate (ScopedPorts.Support.extend ScopedPorts.Support.empty name bound)
      code.dependencies ⊆ available) :
    Expression operations policy contracts world allowed scope Environment.empty (code.subst name value)
      result demand requirements dependencies ∧
    Local outward actions phases world dependencies receiving ∧
    Syntax.resourceDependencies (code.subst name value).dependencies ⊆ available :=
  ⟨SourceDependencyAnnotations.substitution source replacement closed, checked,
    ScopedPorts.Support.parameter_binding_preserves_support closed valueSupport bodySupport⟩

/-- A finite support annotation supplies release exclusion for arbitrary
    values, including closures. The ordinary port is not used as a capture bound. -/
theorem leave_resource_source
    (current : Expression operations policy contracts world allowed runtimeScope Environment.empty
      value input currentDemand currentRequirements dependencies)
    (pending : ModeSource operations policy contracts tables families actions world
      (.push (.cell identity payload caller answer) tail) (.value input) output pendingDemand pendingRequirements dependencyScope)
    (closed : ClosedValue value)
    (retained : ModePending outward actions phases world tables families
      (.push (.cell identity payload caller answer) tail) dependencyScope .nil .ordinary output.mode)
    (annotationBound : Bound annotations dependencyScope)
    (valueSupport : Syntax.resourceDependencies value.dependencies ⊆ bound)
    (excluded : identity ∉ bound)
    (supported : LexicalUnwind.MachineAccess ambient
      (.eval ⟨value, runtimeScope, .push (.cell identity payload caller answer) tail⟩)) :
    ∃ boundary restScope, ∃ nextRequirements : Requirements pendingDemand,
      currentDemand = [] ∧ ScopedPorts.EffectScopeKnown contracts.erase.ports caller ∧
      Expression operations policy contracts world boundary caller Environment.empty
        value input [] (.request [] []) .pure ∧
      ModeSource operations policy contracts tables families actions world
        tail (.value input) output pendingDemand nextRequirements restScope ∧
      ModePending outward actions phases world tables families
        tail restScope .nil .ordinary output.mode ∧
      LexicalUnwind.AccessConditions ⟨value, runtimeScope, .push (.cell identity payload caller answer) tail⟩ ambient ∧
      Bound annotations restScope ∧
      LexicalUnwind.UseTransition (.eval ⟨value, runtimeScope, .push (.cell identity payload caller answer) tail⟩)
        (.eval ⟨value, caller, tail⟩) [] [.resource identity] ∧
      LexicalUnwind.MachineAccess ambient (.eval ⟨value, caller, tail⟩) := by
  have excludes := ScopedPorts.Support.result_excludes_resource valueSupport excluded
  have access : LexicalUnwind.AccessConditions
      ⟨value, runtimeScope, .push (.cell identity payload caller answer) tail⟩ ambient := by
    constructor
    · intro other payload' answer' savedScope scope returned rest same returnedClosed
      cases same
      exact excludes
    · intro requested operation operand scope whole cap rest handler same cut operandClosed
      cases same
      cases closed.1
  have step : LexicalUnwind.UseTransition
      (.eval ⟨value, runtimeScope, .push (.cell identity payload caller answer) tail⟩)
      (.eval ⟨value, caller, tail⟩) [] [.resource identity] :=
    .evaluate (.leaveCell identity payload answer caller runtimeScope value closed tail)
      (by cases value <;> first | trivial | cases closed.1)
  have nextAccess := LexicalUnwind.transition_access step.erases supported access
  have empty := SourceTemplates.expression_value_demand
    (DeclaredSources.expression_erase (expression_erase current)) closed.1
  cases pending with
  | push frame rest => cases frame with
    | ordinary frame => cases frame with
      | cell scope noEscape annotation interface =>
          obtain ⟨_, _, _, checkedFrame, remaining, scopeSame⟩ := mode_pending_pop retained
          cases checkedFrame with
          | cell =>
              cases scopeSame
              cases interface with
              | cell savedScope absent =>
                exact ⟨_, _, _, empty, savedScope,
                  Values.change_context (Values.summary current closed.1) closed.1 [] caller,
                  rest, remaining, access, (by cases annotationBound with | cell bound => exact bound), step, nextAccess⟩

/-- The existing higher-order counterexample cannot satisfy any release
    annotation excluding its captured resource, even though its port omits it. -/
theorem escaping_closure_has_no_release_bound :
    ¬ ∃ bound : List Nat,
      Syntax.resourceDependencies (ScopedSignatureGap.Examples.payload (.activation 0)).dependencies ⊆ bound ∧ 0 ∉ bound := by
  rintro ⟨bound, included, absent⟩
  apply absent
  apply included
  decide

#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.leave_resource_source
#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.escaping_closure_has_no_release_bound
#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.substitution_preserves_source_support
#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.closed_binding_preserves_source_support
end Ash.OneShot.SourceDependencyNeutral.Lexical


namespace Ash.OneShot.SourceDependencyNeutral.Lexical
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations SourceDependencyFrames
open SourceDependencyChecks.Lexical (Local Pending ModeFrame ModePending)
open SourceDependencySchemes.Closing (Bound)
open RecursiveRequirements (Requirements)

/-- Fresh resource entry constructs one matching body and cell frame, retaining
    the source requirement-hiding relation for later effect-row checking. -/
theorem enter_resource_source
    (current : Expression operations policy contracts world allowed runtimeScope Environment.empty
      (.resource binder initializer body) input currentDemand currentRequirements dependencies)
    (pending : ModeSource operations policy contracts tables families actions world
      stack (.value input) output pendingDemand pendingRequirements dependencyScope)
    (scopeTyped : ScopedPorts.EffectScope contracts.erase.ports runtimeScope ticket)
    (isValue : initializer.IsValue)
    (checked : Local outward actions phases world dependencies dependencyScope)
    (retained : ModePending outward actions phases world tables families
      stack dependencyScope .nil .ordinary output.mode)
    (annotationBound : Bound annotations dependencyScope)
    (fresh : identity ∉ world) :
    ∃ payload answer residual bodyDependencies,
    ∃ bodyRequirements outwardRequirements : Requirements currentDemand,
    ∃ nextRequirements : Requirements pendingDemand,
      initializer = .integer payload ∧
      currentRequirements = .sequence (.request [] []) outwardRequirements ∧
      ResourceRequirements.Hides identity bodyRequirements outwardRequirements ∧
      Expression operations policy contracts (world ++ [identity]) (.cell identity :: residual)
        runtimeScope Environment.empty
        (body.instantiate (Instantiation.Environment.empty.bind binder identity)) input
        currentDemand bodyRequirements bodyDependencies ∧
      ModeSource operations policy contracts tables families actions (world ++ [identity])
        (.push (.cell identity payload runtimeScope answer) stack) (.value input) output pendingDemand nextRequirements
        (.cell identity dependencyScope) ∧
      Local outward actions phases (world ++ [identity]) bodyDependencies (.cell identity dependencyScope) ∧
      ModePending outward actions phases (world ++ [identity]) tables families
        (.push (.cell identity payload runtimeScope answer) stack) (.cell identity dependencyScope) .nil .ordinary output.mode ∧
      Bound annotations (.cell identity dependencyScope) ∧
      LexicalUnwind.UseTransition (.eval ⟨.resource binder initializer body, runtimeScope, stack⟩)
        (.eval ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), runtimeScope,
          .push (.cell identity payload runtimeScope answer) stack⟩) [.resource identity] [] := by
  have ready := ScopedPorts.typed_resource_closed
    (SourceTemplates.expression_ports (DeclaredSources.expression_erase (expression_erase current)) scopeTyped)
  cases current with
  | resource initial opened formed effectsBound admitted hidden =>
      obtain ⟨payload, same⟩ := ScopedPorts.typed_integer_value
        (SourceTemplates.expression_ports (DeclaredSources.expression_erase (expression_erase initial)) scopeTyped) isValue
      subst initializer
      cases initial
      rename_i bodyDemand residual outwardRequirements bodyRequirements bodyDependencies
      let answer := ScopedPorts.embedPort input.erase.port
      have noEscape : identity ∉ (ScopedPorts.eraseType answer).resources := by
        simpa only [answer, ScopedPorts.erase_embed_port] using
          (fun member => fresh (formed member))
      have frame : SourceDependencyFrames.Frame operations policy contracts tables families (world ++ [identity])
          (.cell identity payload runtimeScope answer) input input [] (.request [] [])
          (.cell identity) (.cell identity :: residual) residual :=
        .cell ⟨_, ScopedPorts.effect_scope_has_types scopeTyped⟩ noEscape
          (by simp only [answer, ScopedPorts.erase_embed_port]) (.cell ⟨_, scopeTyped⟩ noEscape)
      have grown := pending.transport (fun _ _ known => known) (fun _ _ known => known)
        (List.subset_append_left world [identity])
      have openedCheck := (Local.sequence_iff.mp checked).2
      cases openedCheck with
      | resource bodyChecked =>
          refine ⟨payload, answer, residual, bodyDependencies identity, bodyRequirements identity,
            outwardRequirements, _, rfl, rfl, hidden identity fresh, opened identity fresh,
            .push (.ordinary frame) grown,
            bodyChecked identity fresh, .push .cell (mode_pending_world retained (List.subset_append_left _ _)), .cell annotationBound, ?_⟩
          exact .evaluate (.enterCell binder identity payload body runtimeScope answer stack ready) trivial

#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.enter_resource_source
end Ash.OneShot.SourceDependencyNeutral.Lexical

namespace Ash.OneShot.SourceDependencyNeutral.Lexical
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations SourceDependencyFrames
open SourceDependencyChecks.Lexical (Local Pending ModeFrame ModePending)
open SourceDependencySchemes.Closing (Bound)
open RecursiveRequirements (Requirements)

/-- Changing a selected cell's payload leaves rich source annotations and the
    exact lexical dependency scope unchanged, including dormant captures. -/
theorem cell_update_segment
    (update : CellUpdate identity old new before after)
    (source : ModeSource operations policy contracts tables families actions world
      before input output demand requirements dependencyScope) :
    ModeSource operations policy contracts tables families actions world
      after input output demand requirements dependencyScope := by
  induction update generalizing input demand requirements dependencyScope with
  | hit => cases source with
    | push head rest => cases head with
      | ordinary head => cases head with
        | cell scopeKnown noEscape annotation interface => cases interface with
          | cell scopeTyped excluded =>
              rename_i residual
              exact .push (.ordinary (.cell scopeKnown noEscape annotation
                (.cell (residual := residual) scopeTyped excluded))) rest
      | cell => exact .push .cell rest
  | push miss next ih => cases source with
    | push head rest =>
        simpa only [RecursiveCells.update_context next] using ModeSource.push head (ih rest)
  | live next ih => cases source with
    | live known actionKnown inputAnnotation answerAnnotation scope held saved answer rest =>
        exact .live known actionKnown inputAnnotation answerAnnotation scope held saved answer (ih rest)
    | opening saved rest =>
        have same := RecursiveCells.update_context (tables := tables) next
        simpa only [OwnerPhases.ofStack, same] using ModeSource.opening saved (ih rest)
  | spent next ih => cases source with
    | spent known annotation scope rest => exact .spent known annotation scope (ih rest)
    | skippedSpent rest => exact .skippedSpent (ih rest)

/-- The actual cell payload update changes neither receiving scope nor the
ordinary/unwinding mode of pending code. -/
theorem cell_update_pending
    (update : CellUpdate identity old new before after)
    (pending : ModePending outward actions phases world tables families before scope outside input output) :
    ModePending outward actions phases world tables families after scope outside input output := by
  induction update generalizing scope input with
  | hit => cases pending with
      | push frame tail => cases frame with
          | cell => exact .push .cell tail
  | push miss next ih => cases pending with
      | push frame tail => exact .push frame (ih tail)
  | live next ih => cases pending with
      | live saved tail => exact .live saved (ih tail)
      | opening saved tail => exact .opening saved (ih tail)
  | spent next ih => cases pending with
      | spent tail => exact .spent (ih tail)

/-- A builtin read derives its rich reply type from the source signature and
    preserves the exact checked pending scope through the actual cell update. -/
theorem read_cell_source
    (signature : operations.erase.ports (.cell identity) 0 = some (.reference identity, .integer))
    (current : Expression operations policy contracts world allowed runtimeScope Environment.empty
      (.perform (Instantiation.freezeEffect (.cell identity)) 0 (.resourceRef (.activation identity)))
      input currentDemand currentRequirements dependencies)
    (pending : ModeSource operations policy contracts tables families actions world
      before (.value input) output pendingDemand pendingRequirements dependencyScope)
    (retained : ModePending outward actions phases world tables families
      before dependencyScope .nil .ordinary output.mode)
    (annotationBound : Bound annotations dependencyScope)
    (selected : CellUpdate identity payload payload before after) :
    currentDemand = [] ∧
    Expression operations policy contracts world allowed runtimeScope Environment.empty
      (.integer payload) input [] (.request [] []) .pure ∧
    ModeSource operations policy contracts tables families actions world
      after (.value input) output pendingDemand pendingRequirements dependencyScope ∧
    Local outward actions phases world .pure dependencyScope ∧
    ModePending outward actions phases world tables families
        after dependencyScope .nil .ordinary output.mode ∧
    Bound annotations dependencyScope ∧
    LexicalUnwind.UseTransition
      (.eval ⟨.perform (Instantiation.freezeEffect (.cell identity)) 0 (.resourceRef (.activation identity)), runtimeScope, before⟩)
      (.eval ⟨.integer payload, runtimeScope, after⟩) [] [] := by
  generalize encoded : Instantiation.freezeEffect (.cell identity) = syntaxEffect at current
  cases current with
  | perform known admitted operand formed =>
      cases freeze_effect_injective encoded
      have result := (Prod.mk.inj (Option.some.inj
        (signature.symm.trans (CoherentSourceTypes.port_lookup (operation_erase known))))).2
      cases input <;> cases result
      cases operand
      exact ⟨rfl, .integer, cell_update_segment selected pending, .pure, cell_update_pending selected retained, annotationBound,
        .evaluate (.readCell identity payload runtimeScope before after selected) trivial⟩

#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.cell_update_segment
#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.read_cell_source
end Ash.OneShot.SourceDependencyNeutral.Lexical

namespace Ash.OneShot.SourceDependencyNeutral.Lexical
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations SourceDependencyFrames
open SourceDependencyChecks.Lexical (Local Pending ModeFrame ModePending)
open SourceDependencySchemes.Closing (Bound)

theorem write_cell_source
    (signature : operations.erase.ports (.cell identity) 1 = some (.product (.reference identity) .integer, .unit))
    (current : Expression operations policy contracts world allowed runtimeScope Environment.empty
      (.perform (Instantiation.freezeEffect (.cell identity)) 1
        (.pair (.resourceRef (.activation identity)) (.integer new)))
      input currentDemand currentRequirements dependencies)
    (pending : ModeSource operations policy contracts tables families actions world
      before (.value input) output pendingDemand pendingRequirements dependencyScope)
    (retained : ModePending outward actions phases world tables families
      before dependencyScope .nil .ordinary output.mode)
    (annotationBound : Bound annotations dependencyScope)
    (selected : CellUpdate identity old new before after) :
    currentDemand = [] ∧
    Expression operations policy contracts world allowed runtimeScope Environment.empty
      .unit input [] (.request [] []) .pure ∧
    ModeSource operations policy contracts tables families actions world
      after (.value input) output pendingDemand pendingRequirements dependencyScope ∧
    Local outward actions phases world .pure dependencyScope ∧
    ModePending outward actions phases world tables families
        after dependencyScope .nil .ordinary output.mode ∧
    Bound annotations dependencyScope ∧
    LexicalUnwind.UseTransition
      (.eval ⟨.perform (Instantiation.freezeEffect (.cell identity)) 1
        (.pair (.resourceRef (.activation identity)) (.integer new)), runtimeScope, before⟩)
      (.eval ⟨.unit, runtimeScope, after⟩) [] [] := by
  generalize encoded : Instantiation.freezeEffect (.cell identity) = syntaxEffect at current
  cases current with
  | perform known admitted operand formed =>
      cases freeze_effect_injective encoded
      have result := (Prod.mk.inj (Option.some.inj
        (signature.symm.trans (CoherentSourceTypes.port_lookup (operation_erase known))))).2
      cases input <;> cases result
      have empty := SourceTemplates.expression_value_demand
        (DeclaredSources.expression_erase (expression_erase operand)) (by trivial)
      exact ⟨empty, .unit, cell_update_segment selected pending, .pure, cell_update_pending selected retained, annotationBound,
        .evaluate (.writeCell identity old new runtimeScope before after selected) trivial⟩

#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.write_cell_source
end Ash.OneShot.SourceDependencyNeutral.Lexical

namespace Ash.OneShot.SourceDependencyNeutral.Lexical
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations SourceDependencyFrames
open SourceDependencyChecks.Lexical (Local Pending ModeFrame ModePending)
open SourceDependencySchemes.Closing (Bound)
open RecursiveRequirements (Requirements)

/-- Returning through an already-spent owner restores its saved caller while
    retaining the value's complete source summary and the checked suffix. -/
theorem leave_clause_source
    (current : Expression operations policy contracts world allowed runtimeScope Environment.empty
      value input currentDemand currentRequirements dependencies)
    (pending : ModeSource operations policy contracts tables families actions world
      (.spent owner answer caller tail) (.value input) output pendingDemand pendingRequirements dependencyScope)
    (closed : ClosedValue value)
    (retained : ModePending outward actions phases world tables families
      (.spent owner answer caller tail) dependencyScope .nil .ordinary output.mode)
    (annotationBound : Bound annotations dependencyScope) :
    ∃ boundary restScope, ∃ nextRequirements : Requirements pendingDemand,
      currentDemand = [] ∧ ScopedPorts.EffectScopeKnown contracts.erase.ports caller ∧
      Expression operations policy contracts world boundary caller Environment.empty
        value input [] (.request [] []) .pure ∧
      ModeSource operations policy contracts tables families actions world
        tail (.value input) output pendingDemand nextRequirements restScope ∧
      ModePending outward actions phases world tables families
        tail restScope .nil .ordinary output.mode ∧
      Bound annotations restScope ∧
      LexicalUnwind.UseTransition (.eval ⟨value, runtimeScope, .spent owner answer caller tail⟩)
        (.eval ⟨value, caller, tail⟩) [] [] := by
  have empty := SourceTemplates.expression_value_demand
    (DeclaredSources.expression_erase (expression_erase current)) closed.1
  cases pending with
  | spent known annotation scope rest => cases retained with
    | spent remaining =>
        exact ⟨_, _, _, empty, scope,
          Values.change_context (Values.summary current closed.1) closed.1 [] caller,
          rest, remaining, (by cases annotationBound with | spent bound => exact bound), .evaluate (.leaveClause owner answer value closed runtimeScope caller tail)
            (by cases value <;> first | trivial | cases closed.1)⟩

/-- A value reaching the disposal delimiter returns Unit to the exact checked
    caller, independently of the abandoned computation's answer type. -/
theorem close_value_source
    (pending : ModeSource operations policy contracts tables families actions world
      (.push (.closing identity caller) tail) (.value input) output pendingDemand pendingRequirements dependencyScope)
    (closed : ClosedValue value)
    (retained : ModePending outward actions phases world tables families
      (.push (.closing identity caller) tail) dependencyScope .nil .ordinary output.mode)
    (annotationBound : Bound annotations dependencyScope) :
    ∃ boundary restScope, ∃ nextRequirements : Requirements pendingDemand,
      ScopedPorts.EffectScopeKnown contracts.erase.ports caller ∧
      Expression operations policy contracts world boundary caller Environment.empty
        .unit .unit [] (.request [] []) .pure ∧
      ModeSource operations policy contracts tables families actions world
        tail (.value .unit) output pendingDemand nextRequirements restScope ∧
      Local outward actions phases world .pure restScope ∧
      ModePending outward actions phases world tables families
        tail restScope .nil .ordinary output.mode ∧
      Bound annotations restScope ∧
      LexicalUnwind.UseTransition (.eval ⟨value, runtimeScope, .push (.closing identity caller) tail⟩)
        (.eval ⟨.unit, caller, tail⟩) [] [.close identity] := by
  cases pending with
  | push frame rest => cases frame with
    | ordinary frame => cases frame with
      | closing scopeKnown interface => cases interface with
        | closing scope =>
            obtain ⟨_, _, _, checkedFrame, remaining, scopeSame⟩ := mode_pending_pop retained
            cases checkedFrame with
            | closing =>
                cases scopeSame
                exact ⟨[], _, _, scope, .unit, rest, .pure, remaining,
                  (by cases annotationBound with | running bound => exact bound), .closeValue closed⟩
    | closing scope =>
        obtain ⟨_, _, _, checkedFrame, remaining, scopeSame⟩ := mode_pending_pop retained
        cases checkedFrame with
        | closing =>
            cases scopeSame
            exact ⟨[], _, _, scope, .unit, rest, .pure, remaining,
              (by cases annotationBound with | running bound => exact bound), .closeValue closed⟩

#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.leave_clause_source
#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.close_value_source
end Ash.OneShot.SourceDependencyNeutral.Lexical

#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.source_frame_registries
#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.mode_frame_registries
#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.mode_pending_registries
#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.mode_pending_world
#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.mode_pending_pop
#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.cell_update_pending


namespace Ash.OneShot.SourceDependencyNeutral.Lexical
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open SourceDependencyAnnotations SourceDependencyFrames
open SourceDependencyChecks.Lexical (Local ModePending)
open SourceDependencySchemes.Closing (Bound)
open RecursiveRequirements (Requirements Checked evaluate)
open RecursiveExpressions (Ready ready_not_focus ready_not_value)

/-- Ordinary source reduction reuses substitution and branch checking for the
actual raw step. No successor source or effect certificate is a premise. -/
private theorem ready_source_reduction
    (current : Expression operations policy contracts world allowed runtimeScope Environment.empty
      code input currentDemand currentRequirements dependencies)
    (scopeTyped : ScopedPorts.EffectScope contracts.erase.ports runtimeScope ticket)
    (checked : Local outward actions phases world dependencies dependencyScope)
    (ready : Ready code)
    (step : RawStep ⟨code, runtimeScope, stack⟩ after created completed) :
    ∃ nextDemand, ∃ nextRequirements : Requirements nextDemand, ∃ nextDependencies nextTicket,
      Expression operations policy contracts world allowed after.scope Environment.empty
        after.expression input nextDemand nextRequirements nextDependencies ∧
      Local outward actions phases world nextDependencies dependencyScope ∧
      ScopedPorts.EffectScope contracts.erase.ports after.scope nextTicket ∧
      currentDemand.Perm nextDemand ∧ after.stack = stack ∧ created = [] ∧ completed = [] ∧
      ∀ entries receiving before row, Checked entries receiving before currentRequirements row →
        ∃ nextRow, Checked entries receiving before nextRequirements nextRow ∧ nextRow.Sublist row := by
  cases step with
  | focus plain focus tail => exact False.elim (ready_not_focus ready focus)
  | plug plain value closed scope tail => exact False.elim (ready_not_value ready closed.1)
  | leaveHandler handler value closed scope tail => exact False.elim (ready_not_value ready closed.1)
  | leaveCell identity payload answer savedScope scope value closed tail => exact False.elim (ready_not_value ready closed.1)
  | startCleanup action saved closed scope tail => exact False.elim (ready_not_value ready closed.1)
  | leaveClause owner answer value closed scope caller tail => exact False.elim (ready_not_value ready closed.1)
  | bind parameter value body scope tail closed environmentReady =>
      obtain ⟨requirements, dependencies, source, localCheck, shape, evaluation⟩ := bind_preserves_local current closed checked
      refine ⟨_, requirements, dependencies, _, source, localCheck, scopeTyped, .refl _, rfl, rfl, rfl, ?_⟩
      intro entries receiving before row original
      exact ⟨row, RecursiveRequirements.evaluate_sound ((evaluation entries receiving before).trans
        (RecursiveRequirements.checked_complete original)), .refl _⟩
  | beta parameter body value scope tail closed closureReady =>
      obtain ⟨requirements, dependencies, source, localCheck, shape, evaluation⟩ := beta_preserves_local current closed checked
      refine ⟨_, requirements, dependencies, _, source, localCheck, .none, .refl _, rfl, rfl, rfl, ?_⟩
      intro entries receiving before row original
      exact ⟨row, RecursiveRequirements.evaluate_sound ((evaluation entries receiving before).trans
        (RecursiveRequirements.checked_complete original)), .refl _⟩
  | ifTrue yes no scope tail =>
      obtain ⟨demand, requirements, dependencies, source, localCheck, same, selected⟩ := branch_preserves_local current checked
      exact ⟨demand, requirements, dependencies, _, source, localCheck, scopeTyped, same, rfl, rfl, rfl, selected⟩
  | ifFalse yes no scope tail =>
      obtain ⟨demand, requirements, dependencies, source, localCheck, same, selected⟩ := branch_preserves_local current checked
      exact ⟨demand, requirements, dependencies, _, source, localCheck, scopeTyped, same, rfl, rfl, rfl, selected⟩
  | enterHandler | enterCell | enterCleanup | finishCleanup | capture | resume | discard | finishClose | retire | readCell | writeCell => cases ready

/-- Ready bind, beta and boolean branch steps retain the complete annotated
expression/stack check. The existing port proof constructs lexical readiness;
the exact pending stack, cleanup source and ownership are unchanged. -/
theorem ready_preserves_source
    (current : Expression operations policy contracts world allowed runtimeScope Environment.empty
      code input currentDemand currentRequirements dependencies)
    (pending : ModeSource operations policy contracts tables families actions world
      stack (.value input) output pendingDemand pendingRequirements dependencyScope)
    (scopeTyped : ScopedPorts.EffectScope contracts.erase.ports runtimeScope ticket)
    (ready : Ready code)
    (checked : Local outward actions phases world dependencies dependencyScope)
    (retained : ModePending outward actions phases world tables families
      stack dependencyScope .nil .ordinary output.mode)
    (annotationBound : Bound annotations dependencyScope)
    (annotation : RowAnnotation
      (.sequence (currentRequirements.prepend (OwnerPhases.ofStack tables stack)) pendingRequirements)
      annotatedRequirements)
    (rowChecked : Checked entries receiving before annotatedRequirements row) :
    ∃ after : Configuration, ∃ nextDemand, ∃ nextRequirements : Requirements nextDemand,
    ∃ nextDependencies nextTicket, ∃ nextAnnotated : Requirements (nextDemand ++ pendingDemand), ∃ nextRow,
      Expression operations policy contracts world allowed after.scope Environment.empty
        after.expression input nextDemand nextRequirements nextDependencies ∧
      ScopedPorts.EffectScope contracts.erase.ports after.scope nextTicket ∧
      ModeSource operations policy contracts tables families actions world
        after.stack (.value input) output pendingDemand pendingRequirements dependencyScope ∧
      Local outward actions phases world nextDependencies dependencyScope ∧
      ModePending outward actions phases world tables families
        after.stack dependencyScope .nil .ordinary output.mode ∧
      Bound annotations dependencyScope ∧ currentDemand.Perm nextDemand ∧ after.stack = stack ∧
      (∀ closeDemand (closeRequirements : Requirements closeDemand),
        UnwindSource operations policy contracts tables families world stack closeDemand closeRequirements dependencyScope ↔
        UnwindSource operations policy contracts tables families world after.stack closeDemand closeRequirements dependencyScope) ∧
      RowAnnotation
        (.sequence (nextRequirements.prepend (OwnerPhases.ofStack tables after.stack)) pendingRequirements) nextAnnotated ∧
      RequirementPath annotatedRequirements nextAnnotated [] ∧
      Checked entries receiving before nextAnnotated nextRow ∧ nextRow ⊆ row ∧
      LexicalUnwind.UseTransition (.eval ⟨code, runtimeScope, stack⟩) (.eval after) [] [] := by
  have typed := SourceTemplates.expression_ports
    (DeclaredSources.expression_erase (expression_erase current)) scopeTyped
  change ScopedPorts.Typed operations.erase.ports world ScopedPorts.TypeEnv.empty _ _ _ _ at typed
  have progress : ∃ after, RawStep ⟨code, runtimeScope, stack⟩ after [] [] := by
    cases ready with
    | bind value => exact ⟨_, (ScopedPorts.typed_bind_value_progress typed value _ _).1⟩
    | app value =>
        obtain ⟨after, step, typedAfter⟩ := ScopedPorts.typed_application_value_progress typed trivial value _ _
        exact ⟨_, step⟩
    | @branch flag yes no => cases flag with
        | false => exact ⟨_, .ifFalse yes no _ _⟩
        | true => exact ⟨_, .ifTrue yes no _ _⟩
  obtain ⟨after, step⟩ := progress
  obtain ⟨nextDemand, nextRequirements, nextDependencies, nextTicket,
    nextSource, nextLocal, nextScope, sameDemand, sameStack, created, completed, selected⟩ :=
    ready_source_reduction current scopeTyped checked ready step
  obtain ⟨normalRow, normalCheck, normalBound⟩ := annotation.checked rowChecked
  obtain ⟨currentRow, pendingRow, currentCheck, pendingCheck, rowSame⟩ :=
    RecursiveRequirements.checked_sequence_parts normalCheck
  obtain ⟨nextCurrentRow, nextCurrentCheck, included⟩ := selected _ _ _ _
    (RecursiveRequirements.checked_prepend_iff.mp currentCheck)
  have nextPendingCheck := pendingCheck
  rw [PhaseRechecking.spendAll_permutation sameDemand] at nextPendingCheck
  have nextNormal : Checked entries receiving before
      (.sequence (nextRequirements.prepend (OwnerPhases.ofStack tables after.stack)) pendingRequirements)
      (nextCurrentRow ++ pendingRow) := by
    rw [sameStack]
    exact .sequence (RecursiveRequirements.checked_prepend_iff.mpr nextCurrentCheck) nextPendingCheck
  have within : nextCurrentRow ++ pendingRow ⊆ row :=
    ((included.append (List.Sublist.refl pendingRow)).subset.trans (rowSame ▸ normalBound))
  have aligned := sameDemand.symm.append_right pendingDemand
  refine ⟨after, nextDemand, nextRequirements, nextDependencies, nextTicket,
    .choice _ annotatedRequirements aligned, (nextCurrentRow ++ pendingRow) ++ row,
    nextSource, nextScope, sameStack.symm ▸ pending, nextLocal,
    sameStack.symm ▸ retained, annotationBound, sameDemand, sameStack,
    (fun _ _ => by rw [sameStack]), .alternatives .original aligned, .no .here,
    .choice nextNormal rowChecked, List.append_subset.mpr ⟨within, List.Subset.refl _⟩, ?_⟩
  exact .evaluate step (by cases ready <;> trivial)

end Ash.OneShot.SourceDependencyNeutral.Lexical
#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.ready_preserves_source


namespace Ash.OneShot.SourceDependencyNeutral.Lexical.Recursive
open ScopedExpressions ScopedExecution SourceDependencyAnnotations
open SourceDependencyChecks.Lexical.ReturnHints.Recursive (Local)
open RecursiveRequirements (Requirements evaluate)
/-- Bind removes only a silent initializer. The exact remaining source,
contextual check and old requirement evaluation all follow existing lemmas. -/
theorem bind_preserves_local
    (source : Expression operations policy contracts world allowed lexical environment (.bind name value body)
      result demand requirements dependencies)
    (closed : ClosedValue value)
    (checked : Local outward actions phases world dependencies receiving) :
    ∃ (reduced : Requirements demand) (remaining : Dependencies),
      Expression operations policy contracts world allowed lexical environment (body.subst name value)
        result demand reduced remaining ∧ Local outward actions phases world remaining receiving ∧
      (∃ initial, dependencies = .sequence initial remaining ∧ initial.Silent) ∧
      ∀ store context before, evaluate store context before reduced = evaluate store context before requirements := by
  obtain ⟨reduced, remaining, next, ⟨initial, same, silent⟩, evaluation⟩ :=
    SourceDependencyAnnotations.bind_expression source closed
  subst dependencies
  exact ⟨reduced, remaining, next, (Local.silent_prefix silent).mp checked, ⟨initial, rfl, silent⟩, evaluation⟩

/-- Beta exposes the function's retained latent tree. Its function and
argument prefixes are silent; its lexical scope follows the existing rule. -/
theorem beta_preserves_local
    (source : Expression operations policy contracts world allowed lexical environment (.app (.lambda name body) value)
      result demand requirements dependencies)
    (closed : ClosedValue value)
    (checked : Local outward actions phases world dependencies receiving) :
    ∃ (reduced : Requirements demand) (remaining : Dependencies),
      Expression operations policy contracts world allowed .none environment (body.subst name value)
        result demand reduced remaining ∧ Local outward actions phases world remaining receiving ∧
      (∃ function argument, dependencies = .sequence function (.sequence argument remaining) ∧ function.Silent ∧ argument.Silent) ∧
      ∀ store context before, evaluate store context before reduced = evaluate store context before requirements := by
  obtain ⟨reduced, remaining, next, ⟨function, argument, same, functionSilent, argumentSilent⟩, evaluation⟩ :=
    SourceDependencyAnnotations.beta_expression source closed
  subst dependencies
  exact ⟨reduced, remaining, next,
    (Local.silent_prefix argumentSilent).mp ((Local.silent_prefix functionSilent).mp checked), ⟨function, argument, rfl, functionSilent, argumentSilent⟩, evaluation⟩

end Ash.OneShot.SourceDependencyNeutral.Lexical.Recursive
#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.Recursive.bind_preserves_local
#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.Recursive.beta_preserves_local


namespace Ash.OneShot.SourceDependencyNeutral.Lexical.Recursive
open ScopedExpressions ProtectionContracts
open SourceDependencyCapture (Scope OwnerCut OwnerSelection select lookupDependencies)
open SourceDependencyChecks.Lexical (ReturnHints ReturnBoundary Capture)
open SourceDependencyChecks.Lexical.ReturnHints.Recursive (Local Pending callbackBoundary)
open OwnerPhaseTransitions (Phases spend)
open LexicalUnwind (UseMode)

/-- Insert spent history, a pure waiting frame or a pure cleanup on the active lexical spine. Every
return-marker kind and dormant continuation stays unchanged. This proof relation
also supports the existing structural source recipe for pure cleanup. -/
inductive History : {first second : Scope} → ReturnHints first → ReturnHints second → Prop where
  | refl : History hints hints
  | pureFrame : History before after → History before (.plain (dependencies := .pure) after)
  | completion : History before after → History before (.cleanup (needs := []) (callback := .pure) after)
  | history : History before after → History before (.spent (owner := owner) after)
  | plain : History before after →
      History (.plain (dependencies := dependencies) before) (.plain (dependencies := dependencies) after)
  | handler : History before after →
      History (.handler (effect := effect) (table := table) (families := families) before)
        (.handler (effect := effect) (table := table) (families := families) after)
  | cell : History before after → History (.cell (identity := identity) before) (.cell (identity := identity) after)
  | cleanup : History before after →
      History (.cleanup (needs := needs) (callback := callback) before) (.cleanup (needs := needs) (callback := callback) after)
  | running : History before after → History (.running kind before) (.running kind after)
  | live : History before after → History (.live (owner := owner) saved before) (.live (owner := owner) saved after)
  | spent : History before after → History (.spent (owner := owner) before) (.spent (owner := owner) after)

theorem History.prefix (front : ReturnHints scope) (changed : History first second) :
    History (front.append first) (front.append second) := by
  induction front with
  | nil => exact changed
  | plain rest ih => exact .plain ih
  | handler rest ih => exact .handler ih
  | cell rest ih => exact .cell ih
  | cleanup rest ih => exact .cleanup ih
  | running kind rest ih => exact .running ih
  | live saved rest ihSaved ihRest => exact .live ihRest
  | spent rest ih => exact .spent ih

theorem History.append (first : History a b) (second : History c d) :
    History (a.append c) (b.append d) := by
  induction first with
  | refl => exact second.prefix _
  | history next ih => exact .history ih
  | pureFrame next ih => exact .pureFrame ih
  | completion next ih => exact .completion ih
  | plain next ih => exact .plain ih
  | handler next ih => exact .handler ih
  | cell next ih => exact .cell ih
  | cleanup next ih => exact .cleanup ih
  | running next ih => exact .running ih
  | live next ih => exact .live ih
  | spent next ih => exact .spent ih

theorem History.held {before : ReturnHints first} {after : ReturnHints second} (changed : History before after) :
    first.held = second.held := by
  induction changed <;> simp_all [Scope.held]


theorem History.return_mode (changed : History before after) (mode : UseMode) :
    before.returnMode mode = after.returnMode mode := by
  induction changed generalizing mode <;> simp_all [ReturnHints.returnMode]

/-- Forget return annotations only to reuse existing scope observations. -/
def eraseReturn : ReturnHints scope → SourceContextualHints.Hints scope
  | .nil => .nil
  | .plain rest => .plain (eraseReturn rest)
  | .handler rest => .handler [] (eraseReturn rest)
  | .cell rest => .cell (eraseReturn rest)
  | .cleanup rest => .cleanup (eraseReturn rest)
  | .running _ rest => .running (eraseReturn rest)
  | .live saved rest => .live (eraseReturn saved) (eraseReturn rest)
  | .spent rest => .spent (eraseReturn rest)

theorem History.erases (changed : History before after) :
    SourcePlannedNeutralFrames.Expansion (eraseReturn before) (eraseReturn after) := by
  induction changed with
  | refl => exact .refl
  | history next ih => exact .history ih
  | pureFrame next ih => exact .extra ih
  | completion next ih => exact .completion ih
  | plain next ih => exact .plain ih
  | handler next ih => exact .handler ih
  | cell next ih => exact .cell ih
  | cleanup next ih => exact .cleanup ih
  | running next ih => exact .running ih
  | live next ih => exact .live ih
  | spent next ih => exact .spent ih

abbrev Modes := Option (Nat → SourceDependencyAnnotations.Dependencies) × Option (Nat → SourceDependencyAnnotations.Dependencies)

inductive Cut (effect : Instance) (operation : Nat) (contract : ClauseContract) (modes : Modes) :
    {scope captured tail : Scope} → ReturnHints scope → ReturnHints captured → ReturnHints tail → Prop where
  | hit (known : lookup operation table = some contract) (declared : lookupDependencies operation families = some modes) :
      Cut effect operation contract modes
        (.handler (effect := effect) (table := table) (families := families) rest)
        (.handler (effect := effect) (table := table) (families := families) .nil) rest
  | plain : Cut effect operation contract modes rest saved waiting →
      Cut effect operation contract modes (.plain (dependencies := dependencies) rest) (.plain (dependencies := dependencies) saved) waiting
  | handler (different : effect ≠ other) : Cut effect operation contract modes rest saved waiting →
      Cut effect operation contract modes
        (.handler (effect := other) (table := table) (families := families) rest)
        (.handler (effect := other) (table := table) (families := families) saved) waiting
  | cell (different : effect ≠ .cell identity) : Cut effect operation contract modes rest saved waiting →
      Cut effect operation contract modes (.cell (identity := identity) rest) (.cell (identity := identity) saved) waiting
  | cleanup : Cut effect operation contract modes rest saved waiting →
      Cut effect operation contract modes (.cleanup (needs := needs) (callback := callback) rest)
        (.cleanup (needs := needs) (callback := callback) saved) waiting
  | running : Cut effect operation contract modes rest saved waiting →
      Cut effect operation contract modes (.running kind rest) (.running kind saved) waiting
  | live : Cut effect operation contract modes rest saved waiting →
      Cut effect operation contract modes (.live (owner := owner) dormant rest) (.live (owner := owner) dormant saved) waiting
  | spent : Cut effect operation contract modes rest saved waiting →
      Cut effect operation contract modes (.spent (owner := owner) rest) (.spent (owner := owner) saved) waiting

theorem Cut.lookup {whole : ReturnHints scope} {saved : ReturnHints captured} {waiting : ReturnHints tail}
    (cut : Cut effect operation contract modes whole saved waiting) :
    select effect operation scope = some (.handler captured tail contract modes) := by
  induction cut with
  | hit known declared => simp [select, known, declared]
  | handler different next ih | cell different next ih =>
      simp only [select, if_neg different, ih, Option.map_some, SourceDependencyCapture.Selection.prepend]
  | plain next ih | cleanup next ih | running next ih | live next ih | spent next ih =>
      simp only [select, ih, Option.map_some, SourceDependencyCapture.Selection.prepend]

theorem Cut.reconstruct_scope {scope : Scope} {whole : ReturnHints scope} {saved : ReturnHints captured} {waiting : ReturnHints tail}
    (cut : Cut effect operation contract modes whole saved waiting) : scope = captured.append tail := by
  induction cut <;> simp_all [Scope.append]

theorem Cut.hints {whole : ReturnHints scope} {saved : ReturnHints captured} {waiting : ReturnHints tail}
    (cut : Cut effect operation contract modes whole saved waiting) : HEq whole (saved.append waiting) := by
  induction cut with
  | hit => rfl
  | plain next ih | handler different next ih | cell different next ih | cleanup next ih
  | running next ih | live next ih | spent next ih =>
      have same := next.reconstruct_scope
      cases same
      cases ih
      rfl

/-- Recover the exact annotated pieces from the existing lookup result. This
is a proof of its structural cut, not a second selection algorithm. -/
theorem of_lookup (hints : ReturnHints scope)
    (found : select effect operation scope = some (.handler captured tail contract modes)) :
    ∃ saved : ReturnHints captured, ∃ waiting : ReturnHints tail, Cut effect operation contract modes hints saved waiting := by
  induction hints generalizing captured tail with
  | nil => cases found
  | handler rest ih =>
      rename_i handlerEffect table families
      by_cases same : effect = handlerEffect
      · subst handlerEffect
        simp only [select] at found
        cases known : lookup operation table with
        | none => simp [known] at found
        | some offered =>
            cases declared : lookupDependencies operation families with
            | none => simp [known, declared] at found
            | some bodyModes =>
                simp only [known, declared] at found
                cases Option.some.inj found
                exact ⟨_, _, .hit known declared⟩
      · simp only [select, if_neg same, Option.map_eq_some_iff] at found
        obtain ⟨selected, looked, sameSelection⟩ := found
        cases selected with
        | builtin identity => cases sameSelection
        | handler inside outside offered bodyModes =>
            cases sameSelection
            obtain ⟨saved, waiting, cut⟩ := ih looked
            exact ⟨_, _, .handler same cut⟩
  | cell rest ih =>
      rename_i identity
      by_cases same : effect = .cell identity
      · simp [select, same] at found
      · simp only [select, if_neg same, Option.map_eq_some_iff] at found
        obtain ⟨selected, looked, sameSelection⟩ := found
        cases selected with
        | builtin identity => cases sameSelection
        | handler inside outside offered bodyModes =>
            cases sameSelection
            obtain ⟨saved, waiting, cut⟩ := ih looked
            exact ⟨_, _, .cell same cut⟩
  | plain rest ih | cleanup rest ih | running kind rest ih | live dormant rest ihDormant ih | spent rest ih =>
      simp only [select, Option.map_eq_some_iff] at found
      obtain ⟨selected, looked, sameSelection⟩ := found
      cases selected with
      | builtin identity => cases sameSelection
      | handler inside outside offered bodyModes =>
          cases sameSelection
          obtain ⟨saved, waiting, cut⟩ := ih looked
          first
          | exact ⟨_, _, .plain cut⟩
          | exact ⟨_, _, .cleanup cut⟩
          | exact ⟨_, _, .running cut⟩
          | exact ⟨_, _, .live cut⟩
          | exact ⟨_, _, .spent cut⟩

/-- History insertion preserves the selected handler, modes and annotations
of both resulting pieces. -/
theorem expand {saved : ReturnHints captured} {waiting : ReturnHints tail} (changed : History before after)
    (cut : Cut effect operation contract modes before saved waiting) :
    ∃ captured tail, ∃ nextSaved : ReturnHints captured, ∃ nextWaiting : ReturnHints tail,
      Cut effect operation contract modes after nextSaved nextWaiting ∧
      History saved nextSaved ∧ History waiting nextWaiting := by
  induction changed generalizing captured tail with
  | refl => exact ⟨_, _, _, _, cut, .refl, .refl⟩
  | pureFrame changed ih =>
      obtain ⟨_, _, saved, waiting, cut, inside, outside⟩ := ih cut
      exact ⟨_, _, _, _, .plain cut, .pureFrame inside, outside⟩
  | completion changed ih =>
      obtain ⟨_, _, saved, waiting, cut, inside, outside⟩ := ih cut
      exact ⟨_, _, _, _, .cleanup cut, .completion inside, outside⟩
  | history changed ih =>
      obtain ⟨_, _, saved, waiting, cut, inside, outside⟩ := ih cut
      exact ⟨_, _, _, _, .spent cut, .history inside, outside⟩
  | handler changed ih => cases cut with
    | hit known declared => exact ⟨_, _, _, _, .hit known declared, .refl, changed⟩
    | handler different next =>
        obtain ⟨_, _, saved, waiting, cut, inside, outside⟩ := ih next
        exact ⟨_, _, _, _, .handler different cut, .handler inside, outside⟩
  | plain changed ih => cases cut with
    | plain next =>
        obtain ⟨_, _, saved, waiting, cut, inside, outside⟩ := ih next
        exact ⟨_, _, _, _, .plain cut, .plain inside, outside⟩
  | cell changed ih => cases cut with
    | cell different next =>
        obtain ⟨_, _, saved, waiting, cut, inside, outside⟩ := ih next
        exact ⟨_, _, _, _, .cell different cut, .cell inside, outside⟩
  | cleanup changed ih => cases cut with
    | cleanup next =>
        obtain ⟨_, _, saved, waiting, cut, inside, outside⟩ := ih next
        exact ⟨_, _, _, _, .cleanup cut, .cleanup inside, outside⟩
  | running changed ih => cases cut with
    | running next =>
        obtain ⟨_, _, saved, waiting, cut, inside, outside⟩ := ih next
        exact ⟨_, _, _, _, .running cut, .running inside, outside⟩
  | live changed ih => cases cut with
    | live next =>
        obtain ⟨_, _, saved, waiting, cut, inside, outside⟩ := ih next
        exact ⟨_, _, _, _, .live cut, .live inside, outside⟩
  | spent changed ih => cases cut with
    | spent next =>
        obtain ⟨_, _, saved, waiting, cut, inside, outside⟩ := ih next
        exact ⟨_, _, _, _, .spent cut, .spent inside, outside⟩

/-- At fixed captured and waiting scopes, return-annotation splitting is unique. -/
theorem append_injective {first second : ReturnHints captured} {outside otherOutside : ReturnHints tail}
    (same : first.append outside = second.append otherOutside) : first = second ∧ outside = otherOutside := by
  induction first with
  | nil => cases second; exact ⟨rfl, same⟩
  | plain rest ih => cases second with
    | plain other => obtain ⟨rfl, rfl⟩ := ih (ReturnHints.plain.inj same); exact ⟨rfl, rfl⟩
  | handler rest ih => cases second with
    | handler other => obtain ⟨rfl, rfl⟩ := ih (ReturnHints.handler.inj same); exact ⟨rfl, rfl⟩
  | cell rest ih => cases second with
    | cell other => obtain ⟨rfl, rfl⟩ := ih (ReturnHints.cell.inj same); exact ⟨rfl, rfl⟩
  | cleanup rest ih => cases second with
    | cleanup other => obtain ⟨rfl, rfl⟩ := ih (ReturnHints.cleanup.inj same); exact ⟨rfl, rfl⟩
  | running kind rest ih => cases second with
    | running otherKind other =>
        obtain ⟨rfl, next⟩ := ReturnHints.running.inj same
        obtain ⟨rfl, rfl⟩ := ih next
        exact ⟨rfl, rfl⟩
  | live saved rest ihSaved ihRest => cases second with
    | live otherSaved other =>
        obtain ⟨rfl, next⟩ := ReturnHints.live.inj same
        obtain ⟨rfl, rfl⟩ := ihRest next
        exact ⟨rfl, rfl⟩
  | spent rest ih => cases second with
    | spent other => obtain ⟨rfl, rfl⟩ := ih (ReturnHints.spent.inj same); exact ⟨rfl, rfl⟩

theorem Cut.unique {whole : ReturnHints scope} {first second : ReturnHints captured} {outside otherOutside : ReturnHints tail}
    (cut : Cut effect operation contract modes whole first outside)
    (same : HEq whole (second.append otherOutside)) : first = second ∧ outside = otherOutside :=
  append_injective (eq_of_heq (cut.hints.symm.trans same))

structure Selection where
  scopes : OwnerSelection
  front : ReturnHints scopes.front
  saved : ReturnHints scopes.captured
  tail : ReturnHints scopes.tail

def Selection.prepend (layer : Scope → Scope)
    (lift : {scope : Scope} → ReturnHints scope → ReturnHints (layer scope)) (selected : Selection) : Selection :=
  ⟨selected.scopes.prepend layer, lift selected.front, selected.saved, selected.tail⟩

/-- Decorate the existing active-owner lookup with return annotations. The
erasure theorem below authenticates it against that lookup. -/
def findOwner (owner : Nat) : {scope : Scope} → ReturnHints scope → Option Selection
  | _, .nil => none
  | .plain dependencies _, .plain rest =>
      (findOwner owner rest).map (Selection.prepend (.plain dependencies) .plain)
  | .handler effect table families _, .handler rest =>
      (findOwner owner rest).map (Selection.prepend (.handler effect table families) (.handler))
  | .cell identity _, .cell rest =>
      (findOwner owner rest).map (Selection.prepend (.cell identity) .cell)
  | .cleanup needs callback _, .cleanup rest =>
      (findOwner owner rest).map (Selection.prepend (.cleanup needs callback) .cleanup)
  | _, .running kind rest => (findOwner owner rest).map (Selection.prepend .running (.running kind))
  | .live other _ _, .live saved rest =>
      if owner = other then some ⟨⟨.nil, _, _⟩, .nil, saved, rest⟩
      else (findOwner owner rest).map (Selection.prepend (.live other _) (.live saved))
  | .spent other _, .spent rest =>
      (findOwner owner rest).map (Selection.prepend (.spent other) .spent)

theorem find_owner_erases (hints : ReturnHints scope) :
    (findOwner owner hints).map Selection.scopes = SourceDependencyCapture.findOwner owner scope := by
  induction hints with
  | nil => rfl
  | live saved rest ihSaved ihRest =>
      simp only [findOwner, SourceDependencyCapture.findOwner]
      split
      · rfl
      · rw [← ihRest]; cases findOwner owner rest <;> rfl
  | plain rest ih | handler rest ih | cell rest ih | cleanup rest ih
  | running kind rest ih | spent rest ih =>
      simp only [findOwner, SourceDependencyCapture.findOwner]
      rw [← ih]
      cases findOwner owner rest <;> rfl

theorem selected_cut {hints : ReturnHints scope} (found : findOwner owner hints = some selected) :
    SourceDependencyCapture.OwnerCut owner scope selected.scopes := by
  apply SourceDependencyCapture.find_owner_sound
  rw [← find_owner_erases hints, found]
  rfl


theorem selected_reconstructed_cut {hints : ReturnHints scope}
    (found : findOwner owner hints = some selected) :
    OwnerCut owner (selected.scopes.front.append (.live owner selected.scopes.captured selected.scopes.tail))
      selected.scopes := by
  have cut := selected_cut found
  rw [← cut.reconstruct]
  exact cut

theorem selected_hints {hints : ReturnHints scope}
    (found : findOwner owner hints = some selected) :
    HEq hints (selected.front.append (.live (owner := owner) selected.saved selected.tail)) := by
  induction hints generalizing selected with
  | nil => cases found
  | live saved rest ihSaved ih =>
      simp only [findOwner] at found
      split at found
      next hit => subst_vars; cases Option.some.inj found; rfl
      next miss =>
        obtain ⟨inside, located, rfl⟩ := Option.map_eq_some_iff.mp found
        have same := (selected_cut located).reconstruct
        have related := ih located
        cases same
        cases related
        rfl
  | plain rest ih | handler rest ih | cell rest ih | cleanup rest ih
  | running kind rest ih | spent rest ih =>
      obtain ⟨inside, located, rfl⟩ := Option.map_eq_some_iff.mp found
      have same := (selected_cut located).reconstruct
      have related := ih located
      cases same
      cases related
      rfl

theorem find_owner_pieces {front : ReturnHints frontScope}
    {saved : ReturnHints savedScope} {tail : ReturnHints tailScope}
    (located : OwnerCut owner (frontScope.append (.live owner savedScope tailScope))
      ⟨frontScope, savedScope, tailScope⟩) :
    findOwner owner (front.append (.live (owner := owner) saved tail)) =
      some ⟨⟨frontScope, savedScope, tailScope⟩, front, saved, tail⟩ := by
  have erased := find_owner_erases (owner := owner) (front.append (.live (owner := owner) saved tail))
  rw [located.lookup] at erased
  obtain ⟨selected, found, same⟩ := Option.map_eq_some_iff.mp erased
  cases selected with
  | mk scopes caller captured waiting =>
    cases same
    obtain ⟨rfl, remaining⟩ := append_injective (eq_of_heq (selected_hints (owner := owner) (hints := front.append (.live (owner := owner) saved tail)) found))
    obtain ⟨rfl, rfl⟩ := ReturnHints.live.inj remaining
    exact found

inductive OwnerHistory : Selection → Selection → Prop where
  | pieces {front : ReturnHints firstFront} {nextFront : ReturnHints secondFront}
      {saved : ReturnHints savedScope} {tail : ReturnHints firstTail} {nextTail : ReturnHints secondTail}
      (caller : History front nextFront) (waiting : History tail nextTail) :
      OwnerHistory ⟨⟨firstFront, savedScope, firstTail⟩, front, saved, tail⟩
        ⟨⟨secondFront, savedScope, secondTail⟩, nextFront, saved, nextTail⟩

private theorem owner_refl (selected : Selection) : OwnerHistory selected selected := by
  cases selected with
  | mk scopes front saved tail => cases scopes; exact .pieces .refl .refl

private theorem OwnerHistory.prepend (changed : OwnerHistory first second)
    (layer : Scope → Scope) (lift : ∀ {scope}, ReturnHints scope → ReturnHints (layer scope))
    (preserves : ∀ {a b} {before : ReturnHints a} {after : ReturnHints b}, History before after → History (lift before) (lift after)) :
    OwnerHistory (first.prepend layer lift) (second.prepend layer lift) := by
  cases changed with | pieces caller waiting => exact .pieces (preserves caller) waiting

private theorem OwnerHistory.pureFrame (changed : OwnerHistory first second) :
    OwnerHistory first (second.prepend (.plain .pure) .plain) := by
  cases changed with | pieces caller waiting => exact .pieces (.pureFrame caller) waiting

private theorem OwnerHistory.completion (changed : OwnerHistory first second) :
    OwnerHistory first (second.prepend (.cleanup [] .pure) .cleanup) := by
  cases changed with | pieces caller waiting => exact .pieces (.completion caller) waiting

private theorem OwnerHistory.history (changed : OwnerHistory first second) :
    OwnerHistory first (second.prepend (.spent owner) .spent) := by
  cases changed with | pieces caller waiting => exact .pieces (.history caller) waiting

/-- Owner lookup still selects the same saved program and owner identity. -/
theorem History.find_owner (changed : History before after)
    (found : findOwner owner before = some selected) :
    ∃ next, findOwner owner after = some next ∧ OwnerHistory selected next := by
  induction changed generalizing selected with
  | refl => exact ⟨_, found, owner_refl _⟩
  | pureFrame changed ih =>
      obtain ⟨next, selected, same⟩ := ih found
      exact ⟨_, by simp only [findOwner, selected, Option.map_some], same.pureFrame⟩
  | completion changed ih =>
      obtain ⟨next, selected, same⟩ := ih found
      exact ⟨_, by simp only [findOwner, selected, Option.map_some], same.completion⟩
  | history changed ih =>
      rename_i historyOwner
      obtain ⟨next, selected, same⟩ := ih found
      exact ⟨_, by simp only [findOwner, selected, Option.map_some], same.history (owner := historyOwner)⟩
  | live changed ih =>
      simp only [findOwner] at found ⊢
      split at found
      next hit =>
        cases Option.some.inj found
        exact ⟨_, by simp only [if_pos hit], .pieces .refl changed⟩
      next miss =>
        simp only [if_neg miss, Option.map_eq_some_iff] at found ⊢
        obtain ⟨inside, located, rfl⟩ := found
        obtain ⟨next, locatedNext, same⟩ := ih located
        exact ⟨_, ⟨next, locatedNext, rfl⟩, same.prepend _ _ (fun changed => .live changed)⟩
  | plain changed ih =>
      simp only [findOwner, Option.map_eq_some_iff] at found ⊢
      obtain ⟨inside, located, rfl⟩ := found
      obtain ⟨next, locatedNext, same⟩ := ih located
      exact ⟨_, ⟨next, locatedNext, rfl⟩, same.prepend _ _ (fun changed => .plain changed)⟩
  | handler changed ih =>
      simp only [findOwner, Option.map_eq_some_iff] at found ⊢
      obtain ⟨inside, located, rfl⟩ := found
      obtain ⟨next, locatedNext, same⟩ := ih located
      exact ⟨_, ⟨next, locatedNext, rfl⟩, same.prepend _ _ (fun changed => .handler changed)⟩
  | cell changed ih =>
      simp only [findOwner, Option.map_eq_some_iff] at found ⊢
      obtain ⟨inside, located, rfl⟩ := found
      obtain ⟨next, locatedNext, same⟩ := ih located
      exact ⟨_, ⟨next, locatedNext, rfl⟩, same.prepend _ _ (fun changed => .cell changed)⟩
  | cleanup changed ih =>
      simp only [findOwner, Option.map_eq_some_iff] at found ⊢
      obtain ⟨inside, located, rfl⟩ := found
      obtain ⟨next, locatedNext, same⟩ := ih located
      exact ⟨_, ⟨next, locatedNext, rfl⟩, same.prepend _ _ (fun changed => .cleanup changed)⟩
  | running changed ih =>
      simp only [findOwner, Option.map_eq_some_iff] at found ⊢
      obtain ⟨inside, located, rfl⟩ := found
      obtain ⟨next, locatedNext, same⟩ := ih located
      exact ⟨_, ⟨next, locatedNext, rfl⟩, same.prepend _ _ (fun changed => .running changed)⟩
  | spent changed ih =>
      simp only [findOwner, Option.map_eq_some_iff] at found ⊢
      obtain ⟨inside, located, rfl⟩ := found
      obtain ⟨next, locatedNext, same⟩ := ih located
      exact ⟨_, ⟨next, locatedNext, rfl⟩, same.prepend _ _ (fun changed => .spent changed)⟩


theorem return_mode_heq {before : ReturnHints first} {after : ReturnHints second}
    (scopes : first = second) (same : HEq before after) (mode : UseMode) : before.returnMode mode = after.returnMode mode := by
  cases scopes
  cases eq_of_heq same
  rfl

/-- A pure waiting frame has no executing or abandoned-code obligation. -/
theorem pending_pure_frame
    (checked : Pending outward actions phases world hints outside before after) :
    Pending outward actions phases world (.plain (dependencies := .pure) hints) outside before after := by
  cases before with
  | ordinary => exact .plain .pure checked
  | unwind => exact .skipped checked

/-- Neutral insertions cannot change dispatch, invocation rights or callback return
mode. Prove this simultaneously for executing and retained source checks. -/
theorem local_history
    (checked : Local outward actions phases world dependencies hints)
    {next : ReturnHints nextScope} (changed : History hints next) :
    Local outward actions phases world dependencies next := by
  refine (Local.rec
    (motive_1 := fun phases world dependencies scope hints _ => ∀ {nextScope}
      (next : ReturnHints nextScope), History hints next →
      Local outward actions phases world dependencies next)
    (motive_2 := fun phases world scope outside hints outsideHints initial finalMode _ =>
      ∀ {nextScope nextOutside} (next : ReturnHints nextScope) (nextOutsideHints : ReturnHints nextOutside),
      History hints next → History outsideHints nextOutsideHints →
      Pending outward actions phases world next nextOutsideHints initial finalMode)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (t := checked)) next changed
  · intros; exact .pure
  · intros
    rename_i guard callbacks bounded ihCallbacks nextScope next changed
    cases guard with
    | builtin found =>
        have nextFound := SourcePlannedCuts.builtin_expand changed.erases found
        apply Local.request (.builtin nextFound)
        · intro capturedScope tailScope saved waiting contract modes same found disposes
          cases Option.some.inj (nextFound.symm.trans found)
        · intro saved waiting contract modes found disposes
          cases Option.some.inj (nextFound.symm.trans found)
    | handler found permission row body =>
        obtain ⟨saved, waiting, cut⟩ := of_lookup _ found
        obtain ⟨_, _, nextSaved, nextWaiting, nextCut, inside, outside⟩ := expand changed cut
        apply Local.request (.handler nextCut.lookup (inside.held ▸ permission)
          (inside.held ▸ row) (inside.held ▸ body))
        · intro actualSavedScope actualWaitingScope actualSaved actualWaiting contract modes same actual disposes
          cases Option.some.inj (nextCut.lookup.symm.trans actual)
          obtain ⟨rfl, rfl⟩ := nextCut.unique same
          exact ihCallbacks saved waiting _ _ cut.hints found disposes nextSaved (.running .close nextWaiting)
            inside (.running outside)
        · intro actualSaved actualWaiting contract modes actual disposes
          cases Option.some.inj (nextCut.lookup.symm.trans actual)
          have owners := inside.erases.pending_owners (bounded _ _ _ _ found disposes)
          rw [inside.erases.owners] at owners
          exact owners
  · intros
    rename_i frontScope capturedScope tailScope owner rights phases world front captured tail located known permission available restored ih nextScope next changed
    obtain ⟨nextSelected, foundNext, related⟩ := changed.find_owner (find_owner_pieces located)
    have same := selected_hints foundNext
    have modes := (changed.return_mode .ordinary).trans (return_mode_heq (selected_cut foundNext).reconstruct same .ordinary)
    have expansion : History (captured.append (front.append (.spent (owner := owner) tail)))
        (nextSelected.saved.append (nextSelected.front.append (.spent (owner := owner) nextSelected.tail))) := by
      cases related with | pieces caller waiting => exact (caller.append (.spent waiting)).prefix _
    have transported := ih _ .nil expansion .refl
    rw [modes] at transported
    exact (Local.resume (front := nextSelected.front) (captured := nextSelected.saved) (tail := nextSelected.tail)
      (selected_reconstructed_cut foundNext) known permission available transported).reindex_scope
        (selected_cut foundNext).reconstruct.symm same.symm
  · intros
    rename_i frontScope capturedScope tailScope owner rights phases world front captured tailHints located known permission available unprotected abandoned waiting ihAbandoned ihWaiting nextScope next changed
    obtain ⟨nextSelected, foundNext, related⟩ := changed.find_owner (find_owner_pieces located)
    have same := selected_hints foundNext
    have modes := (changed.return_mode .ordinary).trans (return_mode_heq (selected_cut foundNext).reconstruct same .ordinary)
    cases related with
    | pieces caller tail =>
      rename_i nextFrontScope nextTailScope nextFront nextTail
      have outside := caller.append (.spent (owner := owner) tail)
      have nextAbandoned := ihAbandoned _ _ .refl (.running outside)
      have nextWaiting := ihWaiting _ .nil outside .refl
      rw [modes] at nextWaiting
      exact (Local.dispose (front := nextFront) (captured := captured) (tail := nextTail) (selected_reconstructed_cut foundNext) known permission available unprotected nextAbandoned nextWaiting).reindex_scope
        (selected_cut foundNext).reconstruct.symm same.symm
  · intros
    rename_i first second ihFirst ihSecond nextScope next changed
    exact .sequence (ihFirst (.plain next) (.plain changed)) (ihSecond next changed)
  · intros
    rename_i first second ihFirst ihSecond nextScope next changed
    exact .choice (ihFirst next changed) (ihSecond next changed)
  · intros
    rename_i body ih nextScope next changed
    exact .handler (ih (.handler next) (.handler changed))
  · intros
    rename_i body completion ihBody ihCompletion nextScope next changed
    exact .cleanup (ihBody (.cleanup next) (.cleanup changed))
      (ihCompletion (.running .normal next) (.running changed))
  · intros
    rename_i body ih nextScope next changed
    exact .resource (fun identity fresh => ih identity fresh (.cell next) (.cell changed))
  · intros
    rename_i nextScope nextOutside next nextOutsideHints changed outsideChanged
    induction next <;> cases changed
    all_goals first
      | exact .nil
      | (rename_i ihHistory history; exact .spent (ihHistory history))
      | (rename_i ihCompletion completion; exact .cleanup .pure (ihCompletion completion))
      | (rename_i ihFrame inserted; exact pending_pure_frame (ihFrame inserted))
  · intros
    rename_i code tail ihCode ihTail nextScope nextOutside next nextOutsideHints changed outsideChanged
    induction next <;> cases changed
    all_goals first
      | (rename_i ihHistory history; exact .spent (ihHistory history))
      | (rename_i ihCompletion completion; exact .cleanup .pure (ihCompletion completion))
      | (rename_i ihFrame inserted; exact pending_pure_frame (ihFrame inserted))
      | exact .plain (ihCode _ (History.append (by first | exact .refl | assumption) outsideChanged))
          (ihTail _ nextOutsideHints (by first | exact .refl | assumption) outsideChanged)
  · intros
    rename_i tail ih nextScope nextOutside next nextOutsideHints changed outsideChanged
    induction next <;> cases changed
    all_goals first
      | (rename_i ihHistory history; exact .spent (ihHistory history))
      | (rename_i ihCompletion completion; exact .cleanup .pure (ihCompletion completion))
      | (rename_i ihFrame inserted; exact pending_pure_frame (ihFrame inserted))
      | exact .skipped (ih _ nextOutsideHints (by first | exact .refl | assumption) outsideChanged)
  · intros
    rename_i tail ih nextScope nextOutside next nextOutsideHints changed outsideChanged
    induction next <;> cases changed
    all_goals first
      | (rename_i ihHistory history; exact .spent (ihHistory history))
      | (rename_i ihCompletion completion; exact .cleanup .pure (ihCompletion completion))
      | (rename_i ihFrame inserted; exact pending_pure_frame (ihFrame inserted))
      | exact .handler (ih _ nextOutsideHints (by first | exact .refl | assumption) outsideChanged)
  · intros
    rename_i tail ih nextScope nextOutside next nextOutsideHints changed outsideChanged
    induction next <;> cases changed
    all_goals first
      | (rename_i ihHistory history; exact .spent (ihHistory history))
      | (rename_i ihCompletion completion; exact .cleanup .pure (ihCompletion completion))
      | (rename_i ihFrame inserted; exact pending_pure_frame (ihFrame inserted))
      | exact .cell (ih _ nextOutsideHints (by first | exact .refl | assumption) outsideChanged)
  · intros
    rename_i code tail ihCode ihTail nextScope nextOutside next nextOutsideHints changed outsideChanged
    induction next <;> cases changed
    all_goals first
      | (rename_i ihHistory history; exact .spent (ihHistory history))
      | (rename_i ihCompletion completion; exact .cleanup .pure (ihCompletion completion))
      | (rename_i ihFrame inserted; exact pending_pure_frame (ihFrame inserted))
      | exact .cleanup (ihCode _ (.running (History.append (by first | exact .refl | assumption) outsideChanged)))
          (ihTail _ nextOutsideHints (by first | exact .refl | assumption) outsideChanged)
  · intros
    rename_i tail ih nextScope nextOutside next nextOutsideHints changed outsideChanged
    induction next <;> cases changed
    all_goals first
      | (rename_i ihHistory history; exact .spent (ihHistory history))
      | (rename_i ihCompletion completion; exact .cleanup .pure (ihCompletion completion))
      | (rename_i ihFrame inserted; exact pending_pure_frame (ihFrame inserted))
      | exact .normal (ih _ nextOutsideHints (by first | exact .refl | assumption) outsideChanged)
  · intros
    rename_i tail ih nextScope nextOutside next nextOutsideHints changed outsideChanged
    induction next <;> cases changed
    all_goals first
      | (rename_i ihHistory history; exact .spent (ihHistory history))
      | (rename_i ihCompletion completion; exact .cleanup .pure (ihCompletion completion))
      | (rename_i ihFrame inserted; exact pending_pure_frame (ihFrame inserted))
      | exact .unwinding (ih _ nextOutsideHints (by first | exact .refl | assumption) outsideChanged)
  · intros
    rename_i tail ih nextScope nextOutside next nextOutsideHints changed outsideChanged
    induction next <;> cases changed
    all_goals first
      | (rename_i ihHistory history; exact .spent (ihHistory history))
      | (rename_i ihCompletion completion; exact .cleanup .pure (ihCompletion completion))
      | (rename_i ihFrame inserted; exact pending_pure_frame (ihFrame inserted))
      | exact .closing (ih _ nextOutsideHints (by first | exact .refl | assumption) outsideChanged)
  · intros
    rename_i tail ih nextScope nextOutside next nextOutsideHints changed outsideChanged
    induction next <;> cases changed
    all_goals first
      | (rename_i ihHistory history; exact .spent (ihHistory history))
      | (rename_i ihCompletion completion; exact .cleanup .pure (ihCompletion completion))
      | (rename_i ihFrame inserted; exact pending_pure_frame (ihFrame inserted))
      | exact .retiring (ih _ nextOutsideHints (by first | exact .refl | assumption) outsideChanged)
  · intros
    rename_i code tail ihCode ihTail nextScope nextOutside next nextOutsideHints changed outsideChanged
    induction next <;> cases changed
    all_goals first
      | (rename_i ihHistory history; exact .spent (ihHistory history))
      | (rename_i ihCompletion completion; exact .cleanup .pure (ihCompletion completion))
      | (rename_i ihFrame inserted; exact pending_pure_frame (ihFrame inserted))
      | exact .live (ihCode _ _ .refl (History.append (by first | exact .refl | assumption) outsideChanged))
          (ihTail _ nextOutsideHints (by first | exact .refl | assumption) outsideChanged)
  · intros
    rename_i code tail ihCode ihTail nextScope nextOutside next nextOutsideHints changed outsideChanged
    induction next <;> cases changed
    all_goals first
      | (rename_i ihHistory history; exact .spent (ihHistory history))
      | (rename_i ihCompletion completion; exact .cleanup .pure (ihCompletion completion))
      | (rename_i ihFrame inserted; exact pending_pure_frame (ihFrame inserted))
      | exact .opening (ihCode _ _ .refl (.running (History.append (by first | exact .refl | assumption) outsideChanged)))
          (ihTail _ nextOutsideHints (by first | exact .refl | assumption) outsideChanged)
  · intros
    rename_i tail ih nextScope nextOutside next nextOutsideHints changed outsideChanged
    induction next <;> cases changed
    all_goals first
      | (rename_i ihHistory history; exact .spent (ihHistory history))
      | (rename_i ihCompletion completion; exact .cleanup .pure (ihCompletion completion))
      | (rename_i ihFrame inserted; exact pending_pure_frame (ihFrame inserted))
      | exact .spent (ih _ nextOutsideHints (by first | exact .refl | assumption) outsideChanged)

/-- Moving the receiving suffix keeps all saved code and callbacks checked in
that same suffix, including callbacks that return to unwinding. -/
theorem pending_outside_history {hints : ReturnHints scope} {outside : ReturnHints outsideScope}
    {next : ReturnHints nextScope}
    (checked : Pending outward actions phases world hints outside before after)
    (changed : History outside next) : Pending outward actions phases world hints next before after := by
  induction hints generalizing outsideScope nextScope before after with
  | nil => cases checked; exact .nil
  | plain rest ih => cases checked with
    | plain code tail => exact .plain (local_history code (changed.prefix rest)) (ih tail changed)
    | skipped tail => exact .skipped (ih tail changed)
  | handler rest ih => cases checked with | handler tail => exact .handler (ih tail changed)
  | cell rest ih => cases checked with | cell tail => exact .cell (ih tail changed)
  | cleanup rest ih => cases checked with | cleanup callback tail =>
      exact .cleanup (local_history callback (.running (changed.prefix rest))) (ih tail changed)
  | running kind rest ih => cases checked with
    | normal tail => exact .normal (ih tail changed)
    | unwinding tail => exact .unwinding (ih tail changed)
    | closing tail => exact .closing (ih tail changed)
    | retiring tail => exact .retiring (ih tail changed)
  | live saved rest ihSaved ihRest => cases checked with
    | live inside tail => exact .live (ihSaved inside (changed.prefix rest)) (ihRest tail changed)
    | opening inside tail => exact .opening (ihSaved inside (.running (changed.prefix rest))) (ihRest tail changed)
  | spent rest ih => cases checked with | spent tail => exact .spent (ih tail changed)

theorem pending_history {hints : ReturnHints scope} {next : ReturnHints nextScope}
    {outside : ReturnHints outsideScope} {nextOutside : ReturnHints nextOutsideScope}
    (checked : Pending outward actions phases world hints outside before after)
    (changed : History hints next) (outsideChanged : History outside nextOutside) :
    Pending outward actions phases world next nextOutside before after := by
  induction changed generalizing before after with
  | refl => exact pending_outside_history checked outsideChanged
  | history changed ih => exact .spent (ih checked)
  | pureFrame changed ih => exact pending_pure_frame (ih checked)
  | completion changed ih => exact .cleanup .pure (ih checked)
  | plain changed ih => cases checked with
    | plain code tail => exact .plain (local_history code (changed.append outsideChanged)) (ih tail)
    | skipped tail => exact .skipped (ih tail)
  | handler changed ih => cases checked with | handler tail => exact .handler (ih tail)
  | cell changed ih => cases checked with | cell tail => exact .cell (ih tail)
  | cleanup changed ih => cases checked with | cleanup callback tail =>
      exact .cleanup (local_history callback (.running (changed.append outsideChanged))) (ih tail)
  | running changed ih => cases checked with
    | normal tail => exact .normal (ih tail)
    | unwinding tail => exact .unwinding (ih tail)
    | closing tail => exact .closing (ih tail)
    | retiring tail => exact .retiring (ih tail)
  | live changed ih => cases checked with
    | live inside tail => exact .live (pending_outside_history inside (changed.append outsideChanged)) (ih tail)
    | opening inside tail => exact .opening (pending_outside_history inside (.running (changed.append outsideChanged))) (ih tail)
  | spent changed ih => cases checked with | spent tail => exact .spent (ih tail)

theorem running_congr {first : ReturnHints a} {second : ReturnHints b}
    (scopes : a = b) (same : HEq first second) (kind : ReturnBoundary) :
    HEq (ReturnHints.running kind first) (ReturnHints.running kind second) := by
  cases scopes
  cases eq_of_heq same
  rfl

/-- Recomposition is the converse of the existing annotated prefix split. -/
theorem pending_join {first : ReturnHints firstScope} {second : ReturnHints secondScope}
    {outside : ReturnHints outsideScope}
    (inside : Pending outward actions phases world first (second.append outside) before middle)
    (remaining : Pending outward actions phases world second outside middle after) :
    Pending outward actions phases world (first.append second) outside before after := by
  induction first generalizing outsideScope before middle after with
  | nil => cases inside; exact remaining
  | plain rest ih => cases inside with
    | plain code tail =>
      exact .plain
        (code.reindex_scope (SourceDependencyChecks.scope_append_assoc _ _ _).symm ReturnHints.append_assoc.symm)
        (ih tail remaining)
    | skipped tail => exact .skipped (ih tail remaining)
  | handler rest ih => cases inside with | handler tail => exact .handler (ih tail remaining)
  | cell rest ih => cases inside with | cell tail => exact .cell (ih tail remaining)
  | cleanup rest ih => cases inside with | cleanup callback tail =>
      exact .cleanup (callback.reindex_scope
        (congrArg Scope.running (SourceDependencyChecks.scope_append_assoc _ _ _).symm)
        (running_congr (SourceDependencyChecks.scope_append_assoc _ _ _).symm ReturnHints.append_assoc.symm _))
        (ih tail remaining)
  | running kind rest ih => cases inside with
    | normal tail => exact .normal (ih tail remaining)
    | unwinding tail => exact .unwinding (ih tail remaining)
    | closing tail => exact .closing (ih tail remaining)
    | retiring tail => exact .retiring (ih tail remaining)
  | live saved rest ihSaved ihRest => cases inside with
    | live cap tail =>
      exact .live
        (cap.reindex_outside (SourceDependencyChecks.scope_append_assoc _ _ _).symm ReturnHints.append_assoc.symm)
        (ihRest tail remaining)
    | opening cap tail =>
      exact .opening
        (cap.reindex_outside (congrArg Scope.running (SourceDependencyChecks.scope_append_assoc _ _ _).symm)
          (running_congr (SourceDependencyChecks.scope_append_assoc _ _ _).symm ReturnHints.append_assoc.symm _))
        (ihRest tail remaining)
  | spent rest ih => cases inside with | spent tail => exact .spent (ih tail remaining)

/-- A resuming clause is checked from its saved and waiting source. The spent
marker is inserted by proved transport; no restored-successor check is assumed. -/
theorem resume_clause_from_retained {captured : ReturnHints capturedScope} {tail : ReturnHints tailScope}
    (known : actions owner = some rights) (permission : rights.resume = true)
    (available : phases owner = .available)
    (retained : Pending outward actions (spend phases owner) world
      (.live (owner := owner) captured tail) .nil .ordinary finalMode) :
    Local outward actions phases world (.invoke ⟨owner, .resume⟩) (.live (owner := owner) captured tail) := by
  have mode := retained.return_mode
  cases retained with
  | live saved waiting =>
      apply Local.resume (front := .nil) .hit known permission available
      change Pending outward actions (spend phases owner) world
        (captured.append (.spent (owner := owner) tail)) .nil .ordinary
        ((ReturnHints.live (owner := owner) captured tail).returnMode .ordinary)
      rw [mode]
      exact pending_join (pending_outside_history saved (.history (owner := owner) .refl)) (.spent waiting)

/-- With no protected return marker, traversing this finite segment preserves
its input mode. Dormant branches satisfy the same property. -/
theorem return_mode_unprotected (hints : ReturnHints scope) (unprotected : scope.held = false)
    (mode : UseMode) : hints.returnMode mode = mode := by
  induction hints generalizing mode with
  | nil => rfl
  | plain rest ih | handler rest ih | cell rest ih | cleanup rest ih | spent rest ih => exact ih unprotected mode
  | running kind rest ih => cases unprotected
  | live saved rest ihSaved ihRest =>
      obtain ⟨inside, outside⟩ := Bool.or_eq_false_iff.mp unprotected
      simp only [ReturnHints.returnMode, ihSaved inside, ihRest outside]

/-- Disposal uses the same finite retained source and request callback check.
Protection proves the waiting source starts in ordinary mode. -/
theorem dispose_clause_from_retained {captured : ReturnHints capturedScope} {tail : ReturnHints tailScope}
    (known : actions owner = some rights) (permission : rights.dispose = true)
    (available : phases owner = .available) (unprotected : capturedScope.held = false)
    (retained : Pending outward actions (spend phases owner) world
      (.live (owner := owner) captured tail) .nil .ordinary finalMode)
    (abandoned : Pending outward actions (spend phases owner) world captured
      (.running .close tail) .unwind .unwind) :
    Local outward actions phases world (.invoke ⟨owner, .dispose⟩) (.live (owner := owner) captured tail) := by
  have mode := retained.return_mode
  cases retained with
  | live saved waiting =>
      have middle := saved.return_mode.symm.trans (return_mode_unprotected captured unprotected .ordinary)
      cases middle
      apply Local.dispose (front := .nil) .hit known permission available unprotected
      · exact pending_outside_history abandoned (.running (.history (owner := owner) .refl))
      · change Pending outward actions (spend phases owner) world
          (.spent (owner := owner) tail) .nil .ordinary
          ((ReturnHints.live (owner := owner) captured tail).returnMode .ordinary)
        rw [mode]
        exact .spent waiting

end Ash.OneShot.SourceDependencyNeutral.Lexical.Recursive
#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.Recursive.local_history
#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.Recursive.pending_outside_history
#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.Recursive.pending_history
#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.Recursive.pending_join
#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.Recursive.resume_clause_from_retained

#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.Recursive.return_mode_unprotected
#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.Recursive.dispose_clause_from_retained

namespace Ash.OneShot.SourceDependencyNeutral.Lexical.Recursive
open SourceDependencyChecks.Lexical.ReturnHints.Recursive (Local)
/-- A pure cleanup adds no callback obligation; its frame is retained in the
receiving scope of the checked body. -/
theorem pure_cleanup (body : Local outward actions phases world dependencies hints) :
    Local outward actions phases world (.cleanup [] .pure dependencies) hints :=
  .cleanup (local_history body (.completion .refl)) .pure
end Ash.OneShot.SourceDependencyNeutral.Lexical.Recursive
#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.Recursive.pure_cleanup

#print axioms Ash.OneShot.SourceDependencyNeutral.Lexical.Recursive.pending_pure_frame
