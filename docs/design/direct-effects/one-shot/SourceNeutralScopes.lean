import SourceContextualInvocationHints
import SourceDependencyOwners

/-! Pure pending frames, spent-history markers and armed pure callbacks
preserve interpretation, protection and source-owner observations. Closing
retains the added callbacks. These transports assume no checked successor. -/
namespace Ash.OneShot.SourcePlannedNeutralFrames
open SourceContextualHints (Hints)
open SourceDependencyCapture (Scope)
open SourceContextualInvocationHints (forClosing)
open SourceDependencyOwners (owners PendingWithin)

/-- Only the active spine gains pure frames, pure callbacks or spent markers. Dormant
programs, interpretation order and existing annotations are retained exactly.
Adding a history marker does not change the independently checked phase map. -/
inductive Expansion : {first second : Scope} → Hints first → Hints second → Prop where
  | refl : Expansion hints hints
  | extra : Expansion before after → Expansion before (.plain (dependencies := .pure) after)
  | completion : Expansion before after → Expansion before (.cleanup (needs := []) (callback := .pure) after)
  | history : Expansion before after → Expansion before (.spent (owner := owner) after)
  | plain : Expansion before after →
      Expansion (.plain (dependencies := dependencies) before) (.plain (dependencies := dependencies) after)
  | handler : Expansion before after →
      Expansion (.handler (effect := effect) (table := table) (families := families) required before)
        (.handler (effect := effect) (table := table) (families := families) required after)
  | cell : Expansion before after → Expansion (.cell (identity := identity) before) (.cell (identity := identity) after)
  | cleanup : Expansion before after →
      Expansion (.cleanup (needs := needs) (callback := callback) before) (.cleanup (needs := needs) (callback := callback) after)
  | running : Expansion before after → Expansion (.running before) (.running after)
  | live : Expansion before after → Expansion (.live (owner := owner) saved before) (.live (owner := owner) saved after)
  | spent : Expansion before after → Expansion (.spent (owner := owner) before) (.spent (owner := owner) after)

theorem Expansion.prefix (front : Hints scope) (changed : Expansion first second) :
    Expansion (front.append first) (front.append second) := by
  induction front with
  | nil => exact changed
  | plain rest ih => exact .plain ih
  | handler required rest ih => exact .handler ih
  | cell rest ih => exact .cell ih
  | cleanup rest ih => exact .cleanup ih
  | running rest ih => exact .running ih
  | live saved rest ihSaved ihRest => exact .live ihRest
  | spent rest ih => exact .spent ih

theorem Expansion.append (first : Expansion a b) (second : Expansion c d) :
    Expansion (a.append c) (b.append d) := by
  induction first with
  | refl => exact second.prefix _
  | extra next ih => exact .extra ih
  | completion next ih => exact .completion ih
  | history next ih => exact .history ih
  | plain next ih => exact .plain ih
  | handler next ih => exact .handler ih
  | cell next ih => exact .cell ih
  | cleanup next ih => exact .cleanup ih
  | running next ih => exact .running ih
  | live next ih => exact .live ih
  | spent next ih => exact .spent ih

theorem Expansion.held {before : Hints first} {after : Hints second} (changed : Expansion before after) :
    first.held = second.held := by
  induction changed <;> simp_all [Scope.held]

theorem Expansion.normal {before : Hints first} {after : Hints second} (changed : Expansion before after) :
    first.shape.normal = second.shape.normal := by
  induction changed <;> simp_all [Scope.shape, SourceRecursiveRoutes.Shape.normal]

theorem Expansion.closing {before : Hints first} {after : Hints second} (changed : Expansion before after) :
    first.shape.closing = second.shape.closing := by
  induction changed <;> simp_all [Scope.shape, SourceRecursiveRoutes.Shape.closing]

theorem Expansion.closing_check {before : Hints first} {after : Hints second} (changed : Expansion before after) :
    SourceDependencyCapture.checkClosing outward first.shape original surviving =
      SourceDependencyCapture.checkClosing outward second.shape original surviving := by
  induction changed generalizing original surviving with
  | refl => rfl
  | extra next ih | history next ih | plain next ih | handler next ih | cell next ih | running next ih | spent next ih => exact ih
  | completion next ih => simpa only [Scope.shape, SourceDependencyCapture.checkClosing, List.all_nil, Bool.true_and] using ih
  | cleanup next ih | live next ih =>
      simp only [Scope.shape, SourceDependencyCapture.checkClosing, next.normal, next.closing, ih]

/-- Closing retains inserted pure callbacks. The resulting schedules are
related structurally; they need not have equal shapes or equal annotations. -/
theorem Expansion.forClosing {before : Hints first} {after : Hints second} (changed : Expansion before after) :
    Expansion (forClosing before) (forClosing after) := by
  induction changed with
  | refl => exact .refl
  | extra next ih | history next ih | plain next ih | handler next ih | spent next ih => exact ih
  | completion next ih => exact .completion ih
  | cell next ih => exact .cell ih
  | cleanup next ih => exact .cleanup ih
  | running next ih => exact .running ih
  | live next ih => exact (Expansion.running ih).prefix _

theorem Expansion.owners {before : Hints first} {after : Hints second} (changed : Expansion before after) :
    owners first = owners second := by
  induction changed <;> simp_all [SourceDependencyOwners.owners]

theorem Expansion.pending_owners {before : Hints first} {after : Hints second} (changed : Expansion before after)
    (checked : PendingWithin world owned first) : PendingWithin world owned second := by
  induction changed with
  | refl => exact checked
  | extra next ih => exact .plain .pure (ih checked)
  | completion next ih => exact .cleanup (ih checked)
  | history next ih => exact .spent (ih checked)
  | plain next ih => cases checked with | plain code rest => exact .plain code (ih rest)
  | handler next ih => cases checked with | handler rest => exact .handler (ih rest)
  | cell next ih => cases checked with | cell rest => exact .cell (ih rest)
  | cleanup next ih => cases checked with | cleanup rest => exact .cleanup (ih rest)
  | running next ih => cases checked with | running rest => exact .running (ih rest)
  | live next ih => cases checked with | live saved rest => exact .live saved (ih rest)
  | spent next ih => cases checked with | spent rest => exact .spent (ih rest)

open SourceContextualInvocationHints (Selection findOwner)

/-- Active-spine expansion keeps the selected dormant continuation identical.
Only its caller prefix and waiting suffix may gain frames and pure callbacks. -/
inductive OwnerExpansion : Selection → Selection → Prop where
  | pieces {front : Hints firstFront} {nextFront : Hints secondFront}
      {saved : Hints savedScope} {tail : Hints firstTail} {nextTail : Hints secondTail}
      (caller : Expansion front nextFront) (waiting : Expansion tail nextTail) :
      OwnerExpansion ⟨⟨firstFront, savedScope, firstTail⟩, front, saved, tail⟩
        ⟨⟨secondFront, savedScope, secondTail⟩, nextFront, saved, nextTail⟩

private theorem owner_refl (selected : Selection) : OwnerExpansion selected selected := by
  cases selected with
  | mk scopes front saved tail => cases scopes; exact .pieces .refl .refl

private theorem OwnerExpansion.prepend (changed : OwnerExpansion first second)
    (layer : Scope → Scope) (lift : ∀ {scope}, Hints scope → Hints (layer scope))
    (preserves : ∀ {a b} {before : Hints a} {after : Hints b}, Expansion before after → Expansion (lift before) (lift after)) :
    OwnerExpansion (first.prepend layer lift) (second.prepend layer lift) := by
  cases changed with | pieces caller waiting => exact .pieces (preserves caller) waiting

private theorem OwnerExpansion.extra (changed : OwnerExpansion first second) :
    OwnerExpansion first (second.prepend (.plain .pure) .plain) := by
  cases changed with | pieces caller waiting => exact .pieces (.extra caller) waiting

private theorem OwnerExpansion.completion (changed : OwnerExpansion first second) :
    OwnerExpansion first (second.prepend (.cleanup [] .pure) .cleanup) := by
  cases changed with | pieces caller waiting => exact .pieces (.completion caller) waiting

private theorem OwnerExpansion.history (changed : OwnerExpansion first second) :
    OwnerExpansion first (second.prepend (.spent owner) .spent) := by
  cases changed with | pieces caller waiting => exact .pieces (.history caller) waiting

/-- Owner lookup still selects the same saved program and owner identity. -/
theorem Expansion.find_owner (changed : Expansion before after)
    (found : findOwner owner before = some selected) :
    ∃ next, findOwner owner after = some next ∧ OwnerExpansion selected next := by
  induction changed generalizing selected with
  | refl => exact ⟨_, found, owner_refl _⟩
  | extra changed ih =>
      obtain ⟨next, selected, same⟩ := ih found
      exact ⟨_, by simp only [findOwner, selected, Option.map_some], same.extra⟩
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

theorem OwnerExpansion.resumed (changed : OwnerExpansion first second) :
    Expansion (first.resumed owner).hints (second.resumed owner).hints := by
  cases changed with
  | pieces caller waiting => exact (caller.append (.spent waiting)).prefix _

theorem OwnerExpansion.disposed (changed : OwnerExpansion first second) :
    Expansion (first.disposed owner).hints (second.disposed owner).hints := by
  cases changed with
  | pieces caller waiting => exact (Expansion.running (caller.append (.spent waiting))).prefix _

private def rating : Option SourceDependencyCapture.Selection → Bool
  | none => false
  | some (.builtin _) => true
  | some (.handler _ _ contract modes) =>
      !contract.dispose && (contract.row false).isSome && (contract.row true).isSome &&
        (SourceDependencyCapture.modeDependencies false modes).isSome &&
        (SourceDependencyCapture.modeDependencies true modes).isSome

private theorem rating_prepend (selected : Option SourceDependencyCapture.Selection) (layer : Scope → Scope) :
    rating (selected.map (SourceDependencyCapture.Selection.prepend layer)) = rating selected := by
  cases selected with
  | none => rfl
  | some selected => cases selected <;> rfl

theorem Expansion.capability {before : Hints first} {after : Hints second} (changed : Expansion before after) :
    SourceContextualHints.checkCapability first effect operation = SourceContextualHints.checkCapability second effect operation := by
  change rating (SourceDependencyCapture.select effect operation first) = rating (SourceDependencyCapture.select effect operation second)
  induction changed with
  | refl => rfl
  | extra changed ih | completion changed ih | history changed ih | plain changed ih | cleanup changed ih | running changed ih | live changed ih | spent changed ih =>
      simpa only [SourceDependencyCapture.select, rating_prepend] using ih
  | handler changed ih =>
      rename_i handlerEffect table families required
      by_cases same : effect = handlerEffect
      · simp only [SourceDependencyCapture.select, if_pos same]
        cases ProtectionContracts.lookup operation table <;>
          cases SourceDependencyCapture.lookupDependencies operation families <;> rfl
      · simpa only [SourceDependencyCapture.select, if_neg same, rating_prepend] using ih
  | cell changed ih =>
      rename_i identity
      by_cases same : effect = .cell identity
      · simp only [SourceDependencyCapture.select, if_pos same]
      · simpa only [SourceDependencyCapture.select, if_neg same, rating_prepend] using ih

theorem Expansion.requirements {before : Hints first} {after : Hints second} (changed : Expansion before after) :
    SourceContextualHints.checkRequirements first required = SourceContextualHints.checkRequirements second required := by
  simp only [SourceContextualHints.checkRequirements, changed.capability]

private theorem check_outside (hints : Hints scope) {before : Hints first} {after : Hints second}
    (outside : Expansion before after) : hints.check first = hints.check second := by
  induction hints generalizing first second with
  | nil => rfl
  | plain rest ih | cell rest ih | cleanup rest ih | running rest ih | spent rest ih => exact ih outside
  | handler required rest ih =>
      simp only [Hints.check, (outside.prefix rest).requirements, ih outside]
  | live saved rest ihSaved ihRest =>
      simp only [Hints.check, ihRest outside, ihSaved (outside.prefix rest)]

theorem Expansion.check {before : Hints first} {after : Hints second} (changed : Expansion before after)
    {outsideBefore : Hints firstOutside} {outsideAfter : Hints secondOutside}
    (outside : Expansion outsideBefore outsideAfter) : before.check firstOutside = after.check secondOutside := by
  induction changed with
  | refl => exact check_outside _ outside
  | extra changed ih | completion changed ih | history changed ih | plain changed ih | cell changed ih | cleanup changed ih | running changed ih | spent changed ih => exact ih
  | handler changed ih => simp only [Hints.check, (changed.append outside).requirements, ih]
  | live changed ih => simp only [Hints.check, ih, check_outside _ (changed.append outside)]

end Ash.OneShot.SourcePlannedNeutralFrames

#print axioms Ash.OneShot.SourcePlannedNeutralFrames.Expansion.prefix
#print axioms Ash.OneShot.SourcePlannedNeutralFrames.Expansion.append
#print axioms Ash.OneShot.SourcePlannedNeutralFrames.Expansion.held
#print axioms Ash.OneShot.SourcePlannedNeutralFrames.Expansion.normal
#print axioms Ash.OneShot.SourcePlannedNeutralFrames.Expansion.closing
#print axioms Ash.OneShot.SourcePlannedNeutralFrames.Expansion.closing_check
#print axioms Ash.OneShot.SourcePlannedNeutralFrames.Expansion.forClosing
#print axioms Ash.OneShot.SourcePlannedNeutralFrames.Expansion.owners
#print axioms Ash.OneShot.SourcePlannedNeutralFrames.Expansion.pending_owners
#print axioms Ash.OneShot.SourcePlannedNeutralFrames.Expansion.find_owner
#print axioms Ash.OneShot.SourcePlannedNeutralFrames.OwnerExpansion.resumed
#print axioms Ash.OneShot.SourcePlannedNeutralFrames.OwnerExpansion.disposed
#print axioms Ash.OneShot.SourcePlannedNeutralFrames.Expansion.capability
#print axioms Ash.OneShot.SourcePlannedNeutralFrames.Expansion.requirements
#print axioms Ash.OneShot.SourcePlannedNeutralFrames.Expansion.check
