import SourceNeutralScopes

/-! Structural handler cuts authenticate the annotated captured and waiting
pieces against existing nearest-handler lookup. Pure-frame, pure-callback and history expansion preserves
that selection and its exact declaration table and capability modes. -/
namespace Ash.OneShot.SourcePlannedCuts
open ScopedExpressions ProtectionContracts
open SourceDependencyCapture (Scope select lookupDependencies)
open SourceContextualHints (Hints)
open SourcePlannedNeutralFrames (Expansion)
abbrev Modes := Option (Nat → SourceDependencyAnnotations.Dependencies) × Option (Nat → SourceDependencyAnnotations.Dependencies)

inductive Cut (effect : Instance) (operation : Nat) (contract : ClauseContract) (modes : Modes) :
    {scope captured tail : Scope} → Hints scope → Hints captured → Hints tail → Prop where
  | hit (known : lookup operation table = some contract) (declared : lookupDependencies operation families = some modes) :
      Cut effect operation contract modes
        (.handler (effect := effect) (table := table) (families := families) required rest)
        (.handler (effect := effect) (table := table) (families := families) required .nil) rest
  | plain : Cut effect operation contract modes rest saved waiting →
      Cut effect operation contract modes (.plain (dependencies := dependencies) rest) (.plain (dependencies := dependencies) saved) waiting
  | handler (different : effect ≠ other) : Cut effect operation contract modes rest saved waiting →
      Cut effect operation contract modes
        (.handler (effect := other) (table := table) (families := families) required rest)
        (.handler (effect := other) (table := table) (families := families) required saved) waiting
  | cell (different : effect ≠ .cell identity) : Cut effect operation contract modes rest saved waiting →
      Cut effect operation contract modes (.cell (identity := identity) rest) (.cell (identity := identity) saved) waiting
  | cleanup : Cut effect operation contract modes rest saved waiting →
      Cut effect operation contract modes (.cleanup (needs := needs) (callback := callback) rest)
        (.cleanup (needs := needs) (callback := callback) saved) waiting
  | running : Cut effect operation contract modes rest saved waiting →
      Cut effect operation contract modes (.running rest) (.running saved) waiting
  | live : Cut effect operation contract modes rest saved waiting →
      Cut effect operation contract modes (.live (owner := owner) dormant rest) (.live (owner := owner) dormant saved) waiting
  | spent : Cut effect operation contract modes rest saved waiting →
      Cut effect operation contract modes (.spent (owner := owner) rest) (.spent (owner := owner) saved) waiting

theorem Cut.lookup {whole : Hints scope} {saved : Hints captured} {waiting : Hints tail}
    (cut : Cut effect operation contract modes whole saved waiting) :
    select effect operation scope = some (.handler captured tail contract modes) := by
  induction cut with
  | hit known declared => simp [select, known, declared]
  | handler different next ih | cell different next ih =>
      simp only [select, if_neg different, ih, Option.map_some, SourceDependencyCapture.Selection.prepend]
  | plain next ih | cleanup next ih | running next ih | live next ih | spent next ih =>
      simp only [select, ih, Option.map_some, SourceDependencyCapture.Selection.prepend]

theorem Cut.reconstruct_scope {scope : Scope} {whole : Hints scope} {saved : Hints captured} {waiting : Hints tail}
    (cut : Cut effect operation contract modes whole saved waiting) : scope = captured.append tail := by
  induction cut <;> simp_all [Scope.append]

theorem Cut.hints {whole : Hints scope} {saved : Hints captured} {waiting : Hints tail}
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
theorem of_lookup (hints : Hints scope)
    (found : select effect operation scope = some (.handler captured tail contract modes)) :
    ∃ saved : Hints captured, ∃ waiting : Hints tail, Cut effect operation contract modes hints saved waiting := by
  induction hints generalizing captured tail with
  | nil => cases found
  | handler required rest ih =>
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
  | plain rest ih | cleanup rest ih | running rest ih | live dormant rest ihDormant ih | spent rest ih =>
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

/-- The same handler and modes are selected after pure-frame expansion.
Both resulting annotated pieces retain their existing source metadata. -/
theorem expand {saved : Hints captured} {waiting : Hints tail} (changed : Expansion before after)
    (cut : Cut effect operation contract modes before saved waiting) :
    ∃ captured tail, ∃ nextSaved : Hints captured, ∃ nextWaiting : Hints tail,
      Cut effect operation contract modes after nextSaved nextWaiting ∧
      Expansion saved nextSaved ∧ Expansion waiting nextWaiting := by
  induction changed generalizing captured tail with
  | refl => exact ⟨_, _, _, _, cut, .refl, .refl⟩
  | extra changed ih =>
      obtain ⟨_, _, saved, waiting, cut, inside, outside⟩ := ih cut
      exact ⟨_, _, _, _, .plain cut, .extra inside, outside⟩
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

/-- At fixed captured and waiting scopes, annotation splitting is unique.
This prevents an alternative handler-requirement list from discharging a cut. -/
theorem append_injective {first second : Hints captured} {outside otherOutside : Hints tail}
    (same : first.append outside = second.append otherOutside) : first = second ∧ outside = otherOutside := by
  induction first with
  | nil => cases second; exact ⟨rfl, same⟩
  | plain rest ih => cases second with
    | plain other => obtain ⟨rfl, rfl⟩ := ih (Hints.plain.inj same); exact ⟨rfl, rfl⟩
  | handler required rest ih => cases second with
    | handler otherRequired other =>
        obtain ⟨rfl, next⟩ := Hints.handler.inj same
        obtain ⟨rfl, rfl⟩ := ih next
        exact ⟨rfl, rfl⟩
  | cell rest ih => cases second with
    | cell other => obtain ⟨rfl, rfl⟩ := ih (Hints.cell.inj same); exact ⟨rfl, rfl⟩
  | cleanup rest ih => cases second with
    | cleanup other => obtain ⟨rfl, rfl⟩ := ih (Hints.cleanup.inj same); exact ⟨rfl, rfl⟩
  | running rest ih => cases second with
    | running other => obtain ⟨rfl, rfl⟩ := ih (Hints.running.inj same); exact ⟨rfl, rfl⟩
  | live saved rest ihSaved ihRest => cases second with
    | live otherSaved other =>
        obtain ⟨rfl, next⟩ := Hints.live.inj same
        obtain ⟨rfl, rfl⟩ := ihRest next
        exact ⟨rfl, rfl⟩
  | spent rest ih => cases second with
    | spent other => obtain ⟨rfl, rfl⟩ := ih (Hints.spent.inj same); exact ⟨rfl, rfl⟩

theorem Cut.unique {whole : Hints scope} {first second : Hints captured} {outside otherOutside : Hints tail}
    (cut : Cut effect operation contract modes whole first outside)
    (same : HEq whole (second.append otherOutside)) : first = second ∧ outside = otherOutside :=
  append_injective (eq_of_heq (cut.hints.symm.trans same))

theorem builtin_expand {before : Hints first} {after : Hints second} (changed : Expansion before after)
    (found : select effect operation first = some (.builtin identity)) :
    select effect operation second = some (.builtin identity) := by
  induction changed with
  | refl => exact found
  | extra changed ih | completion changed ih | history changed ih => simp only [select, ih found, Option.map_some, SourceDependencyCapture.Selection.prepend]
  | handler changed ih =>
      rename_i other table families required
      by_cases same : effect = other
      · simp only [select, if_pos same] at found
        cases known : lookup operation table <;> cases declared : lookupDependencies operation families <;>
          simp [known, declared] at found
      · simp only [select, if_neg same, Option.map_eq_some_iff] at found
        obtain ⟨selected, looked, equality⟩ := found
        cases selected with
        | handler => cases equality
        | builtin actual =>
            cases equality
            simp only [select, if_neg same, ih looked, Option.map_some, SourceDependencyCapture.Selection.prepend]
  | cell changed ih =>
      rename_i cellIdentity
      by_cases same : effect = .cell cellIdentity
      · simpa only [select, if_pos same] using found
      · simp only [select, if_neg same, Option.map_eq_some_iff] at found
        obtain ⟨selected, looked, equality⟩ := found
        cases selected with
        | handler => cases equality
        | builtin actual =>
            cases equality
            simp only [select, if_neg same, ih looked, Option.map_some, SourceDependencyCapture.Selection.prepend]
  | plain changed ih | cleanup changed ih | running changed ih | live changed ih | spent changed ih =>
      simp only [select, Option.map_eq_some_iff] at found
      obtain ⟨selected, looked, equality⟩ := found
      cases selected with
      | handler => cases equality
      | builtin actual =>
          cases equality
          simp only [select, ih looked, Option.map_some, SourceDependencyCapture.Selection.prepend]

end Ash.OneShot.SourcePlannedCuts

#print axioms Ash.OneShot.SourcePlannedCuts.Cut.lookup
#print axioms Ash.OneShot.SourcePlannedCuts.Cut.reconstruct_scope
#print axioms Ash.OneShot.SourcePlannedCuts.Cut.hints
#print axioms Ash.OneShot.SourcePlannedCuts.of_lookup
#print axioms Ash.OneShot.SourcePlannedCuts.expand

#print axioms Ash.OneShot.SourcePlannedCuts.append_injective
#print axioms Ash.OneShot.SourcePlannedCuts.Cut.unique
#print axioms Ash.OneShot.SourcePlannedCuts.builtin_expand
