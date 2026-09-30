import SourceScheduledTransport

/-! Pure pending frames, pure callbacks and spent history retain actual plans.
Erasure reuses existing interpretation, protection and capability observations;
structural cuts retain the plan witnesses needed by scheduling. -/
namespace Ash.OneShot.SourceScheduledNeutral
open ScopedExpressions ProtectionContracts
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDependencyCapture (Scope)

inductive Expansion : {first second : Scope} → {beforeHints : Hints first} → {afterHints : Hints second} →
    Forest beforeHints → Forest afterHints → Prop where
  | refl : Expansion forest forest
  | extra : Expansion before after → Expansion before (.plain .pure after)
  | completion : Expansion before after → Expansion before (.cleanup (needs := []) .pure after)
  | history : Expansion before after → Expansion before (.spent (owner := owner) after)
  | plain : Expansion before after → Expansion (.plain plan before) (.plain plan after)
  | handler : Expansion before after →
      Expansion (.handler (effect := effect) (table := table) (families := families) (required := required) before)
        (.handler (effect := effect) (table := table) (families := families) (required := required) after)
  | cell : Expansion before after → Expansion (.cell (identity := identity) before) (.cell (identity := identity) after)
  | cleanup : Expansion before after → Expansion (.cleanup (needs := needs) plan before) (.cleanup (needs := needs) plan after)
  | running : Expansion before after → Expansion (.running before) (.running after)
  | live : Expansion before after → Expansion (.live (owner := owner) saved before) (.live (owner := owner) saved after)
  | spent : Expansion before after → Expansion (.spent (owner := owner) before) (.spent (owner := owner) after)

theorem Expansion.erase {beforeHints : Hints first} {afterHints : Hints second}
    {before : Forest beforeHints} {after : Forest afterHints} (changed : Expansion before after) :
    SourcePlannedNeutralFrames.Expansion beforeHints afterHints := by
  induction changed with
  | refl => exact .refl
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

theorem Expansion.prefix (front : Forest hints) (changed : Expansion first second) :
    Expansion (front.append first) (front.append second) := by
  induction front with
  | nil => exact changed
  | plain plan rest ih => exact .plain ih
  | handler rest ih => exact .handler ih
  | cell rest ih => exact .cell ih
  | cleanup plan rest ih => exact .cleanup ih
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

theorem lift_heq {shape : Scope → Scope} {decorate : ∀ {scope}, Hints scope → Hints (shape scope)}
    {beforeHints : Hints first} {afterHints : Hints second} {before : Forest beforeHints} {after : Forest afterHints}
    (sameScope : first = second) (sameHints : HEq beforeHints afterHints) (sameForest : HEq before after)
    (lift : ∀ {scope} {hints : Hints scope}, Forest hints → Forest (decorate hints)) : HEq (lift before) (lift after) := by
  cases sameScope
  cases sameHints
  cases sameForest
  rfl

/-- Closing preserves the structural expansion and retains each new callback. -/
theorem Expansion.forClosing {beforeHints : Hints first} {afterHints : Hints second}
    {before : Forest beforeHints} {after : Forest afterHints} (changed : Expansion before after) :
    Expansion before.forClosing after.forClosing := by
  induction changed with
  | refl => exact .refl
  | extra next ih | history next ih | plain next ih | handler next ih | spent next ih => exact ih
  | completion next ih => exact .completion ih
  | cell next ih => exact .cell ih
  | cleanup next ih => exact .cleanup ih
  | running next ih => exact .running ih
  | live next ih => exact (Expansion.running ih).prefix _

inductive Cut (effect : Instance) (operation : Nat) (contract : ClauseContract) (modes : SourcePlannedCuts.Modes) :
    {scope captured tail : Scope} → {wholeHints : Hints scope} → {savedHints : Hints captured} → {waitingHints : Hints tail} →
      Forest wholeHints → Forest savedHints → Forest waitingHints → Prop where
  | hit (known : ProtectionContracts.lookup operation table = some contract) (declared : SourceDependencyCapture.lookupDependencies operation families = some modes) :
      Cut effect operation contract modes
        (.handler (effect := effect) (table := table) (families := families) (required := required) rest)
        (.handler (effect := effect) (table := table) (families := families) (required := required) .nil) rest
  | plain : Cut effect operation contract modes rest saved waiting →
      Cut effect operation contract modes (.plain plan rest) (.plain plan saved) waiting
  | handler (different : effect ≠ other) : Cut effect operation contract modes rest saved waiting →
      Cut effect operation contract modes
        (.handler (effect := other) (table := table) (families := families) (required := required) rest)
        (.handler (effect := other) (table := table) (families := families) (required := required) saved) waiting
  | cell (different : effect ≠ .cell identity) : Cut effect operation contract modes rest saved waiting →
      Cut effect operation contract modes (.cell (identity := identity) rest) (.cell (identity := identity) saved) waiting
  | cleanup : Cut effect operation contract modes rest saved waiting →
      Cut effect operation contract modes (.cleanup (needs := needs) plan rest)
        (.cleanup (needs := needs) plan saved) waiting
  | running : Cut effect operation contract modes rest saved waiting →
      Cut effect operation contract modes (.running rest) (.running saved) waiting
  | live : Cut effect operation contract modes rest saved waiting →
      Cut effect operation contract modes (.live (owner := owner) dormant rest) (.live (owner := owner) dormant saved) waiting
  | spent : Cut effect operation contract modes rest saved waiting →
      Cut effect operation contract modes (.spent (owner := owner) rest) (.spent (owner := owner) saved) waiting

theorem Cut.erase {wholeHints : Hints scope} {savedHints : Hints captured} {waitingHints : Hints tail}
    {whole : Forest wholeHints} {saved : Forest savedHints} {waiting : Forest waitingHints}
    (cut : Cut effect operation contract modes whole saved waiting) :
    SourcePlannedCuts.Cut effect operation contract modes wholeHints savedHints waitingHints := by
  induction cut with
  | hit known declared => exact .hit known declared
  | plain next ih => exact .plain ih
  | handler different next ih => exact .handler different ih
  | cell different next ih => exact .cell different ih
  | cleanup next ih => exact .cleanup ih
  | running next ih => exact .running ih
  | live next ih => exact .live ih
  | spent next ih => exact .spent ih

theorem Cut.forest (cut : Cut effect operation contract modes whole saved waiting) :
    HEq whole (saved.append waiting) := by
  induction cut with
  | hit => rfl
  | plain next ih => exact lift_heq (decorate := fun hints => .plain hints) next.erase.reconstruct_scope next.erase.hints ih (fun forest => .plain _ forest)
  | handler different next ih => exact lift_heq (decorate := fun hints => .handler _ hints) next.erase.reconstruct_scope next.erase.hints ih (fun forest => .handler forest)
  | cell different next ih => exact lift_heq (decorate := fun hints => .cell hints) next.erase.reconstruct_scope next.erase.hints ih (fun forest => .cell forest)
  | cleanup next ih => exact lift_heq (decorate := fun hints => .cleanup hints) next.erase.reconstruct_scope next.erase.hints ih (fun forest => .cleanup _ forest)
  | running next ih => exact lift_heq (decorate := fun hints => .running hints) next.erase.reconstruct_scope next.erase.hints ih (fun forest => .running forest)
  | live next ih => exact lift_heq (decorate := fun hints => .live _ hints) next.erase.reconstruct_scope next.erase.hints ih (fun forest => .live _ forest)
  | spent next ih => exact lift_heq (decorate := fun hints => .spent hints) next.erase.reconstruct_scope next.erase.hints ih (fun forest => .spent forest)

/-- Lift an existing selected cut through the actual retained plans. -/
theorem of_cut (cut : SourcePlannedCuts.Cut effect operation contract modes hints saved waiting)
    (forest : Forest hints) :
    ∃ savedForest : Forest saved, ∃ waitingForest : Forest waiting,
      Cut effect operation contract modes forest savedForest waitingForest := by
  induction cut with
  | hit known declared => cases forest with | handler rest => exact ⟨_, _, .hit known declared⟩
  | plain next ih => cases forest with | plain plan rest =>
      obtain ⟨saved, waiting, cut⟩ := ih rest; exact ⟨_, _, .plain cut⟩
  | handler different next ih => cases forest with | handler rest =>
      obtain ⟨saved, waiting, cut⟩ := ih rest; exact ⟨_, _, .handler different cut⟩
  | cell different next ih => cases forest with | cell rest =>
      obtain ⟨saved, waiting, cut⟩ := ih rest; exact ⟨_, _, .cell different cut⟩
  | cleanup next ih => cases forest with | cleanup plan rest =>
      obtain ⟨saved, waiting, cut⟩ := ih rest; exact ⟨_, _, .cleanup cut⟩
  | running next ih => cases forest with | running rest =>
      obtain ⟨saved, waiting, cut⟩ := ih rest; exact ⟨_, _, .running cut⟩
  | live next ih => cases forest with | live dormant rest =>
      obtain ⟨saved, waiting, cut⟩ := ih rest; exact ⟨_, _, .live cut⟩
  | spent next ih => cases forest with | spent rest =>
      obtain ⟨saved, waiting, cut⟩ := ih rest; exact ⟨_, _, .spent cut⟩

theorem expand {savedHints : Hints captured} {waitingHints : Hints tail}
    {saved : Forest savedHints} {waiting : Forest waitingHints} (changed : Expansion before after)
    (cut : Cut effect operation contract modes before saved waiting) :
    ∃ captured tail, ∃ nextSaved : Hints captured, ∃ nextWaiting : Hints tail,
      ∃ nextSavedForest : Forest nextSaved, ∃ nextWaitingForest : Forest nextWaiting,
      Cut effect operation contract modes after nextSavedForest nextWaitingForest ∧
      Expansion saved nextSavedForest ∧ Expansion waiting nextWaitingForest := by
  induction changed generalizing captured tail with
  | refl => exact ⟨_, _, _, _, _, _, cut, .refl, .refl⟩
  | extra changed ih =>
      obtain ⟨_, _, _, _, saved, waiting, cut, inside, outside⟩ := ih cut
      exact ⟨_, _, _, _, _, _, .plain cut, .extra inside, outside⟩
  | completion changed ih =>
      obtain ⟨_, _, _, _, saved, waiting, cut, inside, outside⟩ := ih cut
      exact ⟨_, _, _, _, _, _, .cleanup cut, .completion inside, outside⟩
  | history changed ih =>
      obtain ⟨_, _, _, _, saved, waiting, cut, inside, outside⟩ := ih cut
      exact ⟨_, _, _, _, _, _, .spent cut, .history inside, outside⟩
  | handler changed ih => cases cut with
    | hit known declared => exact ⟨_, _, _, _, _, _, .hit known declared, .refl, changed⟩
    | handler different next =>
        obtain ⟨_, _, _, _, saved, waiting, cut, inside, outside⟩ := ih next
        exact ⟨_, _, _, _, _, _, .handler different cut, .handler inside, outside⟩
  | plain changed ih => cases cut with
    | plain next =>
        obtain ⟨_, _, _, _, saved, waiting, cut, inside, outside⟩ := ih next
        exact ⟨_, _, _, _, _, _, .plain cut, .plain inside, outside⟩
  | cell changed ih => cases cut with
    | cell different next =>
        obtain ⟨_, _, _, _, saved, waiting, cut, inside, outside⟩ := ih next
        exact ⟨_, _, _, _, _, _, .cell different cut, .cell inside, outside⟩
  | cleanup changed ih => cases cut with
    | cleanup next =>
        obtain ⟨_, _, _, _, saved, waiting, cut, inside, outside⟩ := ih next
        exact ⟨_, _, _, _, _, _, .cleanup cut, .cleanup inside, outside⟩
  | running changed ih => cases cut with
    | running next =>
        obtain ⟨_, _, _, _, saved, waiting, cut, inside, outside⟩ := ih next
        exact ⟨_, _, _, _, _, _, .running cut, .running inside, outside⟩
  | live changed ih => cases cut with
    | live next =>
        obtain ⟨_, _, _, _, saved, waiting, cut, inside, outside⟩ := ih next
        exact ⟨_, _, _, _, _, _, .live cut, .live inside, outside⟩
  | spent changed ih => cases cut with
    | spent next =>
        obtain ⟨_, _, _, _, saved, waiting, cut, inside, outside⟩ := ih next
        exact ⟨_, _, _, _, _, _, .spent cut, .spent inside, outside⟩

/-- The existing active-owner selection, with its exact retained plan pieces. -/
inductive OwnerCut (owner : Nat) : {wholeScope frontScope savedScope tailScope : Scope} →
    {wholeHints : Hints wholeScope} → {frontHints : Hints frontScope} →
    {savedHints : Hints savedScope} → {tailHints : Hints tailScope} →
    Forest wholeHints → Forest frontHints → Forest savedHints → Forest tailHints → Prop where
  | hit : OwnerCut owner (.live (owner := owner) saved tail) .nil saved tail
  | plain : OwnerCut owner rest front saved tail → OwnerCut owner (.plain plan rest) (.plain plan front) saved tail
  | handler : OwnerCut owner rest front saved tail →
      OwnerCut owner (.handler (effect := effect) (table := table) (families := families) (required := required) rest)
        (.handler (effect := effect) (table := table) (families := families) (required := required) front) saved tail
  | cell : OwnerCut owner rest front saved tail → OwnerCut owner (.cell (identity := identity) rest) (.cell (identity := identity) front) saved tail
  | cleanup : OwnerCut owner rest front saved tail → OwnerCut owner (.cleanup (needs := needs) plan rest) (.cleanup (needs := needs) plan front) saved tail
  | running : OwnerCut owner rest front saved tail → OwnerCut owner (.running rest) (.running front) saved tail
  | live (different : owner ≠ other) : OwnerCut owner rest front saved tail →
      OwnerCut owner (.live (owner := other) dormant rest) (.live (owner := other) dormant front) saved tail
  | spent : OwnerCut owner rest front saved tail → OwnerCut owner (.spent (owner := other) rest) (.spent (owner := other) front) saved tail

theorem OwnerCut.found {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {whole : Forest wholeHints} {front : Forest frontHints} {saved : Forest savedHints} {tail : Forest tailHints}
    (cut : OwnerCut owner whole front saved tail) :
    SourceContextualInvocationHints.findOwner owner wholeHints =
      some ⟨⟨frontScope, savedScope, tailScope⟩, frontHints, savedHints, tailHints⟩ := by
  induction cut with
  | hit => simp [SourceContextualInvocationHints.findOwner]
  | live different next ih => simp [SourceContextualInvocationHints.findOwner, different, ih, SourceContextualInvocationHints.Selection.prepend, SourceDependencyCapture.OwnerSelection.prepend]
  | plain next ih | handler next ih | cell next ih | cleanup next ih | running next ih | spent next ih =>
      simp [SourceContextualInvocationHints.findOwner, ih, SourceContextualInvocationHints.Selection.prepend, SourceDependencyCapture.OwnerSelection.prepend]

private theorem lift_hints {shape : Scope → Scope} {before : Hints first} {after : Hints second}
    (sameScope : first = second) (sameHints : HEq before after)
    (lift : ∀ {scope}, Hints scope → Hints (shape scope)) : HEq (lift before) (lift after) := by
  cases sameScope
  cases sameHints
  rfl

theorem OwnerCut.hints {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {whole : Forest wholeHints} {front : Forest frontHints} {saved : Forest savedHints} {tail : Forest tailHints}
    (cut : OwnerCut owner whole front saved tail) :
    HEq wholeHints (frontHints.append (.live (owner := owner) savedHints tailHints)) := by
  induction cut with
  | hit => rfl
  | plain next ih => exact lift_hints (SourceContextualInvocationHints.selected_cut next.found).reconstruct ih (fun hints => .plain hints)
  | handler next ih => exact lift_hints (SourceContextualInvocationHints.selected_cut next.found).reconstruct ih (fun hints => .handler _ hints)
  | cell next ih => exact lift_hints (SourceContextualInvocationHints.selected_cut next.found).reconstruct ih (fun hints => .cell hints)
  | cleanup next ih => exact lift_hints (SourceContextualInvocationHints.selected_cut next.found).reconstruct ih (fun hints => .cleanup hints)
  | running next ih => exact lift_hints (SourceContextualInvocationHints.selected_cut next.found).reconstruct ih (fun hints => .running hints)
  | live different next ih => exact lift_hints (SourceContextualInvocationHints.selected_cut next.found).reconstruct ih (fun hints => .live _ hints)
  | spent next ih => exact lift_hints (SourceContextualInvocationHints.selected_cut next.found).reconstruct ih (fun hints => .spent hints)

theorem OwnerCut.forest (cut : OwnerCut owner whole front saved tail) :
    HEq whole (front.append (.live (owner := owner) saved tail)) := by
  induction cut with
  | hit => rfl
  | plain next ih => exact lift_heq (decorate := fun hints => .plain hints) (SourceContextualInvocationHints.selected_cut next.found).reconstruct next.hints ih (fun forest => .plain _ forest)
  | handler next ih => exact lift_heq (decorate := fun hints => .handler _ hints) (SourceContextualInvocationHints.selected_cut next.found).reconstruct next.hints ih (fun forest => .handler forest)
  | cell next ih => exact lift_heq (decorate := fun hints => .cell hints) (SourceContextualInvocationHints.selected_cut next.found).reconstruct next.hints ih (fun forest => .cell forest)
  | cleanup next ih => exact lift_heq (decorate := fun hints => .cleanup hints) (SourceContextualInvocationHints.selected_cut next.found).reconstruct next.hints ih (fun forest => .cleanup _ forest)
  | running next ih => exact lift_heq (decorate := fun hints => .running hints) (SourceContextualInvocationHints.selected_cut next.found).reconstruct next.hints ih (fun forest => .running forest)
  | live different next ih => exact lift_heq (decorate := fun hints => .live _ hints) (SourceContextualInvocationHints.selected_cut next.found).reconstruct next.hints ih (fun forest => .live _ forest)
  | spent next ih => exact lift_heq (decorate := fun hints => .spent hints) (SourceContextualInvocationHints.selected_cut next.found).reconstruct next.hints ih (fun forest => .spent forest)

/-- Recover plan-carrying owner-cut evidence from existing annotated lookup. -/
theorem of_owner {hints : Hints scope} (forest : Forest hints)
    (found : SourceContextualInvocationHints.findOwner owner hints = some selected) :
    ∃ front : Forest selected.front, ∃ saved : Forest selected.saved, ∃ tail : Forest selected.tail,
      OwnerCut owner forest front saved tail := by
  induction forest generalizing selected with
  | nil => cases found
  | plain plan rest ih =>
      simp only [SourceContextualInvocationHints.findOwner, Option.map_eq_some_iff] at found
      obtain ⟨inside, located, rfl⟩ := found
      obtain ⟨front, saved, tail, cut⟩ := ih located
      exact ⟨_, _, _, .plain cut⟩
  | handler rest ih =>
      simp only [SourceContextualInvocationHints.findOwner, Option.map_eq_some_iff] at found
      obtain ⟨inside, located, rfl⟩ := found
      obtain ⟨front, saved, tail, cut⟩ := ih located
      exact ⟨_, _, _, .handler cut⟩
  | cell rest ih =>
      simp only [SourceContextualInvocationHints.findOwner, Option.map_eq_some_iff] at found
      obtain ⟨inside, located, rfl⟩ := found
      obtain ⟨front, saved, tail, cut⟩ := ih located
      exact ⟨_, _, _, .cell cut⟩
  | cleanup plan rest ih =>
      simp only [SourceContextualInvocationHints.findOwner, Option.map_eq_some_iff] at found
      obtain ⟨inside, located, rfl⟩ := found
      obtain ⟨front, saved, tail, cut⟩ := ih located
      exact ⟨_, _, _, .cleanup cut⟩
  | running rest ih =>
      simp only [SourceContextualInvocationHints.findOwner, Option.map_eq_some_iff] at found
      obtain ⟨inside, located, rfl⟩ := found
      obtain ⟨front, saved, tail, cut⟩ := ih located
      exact ⟨_, _, _, .running cut⟩
  | live saved rest ihSaved ih =>
      rename_i other
      by_cases same : owner = other
      · cases same
        simp only [SourceContextualInvocationHints.findOwner, ↓reduceIte, Option.some.injEq] at found
        subst selected
        exact ⟨_, _, _, .hit⟩
      · simp only [SourceContextualInvocationHints.findOwner, if_neg same, Option.map_eq_some_iff] at found
        obtain ⟨inside, located, rfl⟩ := found
        obtain ⟨front, saved, tail, cut⟩ := ih located
        exact ⟨_, _, _, .live same cut⟩
  | spent rest ih =>
      simp only [SourceContextualInvocationHints.findOwner, Option.map_eq_some_iff] at found
      obtain ⟨inside, located, rfl⟩ := found
      obtain ⟨front, saved, tail, cut⟩ := ih located
      exact ⟨_, _, _, .spent cut⟩

theorem expand_owner {frontHints : Hints frontScope} {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {front : Forest frontHints} {saved : Forest savedHints} {tail : Forest tailHints}
    (changed : Expansion before after) (cut : OwnerCut owner before front saved tail) :
    ∃ nextFrontScope nextTailScope, ∃ nextFrontHints : Hints nextFrontScope, ∃ nextTailHints : Hints nextTailScope,
    ∃ nextFront : Forest nextFrontHints, ∃ nextTail : Forest nextTailHints,
      OwnerCut owner after nextFront saved nextTail ∧ Expansion front nextFront ∧ Expansion tail nextTail := by
  induction changed generalizing frontScope tailScope with
  | refl => exact ⟨_, _, _, _, _, _, cut, .refl, .refl⟩
  | extra changed ih =>
      obtain ⟨_, _, _, _, _, _, cut, caller, waiting⟩ := ih cut
      exact ⟨_, _, _, _, _, _, .plain cut, .extra caller, waiting⟩
  | completion changed ih =>
      obtain ⟨_, _, _, _, _, _, cut, caller, waiting⟩ := ih cut
      exact ⟨_, _, _, _, _, _, .cleanup cut, .completion caller, waiting⟩
  | history changed ih =>
      obtain ⟨_, _, _, _, _, _, cut, caller, waiting⟩ := ih cut
      exact ⟨_, _, _, _, _, _, .spent cut, .history caller, waiting⟩
  | plain changed ih => cases cut with
    | plain next =>
        obtain ⟨_, _, _, _, _, _, cut, caller, waiting⟩ := ih next
        exact ⟨_, _, _, _, _, _, .plain cut, .plain caller, waiting⟩
  | handler changed ih => cases cut with
    | handler next =>
        obtain ⟨_, _, _, _, _, _, cut, caller, waiting⟩ := ih next
        exact ⟨_, _, _, _, _, _, .handler cut, .handler caller, waiting⟩
  | cell changed ih => cases cut with
    | cell next =>
        obtain ⟨_, _, _, _, _, _, cut, caller, waiting⟩ := ih next
        exact ⟨_, _, _, _, _, _, .cell cut, .cell caller, waiting⟩
  | cleanup changed ih => cases cut with
    | cleanup next =>
        obtain ⟨_, _, _, _, _, _, cut, caller, waiting⟩ := ih next
        exact ⟨_, _, _, _, _, _, .cleanup cut, .cleanup caller, waiting⟩
  | running changed ih => cases cut with
    | running next =>
        obtain ⟨_, _, _, _, _, _, cut, caller, waiting⟩ := ih next
        exact ⟨_, _, _, _, _, _, .running cut, .running caller, waiting⟩
  | live changed ih => cases cut with
    | hit => exact ⟨_, _, _, _, _, _, .hit, .refl, changed⟩
    | live different next =>
        obtain ⟨_, _, _, _, _, _, cut, caller, waiting⟩ := ih next
        exact ⟨_, _, _, _, _, _, .live different cut, .live caller, waiting⟩
  | spent changed ih => cases cut with
    | spent next =>
        obtain ⟨_, _, _, _, _, _, cut, caller, waiting⟩ := ih next
        exact ⟨_, _, _, _, _, _, .spent cut, .spent caller, waiting⟩

end Ash.OneShot.SourceScheduledNeutral

#print axioms Ash.OneShot.SourceScheduledNeutral.Expansion.erase
#print axioms Ash.OneShot.SourceScheduledNeutral.Expansion.prefix
#print axioms Ash.OneShot.SourceScheduledNeutral.Expansion.append
#print axioms Ash.OneShot.SourceScheduledNeutral.Expansion.forClosing
#print axioms Ash.OneShot.SourceScheduledNeutral.Cut.erase
#print axioms Ash.OneShot.SourceScheduledNeutral.Cut.forest
#print axioms Ash.OneShot.SourceScheduledNeutral.of_cut
#print axioms Ash.OneShot.SourceScheduledNeutral.expand
#print axioms Ash.OneShot.SourceScheduledNeutral.OwnerCut.found
#print axioms Ash.OneShot.SourceScheduledNeutral.OwnerCut.hints
#print axioms Ash.OneShot.SourceScheduledNeutral.OwnerCut.forest
#print axioms Ash.OneShot.SourceScheduledNeutral.of_owner
#print axioms Ash.OneShot.SourceScheduledNeutral.expand_owner

#print axioms Ash.OneShot.SourceScheduledNeutral.lift_heq
