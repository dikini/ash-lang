import SourceCleanupClosingInsertion
import SourceScheduledPendingSites

/-! Structural movement of one actual cleanup plan on the active spine.
This preserves exact handler and owner cuts, but is not a scheduling admission
rule: the new callback contributes its own code site and closing obligations. -/
namespace Ash.OneShot.SourceScheduledCleanupInsertion
open SourceDependencyCapture (Scope)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open SourceScheduledNeutral (Cut OwnerCut)

inductive Insertion (needs : List Instance) {dependencies : SourceDependencyAnnotations.Dependencies}
    (callback : Plan dependencies) : {first second : Scope} →
    {beforeHints : Hints first} → {afterHints : Hints second} →
    Forest beforeHints → Forest afterHints → Prop where
  | here : Insertion needs callback before (.cleanup (needs := needs) callback before)
  | plain : Insertion needs callback before after →
      Insertion needs callback (.plain plan before) (.plain plan after)
  | handler : Insertion needs callback before after →
      Insertion needs callback
        (.handler (effect := effect) (table := table) (families := families) (required := required) before)
        (.handler (effect := effect) (table := table) (families := families) (required := required) after)
  | cell : Insertion needs callback before after →
      Insertion needs callback (.cell (identity := identity) before) (.cell (identity := identity) after)
  | cleanup : Insertion needs callback before after →
      Insertion needs callback (.cleanup (needs := otherNeeds) plan before) (.cleanup (needs := otherNeeds) plan after)
  | running : Insertion needs callback before after →
      Insertion needs callback (.running before) (.running after)
  | live : Insertion needs callback before after →
      Insertion needs callback (.live (owner := owner) saved before) (.live (owner := owner) saved after)
  | spent : Insertion needs callback before after →
      Insertion needs callback (.spent (owner := owner) before) (.spent (owner := owner) after)

theorem Insertion.prefix (front : Forest hints) (changed : Insertion needs callback before after) :
    Insertion needs callback (front.append before) (front.append after) := by
  induction front with
  | nil => exact changed
  | plain plan rest ih => exact .plain ih
  | handler rest ih => exact .handler ih
  | cell rest ih => exact .cell ih
  | cleanup plan rest ih => exact .cleanup ih
  | running rest ih => exact .running ih
  | live saved rest ihSaved ihRest => exact .live ihRest
  | spent rest ih => exact .spent ih

theorem Insertion.suffix (changed : Insertion needs callback before after) (tail : Forest hints) :
    Insertion needs callback (before.append tail) (after.append tail) := by
  induction changed with
  | here => exact .here
  | plain next ih => exact .plain ih
  | handler next ih => exact .handler ih
  | cell next ih => exact .cell ih
  | cleanup next ih => exact .cleanup ih
  | running next ih => exact .running ih
  | live next ih => exact .live ih
  | spent next ih => exact .spent ih

/-- Closing keeps the same callback plan, including when dormant captures are
materialized ahead of the insertion. -/
theorem Insertion.forClosing (changed : Insertion needs callback before after) :
    Insertion needs callback before.forClosing after.forClosing := by
  induction changed with
  | here => exact .here
  | plain next ih | handler next ih | spent next ih => exact ih
  | cell next ih => exact .cell ih
  | cleanup next ih => exact .cleanup ih
  | running next ih => exact .running ih
  | live next ih => exact (Insertion.running ih).prefix _

/-- Callback insertion does not create or duplicate continuation owners. The
callback's own action permissions are not inferred from this inventory fact. -/
theorem Insertion.owners {beforeHints : Hints first} {afterHints : Hints second}
    {before : Forest beforeHints} {after : Forest afterHints}
    (changed : Insertion needs callback before after) :
    SourceDependencyOwners.owners first = SourceDependencyOwners.owners second := by
  induction changed <;> simp_all [SourceDependencyOwners.owners]

/-- Recover the concrete registration boundary from the structural insertion.
The old and new scopes differ only by this callback at that boundary. -/
theorem Insertion.location {beforeHints : Hints first} {afterHints : Hints second}
    {before : Forest beforeHints} {after : Forest afterHints}
    {callback : Plan dependencies} (changed : Insertion needs callback before after) :
    ∃ front tail : Scope, first = front.append tail ∧
      second = front.append (.cleanup needs dependencies tail) := by
  induction changed with
  | here => exact ⟨.nil, _, rfl, rfl⟩
  | plain next ih => obtain ⟨front, tail, rfl, rfl⟩ := ih; exact ⟨.plain _ front, tail, rfl, rfl⟩
  | handler next ih => obtain ⟨front, tail, rfl, rfl⟩ := ih; exact ⟨.handler _ _ _ front, tail, rfl, rfl⟩
  | cell next ih => obtain ⟨front, tail, rfl, rfl⟩ := ih; exact ⟨.cell _ front, tail, rfl, rfl⟩
  | cleanup next ih => obtain ⟨front, tail, rfl, rfl⟩ := ih; exact ⟨.cleanup _ _ front, tail, rfl, rfl⟩
  | running next ih => obtain ⟨front, tail, rfl, rfl⟩ := ih; exact ⟨.running front, tail, rfl, rfl⟩
  | live next ih => obtain ⟨front, tail, rfl, rfl⟩ := ih; exact ⟨.live _ _ front, tail, rfl, rfl⟩
  | spent next ih => obtain ⟨front, tail, rfl, rfl⟩ := ih; exact ⟨.spent _ front, tail, rfl, rfl⟩

/-- Reuse the existing lookup-composition laws. A cleanup frame changes no
ordinary operation capability; disposing-request guards are separate. -/
theorem Insertion.capability {beforeHints : Hints first} {afterHints : Hints second}
    {before : Forest beforeHints} {after : Forest afterHints}
    (changed : Insertion needs callback before after) :
    SourceContextualHints.checkCapability first effect operation =
      SourceContextualHints.checkCapability second effect operation := by
  obtain ⟨front, tail, firstSame, secondSame⟩ := changed.location
  rw [firstSame, secondSame, SourceHandlerRequirements.capability_append,
    SourceHandlerRequirements.capability_append]
  rw [SourceHandlerRequirements.capability_prepend
    (first := .cleanup needs _ tail) (second := tail) (effect := effect) (operation := operation) rfl]

theorem Insertion.requirements {beforeHints : Hints first} {afterHints : Hints second}
    {before : Forest beforeHints} {after : Forest afterHints}
    (changed : Insertion needs callback before after) :
    SourceContextualHints.checkRequirements first required = SourceContextualHints.checkRequirements second required := by
  simp only [SourceContextualHints.checkRequirements, changed.capability]

theorem Insertion.check_outside {beforeHints : Hints first} {afterHints : Hints second}
    {before : Forest beforeHints} {after : Forest afterHints}
    (changed : Insertion needs callback before after) (hints : Hints scope) :
    hints.check first = hints.check second := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro checked
    apply SourceHandlerRequirements.check_transport hints checked
    rw [← changed.requirements]
    exact SourceHandlerRequirements.exposed_requirements hints checked
  · intro checked
    apply SourceHandlerRequirements.check_transport hints checked
    rw [changed.requirements]
    exact SourceHandlerRequirements.exposed_requirements hints checked

theorem Insertion.check_inside {beforeHints : Hints first} {afterHints : Hints second}
    {before : Forest beforeHints} {after : Forest afterHints}
    {outsideHints : Hints outsideScope}
    (changed : Insertion needs callback before after) (outside : Forest outsideHints) :
    beforeHints.check outsideScope = afterHints.check outsideScope := by
  induction changed with
  | here => rfl
  | plain next ih | cell next ih | cleanup next ih | running next ih | spent next ih => exact ih
  | handler next ih => simp only [Hints.check, (next.suffix outside).requirements, ih]
  | live next ih => simp only [Hints.check, (next.suffix outside).check_outside, ih]

inductive Split (needs : List Instance) {dependencies : SourceDependencyAnnotations.Dependencies}
    (callback : Plan dependencies) : {first outside second nextOutside : Scope} →
    {firstHints : Hints first} → {outsideHints : Hints outside} →
    {secondHints : Hints second} → {nextOutsideHints : Hints nextOutside} →
    Forest firstHints → Forest outsideHints → Forest secondHints → Forest nextOutsideHints → Prop where
  | inside (changed : Insertion needs callback before after) : Split needs callback before tail after tail
  | outside (changed : Insertion needs callback before after) : Split needs callback saved before saved after

theorem Split.forClosing (changed : Split needs callback saved waiting nextSaved nextWaiting) :
    Split needs callback saved.forClosing (.running waiting) nextSaved.forClosing (.running nextWaiting) := by
  cases changed with
  | inside inserted => exact .inside inserted.forClosing
  | outside inserted => exact .outside (.running inserted)

theorem Split.spent_append (changed : Split needs callback front tail nextFront nextTail) :
    Insertion needs callback (front.append (.spent (owner := owner) tail))
      (nextFront.append (.spent (owner := owner) nextTail)) := by
  cases changed with
  | inside inserted => exact inserted.suffix _
  | outside inserted => exact (Insertion.spent inserted).prefix _

theorem Split.resumed (changed : Split needs callback front tail nextFront nextTail) (saved : Forest savedHints) :
    Insertion needs callback (saved.append (front.append (.spent (owner := owner) tail)))
      (saved.append (nextFront.append (.spent (owner := owner) nextTail))) :=
  changed.spent_append.prefix saved

theorem Split.disposed (changed : Split needs callback front tail nextFront nextTail) (saved : Forest savedHints) :
    Insertion needs callback (saved.forClosing.append (.running (front.append (.spent (owner := owner) tail))))
      (saved.forClosing.append (.running (nextFront.append (.spent (owner := owner) nextTail)))) :=
  (Insertion.running changed.spent_append).prefix saved.forClosing

/-- An operation keeps its selected handler; the inserted callback lies in
exactly one of the actual saved and waiting pieces. -/
theorem Insertion.cut {beforeHints : Hints first} {afterHints : Hints second}
    {before : Forest beforeHints} {after : Forest afterHints}
    {savedHints : Hints captured} {waitingHints : Hints tail}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (changed : Insertion needs callback before after)
    (cut : SourceScheduledNeutral.Cut effect operation contract modes before saved waiting) :
    ∃ nextCaptured nextTail, ∃ nextSavedHints : Hints nextCaptured, ∃ nextWaitingHints : Hints nextTail,
      ∃ nextSaved : Forest nextSavedHints, ∃ nextWaiting : Forest nextWaitingHints,
        SourceScheduledNeutral.Cut effect operation contract modes after nextSaved nextWaiting ∧
        Split needs callback saved waiting nextSaved nextWaiting := by
  induction changed generalizing captured tail with
  | here => exact ⟨_, _, _, _, _, _, .cleanup cut, .inside .here⟩
  | plain changed ih => cases cut with
    | plain next =>
        obtain ⟨_, _, _, _, _, _, nextCut, pieces⟩ := ih next
        cases pieces with
        | inside inserted => exact ⟨_, _, _, _, _, _, .plain nextCut, .inside (.plain inserted)⟩
        | outside inserted => exact ⟨_, _, _, _, _, _, .plain nextCut, .outside inserted⟩
  | handler changed ih => cases cut with
    | hit known declared => exact ⟨_, _, _, _, _, _, .hit known declared, .outside changed⟩
    | handler different next =>
        obtain ⟨_, _, _, _, _, _, nextCut, pieces⟩ := ih next
        cases pieces with
        | inside inserted => exact ⟨_, _, _, _, _, _, .handler different nextCut, .inside (.handler inserted)⟩
        | outside inserted => exact ⟨_, _, _, _, _, _, .handler different nextCut, .outside inserted⟩
  | cell changed ih => cases cut with
    | cell different next =>
        obtain ⟨_, _, _, _, _, _, nextCut, pieces⟩ := ih next
        cases pieces with
        | inside inserted => exact ⟨_, _, _, _, _, _, .cell different nextCut, .inside (.cell inserted)⟩
        | outside inserted => exact ⟨_, _, _, _, _, _, .cell different nextCut, .outside inserted⟩
  | cleanup changed ih => cases cut with
    | cleanup next =>
        obtain ⟨_, _, _, _, _, _, nextCut, pieces⟩ := ih next
        cases pieces with
        | inside inserted => exact ⟨_, _, _, _, _, _, .cleanup nextCut, .inside (.cleanup inserted)⟩
        | outside inserted => exact ⟨_, _, _, _, _, _, .cleanup nextCut, .outside inserted⟩
  | running changed ih => cases cut with
    | running next =>
        obtain ⟨_, _, _, _, _, _, nextCut, pieces⟩ := ih next
        cases pieces with
        | inside inserted => exact ⟨_, _, _, _, _, _, .running nextCut, .inside (.running inserted)⟩
        | outside inserted => exact ⟨_, _, _, _, _, _, .running nextCut, .outside inserted⟩
  | live changed ih => cases cut with
    | live next =>
        obtain ⟨_, _, _, _, _, _, nextCut, pieces⟩ := ih next
        cases pieces with
        | inside inserted => exact ⟨_, _, _, _, _, _, .live nextCut, .inside (.live inserted)⟩
        | outside inserted => exact ⟨_, _, _, _, _, _, .live nextCut, .outside inserted⟩
  | spent changed ih => cases cut with
    | spent next =>
        obtain ⟨_, _, _, _, _, _, nextCut, pieces⟩ := ih next
        cases pieces with
        | inside inserted => exact ⟨_, _, _, _, _, _, .spent nextCut, .inside (.spent inserted)⟩
        | outside inserted => exact ⟨_, _, _, _, _, _, .spent nextCut, .outside inserted⟩

/-- Reuse the existing owner-cut induction with cleanup as the inserted frame.
The owner retains exactly its old saved plan; the callback enters either the
caller prefix or waiting suffix, including calls to outside owners. -/
theorem Insertion.owner_cut {frontHints : Hints frontScope} {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {front : Forest frontHints} {saved : Forest savedHints} {tail : Forest tailHints}
    (changed : Insertion needs callback before after) (cut : SourceScheduledNeutral.OwnerCut owner before front saved tail) :
    ∃ nextFrontScope nextTailScope, ∃ nextFrontHints : Hints nextFrontScope, ∃ nextTailHints : Hints nextTailScope,
    ∃ nextFront : Forest nextFrontHints, ∃ nextTail : Forest nextTailHints,
      SourceScheduledNeutral.OwnerCut owner after nextFront saved nextTail ∧ Split needs callback front tail nextFront nextTail := by
  induction changed generalizing frontScope tailScope with
  | here => exact ⟨_, _, _, _, _, _, .cleanup cut, .inside .here⟩
  | plain changed ih => cases cut with
    | plain next =>
        obtain ⟨_, _, _, _, _, _, nextCut, pieces⟩ := ih next
        cases pieces with
        | inside inserted => exact ⟨_, _, _, _, _, _, .plain nextCut, .inside (.plain inserted)⟩
        | outside inserted => exact ⟨_, _, _, _, _, _, .plain nextCut, .outside inserted⟩
  | handler changed ih => cases cut with
    | handler next =>
        obtain ⟨_, _, _, _, _, _, nextCut, pieces⟩ := ih next
        cases pieces with
        | inside inserted => exact ⟨_, _, _, _, _, _, .handler nextCut, .inside (.handler inserted)⟩
        | outside inserted => exact ⟨_, _, _, _, _, _, .handler nextCut, .outside inserted⟩
  | cell changed ih => cases cut with
    | cell next =>
        obtain ⟨_, _, _, _, _, _, nextCut, pieces⟩ := ih next
        cases pieces with
        | inside inserted => exact ⟨_, _, _, _, _, _, .cell nextCut, .inside (.cell inserted)⟩
        | outside inserted => exact ⟨_, _, _, _, _, _, .cell nextCut, .outside inserted⟩
  | cleanup changed ih => cases cut with
    | cleanup next =>
        obtain ⟨_, _, _, _, _, _, nextCut, pieces⟩ := ih next
        cases pieces with
        | inside inserted => exact ⟨_, _, _, _, _, _, .cleanup nextCut, .inside (.cleanup inserted)⟩
        | outside inserted => exact ⟨_, _, _, _, _, _, .cleanup nextCut, .outside inserted⟩
  | running changed ih => cases cut with
    | running next =>
        obtain ⟨_, _, _, _, _, _, nextCut, pieces⟩ := ih next
        cases pieces with
        | inside inserted => exact ⟨_, _, _, _, _, _, .running nextCut, .inside (.running inserted)⟩
        | outside inserted => exact ⟨_, _, _, _, _, _, .running nextCut, .outside inserted⟩
  | live changed ih => cases cut with
    | hit => exact ⟨_, _, _, _, _, _, .hit, .outside changed⟩
    | live different next =>
        obtain ⟨_, _, _, _, _, _, nextCut, pieces⟩ := ih next
        cases pieces with
        | inside inserted => exact ⟨_, _, _, _, _, _, .live different nextCut, .inside (.live inserted)⟩
        | outside inserted => exact ⟨_, _, _, _, _, _, .live different nextCut, .outside inserted⟩
  | spent changed ih => cases cut with
    | spent next =>
        obtain ⟨_, _, _, _, _, _, nextCut, pieces⟩ := ih next
        cases pieces with
        | inside inserted => exact ⟨_, _, _, _, _, _, .spent nextCut, .inside (.spent inserted)⟩
        | outside inserted => exact ⟨_, _, _, _, _, _, .spent nextCut, .outside inserted⟩

open SourceScheduledPendingSites (Site)

/-- Existing sites in a saved forest keep their exact code when its outside
receiver gains the callback. The new callback belongs to the outside forest. -/
theorem Site.outside {beforeHints : Hints first} {afterHints : Hints second}
    {before : Forest beforeHints} {after : Forest afterHints}
    {hints : Hints scope} {forest : Forest hints} {plan : Plan dependencies}
    {atHints : Hints atScope} {atForest : Forest atHints}
    (changed : Insertion needs callback before after) (site : Site forest after plan atForest) :
    ∃ oldScope, ∃ oldHints : Hints oldScope, ∃ oldForest : Forest oldHints,
      Site forest before plan oldForest ∧ Insertion needs callback oldForest atForest := by
  induction site generalizing first with
  | code => exact ⟨_, _, _, .code, changed.prefix _⟩
  | callback => exact ⟨_, _, _, .callback, .running (changed.prefix _)⟩
  | plain site ih =>
      obtain ⟨_, _, _, oldSite, inserted⟩ := ih changed
      exact ⟨_, _, _, .plain oldSite, inserted⟩
  | handler site ih =>
      obtain ⟨_, _, _, oldSite, inserted⟩ := ih changed
      exact ⟨_, _, _, .handler oldSite, inserted⟩
  | cell site ih =>
      obtain ⟨_, _, _, oldSite, inserted⟩ := ih changed
      exact ⟨_, _, _, .cell oldSite, inserted⟩
  | cleanup site ih =>
      obtain ⟨_, _, _, oldSite, inserted⟩ := ih changed
      exact ⟨_, _, _, .cleanup oldSite, inserted⟩
  | running site ih =>
      obtain ⟨_, _, _, oldSite, inserted⟩ := ih changed
      exact ⟨_, _, _, .running oldSite, inserted⟩
  | saved site ih =>
      obtain ⟨_, _, _, oldSite, inserted⟩ := ih (changed.prefix _)
      exact ⟨_, _, _, .saved oldSite, inserted⟩
  | live site ih =>
      obtain ⟨_, _, _, oldSite, inserted⟩ := ih changed
      exact ⟨_, _, _, .live oldSite, inserted⟩
  | spent site ih =>
      obtain ⟨_, _, _, oldSite, inserted⟩ := ih changed
      exact ⟨_, _, _, .spent oldSite, inserted⟩

/-- The callback's newly registered site follows the actual insertion
derivation. Its receiver is the suffix at registration, under running protection. -/
inductive Registered {needs : List Instance} {dependencies : SourceDependencyAnnotations.Dependencies}
    {callback : Plan dependencies} :
    {first second : Scope} → {beforeHints : Hints first} → {afterHints : Hints second} →
    {before : Forest beforeHints} → {after : Forest afterHints} →
    Insertion needs callback before after →
    {outsideScope : Scope} → {outsideHints : Hints outsideScope} → Forest outsideHints →
    {atScope : Scope} → {atHints : Hints atScope} → Forest atHints → Prop where
  | here : Registered (.here (before := before)) outside (.running (before.append outside))
  | plain : Registered changed outside atForest → Registered (.plain (plan := plan) changed) outside atForest
  | handler : Registered changed outside atForest →
      Registered (.handler (effect := effect) (table := table) (families := families) (required := required) changed) outside atForest
  | cell : Registered changed outside atForest → Registered (.cell (identity := identity) changed) outside atForest
  | cleanup : Registered changed outside atForest → Registered (.cleanup (otherNeeds := otherNeeds) (plan := plan) changed) outside atForest
  | running : Registered changed outside atForest → Registered (.running changed) outside atForest
  | live : Registered changed outside atForest → Registered (.live (owner := owner) (saved := saved) changed) outside atForest
  | spent : Registered changed outside atForest → Registered (.spent (owner := owner) changed) outside atForest

theorem Insertion.registered (changed : Insertion needs callback before after) (outside : Forest outsideHints) :
    ∃ atScope, ∃ atHints : Hints atScope, ∃ atForest : Forest atHints, Registered changed outside atForest := by
  induction changed with
  | here => exact ⟨_, _, _, .here⟩
  | plain changed ih => obtain ⟨_, _, _, registered⟩ := ih; exact ⟨_, _, _, .plain registered⟩
  | handler changed ih => obtain ⟨_, _, _, registered⟩ := ih; exact ⟨_, _, _, .handler registered⟩
  | cell changed ih => obtain ⟨_, _, _, registered⟩ := ih; exact ⟨_, _, _, .cell registered⟩
  | cleanup changed ih => obtain ⟨_, _, _, registered⟩ := ih; exact ⟨_, _, _, .cleanup registered⟩
  | running changed ih => obtain ⟨_, _, _, registered⟩ := ih; exact ⟨_, _, _, .running registered⟩
  | live changed ih => obtain ⟨_, _, _, registered⟩ := ih; exact ⟨_, _, _, .live registered⟩
  | spent changed ih => obtain ⟨_, _, _, registered⟩ := ih; exact ⟨_, _, _, .spent registered⟩

/-- The added site is an actual callback obligation in the existing pending
source judgment, not an abstract requirement detached from stored plans. -/
theorem Registered.site {changed : Insertion needs callback before after}
    (registered : Registered changed outside atForest) : Site after outside callback atForest := by
  induction registered with
  | here => exact .callback
  | plain registered ih => exact .plain ih
  | handler registered ih => exact .handler ih
  | cell registered ih => exact .cell ih
  | cleanup registered ih => exact .cleanup ih
  | running registered ih => exact .running ih
  | live registered ih => exact .live ih
  | spent registered ih => exact .spent ih

/-- Every target site is old, transported, or the newly registered callback
at its exact receiver. The third case is essential for effectful cleanup. -/
theorem Site.inside {beforeHints : Hints first} {afterHints : Hints second}
    {before : Forest beforeHints} {after : Forest afterHints}
    {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
    {plan : Plan dependencies} {callback : Plan callbackDependencies}
    {atHints : Hints atScope} {atForest : Forest atHints}
    (changed : Insertion needs callback before after) (site : Site after outside plan atForest) :
    Site before outside plan atForest ∨
      (∃ oldScope, ∃ oldHints : Hints oldScope, ∃ oldForest : Forest oldHints,
        Site before outside plan oldForest ∧ Insertion needs callback oldForest atForest) ∨
      (dependencies = callbackDependencies ∧ HEq plan callback ∧ Registered changed outside atForest) := by
  induction changed generalizing atScope with
  | here => cases site with
    | callback => exact Or.inr (Or.inr ⟨rfl, HEq.rfl, .here⟩)
    | cleanup next => exact Or.inl next
  | plain changed ih => cases site with
    | code => exact Or.inr (Or.inl ⟨_, _, _, .code, changed.suffix outside⟩)
    | plain next =>
        rcases ih next with same | ⟨_, _, _, oldSite, inserted⟩ | ⟨indices, same, registered⟩
        · exact Or.inl (.plain same)
        · exact Or.inr (Or.inl ⟨_, _, _, .plain oldSite, inserted⟩)
        · exact Or.inr (Or.inr ⟨indices, same, .plain registered⟩)
  | handler changed ih => cases site with
    | handler next =>
        rcases ih next with same | ⟨_, _, _, oldSite, inserted⟩ | ⟨indices, same, registered⟩
        · exact Or.inl (.handler same)
        · exact Or.inr (Or.inl ⟨_, _, _, .handler oldSite, inserted⟩)
        · exact Or.inr (Or.inr ⟨indices, same, .handler registered⟩)
  | cell changed ih => cases site with
    | cell next =>
        rcases ih next with same | ⟨_, _, _, oldSite, inserted⟩ | ⟨indices, same, registered⟩
        · exact Or.inl (.cell same)
        · exact Or.inr (Or.inl ⟨_, _, _, .cell oldSite, inserted⟩)
        · exact Or.inr (Or.inr ⟨indices, same, .cell registered⟩)
  | cleanup changed ih => cases site with
    | callback => exact Or.inr (Or.inl ⟨_, _, _, .callback, .running (changed.suffix outside)⟩)
    | cleanup next =>
        rcases ih next with same | ⟨_, _, _, oldSite, inserted⟩ | ⟨indices, same, registered⟩
        · exact Or.inl (.cleanup same)
        · exact Or.inr (Or.inl ⟨_, _, _, .cleanup oldSite, inserted⟩)
        · exact Or.inr (Or.inr ⟨indices, same, .cleanup registered⟩)
  | running changed ih => cases site with
    | running next =>
        rcases ih next with same | ⟨_, _, _, oldSite, inserted⟩ | ⟨indices, same, registered⟩
        · exact Or.inl (.running same)
        · exact Or.inr (Or.inl ⟨_, _, _, .running oldSite, inserted⟩)
        · exact Or.inr (Or.inr ⟨indices, same, .running registered⟩)
  | live changed ih => cases site with
    | saved next =>
        obtain ⟨_, _, _, oldSite, inserted⟩ := Site.outside (changed.suffix outside) next
        exact Or.inr (Or.inl ⟨_, _, _, .saved oldSite, inserted⟩)
    | live next =>
        rcases ih next with same | ⟨_, _, _, oldSite, inserted⟩ | ⟨indices, same, registered⟩
        · exact Or.inl (.live same)
        · exact Or.inr (Or.inl ⟨_, _, _, .live oldSite, inserted⟩)
        · exact Or.inr (Or.inr ⟨indices, same, .live registered⟩)
  | spent changed ih => cases site with
    | spent next =>
        rcases ih next with same | ⟨_, _, _, oldSite, inserted⟩ | ⟨indices, same, registered⟩
        · exact Or.inl (.spent same)
        · exact Or.inr (Or.inl ⟨_, _, _, .spent oldSite, inserted⟩)
        · exact Or.inr (Or.inr ⟨indices, same, .spent registered⟩)

/-- Internal recomposition of pending source after the old local sites have
been transported and the newly registered callback has been checked. This is
not declaration admission: those local derivations remain explicit premises.
The handler-interface check is derived from the original pending judgment. -/
theorem pending_inside
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    {beforeHints : Hints first} {afterHints : Hints second}
    {before : Forest beforeHints} {after : Forest afterHints}
    {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
    {callback : Plan callbackDependencies}
    (checked : SourceScheduledChecks.Pending outward actions phases world before outside)
    (changed : Insertion needs callback before after)
    (transfer : ∀ {dependencies oldScope nextScope} {plan : Plan dependencies}
      {oldHints : Hints oldScope} {nextHints : Hints nextScope}
      {old : Forest oldHints} {next : Forest nextHints},
      Site before outside plan old → Insertion needs callback old next →
      SourceScheduledChecks.Local outward actions phases world plan old →
      SourceScheduledChecks.Local outward actions phases world plan next)
    (completion : ∀ {atScope} {atHints : Hints atScope} {atForest : Forest atHints},
      Registered changed outside atForest → SourceScheduledChecks.Local outward actions phases world callback atForest) :
    SourceScheduledChecks.Pending outward actions phases world after outside := by
  apply SourceScheduledPendingSites.pending_iff.mpr
  refine ⟨?_, ?_⟩
  · rw [← changed.check_inside outside]
    exact (SourceScheduledPendingSites.pending_iff.mp checked).1
  · intro dependencies atScope plan atHints atForest site
    rcases Site.inside changed site with same | ⟨_, _, _, oldSite, inserted⟩ | ⟨indices, same, registered⟩
    · exact same.checked checked
    · exact transfer oldSite inserted (oldSite.checked checked)
    · cases indices
      cases eq_of_heq same
      exact completion registered

/-- Outside insertion adds no callback site to this retained forest. Its
existing sites are rechecked at their transported receivers; the caller owns
the separate obligation for the callback stored in the outside forest. -/
theorem pending_outside
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    {hints : Hints scope} {forest : Forest hints}
    {beforeHints : Hints first} {afterHints : Hints second}
    {before : Forest beforeHints} {after : Forest afterHints}
    (checked : SourceScheduledChecks.Pending outward actions phases world forest before)
    (changed : Insertion needs callback before after)
    (transfer : ∀ {dependencies oldScope nextScope} {plan : Plan dependencies}
      {oldHints : Hints oldScope} {nextHints : Hints nextScope}
      {old : Forest oldHints} {next : Forest nextHints},
      Site forest before plan old → Insertion needs callback old next →
      SourceScheduledChecks.Local outward actions phases world plan old →
      SourceScheduledChecks.Local outward actions phases world plan next) :
    SourceScheduledChecks.Pending outward actions phases world forest after := by
  apply SourceScheduledPendingSites.pending_iff.mpr
  refine ⟨?_, ?_⟩
  · rw [← changed.check_outside hints]
    exact (SourceScheduledPendingSites.pending_iff.mp checked).1
  · intro dependencies atScope plan atHints atForest site
    obtain ⟨_, _, _, oldSite, inserted⟩ := Site.outside changed site
    exact transfer oldSite inserted (oldSite.checked checked)

namespace Examples

def callback := Plan.request (effect := Instance.cell 4) (operation := 0)
def providedHints : Hints (.cell 4 .nil) := .cell .nil
def provided : Forest providedHints := .cell .nil

/-- Registering an effectful callback creates a code obligation even when
the original pending forest contains only a provider and no code sites. -/
theorem callback_site_is_new :
    Site (.cleanup (needs := [Instance.cell 4]) callback provided) .nil callback (.running (provided.append .nil)) ∧
      ¬ (∃ atScope, ∃ atHints : Hints atScope, ∃ atForest : Forest atHints,
        Site provided .nil callback atForest) := by
  refine ⟨.callback, ?_⟩
  rintro ⟨_, _, _, site⟩
  cases site with | cell next => cases next

/-- The added callback is compiled from its original operation footprint and
the actual provider. There are no old code sites whose transport is assumed. -/
theorem effectful_callback_pending :
    SourceScheduledChecks.Pending [] actions phases [4]
      (.cleanup (needs := [Instance.cell 4]) callback provided) .nil := by
  apply pending_inside (before := provided) (.cell .nil) .here
  · intro dependencies oldScope nextScope plan oldHints nextHints old next site inserted ready
    cases site with | cell next => cases next
  · intro atScope atHints atForest registered
    cases registered with
    | here => exact SourceScheduledSourceInterfaces.compile .request .request rfl

end Examples

end Ash.OneShot.SourceScheduledCleanupInsertion

#print axioms Ash.OneShot.SourceScheduledCleanupInsertion.Insertion.prefix
#print axioms Ash.OneShot.SourceScheduledCleanupInsertion.Insertion.suffix
#print axioms Ash.OneShot.SourceScheduledCleanupInsertion.Insertion.forClosing
#print axioms Ash.OneShot.SourceScheduledCleanupInsertion.Insertion.owners
#print axioms Ash.OneShot.SourceScheduledCleanupInsertion.Split.forClosing
#print axioms Ash.OneShot.SourceScheduledCleanupInsertion.Split.spent_append
#print axioms Ash.OneShot.SourceScheduledCleanupInsertion.Split.resumed
#print axioms Ash.OneShot.SourceScheduledCleanupInsertion.Split.disposed
#print axioms Ash.OneShot.SourceScheduledCleanupInsertion.Insertion.cut

#print axioms Ash.OneShot.SourceScheduledCleanupInsertion.Insertion.owner_cut

#print axioms Ash.OneShot.SourceScheduledCleanupInsertion.Site.outside
#print axioms Ash.OneShot.SourceScheduledCleanupInsertion.Insertion.registered
#print axioms Ash.OneShot.SourceScheduledCleanupInsertion.Registered.site
#print axioms Ash.OneShot.SourceScheduledCleanupInsertion.Site.inside

#print axioms Ash.OneShot.SourceScheduledCleanupInsertion.Insertion.location

#print axioms Ash.OneShot.SourceScheduledCleanupInsertion.Insertion.capability

#print axioms Ash.OneShot.SourceScheduledCleanupInsertion.Insertion.requirements

#print axioms Ash.OneShot.SourceScheduledCleanupInsertion.Insertion.check_outside

#print axioms Ash.OneShot.SourceScheduledCleanupInsertion.Insertion.check_inside
#print axioms Ash.OneShot.SourceScheduledCleanupInsertion.pending_inside
#print axioms Ash.OneShot.SourceScheduledCleanupInsertion.pending_outside
#print axioms Ash.OneShot.SourceScheduledCleanupInsertion.Examples.callback_site_is_new
#print axioms Ash.OneShot.SourceScheduledCleanupInsertion.Examples.effectful_callback_pending
