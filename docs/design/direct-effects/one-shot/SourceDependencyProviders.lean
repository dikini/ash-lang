import SourceProviderInsertion
import SourceDependencyNeutral

/-! Transport the retained dependency checks through one active builtin
provider. Requests may change from a source handler to the builtin; dormant
captures retain their code and receive the provider through their outside. -/
namespace Ash.OneShot.SourceDependencyProviders
open SourceContextualHints (Hints)
open SourceContextualInvocationHints (forClosing)
open SourceDependencyChecks (Local Pending)
open SourceDependencyNeutral (projected)
open SourceProviderInsertion (Insertion Split)

theorem insertion_projected (changed : Insertion identity before after) :
    Insertion identity (projected before) (projected after) := by
  induction changed with
  | here => exact .here
  | plain next ih => exact .plain ih
  | handler next ih => exact .handler ih
  | cell next ih => exact .cell ih
  | cleanup next ih => exact .cleanup ih
  | running next ih => exact .running ih
  | live next ih => exact .live ih
  | spent next ih => exact ih

/-- Reuse the existing mutual checking induction. The pending motive records
which side gains the provider, rather than assuming identical handler lookup. -/
theorem local_transport (checked : Local outward actions phases world dependencies scope)
    {hints : Hints scope} {next : Hints nextScope} (changed : Insertion identity hints next) :
    Local outward actions phases world dependencies nextScope := by
  refine (Local.rec
    (motive_1 := fun phases world dependencies scope _ => ∀ {nextScope}
      (hints : Hints scope) (next : Hints nextScope), Insertion identity hints next →
      Local outward actions phases world dependencies nextScope)
    (motive_2 := fun phases world scope outside _ => ∀ {nextScope nextOutside}
      (hints : Hints scope) (outsideHints : Hints outside)
      (next : Hints nextScope) (nextOutsideHints : Hints nextOutside),
      Split identity hints outsideHints next nextOutsideHints →
      Pending outward actions phases world nextScope nextOutside)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (t := checked)) hints next changed
  · intros; exact .pure
  · intros
    rename_i guard scheduled bounded ih nextScope hints next changed
    have guarded := changed.capture_guard guard
    apply Local.request guarded
    · intro actualSaved actualWaiting contract modes actual disposes
      cases guard with
      | builtin found =>
          obtain ⟨_, nextFound⟩ := changed.builtin found
          cases Option.some.inj (nextFound.symm.trans actual)
      | handler found permission row body closing =>
          obtain ⟨saved, waiting, cut⟩ := SourcePlannedCuts.of_lookup hints found
          rcases changed.cut cut with nextFound | ⟨_, _, nextSaved, nextWaiting, nextCut, pieces⟩
          · cases Option.some.inj (nextFound.symm.trans actual)
          · cases Option.some.inj (nextCut.lookup.symm.trans actual)
            apply ih _ _ _ _ found disposes (projected (forClosing saved)) (projected (.running waiting))
              (projected (forClosing nextSaved)) (projected (.running nextWaiting))
            cases pieces with
            | inside inserted => exact .inside (insertion_projected inserted.forClosing)
            | outside inserted => exact .outside (insertion_projected (.running inserted))
    · intro actualSaved actualWaiting contract modes actual disposes
      cases guard with
      | builtin found =>
          obtain ⟨_, nextFound⟩ := changed.builtin found
          cases Option.some.inj (nextFound.symm.trans actual)
      | handler found permission row body closing =>
          obtain ⟨saved, waiting, cut⟩ := SourcePlannedCuts.of_lookup hints found
          rcases changed.cut cut with nextFound | ⟨_, _, nextSaved, nextWaiting, nextCut, pieces⟩
          · cases Option.some.inj (nextFound.symm.trans actual)
          · cases Option.some.inj (nextCut.lookup.symm.trans actual)
            cases pieces with
            | inside inserted =>
                have owners := inserted.pending_owners (bounded _ _ _ _ found disposes)
                rw [inserted.owners] at owners
                exact owners
            | outside inserted => exact bounded _ _ _ _ found disposes
  · intros
    rename_i access restored ih nextScope hints next changed
    obtain ⟨original, _, after, nextAccess, related⟩ := changed.resume_access access
    exact .resume nextAccess (ih (projected original) .nil (projected after) .nil (.inside (insertion_projected related)))
  · intros
    rename_i access scheduled ih nextScope hints next changed
    obtain ⟨original, _, after, nextAccess, related⟩ := changed.dispose_access access
    exact .dispose nextAccess (ih (projected original) .nil (projected after) .nil (.inside (insertion_projected related)))
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
    rename_i nextScope nextOutside hints outsideHints next nextOutsideHints changed
    cases changed with
    | inside inserted => cases hints; cases inserted; exact .cell .nil
    | outside inserted => exact .nil
  · intros
    rename_i code tail ihCode ihTail nextScope nextOutside hints outsideHints next nextOutsideHints changed
    cases hints with | plain rest =>
      cases changed with
      | outside inserted =>
          exact .plain (ihCode (rest.append outsideHints) _ (inserted.prefix rest))
            (ihTail rest outsideHints _ _ (.outside inserted))
      | inside inserted => cases inserted with
        | here => exact .cell (.plain code tail)
        | plain inserted =>
            exact .plain (ihCode (rest.append outsideHints) _ (inserted.suffix outsideHints))
              (ihTail rest outsideHints _ _ (.inside inserted))
  · intros
    rename_i tail ih nextScope nextOutside hints outsideHints next nextOutsideHints changed
    cases hints with | handler required rest =>
      cases changed with
      | outside inserted => exact .handler (ih rest outsideHints _ _ (.outside inserted))
      | inside inserted => cases inserted with
        | here => exact .cell (.handler tail)
        | handler inserted => exact .handler (ih rest outsideHints _ _ (.inside inserted))
  · intros
    rename_i tail ih nextScope nextOutside hints outsideHints next nextOutsideHints changed
    cases hints with | cell rest =>
      cases changed with
      | outside inserted => exact .cell (ih rest outsideHints _ _ (.outside inserted))
      | inside inserted => cases inserted with
        | here => exact .cell (.cell tail)
        | cell inserted => exact .cell (ih rest outsideHints _ _ (.inside inserted))
  · intros
    rename_i completion tail ihCompletion ihTail nextScope nextOutside hints outsideHints next nextOutsideHints changed
    cases hints with | cleanup rest =>
      cases changed with
      | outside inserted =>
          exact .cleanup (ihCompletion (.running (rest.append outsideHints)) _ (.running (inserted.prefix rest)))
            (ihTail rest outsideHints _ _ (.outside inserted))
      | inside inserted => cases inserted with
        | here => exact .cell (.cleanup completion tail)
        | cleanup inserted =>
            exact .cleanup (ihCompletion (.running (rest.append outsideHints)) _ (.running (inserted.suffix outsideHints)))
              (ihTail rest outsideHints _ _ (.inside inserted))
  · intros
    rename_i tail ih nextScope nextOutside hints outsideHints next nextOutsideHints changed
    cases hints with | running rest =>
      cases changed with
      | outside inserted => exact .running (ih rest outsideHints _ _ (.outside inserted))
      | inside inserted => cases inserted with
        | here => exact .cell (.running tail)
        | running inserted => exact .running (ih rest outsideHints _ _ (.inside inserted))
  · intros
    rename_i saved tail ihSaved ihTail nextScope nextOutside hints outsideHints next nextOutsideHints changed
    cases hints with | live savedHints rest =>
      cases changed with
      | outside inserted =>
          exact .live (ihSaved savedHints (rest.append outsideHints) _ _ (.outside (inserted.prefix rest)))
            (ihTail rest outsideHints _ _ (.outside inserted))
      | inside inserted => cases inserted with
        | here => exact .cell (.live saved tail)
        | live inserted =>
            exact .live (ihSaved savedHints (rest.append outsideHints) _ _ (.outside (inserted.suffix outsideHints)))
              (ihTail rest outsideHints _ _ (.inside inserted))
  · intros
    rename_i tail ih nextScope nextOutside hints outsideHints next nextOutsideHints changed
    cases hints with | spent rest =>
      cases changed with
      | outside inserted => exact .spent (ih rest outsideHints _ _ (.outside inserted))
      | inside inserted => cases inserted with
        | here => exact .cell (.spent tail)
        | spent inserted => exact .spent (ih rest outsideHints _ _ (.inside inserted))

/-- Stored source can also receive an additional provider from its outside.
This includes the dormant captures retained in live clauses. -/
theorem pending_outside_transport (checked : Pending outward actions phases world scope outside)
    {hints : Hints scope} {outsideHints : Hints outside} {next : Hints nextScope}
    (changed : Insertion identity outsideHints next) :
    Pending outward actions phases world scope nextScope := by
  induction hints generalizing outside nextScope with
  | nil => exact .nil
  | plain rest ih => cases checked with
    | plain code tail => exact .plain (local_transport code (changed.prefix rest)) (ih tail changed)
  | handler required rest ih => cases checked with | handler tail => exact .handler (ih tail changed)
  | cell rest ih => cases checked with | cell tail => exact .cell (ih tail changed)
  | cleanup rest ih => cases checked with
    | cleanup callback tail => exact .cleanup (local_transport callback (.running (changed.prefix rest))) (ih tail changed)
  | running rest ih => cases checked with | running tail => exact .running (ih tail changed)
  | live saved rest ihSaved ihRest => cases checked with
    | live inside tail => exact .live (ihSaved inside (changed.prefix rest)) (ihRest tail changed)
  | spent rest ih => cases checked with | spent tail => exact .spent (ih tail changed)

/-- Retain every pending expression and callback when its active spine gains
one provider. Existing source and continuation phases are unchanged. -/
theorem pending_inside_transport (checked : Pending outward actions phases world scope outside)
    {hints : Hints scope} {outsideHints : Hints outside} {next : Hints nextScope}
    (changed : Insertion identity hints next) :
    Pending outward actions phases world nextScope outside := by
  induction changed with
  | here => exact .cell checked
  | plain changed ih => cases checked with
    | plain code tail => exact .plain (local_transport code (changed.suffix outsideHints)) (ih tail)
  | handler changed ih => cases checked with | handler tail => exact .handler (ih tail)
  | cell changed ih => cases checked with | cell tail => exact .cell (ih tail)
  | cleanup changed ih => cases checked with
    | cleanup callback tail => exact .cleanup (local_transport callback (.running (changed.suffix outsideHints))) (ih tail)
  | running changed ih => cases checked with | running tail => exact .running (ih tail)
  | live changed ih =>
      rename_i savedHints
      cases checked with
      | live saved tail => exact .live (pending_outside_transport saved (hints := savedHints) (changed.suffix outsideHints)) (ih tail)
  | spent changed ih => cases checked with | spent tail => exact .spent (ih tail)

end Ash.OneShot.SourceDependencyProviders

#print axioms Ash.OneShot.SourceDependencyProviders.insertion_projected
#print axioms Ash.OneShot.SourceDependencyProviders.local_transport
#print axioms Ash.OneShot.SourceDependencyProviders.pending_outside_transport
#print axioms Ash.OneShot.SourceDependencyProviders.pending_inside_transport

namespace Ash.OneShot.SourceDependencyProviders.Lexical
open SourceContextualHints (Hints)
open SourceDependencyChecks.Lexical (Local Pending Unwind)
open SourceProviderInsertion (Insertion Split)

/-- An active builtin provider retains lexical callback and owner checks.
The existing insertion laws supply handler and owner lookup correspondence. -/
theorem local_transport (checked : Local outward actions phases world dependencies scope)
    {hints : Hints scope} {next : Hints nextScope} (changed : Insertion identity hints next) :
    Local outward actions phases world dependencies nextScope := by
  refine (Local.rec
    (motive_1 := fun phases world dependencies scope _ => ∀ {nextScope}
      (hints : Hints scope) (next : Hints nextScope), Insertion identity hints next →
      Local outward actions phases world dependencies nextScope)
    (motive_2 := fun phases world scope outside _ => ∀ {nextScope nextOutside}
      (hints : Hints scope) (outsideHints : Hints outside)
      (next : Hints nextScope) (nextOutsideHints : Hints nextOutside),
      Split identity hints outsideHints next nextOutsideHints →
      Pending outward actions phases world nextScope nextOutside)
    (motive_3 := fun phases world scope outside _ => ∀ {nextScope nextOutside}
      (hints : Hints scope) (outsideHints : Hints outside)
      (next : Hints nextScope) (nextOutsideHints : Hints nextOutside),
      Split identity hints outsideHints next nextOutsideHints →
      Unwind outward actions phases world nextScope nextOutside)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (t := checked)) hints next changed
  · intros; exact .pure
  · intros
    rename_i guard callbacks bounded ihCallbacks nextScope hints next changed
    cases guard with
    | builtin found =>
        obtain ⟨_, nextFound⟩ := changed.builtin found
        apply Local.request (.builtin nextFound)
        all_goals
          intro saved waiting contract modes found disposes
          cases Option.some.inj (nextFound.symm.trans found)
    | handler found permission row body =>
        obtain ⟨saved, waiting, cut⟩ := SourcePlannedCuts.of_lookup hints found
        rcases changed.cut cut with nextFound | ⟨_, _, nextSaved, nextWaiting, nextCut, pieces⟩
        · apply Local.request (.builtin nextFound)
          all_goals
            intro saved waiting contract modes found disposes
            cases Option.some.inj (nextFound.symm.trans found)
        · have heldSame := by
            cases pieces with
            | inside inserted => exact inserted.held
            | outside inserted => exact rfl
          apply Local.request (.handler nextCut.lookup (heldSame ▸ permission) (heldSame ▸ row) (heldSame ▸ body))
          · intro actualSaved actualWaiting contract modes actual disposes
            cases Option.some.inj (nextCut.lookup.symm.trans actual)
            apply ihCallbacks _ _ _ _ found disposes saved (.running waiting) nextSaved (.running nextWaiting)
            cases pieces with
            | inside inserted => exact .inside inserted
            | outside inserted => exact .outside (.running inserted)
          · intro actualSaved actualWaiting contract modes actual disposes
            cases Option.some.inj (nextCut.lookup.symm.trans actual)
            cases pieces with
            | inside inserted =>
                have owners := inserted.pending_owners (bounded _ _ _ _ found disposes)
                rw [inserted.owners] at owners
                exact owners
            | outside inserted => exact bounded _ _ _ _ found disposes
  · intros
    rename_i access restored ih nextScope hints next changed
    obtain ⟨original, _, after, nextAccess, related⟩ := changed.resume_access access
    exact .resume nextAccess (ih original .nil after .nil (.inside related))
  · intros
    rename_i located known permission available unprotected callbacks waiting ihCallbacks ihWaiting nextScope hints next changed
    obtain ⟨selected, found, same⟩ : ∃ selected,
        SourceContextualInvocationHints.findOwner _ hints = some selected ∧ selected.scopes = _ := by
      apply Option.map_eq_some_iff.mp
      rw [SourceContextualInvocationHints.find_owner_erases]
      exact located.lookup
    cases same
    obtain ⟨nextSelected, foundNext, related⟩ := changed.find_owner found
    have savedSame : selected.scopes.captured = nextSelected.scopes.captured := by cases related <;> rfl
    rename_i owner _ _ _ _
    have waitingInsertion : Insertion identity (selected.front.append (.spent (owner := owner) selected.tail))
        (nextSelected.front.append (.spent (owner := owner) nextSelected.tail)) := by
      cases related with
      | caller changed => exact changed.suffix _
      | waiting changed => exact (Insertion.spent changed).prefix _
    apply Local.dispose (SourceContextualInvocationHints.selected_cut foundNext) known permission available
      (savedSame ▸ unprotected)
    · have pieces : Split identity selected.saved (.running (selected.front.append (.spent (owner := owner) selected.tail)))
          nextSelected.saved (.running (nextSelected.front.append (.spent (owner := owner) nextSelected.tail))) := by
        cases related <;> exact .outside (.running waitingInsertion)
      exact ihCallbacks _ _ _ _ pieces
    · exact ihWaiting _ .nil _ .nil (.inside waitingInsertion)
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
    rename_i nextScope nextOutside hints outsideHints next nextOutsideHints changed
    cases changed with
    | inside inserted => cases hints; cases inserted; exact .cell .nil
    | outside inserted => exact .nil
  · intros
    rename_i code tail ihCode ihTail nextScope nextOutside hints outsideHints next nextOutsideHints changed
    cases hints with | plain rest =>
      cases changed with
      | outside inserted =>
          exact .plain (ihCode (rest.append outsideHints) _ (inserted.prefix rest))
            (ihTail rest outsideHints _ _ (.outside inserted))
      | inside inserted => cases inserted with
        | here => exact .cell (.plain code tail)
        | plain inserted =>
            exact .plain (ihCode (rest.append outsideHints) _ (inserted.suffix outsideHints))
              (ihTail rest outsideHints _ _ (.inside inserted))
  · intros
    rename_i tail ih nextScope nextOutside hints outsideHints next nextOutsideHints changed
    cases hints with | handler required rest =>
      cases changed with
      | outside inserted => exact .handler (ih rest outsideHints _ _ (.outside inserted))
      | inside inserted => cases inserted with
        | here => exact .cell (.handler tail)
        | handler inserted => exact .handler (ih rest outsideHints _ _ (.inside inserted))
  · intros
    rename_i tail ih nextScope nextOutside hints outsideHints next nextOutsideHints changed
    cases hints with | cell rest =>
      cases changed with
      | outside inserted => exact .cell (ih rest outsideHints _ _ (.outside inserted))
      | inside inserted => cases inserted with
        | here => exact .cell (.cell tail)
        | cell inserted => exact .cell (ih rest outsideHints _ _ (.inside inserted))
  · intros
    rename_i completion tail ihCompletion ihTail nextScope nextOutside hints outsideHints next nextOutsideHints changed
    cases hints with | cleanup rest =>
      cases changed with
      | outside inserted =>
          exact .cleanup (ihCompletion (.running (rest.append outsideHints)) _ (.running (inserted.prefix rest)))
            (ihTail rest outsideHints _ _ (.outside inserted))
      | inside inserted => cases inserted with
        | here => exact .cell (.cleanup completion tail)
        | cleanup inserted =>
            exact .cleanup (ihCompletion (.running (rest.append outsideHints)) _ (.running (inserted.suffix outsideHints)))
              (ihTail rest outsideHints _ _ (.inside inserted))
  · intros
    rename_i tail ih nextScope nextOutside hints outsideHints next nextOutsideHints changed
    cases hints with | running rest =>
      cases changed with
      | outside inserted => exact .running (ih rest outsideHints _ _ (.outside inserted))
      | inside inserted => cases inserted with
        | here => exact .cell (.running tail)
        | running inserted => exact .running (ih rest outsideHints _ _ (.inside inserted))
  · intros
    rename_i saved tail ihSaved ihTail nextScope nextOutside hints outsideHints next nextOutsideHints changed
    cases hints with | live savedHints rest =>
      cases changed with
      | outside inserted =>
          exact .live (ihSaved savedHints (rest.append outsideHints) _ _ (.outside (inserted.prefix rest)))
            (ihTail rest outsideHints _ _ (.outside inserted))
      | inside inserted => cases inserted with
        | here => exact .cell (.live saved tail)
        | live inserted =>
            exact .live (ihSaved savedHints (rest.append outsideHints) _ _ (.outside (inserted.suffix outsideHints)))
              (ihTail rest outsideHints _ _ (.inside inserted))
  · intros
    rename_i tail ih nextScope nextOutside hints outsideHints next nextOutsideHints changed
    cases hints with | spent rest =>
      cases changed with
      | outside inserted => exact .spent (ih rest outsideHints _ _ (.outside inserted))
      | inside inserted => cases inserted with
        | here => exact .cell (.spent tail)
        | spent inserted => exact .spent (ih rest outsideHints _ _ (.inside inserted))
  · intros
    rename_i nextScope nextOutside hints outsideHints next nextOutsideHints changed
    cases changed with
    | inside inserted => cases hints; cases inserted; exact .cell .nil
    | outside inserted => exact .nil
  · intros
    rename_i tail ih nextScope nextOutside hints outsideHints next nextOutsideHints changed
    cases hints with | plain rest =>
      cases changed with
      | outside inserted => exact .plain (ih rest outsideHints _ _ (.outside inserted))
      | inside inserted => cases inserted with
        | here => exact .cell (.plain tail)
        | plain inserted => exact .plain (ih rest outsideHints _ _ (.inside inserted))
  · intros
    rename_i tail ih nextScope nextOutside hints outsideHints next nextOutsideHints changed
    cases hints with | handler required rest =>
      cases changed with
      | outside inserted => exact .handler (ih rest outsideHints _ _ (.outside inserted))
      | inside inserted => cases inserted with
        | here => exact .cell (.handler tail)
        | handler inserted => exact .handler (ih rest outsideHints _ _ (.inside inserted))
  · intros
    rename_i tail ih nextScope nextOutside hints outsideHints next nextOutsideHints changed
    cases hints with | cell rest =>
      cases changed with
      | outside inserted => exact .cell (ih rest outsideHints _ _ (.outside inserted))
      | inside inserted => cases inserted with
        | here => exact .cell (.cell tail)
        | cell inserted => exact .cell (ih rest outsideHints _ _ (.inside inserted))
  · intros
    rename_i completion tail ihCompletion ihTail nextScope nextOutside hints outsideHints next nextOutsideHints changed
    cases hints with | cleanup rest =>
      cases changed with
      | outside inserted =>
          exact .cleanup (ihCompletion (.running (rest.append outsideHints)) _ (.running (inserted.prefix rest)))
            (ihTail rest outsideHints _ _ (.outside inserted))
      | inside inserted => cases inserted with
        | here => exact .cell (.cleanup completion tail)
        | cleanup inserted =>
            exact .cleanup (ihCompletion (.running (rest.append outsideHints)) _ (.running (inserted.suffix outsideHints)))
              (ihTail rest outsideHints _ _ (.inside inserted))
  · intros
    rename_i tail ih nextScope nextOutside hints outsideHints next nextOutsideHints changed
    cases hints with | running rest =>
      cases changed with
      | outside inserted => exact .running (ih rest outsideHints _ _ (.outside inserted))
      | inside inserted => cases inserted with
        | here => exact .cell (.running tail)
        | running inserted => exact .running (ih rest outsideHints _ _ (.inside inserted))
  · intros
    rename_i saved tail ihSaved ihTail nextScope nextOutside hints outsideHints next nextOutsideHints changed
    cases hints with | live savedHints rest =>
      cases changed with
      | outside inserted =>
          exact .live (ihSaved savedHints (.running (rest.append outsideHints)) _ _ (.outside (.running (inserted.prefix rest))))
            (ihTail rest outsideHints _ _ (.outside inserted))
      | inside inserted => cases inserted with
        | here => exact .cell (.live saved tail)
        | live inserted =>
            exact .live (ihSaved savedHints (.running (rest.append outsideHints)) _ _ (.outside (.running (inserted.suffix outsideHints))))
              (ihTail rest outsideHints _ _ (.inside inserted))
  · intros
    rename_i tail ih nextScope nextOutside hints outsideHints next nextOutsideHints changed
    cases hints with | spent rest =>
      cases changed with
      | outside inserted => exact .spent (ih rest outsideHints _ _ (.outside inserted))
      | inside inserted => cases inserted with
        | here => exact .cell (.spent tail)
        | spent inserted => exact .spent (ih rest outsideHints _ _ (.inside inserted))


end Ash.OneShot.SourceDependencyProviders.Lexical
#print axioms Ash.OneShot.SourceDependencyProviders.Lexical.local_transport

namespace Ash.OneShot.SourceDependencyProviders.Lexical.Recursive
open ScopedExpressions ProtectionContracts
open SourceDependencyCapture (Scope OwnerCut select)
open SourceDependencyChecks.Lexical (ReturnHints Capture)
open SourceDependencyChecks.Lexical.ReturnHints.Recursive (Local Pending callbackBoundary)
open SourceDependencyNeutral.Lexical.Recursive (Cut Selection findOwner selected_cut selected_reconstructed_cut
  selected_hints find_owner_pieces return_mode_heq eraseReturn)
open OwnerPhaseTransitions (spend)
open LexicalUnwind (UseMode)

inductive Insertion (identity : Nat) : {first second : Scope} → ReturnHints first → ReturnHints second → Prop where
  | here : Insertion identity before (.cell (identity := identity) before)
  | plain : Insertion identity before after →
      Insertion identity (.plain (dependencies := dependencies) before) (.plain (dependencies := dependencies) after)
  | handler : Insertion identity before after →
      Insertion identity (.handler (effect := effect) (table := table) (families := families) before)
        (.handler (effect := effect) (table := table) (families := families) after)
  | cell : Insertion identity before after →
      Insertion identity (.cell (identity := other) before) (.cell (identity := other) after)
  | cleanup : Insertion identity before after →
      Insertion identity (.cleanup (needs := needs) (callback := callback) before)
        (.cleanup (needs := needs) (callback := callback) after)
  | running : Insertion identity before after → Insertion identity (.running kind before) (.running kind after)
  | live : Insertion identity before after →
      Insertion identity (.live (owner := owner) saved before) (.live (owner := owner) saved after)
  | spent : Insertion identity before after →
      Insertion identity (.spent (owner := owner) before) (.spent (owner := owner) after)

theorem Insertion.prefix (front : ReturnHints scope) (changed : Insertion identity before after) :
    Insertion identity (front.append before) (front.append after) := by
  induction front with
  | nil => exact changed
  | plain rest ih => exact .plain ih
  | handler rest ih => exact .handler ih
  | cell rest ih => exact .cell ih
  | cleanup rest ih => exact .cleanup ih
  | running kind rest ih => exact .running ih
  | live saved rest ihSaved ihRest => exact .live ihRest
  | spent rest ih => exact .spent ih

theorem Insertion.suffix (changed : Insertion identity before after) (tail : ReturnHints scope) :
    Insertion identity (before.append tail) (after.append tail) := by
  induction changed with
  | here => exact .here
  | plain changed ih => exact .plain ih
  | handler changed ih => exact .handler ih
  | cell changed ih => exact .cell ih
  | cleanup changed ih => exact .cleanup ih
  | running changed ih => exact .running ih
  | live changed ih => exact .live ih
  | spent changed ih => exact .spent ih

theorem Insertion.erases (changed : Insertion identity before after) :
    SourceProviderInsertion.Insertion identity (eraseReturn before) (eraseReturn after) := by
  induction changed with
  | here => exact .here
  | plain changed ih => exact .plain ih
  | handler changed ih => exact .handler ih
  | cell changed ih => exact .cell ih
  | cleanup changed ih => exact .cleanup ih
  | running changed ih => exact .running ih
  | live changed ih => exact .live ih
  | spent changed ih => exact .spent ih

theorem Insertion.return_mode (changed : Insertion identity before after) (mode : UseMode) :
    before.returnMode mode = after.returnMode mode := by
  induction changed generalizing mode <;> simp_all [ReturnHints.returnMode]

inductive Split (identity : Nat) : {first outside second nextOutside : Scope} →
    ReturnHints first → ReturnHints outside → ReturnHints second → ReturnHints nextOutside → Prop where
  | inside (changed : Insertion identity before after) : Split identity before tail after tail
  | outside (changed : Insertion identity before after) : Split identity saved before saved after

theorem Split.prepend (changed : Split identity saved waiting nextSaved nextWaiting)
    (layer : Scope → Scope) (lift : ∀ {scope}, ReturnHints scope → ReturnHints (layer scope))
    (preserves : ∀ {first second} {before : ReturnHints first} {after : ReturnHints second},
      Insertion identity before after → Insertion identity (lift before) (lift after)) :
    Split identity (lift saved) waiting (lift nextSaved) nextWaiting := by
  cases changed with
  | inside next => exact .inside (preserves next)
  | outside next => exact .outside next

open SourceDependencyCapture (select)

/-- A cell can replace the selected handler with its builtin. Otherwise the
same handler, modes and actual annotated pieces survive the insertion. -/
theorem Insertion.cut {before : ReturnHints first} {after : ReturnHints second}
    {saved : ReturnHints captured} {waiting : ReturnHints tail}
    (changed : Insertion identity before after)
    (cut : SourceDependencyNeutral.Lexical.Recursive.Cut effect operation contract modes before saved waiting) :
    select effect operation second = some (.builtin identity) ∨
      ∃ captured tail, ∃ nextSaved : ReturnHints captured, ∃ nextWaiting : ReturnHints tail,
        SourceDependencyNeutral.Lexical.Recursive.Cut effect operation contract modes after nextSaved nextWaiting ∧ Split identity saved waiting nextSaved nextWaiting := by
  induction changed generalizing captured tail with
  | here =>
      by_cases hit : effect = .cell identity
      · exact .inl (by simp only [select, if_pos hit])
      · exact .inr ⟨_, _, _, _, .cell hit cut, .inside .here⟩
  | handler changed ih => cases cut with
    | hit known declared => exact .inr ⟨_, _, _, _, .hit known declared, .outside changed⟩
    | handler different next =>
        rcases ih next with found | ⟨_, _, nextSaved, nextWaiting, nextCut, pieces⟩
        · exact .inl (by simp only [select, if_neg different, found, Option.map_some, SourceDependencyCapture.Selection.prepend])
        · exact .inr ⟨_, _, _, _, .handler different nextCut, pieces.prepend (fun scope => .handler _ _ _ scope) (fun hints => .handler hints) (fun changed => .handler changed)⟩
  | cell changed ih => cases cut with
    | cell different next =>
        rcases ih next with found | ⟨_, _, nextSaved, nextWaiting, nextCut, pieces⟩
        · exact .inl (by simp only [select, if_neg different, found, Option.map_some, SourceDependencyCapture.Selection.prepend])
        · exact .inr ⟨_, _, _, _, .cell different nextCut, pieces.prepend (fun scope => .cell _ scope) (fun hints => .cell hints) (fun changed => .cell changed)⟩
  | plain changed ih => cases cut with
    | plain next =>
        rcases ih next with found | ⟨_, _, nextSaved, nextWaiting, nextCut, pieces⟩
        · exact .inl (by simp only [select, found, Option.map_some, SourceDependencyCapture.Selection.prepend])
        · exact .inr ⟨_, _, _, _, .plain nextCut, pieces.prepend (fun scope => .plain _ scope) (fun hints => .plain hints) (fun changed => .plain changed)⟩
  | cleanup changed ih => cases cut with
    | cleanup next =>
        rcases ih next with found | ⟨_, _, nextSaved, nextWaiting, nextCut, pieces⟩
        · exact .inl (by simp only [select, found, Option.map_some, SourceDependencyCapture.Selection.prepend])
        · exact .inr ⟨_, _, _, _, .cleanup nextCut, pieces.prepend (fun scope => .cleanup _ _ scope) (fun hints => .cleanup hints) (fun changed => .cleanup changed)⟩
  | running changed ih => cases cut with
    | running next =>
        rcases ih next with found | ⟨_, _, nextSaved, nextWaiting, nextCut, pieces⟩
        · exact .inl (by simp only [select, found, Option.map_some, SourceDependencyCapture.Selection.prepend])
        · exact .inr ⟨_, _, _, _, .running nextCut, pieces.prepend (fun scope => .running scope) (fun hints => .running _ hints) (fun changed => .running changed)⟩
  | live changed ih => cases cut with
    | live next =>
        rcases ih next with found | ⟨_, _, nextSaved, nextWaiting, nextCut, pieces⟩
        · exact .inl (by simp only [select, found, Option.map_some, SourceDependencyCapture.Selection.prepend])
        · exact .inr ⟨_, _, _, _, .live nextCut, pieces.prepend (fun scope => .live _ _ scope) (fun hints => .live _ hints) (fun changed => .live changed)⟩
  | spent changed ih => cases cut with
    | spent next =>
        rcases ih next with found | ⟨_, _, nextSaved, nextWaiting, nextCut, pieces⟩
        · exact .inl (by simp only [select, found, Option.map_some, SourceDependencyCapture.Selection.prepend])
        · exact .inr ⟨_, _, _, _, .spent nextCut, pieces.prepend (fun scope => .spent _ scope) (fun hints => .spent hints) (fun changed => .spent changed)⟩

theorem Split.append (changed : Split identity first suffix second nextOutside) :
    Insertion identity (first.append suffix) (second.append nextOutside) := by
  cases changed with
  | inside inserted => exact inserted.suffix _
  | outside inserted => exact inserted.prefix _

inductive OwnerInsertion (identity : Nat) : Selection → Selection → Prop where
  | caller {front : ReturnHints first} {nextFront : ReturnHints second} {saved : ReturnHints captured} {tail : ReturnHints waiting}
      (changed : Insertion identity front nextFront) :
      OwnerInsertion identity ⟨⟨first, captured, waiting⟩, front, saved, tail⟩
        ⟨⟨second, captured, waiting⟩, nextFront, saved, tail⟩
  | waiting {front : ReturnHints caller} {saved : ReturnHints captured} {tail : ReturnHints first} {nextTail : ReturnHints second}
      (changed : Insertion identity tail nextTail) :
      OwnerInsertion identity ⟨⟨caller, captured, first⟩, front, saved, tail⟩
        ⟨⟨caller, captured, second⟩, front, saved, nextTail⟩

theorem OwnerInsertion.prepend (changed : OwnerInsertion identity first second)
    (layer : Scope → Scope) (lift : ∀ {scope}, ReturnHints scope → ReturnHints (layer scope))
    (preserves : ∀ {a b} {before : ReturnHints a} {after : ReturnHints b},
      Insertion identity before after → Insertion identity (lift before) (lift after)) :
    OwnerInsertion identity (first.prepend layer lift) (second.prepend layer lift) := by
  cases changed with
  | caller inserted => exact .caller (preserves inserted)
  | waiting inserted => exact .waiting inserted

theorem Insertion.find_owner (changed : Insertion identity before after)
    (found : findOwner owner before = some selected) :
    ∃ next, findOwner owner after = some next ∧ OwnerInsertion identity selected next := by
  induction changed generalizing selected with
  | here =>
      exact ⟨_, by simp only [findOwner, found, Option.map_some]; rfl, .caller .here⟩
  | live changed ih =>
      simp only [findOwner] at found ⊢
      split at found
      next hit =>
        cases Option.some.inj found
        exact ⟨_, by simp only [if_pos hit], .waiting changed⟩
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

theorem OwnerInsertion.caller_tail (changed : OwnerInsertion identity first second) :
    Insertion identity (first.front.append (.spent (owner := owner) first.tail))
      (second.front.append (.spent (owner := owner) second.tail)) := by
  cases changed with
  | caller inserted => exact inserted.suffix _
  | waiting inserted => exact (Insertion.spent inserted).prefix _

theorem OwnerInsertion.restored (changed : OwnerInsertion identity first second) :
    Insertion identity (first.saved.append (first.front.append (.spent (owner := owner) first.tail)))
      (second.saved.append (second.front.append (.spent (owner := owner) second.tail))) := by
  cases changed with
  | caller inserted => exact (inserted.suffix _).prefix _
  | waiting inserted => exact ((Insertion.spent inserted).prefix _).prefix _

theorem OwnerInsertion.abandoned (changed : OwnerInsertion identity first second) :
    Split identity first.saved (.running .close (first.front.append (.spent (owner := owner) first.tail)))
      second.saved (.running .close (second.front.append (.spent (owner := owner) second.tail))) := by
  cases changed with
  | caller inserted => exact .outside (.running (inserted.suffix _))
  | waiting inserted => exact .outside (.running ((Insertion.spent inserted).prefix _))

/-- Reuse lexical provider insertion while retaining the precise callback and
continuation return annotations in the recursive source judgments. -/
theorem local_transport
    (checked : Local outward actions phases world dependencies hints)
    {next : ReturnHints nextScope} (changed : Insertion identity hints next) :
    Local outward actions phases world dependencies next := by
  refine (Local.rec
    (motive_1 := fun phases world dependencies scope hints _ => ∀ {nextScope}
      (next : ReturnHints nextScope), Insertion identity hints next →
      Local outward actions phases world dependencies next)
    (motive_2 := fun phases world scope outside hints outsideHints initial finalMode _ =>
      ∀ {nextScope nextOutside} (next : ReturnHints nextScope) (nextOutsideHints : ReturnHints nextOutside),
      Split identity hints outsideHints next nextOutsideHints →
      Pending outward actions phases world next nextOutsideHints initial finalMode)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (t := checked)) next changed
  · intros; exact .pure
  · intros
    rename_i guard callbacks bounded ihCallbacks nextScope next changed
    cases guard with
    | builtin found =>
        obtain ⟨_, nextFound⟩ := changed.erases.builtin found
        apply Local.request (.builtin nextFound)
        · intro capturedScope tailScope saved waiting contract modes same found disposes
          cases Option.some.inj (nextFound.symm.trans found)
        · intro saved waiting contract modes found disposes
          cases Option.some.inj (nextFound.symm.trans found)
    | handler found permission row body =>
        obtain ⟨saved, waiting, cut⟩ := SourceDependencyNeutral.Lexical.Recursive.of_lookup _ found
        rcases changed.cut cut with nextFound | ⟨_, _, nextSaved, nextWaiting, nextCut, pieces⟩
        · apply Local.request (.builtin nextFound)
          · intro capturedScope tailScope saved waiting contract modes same found disposes
            cases Option.some.inj (nextFound.symm.trans found)
          · intro saved waiting contract modes found disposes
            cases Option.some.inj (nextFound.symm.trans found)
        · have sameHeld := by
            cases pieces with
            | inside inserted => exact inserted.erases.held
            | outside inserted => exact rfl
          apply Local.request (.handler nextCut.lookup (sameHeld ▸ permission) (sameHeld ▸ row) (sameHeld ▸ body))
          · intro actualSavedScope actualWaitingScope actualSaved actualWaiting contract modes same actual disposes
            cases Option.some.inj (nextCut.lookup.symm.trans actual)
            obtain ⟨rfl, rfl⟩ := nextCut.unique same
            apply ihCallbacks saved waiting _ _ cut.hints found disposes nextSaved (.running .close nextWaiting)
            cases pieces with
            | inside inserted => exact .inside inserted
            | outside inserted => exact .outside (.running inserted)
          · intro actualSaved actualWaiting contract modes actual disposes
            cases Option.some.inj (nextCut.lookup.symm.trans actual)
            cases pieces with
            | inside inserted =>
              have owners := inserted.erases.pending_owners (bounded _ _ _ _ found disposes)
              rw [inserted.erases.owners] at owners
              exact owners
            | outside inserted => exact bounded _ _ _ _ found disposes
  · intros
    rename_i located known permission available restored ih nextScope next changed
    obtain ⟨nextSelected, foundNext, related⟩ := changed.find_owner (find_owner_pieces located)
    have same := selected_hints foundNext
    have modes := (changed.return_mode .ordinary).trans
      (return_mode_heq (selected_cut foundNext).reconstruct same .ordinary)
    have transported := ih _ .nil (.inside related.restored)
    rw [modes] at transported
    exact (Local.resume (front := nextSelected.front) (captured := nextSelected.saved) (tail := nextSelected.tail)
      (selected_reconstructed_cut foundNext) known permission available transported).reindex_scope
        (selected_cut foundNext).reconstruct.symm same.symm
  · intros
    rename_i located known permission available unprotected abandoned waiting ihAbandoned ihWaiting nextScope next changed
    obtain ⟨nextSelected, foundNext, related⟩ := changed.find_owner (find_owner_pieces located)
    have same := selected_hints foundNext
    have modes := (changed.return_mode .ordinary).trans
      (return_mode_heq (selected_cut foundNext).reconstruct same .ordinary)
    have nextAbandoned := ihAbandoned _ _ related.abandoned
    have nextWaiting := ihWaiting _ .nil (.inside related.caller_tail)
    rw [modes] at nextWaiting
    have held : nextSelected.scopes.captured.held = false := by cases related <;> exact unprotected
    exact (Local.dispose (front := nextSelected.front) (captured := nextSelected.saved) (tail := nextSelected.tail)
      (selected_reconstructed_cut foundNext) known permission available held nextAbandoned nextWaiting).reindex_scope
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
    rename_i nextScope nextOutside next nextOutsideHints changed
    cases changed with
    | inside inserted => cases inserted; exact .cell .nil
    | outside inserted => exact .nil
  · intros
    rename_i code tail ihCode ihTail nextScope nextOutside next nextOutsideHints changed
    cases changed with
    | outside inserted =>
        exact .plain (ihCode _ (inserted.prefix _)) (ihTail _ _ (.outside inserted))
    | inside inserted => cases inserted with
      | here => exact .cell (.plain code tail)
      | plain inserted => exact .plain (ihCode _ (inserted.suffix _)) (ihTail _ _ (.inside inserted))
  · intros
    rename_i tail ih nextScope nextOutside next nextOutsideHints changed
    cases changed with
    | outside inserted =>
        exact .skipped (ih _ _ (.outside inserted))
    | inside inserted => cases inserted with
      | here => exact .cell (.skipped tail)
      | plain inserted => exact .skipped (ih _ _ (.inside inserted))
  · intros
    rename_i tail ih nextScope nextOutside next nextOutsideHints changed
    cases changed with
    | outside inserted =>
        exact .handler (ih _ _ (.outside inserted))
    | inside inserted => cases inserted with
      | here => exact .cell (.handler tail)
      | handler inserted => exact .handler (ih _ _ (.inside inserted))
  · intros
    rename_i tail ih nextScope nextOutside next nextOutsideHints changed
    cases changed with
    | outside inserted =>
        exact .cell (ih _ _ (.outside inserted))
    | inside inserted => cases inserted with
      | here => exact .cell (.cell tail)
      | cell inserted => exact .cell (ih _ _ (.inside inserted))
  · intros
    rename_i code tail ihCode ihTail nextScope nextOutside next nextOutsideHints changed
    cases changed with
    | outside inserted =>
        exact .cleanup (ihCode _ (.running (inserted.prefix _))) (ihTail _ _ (.outside inserted))
    | inside inserted => cases inserted with
      | here => exact .cell (.cleanup code tail)
      | cleanup inserted => exact .cleanup (ihCode _ (.running (inserted.suffix _))) (ihTail _ _ (.inside inserted))
  · intros
    rename_i tail ih nextScope nextOutside next nextOutsideHints changed
    cases changed with
    | outside inserted =>
        exact .normal (ih _ _ (.outside inserted))
    | inside inserted => cases inserted with
      | here => exact .cell (.normal tail)
      | running inserted => exact .normal (ih _ _ (.inside inserted))
  · intros
    rename_i tail ih nextScope nextOutside next nextOutsideHints changed
    cases changed with
    | outside inserted =>
        exact .unwinding (ih _ _ (.outside inserted))
    | inside inserted => cases inserted with
      | here => exact .cell (.unwinding tail)
      | running inserted => exact .unwinding (ih _ _ (.inside inserted))
  · intros
    rename_i tail ih nextScope nextOutside next nextOutsideHints changed
    cases changed with
    | outside inserted =>
        exact .closing (ih _ _ (.outside inserted))
    | inside inserted => cases inserted with
      | here => exact .cell (.closing tail)
      | running inserted => exact .closing (ih _ _ (.inside inserted))
  · intros
    rename_i tail ih nextScope nextOutside next nextOutsideHints changed
    cases changed with
    | outside inserted =>
        exact .retiring (ih _ _ (.outside inserted))
    | inside inserted => cases inserted with
      | here => exact .cell (.retiring tail)
      | running inserted => exact .retiring (ih _ _ (.inside inserted))
  · intros
    rename_i code tail ihCode ihTail nextScope nextOutside next nextOutsideHints changed
    cases changed with
    | outside inserted =>
        exact .live (ihCode _ _ (.outside (inserted.prefix _))) (ihTail _ _ (.outside inserted))
    | inside inserted => cases inserted with
      | here => exact .cell (.live code tail)
      | live inserted => exact .live (ihCode _ _ (.outside (inserted.suffix _))) (ihTail _ _ (.inside inserted))
  · intros
    rename_i code tail ihCode ihTail nextScope nextOutside next nextOutsideHints changed
    cases changed with
    | outside inserted =>
        exact .opening (ihCode _ _ (.outside (.running (inserted.prefix _)))) (ihTail _ _ (.outside inserted))
    | inside inserted => cases inserted with
      | here => exact .cell (.opening code tail)
      | live inserted => exact .opening (ihCode _ _ (.outside (.running (inserted.suffix _)))) (ihTail _ _ (.inside inserted))
  · intros
    rename_i tail ih nextScope nextOutside next nextOutsideHints changed
    cases changed with
    | outside inserted =>
        exact .spent (ih _ _ (.outside inserted))
    | inside inserted => cases inserted with
      | here => exact .cell (.spent tail)
      | spent inserted => exact .spent (ih _ _ (.inside inserted))

end Ash.OneShot.SourceDependencyProviders.Lexical.Recursive
#print axioms Ash.OneShot.SourceDependencyProviders.Lexical.Recursive.local_transport
