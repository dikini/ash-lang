import SourceScheduledAdaptationCompilation

/-! Static insertion of an actual effectful plain suffix. The finite operation
interface is checked at its receiving position; no future Pending is supplied. -/
namespace Ash.OneShot.SourcePlainSuffixTransport
open ScopedExpressions ProtectionContracts
open SourceDependencyCapture (Scope OwnerCut select)
open SourceDependencyChecks.Lexical (ReturnHints Capture)
open SourceDependencyChecks.Lexical.ReturnHints.Recursive (Local Pending callbackBoundary)
open SourceDependencyNeutral.Lexical.Recursive (Cut Selection findOwner selected_cut selected_reconstructed_cut
  selected_hints find_owner_pieces return_mode_heq)
open OwnerPhaseTransitions (spend)
open LexicalUnwind (UseMode)

open SourceContextualHints (Requirement checkRequirements checkCapability)
open SourceDependencyAnnotations (Dependencies)
open SourcePlanSignatures (Signature)
open SourceRequestFootprints (Footprint)
open SourceScheduledAdaptationCompilation.Lexical.Recursive (compile_footprint)

theorem footprintWithin {checking : Signature dependencies}
    (footprint : Footprint checking required) : SourceDependencyOwners.Within world owned dependencies := by
  induction footprint generalizing world with
  | pure => exact .pure
  | request => exact .request
  | handledRequest => exact .handler (.sequence .pure .request)
  | sequence first second ihFirst ihSecond => exact .sequence ihFirst ihSecond
  | choice first second ihFirst ihSecond => exact .choice ihFirst ihSecond
  | handler body internal ih => exact .handler ih
  | cleanup callback body ihCallback ihBody => exact .cleanup ihCallback ihBody
  | resource body ih => exact .resource (fun identity _ => ih identity)
  | weaken body included ih => exact ih

inductive Supplied (suffixCode : Dependencies) (required : List Requirement) (outside : Scope) : {first second : Scope} → ReturnHints first → ReturnHints second → Prop where
  | here {before : ReturnHints scope}
      (checked : checkRequirements (scope.append outside) required = true) :
      Supplied suffixCode required outside before (.plain (dependencies := suffixCode) before)
  | plain : Supplied suffixCode required outside before after →
      Supplied suffixCode required outside (.plain (dependencies := dependencies) before) (.plain (dependencies := dependencies) after)
  | handler : Supplied suffixCode required outside before after →
      Supplied suffixCode required outside (.handler (effect := effect) (table := table) (families := families) before)
        (.handler (effect := effect) (table := table) (families := families) after)
  | cell : Supplied suffixCode required outside before after →
      Supplied suffixCode required outside (.cell (identity := other) before) (.cell (identity := other) after)
  | cleanup : Supplied suffixCode required outside before after →
      Supplied suffixCode required outside (.cleanup (needs := otherNeeds) (callback := otherCallback) before)
        (.cleanup (needs := otherNeeds) (callback := otherCallback) after)
  | running : Supplied suffixCode required outside before after → Supplied suffixCode required outside (.running kind before) (.running kind after)
  | live : Supplied suffixCode required outside before after →
      Supplied suffixCode required outside (.live (owner := owner) saved before) (.live (owner := owner) saved after)
  | spent : Supplied suffixCode required outside before after →
      Supplied suffixCode required outside (.spent (owner := owner) before) (.spent (owner := owner) after)

theorem Supplied.prefix (front : ReturnHints scope) (changed : Supplied suffixCode required outside before after) :
    Supplied suffixCode required outside (front.append before) (front.append after) := by
  induction front with
  | nil => exact changed
  | plain rest ih => exact .plain ih
  | handler rest ih => exact .handler ih
  | cell rest ih => exact .cell ih
  | cleanup rest ih => exact .cleanup ih
  | running kind rest ih => exact .running ih
  | live saved rest ihSaved ihRest => exact .live ihRest
  | spent rest ih => exact .spent ih

theorem Supplied.suffix (tail : ReturnHints scope) (changed : Supplied suffixCode required (scope.append outside) before after) :
    Supplied suffixCode required outside (before.append tail) (after.append tail) := by
  induction changed with
  | here checked => exact .here (by simpa only [SourceDependencyChecks.scope_append_assoc] using checked)
  | plain changed ih => exact .plain ih
  | handler changed ih => exact .handler ih
  | cell changed ih => exact .cell ih
  | cleanup changed ih => exact .cleanup ih
  | running changed ih => exact .running ih
  | live changed ih => exact .live ih
  | spent changed ih => exact .spent ih

theorem Supplied.receiver
    (changed : Supplied suffixCode required first before after)
    (same : ∀ effect operation, checkCapability first effect operation = checkCapability second effect operation) :
    Supplied suffixCode required second before after := by
  induction changed with
  | here checked =>
      apply Supplied.here
      apply List.all_eq_true.mpr
      intro request member
      have accepted := List.all_eq_true.mp checked request member
      simpa only [SourceHandlerRequirements.capability_append, ← same] using accepted
  | plain next ih => exact .plain ih
  | handler next ih => exact .handler ih
  | cell next ih => exact .cell ih
  | cleanup next ih => exact .cleanup ih
  | running next ih => exact .running ih
  | live next ih => exact .live ih
  | spent next ih => exact .spent ih

theorem Supplied.running_receiver (changed : Supplied suffixCode required outside before after) :
    Supplied suffixCode required (.running outside) before after :=
  changed.receiver (fun _ _ => (SourceHandlerRequirements.capability_prepend rfl).symm)

theorem Supplied.held {before : ReturnHints first} {after : ReturnHints second}
    (changed : Supplied suffixCode required outside before after) : first.held = second.held := by
  induction changed <;> simp_all [Scope.held]

theorem Supplied.owners {before : ReturnHints first} {after : ReturnHints second}
    (changed : Supplied suffixCode required outside before after) :
    SourceDependencyOwners.owners second = SourceDependencyOwners.owners first := by
  induction changed <;> simp_all [SourceDependencyOwners.owners]

theorem Supplied.pending_owners {checking : Signature suffixCode}
    (footprint : Footprint checking required) {before : ReturnHints first} {after : ReturnHints second}
    (changed : Supplied suffixCode required outside before after)
    (checked : SourceDependencyOwners.PendingWithin world owned first) :
    SourceDependencyOwners.PendingWithin world owned second := by
  induction changed with
  | here supplied => exact .plain (footprintWithin footprint) checked
  | plain changed ih => cases checked with | plain code tail => exact .plain code (ih tail)
  | handler changed ih => cases checked with | handler tail => exact .handler (ih tail)
  | cell changed ih => cases checked with | cell tail => exact .cell (ih tail)
  | cleanup changed ih => cases checked with | cleanup tail => exact .cleanup (ih tail)
  | running changed ih => cases checked with | running tail => exact .running (ih tail)
  | live changed ih => cases checked with | live saved tail => exact .live saved (ih tail)
  | spent changed ih => cases checked with | spent tail => exact .spent (ih tail)

private theorem builtin_prepend
    (ih : select effect operation first = some (.builtin identity) →
      select effect operation second = some (.builtin identity))
    (found : (select effect operation first).map (SourceDependencyCapture.Selection.prepend layer) = some (.builtin identity)) :
    (select effect operation second).map (SourceDependencyCapture.Selection.prepend layer) = some (.builtin identity) := by
  obtain ⟨selected, found, same⟩ := Option.map_eq_some_iff.mp found
  cases selected with
  | builtin id =>
      cases same
      simp only [ih found, Option.map_some, SourceDependencyCapture.Selection.prepend]
  | handler saved waiting contract modes => cases same

theorem Supplied.builtin {before : ReturnHints first} {after : ReturnHints second}
    (changed : Supplied suffixCode required outside before after)
    (found : select effect operation first = some (.builtin identity)) :
    select effect operation second = some (.builtin identity) := by
  induction changed with
  | here checked => simp only [select, found, Option.map_some, SourceDependencyCapture.Selection.prepend]
  | handler changed ih =>
      simp only [select] at found ⊢
      split at found
      next same => split at found <;> cases found
      next different => simpa only [if_neg different] using builtin_prepend ih found
  | cell changed ih =>
      simp only [select] at found ⊢
      split at found
      next same => simpa only [if_pos same] using found
      next different => simpa only [if_neg different] using builtin_prepend ih found
  | plain changed ih | cleanup changed ih | running changed ih | live changed ih | spent changed ih =>
      exact builtin_prepend ih found

theorem Supplied.return_mode (changed : Supplied suffixCode required outside before after) (mode : UseMode) :
    before.returnMode mode = after.returnMode mode := by
  induction changed generalizing mode <;> simp_all [ReturnHints.returnMode]

inductive Split (suffixCode : Dependencies) (required : List Requirement) : {first outside second nextOutside : Scope} →
    ReturnHints first → ReturnHints outside → ReturnHints second → ReturnHints nextOutside → Prop where
  | inside {tail : ReturnHints tailScope}
      (changed : Supplied suffixCode required tailScope before after) : Split suffixCode required before tail after tail
  | outside (changed : Supplied suffixCode required .nil before after) : Split suffixCode required saved before saved after

theorem Split.prepend (changed : Split suffixCode required saved waiting nextSaved nextWaiting)
    (layer : Scope → Scope) (lift : ∀ {scope}, ReturnHints scope → ReturnHints (layer scope))
    (preserves : ∀ {outside first second} {before : ReturnHints first} {after : ReturnHints second},
      Supplied suffixCode required outside before after → Supplied suffixCode required outside (lift before) (lift after)) :
    Split suffixCode required (lift saved) waiting (lift nextSaved) nextWaiting := by
  cases changed with
  | inside next => exact .inside (preserves next)
  | outside next => exact .outside next

theorem Supplied.cut {before : ReturnHints first} {after : ReturnHints second}
    {saved : ReturnHints captured} {waiting : ReturnHints tail}
    (changed : Supplied suffixCode required .nil before after)
    (cut : SourceDependencyNeutral.Lexical.Recursive.Cut effect operation contract modes before saved waiting) :
    ∃ captured tail, ∃ nextSaved : ReturnHints captured, ∃ nextWaiting : ReturnHints tail,
      SourceDependencyNeutral.Lexical.Recursive.Cut effect operation contract modes after nextSaved nextWaiting ∧
      Split suffixCode required saved waiting nextSaved nextWaiting := by
  induction changed generalizing captured tail with
  | here checked =>
      exact ⟨_, _, _, _, .plain cut, .inside (.here
        (by simpa only [SourceDependencyProjection.scope_append_nil, cut.reconstruct_scope] using checked))⟩
  | handler changed ih => cases cut with
    | hit known declared => exact ⟨_, _, _, _, .hit known declared, .outside changed⟩
    | handler different next =>
        obtain ⟨_, _, nextSaved, nextWaiting, nextCut, pieces⟩ := ih next
        exact ⟨_, _, _, _, .handler different nextCut,
          pieces.prepend (fun scope => .handler _ _ _ scope) (fun hints => .handler hints) (fun changed => .handler changed)⟩
  | cell changed ih => cases cut with
    | cell different next =>
        obtain ⟨_, _, nextSaved, nextWaiting, nextCut, pieces⟩ := ih next
        exact ⟨_, _, _, _, .cell different nextCut,
          pieces.prepend (fun scope => .cell _ scope) (fun hints => .cell hints) (fun changed => .cell changed)⟩
  | plain changed ih => cases cut with
    | plain next =>
        obtain ⟨_, _, nextSaved, nextWaiting, nextCut, pieces⟩ := ih next
        exact ⟨_, _, _, _, .plain nextCut,
          pieces.prepend (fun scope => .plain _ scope) (fun hints => .plain hints) (fun changed => .plain changed)⟩
  | cleanup changed ih => cases cut with
    | cleanup next =>
        obtain ⟨_, _, nextSaved, nextWaiting, nextCut, pieces⟩ := ih next
        exact ⟨_, _, _, _, .cleanup nextCut,
          pieces.prepend (fun scope => .cleanup _ _ scope) (fun hints => .cleanup hints) (fun changed => .cleanup changed)⟩
  | running changed ih => cases cut with
    | running next =>
        obtain ⟨_, _, nextSaved, nextWaiting, nextCut, pieces⟩ := ih next
        exact ⟨_, _, _, _, .running nextCut,
          pieces.prepend (fun scope => .running scope) (fun hints => .running _ hints) (fun changed => .running changed)⟩
  | live changed ih => cases cut with
    | live next =>
        obtain ⟨_, _, nextSaved, nextWaiting, nextCut, pieces⟩ := ih next
        exact ⟨_, _, _, _, .live nextCut,
          pieces.prepend (fun scope => .live _ _ scope) (fun hints => .live _ hints) (fun changed => .live changed)⟩
  | spent changed ih => cases cut with
    | spent next =>
        obtain ⟨_, _, nextSaved, nextWaiting, nextCut, pieces⟩ := ih next
        exact ⟨_, _, _, _, .spent nextCut,
          pieces.prepend (fun scope => .spent _ scope) (fun hints => .spent hints) (fun changed => .spent changed)⟩

theorem Split.append (changed : Split suffixCode required first waiting second nextOutside) :
    Supplied suffixCode required .nil (first.append waiting) (second.append nextOutside) := by
  cases changed with
  | inside inserted => exact Supplied.suffix _ (by simpa only [SourceDependencyProjection.scope_append_nil] using inserted)
  | outside inserted => exact inserted.prefix _

inductive OwnerInsertion (suffixCode : Dependencies) (required : List Requirement) (owner : Nat) : Selection → Selection → Prop where
  | caller {front : ReturnHints first} {nextFront : ReturnHints second} {saved : ReturnHints captured} {tail : ReturnHints waiting}
      (changed : Supplied suffixCode required (.live owner captured waiting) front nextFront) :
      OwnerInsertion suffixCode required owner ⟨⟨first, captured, waiting⟩, front, saved, tail⟩
        ⟨⟨second, captured, waiting⟩, nextFront, saved, tail⟩
  | waiting {front : ReturnHints caller} {saved : ReturnHints captured} {tail : ReturnHints first} {nextTail : ReturnHints second}
      (changed : Supplied suffixCode required .nil tail nextTail) :
      OwnerInsertion suffixCode required owner ⟨⟨caller, captured, first⟩, front, saved, tail⟩
        ⟨⟨caller, captured, second⟩, front, saved, nextTail⟩

theorem OwnerInsertion.prepend (changed : OwnerInsertion suffixCode required owner first second)
    (layer : Scope → Scope) (lift : ∀ {scope}, ReturnHints scope → ReturnHints (layer scope))
    (preserves : ∀ {outside a b} {before : ReturnHints a} {after : ReturnHints b},
      Supplied suffixCode required outside before after → Supplied suffixCode required outside (lift before) (lift after)) :
    OwnerInsertion suffixCode required owner (first.prepend layer lift) (second.prepend layer lift) := by
  cases changed with
  | caller inserted => exact .caller (preserves inserted)
  | waiting inserted => exact .waiting inserted

theorem Supplied.find_owner (changed : Supplied suffixCode required .nil before after)
    (found : findOwner owner before = some selected) :
    ∃ next, findOwner owner after = some next ∧ OwnerInsertion suffixCode required owner selected next := by
  induction changed generalizing selected with
  | here checked =>
      refine ⟨_, by simp only [findOwner, found, Option.map_some]; rfl, ?_⟩
      cases selected with
      | mk scopes front saved tail => cases scopes with
        | mk caller captured waiting =>
          apply OwnerInsertion.caller
          apply Supplied.here
          simpa only [SourceDependencyProjection.scope_append_nil, (selected_cut found).reconstruct] using checked
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

theorem OwnerInsertion.caller_tail (changed : OwnerInsertion suffixCode required owner first second) :
    Supplied suffixCode required .nil (first.front.append (.spent (owner := owner) first.tail))
      (second.front.append (.spent (owner := owner) second.tail)) := by
  cases changed with
  | caller inserted =>
      apply Supplied.suffix
      simpa only [SourceDependencyProjection.scope_append_nil] using inserted.receiver (second := .spent owner _) (fun _ _ => (SourceHandlerRequirements.capability_prepend rfl).trans
        (SourceHandlerRequirements.capability_prepend rfl).symm)
  | waiting inserted => exact (Supplied.spent inserted).prefix _

theorem OwnerInsertion.restored (changed : OwnerInsertion suffixCode required owner first second) :
    Supplied suffixCode required .nil (first.saved.append (first.front.append (.spent (owner := owner) first.tail)))
      (second.saved.append (second.front.append (.spent (owner := owner) second.tail))) := by
  cases changed with
  | caller inserted =>
      apply Supplied.prefix
      apply Supplied.suffix
      simpa only [SourceDependencyProjection.scope_append_nil] using inserted.receiver (second := .spent owner _) (fun _ _ => (SourceHandlerRequirements.capability_prepend rfl).trans
        (SourceHandlerRequirements.capability_prepend rfl).symm)
  | waiting inserted => exact ((Supplied.spent inserted).prefix _).prefix _

theorem OwnerInsertion.abandoned (changed : OwnerInsertion suffixCode required owner first second) :
    Split suffixCode required first.saved (.running .close (first.front.append (.spent (owner := owner) first.tail)))
      second.saved (.running .close (second.front.append (.spent (owner := owner) second.tail))) := by
  cases changed with
  | caller inserted =>
      apply Split.outside
      apply Supplied.running
      apply Supplied.suffix
      simpa only [SourceDependencyProjection.scope_append_nil] using inserted.receiver (second := .spent owner _) (fun _ _ => (SourceHandlerRequirements.capability_prepend rfl).trans
        (SourceHandlerRequirements.capability_prepend rfl).symm)
  | waiting inserted => exact .outside (.running ((Supplied.spent inserted).prefix _))

theorem Supplied.close_suffix (tail : ReturnHints scope)
    (changed : Supplied suffixCode required scope before after) :
    Supplied suffixCode required .nil (before.append tail) (after.append tail) :=
  Supplied.suffix tail (by simpa only [SourceDependencyProjection.scope_append_nil] using changed)

theorem suffix_checked {checking : Signature suffixCode} {hints : ReturnHints scope}
    (footprint : Footprint checking required) (supplied : checkRequirements scope required = true) :
    Local outward actions phases world suffixCode hints :=
  compile_footprint footprint supplied

theorem pending_suffix {checking : Signature suffixCode}
    (footprint : Footprint checking required) (supplied : checkRequirements (scope.append outsideScope) required = true)
    {hints : ReturnHints scope} {outside : ReturnHints outsideScope}
    (retained : Pending outward actions phases world hints outside mode finalMode) :
    Pending outward actions phases world (.plain (dependencies := suffixCode) hints) outside mode finalMode := by
  cases mode with
  | ordinary => exact .plain (compile_footprint footprint supplied) retained
  | unwind => exact .skipped retained

/-- Check the inserted plain suffix from its static footprint at the exact
receiving position. Mutual induction transports existing code and retained
segments, including resume, discard, and dormant captures. -/
theorem local_transport {checking : Signature suffixCode}
    (footprint : Footprint checking required)
    (checked : Local outward actions phases world dependencies hints)
    {next : ReturnHints nextScope} (changed : Supplied suffixCode required .nil hints next) :
    Local outward actions phases world dependencies next := by
  refine (Local.rec
    (motive_1 := fun phases world dependencies scope hints _ => ∀ {nextScope}
      (next : ReturnHints nextScope), Supplied suffixCode required .nil hints next →
      Local outward actions phases world dependencies next)
    (motive_2 := fun phases world scope outside hints outsideHints initial finalMode _ =>
      ∀ {nextScope nextOutside} (next : ReturnHints nextScope) (nextOutsideHints : ReturnHints nextOutside),
      Split suffixCode required hints outsideHints next nextOutsideHints →
      Pending outward actions phases world next nextOutsideHints initial finalMode)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (t := checked)) next changed
  · intros; exact .pure
  · intros
    rename_i guard callbacks bounded ihCallbacks nextScope next changed
    cases guard with
    | builtin found =>
        have nextFound := changed.builtin found
        apply Local.request (.builtin nextFound)
        · intro capturedScope tailScope saved waiting contract modes same found disposes
          cases Option.some.inj (nextFound.symm.trans found)
        · intro saved waiting contract modes found disposes
          cases Option.some.inj (nextFound.symm.trans found)
    | handler found permission row body =>
        obtain ⟨saved, waiting, cut⟩ := SourceDependencyNeutral.Lexical.Recursive.of_lookup _ found
        obtain ⟨_, _, nextSaved, nextWaiting, nextCut, pieces⟩ := changed.cut cut
        have sameHeld := by
          cases pieces with
          | inside inserted => exact inserted.held
          | outside inserted => exact rfl
        apply Local.request (.handler nextCut.lookup (sameHeld ▸ permission) (sameHeld ▸ row) (sameHeld ▸ body))
        · intro actualSavedScope actualWaitingScope actualSaved actualWaiting contract modes same actual disposes
          cases Option.some.inj (nextCut.lookup.symm.trans actual)
          obtain ⟨rfl, rfl⟩ := nextCut.unique same
          apply ihCallbacks saved waiting _ _ cut.hints found disposes nextSaved (.running .close nextWaiting)
          cases pieces with
          | inside inserted => exact .inside inserted.running_receiver
          | outside inserted => exact .outside (.running inserted)
        · intro actualSaved actualWaiting contract modes actual disposes
          cases Option.some.inj (nextCut.lookup.symm.trans actual)
          cases pieces with
          | inside inserted =>
            have owners := inserted.pending_owners footprint (bounded _ _ _ _ found disposes)
            simpa only [inserted.owners] using owners
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
    | inside inserted => cases inserted with
      | here supplied => exact pending_suffix footprint supplied .nil
    | outside inserted => exact .nil
  · intros
    rename_i code tail ihCode ihTail nextScope nextOutside next nextOutsideHints changed
    cases changed with
    | outside inserted =>
        exact .plain (ihCode _ (inserted.prefix _)) (ihTail _ _ (.outside inserted))
    | inside inserted => cases inserted with
      | here supplied => exact pending_suffix footprint supplied (.plain code tail)
      | plain inserted => exact .plain (ihCode _ (inserted.close_suffix _)) (ihTail _ _ (.inside inserted))
  · intros
    rename_i tail ih nextScope nextOutside next nextOutsideHints changed
    cases changed with
    | outside inserted =>
        exact .skipped (ih _ _ (.outside inserted))
    | inside inserted => cases inserted with
      | here supplied => exact pending_suffix footprint supplied (.skipped tail)
      | plain inserted => exact .skipped (ih _ _ (.inside inserted))
  · intros
    rename_i tail ih nextScope nextOutside next nextOutsideHints changed
    cases changed with
    | outside inserted =>
        exact .handler (ih _ _ (.outside inserted))
    | inside inserted => cases inserted with
      | here supplied => exact pending_suffix footprint supplied (.handler tail)
      | handler inserted => exact .handler (ih _ _ (.inside inserted))
  · intros
    rename_i tail ih nextScope nextOutside next nextOutsideHints changed
    cases changed with
    | outside inserted =>
        exact .cell (ih _ _ (.outside inserted))
    | inside inserted => cases inserted with
      | here supplied => exact pending_suffix footprint supplied (.cell tail)
      | cell inserted => exact .cell (ih _ _ (.inside inserted))
  · intros
    rename_i code tail ihCode ihTail nextScope nextOutside next nextOutsideHints changed
    cases changed with
    | outside inserted =>
        exact .cleanup (ihCode _ (.running (inserted.prefix _))) (ihTail _ _ (.outside inserted))
    | inside inserted => cases inserted with
      | here supplied => exact pending_suffix footprint supplied (.cleanup code tail)
      | cleanup inserted => exact .cleanup (ihCode _ (.running (inserted.close_suffix _))) (ihTail _ _ (.inside inserted))
  · intros
    rename_i tail ih nextScope nextOutside next nextOutsideHints changed
    cases changed with
    | outside inserted =>
        exact .normal (ih _ _ (.outside inserted))
    | inside inserted => cases inserted with
      | here supplied => exact pending_suffix footprint supplied (.normal tail)
      | running inserted => exact .normal (ih _ _ (.inside inserted))
  · intros
    rename_i tail ih nextScope nextOutside next nextOutsideHints changed
    cases changed with
    | outside inserted =>
        exact .unwinding (ih _ _ (.outside inserted))
    | inside inserted => cases inserted with
      | here supplied => exact pending_suffix footprint supplied (.unwinding tail)
      | running inserted => exact .unwinding (ih _ _ (.inside inserted))
  · intros
    rename_i tail ih nextScope nextOutside next nextOutsideHints changed
    cases changed with
    | outside inserted =>
        exact .closing (ih _ _ (.outside inserted))
    | inside inserted => cases inserted with
      | here supplied => exact pending_suffix footprint supplied (.closing tail)
      | running inserted => exact .closing (ih _ _ (.inside inserted))
  · intros
    rename_i tail ih nextScope nextOutside next nextOutsideHints changed
    cases changed with
    | outside inserted =>
        exact .retiring (ih _ _ (.outside inserted))
    | inside inserted => cases inserted with
      | here supplied => exact pending_suffix footprint supplied (.retiring tail)
      | running inserted => exact .retiring (ih _ _ (.inside inserted))
  · intros
    rename_i code tail ihCode ihTail nextScope nextOutside next nextOutsideHints changed
    cases changed with
    | outside inserted =>
        exact .live (ihCode _ _ (.outside (inserted.prefix _))) (ihTail _ _ (.outside inserted))
    | inside inserted => cases inserted with
      | here supplied => exact pending_suffix footprint supplied (.live code tail)
      | live inserted => exact .live (ihCode _ _ (.outside (inserted.close_suffix _))) (ihTail _ _ (.inside inserted))
  · intros
    rename_i code tail ihCode ihTail nextScope nextOutside next nextOutsideHints changed
    cases changed with
    | outside inserted =>
        exact .opening (ihCode _ _ (.outside (.running (inserted.prefix _)))) (ihTail _ _ (.outside inserted))
    | inside inserted => cases inserted with
      | here supplied => exact pending_suffix footprint supplied (.opening code tail)
      | live inserted => exact .opening (ihCode _ _ (.outside (.running (inserted.close_suffix _)))) (ihTail _ _ (.inside inserted))
  · intros
    rename_i tail ih nextScope nextOutside next nextOutsideHints changed
    cases changed with
    | outside inserted =>
        exact .spent (ih _ _ (.outside inserted))
    | inside inserted => cases inserted with
      | here supplied => exact pending_suffix footprint supplied (.spent tail)
      | spent inserted => exact .spent (ih _ _ (.inside inserted))


theorem plain_suffix_admission {checking : Signature suffixCode} {hints : ReturnHints scope}
    (footprint : Footprint checking required)
    (supplied : checkRequirements scope required = true)
    (body : Local outward actions phases world dependencies hints) :
    Local outward actions phases world (.sequence dependencies suffixCode) hints :=
  .sequence (local_transport footprint body (.here
    (by simpa only [SourceDependencyProjection.scope_append_nil] using supplied)))
    (compile_footprint footprint supplied)

end Ash.OneShot.SourcePlainSuffixTransport
#print axioms Ash.OneShot.SourcePlainSuffixTransport.plain_suffix_admission
