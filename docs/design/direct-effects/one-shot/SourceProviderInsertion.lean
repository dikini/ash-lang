import SourcePlannedCuts
import SourceHandlerRequirements
import SourceInterpretationInsertion

/-! Adding an active builtin provider preserves closing-route agreement.
The selected interpretation may change to that builtin. This is a structural
checking theorem, not an assertion that handler selection is unchanged or
that runtime resource freshness and ownership may be omitted. -/
namespace Ash.OneShot.SourceProviderInsertion
open ScopedExpressions
open ProtectionContracts (ClauseContract)
open SourceDependencyCapture (Scope)
open SourceContextualHints (Hints)
open SourceResourceRoutes (Context Entry Route)
open SourceRecursiveRoutes (Shape Closing)

/-- One retained cell is inserted into an interpretation projection. -/
inductive ContextInsertion (identity : Nat) : Context → Context → Prop where
  | here : ContextInsertion identity before (.cell identity :: before)
  | next : ContextInsertion identity before after →
      ContextInsertion identity (entry :: before) (entry :: after)

theorem ContextInsertion.prefix (front : Context) (changed : ContextInsertion identity before after) :
    ContextInsertion identity (front ++ before) (front ++ after) := by
  induction front with
  | nil => exact changed
  | cons entry rest ih => exact .next ih

theorem ContextInsertion.suffix (changed : ContextInsertion identity before after) (tail : Context) :
    ContextInsertion identity (before ++ tail) (after ++ tail) := by
  induction changed with
  | here => exact .here
  | next changed ih => exact .next ih

def targetAfter (identity : Nat) (effect : Instance) (target : Option Nat) : Option Nat :=
  if effect = .cell identity then some identity else target

/-- A matching inserted provider may replace an exported route. Every other
request retains its previous route target. -/
theorem ContextInsertion.route (changed : ContextInsertion identity before after)
    (route : Route outward before effect target) :
    Route outward after effect (targetAfter identity effect target) := by
  induction changed generalizing target with
  | here =>
      by_cases same : effect = .cell identity
      · simpa only [targetAfter, if_pos same] using (Route.cell (rest := _) same : Route outward (.cell identity :: _) effect (some identity))
      · simpa only [targetAfter, if_neg same] using Route.cellMiss same route
  | next changed ih => cases route with
    | cell same =>
        rename_i original
        by_cases hit : effect = .cell identity
        · have equal : original = identity := Instance.cell.inj (same.symm.trans hit)
          cases equal
          simpa only [targetAfter, if_pos hit] using (Route.cell (rest := _) hit : Route outward (.cell identity :: _) effect (some identity))
        · simpa only [targetAfter, if_neg hit] using (Route.cell (rest := _) same : Route outward (.cell original :: _) effect (some original))
    | cellMiss different next => exact .cellMiss different (ih next)
    | handler different next => exact .handler different (ih next)
    | cleanup next => exact .cleanup (ih next)

/-- Insertions in the two contexts use the same target transformation. Their
positions need not be equal; previously agreeing routes continue to agree. -/
theorem route_agreement (original : ContextInsertion identity before nextBefore)
    (surviving : ContextInsertion identity after nextAfter)
    (routes : ∃ target, Route outward before effect target ∧ Route outward after effect target) :
    ∃ target, Route outward nextBefore effect target ∧ Route outward nextAfter effect target := by
  obtain ⟨target, first, second⟩ := routes
  exact ⟨_, original.route first, surviving.route second⟩

/-- Reuse the same callback structure under expanded original and closing
contexts. Both sides retain the newly inserted builtin. -/
theorem closing_contexts (checked : Closing outward shape before after)
    (original : ContextInsertion identity before nextBefore)
    (surviving : ContextInsertion identity after nextAfter) : Closing outward shape nextBefore nextAfter := by
  induction checked generalizing nextBefore nextAfter with
  | nil => exact .nil
  | plain tail ih => exact .plain (ih original surviving)
  | handler tail ih => exact .handler (ih original surviving)
  | cell tail ih => exact .cell (ih original surviving)
  | spent tail ih => exact .spent (ih original surviving)
  | cleanup routes tail ih =>
      exact .cleanup (fun effect member => route_agreement (original.prefix _) (surviving.prefix _) (routes effect member))
        (ih original surviving)
  | live inside outside ihInside ihOutside =>
      exact .live (ihInside (original.prefix _) (surviving.prefix _)) (ihOutside original surviving)

/-- Only the active spine gains a provider. Dormant captured code and all
existing frame annotations remain exactly the same. -/
inductive Insertion (identity : Nat) : {first second : Scope} → Hints first → Hints second → Prop where
  | here : Insertion identity before (.cell (identity := identity) before)
  | plain : Insertion identity before after →
      Insertion identity (.plain (dependencies := dependencies) before) (.plain (dependencies := dependencies) after)
  | handler : Insertion identity before after →
      Insertion identity (.handler (effect := effect) (table := table) (families := families) required before)
        (.handler (effect := effect) (table := table) (families := families) required after)
  | cell : Insertion identity before after →
      Insertion identity (.cell (identity := other) before) (.cell (identity := other) after)
  | cleanup : Insertion identity before after →
      Insertion identity (.cleanup (needs := needs) (callback := callback) before)
        (.cleanup (needs := needs) (callback := callback) after)
  | running : Insertion identity before after → Insertion identity (.running before) (.running after)
  | live : Insertion identity before after →
      Insertion identity (.live (owner := owner) saved before) (.live (owner := owner) saved after)
  | spent : Insertion identity before after →
      Insertion identity (.spent (owner := owner) before) (.spent (owner := owner) after)

theorem Insertion.prefix (front : Hints scope) (changed : Insertion identity before after) :
    Insertion identity (front.append before) (front.append after) := by
  induction front with
  | nil => exact changed
  | plain rest ih => exact .plain ih
  | handler required rest ih => exact .handler ih
  | cell rest ih => exact .cell ih
  | cleanup rest ih => exact .cleanup ih
  | running rest ih => exact .running ih
  | live saved rest ihSaved ihRest => exact .live ihRest
  | spent rest ih => exact .spent ih

theorem Insertion.suffix (changed : Insertion identity before after) (tail : Hints scope) :
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

/-- Reuse the shared owner transport without changing the provider relation
used by operation selection and closing-route proofs. -/
theorem Insertion.shared (changed : Insertion identity before after) :
    SourceInterpretationInsertion.Insertion (.cell identity) before after := by
  induction changed with
  | here => exact .here
  | plain changed ih => exact .plain ih
  | handler changed ih => exact .handler ih
  | cell changed ih => exact .cell ih
  | cleanup changed ih => exact .cleanup ih
  | running changed ih => exact .running ih
  | live changed ih => exact .live ih
  | spent changed ih => exact .spent ih

theorem Insertion.of_shared (changed : SourceInterpretationInsertion.Insertion (.cell identity) before after) :
    Insertion identity before after := by
  induction changed with
  | here => exact .here
  | plain changed ih => exact .plain ih
  | handler changed ih => exact .handler ih
  | cell changed ih => exact .cell ih
  | cleanup changed ih => exact .cleanup ih
  | running changed ih => exact .running ih
  | live changed ih => exact .live ih
  | spent changed ih => exact .spent ih

theorem Insertion.held {before : Hints first} {after : Hints second} (changed : Insertion identity before after) :
    first.held = second.held := by
  induction changed <;> simp_all [Scope.held]

theorem Insertion.normal {before : Hints first} {after : Hints second} (changed : Insertion identity before after) :
    ContextInsertion identity first.shape.normal second.shape.normal := by
  induction changed with
  | here => exact .here
  | plain changed ih | cleanup changed ih | running changed ih | live changed ih | spent changed ih => exact ih
  | handler changed ih | cell changed ih => exact .next ih

theorem Insertion.closing {before : Hints first} {after : Hints second} (changed : Insertion identity before after) :
    ContextInsertion identity first.shape.closing second.shape.closing := by
  induction changed with
  | here => exact .here
  | plain changed ih | handler changed ih | cleanup changed ih | running changed ih | spent changed ih => exact ih
  | cell changed ih => exact .next ih
  | live changed ih => exact ih.prefix _

/-- Closing-route safety is monotone under active provider insertion. It is
not an equality of routes: exported cell requests can become locally supplied. -/
theorem Insertion.closing_checked {before : Hints first} {after : Hints second}
    (changed : Insertion identity before after) (checked : Closing outward first.shape original surviving) :
    Closing outward second.shape original surviving := by
  induction changed with
  | here => exact .cell checked
  | plain changed ih => cases checked with | plain tail => exact .plain (ih tail)
  | handler changed ih => cases checked with | handler tail => exact .handler (ih tail)
  | cell changed ih => cases checked with | cell tail => exact .cell (ih tail)
  | cleanup changed ih => cases checked with
    | cleanup routes tail =>
        exact .cleanup (fun effect member => route_agreement (changed.normal.suffix _) (changed.closing.suffix _) (routes effect member)) (ih tail)
  | running changed ih => cases checked with | plain tail => exact .plain (ih tail)
  | live changed ih => cases checked with
    | live inside outside =>
        exact .live (closing_contexts inside (changed.normal.suffix _) (changed.closing.suffix _)) (ih outside)
  | spent changed ih => cases checked with | spent tail => exact .spent (ih tail)

theorem Insertion.forClosing {before : Hints first} {after : Hints second} (changed : Insertion identity before after) :
    Insertion identity (SourceContextualInvocationHints.forClosing before) (SourceContextualInvocationHints.forClosing after) := by
  induction changed with
  | here => exact .here
  | plain changed ih | handler changed ih | spent changed ih => exact ih
  | cell changed ih => exact .cell ih
  | cleanup changed ih => exact .cleanup ih
  | running changed ih => exact .running ih
  | live changed ih => exact (Insertion.running ih).prefix _

theorem Insertion.owners {before : Hints first} {after : Hints second} (changed : Insertion identity before after) :
    SourceDependencyOwners.owners first = SourceDependencyOwners.owners second := by
  induction changed <;> simp_all [SourceDependencyOwners.owners]

theorem Insertion.pending_owners {before : Hints first} {after : Hints second}
    (changed : Insertion identity before after) (checked : SourceDependencyOwners.PendingWithin world owned first) :
    SourceDependencyOwners.PendingWithin world owned second := by
  induction changed with
  | here => exact .cell checked
  | plain changed ih => cases checked with | plain code tail => exact .plain code (ih tail)
  | handler changed ih => cases checked with | handler tail => exact .handler (ih tail)
  | cell changed ih => cases checked with | cell tail => exact .cell (ih tail)
  | cleanup changed ih => cases checked with | cleanup tail => exact .cleanup (ih tail)
  | running changed ih => cases checked with | running tail => exact .running (ih tail)
  | live changed ih => cases checked with | live saved tail => exact .live saved (ih tail)
  | spent changed ih => cases checked with | spent tail => exact .spent (ih tail)

/-- Exactly one side of the selected handler split gains the cell. -/
inductive Split (identity : Nat) : {first outside second nextOutside : Scope} →
    Hints first → Hints outside → Hints second → Hints nextOutside → Prop where
  | inside (changed : Insertion identity before after) : Split identity before tail after tail
  | outside (changed : Insertion identity before after) : Split identity saved before saved after

theorem Split.prepend (changed : Split identity saved waiting nextSaved nextWaiting)
    (layer : Scope → Scope) (lift : ∀ {scope}, Hints scope → Hints (layer scope))
    (preserves : ∀ {first second} {before : Hints first} {after : Hints second},
      Insertion identity before after → Insertion identity (lift before) (lift after)) :
    Split identity (lift saved) waiting (lift nextSaved) nextWaiting := by
  cases changed with
  | inside next => exact .inside (preserves next)
  | outside next => exact .outside next

open SourceDependencyCapture (select)

/-- A cell can replace the selected handler with its builtin. Otherwise the
same handler, modes and actual annotated pieces survive the insertion. -/
theorem Insertion.cut {before : Hints first} {after : Hints second}
    {saved : Hints captured} {waiting : Hints tail}
    (changed : Insertion identity before after)
    (cut : SourcePlannedCuts.Cut effect operation contract modes before saved waiting) :
    select effect operation second = some (.builtin identity) ∨
      ∃ captured tail, ∃ nextSaved : Hints captured, ∃ nextWaiting : Hints tail,
        SourcePlannedCuts.Cut effect operation contract modes after nextSaved nextWaiting ∧ Split identity saved waiting nextSaved nextWaiting := by
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
        · exact .inr ⟨_, _, _, _, .handler different nextCut, pieces.prepend (fun scope => .handler _ _ _ scope) (fun hints => .handler _ hints) (fun changed => .handler changed)⟩
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
        · exact .inr ⟨_, _, _, _, .running nextCut, pieces.prepend (fun scope => .running scope) (fun hints => .running hints) (fun changed => .running changed)⟩
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

/-- An already available builtin remains available. -/
theorem Insertion.builtin {before : Hints first} {after : Hints second}
    (changed : Insertion identity before after) (found : select effect operation first = some (.builtin actual)) :
    ∃ next, select effect operation second = some (.builtin next) := by
  induction changed with
  | here =>
      by_cases hit : effect = .cell identity
      · exact ⟨identity, by simp only [select, if_pos hit]⟩
      · exact ⟨actual, by simp only [select, if_neg hit, found, Option.map_some, SourceDependencyCapture.Selection.prepend]⟩
  | handler changed ih =>
      rename_i other table families required
      by_cases hit : effect = other
      · simp only [select, if_pos hit] at found
        cases known : ProtectionContracts.lookup operation table <;>
          cases declared : SourceDependencyCapture.lookupDependencies operation families <;> simp [known, declared] at found
      · simp only [select, if_neg hit, Option.map_eq_some_iff] at found
        obtain ⟨selected, looked, same⟩ := found
        cases selected with
        | handler => cases same
        | builtin actual =>
            cases same
            obtain ⟨next, nextFound⟩ := ih looked
            exact ⟨next, by simp only [select, if_neg hit, nextFound, Option.map_some, SourceDependencyCapture.Selection.prepend]⟩
  | cell changed ih =>
      rename_i other
      by_cases hit : effect = .cell other
      · exact ⟨other, by simp only [select, if_pos hit]⟩
      · simp only [select, if_neg hit, Option.map_eq_some_iff] at found
        obtain ⟨selected, looked, same⟩ := found
        cases selected with
        | handler => cases same
        | builtin actual =>
            cases same
            obtain ⟨next, nextFound⟩ := ih looked
            exact ⟨next, by simp only [select, if_neg hit, nextFound, Option.map_some, SourceDependencyCapture.Selection.prepend]⟩
  | plain changed ih | cleanup changed ih | running changed ih | live changed ih | spent changed ih =>
      simp only [select, Option.map_eq_some_iff] at found
      obtain ⟨selected, looked, same⟩ := found
      cases selected with
      | handler => cases same
      | builtin actual =>
          cases same
          obtain ⟨next, nextFound⟩ := ih looked
          exact ⟨next, by simp only [select, nextFound, Option.map_some, SourceDependencyCapture.Selection.prepend]⟩

/-- Protection, offered mode and closing routes suffice to transport the
capture guard. This does not yet transport the scheduled source judgments. -/
theorem Insertion.capture_guard {before : Hints first} {after : Hints second}
    (changed : Insertion identity before after)
    (checked : SourceDependencyCapture.CaptureGuard outward first effect operation) :
    SourceDependencyCapture.CaptureGuard outward second effect operation := by
  cases checked with
  | builtin found =>
      obtain ⟨next, nextFound⟩ := changed.builtin found
      exact .builtin nextFound
  | handler found permission row body closing =>
      obtain ⟨saved, waiting, cut⟩ := SourcePlannedCuts.of_lookup before found
      rcases changed.cut cut with nextFound | ⟨_, _, nextSaved, nextWaiting, nextCut, pieces⟩
      · exact .builtin nextFound
      · cases pieces with
        | inside inserted =>
            exact .handler nextCut.lookup (inserted.held ▸ permission) (inserted.held ▸ row) (inserted.held ▸ body)
              (fun disposes => inserted.closing_checked (closing disposes))
        | outside inserted => exact .handler nextCut.lookup permission row body closing

/-- Operation capability requirements are monotone, even when the new
builtin replaces a source handler. No equality of lookup results is claimed. -/
theorem Insertion.capability {before : Hints first} {after : Hints second}
    (changed : Insertion identity before after)
    (checked : SourceContextualHints.checkCapability first effect operation = true) :
    SourceContextualHints.checkCapability second effect operation = true := by
  cases found : select effect operation first with
  | none => simp [SourceContextualHints.checkCapability, found] at checked
  | some selected => cases selected with
    | builtin actual =>
        obtain ⟨next, nextFound⟩ := changed.builtin found
        simp only [SourceContextualHints.checkCapability, nextFound]
    | handler captured tail contract modes =>
        obtain ⟨saved, waiting, cut⟩ := SourcePlannedCuts.of_lookup before found
        rcases changed.cut cut with nextFound | ⟨_, _, nextSaved, nextWaiting, nextCut, pieces⟩
        · simp only [SourceContextualHints.checkCapability, nextFound]
        · simpa only [SourceContextualHints.checkCapability, found, nextCut.lookup] using checked

theorem Insertion.requirements {before : Hints first} {after : Hints second}
    (changed : Insertion identity before after)
    (checked : SourceContextualHints.checkRequirements first required = true) :
    SourceContextualHints.checkRequirements second required = true := by
  apply List.all_eq_true.mpr
  intro requirement member
  exact changed.capability (List.all_eq_true.mp checked requirement member)

/-- Unchanged saved hints retain their handler requirements when their
receiving scope gains an active builtin provider. -/
theorem check_outside (hints : Hints scope) {before : Hints first} {after : Hints second}
    (changed : Insertion identity before after) (checked : hints.check first = true) : hints.check second = true := by
  exact SourceHandlerRequirements.check_transport hints checked
    (changed.requirements (SourceHandlerRequirements.exposed_requirements hints checked))

/-- Both ordinary installed-handler requirements and dormant saved
requirements continue to hold at their actual receiving scopes. -/
theorem Insertion.check {before : Hints first} {after : Hints second}
    (changed : Insertion identity before after) (outside : Hints outsideScope)
    (checked : before.check outsideScope = true) : after.check outsideScope = true := by
  induction changed with
  | here => exact checked
  | plain changed ih | cell changed ih | cleanup changed ih | running changed ih | spent changed ih => exact ih checked
  | handler changed ih =>
      simp only [Hints.check, Bool.and_eq_true] at checked ⊢
      obtain ⟨supplied, retained⟩ := checked
      exact ⟨(changed.suffix outside).requirements supplied, ih retained⟩
  | live changed ih =>
      simp only [Hints.check, Bool.and_eq_true] at checked ⊢
      obtain ⟨inside, outsideCheck⟩ := checked
      exact ⟨check_outside _ (changed.suffix outside) inside, ih outsideCheck⟩

open SourceContextualInvocationHints (Selection findOwner)

/-- An active owner keeps its dormant saved program. The inserted provider
belongs either to its caller prefix or to its waiting suffix. -/
inductive OwnerInsertion (identity : Nat) : Selection → Selection → Prop where
  | caller {front : Hints first} {nextFront : Hints second} {saved : Hints captured} {tail : Hints waiting}
      (changed : Insertion identity front nextFront) :
      OwnerInsertion identity ⟨⟨first, captured, waiting⟩, front, saved, tail⟩
        ⟨⟨second, captured, waiting⟩, nextFront, saved, tail⟩
  | waiting {front : Hints caller} {saved : Hints captured} {tail : Hints first} {nextTail : Hints second}
      (changed : Insertion identity tail nextTail) :
      OwnerInsertion identity ⟨⟨caller, captured, first⟩, front, saved, tail⟩
        ⟨⟨caller, captured, second⟩, front, saved, nextTail⟩

theorem OwnerInsertion.of_shared (changed : SourceInterpretationInsertion.OwnerInsertion (.cell identity) first second) :
    OwnerInsertion identity first second := by
  cases changed with
  | caller next => exact .caller (Insertion.of_shared next)
  | waiting next => exact .waiting (Insertion.of_shared next)

theorem OwnerInsertion.shared (changed : OwnerInsertion identity first second) :
    SourceInterpretationInsertion.OwnerInsertion (.cell identity) first second := by
  cases changed with
  | caller next => exact .caller next.shared
  | waiting next => exact .waiting next.shared

theorem Insertion.find_owner (changed : Insertion identity before after)
    (found : findOwner owner before = some selected) :
    ∃ next, findOwner owner after = some next ∧ OwnerInsertion identity selected next := by
  obtain ⟨next, foundNext, related⟩ := changed.shared.find_owner found
  exact ⟨next, foundNext, OwnerInsertion.of_shared related⟩

theorem OwnerInsertion.resumed (changed : OwnerInsertion identity first second) :
    Insertion identity (first.resumed owner).hints (second.resumed owner).hints :=
  Insertion.of_shared changed.shared.resumed

theorem OwnerInsertion.disposed (changed : OwnerInsertion identity first second) :
    Insertion identity (first.disposed owner).hints (second.disposed owner).hints :=
  Insertion.of_shared changed.shared.disposed

/-- Reuse independent permission and phase checks at the same saved owner.
The result explicitly retains the new cell in the recomposed caller. -/
theorem Insertion.resume_access {before : Hints first} {after : Hints second}
    (changed : Insertion identity before after)
    (access : SourceDependencyCapture.ResumeChecked actions phases owner first result) :
    ∃ original : Hints result, ∃ nextScope, ∃ next : Hints nextScope,
      SourceDependencyCapture.ResumeChecked actions phases owner second nextScope ∧ Insertion identity original next := by
  obtain ⟨original, nextScope, next, nextAccess, related⟩ := changed.shared.resume_access access
  exact ⟨original, nextScope, next, nextAccess, Insertion.of_shared related⟩

theorem Insertion.dispose_access {before : Hints first} {after : Hints second}
    (changed : Insertion identity before after)
    (access : SourceDependencyCapture.DisposeChecked outward actions phases owner first result) :
    ∃ original : Hints result, ∃ nextScope, ∃ next : Hints nextScope,
      SourceDependencyCapture.DisposeChecked outward actions phases owner second nextScope ∧ Insertion identity original next := by
  obtain ⟨original, nextScope, next, nextAccess, related⟩ := changed.shared.dispose_access access
  exact ⟨original, nextScope, next, nextAccess, Insertion.of_shared related⟩

namespace Examples
open SourceDependencyCapture.Examples (disposeTable disposeDependencies)

def before : Hints (.handler (.cell 4) disposeTable disposeDependencies .nil) := .handler [] .nil

/-- A source handler may become preempted by the new builtin. Admissibility
is preserved even though its selected interpretation is not equal. -/
theorem builtin_preempts_handler :
    select (.cell 4) 0 (.handler (.cell 4) disposeTable disposeDependencies .nil) ≠
      select (.cell 4) 0 (.cell 4 (.handler (.cell 4) disposeTable disposeDependencies .nil)) ∧
    SourceDependencyCapture.CaptureGuard [] (.cell 4 (.handler (.cell 4) disposeTable disposeDependencies .nil)) (.cell 4) 0 := by
  constructor
  · intro same; cases same
  · exact (Insertion.here (identity := 4) (before := before)).capture_guard
      (.handler rfl rfl rfl rfl (fun _ => .handler .nil))

/-- The same inserted cell can convert two agreeing exported routes to two
agreeing local routes, without preserving their old target. -/
theorem exported_route_becomes_local :
    Route [.cell 4] [] (.cell 4) none ∧ Route [.cell 4] [.cell 4] (.cell 4) (some 4) :=
  ⟨.outside (by simp), (ContextInsertion.here (identity := 4) (before := [])).route (.outside (by simp))⟩

/-- Closing a dormant provider can expose it only on the closing side. The
existing counterexample therefore still excludes arbitrary forest insertion. -/
theorem dormant_insertion_rejected :
    ¬ Insertion 4 (Hints.live (owner := 9) Hints.nil Hints.nil)
      (Hints.live (owner := 9) (Hints.cell (identity := 4) Hints.nil) Hints.nil) ∧
    ¬ Closing [.cell 4] (.cleanup [.cell 4] (.live (.cell 4 .nil) .nil)) [] [] := by
  constructor
  · intro changed; cases changed
  · exact SourceRecursiveRoutes.Examples.newly_visible_cell_rejected _

end Examples

end Ash.OneShot.SourceProviderInsertion

#print axioms Ash.OneShot.SourceProviderInsertion.ContextInsertion.prefix
#print axioms Ash.OneShot.SourceProviderInsertion.ContextInsertion.suffix
#print axioms Ash.OneShot.SourceProviderInsertion.ContextInsertion.route
#print axioms Ash.OneShot.SourceProviderInsertion.route_agreement
#print axioms Ash.OneShot.SourceProviderInsertion.closing_contexts
#print axioms Ash.OneShot.SourceProviderInsertion.Insertion.prefix
#print axioms Ash.OneShot.SourceProviderInsertion.Insertion.suffix
#print axioms Ash.OneShot.SourceProviderInsertion.Insertion.held
#print axioms Ash.OneShot.SourceProviderInsertion.Insertion.normal
#print axioms Ash.OneShot.SourceProviderInsertion.Insertion.closing
#print axioms Ash.OneShot.SourceProviderInsertion.Insertion.closing_checked
#print axioms Ash.OneShot.SourceProviderInsertion.Insertion.forClosing
#print axioms Ash.OneShot.SourceProviderInsertion.Insertion.owners
#print axioms Ash.OneShot.SourceProviderInsertion.Insertion.pending_owners

#print axioms Ash.OneShot.SourceProviderInsertion.Split.prepend
#print axioms Ash.OneShot.SourceProviderInsertion.Insertion.cut
#print axioms Ash.OneShot.SourceProviderInsertion.Insertion.builtin
#print axioms Ash.OneShot.SourceProviderInsertion.Insertion.capture_guard
#print axioms Ash.OneShot.SourceProviderInsertion.Examples.builtin_preempts_handler
#print axioms Ash.OneShot.SourceProviderInsertion.Examples.exported_route_becomes_local
#print axioms Ash.OneShot.SourceProviderInsertion.Examples.dormant_insertion_rejected

#print axioms Ash.OneShot.SourceProviderInsertion.Insertion.capability
#print axioms Ash.OneShot.SourceProviderInsertion.Insertion.requirements
#print axioms Ash.OneShot.SourceProviderInsertion.check_outside
#print axioms Ash.OneShot.SourceProviderInsertion.Insertion.check

#print axioms Ash.OneShot.SourceProviderInsertion.Insertion.find_owner
#print axioms Ash.OneShot.SourceProviderInsertion.OwnerInsertion.resumed
#print axioms Ash.OneShot.SourceProviderInsertion.OwnerInsertion.disposed
#print axioms Ash.OneShot.SourceProviderInsertion.Insertion.resume_access
#print axioms Ash.OneShot.SourceProviderInsertion.Insertion.dispose_access

#print axioms Ash.OneShot.SourceProviderInsertion.Insertion.shared
#print axioms Ash.OneShot.SourceProviderInsertion.Insertion.of_shared
#print axioms Ash.OneShot.SourceProviderInsertion.OwnerInsertion.of_shared
#print axioms Ash.OneShot.SourceProviderInsertion.OwnerInsertion.shared
