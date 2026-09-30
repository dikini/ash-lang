import SourceContextualInvocationHints

/-! Shared owner-selection transport for inserting a builtin or source handler.
This generalizes the existing provider proof. It makes no claim about operation
selection, retained-source checking or installed-handler compatibility. -/
namespace Ash.OneShot.SourceInterpretationInsertion
open ScopedExpressions
open SourceDependencyCapture (Scope)
open SourceContextualHints (Hints)

inductive Frame where
  | cell (identity : Nat)
  | handler (effect : Instance) (table : List (Nat × ProtectionContracts.ClauseContract))
      (families : SourceDependencyAnnotations.ClauseDependencies) (required : List SourceContextualHints.Requirement)

def Frame.layer : Frame → Scope → Scope
  | .cell identity => .cell identity
  | .handler effect table families _ => .handler effect table families

def Frame.apply (frame : Frame) : {scope : Scope} → Hints scope → Hints (frame.layer scope) :=
  match frame with
  | .cell _ => .cell
  | .handler _ _ _ required => .handler required

theorem Frame.find_owner (frame : Frame) (before : Hints scope) :
    SourceContextualInvocationHints.findOwner owner (frame.apply before) =
      (SourceContextualInvocationHints.findOwner owner before).map
        (SourceContextualInvocationHints.Selection.prepend frame.layer frame.apply) := by
  cases frame <;> rfl

/-- Insert one interpretation frame on the active spine; saved branches and
all existing annotations are retained. -/
inductive Insertion (frame : Frame) : {first second : Scope} → Hints first → Hints second → Prop where
  | here : Insertion frame before (frame.apply before)
  | plain : Insertion frame before after →
      Insertion frame (.plain (dependencies := dependencies) before) (.plain (dependencies := dependencies) after)
  | handler : Insertion frame before after →
      Insertion frame (.handler (effect := effect) (table := table) (families := families) required before)
        (.handler (effect := effect) (table := table) (families := families) required after)
  | cell : Insertion frame before after →
      Insertion frame (.cell (identity := other) before) (.cell (identity := other) after)
  | cleanup : Insertion frame before after →
      Insertion frame (.cleanup (needs := needs) (callback := callback) before)
        (.cleanup (needs := needs) (callback := callback) after)
  | running : Insertion frame before after → Insertion frame (.running before) (.running after)
  | live : Insertion frame before after →
      Insertion frame (.live (owner := owner) saved before) (.live (owner := owner) saved after)
  | spent : Insertion frame before after →
      Insertion frame (.spent (owner := owner) before) (.spent (owner := owner) after)

theorem Insertion.prefix (front : Hints scope) (changed : Insertion frame before after) :
    Insertion frame (front.append before) (front.append after) := by
  induction front with
  | nil => exact changed
  | plain rest ih => exact .plain ih
  | handler required rest ih => exact .handler ih
  | cell rest ih => exact .cell ih
  | cleanup rest ih => exact .cleanup ih
  | running rest ih => exact .running ih
  | live saved rest ihSaved ihRest => exact .live ihRest
  | spent rest ih => exact .spent ih

theorem Insertion.suffix (changed : Insertion frame before after) (tail : Hints scope) :
    Insertion frame (before.append tail) (after.append tail) := by
  induction changed with
  | here => cases frame <;> exact .here
  | plain changed ih => exact .plain ih
  | handler changed ih => exact .handler ih
  | cell changed ih => exact .cell ih
  | cleanup changed ih => exact .cleanup ih
  | running changed ih => exact .running ih
  | live changed ih => exact .live ih
  | spent changed ih => exact .spent ih

open SourceContextualInvocationHints (Selection findOwner)

/-- An active owner keeps its dormant saved program. The inserted interpretation
belongs either to its caller prefix or to its waiting suffix. -/
inductive OwnerInsertion (frame : Frame) : Selection → Selection → Prop where
  | caller {front : Hints first} {nextFront : Hints second} {saved : Hints captured} {tail : Hints waiting}
      (changed : Insertion frame front nextFront) :
      OwnerInsertion frame ⟨⟨first, captured, waiting⟩, front, saved, tail⟩
        ⟨⟨second, captured, waiting⟩, nextFront, saved, tail⟩
  | waiting {front : Hints caller} {saved : Hints captured} {tail : Hints first} {nextTail : Hints second}
      (changed : Insertion frame tail nextTail) :
      OwnerInsertion frame ⟨⟨caller, captured, first⟩, front, saved, tail⟩
        ⟨⟨caller, captured, second⟩, front, saved, nextTail⟩

private theorem OwnerInsertion.here (selected : Selection) :
    OwnerInsertion frame selected (selected.prepend frame.layer frame.apply) := by
  cases selected with
  | mk scopes front saved tail => cases scopes; exact .caller .here

private theorem OwnerInsertion.prepend (changed : OwnerInsertion frame first second)
    (layer : Scope → Scope) (lift : ∀ {scope}, Hints scope → Hints (layer scope))
    (preserves : ∀ {first second} {before : Hints first} {after : Hints second},
      Insertion frame before after → Insertion frame (lift before) (lift after)) :
    OwnerInsertion frame (first.prepend layer lift) (second.prepend layer lift) := by
  cases changed with
  | caller next => exact .caller (preserves next)
  | waiting next => exact .waiting next

theorem Insertion.find_owner (changed : Insertion frame before after)
    (found : findOwner owner before = some selected) :
    ∃ next, findOwner owner after = some next ∧ OwnerInsertion frame selected next := by
  induction changed generalizing selected with
  | here => exact ⟨_, by simp only [Frame.find_owner, found, Option.map_some], OwnerInsertion.here _⟩
  | live changed ih =>
      simp only [findOwner] at found ⊢
      split at found
      next hit =>
        cases Option.some.inj found
        exact ⟨_, by simp only [if_pos hit], .waiting changed⟩
      next miss =>
        simp only [if_neg miss, Option.map_eq_some_iff] at found ⊢
        obtain ⟨inside, located, rfl⟩ := found
        obtain ⟨next, locatedNext, related⟩ := ih located
        exact ⟨_, ⟨next, locatedNext, rfl⟩, related.prepend _ _ (fun changed => .live changed)⟩
  | plain changed ih =>
      simp only [findOwner, Option.map_eq_some_iff] at found ⊢
      obtain ⟨inside, located, rfl⟩ := found
      obtain ⟨next, locatedNext, related⟩ := ih located
      exact ⟨_, ⟨next, locatedNext, rfl⟩, related.prepend _ _ (fun changed => .plain changed)⟩
  | handler changed ih =>
      simp only [findOwner, Option.map_eq_some_iff] at found ⊢
      obtain ⟨inside, located, rfl⟩ := found
      obtain ⟨next, locatedNext, related⟩ := ih located
      exact ⟨_, ⟨next, locatedNext, rfl⟩, related.prepend _ _ (fun changed => .handler changed)⟩
  | cell changed ih =>
      simp only [findOwner, Option.map_eq_some_iff] at found ⊢
      obtain ⟨inside, located, rfl⟩ := found
      obtain ⟨next, locatedNext, related⟩ := ih located
      exact ⟨_, ⟨next, locatedNext, rfl⟩, related.prepend _ _ (fun changed => .cell changed)⟩
  | cleanup changed ih =>
      simp only [findOwner, Option.map_eq_some_iff] at found ⊢
      obtain ⟨inside, located, rfl⟩ := found
      obtain ⟨next, locatedNext, related⟩ := ih located
      exact ⟨_, ⟨next, locatedNext, rfl⟩, related.prepend _ _ (fun changed => .cleanup changed)⟩
  | running changed ih =>
      simp only [findOwner, Option.map_eq_some_iff] at found ⊢
      obtain ⟨inside, located, rfl⟩ := found
      obtain ⟨next, locatedNext, related⟩ := ih located
      exact ⟨_, ⟨next, locatedNext, rfl⟩, related.prepend _ _ (fun changed => .running changed)⟩
  | spent changed ih =>
      simp only [findOwner, Option.map_eq_some_iff] at found ⊢
      obtain ⟨inside, located, rfl⟩ := found
      obtain ⟨next, locatedNext, related⟩ := ih located
      exact ⟨_, ⟨next, locatedNext, rfl⟩, related.prepend _ _ (fun changed => .spent changed)⟩

theorem OwnerInsertion.resumed (changed : OwnerInsertion frame first second) :
    Insertion frame (first.resumed owner).hints (second.resumed owner).hints := by
  cases changed with
  | caller next => exact (next.suffix _).prefix _
  | waiting next => exact ((Insertion.spent next).prefix _).prefix _

theorem OwnerInsertion.disposed (changed : OwnerInsertion frame first second) :
    Insertion frame (first.disposed owner).hints (second.disposed owner).hints := by
  cases changed with
  | caller next => exact (Insertion.running (next.suffix _)).prefix _
  | waiting next => exact (Insertion.running ((Insertion.spent next).prefix _)).prefix _

private theorem annotated_owner {hints : Hints scope}
    (cut : SourceDependencyCapture.OwnerCut owner scope selected) :
    ∃ original, findOwner owner hints = some original ∧ original.scopes = selected := by
  apply Option.map_eq_some_iff.mp
  rw [SourceContextualInvocationHints.find_owner_erases]
  exact cut.lookup

/-- Reuse independent permission and phase checks at the same saved owner.
The result explicitly retains the new frame in the recomposed caller. -/
theorem Insertion.resume_access {before : Hints first} {after : Hints second}
    (changed : Insertion frame before after)
    (access : SourceDependencyCapture.ResumeChecked actions phases owner first result) :
    ∃ original : Hints result, ∃ nextScope, ∃ next : Hints nextScope,
      SourceDependencyCapture.ResumeChecked actions phases owner second nextScope ∧ Insertion frame original next := by
  cases access with
  | checked cut known permission available =>
      obtain ⟨selected, found, same⟩ := annotated_owner (hints := before) cut
      cases same
      obtain ⟨next, foundNext, related⟩ := changed.find_owner found
      exact ⟨(selected.resumed owner).hints, _, (next.resumed owner).hints,
        .checked (SourceContextualInvocationHints.selected_cut foundNext) known permission available, related.resumed⟩

theorem Insertion.dispose_access {before : Hints first} {after : Hints second}
    (changed : Insertion frame before after)
    (access : SourceDependencyCapture.DisposeChecked outward actions phases owner first result) :
    ∃ original : Hints result, ∃ nextScope, ∃ next : Hints nextScope,
      SourceDependencyCapture.DisposeChecked outward actions phases owner second nextScope ∧ Insertion frame original next := by
  cases access with
  | checked cut known permission available unprotected closing =>
      obtain ⟨selected, found, same⟩ := annotated_owner (hints := before) cut
      cases same
      obtain ⟨next, foundNext, related⟩ := changed.find_owner found
      have savedSame : selected.scopes.captured = next.scopes.captured := by cases related <;> rfl
      exact ⟨(selected.disposed owner).hints, _, (next.disposed owner).hints,
        .checked (SourceContextualInvocationHints.selected_cut foundNext) known permission available
          (savedSame ▸ unprotected) (savedSame ▸ closing), related.disposed⟩

end Ash.OneShot.SourceInterpretationInsertion

#print axioms Ash.OneShot.SourceInterpretationInsertion.Frame.find_owner
#print axioms Ash.OneShot.SourceInterpretationInsertion.Insertion.prefix
#print axioms Ash.OneShot.SourceInterpretationInsertion.Insertion.suffix
#print axioms Ash.OneShot.SourceInterpretationInsertion.Insertion.find_owner
#print axioms Ash.OneShot.SourceInterpretationInsertion.OwnerInsertion.resumed
#print axioms Ash.OneShot.SourceInterpretationInsertion.OwnerInsertion.disposed
#print axioms Ash.OneShot.SourceInterpretationInsertion.Insertion.resume_access
#print axioms Ash.OneShot.SourceInterpretationInsertion.Insertion.dispose_access
