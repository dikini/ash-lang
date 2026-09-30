import CoreTranslation

/-! Fuel properties of the existing syntax translator. These concern finite
syntax traversal, not execution, metadata authentication or admission. -/
namespace Ash.OneShot.CoreTranslationFuel
open Ash.OneShot Instantiation ScopedExpressions CoreSyntax CoreTranslation

private def Extends {α : Type} (a b : Except Error α) : Prop :=
  ∀ value, a = .ok value → b = .ok value

private theorem extends_refl {α : Type} (a : Except Error α) : Extends a a :=
  fun _ h => h

private theorem extends_bind {α β : Type} (a b : Except Error α)
    (f g : α → Except Error β) (ha : Extends a b)
    (hf : ∀ value, Extends (f value) (g value)) :
    Extends (a.bind f) (b.bind g) := by
  intro value h
  cases h₁ : a with
  | error error => simp [h₁, Except.bind] at h
  | ok item =>
      have h₂ := ha item h₁
      simpa [h₂, Except.bind] using hf item value (by simpa [h₁, Except.bind] using h)

private theorem extends_mapM {α β : Type} (xs : List α)
    (f g : α → Except Error β) (h : ∀ x, Extends (f x) (g x)) :
    Extends (xs.mapM f) (xs.mapM g) := by
  induction xs with
  | nil => exact extends_refl _
  | cons x xs ih =>
      simp only [List.mapM_cons]
      apply extends_bind _ _ _ _ (h x)
      intro y
      apply extends_bind _ _ _ _ ih
      intro ys
      exact extends_refl _

private theorem fuel_extension (graph : Graph) (fuel : Nat) :
    ∀ owners index, Extends (translateFuel graph fuel owners index)
      (translateFuel graph (fuel + 1) owners index) := by
  induction fuel with
  | zero =>
      intro owners index code success
      simp [translateFuel] at success
  | succ fuel ih =>
      intro owners index
      rw [translateFuel, translateFuel]
      apply extends_bind _ _ _ _ (extends_refl _)
      intro node
      split <;> try simp_all only
      all_goals
        repeat first
          | exact extends_refl _
          | apply extends_bind _ _ _ _ (ih _ _); intro item
          | apply extends_bind _ _ _ _ (extends_mapM _ _ _ (by
              intro clause
              split
              · apply extends_bind _ _ _ _ (extends_refl _)
                intro item
                split
                · apply extends_bind _ _ _ _ (ih _ _)
                  intro item
                  exact extends_refl _
                · exact extends_refl _
              · split
                · apply extends_bind _ _ _ _ (ih _ _)
                  intro item
                  exact extends_refl _
                · exact extends_refl _)); intro item
          | apply extends_bind _ _ _ _ (extends_refl _); intro item
          | split <;> try simp_all only

/-- One more recursion level preserves successful syntax, including handler
clauses translated under extended owner maps. -/
theorem success_succ (graph : Graph) (fuel : Nat) (owners : OwnerMap)
    (index : NodeRef) (code : Code)
    (success : translateFuel graph fuel owners index = .ok code) :
    translateFuel graph (fuel + 1) owners index = .ok code :=
  fuel_extension graph fuel owners index code success

/-- Larger fuel preserves the exact successful syntax, for arbitrary graphs
and owner maps. No graph-shape or execution-success premise is required. -/
theorem success_mono (graph : Graph) (small large : Nat) (owners : OwnerMap)
    (index : NodeRef) (code : Code) (bound : small ≤ large)
    (success : translateFuel graph small owners index = .ok code) :
    translateFuel graph large owners index = .ok code := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le bound
  clear bound
  induction extra with
  | zero => simpa using success
  | succ extra ih =>
      simpa [Nat.add_assoc] using success_succ graph (small + extra) owners index code ih

/-- Stored references are strictly earlier than their parent node. -/
def Postorder (graph : Graph) : Prop :=
  ∀ index node, graph.node index = some node →
    ∀ child, child ∈ node.kind.children → child < index

private def FuelSafe {α : Type} (result : Except Error α) : Prop :=
  ∀ index, result ≠ .error (.fuelExhausted index)

private theorem safe_ok {α : Type} (value : α) : FuelSafe (.ok value) := by
  intro index h
  cases h

private theorem safe_bind {α β : Type} (a : Except Error α)
    (f : α → Except Error β) (ha : FuelSafe a)
    (hf : ∀ value, a = .ok value → FuelSafe (f value)) :
    FuelSafe (a.bind f) := by
  cases h : a with
  | error e =>
      intro index bad
      apply ha index
      simpa [h, Except.bind] using bad
  | ok v => simpa [h, Except.bind] using hf v h

private theorem safe_forIn {α β : Type} (xs : List α)
    (f : α → β → Except Error (ForInStep β))
    (h : ∀ x, x ∈ xs → ∀ state, FuelSafe (f x state)) (state : β) :
    FuelSafe (forIn xs state f) := by
  induction xs generalizing state with
  | nil => simpa only [List.forIn_nil, Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw] using safe_ok state
  | cons x xs ih =>
      rw [List.forIn_cons]
      apply safe_bind _ _ (h x (by simp) state)
      intro step _
      cases step with
      | done state => exact safe_ok state
      | yield state => exact ih (by intro x hx; exact h x (by simp [hx])) state

private theorem safe_mapM {α β : Type} (xs : List α)
    (f : α → Except Error β) (h : ∀ x, x ∈ xs → FuelSafe (f x)) :
    FuelSafe (xs.mapM f) := by
  induction xs with
  | nil => exact safe_ok _
  | cons x xs ih =>
      simp only [List.mapM_cons]
      apply safe_bind _ _ (h x (by simp))
      intro y _
      apply safe_bind _ _ (ih (by intro x hx; exact h x (by simp [hx])))
      intro ys _
      exact safe_ok _

private theorem require_safe (graph : Graph) (index : Nat) :
    FuelSafe (requireNode graph index) := by
  unfold requireNode
  split
  · intro i h; cases h
  · exact safe_ok _

private theorem resolve_safe (owners : OwnerMap) (index handler owner : Nat) :
    FuelSafe (resolveOwner owners index handler owner) := by
  unfold resolveOwner
  split
  · intro i h; cases h
  · split
    · intro i h; cases h
    · exact safe_ok _

private theorem clauses_safe (index : Nat) (clauses : List Clause) :
    FuelSafe (checkClauseShapes index clauses) := by
  unfold checkClauseShapes
  apply safe_bind
  · apply safe_forIn
    intro clause _ state
    dsimp only
    split <;> split <;> try split <;>
      simp [FuelSafe, Except.bind, Pure.pure, Bind.bind, Except.pure, throw, throwThe, MonadExceptOf.throw]
  · intro _ _; exact safe_ok _

private theorem cleanup_safe (graph : Graph) (index : Nat) (callback : Binder) (action : Nat) :
    FuelSafe (checkCleanup graph index callback action) := by
  unfold checkCleanup
  apply safe_bind _ _ (require_safe _ _)
  intro actionNode _
  split
  · apply safe_bind _ _ (require_safe _ _)
    intro functionNode _
    apply safe_bind _ _ (require_safe _ _)
    intro argumentNode _
    split
    · split
      · exact safe_ok _
      · intro i h; cases h
    · intro i h; cases h
  · intro i h; cases h

/-- Postorder node index is a structural recursion bound. Static rejection
reasons remain possible, but enough fuel cannot yield fuelExhausted. -/
theorem postorder_fuel_safe (graph : Graph) (ordered : Postorder graph)
    (fuel : Nat) (owners : OwnerMap) (index : NodeRef) (enough : index < fuel) :
    ∀ exhausted, translateFuel graph fuel owners index ≠ .error (.fuelExhausted exhausted) := by
  induction fuel generalizing owners index with
  | zero => simp at enough
  | succ fuel ih =>
      rw [translateFuel]
      apply safe_bind _ _ (require_safe _ _)
      intro node known
      have present : graph.node index = some node := by
        unfold requireNode at known
        split at known <;> simp_all
      have children := ordered index node present
      split
      all_goals simp only [*, Kind.children, List.map_cons, List.map_nil, List.mem_cons,
        List.mem_append, List.mem_map, List.not_mem_nil, or_false, or_imp, forall_and, forall_eq] at children
      case h_5 =>
        apply safe_bind
        · exact ih _ _ (Nat.lt_of_lt_of_le children (Nat.lt_succ_iff.mp enough))
        · intro item _; exact safe_ok _
      case h_6 =>
        apply safe_bind
        · exact ih _ _ (Nat.lt_of_lt_of_le children.1 (Nat.lt_succ_iff.mp enough))
        · intro item _
          apply safe_bind
          · exact ih _ _ (Nat.lt_of_lt_of_le children.2 (Nat.lt_succ_iff.mp enough))
          · intro item _; exact safe_ok _
      case h_7 =>
        apply safe_bind
        · exact ih _ _ (Nat.lt_of_lt_of_le children.1 (Nat.lt_succ_iff.mp enough))
        · intro item _
          apply safe_bind
          · exact ih _ _ (Nat.lt_of_lt_of_le children.2 (Nat.lt_succ_iff.mp enough))
          · intro item _; exact safe_ok _
      case h_8 =>
        apply safe_bind
        · exact ih _ _ (Nat.lt_of_lt_of_le children.1 (Nat.lt_succ_iff.mp enough))
        · intro item _
          apply safe_bind
          · exact ih _ _ (Nat.lt_of_lt_of_le children.2 (Nat.lt_succ_iff.mp enough))
          · intro item _; exact safe_ok _
      case h_10 =>
        apply safe_bind
        · exact ih _ _ (Nat.lt_of_lt_of_le children.1 (Nat.lt_succ_iff.mp enough))
        · intro item _
          apply safe_bind
          · exact ih _ _ (Nat.lt_of_lt_of_le children.2 (Nat.lt_succ_iff.mp enough))
          · intro item _; exact safe_ok _
      case h_18 =>
        apply safe_bind
        · exact ih _ _ (Nat.lt_of_lt_of_le children.1 (Nat.lt_succ_iff.mp enough))
        · intro item _
          apply safe_bind
          · exact ih _ _ (Nat.lt_of_lt_of_le children.2 (Nat.lt_succ_iff.mp enough))
          · intro item _; exact safe_ok _
      case h_11 =>
        apply safe_bind
        · exact ih _ _ (Nat.lt_of_lt_of_le children.1 (Nat.lt_succ_iff.mp enough))
        · intro item _
          apply safe_bind
          · exact ih _ _ (Nat.lt_of_lt_of_le children.2.1 (Nat.lt_succ_iff.mp enough))
          · intro item _
            apply safe_bind
            · exact ih _ _ (Nat.lt_of_lt_of_le children.2.2 (Nat.lt_succ_iff.mp enough))
            · intro item _; exact safe_ok _
      case h_12 =>
        apply safe_bind
        · exact ih _ _ (Nat.lt_of_lt_of_le children.1 (Nat.lt_succ_iff.mp enough))
        · intro item _
          apply safe_bind
          · exact ih _ _ (Nat.lt_of_lt_of_le children.2.2 (Nat.lt_succ_iff.mp enough))
          · intro item _
            apply safe_bind
            · exact ih _ _ (Nat.lt_of_lt_of_le children.2.1 (Nat.lt_succ_iff.mp enough))
            · intro item _; exact safe_ok _
      case h_14 =>
        apply safe_bind
        · exact ih _ _ (Nat.lt_of_lt_of_le children (Nat.lt_succ_iff.mp enough))
        · intro item _; exact safe_ok _
      case h_16 =>
        apply safe_bind _ _ (resolve_safe _ _ _ _)
        intro item _
        apply safe_bind
        · exact ih _ _ (Nat.lt_of_lt_of_le children (Nat.lt_succ_iff.mp enough))
        · intro item _; exact safe_ok _
      case h_19 =>
        apply safe_bind _ _ (cleanup_safe _ _ _ _)
        intro item _
        apply safe_bind
        · exact ih _ _ (Nat.lt_of_lt_of_le children.2 (Nat.lt_succ_iff.mp enough))
        · intro item _; exact safe_ok _
      case h_20 =>
        apply safe_bind
        · exact ih _ _ (Nat.lt_of_lt_of_le children.1 (Nat.lt_succ_iff.mp enough))
        · intro initializer _
          split
          · apply safe_bind _ _ (by intro i h; cases h)
            intro item _
            apply safe_bind
            · exact ih _ _ (Nat.lt_of_lt_of_le children.2 (Nat.lt_succ_iff.mp enough))
            · intro item _; exact safe_ok _
          · apply safe_bind
            · exact ih _ _ (Nat.lt_of_lt_of_le children.2 (Nat.lt_succ_iff.mp enough))
            · intro item _; exact safe_ok _
      case h_15 =>
        apply safe_bind _ _ (clauses_safe _ _)
        intro item _
        apply safe_bind
        · exact ih _ _ (Nat.lt_of_lt_of_le children.1 (Nat.lt_succ_iff.mp enough))
        · intro body _
          apply safe_bind
          · apply safe_mapM
            intro clause member
            have child_bound := children.2 clause.body ⟨clause, member, rfl⟩
            split
            · split
              · apply safe_bind _ _ (by intro i h; cases h)
                intro item _
                apply safe_bind
                · exact ih _ _ (Nat.lt_of_lt_of_le child_bound (Nat.lt_succ_iff.mp enough))
                · intro item _; exact safe_ok _
              · apply safe_bind
                · exact ih _ _ (Nat.lt_of_lt_of_le child_bound (Nat.lt_succ_iff.mp enough))
                · intro item _; exact safe_ok _
            · split
              · apply safe_bind _ _ (by intro i h; cases h)
                intro item _
                intro i h; cases h
              · intro i h; cases h
          · intro item _; exact safe_ok _
      all_goals
        repeat first
          | exact safe_ok _
          | apply safe_bind _ _ (clauses_safe _ _); intro item item_known
          | apply safe_bind _ _ (cleanup_safe _ _ _ _); intro item item_known
          | apply safe_bind _ _ (resolve_safe _ _ _ _); intro item item_known
          | intro exhausted bad; cases bad
private theorem bind_ok {α β : Type} (a : Except Error α)
    (f : α → Except Error β) (value : β) (success : a.bind f = .ok value) :
    ∃ item, a = .ok item ∧ f item = .ok value := by
  cases h : a with
  | error e => simp [h, Except.bind] at success
  | ok item => exact ⟨item, rfl, by simpa [h, Except.bind] using success⟩

private theorem forIn_all {α β : Type} (xs : List α)
    (f : α → β → Except Error (ForInStep β)) (P : α → Prop)
    (step : ∀ x state out, f x state = .ok out → ∃ next, out = .yield next ∧ P x)
    (initial final : β) (success : forIn xs initial f = .ok final) :
    ∀ x, x ∈ xs → P x := by
  induction xs generalizing initial final with
  | nil => simp
  | cons x xs ih =>
      rw [List.forIn_cons] at success
      obtain ⟨out, first, rest⟩ := bind_ok _ _ _ success
      obtain ⟨next, rfl, holds⟩ := step x initial out first
      intro y member
      rcases List.mem_cons.mp member with rfl | tail
      · exact holds
      · exact ih next final rest y tail

/-- The existing checked graph supplies strict postorder, independently of
all retained type and effect-row metadata. -/
theorem checkShape_postorder (graph : Graph) (checked : ShapeChecked graph) :
    Postorder graph := by
  unfold ShapeChecked checkShape at checked
  split at checked
  · simp [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at checked
  · obtain ⟨final, loop, _⟩ := bind_ok _ _ _ checked
    have all := forIn_all _ _
      (fun pair : Node × Nat => ∀ child, child ∈ pair.1.kind.children → child < pair.2)
      (by
        intro pair originals out success
        cases pair with
        | mk node index =>
          dsimp only at success
          split at success
          · simp [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at success
          · split at success
            · simp [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at success
            · obtain ⟨fragmentResult, _, rest⟩ := bind_ok _ _ _ success
              obtain ⟨done, children, result⟩ := bind_ok _ _ _ rest
              have bounded := forIn_all _ _ (fun child : Nat => child < index)
                (by
                  intro child state out child_success
                  split at child_success
                  · simp [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at child_success
                  · have below : child < index := Nat.lt_of_not_ge (by assumption)
                    exact ⟨PUnit.unit, by simpa [Pure.pure, Except.pure] using child_success.symm, below⟩)
                PUnit.unit done children
              exact ⟨node.originalId :: originals, by simpa [Pure.pure, Except.pure] using result.symm, bounded⟩)
      [] final loop
    intro index node present
    have member : (node, index) ∈ graph.nodes.zipIdx :=
      List.mk_mem_zipIdx_iff_getElem?.mpr present
    exact all (node, index) member

theorem checkShape_root_bound (graph : Graph) (checked : ShapeChecked graph) :
    graph.root < graph.nodes.length := by
  unfold ShapeChecked checkShape at checked
  split at checked
  · simp [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at checked
  · exact Nat.lt_of_not_ge (by assumption)

/-- A checked finite graph's public budget cannot fail from fuel exhaustion.
Owner resolution, recursive-initializer restrictions and cleanup shape checks
can still reject the syntax; no successful translation premise is supplied. -/
theorem checked_budget_fuel_safe (graph : Graph) (checked : ShapeChecked graph)
    (owners : OwnerMap) (index : NodeRef) (bounded : index < graph.nodes.length) :
    ∀ exhausted, translateFuel graph (graph.nodes.length + 1) owners index ≠
      .error (.fuelExhausted exhausted) :=
  postorder_fuel_safe graph (checkShape_postorder graph checked) _ owners index
    (Nat.lt_trans bounded (Nat.lt_succ_self _))

theorem translate_not_fuel_exhausted (graph : Graph) (checked : ShapeChecked graph) :
    ∀ exhausted, translate graph ≠ .error (.fuelExhausted exhausted) := by
  rw [translate_of_shape graph checked]
  exact checked_budget_fuel_safe graph checked [] graph.root (checkShape_root_bound graph checked)

namespace Examples
open CoreTranslation.Examples

example : translateFuel strictRequest 2 [] strictRequest.root =
    .error (.fuelExhausted 0) := rfl

example : translateFuel strictRequest 3 [] strictRequest.root =
    .ok (.perform exact 4 (.perform (.user 92 []) 0 .unit)) := rfl

example : translateFuel strictRequest 30 [] strictRequest.root =
    .ok (.perform exact 4 (.perform (.user 92 []) 0 .unit)) :=
  success_mono strictRequest 3 30 [] strictRequest.root _ (by decide) rfl

example : translateFuel ownedHandler 2 [] ownedHandler.root =
    .error (.fuelExhausted 0) := rfl

example (large : Nat) (enough : 5 ≤ large) :
    translateFuel ownedHandler large [] ownedHandler.root =
      translateFuel ownedHandler 5 [] ownedHandler.root := by
  have h := success_mono ownedHandler 5 large [] ownedHandler.root _ enough (by rfl)
  exact h

/-- The singleton recursive wrapper remains syntax-only: its initializer
is checked for the existing nonrecursive dependency restriction. -/
def recursiveWrapper : Graph := ⟨[
  node 0 .unit,
  node 1 (.recursiveBind [⟨⟨4, .unit⟩, 0⟩] 0)], 1⟩

example : translateFuel recursiveWrapper 1 [] 1 =
    .error (.fuelExhausted 0) := rfl

example : translateFuel recursiveWrapper 2 [] 1 =
    .ok (.bind 4 .unit .unit) := rfl

example (large : Nat) (enough : 2 ≤ large) :
    translateFuel recursiveWrapper large [] 1 = .ok (.bind 4 .unit .unit) :=
  success_mono recursiveWrapper 2 large [] 1 _ enough rfl

example : translate ⟨[node 0 (.discard 1 2 .consumed)], 0⟩ =
    .error (.ownerNotActive 0 1 2) := rfl

example : ∀ exhausted, translate strictRequest ≠ .error (.fuelExhausted exhausted) :=
  translate_not_fuel_exhausted strictRequest rfl

example : ∀ exhausted, translate ownedHandler ≠ .error (.fuelExhausted exhausted) :=
  translate_not_fuel_exhausted ownedHandler rfl

example : ∀ exhausted, translate authenticatedCleanup ≠ .error (.fuelExhausted exhausted) :=
  translate_not_fuel_exhausted authenticatedCleanup rfl

end Examples

#print axioms success_succ
#print axioms success_mono
#print axioms postorder_fuel_safe
#print axioms checkShape_postorder
#print axioms checked_budget_fuel_safe
#print axioms translate_not_fuel_exhausted
end Ash.OneShot.CoreTranslationFuel
