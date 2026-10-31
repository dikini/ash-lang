import Std

/-
Finite ordered collection model. Lists here are inductive finite values; the
correspondence to Ash must establish finiteness, since Ash values can be cyclic.
No statement in this file authenticates an actual linked function or checker.
-/
namespace Ash.NetworkLedger

inductive Id where
  | root
  | work (allocator : Nat) (serial : Int)
  deriving DecidableEq, Repr

inductive Status where
  | found | missing
  deriving DecidableEq, Repr

variable {Entry : Type} (key : Entry → Id)

def erase (q : Id) : List Entry → List Entry
  | [] => []
  | x :: xs => if key x = q then xs else x :: erase q xs

def remove (q : Id) : List Entry → List Entry × Status
  | [] => ([], .missing)
  | x :: xs =>
      if key x = q then (xs, .found)
      else let (ys, status) := remove q xs; (x :: ys, status)

def lookup (q : Id) : List Entry → Option Entry
  | [] => none
  | x :: xs => if key x = q then some x else lookup q xs

def insert (x : Entry) (xs : List Entry) : List Entry := xs ++ [x]

def update (q : Id) (replacement : Entry) : List Entry → List Entry
  | [] => []
  | x :: xs => if key x = q then replacement :: xs else x :: update q replacement xs

def Unique (xs : List Entry) : Prop := (xs.map key).Nodup

theorem remove_sequence (q : Id) (xs : List Entry) : (remove key q xs).1 = erase key q xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [remove, erase]
    split <;> simp_all

theorem erase_subsequence (q : Id) (xs : List Entry) : List.Sublist (erase key q xs) xs := by
  induction xs with
  | nil => simp [erase]
  | cons x xs ih =>
    simp only [erase]
    split
    · exact List.Sublist.cons _ (List.Sublist.refl _)
    · exact List.Sublist.cons_cons _ ih

theorem erase_finite_unique (q : Id) (xs : List Entry) (h : Unique key xs) :
    Unique key (erase key q xs) := by
  exact (erase_subsequence key q xs).map key |>.nodup h

theorem erase_retains_whole_order (q : Id) (xs : List Entry) :
    List.Sublist (remove key q xs).1 xs := by
  rw [remove_sequence]
  exact erase_subsequence key q xs

theorem remove_found_iff (q : Id) (xs : List Entry) :
    (remove key q xs).2 = .found ↔ q ∈ xs.map key := by
  induction xs with
  | nil => simp [remove]
  | cons x xs ih =>
    simp only [remove, List.map_cons, List.mem_cons]
    split
    · simp_all
    · simp_all [eq_comm]

theorem remove_missing_iff (q : Id) (xs : List Entry) :
    (remove key q xs).2 = .missing ↔ q ∉ xs.map key := by
  have found := remove_found_iff key q xs
  cases h : (remove key q xs).2 <;> simp_all

theorem lookup_sound (q : Id) (xs : List Entry) (x : Entry)
    (h : lookup key q xs = some x) : x ∈ xs ∧ key x = q := by
  induction xs with
  | nil => simp [lookup] at h
  | cons y ys ih =>
    simp only [lookup] at h
    split at h
    · rename_i eq
      cases h
      exact ⟨by simp, eq⟩
    · obtain ⟨mem, eq⟩ := ih h
      exact ⟨by simp [mem], eq⟩

theorem lookup_complete (q : Id) (xs : List Entry) (h : q ∈ xs.map key) :
    ∃ x, lookup key q xs = some x ∧ key x = q := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.map_cons, List.mem_cons] at h
    by_cases eq : key x = q
    · exact ⟨x, by simp [lookup, eq], eq⟩
    · have tail : q ∈ xs.map key := by
        rcases h with h | h
        · exact False.elim (eq h.symm)
        · exact h
      obtain ⟨v, found, kval⟩ := ih tail
      exact ⟨v, by simpa [lookup, eq] using found, kval⟩

theorem insert_unique (x : Entry) (xs : List Entry) (unique : Unique key xs)
    (fresh : key x ∉ xs.map key) : Unique key (insert x xs) := by
  simp only [Unique, insert, List.map_append, List.map_cons, List.map_nil, List.nodup_append]
  refine ⟨unique, by simp, ?_⟩
  intro a ha b hb eq
  simp only [List.mem_singleton] at hb
  apply fresh
  simpa [eq, hb] using ha

theorem erase_absent_unchanged (q : Id) (xs : List Entry) (h : q ∉ xs.map key) :
    erase key q xs = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp [erase, Ne.symm h.1, ih h.2]

theorem erase_contains_unmatched (q : Id) (xs : List Entry) (x : Entry)
    (member : x ∈ xs) (different : key x ≠ q) : x ∈ erase key q xs := by
  induction xs with
  | nil => simp at member
  | cons y ys ih =>
    simp only [List.mem_cons] at member
    simp only [erase]
    split
    · rename_i eq
      rcases member with same | tail
      · subst y; contradiction
      · exact tail
    · rcases member with same | tail
      · simp [same]
      · exact List.mem_cons_of_mem _ (ih tail)

theorem erase_excludes_key (q : Id) (xs : List Entry) (unique : Unique key xs) :
    q ∉ (erase key q xs).map key := by
  induction xs with
  | nil => simp [erase]
  | cons x xs ih =>
    have pair : key x ∉ xs.map key ∧ Unique key xs := by
      simpa [Unique] using unique
    simp only [erase]
    split
    · rename_i eq
      simpa [eq] using pair.1
    · rename_i ne
      simp only [List.map_cons, List.mem_cons, not_or]
      exact ⟨Ne.symm ne, ih pair.2⟩

theorem erase_membership (q : Id) (xs : List Entry) (x : Entry) (unique : Unique key xs) :
    x ∈ erase key q xs ↔ x ∈ xs ∧ key x ≠ q := by
  constructor
  · intro member
    refine ⟨(erase_subsequence key q xs).mem member, ?_⟩
    intro eq
    apply erase_excludes_key key q xs unique
    exact List.mem_map.mpr ⟨x, member, eq⟩
  · rintro ⟨member, different⟩
    exact erase_contains_unmatched key q xs x member different

theorem lookup_unique (q : Id) (xs : List Entry) (x : Entry)
    (unique : Unique key xs) (member : x ∈ xs) (matchKey : key x = q) :
    lookup key q xs = some x := by
  induction xs with
  | nil => simp at member
  | cons y ys ih =>
    have pair : key y ∉ ys.map key ∧ Unique key ys := by
      simpa [Unique] using unique
    rcases List.mem_cons.mp member with same | tail
    · subst y; simp [lookup, matchKey]
    · have ne : key y ≠ q := by
        intro eq
        apply pair.1
        exact List.mem_map.mpr ⟨x, tail, matchKey.trans eq.symm⟩
      simp [lookup, ne, ih pair.2 tail]

theorem update_keys (q : Id) (replacement : Entry) (xs : List Entry)
    (replacementKey : key replacement = q) :
    (update key q replacement xs).map key = xs.map key := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [update]
    split
    · rename_i eq
      simp [replacementKey, eq]
    · simp [ih]

theorem update_unique (q : Id) (replacement : Entry) (xs : List Entry)
    (replacementKey : key replacement = q) (unique : Unique key xs) :
    Unique key (update key q replacement xs) := by
  simpa [Unique, update_keys key q replacement xs replacementKey] using unique

theorem update_all (q : Id) (replacement : Entry) (xs : List Entry) (P : Entry → Prop)
    (old : ∀ x ∈ xs, P x) (new : P replacement) :
    ∀ x ∈ update key q replacement xs, P x := by
  induction xs with
  | nil => simp [update]
  | cons y ys ih =>
    intro x member
    simp only [update] at member
    split at member
    · simp only [List.mem_cons] at member
      rcases member with same | tail
      · subst x; exact new
      · exact old x (List.mem_cons_of_mem _ tail)
    · simp only [List.mem_cons] at member
      rcases member with same | tail
      · subst x; exact old y (by simp)
      · exact ih (fun z hz ↦ old z (List.mem_cons_of_mem _ hz)) x tail

theorem update_missing (q : Id) (replacement : Entry) (xs : List Entry)
    (missing : q ∉ xs.map key) : update key q replacement xs = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at missing
    simp [update, Ne.symm missing.1, ih missing.2]

theorem lookup_none_of_absent (q : Id) (xs : List Entry) (absent : q ∉ xs.map key) :
    lookup key q xs = none := by
  cases h : lookup key q xs with
  | none => rfl
  | some x =>
    obtain ⟨member, matchKey⟩ := lookup_sound key q xs x h
    exact False.elim (absent (List.mem_map.mpr ⟨x, member, matchKey⟩))

theorem lookup_update (q : Id) (replacement : Entry) (xs : List Entry) (x : Entry)
    (found : lookup key q xs = some x) (replacementKey : key replacement = q) :
    lookup key q (update key q replacement xs) = some replacement := by
  induction xs with
  | nil => simp [lookup] at found
  | cons y ys ih =>
    by_cases eq : key y = q
    · simp [update, lookup, eq, replacementKey]
    · simp only [lookup, eq, ↓reduceIte] at found
      simp [update, lookup, eq, ih found]

theorem update_other_lookup (p q : Id) (replacement : Entry) (xs : List Entry)
    (different : p ≠ q) (replacementKey : key replacement = q) :
    lookup key p (update key q replacement xs) = lookup key p xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases eq : key x = q
    · have oldNe : key x ≠ p := by
        intro h
        exact different (h.symm.trans eq)
      have replacementNe : key replacement ≠ p := by
        intro h
        exact different (h.symm.trans replacementKey)
      simp [update, lookup, eq, replacementNe, Ne.symm different]
    · by_cases px : key x = p
      · simp [update, lookup, px, different]
      · simp [update, lookup, eq, px, ih]

theorem unique_keys_injective (xs : List Entry) (x y : Entry) (unique : Unique key xs)
    (xmem : x ∈ xs) (ymem : y ∈ xs) (sameKey : key x = key y) : x = y := by
  induction xs with
  | nil => simp at xmem
  | cons head tail ih =>
    have pair : key head ∉ tail.map key ∧ Unique key tail := by simpa [Unique] using unique
    rcases List.mem_cons.mp xmem with xHead | xTail
    · rcases List.mem_cons.mp ymem with yHead | yTail
      · exact xHead.trans yHead.symm
      · subst x
        exact False.elim (pair.1 (List.mem_map.mpr ⟨y, yTail, sameKey.symm⟩))
    · rcases List.mem_cons.mp ymem with yHead | yTail
      · subst y
        exact False.elim (pair.1 (List.mem_map.mpr ⟨x, xTail, sameKey⟩))
      · exact ih pair.2 xTail yTail

theorem lookup_update_decompose (q : Id) (replacement : Entry) (xs : List Entry) (x : Entry)
    (found : lookup key q xs = some x) :
    ∃ before after, xs = before ++ x :: after ∧ q ∉ before.map key ∧
      update key q replacement xs = before ++ replacement :: after := by
  induction xs with
  | nil => simp [lookup] at found
  | cons head tail ih =>
    by_cases eq : key head = q
    · simp [lookup, eq] at found
      subst x
      exact ⟨[], tail, rfl, by simp, by simp [update, eq]⟩
    · simp [lookup, eq] at found
      obtain ⟨before, after, split, absent, updated⟩ := ih found
      refine ⟨head :: before, after, ?_, ?_, ?_⟩
      · simp [split]
      · simp [Ne.symm eq, absent]
      · simp [update, eq, updated]

end Ash.NetworkLedger
