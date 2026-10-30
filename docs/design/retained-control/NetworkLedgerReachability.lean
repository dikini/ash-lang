import NetworkLedgerCollections

/- Finite logical dependency paths. Transport and actual completion remain separate. -/
namespace Ash.NetworkLedger.Reachability

open Ash.NetworkLedger

structure Edge where
  parent : Id
  child : Id
  destination : Nat
  deriving DecidableEq, Repr

inductive Rooted (edges : List Edge) : Id → Prop where
  | root : Rooted edges .root
  | child (parent child : Id) (destination : Nat) :
      Rooted edges parent → ⟨parent, child, destination⟩ ∈ edges → Rooted edges child

theorem rooted_mono (old new : List Edge) (id : Id)
    (contains : ∀ e ∈ old, e ∈ new) (rooted : Rooted old id) : Rooted new id := by
  induction rooted with
  | root => exact .root
  | child parent child destination _ member ih =>
    exact .child parent child destination ih (contains _ member)

theorem rooted_register (edges : List Edge) (parent child : Id) (destination : Nat)
    (parentRooted : Rooted edges parent) :
    Rooted (edges ++ [⟨parent, child, destination⟩]) child := by
  apply Rooted.child parent child destination
  · exact rooted_mono edges (edges ++ [⟨parent, child, destination⟩]) parent
      (fun e mem ↦ List.mem_append_left _ mem) parentRooted
  · simp

def Leaf (edges : List Edge) (child : Id) : Prop := ∀ e ∈ edges, e.parent ≠ child

theorem rooted_after_leaf_removal (edges : List Edge) (removed : Edge) (id : Id)
    (unique : Unique Edge.child edges) (leaf : Leaf edges removed.child)
    (rooted : Rooted edges id) (different : id ≠ removed.child) :
    Rooted (erase Edge.child removed.child edges) id := by
  induction rooted with
  | root => exact .root
  | child parent child destination parentRooted member ih =>
    have parentDifferent : parent ≠ removed.child := leaf ⟨parent, child, destination⟩ member
    apply Rooted.child parent child destination
    · exact ih parentDifferent
    · apply (erase_membership Edge.child removed.child edges ⟨parent, child, destination⟩ unique).mpr
      exact ⟨member, different⟩

theorem rooted_has_root_edge (edges : List Edge) (id : Id) (rooted : Rooted edges id)
    (nonroot : id ≠ .root) : ∃ edge ∈ edges, edge.parent = .root := by
  induction rooted with
  | root => exact False.elim (nonroot rfl)
  | child parent child destination parentRooted member ih =>
    by_cases atRoot : parent = .root
    · exact ⟨⟨parent, child, destination⟩, member, atRoot⟩
    · exact ih atRoot

end Ash.NetworkLedger.Reachability
