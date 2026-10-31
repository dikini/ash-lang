import NetworkLedgerTransitions
import NetworkLedgerReachability

/-
Structural bridge from the finite modeled ledger to graph edges. This file
neither authenticates a linked Ash implementation nor asserts protocol safety.
-/
namespace Ash.NetworkLedger.Coupling

open Ash.NetworkLedger
open Ash.NetworkLedger.Reachability

/-- Delivery installs a fresh, open local record; failure leaves the ledger intact. -/
def install (l : Ledger) (id : Id) (parent : Address) : Ledger :=
  if id = .root ∨ id ∈ l.records.map Record.id then l
  else { l with records := insert ⟨id, some parent, .open, []⟩ l.records }

theorem install_preserves_invariant (l : Ledger) (id : Id) (parent : Address)
    (valid : LocalInvariant l) : LocalInvariant (install l id parent) := by
  by_cases reject : id = .root ∨ id ∈ l.records.map Record.id
  · simpa only [install, reject, ↓reduceIte] using valid
  · have fresh : id ∉ l.records.map Record.id := by
      intro member
      exact reject (Or.inr member)
    simp only [install, reject, ↓reduceIte]
    refine ⟨valid.1, insert_unique Record.id _ _ valid.2.1 fresh, ?_⟩
    intro record member
    simp only [insert, List.mem_append, List.mem_singleton] at member
    rcases member with old | same
    · exact valid.2.2 record old
    · subst record
      simp [RecordValid, Unique]

theorem install_frames (l : Ledger) (id : Id) (parent : Address) :
    (install l id parent).owner = l.owner ∧ (install l id parent).next = l.next ∧
    (install l id parent).outputs = l.outputs := by
  simp only [install]
  split <;> simp_all

/-- Every graph edge is derived from a whole child entry in a local record. -/
def recordEdges (r : Record) : List Edge :=
  r.children.map (fun c => ⟨r.id, c.id, c.destination⟩)

def ledgerEdges (l : Ledger) : List Edge := l.records.flatMap recordEdges

def ledgerGraph (workers : List Ledger) : List Edge := workers.flatMap ledgerEdges

theorem edge_membership (l : Ledger) (e : Edge) :
    e ∈ ledgerEdges l ↔ ∃ r ∈ l.records, ∃ c ∈ r.children,
      e = ⟨r.id, c.id, c.destination⟩ := by
  simp [ledgerEdges, recordEdges, eq_comm]

theorem graph_membership (workers : List Ledger) (e : Edge) :
    e ∈ ledgerGraph workers ↔ ∃ l ∈ workers, ∃ r ∈ l.records,
      ∃ c ∈ r.children, e = ⟨r.id, c.id, c.destination⟩ := by
  simp [ledgerGraph, edge_membership]

theorem root_edges_of_quiet_ledger (l : Ledger) (valid : LocalInvariant l)
    (quiet : probeRoot l = true) :
    ∀ e ∈ ledgerEdges l, e.parent ≠ .root := by
  obtain ⟨root, found, _, empty⟩ := quiet_probe_is_closed_empty l quiet
  have rootMember := (lookup_sound Record.id .root l.records root found).1
  have rootKey := (lookup_sound Record.id .root l.records root found).2
  intro edge member rootParent
  obtain ⟨r, rmem, child, cmem, equal⟩ := (edge_membership l edge).mp member
  have key : r.id = root.id := by
    have eq : r.id = .root := by simpa [equal] using rootParent
    exact eq.trans rootKey.symm
  have same : r = root := unique_keys_injective Record.id l.records r root valid.2.1 rmem rootMember key
  subst r
  simp [empty] at cmem

/-- Root identity is confined to one ledger by a separately maintained global invariant. -/
def RootConfined (workers : List Ledger) (rootLedger : Ledger) : Prop :=
  rootLedger ∈ workers ∧
  ∀ l ∈ workers, l ≠ rootLedger → ∀ r ∈ l.records, r.id ≠ .root

theorem root_edges_of_quiet (workers : List Ledger) (rootLedger : Ledger)
    (confined : RootConfined workers rootLedger) (valid : LocalInvariant rootLedger)
    (quiet : probeRoot rootLedger = true) :
    ∀ e ∈ ledgerGraph workers, e.parent ≠ .root := by
  intro edge member rootParent
  obtain ⟨l, lm, r, rm, c, cm, equal⟩ := (graph_membership workers edge).mp member
  by_cases same : l = rootLedger
  · subst l
    apply root_edges_of_quiet_ledger rootLedger valid quiet edge
    · exact (edge_membership rootLedger edge).mpr ⟨r, rm, c, cm, equal⟩
    · exact rootParent
  · have noRoot := confined.2 l lm same r rm
    apply noRoot
    simpa [equal] using rootParent

/-- An open registration adds precisely its child edge and queued work item. -/
theorem register_edges_and_output (l : Ledger) (p : Id) (d : Nat) (payload : List UInt8)
    (r : Record) (found : lookup Record.id p l.records = some r)
    (opened : r.phase = .open) (edge : Edge) :
    let result := (register l p d payload).1
    (edge ∈ ledgerEdges result ↔ edge ∈ ledgerEdges l ∨
      edge = ⟨p, .work l.owner l.next, d⟩) ∧
    result.outputs = l.outputs ++ [.work (.work l.owner l.next) ⟨l.owner, p⟩ d payload] := by
  have key := (lookup_sound Record.id p l.records r found).2
  obtain ⟨before, after, split, _, updated⟩ := lookup_update_decompose Record.id p
    { r with children := insert ⟨.work l.owner l.next, d⟩ r.children } l.records r found
  rw [register_open l p d payload r found opened]
  dsimp
  rw [updated]
  constructor
  · simp only [ledgerEdges, split, List.flatMap_append, List.flatMap_cons,
      recordEdges, insert, List.map_append, List.map_cons, List.map_nil,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    simp only [key]
    simp [or_assoc, or_left_comm, or_comm]
  · rfl

theorem close_edges (l : Ledger) (p : Id) (edge : Edge) :
    edge ∈ ledgerEdges (close l p) ↔ edge ∈ ledgerEdges l := by
  cases found : lookup Record.id p l.records with
  | none => simp [close, found]
  | some r =>
    by_cases closed : r.phase = .closed
    · simp [close, found, closed]
    · obtain ⟨before, after, split, _, updated⟩ :=
        lookup_update_decompose Record.id p { r with phase := .closed } l.records r found
      simp only [close, found, closed, ↓reduceIte]
      rw [updated]
      simp [ledgerEdges, recordEdges, split]

theorem retire_edges (l : Ledger) (p : Id) (edge : Edge) (valid : LocalInvariant l) :
    edge ∈ ledgerEdges (retire l p) ↔ edge ∈ ledgerEdges l := by
  cases found : lookup Record.id p l.records with
  | none => simp [retire, found]
  | some r =>
    cases parent : r.parent with
    | none => simp [retire, found, parent]
    | some address =>
      by_cases ready : r.phase = .closed ∧ r.children = [] ∧ p ≠ .root
      · have rmem := (lookup_sound Record.id p l.records r found).1
        have rkey := (lookup_sound Record.id p l.records r found).2
        simp only [retire, found, parent, ready.1, ready.2.1, true_and]
        rw [if_pos ready.2.2]
        rw [edge_membership, edge_membership]
        constructor
        · rintro ⟨x, xmem, c, cmem, eq⟩
          exact ⟨x, (erase_retains_whole_order Record.id p l.records).mem xmem, c, cmem, eq⟩
        · rintro ⟨x, xmem, c, cmem, eq⟩
          have ne : x.id ≠ p := by
            intro same
            have equal : x = r := unique_keys_injective Record.id l.records x r
              valid.2.1 xmem rmem (same.trans rkey.symm)
            subst x
            simp [ready.2.1] at cmem
          refine ⟨x, ?_, c, cmem, eq⟩
          rw [remove_sequence]
          exact erase_contains_unmatched Record.id p l.records x xmem ne
      · simp [retire, found, parent, ready]

theorem install_edges (l : Ledger) (id : Id) (parent : Address) (edge : Edge) :
    edge ∈ ledgerEdges (install l id parent) ↔ edge ∈ ledgerEdges l := by
  by_cases reject : id = .root ∨ id ∈ l.records.map Record.id
  · simp only [install, reject, ↓reduceIte]
  · simp only [install, reject, ↓reduceIte]
    simp [ledgerEdges, recordEdges, insert]

/-- Acknowledgement cannot create an edge, even on a rejected branch. -/
theorem acknowledge_edges_subset (l : Ledger) (p child : Id) (peer : Nat) (edge : Edge) :
    edge ∈ ledgerEdges (acknowledge l p child peer) → edge ∈ ledgerEdges l := by
  cases found : lookup Record.id p l.records with
  | none => simp [acknowledge, found]
  | some r =>
    cases childFound : lookup Child.id child r.children with
    | none => simp [acknowledge, found, childFound]
    | some entry =>
      by_cases matched : entry.destination = peer
      · obtain ⟨before, after, split, _, updated⟩ := lookup_update_decompose Record.id p
          { r with children := (remove Child.id child r.children).1 } l.records r found
        simp only [acknowledge, found, childFound, matched, ↓reduceIte]
        rw [updated]
        simp only [ledgerEdges, split, List.flatMap_append, List.flatMap_cons,
          List.mem_append]
        intro member
        rcases member with b | middle | a
        · exact Or.inl b
        · apply Or.inr (Or.inl ?_)
          have sub := (erase_retains_whole_order Child.id child r.children).map
            (fun (c : Child) => (⟨r.id, c.id, c.destination⟩ : Edge))
          exact sub.mem middle
        · exact Or.inr (Or.inr a)
      · simp [acknowledge, found, childFound, matched]

/-- Any edge with a different child ID survives acknowledgement. -/
theorem acknowledge_preserves_other_edges (l : Ledger) (p child : Id) (peer : Nat) (edge : Edge)
    (different : edge.child ≠ child) (old : edge ∈ ledgerEdges l) :
    edge ∈ ledgerEdges (acknowledge l p child peer) := by
  cases found : lookup Record.id p l.records with
  | none => simpa [acknowledge, found] using old
  | some r =>
    cases childFound : lookup Child.id child r.children with
    | none => simpa [acknowledge, found, childFound] using old
    | some entry =>
      by_cases matched : entry.destination = peer
      · obtain ⟨before, after, split, _, updated⟩ := lookup_update_decompose Record.id p
          { r with children := (remove Child.id child r.children).1 } l.records r found
        simp only [acknowledge, found, childFound, matched, ↓reduceIte]
        rw [updated]
        simp only [ledgerEdges, split, List.flatMap_append, List.flatMap_cons,
          List.mem_append] at old ⊢
        rcases old with b | middle | a
        · exact Or.inl b
        · apply Or.inr (Or.inl ?_)
          change edge ∈ r.children.map (fun c => ⟨r.id, c.id, c.destination⟩) at middle
          obtain ⟨c, cmem, ceq⟩ := List.mem_map.mp middle
          have cne : c.id ≠ child := by
            intro equal
            apply different
            simpa [← ceq] using equal
          change edge ∈ ((remove Child.id child r.children).1).map
            (fun c => ⟨r.id, c.id, c.destination⟩)
          apply List.mem_map.mpr
          refine ⟨c, ?_, ceq⟩
          rw [remove_sequence]
          exact erase_contains_unmatched Child.id child r.children c cmem cne
        · exact Or.inr (Or.inr a)
      · simpa [acknowledge, found, childFound, matched] using old

def HasRoot (l : Ledger) : Prop := .root ∈ l.records.map Record.id

theorem initial_root_has_root (owner : Nat) : HasRoot (initialRoot owner) := by
  simp [HasRoot, initialRoot]

theorem initial_worker_has_no_root (owner : Nat) : ¬ HasRoot (initialWorker owner) := by
  simp [HasRoot, initialWorker]

theorem install_root_frame (l : Ledger) (id : Id) (parent : Address) :
    HasRoot (install l id parent) ↔ HasRoot l := by
  by_cases reject : id = .root ∨ id ∈ l.records.map Record.id
  · simp only [install, reject, ↓reduceIte]
  · have notRoot : id ≠ .root := fun eq => reject (Or.inl eq)
    simp only [install, reject, ↓reduceIte, HasRoot, insert, List.map_append,
      List.map_cons, List.map_nil, List.mem_append, List.mem_singleton]
    simp [Ne.symm notRoot]

theorem register_root_frame (l : Ledger) (p : Id) (d : Nat) (payload : List UInt8) :
    HasRoot (register l p d payload).1 ↔ HasRoot l := by
  cases found : lookup Record.id p l.records with
  | none => simp [register, found]
  | some r =>
    by_cases closed : r.phase = .closed
    · simp [register, found, closed]
    · have key := (lookup_sound Record.id p l.records r found).2
      simp only [register, found, closed, ↓reduceIte, HasRoot]
      rw [update_keys Record.id p { r with children := insert ⟨.work l.owner l.next, d⟩ r.children } l.records key]

theorem close_root_frame (l : Ledger) (p : Id) : HasRoot (close l p) ↔ HasRoot l := by
  cases found : lookup Record.id p l.records with
  | none => simp [close, found]
  | some r =>
    by_cases closed : r.phase = .closed
    · simp [close, found, closed]
    · have key := (lookup_sound Record.id p l.records r found).2
      simp only [close, found, closed, ↓reduceIte, HasRoot]
      rw [update_keys Record.id p { r with phase := .closed } l.records key]

theorem ack_root_frame (l : Ledger) (p child : Id) (peer : Nat) :
    HasRoot (acknowledge l p child peer) ↔ HasRoot l := by
  cases found : lookup Record.id p l.records with
  | none => simp [acknowledge, found]
  | some r =>
    cases childFound : lookup Child.id child r.children with
    | none => simp [acknowledge, found, childFound]
    | some entry =>
      by_cases matched : entry.destination = peer
      · have key := (lookup_sound Record.id p l.records r found).2
        simp only [acknowledge, found, childFound, matched, ↓reduceIte, HasRoot]
        rw [update_keys Record.id p { r with children := (remove Child.id child r.children).1 } l.records key]
      · simp [acknowledge, found, childFound, matched]

theorem retire_root_frame (l : Ledger) (p : Id) : HasRoot (retire l p) ↔ HasRoot l := by
  cases found : lookup Record.id p l.records with
  | none => simp [retire, found]
  | some r =>
    cases parent : r.parent with
    | none => simp [retire, found, parent]
    | some address =>
      by_cases ready : r.phase = .closed ∧ r.children = [] ∧ p ≠ .root
      · simp only [retire, found, parent, ready.1, ready.2.1, true_and]
        rw [if_pos ready.2.2]
        simp only [HasRoot, List.mem_map]
        constructor
        · rintro ⟨x, member, key⟩
          exact ⟨x, (erase_retains_whole_order Record.id p l.records).mem member, key⟩
        · rintro ⟨x, member, key⟩
          refine ⟨x, ?_, key⟩
          rw [remove_sequence]
          apply erase_contains_unmatched Record.id p l.records x member
          intro eq
          exact ready.2.2 (eq.symm.trans key)
      · simp [retire, found, parent, ready]

/-- Modeled publication takes precisely the oldest queued whole output value. -/
def takeOutput (l : Ledger) : Ledger × Option Output :=
  match l.outputs with
  | [] => (l, none)
  | head :: tail => ({ l with outputs := tail }, some head)

theorem take_output_frames (l : Ledger) :
    (takeOutput l).1.owner = l.owner ∧ (takeOutput l).1.next = l.next ∧
    (takeOutput l).1.records = l.records := by
  simp only [takeOutput]
  split <;> simp_all

/-- A local system step uses the same functional transitions and allocator history. -/
inductive LocalStep : Tracked → Tracked → Prop where
  | noop (t : Tracked) : LocalStep t t
  | action (t : Tracked) (a : Action) : LocalStep t (t.run a)
  | delivery (t : Tracked) (id : Id) (parent : Address) :
      LocalStep t ⟨install t.ledger id parent, t.history⟩
  | take (t : Tracked) : LocalStep t ⟨(takeOutput t.ledger).1, t.history⟩

theorem local_step_valid {before after : Tracked} (valid : before.Valid)
    (step : LocalStep before after) : after.Valid := by
  cases step with
  | noop => exact valid
  | action a => exact tracked_action_preserves before a valid
  | delivery id parent =>
    have frames := install_frames before.ledger id parent
    exact ⟨install_preserves_invariant before.ledger id parent valid.1, valid.2.1,
      valid.2.2.1.trans frames.1.symm, valid.2.2.2.trans frames.2.1.symm⟩
  | take =>
    have frames := take_output_frames before.ledger
    exact ⟨by simpa [LocalInvariant, frames.1, frames.2.1, frames.2.2] using valid.1,
      valid.2.1, valid.2.2.1.trans frames.1.symm, valid.2.2.2.trans frames.2.1.symm⟩

theorem local_step_root_frame {before after : Tracked} (step : LocalStep before after) :
    HasRoot after.ledger ↔ HasRoot before.ledger := by
  cases step with
  | noop => rfl
  | action a =>
    cases a with
    | register p d payload =>
      cases result : register before.ledger p d payload with
      | mk l status =>
        cases status <;>
          simpa [Tracked.run, Tracked.register, result] using register_root_frame before.ledger p d payload
    | close id => exact close_root_frame before.ledger id
    | retire id => exact retire_root_frame before.ledger id
    | ack p c peer => exact ack_root_frame before.ledger p c peer
  | delivery id parent => exact install_root_frame before.ledger id parent
  | take => simp [HasRoot, (take_output_frames before.ledger).2.2]

structure System where
  root : Tracked
  workers : List Tracked
  deriving Repr

def System.Valid (s : System) : Prop :=
  s.root.Valid ∧ HasRoot s.root.ledger ∧
  ∀ w ∈ s.workers, w.Valid ∧ ¬ HasRoot w.ledger

def trackedRoot (owner : Nat) : Tracked :=
  ⟨initialRoot owner, ⟨owner, 0, []⟩⟩

def trackedWorker (owner : Nat) : Tracked :=
  ⟨initialWorker owner, ⟨owner, 0, []⟩⟩

def initialSystem (rootOwner : Nat) (workerOwners : List Nat) : System :=
  ⟨trackedRoot rootOwner, workerOwners.map trackedWorker⟩

theorem tracked_root_valid (owner : Nat) : (trackedRoot owner).Valid := by
  exact ⟨initial_root_invariant owner, allocator_initial_valid owner, rfl, rfl⟩

theorem tracked_worker_valid (owner : Nat) : (trackedWorker owner).Valid := by
  exact ⟨initial_worker_invariant owner, allocator_initial_valid owner, rfl, rfl⟩

theorem initial_system_valid (owner : Nat) (others : List Nat) :
    (initialSystem owner others).Valid := by
  refine ⟨tracked_root_valid owner, initial_root_has_root owner, ?_⟩
  intro worker member
  obtain ⟨workerOwner, _, equal⟩ := List.mem_map.mp member
  subst worker
  exact ⟨tracked_worker_valid workerOwner, initial_worker_has_no_root workerOwner⟩

inductive SystemStep : System → System → Prop where
  | root (s : System) (next : Tracked) (step : LocalStep s.root next) :
      SystemStep s { s with root := next }
  | worker (s : System) (before after : List Tracked) (old next : Tracked)
      (workers : s.workers = before ++ old :: after) (step : LocalStep old next) :
      SystemStep s { s with workers := before ++ next :: after }

theorem system_step_valid {s t : System} (valid : s.Valid) (step : SystemStep s t) :
    t.Valid := by
  cases step with
  | root next localStep =>
    exact ⟨local_step_valid valid.1 localStep,
      (local_step_root_frame localStep).mpr valid.2.1, valid.2.2⟩
  | worker before after old next workers localStep =>
    refine ⟨valid.1, valid.2.1, ?_⟩
    have oldMember : old ∈ s.workers := by rw [workers]; simp
    have oldValid := valid.2.2 old oldMember
    intro worker member
    simp only [List.mem_append, List.mem_cons] at member
    rcases member with earlier | equal | later
    · exact valid.2.2 worker (by rw [workers]; simp [earlier])
    · subst worker
      exact ⟨local_step_valid oldValid.1 localStep,
        fun has => oldValid.2 ((local_step_root_frame localStep).mp has)⟩
    · exact valid.2.2 worker (by rw [workers]; simp [later])

inductive SystemTrace : System → System → Prop where
  | refl (s : System) : SystemTrace s s
  | next {s t u : System} : SystemTrace s t → SystemStep t u → SystemTrace s u

theorem system_trace_valid {s t : System} (valid : s.Valid) (trace : SystemTrace s t) :
    t.Valid := by
  induction trace with
  | refl => exact valid
  | next history step ih => exact system_step_valid ih step

theorem system_root_confined (s : System) (valid : s.Valid) :
    RootConfined (s.root.ledger :: s.workers.map Tracked.ledger) s.root.ledger := by
  refine ⟨by simp, ?_⟩
  intro l lm different r rm rootKey
  simp only [List.mem_cons] at lm
  rcases lm with same | member
  · exact different same
  · obtain ⟨worker, workerMember, equal⟩ := List.mem_map.mp member
    have noRoot := (valid.2.2 worker workerMember).2
    apply noRoot
    unfold HasRoot
    apply List.mem_map.mpr
    exact ⟨r, by simpa [equal] using rm, rootKey⟩

/-- Root-edge correspondence is derived from initialization and local steps. -/
theorem initialized_trace_quiet_no_root_edge (owner : Nat) (others : List Nat)
    (s : System) (trace : SystemTrace (initialSystem owner others) s)
    (quiet : probeRoot s.root.ledger = true) :
    ∀ e ∈ ledgerGraph (s.root.ledger :: s.workers.map Tracked.ledger), e.parent ≠ .root := by
  have valid := system_trace_valid (initial_system_valid owner others) trace
  exact root_edges_of_quiet _ _ (system_root_confined s valid) valid.1.1 quiet

/-- Every child ID was allocated by the ledger that owns its parent record. -/
def OwnerChildren (l : Ledger) : Prop :=
  ∀ r ∈ l.records, ∀ c ∈ r.children, ∃ serial, c.id = .work l.owner serial

theorem initial_root_owner_children (owner : Nat) : OwnerChildren (initialRoot owner) := by
  simp [OwnerChildren, initialRoot]

theorem initial_worker_owner_children (owner : Nat) : OwnerChildren (initialWorker owner) := by
  simp [OwnerChildren, initialWorker]

theorem register_owner_children (l : Ledger) (p : Id) (d : Nat) (payload : List UInt8)
    (own : OwnerChildren l) : OwnerChildren (register l p d payload).1 := by
  cases found : lookup Record.id p l.records with
  | none => simpa [register, found] using own
  | some r =>
    by_cases closed : r.phase = .closed
    · simpa [register, found, closed] using own
    · have member := (lookup_sound Record.id p l.records r found).1
      simp only [register, found, closed, ↓reduceIte, OwnerChildren]
      apply update_all Record.id p _ l.records
        (fun x => ∀ c ∈ x.children, ∃ serial, c.id = .work l.owner serial) own
      intro child childMember
      simp only [insert, List.mem_append, List.mem_singleton] at childMember
      rcases childMember with old | same
      · exact own r member child old
      · subst child
        exact ⟨l.next, rfl⟩

theorem close_owner_children (l : Ledger) (p : Id) (own : OwnerChildren l) :
    OwnerChildren (close l p) := by
  cases found : lookup Record.id p l.records with
  | none => simpa [close, found] using own
  | some r =>
    by_cases closed : r.phase = .closed
    · simpa [close, found, closed] using own
    · have member := (lookup_sound Record.id p l.records r found).1
      simp only [close, found, closed, ↓reduceIte, OwnerChildren]
      apply update_all Record.id p _ l.records
        (fun x => ∀ c ∈ x.children, ∃ serial, c.id = .work l.owner serial) own
      exact own r member

theorem retire_owner_children (l : Ledger) (p : Id) (own : OwnerChildren l) :
    OwnerChildren (retire l p) := by
  cases found : lookup Record.id p l.records with
  | none => simpa [retire, found] using own
  | some r =>
    cases parent : r.parent with
    | none => simpa [retire, found, parent] using own
    | some address =>
      by_cases ready : r.phase = .closed ∧ r.children = [] ∧ p ≠ .root
      · simp only [retire, found, parent, ready.1, ready.2.1, true_and]
        rw [if_pos ready.2.2]
        intro x member
        exact own x ((erase_retains_whole_order Record.id p l.records).mem member)
      · simpa [retire, found, parent, ready] using own

theorem ack_owner_children (l : Ledger) (p child : Id) (peer : Nat) (own : OwnerChildren l) :
    OwnerChildren (acknowledge l p child peer) := by
  cases found : lookup Record.id p l.records with
  | none => simpa [acknowledge, found] using own
  | some r =>
    cases childFound : lookup Child.id child r.children with
    | none => simpa [acknowledge, found, childFound] using own
    | some entry =>
      by_cases matched : entry.destination = peer
      · have member := (lookup_sound Record.id p l.records r found).1
        simp only [acknowledge, found, childFound, matched, ↓reduceIte, OwnerChildren]
        apply update_all Record.id p _ l.records
          (fun x => ∀ c ∈ x.children, ∃ serial, c.id = .work l.owner serial) own
        intro c cmem
        exact own r member c ((erase_retains_whole_order Child.id child r.children).mem cmem)
      · simpa [acknowledge, found, childFound, matched] using own

theorem install_owner_children (l : Ledger) (id : Id) (parent : Address) (own : OwnerChildren l) :
    OwnerChildren (install l id parent) := by
  by_cases reject : id = .root ∨ id ∈ l.records.map Record.id
  · simpa only [install, reject, ↓reduceIte] using own
  · simp only [install, reject, ↓reduceIte, OwnerChildren]
    intro r member c cmem
    simp only [insert, List.mem_append, List.mem_singleton] at member
    rcases member with old | same
    · exact own r old c cmem
    · subst r
      simp at cmem

theorem local_step_owner_children {before after : Tracked} (own : OwnerChildren before.ledger)
    (step : LocalStep before after) : OwnerChildren after.ledger := by
  cases step with
  | noop => exact own
  | action a =>
    cases a with
    | register p d payload =>
      cases result : register before.ledger p d payload with
      | mk l status =>
        cases status <;>
          simpa [Tracked.run, Tracked.register, result] using
            register_owner_children before.ledger p d payload own
    | close p => exact close_owner_children before.ledger p own
    | retire p => exact retire_owner_children before.ledger p own
    | ack p c peer => exact ack_owner_children before.ledger p c peer own
  | delivery id parent => exact install_owner_children before.ledger id parent own
  | take => simpa [OwnerChildren, (take_output_frames before.ledger).1,
      (take_output_frames before.ledger).2.2] using own

def System.Owned (s : System) : Prop :=
  OwnerChildren s.root.ledger ∧ ∀ w ∈ s.workers, OwnerChildren w.ledger

theorem initial_system_owned (owner : Nat) (others : List Nat) :
    (initialSystem owner others).Owned := by
  refine ⟨initial_root_owner_children owner, ?_⟩
  intro worker member
  obtain ⟨workerOwner, _, equal⟩ := List.mem_map.mp member
  subst worker
  exact initial_worker_owner_children workerOwner

theorem system_step_owned {s t : System} (own : s.Owned) (step : SystemStep s t) :
    t.Owned := by
  cases step with
  | root next localStep =>
    exact ⟨local_step_owner_children own.1 localStep, own.2⟩
  | worker before after old next workers localStep =>
    refine ⟨own.1, ?_⟩
    have oldMember : old ∈ s.workers := by rw [workers]; simp
    intro worker member
    simp only [List.mem_append, List.mem_cons] at member
    rcases member with earlier | equal | later
    · exact own.2 worker (by rw [workers]; simp [earlier])
    · subst worker
      exact local_step_owner_children (own.2 old oldMember) localStep
    · exact own.2 worker (by rw [workers]; simp [later])

theorem system_trace_owned {s t : System} (own : s.Owned) (trace : SystemTrace s t) :
    t.Owned := by
  induction trace with
  | refl => exact own
  | next history step ih => exact system_step_owned ih step

/-- History contains every earlier nonnegative serial; no serial was skipped or reused. -/
def CompleteHistory (history : AllocatorHistory) : Prop :=
  ∀ serial, 0 ≤ serial → serial < history.next → serial ∈ history.issued

theorem initial_complete_history (owner : Nat) :
    CompleteHistory ⟨owner, 0, []⟩ := by
  intro serial nonnegative bounded
  change serial < 0 at bounded
  omega

theorem allocate_complete_history (history : AllocatorHistory) (complete : CompleteHistory history) :
    CompleteHistory history.allocate.1 := by
  intro serial nonnegative bounded
  simp only [AllocatorHistory.allocate] at bounded ⊢
  by_cases equal : serial = history.next
  · simp [equal]
  · have older : serial < history.next := by omega
    exact List.mem_cons_of_mem _ (complete serial nonnegative older)

theorem local_step_complete_history {before after : Tracked} (complete : CompleteHistory before.history)
    (step : LocalStep before after) : CompleteHistory after.history := by
  cases step with
  | noop => exact complete
  | action a =>
    cases a with
    | register p d payload =>
      cases result : register before.ledger p d payload with
      | mk l status =>
        cases status with
        | rejected => simpa [Tracked.run, Tracked.register, result] using complete
        | registered id =>
          simpa [Tracked.run, Tracked.register, result] using
            allocate_complete_history before.history complete
    | close => exact complete
    | retire => exact complete
    | ack => exact complete
  | delivery => exact complete
  | take => exact complete

def System.Complete (s : System) : Prop :=
  CompleteHistory s.root.history ∧ ∀ w ∈ s.workers, CompleteHistory w.history

theorem initial_system_complete (owner : Nat) (others : List Nat) :
    (initialSystem owner others).Complete := by
  refine ⟨initial_complete_history owner, ?_⟩
  intro worker member
  obtain ⟨workerOwner, _, equal⟩ := List.mem_map.mp member
  subst worker
  exact initial_complete_history workerOwner

theorem system_step_complete {s t : System} (complete : s.Complete) (step : SystemStep s t) :
    t.Complete := by
  cases step with
  | root next localStep =>
    exact ⟨local_step_complete_history complete.1 localStep, complete.2⟩
  | worker before after old next workers localStep =>
    refine ⟨complete.1, ?_⟩
    have oldMember : old ∈ s.workers := by rw [workers]; simp
    intro worker member
    simp only [List.mem_append, List.mem_cons] at member
    rcases member with earlier | equal | later
    · exact complete.2 worker (by rw [workers]; simp [earlier])
    · subst worker
      exact local_step_complete_history (complete.2 old oldMember) localStep
    · exact complete.2 worker (by rw [workers]; simp [later])

theorem system_trace_complete {s t : System} (complete : s.Complete) (trace : SystemTrace s t) :
    t.Complete := by
  induction trace with
  | refl => exact complete
  | next history step ih => exact system_step_complete ih step

theorem ledger_edge_has_history (t : Tracked) (valid : t.Valid) (own : OwnerChildren t.ledger)
    (complete : CompleteHistory t.history) (edge : Edge) (member : edge ∈ ledgerEdges t.ledger) :
    ∃ serial, edge.child = .work t.history.owner serial ∧ serial ∈ t.history.issued := by
  obtain ⟨r, rmem, child, cmem, equal⟩ := (edge_membership t.ledger edge).mp member
  obtain ⟨serial, childId⟩ := own r rmem child cmem
  have childValid := ((valid.1.2.2 r rmem).2 child cmem)
  have bounds : 0 ≤ serial ∧ serial < t.ledger.next := by
    simpa [ChildValid, childId] using childValid
  refine ⟨serial, ?_, ?_⟩
  · simp [equal, childId, valid.2.2.1]
  · apply complete serial bounds.1
    simpa [valid.2.2.2] using bounds.2

theorem ledger_next_edge_fresh (t : Tracked) (valid : t.Valid) (edge : Edge)
    (member : edge ∈ ledgerEdges t.ledger) : edge.child ≠ .work t.ledger.owner t.ledger.next := by
  obtain ⟨r, rmem, child, cmem, equal⟩ := (edge_membership t.ledger edge).mp member
  intro collision
  have id : child.id = .work t.ledger.owner t.ledger.next := by simpa [equal] using collision
  have childValid := (valid.1.2.2 r rmem).2 child cmem
  simp [ChildValid, id] at childValid

theorem local_step_owner_frame {before after : Tracked} (step : LocalStep before after) :
    after.ledger.owner = before.ledger.owner := by
  cases step with
  | noop => rfl
  | action a =>
    cases a with
    | register p d payload =>
      have accounting := registration_accounting before.ledger p d payload
      cases result : register before.ledger p d payload with
      | mk l status =>
        cases status with
        | rejected =>
          simp only [result] at accounting
          simp [Tracked.run, Tracked.register, result, accounting]
        | registered id =>
          simp only [result] at accounting
          simp [Tracked.run, Tracked.register, result, accounting.2.1]
    | close p => exact (close_counter_frame before.ledger p).1
    | retire p => exact (retire_counter_frame before.ledger p).1
    | ack p c peer => exact (acknowledgement_counter_frame before.ledger p c peer).1
  | delivery id parent => exact (install_frames before.ledger id parent).1
  | take => exact (take_output_frames before.ledger).1

def System.owners (s : System) : List Nat :=
  s.root.ledger.owner :: s.workers.map (fun w => w.ledger.owner)

theorem system_step_owners {s t : System} (step : SystemStep s t) : t.owners = s.owners := by
  cases step with
  | root next localStep =>
    simp [System.owners, local_step_owner_frame localStep]
  | worker before after old next workers localStep =>
    simp [System.owners, workers, local_step_owner_frame localStep]

theorem system_trace_owners {s t : System} (trace : SystemTrace s t) : t.owners = s.owners := by
  induction trace with
  | refl => rfl
  | next history step ih => exact (system_step_owners step).trans ih

theorem initialized_owners (owner : Nat) (others : List Nat) :
    (initialSystem owner others).owners = owner :: others := by
  simp [System.owners, initialSystem, trackedRoot, trackedWorker, initialRoot, initialWorker,
    List.map_map, Function.comp_def]

def trackedGraph (workers : List Tracked) : List Edge :=
  workers.flatMap (fun w => ledgerEdges w.ledger)

theorem tracked_graph_member (workers : List Tracked) (edge : Edge) :
    edge ∈ trackedGraph workers ↔ ∃ w ∈ workers, edge ∈ ledgerEdges w.ledger := by
  simp [trackedGraph]

theorem unique_owner_injective (workers : List Tracked) (a b : Tracked)
    (unique : (workers.map (fun w => w.ledger.owner)).Nodup)
    (amem : a ∈ workers) (bmem : b ∈ workers)
    (same : a.ledger.owner = b.ledger.owner) : a = b := by
  induction workers with
  | nil => simp at amem
  | cons first rest ih =>
    have parts : first.ledger.owner ∉ rest.map (fun w => w.ledger.owner) ∧
        (rest.map (fun w => w.ledger.owner)).Nodup := by simpa using unique
    rcases List.mem_cons.mp amem with aFirst | aRest
    · rcases List.mem_cons.mp bmem with bFirst | bRest
      · exact aFirst.trans bFirst.symm
      · subst a
        exact False.elim (parts.1 (List.mem_map.mpr ⟨b, bRest, same.symm⟩))
    · rcases List.mem_cons.mp bmem with bFirst | bRest
      · subst b
        exact False.elim (parts.1 (List.mem_map.mpr ⟨a, aRest, same⟩))
      · exact ih parts.2 aRest bRest

theorem global_allocator_next_fresh (workers : List Tracked) (current : Tracked)
    (unique : (workers.map (fun w => w.ledger.owner)).Nodup)
    (currentMember : current ∈ workers)
    (valid : ∀ w ∈ workers, w.Valid)
    (own : ∀ w ∈ workers, OwnerChildren w.ledger)
    (complete : ∀ w ∈ workers, CompleteHistory w.history) :
    ∀ edge ∈ trackedGraph workers, edge.child ≠ .work current.ledger.owner current.ledger.next := by
  intro edge member collision
  obtain ⟨worker, workerMember, edgeMember⟩ := (tracked_graph_member workers edge).mp member
  by_cases sameOwner : worker.ledger.owner = current.ledger.owner
  · have same := unique_owner_injective workers worker current unique workerMember currentMember sameOwner
    subst worker
    exact ledger_next_edge_fresh current (valid current currentMember) edge edgeMember collision
  · obtain ⟨serial, childId, _⟩ :=
      ledger_edge_has_history worker (valid worker workerMember) (own worker workerMember)
        (complete worker workerMember) edge edgeMember
    have ownerEq : worker.history.owner = current.ledger.owner := by
      rw [childId] at collision
      exact (Id.work.inj collision).1
    exact sameOwner ((valid worker workerMember).2.2.1.symm.trans ownerEq)

/-- Global freshness follows from distinct initial owners and the local trace invariants. -/
theorem initialized_trace_global_fresh (owner : Nat) (others : List Nat)
    (distinct : (owner :: others).Nodup) (s : System)
    (trace : SystemTrace (initialSystem owner others) s) (current : Tracked)
    (currentMember : current ∈ s.root :: s.workers) :
    ∀ edge ∈ trackedGraph (s.root :: s.workers),
      edge.child ≠ .work current.ledger.owner current.ledger.next := by
  have valid := system_trace_valid (initial_system_valid owner others) trace
  have own := system_trace_owned (initial_system_owned owner others) trace
  have complete := system_trace_complete (initial_system_complete owner others) trace
  have unique : ((s.root :: s.workers).map (fun w => w.ledger.owner)).Nodup := by
    change s.owners.Nodup
    rw [system_trace_owners trace, initialized_owners]
    exact distinct
  apply global_allocator_next_fresh _ current unique currentMember
  · intro w member
    rcases List.mem_cons.mp member with same | rest
    · subst w; exact valid.1
    · exact (valid.2.2 w rest).1
  · intro w member
    rcases List.mem_cons.mp member with same | rest
    · subst w; exact own.1
    · exact own.2 w rest
  · intro w member
    rcases List.mem_cons.mp member with same | rest
    · subst w; exact complete.1
    · exact complete.2 w rest

/-- Acknowledgement preserves the order and whole identity of every remaining edge. -/
theorem acknowledge_edges_sublist (l : Ledger) (p child : Id) (peer : Nat) :
    (ledgerEdges (acknowledge l p child peer)).Sublist (ledgerEdges l) := by
  cases found : lookup Record.id p l.records with
  | none => simp [acknowledge, found]
  | some r =>
    cases childFound : lookup Child.id child r.children with
    | none => simp [acknowledge, found, childFound]
    | some entry =>
      by_cases matched : entry.destination = peer
      · obtain ⟨before, after, split, _, updated⟩ := lookup_update_decompose Record.id p
          { r with children := (remove Child.id child r.children).1 } l.records r found
        simp only [acknowledge, found, childFound, matched, ↓reduceIte]
        rw [updated]
        have sub := (erase_retains_whole_order Child.id child r.children).map
          (fun (c : Child) => (⟨r.id, c.id, c.destination⟩ : Edge))
        have lifted := (sub.append_right (after.flatMap recordEdges)).append_left
          (before.flatMap recordEdges)
        simpa [ledgerEdges, recordEdges, split, List.append_assoc] using lifted
      · simp [acknowledge, found, childFound, matched]

theorem register_edges_perm (l : Ledger) (p : Id) (d : Nat) (payload : List UInt8)
    (r : Record) (found : lookup Record.id p l.records = some r)
    (opened : r.phase = .open) :
    (ledgerEdges (register l p d payload).1).Perm
      (ledgerEdges l ++ [⟨p, .work l.owner l.next, d⟩]) := by
  have key := (lookup_sound Record.id p l.records r found).2
  obtain ⟨before, after, split, _, updated⟩ := lookup_update_decompose Record.id p
    { r with children := insert ⟨.work l.owner l.next, d⟩ r.children } l.records r found
  rw [register_open l p d payload r found opened]
  dsimp
  rw [updated]
  let e : Edge := ⟨p, .work l.owner l.next, d⟩
  let pre := before.flatMap recordEdges ++ recordEdges r
  let post := after.flatMap recordEdges
  have perm := (List.perm_middle (a := e) (l₁ := pre) (l₂ := post)).trans
    (List.perm_append_singleton e (pre ++ post)).symm
  simpa [ledgerEdges, recordEdges, split, insert, key, e, pre, post, List.append_assoc] using perm

theorem erase_empty_record_edges (p : Id) (records : List Record) (r : Record)
    (found : lookup Record.id p records = some r) (empty : r.children = []) :
    (erase Record.id p records).flatMap recordEdges = records.flatMap recordEdges := by
  induction records with
  | nil => simp [lookup] at found
  | cons head tail ih =>
    by_cases same : head.id = p
    · simp [lookup, same] at found
      subst r
      simp [erase, same, recordEdges, empty]
    · simp [lookup, same] at found
      simp [erase, same, ih found]

theorem retire_edges_equal (l : Ledger) (p : Id) :
    ledgerEdges (retire l p) = ledgerEdges l := by
  cases found : lookup Record.id p l.records with
  | none => simp [retire, found]
  | some r =>
    cases parent : r.parent with
    | none => simp [retire, found, parent]
    | some address =>
      by_cases ready : r.phase = .closed ∧ r.children = [] ∧ p ≠ .root
      · simp only [retire, found, parent, ready.1, ready.2.1, true_and]
        rw [if_pos ready.2.2]
        simpa [ledgerEdges, remove_sequence] using
          erase_empty_record_edges p l.records r found ready.2.1
      · simp [retire, found, parent, ready]

theorem close_edges_equal (l : Ledger) (p : Id) : ledgerEdges (close l p) = ledgerEdges l := by
  cases found : lookup Record.id p l.records with
  | none => simp [close, found]
  | some r =>
    by_cases closed : r.phase = .closed
    · simp [close, found, closed]
    · obtain ⟨before, after, split, _, updated⟩ :=
        lookup_update_decompose Record.id p { r with phase := .closed } l.records r found
      simp only [close, found, closed, ↓reduceIte]
      rw [updated]
      simp [ledgerEdges, recordEdges, split]

theorem install_edges_equal (l : Ledger) (id : Id) (parent : Address) :
    ledgerEdges (install l id parent) = ledgerEdges l := by
  by_cases reject : id = .root ∨ id ∈ l.records.map Record.id
  · simp only [install, reject, ↓reduceIte]
  · simp only [install, reject, ↓reduceIte]
    simp [ledgerEdges, recordEdges, insert]

inductive EdgeChange (before after : Tracked) : Prop where
  | remove : (ledgerEdges after.ledger).Sublist (ledgerEdges before.ledger) → EdgeChange before after
  | add (edge : Edge) : edge.child = .work before.ledger.owner before.ledger.next →
      (ledgerEdges after.ledger).Perm (ledgerEdges before.ledger ++ [edge]) → EdgeChange before after

theorem local_step_edge_change {before after : Tracked} (step : LocalStep before after) :
    EdgeChange before after := by
  cases step with
  | noop => exact .remove (List.Sublist.refl _)
  | action action =>
    cases action with
    | register p d payload =>
      cases found : lookup Record.id p before.ledger.records with
      | none =>
        have rejected := register_missing before.ledger p d payload found
        apply EdgeChange.remove
        simp [Tracked.run, Tracked.register, rejected]
      | some r =>
        cases phase : r.phase with
        | closed =>
          have rejected := register_closed before.ledger p d payload r found phase
          apply EdgeChange.remove
          simp [Tracked.run, Tracked.register, rejected]
        | «open» =>
          have result := register_open before.ledger p d payload r found phase
          refine EdgeChange.add ⟨p, .work before.ledger.owner before.ledger.next, d⟩ rfl ?_
          simpa [Tracked.run, Tracked.register, result] using
            register_edges_perm before.ledger p d payload r found phase
    | close p =>
      apply EdgeChange.remove
      simp only [Tracked.run, close_edges_equal]
      exact List.Sublist.refl _
    | retire p =>
      apply EdgeChange.remove
      simp only [Tracked.run, retire_edges_equal]
      exact List.Sublist.refl _
    | ack p child peer =>
      exact EdgeChange.remove (acknowledge_edges_sublist before.ledger p child peer)
  | delivery id parent =>
    apply EdgeChange.remove
    simp only [install_edges_equal]
    exact List.Sublist.refl _
  | take =>
    apply EdgeChange.remove
    simp only [ledgerEdges, (take_output_frames before.ledger).2.2]
    exact List.Sublist.refl _

theorem replaced_graph_preserves_unique (before after : List Tracked) (old next : Tracked)
    (unique : Unique Edge.child (trackedGraph (before ++ old :: after)))
    (change : EdgeChange old next)
    (fresh : ∀ edge ∈ trackedGraph (before ++ old :: after),
      edge.child ≠ .work old.ledger.owner old.ledger.next) :
    Unique Edge.child (trackedGraph (before ++ next :: after)) := by
  let pre := trackedGraph before
  let post := trackedGraph after
  cases change with
  | remove sub =>
    have whole := (sub.append_right post).append_left pre
    have source : Unique Edge.child (pre ++ (ledgerEdges old.ledger ++ post)) := by
      simpa [trackedGraph, pre, post, List.append_assoc] using unique
    have dest := (whole.map Edge.child).nodup source
    simpa [Unique, trackedGraph, pre, post, List.append_assoc] using dest
  | add edge edgeId perm =>
    have noCollision : edge.child ∉ (trackedGraph (before ++ old :: after)).map Edge.child := by
      intro member
      obtain ⟨oldEdge, oldMember, equal⟩ := List.mem_map.mp member
      apply fresh oldEdge oldMember
      exact equal.trans edgeId
    have appended := insert_unique Edge.child edge (trackedGraph (before ++ old :: after)) unique noCollision
    have middle := (perm.append_right post).append_left pre
    have move := (List.perm_middle (a := edge) (l₁ := pre ++ ledgerEdges old.ledger)
      (l₂ := post)).trans (List.perm_append_singleton edge (pre ++ ledgerEdges old.ledger ++ post)).symm
    have whole := middle.trans (by simpa [List.append_assoc] using move)
    have source : Unique Edge.child (pre ++ (ledgerEdges old.ledger ++ (post ++ [edge]))) := by
      simpa [insert, trackedGraph, pre, post, List.append_assoc] using appended
    have dest := (whole.map Edge.child).symm.nodup source
    simpa [Unique, trackedGraph, pre, post, List.append_assoc] using dest

theorem initial_graph_empty (owner : Nat) (others : List Nat) :
    trackedGraph ((initialSystem owner others).root :: (initialSystem owner others).workers) = [] := by
  simp [trackedGraph, initialSystem, trackedRoot, initialRoot, ledgerEdges, recordEdges,
    List.flatMap_map, trackedWorker, initialWorker]

theorem initialized_trace_graph_unique (owner : Nat) (others : List Nat)
    (distinct : (owner :: others).Nodup) {s : System}
    (trace : SystemTrace (initialSystem owner others) s) :
    Unique Edge.child (trackedGraph (s.root :: s.workers)) := by
  induction trace with
  | refl => simp [initial_graph_empty, Unique]
  | @next current successor history step ih =>
    cases step with
    | root next localStep =>
      have member : current.root ∈ current.root :: current.workers := by simp
      have fresh := initialized_trace_global_fresh owner others distinct current history current.root member
      have nextUnique := replaced_graph_preserves_unique [] current.workers current.root next
        (by simpa using ih) (local_step_edge_change localStep) (by simpa using fresh)
      simpa using nextUnique
    | worker before after old next workers localStep =>
      have member : old ∈ current.root :: current.workers := by simp [workers]
      have fresh := initialized_trace_global_fresh owner others distinct current history old member
      have nextUnique := replaced_graph_preserves_unique (current.root :: before) after old next
        (by simpa [workers] using ih) (local_step_edge_change localStep) (by simpa [workers] using fresh)
      simpa using nextUnique

end Ash.NetworkLedger.Coupling
