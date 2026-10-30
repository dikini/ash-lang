import NetworkLedgerCollections

/-
Functional local ledger transitions. A normal returned value is modeled here;
control completion, Core admission, transport and cyclic-value exclusion must
be established by separate checks and correspondence.
-/
namespace Ash.NetworkLedger

inductive Phase where
  | open | closed
  deriving DecidableEq, Repr

structure Address where
  worker : Nat
  id : Id
  deriving DecidableEq, Repr

structure Child where
  id : Id
  destination : Nat
  deriving DecidableEq, Repr

structure Record where
  id : Id
  parent : Option Address
  phase : Phase
  children : List Child
  deriving DecidableEq, Repr

inductive Output where
  | work (id : Id) (parent : Address) (destination : Nat) (payload : List UInt8)
  | ack (parent : Address) (child : Id)
  deriving DecidableEq, Repr

structure Ledger where
  owner : Nat
  next : Int
  records : List Record
  outputs : List Output
  deriving DecidableEq, Repr

inductive Registration where
  | rejected | registered (id : Id)
  deriving DecidableEq, Repr

def initialRoot (owner : Nat) : Ledger :=
  ⟨owner, 0, [⟨.root, none, .open, []⟩], []⟩

def initialWorker (owner : Nat) : Ledger := ⟨owner, 0, [], []⟩

def register (l : Ledger) (parent : Id) (destination : Nat) (payload : List UInt8) :
    Ledger × Registration :=
  match lookup Record.id parent l.records with
  | none => (l, .rejected)
  | some record =>
    if record.phase = .closed then (l, .rejected)
    else
      let child := Id.work l.owner l.next
      let updated := { record with children := insert ⟨child, destination⟩ record.children }
      let successor := { l with
        next := l.next + 1
        records := update Record.id parent updated l.records
        outputs := l.outputs ++ [.work child ⟨l.owner, parent⟩ destination payload] }
      (successor, .registered child)

def close (l : Ledger) (q : Id) : Ledger :=
  match lookup Record.id q l.records with
  | none => l
  | some record =>
    if record.phase = .closed then l
    else { l with records := update Record.id q { record with phase := .closed } l.records }

def retire (l : Ledger) (q : Id) : Ledger :=
  match lookup Record.id q l.records with
  | none => l
  | some record =>
    match record.parent with
    | none => l
    | some parent =>
      if record.phase = .closed ∧ record.children = [] ∧ q ≠ .root then
        { l with records := (remove Record.id q l.records).1
                 outputs := l.outputs ++ [.ack parent q] }
      else l

def acknowledge (l : Ledger) (parent child : Id) (peer : Nat) : Ledger :=
  match lookup Record.id parent l.records with
  | none => l
  | some record =>
    match lookup Child.id child record.children with
    | none => l
    | some entry =>
      if entry.destination = peer then
        let updated := { record with children := (remove Child.id child record.children).1 }
        { l with records := update Record.id parent updated l.records }
      else l

def ChildValid (owner : Nat) (next : Int) (child : Child) : Prop :=
  match child.id with
  | .root => False
  | .work allocator serial => allocator = owner → 0 ≤ serial ∧ serial < next

def RecordValid (owner : Nat) (next : Int) (record : Record) : Prop :=
  Unique Child.id record.children ∧ ∀ child ∈ record.children, ChildValid owner next child

def probeRoot (l : Ledger) : Bool :=
  match lookup Record.id .root l.records with
  | none => false
  | some root => decide (root.phase = .closed ∧ root.children = [])

theorem quiet_probe_is_closed_empty (l : Ledger) (quiet : probeRoot l = true) :
    ∃ root, lookup Record.id .root l.records = some root ∧
      root.phase = .closed ∧ root.children = [] := by
  unfold probeRoot at quiet
  cases found : lookup Record.id .root l.records with
  | none => simp [found] at quiet
  | some root =>
    have result : root.phase = .closed ∧ root.children = [] := by simpa [found] using quiet
    exact ⟨root, rfl, result⟩

def LocalInvariant (l : Ledger) : Prop :=
  0 ≤ l.next ∧ Unique Record.id l.records ∧ ∀ r ∈ l.records, RecordValid l.owner l.next r

theorem initial_root_invariant (owner : Nat) : LocalInvariant (initialRoot owner) := by
  simp [LocalInvariant, RecordValid, initialRoot, Unique]

theorem initial_worker_invariant (owner : Nat) : LocalInvariant (initialWorker owner) := by
  simp [LocalInvariant, initialWorker, Unique]

theorem register_missing (l : Ledger) (p : Id) (d : Nat) (payload : List UInt8)
    (missing : lookup Record.id p l.records = none) :
    register l p d payload = (l, .rejected) := by
  simp [register, missing]

theorem register_closed (l : Ledger) (p : Id) (d : Nat) (payload : List UInt8)
    (record : Record) (found : lookup Record.id p l.records = some record)
    (closed : record.phase = .closed) : register l p d payload = (l, .rejected) := by
  simp [register, found, closed]

theorem register_open (l : Ledger) (p : Id) (d : Nat) (payload : List UInt8)
    (record : Record) (found : lookup Record.id p l.records = some record)
    (opened : record.phase = .open) :
    register l p d payload =
      ({ l with next := l.next + 1
                records := update Record.id p
                  { record with children := insert ⟨.work l.owner l.next, d⟩ record.children }
                  l.records
                outputs := l.outputs ++ [.work (.work l.owner l.next) ⟨l.owner, p⟩ d payload] },
        .registered (.work l.owner l.next)) := by
  simp [register, found, opened]

theorem retire_missing (l : Ledger) (q : Id) (h : lookup Record.id q l.records = none) :
    retire l q = l := by simp [retire, h]

theorem retire_root (l : Ledger) : retire l .root = l := by
  simp only [retire]
  cases h : lookup Record.id Id.root l.records with
  | none => rfl
  | some r =>
    cases hp : r.parent with
    | none => simp [hp]
    | some p => simp [hp]

theorem acknowledge_missing_parent (l : Ledger) (p c : Id) (peer : Nat)
    (h : lookup Record.id p l.records = none) : acknowledge l p c peer = l := by
  simp [acknowledge, h]

theorem acknowledge_missing_child (l : Ledger) (p c : Id) (peer : Nat) (r : Record)
    (parent : lookup Record.id p l.records = some r)
    (child : lookup Child.id c r.children = none) : acknowledge l p c peer = l := by
  simp [acknowledge, parent, child]

theorem acknowledge_wrong_peer (l : Ledger) (p c : Id) (peer : Nat) (r : Record) (ch : Child)
    (parent : lookup Record.id p l.records = some r)
    (child : lookup Child.id c r.children = some ch) (wrong : ch.destination ≠ peer) :
    acknowledge l p c peer = l := by
  simp [acknowledge, parent, child, wrong]

theorem child_valid_successor (owner : Nat) (n : Int) (c : Child)
    (valid : ChildValid owner n c) : ChildValid owner (n + 1) c := by
  cases id : c.id with
  | root => simp [ChildValid, id] at valid
  | work allocator serial =>
    simp only [ChildValid, id] at valid ⊢
    intro eq
    have bounds := valid eq
    omega

theorem new_child_fresh (owner : Nat) (n : Int) (children : List Child)
    (valid : ∀ c ∈ children, ChildValid owner n c) :
    Id.work owner n ∉ children.map Child.id := by
  intro member
  obtain ⟨c, cmem, keyeq⟩ := List.mem_map.mp member
  have cv := valid c cmem
  simp [ChildValid, keyeq] at cv

theorem record_valid_successor (owner : Nat) (n : Int) (r : Record)
    (valid : RecordValid owner n r) : RecordValid owner (n + 1) r := by
  refine ⟨valid.1, ?_⟩
  intro child member
  exact child_valid_successor owner n child (valid.2 child member)

theorem registered_record_valid (owner : Nat) (n : Int) (r : Record) (dest : Nat)
    (nonnegative : 0 ≤ n) (valid : RecordValid owner n r) :
    RecordValid owner (n + 1)
      { r with children := insert ⟨.work owner n, dest⟩ r.children } := by
  refine ⟨?_, ?_⟩
  · exact insert_unique Child.id _ _ valid.1 (new_child_fresh owner n r.children valid.2)
  · intro child member
    simp only [insert, List.mem_append, List.mem_singleton] at member
    rcases member with old | new
    · exact child_valid_successor owner n child (valid.2 child old)
    · subst child
      simp [ChildValid, nonnegative]
      omega

theorem registration_preserves_invariant (l : Ledger) (p : Id) (d : Nat)
    (payload : List UInt8) (invariant : LocalInvariant l) :
    LocalInvariant (register l p d payload).1 := by
  rcases invariant with ⟨nonnegative, unique, recordsValid⟩
  unfold register
  cases found : lookup Record.id p l.records with
  | none => exact ⟨nonnegative, unique, recordsValid⟩
  | some r =>
    by_cases closed : r.phase = .closed
    · simp only [closed, ↓reduceIte]
      exact ⟨nonnegative, unique, recordsValid⟩
    · simp only [closed, ↓reduceIte]
      have matchKey := (lookup_sound Record.id p l.records r found).2
      have member := (lookup_sound Record.id p l.records r found).1
      have valid := recordsValid r member
      refine ⟨by dsimp; omega, ?_, ?_⟩
      · exact update_unique Record.id p _ l.records matchKey unique
      · apply update_all Record.id p _ l.records (RecordValid l.owner (l.next + 1))
        · intro x xmem
          exact record_valid_successor l.owner l.next x (recordsValid x xmem)
        · exact registered_record_valid l.owner l.next r d nonnegative valid

theorem closure_preserves_invariant (l : Ledger) (q : Id) (invariant : LocalInvariant l) :
    LocalInvariant (close l q) := by
  rcases invariant with ⟨nonnegative, unique, recordsValid⟩
  unfold close
  cases found : lookup Record.id q l.records with
  | none => exact ⟨nonnegative, unique, recordsValid⟩
  | some r =>
    by_cases closed : r.phase = .closed
    · simp only [closed, ↓reduceIte]
      exact ⟨nonnegative, unique, recordsValid⟩
    · simp only [closed, ↓reduceIte]
      have matchKey := (lookup_sound Record.id q l.records r found).2
      have member := (lookup_sound Record.id q l.records r found).1
      refine ⟨nonnegative, update_unique Record.id q _ l.records matchKey unique, ?_⟩
      apply update_all Record.id q _ l.records (RecordValid l.owner l.next) recordsValid
      exact recordsValid r member

theorem record_removal_valid (owner : Nat) (n : Int) (r : Record) (q : Id)
    (valid : RecordValid owner n r) :
    RecordValid owner n { r with children := (remove Child.id q r.children).1 } := by
  refine ⟨?_, ?_⟩
  · rw [remove_sequence]
    exact erase_finite_unique Child.id q r.children valid.1
  · intro child member
    exact valid.2 child ((erase_retains_whole_order Child.id q r.children).mem member)

theorem registration_other_record_frame (l : Ledger) (p other : Id) (d : Nat)
    (payload : List UInt8) (different : other ≠ p) :
    lookup Record.id other (register l p d payload).1.records = lookup Record.id other l.records := by
  simp only [register]
  cases found : lookup Record.id p l.records with
  | none => rfl
  | some record =>
    by_cases closed : record.phase = .closed
    · simp [closed]
    · have key := (lookup_sound Record.id p l.records record found).2
      simp only [closed, ↓reduceIte]
      exact update_other_lookup Record.id other p _ l.records different key

theorem close_other_record_frame (l : Ledger) (q other : Id) (different : other ≠ q) :
    lookup Record.id other (close l q).records = lookup Record.id other l.records := by
  simp only [close]
  cases found : lookup Record.id q l.records with
  | none => rfl
  | some record =>
    by_cases closed : record.phase = .closed
    · simp [closed]
    · have key := (lookup_sound Record.id q l.records record found).2
      simp only [closed, ↓reduceIte]
      exact update_other_lookup Record.id other q _ l.records different key

theorem retirement_preserves_invariant (l : Ledger) (q : Id) (invariant : LocalInvariant l) :
    LocalInvariant (retire l q) := by
  rcases invariant with ⟨nonnegative, unique, recordsValid⟩
  cases found : lookup Record.id q l.records with
  | none => simpa [retire, found, LocalInvariant] using And.intro nonnegative ⟨unique, recordsValid⟩
  | some r =>
    cases parent : r.parent with
    | none =>
      simpa [retire, found, parent, LocalInvariant] using And.intro nonnegative ⟨unique, recordsValid⟩
    | some address =>
      by_cases ready : r.phase = .closed ∧ r.children = [] ∧ q ≠ .root
      · simp only [retire, found, parent, ready.1, ready.2.1, true_and]
        rw [if_pos ready.2.2]
        refine ⟨nonnegative, ?_, ?_⟩
        · rw [remove_sequence]
          exact erase_finite_unique Record.id q l.records unique
        · intro record member
          exact recordsValid record ((erase_retains_whole_order Record.id q l.records).mem member)
      · simpa [retire, found, parent, ready, LocalInvariant] using
          And.intro nonnegative ⟨unique, recordsValid⟩

theorem acknowledgement_preserves_invariant (l : Ledger) (p c : Id) (peer : Nat)
    (invariant : LocalInvariant l) : LocalInvariant (acknowledge l p c peer) := by
  rcases invariant with ⟨nonnegative, unique, recordsValid⟩
  cases found : lookup Record.id p l.records with
  | none =>
    simpa [acknowledge, found, LocalInvariant] using And.intro nonnegative ⟨unique, recordsValid⟩
  | some r =>
    cases foundChild : lookup Child.id c r.children with
    | none =>
      simpa [acknowledge, found, foundChild, LocalInvariant] using
        And.intro nonnegative ⟨unique, recordsValid⟩
    | some child =>
      by_cases peerMatches : child.destination = peer
      · simp only [acknowledge, found, foundChild, peerMatches, ↓reduceIte]
        have matchKey := (lookup_sound Record.id p l.records r found).2
        have member := (lookup_sound Record.id p l.records r found).1
        refine ⟨nonnegative, update_unique Record.id p _ l.records matchKey unique, ?_⟩
        apply update_all Record.id p _ l.records (RecordValid l.owner l.next) recordsValid
        exact record_removal_valid l.owner l.next r c (recordsValid r member)
      · simpa [acknowledge, found, foundChild, peerMatches, LocalInvariant] using
          And.intro nonnegative ⟨unique, recordsValid⟩

theorem acknowledgement_idempotent (l : Ledger) (p c : Id) (peer : Nat)
    (invariant : LocalInvariant l) :
    acknowledge (acknowledge l p c peer) p c peer = acknowledge l p c peer := by
  cases found : lookup Record.id p l.records with
  | none => simp [acknowledge, found]
  | some r =>
    cases foundChild : lookup Child.id c r.children with
    | none => simp [acknowledge, found, foundChild]
    | some child =>
      by_cases matched : child.destination = peer
      · have rmem := (lookup_sound Record.id p l.records r found).1
        have rkey := (lookup_sound Record.id p l.records r found).2
        have childrenUnique := (invariant.2.2 r rmem).1
        let newer := { r with children := (remove Child.id c r.children).1 }
        have lookupNew : lookup Record.id p (update Record.id p newer l.records) = some newer :=
          lookup_update Record.id p newer l.records r found rkey
        have absent : c ∉ newer.children.map Child.id := by
          dsimp [newer]
          rw [remove_sequence]
          exact erase_excludes_key Child.id c r.children childrenUnique
        have noChild : lookup Child.id c newer.children = none :=
          lookup_none_of_absent Child.id c newer.children absent
        simp only [acknowledge, found, foundChild, matched, ↓reduceIte]
        change (match lookup Record.id p (update Record.id p newer l.records) with
          | none => _
          | some rr =>
            match lookup Child.id c rr.children with
            | none => _
            | some entry =>
              if entry.destination = peer then _ else _) = _
        rw [lookupNew]
        simp only [noChild]
      · simp [acknowledge, found, foundChild, matched]

/- The ghost history records issued serials even after their records retire. -/
structure AllocatorHistory where
  owner : Nat
  next : Int
  issued : List Int
  deriving DecidableEq, Repr

def AllocatorHistory.Valid (a : AllocatorHistory) : Prop :=
  0 ≤ a.next ∧ a.issued.Nodup ∧ ∀ serial ∈ a.issued, 0 ≤ serial ∧ serial < a.next

def AllocatorHistory.allocate (a : AllocatorHistory) : AllocatorHistory × Id :=
  ({ a with next := a.next + 1, issued := a.next :: a.issued }, .work a.owner a.next)

theorem allocator_initial_valid (owner : Nat) :
    (AllocatorHistory.mk owner 0 []).Valid := by
  simp [AllocatorHistory.Valid]

theorem allocator_fresh (a : AllocatorHistory) (valid : a.Valid) :
    a.next ∉ a.issued := by
  intro member
  have bounds := valid.2.2 a.next member
  omega

theorem allocator_successor (a : AllocatorHistory) (valid : a.Valid) :
    a.allocate.1.Valid ∧ a.allocate.2 = .work a.owner a.next := by
  rcases valid with ⟨nonnegative, unique, bounds⟩
  refine ⟨?_, rfl⟩
  simp only [AllocatorHistory.Valid, AllocatorHistory.allocate, List.nodup_cons]
  refine ⟨by omega, ⟨?_, unique⟩, ?_⟩
  · intro member
    have old := bounds a.next member
    omega
  · intro serial member
    simp only [List.mem_cons] at member
    rcases member with equal | old
    · subst serial; omega
    · have oldBounds := bounds serial old
      omega

theorem allocators_disjoint (left right : Nat) (a b : Int) (different : left ≠ right) :
    Id.work left a ≠ Id.work right b := by
  intro equal
  cases equal
  exact different rfl

theorem registration_accounting (l : Ledger) (p : Id) (d : Nat) (payload : List UInt8) :
    (match register l p d payload with
    | (next, .rejected) => next = l
    | (next, .registered id) => id = .work l.owner l.next ∧
        next.owner = l.owner ∧ next.next = l.next + 1) := by
  simp only [register]
  cases found : lookup Record.id p l.records with
  | none => simp
  | some r =>
    by_cases closed : r.phase = .closed
    · simp [closed]
    · simp [closed]

structure Tracked where
  ledger : Ledger
  history : AllocatorHistory
  deriving Repr

def Tracked.Valid (t : Tracked) : Prop :=
  LocalInvariant t.ledger ∧ t.history.Valid ∧
  t.history.owner = t.ledger.owner ∧ t.history.next = t.ledger.next

def Tracked.register (t : Tracked) (p : Id) (d : Nat) (payload : List UInt8) : Tracked × Registration :=
  match Ash.NetworkLedger.register t.ledger p d payload with
  | (next, .rejected) => (⟨next, t.history⟩, .rejected)
  | (next, .registered id) => (⟨next, t.history.allocate.1⟩, .registered id)

theorem tracked_registration_preserves (t : Tracked) (p : Id) (d : Nat) (payload : List UInt8)
    (valid : t.Valid) : (t.register p d payload).1.Valid ∧
      (match (t.register p d payload).2 with
       | .rejected => (t.register p d payload).1 = t
       | .registered id => id = .work t.history.owner t.history.next ∧
           t.history.next ∉ t.history.issued) := by
  have localPres := registration_preserves_invariant t.ledger p d payload valid.1
  have accounting := registration_accounting t.ledger p d payload
  cases result : register t.ledger p d payload with
  | mk next status =>
    cases status with
    | rejected =>
      simp only [result] at accounting localPres
      simp only [Tracked.register, result]
      simp only [Tracked.Valid]
      subst next
      simpa [Tracked.Valid] using valid
    | registered id =>
      simp only [result] at accounting localPres
      simp only [Tracked.register, result, Tracked.Valid]
      rcases accounting with ⟨identity, owner, nextEq⟩
      have allocated := allocator_successor t.history valid.2.1
      refine ⟨⟨localPres, allocated.1, ?_, ?_⟩, ?_, allocator_fresh t.history valid.2.1⟩
      · simpa [AllocatorHistory.allocate, owner] using valid.2.2.1
      · simp only [AllocatorHistory.allocate]
        simp [valid.2.2.2, nextEq]
      · simpa [valid.2.2.1, valid.2.2.2] using identity

theorem close_counter_frame (l : Ledger) (q : Id) :
    (close l q).owner = l.owner ∧ (close l q).next = l.next := by
  simp only [close]
  split <;> try simp_all
  split <;> try simp_all

theorem retire_counter_frame (l : Ledger) (q : Id) :
    (retire l q).owner = l.owner ∧ (retire l q).next = l.next := by
  simp only [retire]
  split <;> try simp_all
  split <;> try simp_all
  split <;> try simp_all

theorem acknowledgement_counter_frame (l : Ledger) (p c : Id) (peer : Nat) :
    (acknowledge l p c peer).owner = l.owner ∧ (acknowledge l p c peer).next = l.next := by
  simp only [acknowledge]
  split <;> try simp_all
  split <;> try simp_all
  split <;> try simp_all

inductive Action where
  | register (parent : Id) (destination : Nat) (payload : List UInt8)
  | close (id : Id)
  | retire (id : Id)
  | ack (parent child : Id) (peer : Nat)
  deriving Repr

def Tracked.run (t : Tracked) : Action → Tracked
  | .register parent dest payload => (t.register parent dest payload).1
  | .close id => ⟨close t.ledger id, t.history⟩
  | .retire id => ⟨retire t.ledger id, t.history⟩
  | .ack parent child peer => ⟨acknowledge t.ledger parent child peer, t.history⟩

theorem tracked_action_preserves (t : Tracked) (action : Action) (valid : t.Valid) :
    (t.run action).Valid := by
  cases action with
  | register p d payload => exact (tracked_registration_preserves t p d payload valid).1
  | close q =>
    have frame := close_counter_frame t.ledger q
    exact ⟨closure_preserves_invariant t.ledger q valid.1, valid.2.1,
      valid.2.2.1.trans frame.1.symm, valid.2.2.2.trans frame.2.symm⟩
  | retire q =>
    have frame := retire_counter_frame t.ledger q
    exact ⟨retirement_preserves_invariant t.ledger q valid.1, valid.2.1,
      valid.2.2.1.trans frame.1.symm, valid.2.2.2.trans frame.2.symm⟩
  | ack p c peer =>
    have frame := acknowledgement_counter_frame t.ledger p c peer
    exact ⟨acknowledgement_preserves_invariant t.ledger p c peer valid.1, valid.2.1,
      valid.2.2.1.trans frame.1.symm, valid.2.2.2.trans frame.2.symm⟩

def Tracked.runAll : Tracked → List Action → Tracked
  | t, [] => t
  | t, action :: rest => (t.run action).runAll rest

theorem tracked_trace_preserves (t : Tracked) (actions : List Action) (valid : t.Valid) :
    (t.runAll actions).Valid := by
  induction actions generalizing t with
  | nil => exact valid
  | cons action rest ih => exact ih (t.run action) (tracked_action_preserves t action valid)

end Ash.NetworkLedger
