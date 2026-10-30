import NetworkLedgerReachability

/-
Finite abstract coverage handoffs. Actual ledger/transport/control correspondence
and the premises of completion and authenticated acknowledgements are separate.
-/
namespace Ash.NetworkLedger.Network

open Ash.NetworkLedger
open Ash.NetworkLedger.Reachability

structure State where
  edges : List Edge
  issued : List Id
  closedProducers : List Id
  pending : List Edge
  inTransit : List Edge
  running : List Edge
  acknowledgements : List Edge
  ackTransit : List Edge
  closed : Bool
  deriving Repr

def State.Outstanding (s : State) : List Edge := s.pending ++ s.inTransit ++ s.running ++ s.acknowledgements ++ s.ackTransit

def State.Covered (s : State) : Prop :=
  Unique Edge.child s.edges ∧ ∀ e ∈ s.Outstanding, e ∈ s.edges ∧ Rooted s.edges e.child

def initial : State := ⟨[], [], [], [], [], [], [], [], false⟩

theorem initial_covered : initial.Covered := by
  simp [initial, State.Covered, State.Outstanding, Unique]

theorem initial_unique : Unique Edge.child initial.Outstanding := by
  simp [initial, State.Outstanding, Unique]

theorem initial_nonroot : ∀ e ∈ initial.edges, e.child ≠ .root := by
  simp [initial]

def reserve (s : State) (e : Edge) : State :=
  { s with edges := insert e s.edges, issued := s.issued ++ [e.child], pending := s.pending ++ [e] }

theorem reserve_preserves (s : State) (e : Edge) (covered : s.Covered)
    (fresh : e.child ∉ s.edges.map Edge.child) (parent : Rooted s.edges e.parent) :
    (reserve s e).Covered := by
  refine ⟨insert_unique Edge.child e s.edges covered.1 fresh, ?_⟩
  intro x member
  change x ∈ insert e s.edges ∧ Rooted (insert e s.edges) x.child
  simp only [reserve, State.Outstanding, List.mem_append, List.mem_singleton, or_assoc] at member
  rcases member with pending | added | running | ack
  · have old := covered.2 x (by simp [State.Outstanding, pending])
    exact ⟨by simp [insert, old.1], rooted_mono s.edges _ x.child
      (fun a ha ↦ by simp [insert, ha]) old.2⟩
  · subst x
    exact ⟨by simp [insert], rooted_register s.edges e.parent e.child e.destination parent⟩
  · have old := covered.2 x (by simp [State.Outstanding, running])
    exact ⟨by simp [insert, old.1], rooted_mono s.edges _ x.child
      (fun a ha ↦ by simp [insert, ha]) old.2⟩
  · have old := covered.2 x (by simp [State.Outstanding, ack])
    exact ⟨by simp [insert, old.1], rooted_mono s.edges _ x.child
      (fun a ha ↦ by simp [insert, ha]) old.2⟩

theorem reserve_unique (s : State) (e : Edge) (covered : s.Covered)
    (unique : Unique Edge.child s.Outstanding) (fresh : e.child ∉ s.edges.map Edge.child) :
    Unique Edge.child (reserve s e).Outstanding := by
  have outstandingFresh : e.child ∉ s.Outstanding.map Edge.child := by
    intro member
    obtain ⟨x, xmem, equal⟩ := List.mem_map.mp member
    exact fresh (List.mem_map.mpr ⟨x, (covered.2 x xmem).1, equal⟩)
  have inserted := insert_unique Edge.child e s.Outstanding unique outstandingFresh
  have perm : (s.Outstanding ++ [e]).Perm
      (s.pending ++ e :: (s.inTransit ++ s.running ++ s.acknowledgements ++ s.ackTransit)) := by
    apply (List.perm_append_singleton e s.Outstanding).trans
    simpa [State.Outstanding, List.append_assoc] using
      (List.perm_middle (a := e) (l₁ := s.pending)
        (l₂ := s.inTransit ++ s.running ++ s.acknowledgements ++ s.ackTransit)).symm
  have mapped := (perm.map Edge.child).nodup inserted
  simpa [Unique, insert, reserve, State.Outstanding, List.append_assoc] using mapped

def publish (s : State) (e : Edge) (tail : List Edge) : State :=
  { s with pending := tail, inTransit := s.inTransit ++ [e] }

theorem publish_preserves (s : State) (e : Edge) (tail : List Edge) (covered : s.Covered)
    (head : s.pending = e :: tail) : (publish s e tail).Covered := by
  refine ⟨covered.1, ?_⟩
  intro x member
  apply covered.2 x
  simp only [publish, State.Outstanding, List.mem_append, List.mem_singleton, or_assoc] at member
  simp only [State.Outstanding, List.mem_append, head, List.mem_cons, or_assoc]
  rcases member with pending | transit | same | running | ack
  · exact Or.inr (Or.inl pending)
  · exact Or.inr (Or.inr (Or.inl transit))
  · exact Or.inl same
  · exact Or.inr (Or.inr (Or.inr (Or.inl running)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ack)))

def deliver (s : State) (e : Edge) (tail : List Edge) : State :=
  { s with inTransit := tail, running := s.running ++ [e] }

theorem publish_unique (s : State) (e : Edge) (tail : List Edge)
    (unique : Unique Edge.child s.Outstanding) (head : s.pending = e :: tail) :
    Unique Edge.child (publish s e tail).Outstanding := by
  have perm := (List.perm_append_singleton e (tail ++ s.inTransit)).symm
  have extend := perm.append_right (s.running ++ s.acknowledgements ++ s.ackTransit)
  have mapped := extend.map Edge.child
  have source : (List.map Edge.child
      (e :: (tail ++ s.inTransit) ++ (s.running ++ s.acknowledgements ++ s.ackTransit))).Nodup := by
    simpa [Unique, State.Outstanding, head, List.append_assoc] using unique
  simpa [Unique, publish, State.Outstanding, List.append_assoc] using mapped.nodup source

theorem deliver_preserves (s : State) (e : Edge) (tail : List Edge) (covered : s.Covered)
    (head : s.inTransit = e :: tail) : (deliver s e tail).Covered := by
  refine ⟨covered.1, ?_⟩
  intro x member
  apply covered.2 x
  simp only [deliver, State.Outstanding, List.mem_append, List.mem_singleton, or_assoc] at member
  simp only [State.Outstanding, List.mem_append, head, List.mem_cons, or_assoc]
  rcases member with pending | transit | running | same | ack
  · exact Or.inl pending
  · exact Or.inr (Or.inr (Or.inl transit))
  · exact Or.inr (Or.inr (Or.inr (Or.inl running)))
  · exact Or.inr (Or.inl same)
  · exact Or.inr (Or.inr (Or.inr (Or.inr ack)))

theorem deliver_unique (s : State) (e : Edge) (tail : List Edge)
    (unique : Unique Edge.child s.Outstanding) (head : s.inTransit = e :: tail) :
    Unique Edge.child (deliver s e tail).Outstanding := by
  have perm := (List.perm_append_singleton e (tail ++ s.running)).symm
  have extend := (perm.append_right (s.acknowledgements ++ s.ackTransit)).append_left s.pending
  have mapped := extend.map Edge.child
  have source : (List.map Edge.child (s.pending ++
      (e :: (tail ++ s.running) ++ (s.acknowledgements ++ s.ackTransit)))).Nodup := by
    simpa [Unique, State.Outstanding, head, List.append_assoc] using unique
  simpa [Unique, deliver, State.Outstanding, List.append_assoc] using mapped.nodup source

def finish (s : State) (e : Edge) (before after : List Edge) : State :=
  { s with running := before ++ after, acknowledgements := s.acknowledgements ++ [e]
           closedProducers := s.closedProducers ++ [e.child] }

theorem finish_preserves (s : State) (e : Edge) (before after : List Edge) (covered : s.Covered)
    (running : s.running = before ++ e :: after) : (finish s e before after).Covered := by
  refine ⟨covered.1, ?_⟩
  intro x member
  apply covered.2 x
  simp only [finish, State.Outstanding, List.mem_append, List.mem_singleton, or_assoc] at member
  simp only [State.Outstanding, List.mem_append, running, List.mem_cons, or_assoc]
  rcases member with pending | transit | earlier | later | ack | same | inflight
  · exact Or.inl pending
  · exact Or.inr (Or.inl transit)
  · exact Or.inr (Or.inr (Or.inl earlier))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl later))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ack)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl same)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr inflight)))))

theorem finish_unique (s : State) (e : Edge) (before after : List Edge)
    (unique : Unique Edge.child s.Outstanding) (running : s.running = before ++ e :: after) :
    Unique Edge.child (finish s e before after).Outstanding := by
  let pre := s.pending ++ s.inTransit ++ before
  have perm := (List.perm_append_singleton e (after ++ s.acknowledgements)).symm
  have extend := (perm.append_right s.ackTransit).append_left pre
  have mapped := extend.map Edge.child
  have source : (List.map Edge.child (pre ++
      (e :: (after ++ s.acknowledgements) ++ s.ackTransit))).Nodup := by
    simpa [Unique, State.Outstanding, running, pre, List.append_assoc] using unique
  simpa [Unique, finish, State.Outstanding, pre, List.append_assoc] using mapped.nodup source

def publishAcknowledgement (s : State) (e : Edge) (tail : List Edge) : State :=
  { s with acknowledgements := tail, ackTransit := s.ackTransit ++ [e] }

theorem publish_ack_preserves (s : State) (e : Edge) (tail : List Edge) (covered : s.Covered)
    (head : s.acknowledgements = e :: tail) : (publishAcknowledgement s e tail).Covered := by
  refine ⟨covered.1, ?_⟩
  intro x member
  apply covered.2 x
  simp only [publishAcknowledgement, State.Outstanding, List.mem_append, List.mem_singleton,
    or_assoc] at member
  simp only [State.Outstanding, List.mem_append, head, List.mem_cons, or_assoc]
  rcases member with pending | transit | running | queued | inflight | same
  · exact Or.inl pending
  · exact Or.inr (Or.inl transit)
  · exact Or.inr (Or.inr (Or.inl running))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl queued))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr inflight))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl same)))

theorem publish_ack_unique (s : State) (e : Edge) (tail : List Edge)
    (unique : Unique Edge.child s.Outstanding) (head : s.acknowledgements = e :: tail) :
    Unique Edge.child (publishAcknowledgement s e tail).Outstanding := by
  let pre := s.pending ++ s.inTransit ++ s.running
  have perm := (List.perm_append_singleton e (tail ++ s.ackTransit)).symm
  have mapped := (perm.append_left pre).map Edge.child
  have source : (List.map Edge.child (pre ++ e :: (tail ++ s.ackTransit))).Nodup := by
    simpa [Unique, State.Outstanding, head, pre, List.append_assoc] using unique
  simpa [Unique, publishAcknowledgement, State.Outstanding, pre, List.append_assoc] using
    mapped.nodup source

def acknowledge (s : State) (e : Edge) (before after : List Edge) : State :=
  { s with edges := erase Edge.child e.child s.edges, ackTransit := before ++ after }

theorem unique_outstanding_excludes_other (s : State) (e : Edge) (before after : List Edge)
    (ack : s.ackTransit = before ++ e :: after)
    (unique : Unique Edge.child s.Outstanding) :
    ∀ x ∈ s.pending ++ s.inTransit ++ s.running ++ s.acknowledgements ++ (before ++ after),
      x.child ≠ e.child := by
  let preEdges := s.pending ++ s.inTransit ++ s.running ++ s.acknowledgements ++ before
  have normalized : (preEdges.map Edge.child ++ e.child :: after.map Edge.child).Nodup := by
    simpa [Unique, State.Outstanding, ack, preEdges, List.map_append, List.append_assoc] using unique
  have pieces := List.nodup_append.mp normalized
  have tailAbsent : e.child ∉ after.map Edge.child := (List.nodup_cons.mp pieces.2.1).1
  have prefixAbsent : e.child ∉ preEdges.map Edge.child := by
    intro member
    exact pieces.2.2 e.child member e.child (by simp) rfl
  intro x member equal
  have split : x ∈ preEdges ∨ x ∈ after := by
    simpa [preEdges, List.append_assoc, or_assoc] using member
  rcases split with earlier | later
  · exact prefixAbsent (List.mem_map.mpr ⟨x, earlier, equal⟩)
  · exact tailAbsent (List.mem_map.mpr ⟨x, later, equal⟩)

theorem acknowledgement_preserves (s : State) (e : Edge) (before after : List Edge)
    (covered : s.Covered) (ack : s.ackTransit = before ++ e :: after)
    (leaf : Leaf s.edges e.child)
    (others : ∀ x ∈ s.pending ++ s.inTransit ++ s.running ++ s.acknowledgements ++ (before ++ after), x.child ≠ e.child) :
    (acknowledge s e before after).Covered := by
  refine ⟨erase_finite_unique Edge.child e.child s.edges covered.1, ?_⟩
  intro x member
  have remaining : x ∈ s.pending ++ s.inTransit ++ s.running ++ s.acknowledgements ++ (before ++ after) := by
    simpa [acknowledge, State.Outstanding] using member
  have different := others x remaining
  have oldMember : x ∈ s.Outstanding := by
    simp only [State.Outstanding, ack, List.mem_append, List.mem_cons, or_assoc]
    simp only [List.mem_append, or_assoc] at remaining
    rcases remaining with pending | transit | running | queued | earlier | later
    · exact Or.inl pending
    · exact Or.inr (Or.inl transit)
    · exact Or.inr (Or.inr (Or.inl running))
    · exact Or.inr (Or.inr (Or.inr (Or.inl queued)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl earlier))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr later)))))
  have old := covered.2 x oldMember
  refine ⟨?_, ?_⟩
  · exact (erase_membership Edge.child e.child s.edges x covered.1).mpr ⟨old.1, different⟩
  · exact rooted_after_leaf_removal s.edges e x.child covered.1 leaf old.2 different

theorem acknowledgement_unique (s : State) (e : Edge) (before after : List Edge)
    (unique : Unique Edge.child s.Outstanding) (ack : s.ackTransit = before ++ e :: after) :
    Unique Edge.child (acknowledge s e before after).Outstanding := by
  let pre := s.pending ++ s.inTransit ++ s.running ++ s.acknowledgements ++ before
  have sub := (List.Sublist.cons e (List.Sublist.refl after)).append_left pre
  have mapped := sub.map Edge.child
  have source : (List.map Edge.child (pre ++ e :: after)).Nodup := by
    simpa [Unique, State.Outstanding, ack, pre, List.append_assoc] using unique
  simpa [Unique, acknowledge, State.Outstanding, pre, List.append_assoc] using mapped.nodup source

inductive Step (completed authentic : Edge → Prop) : State → State → Prop where
  | reserve (s : State) (e : Edge) (fresh : e.child ∉ s.edges.map Edge.child)
      (parent : Rooted s.edges e.parent) (neverIssued : e.child ∉ s.issued)
      (parentOpen : e.parent ∉ s.closedProducers) (childNotRoot : e.child ≠ .root)
      (admission : s.closed = false ∨ e.parent ≠ .root) :
      Step completed authentic s (reserve s e)
  | closeAdmission (s : State) : Step completed authentic s { s with closed := true }
  | publish (s : State) (e : Edge) (tail : List Edge) (head : s.pending = e :: tail) :
      Step completed authentic s (publish s e tail)
  | deliver (s : State) (e : Edge) (tail : List Edge) (head : s.inTransit = e :: tail) :
      Step completed authentic s (deliver s e tail)
  | finish (s : State) (e : Edge) (before after : List Edge)
      (running : s.running = before ++ e :: after) (done : completed e)
      (leaf : Leaf s.edges e.child) :
      Step completed authentic s (finish s e before after)
  | publishAck (s : State) (e : Edge) (tail : List Edge)
      (head : s.acknowledgements = e :: tail) :
      Step completed authentic s (publishAcknowledgement s e tail)
  | acknowledge (s : State) (e : Edge) (before after : List Edge)
      (ack : s.ackTransit = before ++ e :: after) (source : authentic e)
      (leaf : Leaf s.edges e.child)
      (others : ∀ x ∈ s.pending ++ s.inTransit ++ s.running ++ s.acknowledgements ++ (before ++ after), x.child ≠ e.child) :
      Step completed authentic s (acknowledge s e before after)

theorem acknowledgement_enabled {completed authentic : Edge → Prop} (s : State) (e : Edge)
    (before after : List Edge) (unique : Unique Edge.child s.Outstanding)
    (ack : s.ackTransit = before ++ e :: after) (source : authentic e)
    (leaf : Leaf s.edges e.child) : Step completed authentic s (acknowledge s e before after) := by
  exact .acknowledge s e before after ack source leaf (unique_outstanding_excludes_other s e before after ack unique)

theorem step_preserves {completed authentic : Edge → Prop} {s t : State}
    (covered : s.Covered) (step : Step completed authentic s t) : t.Covered := by
  cases step with
  | reserve e fresh parent _ _ _ _ => exact reserve_preserves _ e covered fresh parent
  | closeAdmission => exact covered
  | publish e tail head => exact publish_preserves _ e tail covered head
  | deliver e tail head => exact deliver_preserves _ e tail covered head
  | finish e before after running _ _ => exact finish_preserves _ e before after covered running
  | publishAck e tail head => exact publish_ack_preserves _ e tail covered head
  | acknowledge e before after ack _ leaf others =>
    exact acknowledgement_preserves _ e before after covered ack leaf others

theorem unique_step_preserves {completed authentic : Edge → Prop} {s t : State}
    (covered : s.Covered) (unique : Unique Edge.child s.Outstanding)
    (step : Step completed authentic s t) : Unique Edge.child t.Outstanding := by
  cases step with
  | reserve e fresh parent neverIssued parentOpen childNotRoot admission => exact reserve_unique _ e covered unique fresh
  | closeAdmission => exact unique
  | publish e tail head => exact publish_unique _ e tail unique head
  | deliver e tail head => exact deliver_unique _ e tail unique head
  | finish e before after running done leaf => exact finish_unique _ e before after unique running
  | publishAck e tail head => exact publish_ack_unique _ e tail unique head
  | acknowledge e before after ack source leaf others =>
    exact acknowledgement_unique _ e before after unique ack

theorem nonroot_step_preserves {completed authentic : Edge → Prop} {s t : State}
    (nonroot : ∀ e ∈ s.edges, e.child ≠ .root) (step : Step completed authentic s t) :
    ∀ e ∈ t.edges, e.child ≠ .root := by
  cases step with
  | reserve e fresh parent neverIssued parentOpen childNotRoot admission =>
    intro item member
    simp only [reserve, insert, List.mem_append, List.mem_singleton] at member
    rcases member with old | same
    · exact nonroot item old
    · subst item; exact childNotRoot
  | closeAdmission => exact nonroot
  | publish => exact nonroot
  | deliver => exact nonroot
  | finish => exact nonroot
  | publishAck => exact nonroot
  | acknowledge e before after ack source leaf others =>
    intro item member
    exact nonroot item ((erase_subsequence Edge.child e.child _).mem member)

def State.ClosedLeaf (s : State) (id : Id) : Prop := id ∈ s.closedProducers ∧ Leaf s.edges id

theorem finish_closes_leaf (s : State) (e : Edge) (before after : List Edge)
    (leaf : Leaf s.edges e.child) : (finish s e before after).ClosedLeaf e.child := by
  exact ⟨by simp [finish], leaf⟩

theorem closed_leaf_step_preserves {completed authentic : Edge → Prop} {s t : State} (id : Id)
    (closedLeaf : s.ClosedLeaf id) (step : Step completed authentic s t) : t.ClosedLeaf id := by
  rcases closedLeaf with ⟨closed, leaf⟩
  cases step with
  | reserve e fresh parent neverIssued parentOpen childNotRoot admission =>
    constructor
    · exact closed
    · intro item member
      simp only [reserve, insert, List.mem_append, List.mem_singleton] at member
      rcases member with old | same
      · exact leaf item old
      · subst item
        intro equal
        apply parentOpen
        simpa [equal] using closed
  | closeAdmission => exact ⟨closed, leaf⟩
  | publish => exact ⟨closed, leaf⟩
  | deliver => exact ⟨closed, leaf⟩
  | finish e before after running done finishedLeaf =>
    exact ⟨by simp [finish, closed], leaf⟩
  | publishAck => exact ⟨closed, leaf⟩
  | acknowledge e before after ack source removedLeaf others =>
    refine ⟨closed, ?_⟩
    intro item member
    exact leaf item ((erase_subsequence Edge.child e.child _).mem member)

theorem issued_step_monotone {completed authentic : Edge → Prop} {s t : State}
    (step : Step completed authentic s t) (id : Id) (issued : id ∈ s.issued) : id ∈ t.issued := by
  cases step with
  | reserve e fresh parent neverIssued parentOpen childNotRoot admission => simp [reserve, issued]
  | closeAdmission => exact issued
  | publish => exact issued
  | deliver => exact issued
  | finish => exact issued
  | publishAck => exact issued
  | acknowledge => exact issued

inductive Trace (completed authentic : Edge → Prop) : State → State → Prop where
  | refl (s : State) : Trace completed authentic s s
  | next {s t u : State} : Trace completed authentic s t → Step completed authentic t u →
      Trace completed authentic s u

theorem trace_preserves {completed authentic : Edge → Prop} {s t : State}
    (covered : s.Covered) (trace : Trace completed authentic s t) : t.Covered := by
  induction trace with
  | refl => exact covered
  | next _ step ih => exact step_preserves ih step

theorem trace_preserves_unique {completed authentic : Edge → Prop} {s t : State}
    (covered : s.Covered) (unique : Unique Edge.child s.Outstanding)
    (trace : Trace completed authentic s t) : Unique Edge.child t.Outstanding := by
  induction trace with
  | refl => exact unique
  | next history step ih =>
    exact unique_step_preserves (trace_preserves covered history) ih step

theorem nonroot_trace_preserves {completed authentic : Edge → Prop} {s t : State}
    (nonroot : ∀ e ∈ s.edges, e.child ≠ .root) (trace : Trace completed authentic s t) :
    ∀ e ∈ t.edges, e.child ≠ .root := by
  induction trace with
  | refl => exact nonroot
  | next _ step ih => exact nonroot_step_preserves ih step

theorem closed_leaf_trace_preserves {completed authentic : Edge → Prop} {s t : State} (id : Id)
    (closedLeaf : s.ClosedLeaf id) (trace : Trace completed authentic s t) : t.ClosedLeaf id := by
  induction trace with
  | refl => exact closedLeaf
  | next history step ih => exact closed_leaf_step_preserves id ih step

theorem issued_trace_monotone {completed authentic : Edge → Prop} {s t : State}
    (trace : Trace completed authentic s t) (id : Id) (issued : id ∈ s.issued) : id ∈ t.issued := by
  induction trace with
  | refl => exact issued
  | next history step ih => exact issued_step_monotone step id ih

theorem reservation_records_issue (s : State) (e : Edge) : e.child ∈ (reserve s e).issued := by
  simp [reserve]

theorem root_empty_has_no_outstanding (s : State) (covered : s.Covered)
    (nonroot : ∀ e ∈ s.edges, e.child ≠ .root)
    (rootEmpty : ∀ e ∈ s.edges, e.parent ≠ .root) : s.Outstanding = [] := by
  cases xs : s.Outstanding with
  | nil => rfl
  | cons x rest =>
    have member : x ∈ s.Outstanding := by simp [xs]
    have coverage := covered.2 x member
    obtain ⟨edge, edgeMember, atRoot⟩ :=
      rooted_has_root_edge s.edges x.child coverage.2 (nonroot x coverage.1)
    exact False.elim (rootEmpty edge edgeMember atRoot)

theorem closed_quiet_stable {completed authentic : Edge → Prop} {s t : State} (closed : s.closed = true) (covered : s.Covered)
    (nonroot : ∀ e ∈ s.edges, e.child ≠ .root)
    (rootEmpty : ∀ e ∈ s.edges, e.parent ≠ .root) (step : Step completed authentic s t) : t = s := by
  have quiet := root_empty_has_no_outstanding s covered nonroot rootEmpty
  have emptyParts : s.pending = [] ∧ s.inTransit = [] ∧ s.running = [] ∧ s.acknowledgements = [] ∧ s.ackTransit = [] := by
    simpa [State.Outstanding, List.append_eq_nil_iff, and_assoc] using quiet
  cases step with
  | reserve e fresh parent neverIssued parentOpen childNotRoot admission =>
    have parentNotRoot : e.parent ≠ .root := by
      rcases admission with openRoot | notRoot
      · simp [closed] at openRoot
      · exact notRoot
    obtain ⟨edge, edgeMember, atRoot⟩ := rooted_has_root_edge s.edges e.parent parent parentNotRoot
    exact False.elim (rootEmpty edge edgeMember atRoot)
  | closeAdmission =>
    cases s with
    | mk edges issued closedProducers pending inTransit running acknowledgements ackTransit closedValue =>
      simp only at closed
      cases closedValue <;> simp_all
  | publish e tail head => simp [emptyParts.1] at head
  | deliver e tail head => simp [emptyParts.2.1] at head
  | finish e before after running done leaf => simp [emptyParts.2.2.1] at running
  | publishAck e tail head => simp [emptyParts.2.2.2.1] at head
  | acknowledge e before after ack source leaf others => simp [emptyParts.2.2.2.2] at ack

theorem closed_quiet_stable_trace {completed authentic : Edge → Prop} {s t : State} (closed : s.closed = true) (covered : s.Covered)
    (nonroot : ∀ e ∈ s.edges, e.child ≠ .root)
    (rootEmpty : ∀ e ∈ s.edges, e.parent ≠ .root) (trace : Trace completed authentic s t) : t = s := by
  induction trace with
  | refl => rfl
  | next _ step ih =>
    subst_vars
    exact closed_quiet_stable closed covered nonroot rootEmpty step

end Ash.NetworkLedger.Network
