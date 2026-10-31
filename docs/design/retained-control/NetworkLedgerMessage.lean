import NetworkLedgerCoupling

namespace Ash.NetworkLedger.Coupling

open Ash.NetworkLedger
open Ash.NetworkLedger.Reachability

theorem install_fresh (l : Ledger) (id : Id) (parent : Address)
    (nonroot : id ≠ .root) (fresh : id ∉ l.records.map Record.id) :
    install l id parent =
      { l with records := insert ⟨id, some parent, .open, []⟩ l.records } := by
  simp only [install]
  rw [if_neg (by simp [nonroot, fresh])]

theorem retire_ready_output (l : Ledger) (id : Id) (r : Record) (parent : Address)
    (found : lookup Record.id id l.records = some r) (parentField : r.parent = some parent)
    (closed : r.phase = .closed) (empty : r.children = []) (nonroot : id ≠ .root) :
    retire l id = { l with
      records := (remove Record.id id l.records).1
      outputs := l.outputs ++ [.ack parent id] } := by
  simp only [retire, found, parentField, closed, empty, true_and]
  rw [if_pos nonroot]

theorem acknowledgement_removes_matching_edge (l : Ledger) (p child : Id) (peer : Nat)
    (r : Record) (entry : Child) (valid : LocalInvariant l)
    (found : lookup Record.id p l.records = some r)
    (childFound : lookup Child.id child r.children = some entry)
    (matched : entry.destination = peer) :
    (⟨p, child, peer⟩ : Edge) ∉ ledgerEdges (acknowledge l p child peer) := by
  have rkey := (lookup_sound Record.id p l.records r found).2
  have rmem := (lookup_sound Record.id p l.records r found).1
  let newer := { r with children := (remove Child.id child r.children).1 }
  have newKey : newer.id = p := rkey
  have unique := update_unique Record.id p newer l.records newKey valid.2.1
  have newFound := lookup_update Record.id p newer l.records r found newKey
  have absent : child ∉ newer.children.map Child.id := by
    dsimp [newer]
    rw [remove_sequence]
    exact erase_excludes_key Child.id child r.children (valid.2.2 r rmem).1
  intro member
  simp only [acknowledge, found, childFound, matched, ↓reduceIte] at member
  obtain ⟨x, xmem, c, cmem, equal⟩ := (edge_membership _ _).mp member
  have xkey : x.id = p := by
    have h := congrArg Edge.parent equal
    simpa using h.symm
  have xFound := lookup_unique Record.id p (update Record.id p newer l.records) x unique xmem xkey
  have xeq : x = newer := by
    rw [newFound] at xFound
    exact Option.some.inj xFound.symm
  subst x
  apply absent
  apply List.mem_map.mpr
  refine ⟨c, cmem, ?_⟩
  have h := congrArg Edge.child equal
  simpa using h.symm

theorem acknowledgement_exact_edge_removal (l : Ledger) (p child : Id) (peer : Nat)
    (r : Record) (entry : Child) (valid : LocalInvariant l)
    (uniqueEdges : Unique Edge.child (ledgerEdges l))
    (found : lookup Record.id p l.records = some r)
    (childFound : lookup Child.id child r.children = some entry)
    (matched : entry.destination = peer) (edge : Edge) :
    edge ∈ ledgerEdges (acknowledge l p child peer) ↔
      edge ∈ ledgerEdges l ∧ edge.child ≠ child := by
  have rinfo := lookup_sound Record.id p l.records r found
  have childInfo := lookup_sound Child.id child r.children entry childFound
  let target : Edge := ⟨p, child, peer⟩
  have targetMember : target ∈ ledgerEdges l := by
    apply (edge_membership l target).mpr
    refine ⟨r, rinfo.1, entry, childInfo.1, ?_⟩
    simp [target, rinfo.2, childInfo.2, matched]
  have absent := acknowledgement_removes_matching_edge l p child peer r entry valid found childFound matched
  constructor
  · intro member
    have old := acknowledge_edges_subset l p child peer edge member
    refine ⟨old, ?_⟩
    intro same
    have equal : edge = target := unique_keys_injective Edge.child _ edge target uniqueEdges old targetMember same
    apply absent
    simpa [target, equal] using member
  · rintro ⟨old, different⟩
    exact acknowledge_preserves_other_edges l p child peer edge different old

theorem worker_edges_sublist (workers : List Tracked) (worker : Tracked)
    (member : worker ∈ workers) : (ledgerEdges worker.ledger).Sublist (trackedGraph workers) := by
  induction workers with
  | nil => simp at member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with same | rest
    · subst worker
      simpa only [trackedGraph, List.flatMap_cons, List.append_nil] using
        (List.Sublist.refl (ledgerEdges head.ledger)).append (List.nil_sublist (trackedGraph tail))
    · have sub := ih rest
      simpa [trackedGraph] using (List.nil_sublist (ledgerEdges head.ledger)).append sub

/-- Local acknowledgement's uniqueness premise is derived from the global trace. -/
theorem initialized_trace_local_edges_unique (owner : Nat) (others : List Nat)
    (distinct : (owner :: others).Nodup) {s : System}
    (trace : SystemTrace (initialSystem owner others) s) (worker : Tracked)
    (member : worker ∈ s.root :: s.workers) : Unique Edge.child (ledgerEdges worker.ledger) := by
  have global := initialized_trace_graph_unique owner others distinct trace
  exact ((worker_edges_sublist (s.root :: s.workers) worker member).map Edge.child).nodup global

/- The permissive local-step relation deliberately does not establish coverage:
   a delivery without a matching transport obligation can create orphan work. -/
def orphanWorker : Ledger :=
  let installed := install (initialWorker 1) (.work 0 0) ⟨0, .root⟩
  (register installed (.work 0 0) 2 []).1

theorem unconstrained_delivery_counterexample :
    probeRoot (close (initialRoot 0) .root) = true ∧
    (⟨.work 0 0, .work 1 0, 2⟩ : Edge) ∈ ledgerEdges orphanWorker ∧
    orphanWorker.outputs = [.work (.work 1 0) ⟨1, .work 0 0⟩ 2 []] := by
  decide

/-- Every live non-root record has an incoming obligation in the ledger graph. -/
def RecordsLinked (graph : List Edge) (l : Ledger) : Prop :=
  ∀ r ∈ l.records, r.id = .root ∨ ∃ edge ∈ graph, edge.child = r.id

theorem initial_root_linked (owner : Nat) (graph : List Edge) :
    RecordsLinked graph (initialRoot owner) := by
  simp [RecordsLinked, initialRoot]

theorem initial_worker_linked (owner : Nat) (graph : List Edge) :
    RecordsLinked graph (initialWorker owner) := by
  simp [RecordsLinked, initialWorker]

theorem install_linked (l : Ledger) (id : Id) (parent : Address) (graph : List Edge)
    (linked : RecordsLinked graph l) (incoming : ∃ edge ∈ graph, edge.child = id) :
    RecordsLinked graph (install l id parent) := by
  by_cases reject : id = .root ∨ id ∈ l.records.map Record.id
  · simpa only [install, reject, ↓reduceIte] using linked
  · simp only [install, reject, ↓reduceIte, RecordsLinked]
    intro record member
    simp only [insert, List.mem_append, List.mem_singleton] at member
    rcases member with old | same
    · exact linked record old
    · subst record
      exact Or.inr incoming

theorem linked_record_rooted (l : Ledger) (graph : List Edge) (r : Record)
    (linked : RecordsLinked graph l) (member : r ∈ l.records)
    (rooted : ∀ edge ∈ graph, Rooted graph edge.child) : Rooted graph r.id := by
  rcases linked r member with root | ⟨edge, edgeMember, equal⟩
  · rw [root]
    exact .root
  · rw [← equal]
    exact rooted edge edgeMember

/-- Work still in a ledger's output queue is backed by its actual child edge. -/
def WorkOutputsBacked (l : Ledger) : Prop :=
  ∀ id parent destination payload, Output.work id parent destination payload ∈ l.outputs →
    parent.worker = l.owner ∧ (⟨parent.id, id, destination⟩ : Edge) ∈ ledgerEdges l

theorem initial_root_work_backed (owner : Nat) : WorkOutputsBacked (initialRoot owner) := by
  simp [WorkOutputsBacked, initialRoot]

theorem initial_worker_work_backed (owner : Nat) : WorkOutputsBacked (initialWorker owner) := by
  simp [WorkOutputsBacked, initialWorker]

theorem register_work_backed (l : Ledger) (p : Id) (d : Nat) (bytes : List UInt8)
    (backed : WorkOutputsBacked l) : WorkOutputsBacked (register l p d bytes).1 := by
  cases found : lookup Record.id p l.records with
  | none => simpa [register, found] using backed
  | some r =>
    cases phase : r.phase with
    | closed => simpa [register, found, phase] using backed
    | «open» =>
      have result := register_open l p d bytes r found phase
      intro id parent destination payload member
      have output : Output.work id parent destination payload ∈
          l.outputs ++ [.work (.work l.owner l.next) ⟨l.owner, p⟩ d bytes] := by
        simpa [result] using member
      rcases List.mem_append.mp output with old | added
      · have oldBacked := backed id parent destination payload old
        refine ⟨by simpa [result] using oldBacked.1, ?_⟩
        exact (register_edges_and_output l p d bytes r found phase _).1.mpr (Or.inl oldBacked.2)
      · simp only [List.mem_singleton] at added
        cases added
        refine ⟨by simp [result], ?_⟩
        exact (register_edges_and_output l p d bytes r found phase _).1.mpr (Or.inr rfl)

theorem work_backed_of_frames (before after : Ledger) (backed : WorkOutputsBacked before)
    (owner : after.owner = before.owner) (edges : ledgerEdges after = ledgerEdges before)
    (outputs : ∀ id parent destination payload,
      Output.work id parent destination payload ∈ after.outputs →
      Output.work id parent destination payload ∈ before.outputs) : WorkOutputsBacked after := by
  intro id parent destination payload member
  have old := backed id parent destination payload (outputs id parent destination payload member)
  exact ⟨old.1.trans owner.symm, by rw [edges]; exact old.2⟩

theorem close_outputs (l : Ledger) (p : Id) : (close l p).outputs = l.outputs := by
  simp only [close]
  split <;> try simp_all
  split <;> try simp_all

theorem close_work_backed (l : Ledger) (p : Id) (backed : WorkOutputsBacked l) :
    WorkOutputsBacked (close l p) := by
  apply work_backed_of_frames l _ backed (close_counter_frame l p).1 (close_edges_equal l p)
  intro id parent destination payload member
  simpa [close_outputs] using member

theorem install_work_backed (l : Ledger) (id : Id) (parent : Address)
    (backed : WorkOutputsBacked l) : WorkOutputsBacked (install l id parent) := by
  have frames := install_frames l id parent
  apply work_backed_of_frames l _ backed frames.1 (install_edges_equal l id parent)
  intro q address destination payload member
  simpa [frames.2.2] using member

theorem retire_work_output_old (l : Ledger) (q id : Id) (parent : Address)
    (destination : Nat) (payload : List UInt8)
    (member : Output.work id parent destination payload ∈ (retire l q).outputs) :
    Output.work id parent destination payload ∈ l.outputs := by
  cases found : lookup Record.id q l.records with
  | none => simpa [retire, found] using member
  | some r =>
    cases parentField : r.parent with
    | none => simpa [retire, found, parentField] using member
    | some address =>
      by_cases ready : r.phase = .closed ∧ r.children = [] ∧ q ≠ .root
      · have result := retire_ready_output l q r address found parentField ready.1 ready.2.1 ready.2.2
        simpa [result] using member
      · simpa [retire, found, parentField, ready] using member

theorem retire_work_backed (l : Ledger) (q : Id) (backed : WorkOutputsBacked l) :
    WorkOutputsBacked (retire l q) := by
  apply work_backed_of_frames l _ backed (retire_counter_frame l q).1 (retire_edges_equal l q)
  exact fun id parent destination payload member => retire_work_output_old l q id parent destination payload member

theorem ack_outputs (l : Ledger) (p child : Id) (peer : Nat) :
    (acknowledge l p child peer).outputs = l.outputs := by
  simp only [acknowledge]
  split <;> try simp_all
  split <;> try simp_all
  split <;> try simp_all

/-- The causal queue condition must be derived by the coupled message lifecycle. -/
theorem ack_work_backed (l : Ledger) (p child : Id) (peer : Nat) (backed : WorkOutputsBacked l)
    (published : ∀ parent destination payload,
      Output.work child parent destination payload ∉ l.outputs) :
    WorkOutputsBacked (acknowledge l p child peer) := by
  intro id parent destination payload member
  have oldOutput : Output.work id parent destination payload ∈ l.outputs := by
    simpa [ack_outputs] using member
  have old := backed id parent destination payload oldOutput
  have different : id ≠ child := by
    intro same
    subst id
    exact published parent destination payload oldOutput
  refine ⟨old.1.trans (acknowledgement_counter_frame l p child peer).1.symm, ?_⟩
  apply acknowledge_preserves_other_edges l p child peer _
  · exact different
  · exact old.2

theorem take_output_empty (l : Ledger) (empty : l.outputs = []) : takeOutput l = (l, none) := by
  simp [takeOutput, empty]

theorem take_output_head (l : Ledger) (head : Output) (tail : List Output)
    (queued : l.outputs = head :: tail) :
    takeOutput l = ({ l with outputs := tail }, some head) := by
  simp [takeOutput, queued]

theorem take_output_work_backed (l : Ledger) (backed : WorkOutputsBacked l) :
    WorkOutputsBacked (takeOutput l).1 := by
  cases outputs : l.outputs with
  | nil => simpa [takeOutput, outputs] using backed
  | cons head tail =>
    simp only [takeOutput, outputs]
    intro id parent destination payload member
    exact backed id parent destination payload (by simp [outputs, member])

theorem take_work_has_edge (l : Ledger) (backed : WorkOutputsBacked l)
    (id : Id) (parent : Address) (destination : Nat) (payload : List UInt8)
    (taken : (takeOutput l).2 = some (.work id parent destination payload)) :
    parent.worker = l.owner ∧ (⟨parent.id, id, destination⟩ : Edge) ∈ ledgerEdges l := by
  cases outputs : l.outputs with
  | nil => simp [takeOutput, outputs] at taken
  | cons head tail =>
    have same : head = .work id parent destination payload := by
      simpa [takeOutput, outputs] using taken
    apply backed id parent destination payload
    simp [outputs, same]

/-- A live record's real parent fields identify its incoming ledger edge. -/
def RecordParentBacked (graph : List Edge) (l : Ledger) : Prop :=
  ∀ r ∈ l.records, ∀ parent, r.parent = some parent →
    (⟨parent.id, r.id, l.owner⟩ : Edge) ∈ graph

theorem initial_root_parent_backed (owner : Nat) (graph : List Edge) :
    RecordParentBacked graph (initialRoot owner) := by
  simp [RecordParentBacked, initialRoot]

theorem initial_worker_parent_backed (owner : Nat) (graph : List Edge) :
    RecordParentBacked graph (initialWorker owner) := by
  simp [RecordParentBacked, initialWorker]

theorem install_parent_backed (l : Ledger) (id : Id) (parent : Address) (graph : List Edge)
    (backed : RecordParentBacked graph l)
    (incoming : (⟨parent.id, id, l.owner⟩ : Edge) ∈ graph) :
    RecordParentBacked graph (install l id parent) := by
  by_cases reject : id = .root ∨ id ∈ l.records.map Record.id
  · simpa only [install, reject, ↓reduceIte] using backed
  · simp only [install, reject, ↓reduceIte, RecordParentBacked]
    intro record member address parentField
    simp only [insert, List.mem_append, List.mem_singleton] at member
    rcases member with old | same
    · exact backed record old address parentField
    · subst record
      simp only [Option.some.injEq] at parentField
      subst address
      exact incoming

theorem retiring_record_has_incoming_edge (l : Ledger) (id : Id) (r : Record) (parent : Address)
    (graph : List Edge) (backed : RecordParentBacked graph l)
    (found : lookup Record.id id l.records = some r) (parentField : r.parent = some parent) :
    (⟨parent.id, id, l.owner⟩ : Edge) ∈ graph := by
  have info := lookup_sound Record.id id l.records r found
  simpa [info.2] using backed r info.1 parent parentField

/-- The parent address includes a worker identity, which graph IDs alone omit. -/
def AddressedParentBacked (workers : List Ledger) (l : Ledger) : Prop :=
  ∀ r ∈ l.records, ∀ parent, r.parent = some parent →
    ∃ parentLedger ∈ workers, parentLedger.owner = parent.worker ∧
      ∃ parentRecord ∈ parentLedger.records, parentRecord.id = parent.id ∧
        ∃ child ∈ parentRecord.children, child.id = r.id ∧ child.destination = l.owner

theorem addressed_parent_implies_graph (workers : List Ledger) (l : Ledger)
    (addressed : AddressedParentBacked workers l) :
    RecordParentBacked (ledgerGraph workers) l := by
  intro r rmem parent parentField
  obtain ⟨parentLedger, lm, _, parentRecord, rm, recordId, child, cm, childId, destination⟩ :=
    addressed r rmem parent parentField
  apply (graph_membership workers _).mpr
  refine ⟨parentLedger, lm, parentRecord, rm, child, cm, ?_⟩
  simp [recordId, childId, destination]

theorem parent_backing_graph_mono (l : Ledger) (before after : List Edge)
    (backed : RecordParentBacked before l)
    (retained : ∀ edge ∈ before, edge ∈ after) : RecordParentBacked after l := by
  intro r member parent field
  exact retained _ (backed r member parent field)

theorem parent_backing_update (l : Ledger) (graph : List Edge) (q : Id) (r : Record)
    (replacement : Record) (backed : RecordParentBacked graph l)
    (found : lookup Record.id q l.records = some r)
    (sameId : replacement.id = r.id) (sameParent : replacement.parent = r.parent) :
    RecordParentBacked graph { l with records := update Record.id q replacement l.records } := by
  have member := (lookup_sound Record.id q l.records r found).1
  apply update_all Record.id q replacement l.records
    (fun x => ∀ parent, x.parent = some parent →
      (⟨parent.id, x.id, l.owner⟩ : Edge) ∈ graph) backed
  intro parent field
  have oldField : r.parent = some parent := by simpa [sameParent] using field
  simpa [sameId] using backed r member parent oldField

theorem parent_backing_retire (l : Ledger) (q : Id) (graph : List Edge)
    (backed : RecordParentBacked graph l) : RecordParentBacked graph (retire l q) := by
  cases found : lookup Record.id q l.records with
  | none => simpa [retire, found] using backed
  | some r =>
    cases parent : r.parent with
    | none => simpa [retire, found, parent] using backed
    | some address =>
      by_cases ready : r.phase = .closed ∧ r.children = [] ∧ q ≠ .root
      · simp only [retire, found, parent, ready.1, ready.2.1, true_and]
        rw [if_pos ready.2.2]
        intro x member parent field
        exact backed x ((erase_retains_whole_order Record.id q l.records).mem member) parent field
      · simpa [retire, found, parent, ready] using backed

structure WorkMessage where
  source : Nat
  id : Id
  parent : Address
  destination : Nat
  payload : List UInt8
  deriving DecidableEq, Repr

def WorkMessage.edge (m : WorkMessage) : Edge := ⟨m.parent.id, m.id, m.destination⟩

def WorkFlightBacked (graph : List Edge) (messages : List WorkMessage) : Prop :=
  ∀ m ∈ messages, m.parent.worker = m.source ∧ m.edge ∈ graph

theorem published_work_is_backed (l : Ledger) (id : Id) (parent : Address)
    (destination : Nat) (payload : List UInt8) (graph : List Edge)
    (backed : WorkOutputsBacked l)
    (incorporated : ∀ edge ∈ ledgerEdges l, edge ∈ graph)
    (taken : (takeOutput l).2 = some (.work id parent destination payload)) :
    let message : WorkMessage := ⟨l.owner, id, parent, destination, payload⟩
    message.parent.worker = message.source ∧ message.edge ∈ graph := by
  have actual := take_work_has_edge l backed id parent destination payload taken
  exact ⟨actual.1, incorporated _ actual.2⟩

theorem publish_flight_preserves (l : Ledger) (id : Id) (parent : Address)
    (destination : Nat) (payload : List UInt8) (graph : List Edge) (messages : List WorkMessage)
    (backed : WorkOutputsBacked l) (flight : WorkFlightBacked graph messages)
    (incorporated : ∀ edge ∈ ledgerEdges l, edge ∈ graph)
    (taken : (takeOutput l).2 = some (.work id parent destination payload)) :
    WorkFlightBacked graph (messages ++ [⟨l.owner, id, parent, destination, payload⟩]) := by
  intro message member
  simp only [List.mem_append, List.mem_singleton] at member
  rcases member with old | added
  · exact flight message old
  · subst message
    exact published_work_is_backed l id parent destination payload graph backed incorporated taken

theorem deliver_flight_preserves_parent_backing (l : Ledger) (message : WorkMessage)
    (graph : List Edge) (backed : RecordParentBacked graph l)
    (flight : WorkFlightBacked graph [message]) (destination : message.destination = l.owner) :
    RecordParentBacked graph (install l message.id message.parent) := by
  have edge := (flight message (by simp)).2
  apply install_parent_backed l message.id message.parent graph backed
  simpa [WorkMessage.edge, destination] using edge

theorem register_parent_backed (l : Ledger) (q : Id) (destination : Nat) (payload : List UInt8)
    (graph : List Edge) (backed : RecordParentBacked graph l) :
    RecordParentBacked graph (register l q destination payload).1 := by
  cases found : lookup Record.id q l.records with
  | none => simpa [register, found] using backed
  | some r =>
    by_cases closed : r.phase = .closed
    · simpa [register, found, closed] using backed
    · simp only [register, found, closed, ↓reduceIte]
      exact parent_backing_update l graph q r
        { r with children := insert ⟨.work l.owner l.next, destination⟩ r.children }
        backed found rfl rfl

theorem close_parent_backed (l : Ledger) (q : Id) (graph : List Edge)
    (backed : RecordParentBacked graph l) : RecordParentBacked graph (close l q) := by
  cases found : lookup Record.id q l.records with
  | none => simpa [close, found] using backed
  | some r =>
    by_cases closed : r.phase = .closed
    · simpa [close, found, closed] using backed
    · simp only [close, found, closed, ↓reduceIte]
      exact parent_backing_update l graph q r { r with phase := .closed } backed found rfl rfl

theorem ack_parent_backed (l : Ledger) (p child : Id) (peer : Nat) (graph : List Edge)
    (backed : RecordParentBacked graph l) : RecordParentBacked graph (acknowledge l p child peer) := by
  cases found : lookup Record.id p l.records with
  | none => simpa [acknowledge, found] using backed
  | some r =>
    cases childFound : lookup Child.id child r.children with
    | none => simpa [acknowledge, found, childFound] using backed
    | some entry =>
      by_cases matched : entry.destination = peer
      · simp only [acknowledge, found, childFound, matched, ↓reduceIte]
        exact parent_backing_update l graph p r
          { r with children := (remove Child.id child r.children).1 } backed found rfl rfl
      · simpa [acknowledge, found, childFound, matched] using backed

theorem tracked_graph_is_ledger_graph (workers : List Tracked) :
    trackedGraph workers = ledgerGraph (workers.map Tracked.ledger) := by
  simp [trackedGraph, ledgerGraph, List.flatMap_map]

theorem member_edges_in_tracked_graph (workers : List Tracked) (worker : Tracked)
    (member : worker ∈ workers) (edge : Edge) (edgeMember : edge ∈ ledgerEdges worker.ledger) :
    edge ∈ trackedGraph workers := by
  exact (tracked_graph_member workers edge).mpr ⟨worker, member, edgeMember⟩

structure PublicationState where
  current : Tracked
  flight : List WorkMessage
  deriving Repr

/-- Publish a work head; an empty queue or an acknowledgement head is untouched. -/
def publishWork (state : PublicationState) : PublicationState :=
  match takeOutput state.current.ledger with
  | (next, some (.work id parent destination payload)) =>
    ⟨⟨next, state.current.history⟩,
      state.flight ++ [⟨state.current.ledger.owner, id, parent, destination, payload⟩]⟩
  | _ => state

theorem publish_work_preserves (state : PublicationState) (graph : List Edge)
    (ledgerBacked : WorkOutputsBacked state.current.ledger)
    (flightBacked : WorkFlightBacked graph state.flight)
    (incorporated : ∀ edge ∈ ledgerEdges state.current.ledger, edge ∈ graph) :
    WorkOutputsBacked (publishWork state).current.ledger ∧
      WorkFlightBacked graph (publishWork state).flight ∧
      (publishWork state).current.ledger.records = state.current.ledger.records ∧
      (publishWork state).current.ledger.owner = state.current.ledger.owner ∧
      (publishWork state).current.ledger.next = state.current.ledger.next := by
  have frames := take_output_frames state.current.ledger
  have nextBacked := take_output_work_backed state.current.ledger ledgerBacked
  cases result : takeOutput state.current.ledger with
  | mk next output =>
    cases output with
    | none => simp [publishWork, result, ledgerBacked, flightBacked]
    | some value =>
      cases value with
      | ack parent child => simp [publishWork, result, ledgerBacked, flightBacked]
      | work id parent destination payload =>
        have taken : (takeOutput state.current.ledger).2 = some (.work id parent destination payload) := by
          rw [result]
        have newFlight := publish_flight_preserves state.current.ledger id parent destination payload
          graph state.flight ledgerBacked flightBacked incorporated taken
        simpa [publishWork, result] using
          And.intro (by simpa [result] using nextBacked) (And.intro newFlight
            (by simpa [result] using And.intro frames.2.2 (And.intro frames.1 frames.2.1)))

structure DeliveryState where
  receiver : Tracked
  flight : List WorkMessage
  deriving Repr

/-- Delivery consumes the oldest message only if its destination and fresh ID match. -/
def deliverWork (state : DeliveryState) : DeliveryState :=
  match state.flight with
  | [] => state
  | head :: tail =>
    if head.destination = state.receiver.ledger.owner ∧ head.id ≠ .root ∧
        head.id ∉ state.receiver.ledger.records.map Record.id then
      ⟨⟨install state.receiver.ledger head.id head.parent, state.receiver.history⟩, tail⟩
    else state

theorem deliver_work_preserves (state : DeliveryState) (graph : List Edge)
    (valid : state.receiver.Valid) (parentBacked : RecordParentBacked graph state.receiver.ledger)
    (flightBacked : WorkFlightBacked graph state.flight) :
    (deliverWork state).receiver.Valid ∧
      RecordParentBacked graph (deliverWork state).receiver.ledger ∧
      WorkFlightBacked graph (deliverWork state).flight := by
  cases queued : state.flight with
  | nil => simpa [deliverWork, queued] using And.intro valid (And.intro parentBacked flightBacked)
  | cons head tail =>
    by_cases ready : head.destination = state.receiver.ledger.owner ∧ head.id ≠ .root ∧
        head.id ∉ state.receiver.ledger.records.map Record.id
    · have headBacked := flightBacked head (by simp [queued])
      have tailBacked : WorkFlightBacked graph tail := by
        intro message member
        apply flightBacked message
        simp [queued, member]
      have incoming : (⟨head.parent.id, head.id, state.receiver.ledger.owner⟩ : Edge) ∈ graph := by
        simpa [WorkMessage.edge, ready.1] using headBacked.2
      have recordBacked := install_parent_backed state.receiver.ledger head.id head.parent graph parentBacked incoming
      have installedValid := local_step_valid valid (LocalStep.delivery state.receiver head.id head.parent)
      simp only [deliverWork, queued]
      rw [if_pos ready]
      exact ⟨installedValid, recordBacked, tailBacked⟩
    · simp only [deliverWork, queued]
      rw [if_neg ready]
      exact ⟨valid, parentBacked, flightBacked⟩

def WorkAddressed (workers : List Ledger) (message : WorkMessage) : Prop :=
  message.parent.worker = message.source ∧
  ∃ sender ∈ workers, sender.owner = message.source ∧
    ∃ parent ∈ sender.records, parent.id = message.parent.id ∧
      ∃ child ∈ parent.children, child.id = message.id ∧ child.destination = message.destination

def WorkFlightsAddressed (workers : List Ledger) (messages : List WorkMessage) : Prop :=
  ∀ message ∈ messages, WorkAddressed workers message

theorem published_work_addressed (workers : List Ledger) (l : Ledger) (ledgerMember : l ∈ workers)
    (id : Id) (parent : Address) (destination : Nat) (payload : List UInt8)
    (backed : WorkOutputsBacked l)
    (taken : (takeOutput l).2 = some (.work id parent destination payload)) :
    WorkAddressed workers ⟨l.owner, id, parent, destination, payload⟩ := by
  have actual := take_work_has_edge l backed id parent destination payload taken
  obtain ⟨r, rm, child, cm, equal⟩ := (edge_membership l _).mp actual.2
  have parentId : r.id = parent.id := by
    have h := congrArg Edge.parent equal
    simpa using h.symm
  have childId : child.id = id := by
    have h := congrArg Edge.child equal
    simpa using h.symm
  have childDestination : child.destination = destination := by
    have h := congrArg Edge.destination equal
    simpa using h.symm
  exact ⟨actual.1, l, ledgerMember, rfl, r, rm, parentId, child, cm, childId, childDestination⟩

theorem install_addressed_parent_backed (workers : List Ledger) (l : Ledger) (message : WorkMessage)
    (backed : AddressedParentBacked workers l) (addressed : WorkAddressed workers message)
    (destination : message.destination = l.owner) :
    AddressedParentBacked workers (install l message.id message.parent) := by
  by_cases reject : message.id = .root ∨ message.id ∈ l.records.map Record.id
  · simpa only [install, reject, ↓reduceIte] using backed
  · simp only [install, reject, ↓reduceIte, AddressedParentBacked]
    intro record member parent field
    simp only [insert, List.mem_append, List.mem_singleton] at member
    rcases member with old | same
    · exact backed record old parent field
    · subst record
      simp only [Option.some.injEq] at field
      subst parent
      obtain ⟨source, sender, lm, owner, r, rm, rid, child, cm, cid, dest⟩ := addressed
      refine ⟨sender, lm, ?_, r, rm, rid, child, cm, cid, ?_⟩
      · exact owner.trans source.symm
      · exact dest.trans destination

structure AckMessage where
  source : Nat
  parent : Address
  child : Id
  deriving DecidableEq, Repr

def AckAddressed (workers : List Ledger) (message : AckMessage) : Prop :=
  ∃ parentLedger ∈ workers, parentLedger.owner = message.parent.worker ∧
    ∃ r ∈ parentLedger.records, r.id = message.parent.id ∧
      ∃ child ∈ r.children, child.id = message.child ∧ child.destination = message.source

theorem retirement_ack_addressed (workers : List Ledger) (l : Ledger) (id : Id) (r : Record)
    (parent : Address) (backed : AddressedParentBacked workers l)
    (found : lookup Record.id id l.records = some r) (field : r.parent = some parent) :
    AckAddressed workers ⟨l.owner, parent, id⟩ := by
  have info := lookup_sound Record.id id l.records r found
  obtain ⟨ledger, lm, owner, parentRecord, rm, rid, child, cm, cid, dest⟩ := backed r info.1 parent field
  refine ⟨ledger, lm, owner, parentRecord, rm, rid, child, cm, ?_, dest⟩
  exact cid.trans info.2

theorem ack_addressed_edge (workers : List Ledger) (message : AckMessage)
    (addressed : AckAddressed workers message) :
    (⟨message.parent.id, message.child, message.source⟩ : Edge) ∈ ledgerGraph workers := by
  obtain ⟨ledger, lm, _, r, rm, rid, child, cm, cid, dest⟩ := addressed
  apply (graph_membership workers _).mpr
  refine ⟨ledger, lm, r, rm, child, cm, ?_⟩
  simp [rid, cid, dest]

theorem unique_ledger_owner_injective (workers : List Ledger) (a b : Ledger)
    (unique : (workers.map Ledger.owner).Nodup) (amem : a ∈ workers) (bmem : b ∈ workers)
    (same : a.owner = b.owner) : a = b := by
  induction workers with
  | nil => simp at amem
  | cons first rest ih =>
    have parts : first.owner ∉ rest.map Ledger.owner ∧ (rest.map Ledger.owner).Nodup := by
      simpa using unique
    rcases List.mem_cons.mp amem with aFirst | aRest
    · rcases List.mem_cons.mp bmem with bFirst | bRest
      · exact aFirst.trans bFirst.symm
      · subst a
        exact False.elim (parts.1 (List.mem_map.mpr ⟨b, bRest, same.symm⟩))
    · rcases List.mem_cons.mp bmem with bFirst | bRest
      · subst b
        exact False.elim (parts.1 (List.mem_map.mpr ⟨a, aRest, same⟩))
      · exact ih parts.2 aRest bRest

/-- An addressed acknowledgement resolves to the exact local whole child entry. -/
theorem ack_addressed_resolves (workers : List Ledger) (receiver : Ledger) (message : AckMessage)
    (uniqueOwners : (workers.map Ledger.owner).Nodup) (receiverMember : receiver ∈ workers)
    (receiverId : receiver.owner = message.parent.worker) (valid : LocalInvariant receiver)
    (addressed : AckAddressed workers message) :
    ∃ r child, lookup Record.id message.parent.id receiver.records = some r ∧
      lookup Child.id message.child r.children = some child ∧ child.destination = message.source := by
  obtain ⟨ledger, lm, owner, r, rm, rid, child, cm, cid, dest⟩ := addressed
  have same := unique_ledger_owner_injective workers ledger receiver uniqueOwners lm receiverMember
    (owner.trans receiverId.symm)
  subst ledger
  refine ⟨r, child, lookup_unique Record.id _ receiver.records r valid.2.1 rm rid, ?_, dest⟩
  exact lookup_unique Child.id _ r.children child ((valid.2.2 r rm).1) cm cid

theorem initialized_trace_ledger_owners_unique (owner : Nat) (others : List Nat)
    (distinct : (owner :: others).Nodup) {s : System}
    (trace : SystemTrace (initialSystem owner others) s) :
    (((s.root :: s.workers).map Tracked.ledger).map Ledger.owner).Nodup := by
  have owners : s.owners.Nodup := by
    rw [system_trace_owners trace, initialized_owners]
    exact distinct
  simpa [System.owners, List.map_map, Function.comp_def] using owners

theorem initialized_trace_worker_valid (owner : Nat) (others : List Nat) {s : System}
    (trace : SystemTrace (initialSystem owner others) s) (worker : Tracked)
    (member : worker ∈ s.root :: s.workers) : worker.Valid := by
  have valid := system_trace_valid (initial_system_valid owner others) trace
  rcases List.mem_cons.mp member with same | rest
  · subst worker; exact valid.1
  · exact (valid.2.2 worker rest).1

theorem initialized_trace_addressed_ack_removes (owner : Nat) (others : List Nat)
    (distinct : (owner :: others).Nodup) {s : System}
    (trace : SystemTrace (initialSystem owner others) s) (worker : Tracked)
    (member : worker ∈ s.root :: s.workers) (message : AckMessage)
    (receiverId : worker.ledger.owner = message.parent.worker)
    (addressed : AckAddressed ((s.root :: s.workers).map Tracked.ledger) message)
    (edge : Edge) :
    edge ∈ ledgerEdges (acknowledge worker.ledger message.parent.id message.child message.source) ↔
      edge ∈ ledgerEdges worker.ledger ∧ edge.child ≠ message.child := by
  have owners := initialized_trace_ledger_owners_unique owner others distinct trace
  have valid := initialized_trace_worker_valid owner others trace worker member
  have unique := initialized_trace_local_edges_unique owner others distinct trace worker member
  have workerMember : worker.ledger ∈ (s.root :: s.workers).map Tracked.ledger :=
    List.mem_map.mpr ⟨worker, member, rfl⟩
  obtain ⟨r, child, found, childFound, matched⟩ := ack_addressed_resolves _ worker.ledger message
    owners workerMember receiverId valid.1 addressed
  exact acknowledgement_exact_edge_removal worker.ledger message.parent.id message.child message.source
    r child valid.1 unique found childFound matched edge

end Ash.NetworkLedger.Coupling
