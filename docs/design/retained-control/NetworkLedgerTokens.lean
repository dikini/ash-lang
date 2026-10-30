import NetworkLedgerMessage

namespace Ash.NetworkLedger.Coupling

open Ash.NetworkLedger
open Ash.NetworkLedger.Reachability

/-- Tokens are extracted from actual output and record fields, not invented graph facts. -/
def outputToken : Output → Id
  | .work id _ _ _ => id
  | .ack _ id => id

def recordToken (r : Record) : Option Id :=
  match r.parent with
  | none => none
  | some _ => some r.id

def ledgerTokens (l : Ledger) : List Id :=
  l.outputs.map outputToken ++ l.records.filterMap recordToken

def protocolTokens (workers : List Ledger) (work : List WorkMessage) (acks : List AckMessage) : List Id :=
  workers.flatMap ledgerTokens ++ work.map WorkMessage.id ++ acks.map AckMessage.child

theorem initial_root_tokens_empty (owner : Nat) : ledgerTokens (initialRoot owner) = [] := by
  simp [ledgerTokens, initialRoot, recordToken]

theorem initial_worker_tokens_empty (owner : Nat) : ledgerTokens (initialWorker owner) = [] := by
  simp [ledgerTokens, initialWorker]

theorem published_work_moves_token (l : Ledger) (id : Id) (parent : Address)
    (destination : Nat) (payload : List UInt8) (tail : List Output)
    (head : l.outputs = .work id parent destination payload :: tail) :
    (takeOutput l).1.outputs.map outputToken ++ [id] =
      tail.map outputToken ++ [id] ∧
    (l.outputs.map outputToken).Perm (tail.map outputToken ++ [id]) := by
  simp only [take_output_head l _ tail head]
  constructor
  · trivial
  · simpa [head, outputToken] using (List.perm_append_singleton id (tail.map outputToken)).symm

theorem install_fresh_adds_record_token (l : Ledger) (id : Id) (parent : Address)
    (nonroot : id ≠ .root) (fresh : id ∉ l.records.map Record.id) :
    ledgerTokens (install l id parent) = ledgerTokens l ++ [id] := by
  rw [install_fresh l id parent nonroot fresh]
  simp [ledgerTokens, recordToken, insert, List.append_assoc]

theorem erase_record_at_lookup (q : Id) (records : List Record) (r : Record)
    (found : lookup Record.id q records = some r) :
    ∃ before after, records = before ++ r :: after ∧
      erase Record.id q records = before ++ after := by
  induction records with
  | nil => simp [lookup] at found
  | cons head tail ih =>
    by_cases same : head.id = q
    · simp [lookup, same] at found
      subst r
      exact ⟨[], tail, by simp, by simp [erase, same]⟩
    · simp [lookup, same] at found
      obtain ⟨before, after, split, removed⟩ := ih found
      refine ⟨head :: before, after, ?_, ?_⟩
      · simp [split]
      · simp [erase, same, removed]

theorem retirement_moves_record_token (l : Ledger) (id : Id) (r : Record) (parent : Address)
    (found : lookup Record.id id l.records = some r) (field : r.parent = some parent)
    (closed : r.phase = .closed) (empty : r.children = []) (nonroot : id ≠ .root) :
    (ledgerTokens (retire l id)).Perm (ledgerTokens l) := by
  have key := (lookup_sound Record.id id l.records r found).2
  obtain ⟨before, after, split, removed⟩ := erase_record_at_lookup id l.records r found
  have result := retire_ready_output l id r parent found field closed empty nonroot
  rw [result]
  simp only [ledgerTokens, remove_sequence]
  rw [removed, split]
  simp only [List.map_append, List.map_cons, List.map_nil, outputToken,
    List.filterMap_append, List.filterMap_cons, recordToken, field, List.append_assoc, key]
  exact (List.perm_middle (a := id) (l₁ := before.filterMap recordToken)
    (l₂ := after.filterMap recordToken)).symm.append_left (l.outputs.map outputToken)

theorem update_record_tokens (q : Id) (records : List Record) (r replacement : Record)
    (found : lookup Record.id q records = some r) (sameId : replacement.id = r.id)
    (sameParent : replacement.parent = r.parent) :
    (update Record.id q replacement records).filterMap recordToken = records.filterMap recordToken := by
  obtain ⟨before, after, split, _, updated⟩ :=
    lookup_update_decompose Record.id q replacement records r found
  have tokenEq : recordToken replacement = recordToken r := by
    simp [recordToken, sameId, sameParent]
  rw [updated, split]
  simp [List.filterMap_cons, tokenEq]

theorem close_tokens (l : Ledger) (q : Id) : ledgerTokens (close l q) = ledgerTokens l := by
  cases found : lookup Record.id q l.records with
  | none => simp [close, found]
  | some r =>
    by_cases closed : r.phase = .closed
    · simp [close, found, closed]
    · simp only [close, found, closed, ↓reduceIte, ledgerTokens]
      rw [update_record_tokens q l.records r { r with phase := .closed } found rfl rfl]

theorem ack_tokens (l : Ledger) (p child : Id) (peer : Nat) :
    ledgerTokens (acknowledge l p child peer) = ledgerTokens l := by
  cases found : lookup Record.id p l.records with
  | none => simp [acknowledge, found]
  | some r =>
    cases childFound : lookup Child.id child r.children with
    | none => simp [acknowledge, found, childFound]
    | some entry =>
      by_cases matched : entry.destination = peer
      · simp only [acknowledge, found, childFound, matched, ↓reduceIte, ledgerTokens]
        rw [update_record_tokens p l.records r
          { r with children := (remove Child.id child r.children).1 } found rfl rfl]
      · simp [acknowledge, found, childFound, matched]

theorem registration_adds_token (l : Ledger) (p : Id) (destination : Nat) (payload : List UInt8)
    (r : Record) (found : lookup Record.id p l.records = some r) (opened : r.phase = .open) :
    (ledgerTokens (register l p destination payload).1).Perm
      (ledgerTokens l ++ [.work l.owner l.next]) := by
  rw [register_open l p destination payload r found opened]
  simp only [ledgerTokens, List.map_append, List.map_cons, List.map_nil, outputToken]
  rw [update_record_tokens p l.records r
    { r with children := insert ⟨.work l.owner l.next, destination⟩ r.children } found rfl rfl]
  let token := Id.work l.owner l.next
  have moved := (List.perm_append_singleton token (l.records.filterMap recordToken)).symm
  simpa [token, List.append_assoc] using moved.append_left (l.outputs.map outputToken)

def publicationTokens (state : PublicationState) : List Id :=
  ledgerTokens state.current.ledger ++ state.flight.map WorkMessage.id

theorem publish_work_moves_token (state : PublicationState) :
    (publicationTokens (publishWork state)).Perm (publicationTokens state) := by
  cases queued : state.current.ledger.outputs with
  | nil => simp [publicationTokens, publishWork, takeOutput, queued]
  | cons head tail =>
    cases head with
    | ack parent child => simp [publicationTokens, publishWork, takeOutput, queued]
    | work id parent destination payload =>
      have moved := List.perm_append_singleton id
        (tail.map outputToken ++ state.current.ledger.records.filterMap recordToken ++
          state.flight.map WorkMessage.id)
      simpa [publicationTokens, publishWork, takeOutput, queued, ledgerTokens, outputToken,
        List.append_assoc] using moved

def deliveryTokens (state : DeliveryState) : List Id :=
  ledgerTokens state.receiver.ledger ++ state.flight.map WorkMessage.id

theorem deliver_work_moves_token (state : DeliveryState) :
    deliveryTokens (deliverWork state) = deliveryTokens state := by
  cases queued : state.flight with
  | nil => simp [deliveryTokens, deliverWork, queued]
  | cons head tail =>
    by_cases ready : head.destination = state.receiver.ledger.owner ∧ head.id ≠ .root ∧
        head.id ∉ state.receiver.ledger.records.map Record.id
    · simp only [deliveryTokens, deliverWork, queued]
      rw [if_pos ready]
      simp only [install_fresh_adds_record_token state.receiver.ledger head.id head.parent ready.2.1 ready.2.2,
        List.map_cons, List.append_assoc, List.singleton_append]
    · simp only [deliveryTokens, deliverWork, queued]
      rw [if_neg ready]
      simp [queued]

structure AckPublicationState where
  current : Tracked
  flight : List AckMessage
  deriving Repr

def publishAck (state : AckPublicationState) : AckPublicationState :=
  match takeOutput state.current.ledger with
  | (next, some (.ack parent child)) =>
    ⟨⟨next, state.current.history⟩,
      state.flight ++ [⟨state.current.ledger.owner, parent, child⟩]⟩
  | _ => state

def ackPublicationTokens (state : AckPublicationState) : List Id :=
  ledgerTokens state.current.ledger ++ state.flight.map AckMessage.child

theorem publish_ack_moves_token (state : AckPublicationState) :
    (ackPublicationTokens (publishAck state)).Perm (ackPublicationTokens state) := by
  cases queued : state.current.ledger.outputs with
  | nil => simp [ackPublicationTokens, publishAck, takeOutput, queued]
  | cons head tail =>
    cases head with
    | work id parent destination payload => simp [ackPublicationTokens, publishAck, takeOutput, queued]
    | ack parent child =>
      have moved := List.perm_append_singleton child
        (tail.map outputToken ++ state.current.ledger.records.filterMap recordToken ++
          state.flight.map AckMessage.child)
      simpa [ackPublicationTokens, publishAck, takeOutput, queued, ledgerTokens, outputToken,
        List.append_assoc] using moved

structure AckDeliveryState where
  receiver : Tracked
  flight : List AckMessage
  deriving Repr

def deliverAck (state : AckDeliveryState) : AckDeliveryState :=
  match state.flight with
  | [] => state
  | message :: tail =>
    if message.parent.worker = state.receiver.ledger.owner then
      ⟨⟨acknowledge state.receiver.ledger message.parent.id message.child message.source,
        state.receiver.history⟩, tail⟩
    else state

def ackDeliveryTokens (state : AckDeliveryState) : List Id :=
  ledgerTokens state.receiver.ledger ++ state.flight.map AckMessage.child

theorem delivered_ack_removes_token (state : AckDeliveryState) (message : AckMessage)
    (tail : List AckMessage) (queued : state.flight = message :: tail)
    (destination : message.parent.worker = state.receiver.ledger.owner) :
    ackDeliveryTokens (deliverAck state) = ledgerTokens state.receiver.ledger ++ tail.map AckMessage.child ∧
    ackDeliveryTokens state = ledgerTokens state.receiver.ledger ++ message.child :: tail.map AckMessage.child := by
  simp only [ackDeliveryTokens, deliverAck, queued]
  rw [if_pos destination]
  simp [ack_tokens]

theorem queued_work_token (workers : List Ledger) (l : Ledger) (id : Id) (parent : Address)
    (destination : Nat) (payload : List UInt8) (member : l ∈ workers)
    (queued : Output.work id parent destination payload ∈ l.outputs) :
    id ∈ workers.flatMap ledgerTokens := by
  apply List.mem_flatMap.mpr
  refine ⟨l, member, ?_⟩
  simp only [ledgerTokens, List.mem_append]
  left
  exact List.mem_map.mpr ⟨.work id parent destination payload, queued, rfl⟩

theorem running_record_token (workers : List Ledger) (l : Ledger) (r : Record) (parent : Address)
    (member : l ∈ workers) (record : r ∈ l.records) (parentField : r.parent = some parent) :
    r.id ∈ workers.flatMap ledgerTokens := by
  apply List.mem_flatMap.mpr
  refine ⟨l, member, ?_⟩
  simp only [ledgerTokens, List.mem_append]
  right
  apply List.mem_filterMap.mpr
  exact ⟨r, record, by simp [recordToken, parentField]⟩

/-- A single-token invariant derives that an acknowledged child has no queued work. -/
theorem ack_flight_excludes_queued_work (workers : List Ledger) (work : List WorkMessage)
    (acks : List AckMessage) (unique : (protocolTokens workers work acks).Nodup)
    (message : AckMessage) (inFlight : message ∈ acks) (l : Ledger) (member : l ∈ workers)
    (parent : Address) (destination : Nat) (payload : List UInt8) :
    Output.work message.child parent destination payload ∉ l.outputs := by
  intro queued
  have earlier := queued_work_token workers l message.child parent destination payload member queued
  have parts := List.nodup_append.mp unique
  exact (parts.2.2 message.child (List.mem_append_left _ earlier) message.child
    (List.mem_map.mpr ⟨message, inFlight, rfl⟩)) rfl

theorem ack_flight_excludes_running_record (workers : List Ledger) (work : List WorkMessage)
    (acks : List AckMessage) (unique : (protocolTokens workers work acks).Nodup)
    (message : AckMessage) (inFlight : message ∈ acks) (l : Ledger) (member : l ∈ workers)
    (r : Record) (record : r ∈ l.records) (parent : Address) (field : r.parent = some parent) :
    r.id ≠ message.child := by
  intro equal
  have earlier := running_record_token workers l r parent member record field
  have parts := List.nodup_append.mp unique
  exact (parts.2.2 r.id (List.mem_append_left _ earlier) message.child
    (List.mem_map.mpr ⟨message, inFlight, rfl⟩)) equal

theorem initialized_protocol_tokens_empty (owner : Nat) (others : List Nat) :
    protocolTokens (((initialSystem owner others).root :: (initialSystem owner others).workers).map Tracked.ledger)
      [] [] = [] := by
  simp [protocolTokens, initialSystem, trackedRoot, trackedWorker, ledgerTokens, initialRoot,
    initialWorker, recordToken, List.flatMap_map, List.map_map, Function.comp_def]

def ParentShape (l : Ledger) : Prop :=
  ∀ r ∈ l.records, r.id ≠ .root → ∃ parent, r.parent = some parent

theorem initial_root_parent_shape (owner : Nat) : ParentShape (initialRoot owner) := by
  simp [ParentShape, initialRoot]

theorem initial_worker_parent_shape (owner : Nat) : ParentShape (initialWorker owner) := by
  simp [ParentShape, initialWorker]

theorem parent_shape_update (l : Ledger) (q : Id) (r replacement : Record)
    (shape : ParentShape l) (found : lookup Record.id q l.records = some r)
    (sameId : replacement.id = r.id) (sameParent : replacement.parent = r.parent) :
    ParentShape { l with records := update Record.id q replacement l.records } := by
  have member := (lookup_sound Record.id q l.records r found).1
  apply update_all Record.id q replacement l.records
    (fun x => x.id ≠ .root → ∃ parent, x.parent = some parent) shape
  intro nonroot
  have oldNonroot : r.id ≠ .root := by simpa [sameId] using nonroot
  obtain ⟨parent, field⟩ := shape r member oldNonroot
  exact ⟨parent, by simpa [sameParent] using field⟩

theorem register_parent_shape (l : Ledger) (q : Id) (destination : Nat) (payload : List UInt8)
    (shape : ParentShape l) : ParentShape (register l q destination payload).1 := by
  cases found : lookup Record.id q l.records with
  | none => simpa [register, found] using shape
  | some r =>
    by_cases closed : r.phase = .closed
    · simpa [register, found, closed] using shape
    · simp only [register, found, closed, ↓reduceIte]
      exact parent_shape_update l q r
        { r with children := insert ⟨.work l.owner l.next, destination⟩ r.children } shape found rfl rfl

theorem close_parent_shape (l : Ledger) (q : Id) (shape : ParentShape l) :
    ParentShape (close l q) := by
  cases found : lookup Record.id q l.records with
  | none => simpa [close, found] using shape
  | some r =>
    by_cases closed : r.phase = .closed
    · simpa [close, found, closed] using shape
    · simp only [close, found, closed, ↓reduceIte]
      exact parent_shape_update l q r { r with phase := .closed } shape found rfl rfl

theorem retire_parent_shape (l : Ledger) (q : Id) (shape : ParentShape l) :
    ParentShape (retire l q) := by
  cases found : lookup Record.id q l.records with
  | none => simpa [retire, found] using shape
  | some r =>
    cases parent : r.parent with
    | none => simpa [retire, found, parent] using shape
    | some address =>
      by_cases ready : r.phase = .closed ∧ r.children = [] ∧ q ≠ .root
      · simp only [retire, found, parent, ready.1, ready.2.1, true_and]
        rw [if_pos ready.2.2]
        intro x member
        exact shape x ((erase_retains_whole_order Record.id q l.records).mem member)
      · simpa [retire, found, parent, ready] using shape

theorem ack_parent_shape (l : Ledger) (p child : Id) (peer : Nat) (shape : ParentShape l) :
    ParentShape (acknowledge l p child peer) := by
  cases found : lookup Record.id p l.records with
  | none => simpa [acknowledge, found] using shape
  | some r =>
    cases childFound : lookup Child.id child r.children with
    | none => simpa [acknowledge, found, childFound] using shape
    | some entry =>
      by_cases matched : entry.destination = peer
      · simp only [acknowledge, found, childFound, matched, ↓reduceIte]
        exact parent_shape_update l p r
          { r with children := (remove Child.id child r.children).1 } shape found rfl rfl
      · simpa [acknowledge, found, childFound, matched] using shape

theorem install_parent_shape (l : Ledger) (id : Id) (parent : Address) (shape : ParentShape l) :
    ParentShape (install l id parent) := by
  by_cases reject : id = .root ∨ id ∈ l.records.map Record.id
  · simpa only [install, reject, ↓reduceIte] using shape
  · simp only [install, reject, ↓reduceIte, ParentShape]
    intro r member nonroot
    simp only [insert, List.mem_append, List.mem_singleton] at member
    rcases member with old | same
    · exact shape r old nonroot
    · subst r
      exact ⟨parent, rfl⟩

theorem local_step_parent_shape {before after : Tracked} (shape : ParentShape before.ledger)
    (step : LocalStep before after) : ParentShape after.ledger := by
  cases step with
  | noop => exact shape
  | action action =>
    cases action with
    | register q d payload =>
      cases result : register before.ledger q d payload with
      | mk l status =>
        cases status <;> simpa [Tracked.run, Tracked.register, result] using
          register_parent_shape before.ledger q d payload shape
    | close q => exact close_parent_shape before.ledger q shape
    | retire q => exact retire_parent_shape before.ledger q shape
    | ack p child peer => exact ack_parent_shape before.ledger p child peer shape
  | delivery id parent => exact install_parent_shape before.ledger id parent shape
  | take => simpa [ParentShape, (take_output_frames before.ledger).2.2] using shape

def System.Shaped (s : System) : Prop :=
  ParentShape s.root.ledger ∧ ∀ worker ∈ s.workers, ParentShape worker.ledger

theorem initial_system_shaped (owner : Nat) (others : List Nat) :
    (initialSystem owner others).Shaped := by
  refine ⟨initial_root_parent_shape owner, ?_⟩
  intro worker member
  obtain ⟨workerOwner, _, equal⟩ := List.mem_map.mp member
  subst worker
  exact initial_worker_parent_shape workerOwner

theorem system_step_shaped {s t : System} (shaped : s.Shaped) (step : SystemStep s t) :
    t.Shaped := by
  cases step with
  | root next localStep => exact ⟨local_step_parent_shape shaped.1 localStep, shaped.2⟩
  | worker before after old next workers localStep =>
    refine ⟨shaped.1, ?_⟩
    have oldMember : old ∈ s.workers := by rw [workers]; simp
    intro worker member
    simp only [List.mem_append, List.mem_cons] at member
    rcases member with earlier | equal | later
    · exact shaped.2 worker (by rw [workers]; simp [earlier])
    · subst worker
      exact local_step_parent_shape (shaped.2 old oldMember) localStep
    · exact shaped.2 worker (by rw [workers]; simp [later])

theorem system_trace_shaped {s t : System} (shaped : s.Shaped) (trace : SystemTrace s t) :
    t.Shaped := by
  induction trace with
  | refl => exact shaped
  | next history step ih => exact system_step_shaped ih step

theorem ledger_edge_nonroot (l : Ledger) (valid : LocalInvariant l) (edge : Edge)
    (member : edge ∈ ledgerEdges l) : edge.child ≠ .root := by
  obtain ⟨r, rm, child, cm, equal⟩ := (edge_membership l edge).mp member
  have validChild := (valid.2.2 r rm).2 child cm
  intro isRoot
  have childRoot : child.id = .root := by simpa [equal] using isRoot
  simp [ChildValid, childRoot] at validChild

theorem initialized_trace_graph_nonroot (owner : Nat) (others : List Nat) {s : System}
    (trace : SystemTrace (initialSystem owner others) s) (edge : Edge)
    (member : edge ∈ trackedGraph (s.root :: s.workers)) : edge.child ≠ .root := by
  obtain ⟨worker, wm, em⟩ := (tracked_graph_member _ edge).mp member
  exact ledger_edge_nonroot worker.ledger (initialized_trace_worker_valid owner others trace worker wm).1 edge em

theorem initialized_trace_ack_nonroot (owner : Nat) (others : List Nat) {s : System}
    (trace : SystemTrace (initialSystem owner others) s) (message : AckMessage)
    (addressed : AckAddressed ((s.root :: s.workers).map Tracked.ledger) message) :
    message.child ≠ .root := by
  have edge := ack_addressed_edge _ message addressed
  rw [← tracked_graph_is_ledger_graph] at edge
  exact initialized_trace_graph_nonroot owner others trace _ edge

/-- Single-token accounting derives the leaf condition for an addressed in-flight ack. -/
theorem initialized_trace_ack_leaf (owner : Nat) (others : List Nat) {s : System}
    (trace : SystemTrace (initialSystem owner others) s) (work : List WorkMessage)
    (acks : List AckMessage)
    (unique : (protocolTokens ((s.root :: s.workers).map Tracked.ledger) work acks).Nodup)
    (message : AckMessage) (inFlight : message ∈ acks)
    (addressed : AckAddressed ((s.root :: s.workers).map Tracked.ledger) message) :
    Leaf (trackedGraph (s.root :: s.workers)) message.child := by
  have nonroot := initialized_trace_ack_nonroot owner others trace message addressed
  have shaped := system_trace_shaped (initial_system_shaped owner others) trace
  intro edge edgeMember parentId
  obtain ⟨worker, wm, em⟩ := (tracked_graph_member _ edge).mp edgeMember
  obtain ⟨r, rm, child, cm, equal⟩ := (edge_membership worker.ledger edge).mp em
  have rid : r.id = message.child := by simpa [equal] using parentId
  have rnonroot : r.id ≠ .root := by simpa [rid] using nonroot
  have workerShape : ParentShape worker.ledger := by
    rcases List.mem_cons.mp wm with same | rest
    · subst worker; exact shaped.1
    · exact shaped.2 worker rest
  obtain ⟨parent, field⟩ := workerShape r rm rnonroot
  have workerLedgerMember : worker.ledger ∈ (s.root :: s.workers).map Tracked.ledger :=
    List.mem_map.mpr ⟨worker, wm, rfl⟩
  exact (ack_flight_excludes_running_record _ work acks unique message inFlight
    worker.ledger workerLedgerMember r rm parent field) rid

theorem publish_work_local_step (t : Tracked) (flight : List WorkMessage) :
    LocalStep t (publishWork ⟨t, flight⟩).current := by
  cases queued : t.ledger.outputs with
  | nil => simpa [publishWork, takeOutput, queued] using LocalStep.noop t
  | cons head tail =>
    cases head with
    | ack parent child => simpa [publishWork, takeOutput, queued] using LocalStep.noop t
    | work id parent destination payload =>
      simpa [publishWork, takeOutput, queued] using LocalStep.take t

theorem publish_ack_local_step (t : Tracked) (flight : List AckMessage) :
    LocalStep t (publishAck ⟨t, flight⟩).current := by
  cases queued : t.ledger.outputs with
  | nil => simpa [publishAck, takeOutput, queued] using LocalStep.noop t
  | cons head tail =>
    cases head with
    | work id parent destination payload => simpa [publishAck, takeOutput, queued] using LocalStep.noop t
    | ack parent child => simpa [publishAck, takeOutput, queued] using LocalStep.take t

theorem deliver_work_local_step (t : Tracked) (flight : List WorkMessage) :
    LocalStep t (deliverWork ⟨t, flight⟩).receiver := by
  cases queued : flight with
  | nil => simpa [deliverWork, queued] using LocalStep.noop t
  | cons head tail =>
    by_cases ready : head.destination = t.ledger.owner ∧ head.id ≠ .root ∧
        head.id ∉ t.ledger.records.map Record.id
    · simp only [deliverWork]
      rw [if_pos ready]
      exact LocalStep.delivery t head.id head.parent
    · simp only [deliverWork]
      rw [if_neg ready]
      exact LocalStep.noop t

theorem deliver_ack_local_step (t : Tracked) (flight : List AckMessage) :
    LocalStep t (deliverAck ⟨t, flight⟩).receiver := by
  cases queued : flight with
  | nil => simpa [deliverAck, queued] using LocalStep.noop t
  | cons head tail =>
    by_cases ready : head.parent.worker = t.ledger.owner
    · simp only [deliverAck]
      rw [if_pos ready]
      exact LocalStep.action t (.ack head.parent.id head.child head.source)
    · simp only [deliverAck]
      rw [if_neg ready]
      exact LocalStep.noop t

end Ash.NetworkLedger.Coupling
