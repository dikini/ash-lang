/-
Finite two-worker/channel safety model. Each step is an abstract atomic action;
Rust, OS, admission, byte-copy and C3 correspondence require separate review.
Received entries, operation keys and callback keys retain distinct identities.
-/
import Std
import Ownership
namespace Ash.WorkerChannel
abbrev Message := List UInt8
structure Entry where
  id : Nat
  bytes : Message
  deriving DecidableEq, Repr
structure Channel where
  capacity : Nat
  accepted : List Entry
  received : List Entry
  queue : List Entry
  done : List Entry
  held : List Entry
  sealed : Bool
  observedEnd : Bool
  failed : Bool
  deriving Repr

def Channel.Safe (c : Channel) : Prop :=
  0 < c.capacity ∧ c.accepted = c.received ++ c.queue ∧ c.queue.length ≤ c.capacity ∧
  (c.accepted.map Entry.id).Nodup ∧ c.received.Perm (c.done ++ c.held) ∧
  (c.observedEnd = true → c.sealed = true ∧ c.queue = [])

def Channel.initial (capacity : Nat) : Channel := ⟨capacity, [], [], [], [], [], false, false, false⟩

theorem channel_initial_safe (n : Nat) (h : 0 < n) : (Channel.initial n).Safe := by
  simp [Channel.Safe, Channel.initial, h]

inductive Side where
  | read | write
  deriving DecidableEq, Repr

inductive ChannelStep : Side → Channel → Channel → Prop where
  | idle (c : Channel) (side : Side) : ChannelStep side c c
  | send (c : Channel) (e : Entry) (fresh : e.id ∉ c.accepted.map Entry.id)
      (openSend : c.sealed = false) (healthy : c.failed = false) (room : c.queue.length < c.capacity) :
      ChannelStep .write c { c with accepted := c.accepted ++ [e], queue := c.queue ++ [e] }
  | receive (c : Channel) (e : Entry) (tail : List Entry)
      (head : c.queue = e :: tail) (healthy : c.failed = false) :
      ChannelStep .read c { c with received := c.received ++ [e], queue := tail, held := c.held ++ [e] }
  | closeSend (c : Channel) (healthy : c.failed = false) : ChannelStep .write c { c with sealed := true }
  | observeEnd (c : Channel) (healthy : c.failed = false) (sealed : c.sealed = true)
      (empty : c.queue = []) : ChannelStep .read c { c with observedEnd := true }

theorem channel_step_safe {side : Side} {c d : Channel} (safe : c.Safe)
    (step : ChannelStep side c d) : d.Safe := by
  rcases safe with ⟨positive, fifo, cap, unique, cover, endSafe⟩
  cases step with
  | idle => exact ⟨positive, fifo, cap, unique, cover, endSafe⟩
  | send _ e fresh op healthy room =>
    refine ⟨positive, ?_, ?_, ?_, cover, ?_⟩
    · simp [fifo, List.append_assoc]
    · simp; omega
    · simp only [List.map_append, List.map_cons, List.map_nil, List.nodup_append]
      refine ⟨unique, by simp, ?_⟩
      intro x hx y hy eq
      simp only [List.mem_singleton] at hy
      apply fresh
      simpa [eq, hy] using hx
    · intro ended
      have sealed := (endSafe ended).1
      simp_all
  | receive _ e tail head healthy =>
    refine ⟨positive, ?_, ?_, unique, ?_, ?_⟩
    · rw [head] at fifo
      simpa [List.append_assoc] using fifo
    · simp [head] at cap
      change tail.length ≤ c.capacity
      omega
    · simpa [List.append_assoc] using cover.append_right [e]
    · intro ended
      have empty := (endSafe ended).2
      simp_all
  | closeSend =>
    refine ⟨positive, fifo, cap, unique, cover, ?_⟩
    intro ended
    exact ⟨rfl, (endSafe ended).2⟩
  | observeEnd _ healthy sealed empty =>
    exact ⟨positive, fifo, cap, unique, cover, fun _ ↦ ⟨sealed, empty⟩⟩

def finishChannel (c : Channel) (e : Entry) (pre post : List Entry) : Channel :=
  { c with held := pre ++ post, done := c.done ++ [e] }

theorem finish_channel_safe (c : Channel) (e : Entry) (pre post : List Entry)
    (safe : c.Safe) (found : c.held = pre ++ e :: post) : (finishChannel c e pre post).Safe := by
  rcases safe with ⟨positive, fifo, cap, unique, cover, endSafe⟩
  refine ⟨positive, fifo, cap, unique, ?_, endSafe⟩
  rw [found] at cover
  apply cover.trans
  simp only [finishChannel, List.append_assoc]
  apply List.Perm.append_left
  exact List.perm_middle
theorem finished_entry_cannot_repeat (c : Channel) (e : Entry) (pre post : List Entry)
    (safe : c.Safe) (found : c.held = pre ++ e :: post) :
    e.id ∉ (finishChannel c e pre post).held.map Entry.id := by
  rcases safe with ⟨_, fifo, _, unique, cover, _⟩
  have recUnique : (c.received.map Entry.id).Nodup := by
    rw [fifo, List.map_append] at unique
    exact (List.nodup_append.mp unique).1
  have combined : ((c.done ++ c.held).map Entry.id).Nodup := (cover.map Entry.id).nodup recUnique
  have heldUnique : (c.held.map Entry.id).Nodup := by
    rw [List.map_append] at combined
    exact (List.nodup_append.mp combined).2.1
  rw [found] at heldUnique
  simp only [List.map_append, List.map_cons, List.nodup_append, List.nodup_cons] at heldUnique
  simp only [finishChannel, List.map_append, List.mem_append, not_or]
  constructor
  · intro h
    exact heldUnique.2.2 _ h _ (by simp) rfl
  · exact heldUnique.2.1.1
theorem channel_step_preserves_held {side : Side} {a b : Channel}
    (step : ChannelStep side a b) (e : Entry) (held : e ∈ a.held) : e ∈ b.held := by
  cases step <;> simp_all

theorem finish_preserves_other (c : Channel) (e x : Entry) (pre post : List Entry)
    (found : c.held = pre ++ e :: post) (member : x ∈ c.held) (distinct : x.id ≠ e.id) :
    x ∈ (finishChannel c e pre post).held := by
  simp only [found, List.mem_append, List.mem_cons] at member
  simp only [finishChannel, List.mem_append]
  rcases member with left | same | right
  · exact Or.inl left
  · subst x; exact False.elim (distinct rfl)
  · exact Or.inr right

def put {α : Type} (f : Nat → α) (key : Nat) (value : α) : Nat → α :=
  fun i ↦ if i = key then value else f i

structure Watch where
  next : Nat
  active : Nat → Bool
  pending : Nat → Bool
  callbackNext : Nat
  callbacks : Nat → Option Nat

def Watch.Valid (w : Watch) : Prop :=
  (∀ g, w.next ≤ g → w.active g = false ∧ w.pending g = false) ∧
  (∀ g, w.pending g = true → w.active g = true) ∧
  (∀ id, w.callbackNext ≤ id → w.callbacks id = none)

def Watch.initial : Watch := ⟨0, fun _ ↦ false, fun _ ↦ false, 0, fun _ ↦ none⟩

def Watch.signal (w : Watch) (ready : Bool) : Watch :=
  { w with pending := fun g ↦ w.pending g || (w.active g && ready) }

def Watch.register (w : Watch) (ready : Bool) : Watch :=
  ⟨w.next + 1, put w.active w.next true, put w.pending w.next ready, w.callbackNext, w.callbacks⟩

def Watch.cancel (w : Watch) (generation : Nat) : Watch :=
  ⟨w.next, put w.active generation false, put w.pending generation false, w.callbackNext, w.callbacks⟩

def Watch.poll (w : Watch) (generation : Nat) (ready : Bool) : Watch :=
  let refreshed := w.signal ready
  ⟨w.next, w.active, put refreshed.pending generation false, w.callbackNext + 1,
    put w.callbacks w.callbackNext (some generation)⟩

def Watch.completeCallback (w : Watch) (id : Nat) : Watch :=
  { w with callbacks := put w.callbacks id none }

theorem watch_signal_valid (w : Watch) (ready : Bool) (valid : w.Valid) :
    (w.signal ready).Valid := by
  rcases valid with ⟨finite, pending, callbacks⟩
  refine ⟨?_, ?_, callbacks⟩
  · intro g bound
    have h := finite g bound
    simp [Watch.signal, h.1, h.2]
  · intro g h
    simp only [Watch.signal, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨h, _⟩
    · exact pending g h
    · exact h

theorem watch_register_valid (w : Watch) (ready : Bool) (valid : w.Valid) :
    (w.register ready).Valid := by
  rcases valid with ⟨finite, pending, callbacks⟩
  refine ⟨?_, ?_, callbacks⟩
  · intro g bound
    change w.next + 1 ≤ g at bound
    have ne : g ≠ w.next := by omega
    have h := finite g (by omega)
    simp [Watch.register, put, ne, h.1, h.2]
  · intro g h
    by_cases eq : g = w.next
    · subst g; simp [Watch.register, put]
    · simp only [Watch.register, put, if_neg eq] at h ⊢
      exact pending g h

theorem watch_cancel_valid (w : Watch) (generation : Nat) (valid : w.Valid) :
    (w.cancel generation).Valid := by
  rcases valid with ⟨finite, pending, callbacks⟩
  refine ⟨?_, ?_, callbacks⟩
  · intro g bound
    by_cases eq : g = generation
    · subst g; simp [Watch.cancel, put]
    · have h := finite g bound
      simp [Watch.cancel, put, eq, h.1, h.2]
  · intro g h
    by_cases eq : g = generation
    · subst g; simp [Watch.cancel, put] at h
    · simp only [Watch.cancel, put, if_neg eq] at h ⊢
      exact pending g h

theorem watch_poll_valid (w : Watch) (generation : Nat) (ready : Bool) (valid : w.Valid) :
    (w.poll generation ready).Valid := by
  have signaled := watch_signal_valid w ready valid
  rcases signaled with ⟨finite, pending, _⟩
  refine ⟨?_, ?_, ?_⟩
  · intro g bound
    change w.next ≤ g at bound
    have h := finite g bound
    simp only [Watch.signal] at h
    by_cases eq : g = generation
    · subst g; simp [Watch.poll, put, h.1]
    · have original := valid.1 g bound
      simp [Watch.poll, Watch.signal, put, eq, original.1, original.2]
  · intro g h
    by_cases eq : g = generation
    · subst g; simp [Watch.poll, put] at h
    · simp only [Watch.poll, put, if_neg eq] at h ⊢
      exact pending g h
  · intro id bound
    change w.callbackNext + 1 ≤ id at bound
    have ne : id ≠ w.callbackNext := by omega
    have h := valid.2.2 id (by omega)
    simp [Watch.poll, put, ne, h]

theorem watch_complete_valid (w : Watch) (id : Nat) (valid : w.Valid) :
    (w.completeCallback id).Valid := by
  rcases valid with ⟨finite, pending, callbacks⟩
  refine ⟨finite, pending, ?_⟩
  intro k bound
  simp only [Watch.completeCallback, put]
  split
  · rfl
  · exact callbacks k bound

theorem watch_signal_fresh (w : Watch) (valid : w.Valid) :
    w.callbacks w.callbackNext = none := valid.2.2 _ (Nat.le_refl _)

theorem watch_completion_once (w : Watch) (id : Nat) :
    (w.completeCallback id).callbacks id = none := by simp [Watch.completeCallback, put]

theorem watch_two_live (w : Watch) (firstReady secondReady : Bool) :
    ((w.register firstReady).register secondReady).active w.next = true ∧
    ((w.register firstReady).register secondReady).active (w.next + 1) = true := by
  simp [Watch.register, put]

theorem watch_registration_fresh (w : Watch) (valid : w.Valid) (ready : Bool) :
    w.active w.next = false ∧ w.pending w.next = false ∧
      (w.register ready).active w.next = true := by
  have before := valid.1 w.next (Nat.le_refl _)
  exact ⟨before.1, before.2, by simp [Watch.register, put]⟩

theorem watch_two_ready (w : Watch) (firstReady secondReady : Bool) :
    (((w.register firstReady).register secondReady).signal true).pending w.next = true ∧
    (((w.register firstReady).register secondReady).signal true).pending (w.next + 1) = true := by
  simp [Watch.signal, Watch.register, put]

theorem watch_signal_coalesces (w : Watch) (ready : Bool) :
    (w.signal ready).signal ready = w.signal ready := by
  cases w with
  | mk next active pending callbackNext callbacks =>
    simp [Watch.signal]

theorem watch_cancel_preserves_other (w : Watch) (g other : Nat) (different : other ≠ g) :
    (w.cancel g).active other = w.active other ∧ (w.cancel g).pending other = w.pending other := by
  simp [Watch.cancel, put, different]

theorem watch_poll_preserves_other_pending (w : Watch) (g other : Nat) (ready : Bool)
    (different : other ≠ g) (pending : w.pending other = true) :
    (w.poll g ready).pending other = true := by
  simp [Watch.poll, Watch.signal, put, different, pending]

theorem watch_cancel_preserves_callbacks (w : Watch) (g id : Nat) :
    (w.cancel g).callbacks id = w.callbacks id := rfl

theorem watch_poll_preserves_old_callbacks (w : Watch) (g id : Nat) (ready : Bool)
    (old : id < w.callbackNext) : (w.poll g ready).callbacks id = w.callbacks id := by
  simp [Watch.poll, put, Nat.ne_of_lt old]

theorem two_watches_poll_keeps_other (w : Watch) (firstReady secondReady : Bool) :
    let both := ((w.register firstReady).register secondReady).signal true
    (both.poll w.next true).pending (w.next + 1) = true := by
  apply watch_poll_preserves_other_pending
  · omega
  · exact (watch_two_ready w firstReady secondReady).2

theorem two_watches_cancel_keeps_other (w : Watch) (firstReady secondReady : Bool) :
    let both := ((w.register firstReady).register secondReady).signal true
    (both.cancel w.next).active (w.next + 1) = true ∧
      (both.cancel w.next).pending (w.next + 1) = true := by
  simp [Watch.cancel, Watch.signal, Watch.register, put]

theorem watch_poll_transfers_one (w : Watch) (g : Nat) (ready : Bool) :
    (w.poll g ready).pending g = false ∧
    (w.poll g ready).callbacks w.callbackNext = some g := by
  simp [Watch.poll, put]


def Channel.ready (c : Channel) : Side → Bool
  | .read => c.failed || c.sealed || !c.queue.isEmpty
  | .write => c.failed || c.sealed || (c.queue.length < c.capacity)

theorem late_terminal_registration (w : Watch) :
    (w.register true).active w.next = true ∧ (w.register true).pending w.next = true := by
  simp [Watch.register, put]

theorem signal_ready_pending (w : Watch) (g : Nat) (active : w.active g = true) :
    (w.signal true).pending g = true := by
  simp [Watch.signal, active]

theorem terminal_signal_all (w : Watch) :
    ∀ g, w.active g = true → (w.signal true).pending g = true := by
  intro g active
  exact signal_ready_pending w g active

theorem cancelled_generation_cannot_be_current (w : Watch) (g : Nat) :
    (w.cancel g).active g = false ∧ (w.cancel g).pending g = false := by simp [Watch.cancel, put]

inductive Worker where
  | first | second
  deriving DecidableEq, Repr

def Worker.peer : Worker → Worker
  | .first => .second
  | .second => .first

theorem Worker.peer_peer (w : Worker) : w.peer.peer = w := by cases w <;> rfl

def sideOwner (lane : Worker) : Side → Worker
  | .write => lane
  | .read => lane.peer

def putWorker {α : Type} (f : Worker → α) (w : Worker) (x : α) : Worker → α :=
  fun i ↦ if i = w then x else f i

def putSide {α : Type} (f : Side → α) (side : Side) (x : α) : Side → α :=
  fun i ↦ if i = side then x else f i

structure Operation where
  lane : Worker
  side : Side
  owner : Worker
  deriving DecidableEq, Repr

def DistinctStores (stores : Worker → RetainedControl.State) : Prop :=
  (stores .first).storeId ≠ (stores .second).storeId ∧
  (stores .first).storeOwner ≠ (stores .second).storeOwner

theorem c1_store_identity {a b : RetainedControl.State} {created : List Nat}
    (step : RetainedControl.Step a created b) :
    b.storeId = a.storeId ∧ b.storeOwner = a.storeOwner := by
  cases step <;> exact ⟨rfl, rfl⟩

theorem update_distinct_stores (stores : Worker → RetainedControl.State) (w : Worker)
    (store : RetainedControl.State) (created : List Nat) (distinct : DistinctStores stores)
    (step : RetainedControl.Step (stores w) created store) :
    DistinctStores (putWorker stores w store) := by
  have identity := c1_store_identity step
  cases w <;> simpa [DistinctStores, putWorker, identity.1, identity.2] using distinct

structure Network where
  prepared : Worker → Bool
  committed : Bool
  failed : Bool
  returned : Worker → Bool
  channels : Worker → Channel
  watches : Worker → Side → Watch
  stores : Worker → RetainedControl.State
  dispatched : Worker → Nat → Bool
  opNext : Nat
  operations : Nat → Option Operation
  backing : Bool

def Network.Valid (s : Network) : Prop :=
  (∀ w, (s.channels w).Safe) ∧
  (∀ w side, (s.watches w side).Valid) ∧
  (∀ id, s.opNext ≤ id → s.operations id = none) ∧
  (s.failed = true → ∀ w, (s.channels w).failed = true) ∧
  (s.committed = true → ∀ w, s.prepared w = true) ∧
  (∀ w, s.returned w = true → (s.stores w).closed = true) ∧
  (∀ w, RetainedControl.Unique (s.stores w) ∧ RetainedControl.ContextSafe (s.stores w) ∧
    RetainedControl.SlotIdsUnique (s.stores w) ∧ RetainedControl.GenerationBounded (s.stores w)) ∧
  (∀ w id, s.dispatched w id = true → ∃ e, e ∈ (s.channels w.peer).held ∧ e.id = id) ∧
  DistinctStores s.stores

def Network.ReadyToRelease (s : Network) : Prop :=
  s.failed = false ∧ s.committed = true ∧ (∀ w, s.returned w = true) ∧
  (∀ w, (s.channels w).sealed = true ∧ (s.channels w).observedEnd = true ∧
    (s.channels w).queue = [] ∧ (s.channels w).held = []) ∧
  (∀ id, s.operations id = none) ∧
  (∀ w side, (∀ g, (s.watches w side).active g = false ∧ (s.watches w side).pending g = false) ∧
    ∀ id, (s.watches w side).callbacks id = none) ∧
  (∀ w id, s.dispatched w id = false)

def Network.Safe (s : Network) : Prop := s.Valid ∧ (s.backing = false → s.ReadyToRelease)

def Network.initial (capacity : Nat) (stores : Worker → RetainedControl.State) : Network :=
  ⟨fun _ ↦ false, false, false, fun _ ↦ false, fun _ ↦ Channel.initial capacity,
    fun _ _ ↦ Watch.initial, stores, fun _ _ ↦ false, 0, fun _ ↦ none, true⟩

theorem network_initial_safe (capacity : Nat) (stores : Worker → RetainedControl.State)
    (positive : 0 < capacity)
    (storeSafe : ∀ w, RetainedControl.Unique (stores w) ∧ RetainedControl.ContextSafe (stores w) ∧
      RetainedControl.SlotIdsUnique (stores w) ∧ RetainedControl.GenerationBounded (stores w))
    (distinct : DistinctStores stores) :
    (Network.initial capacity stores).Safe := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, storeSafe, ?_, distinct⟩
    · intro w; exact channel_initial_safe capacity positive
    · simp [Network.initial, Watch.initial, Watch.Valid]
    · simp [Network.initial]
    · simp [Network.initial]
    · simp [Network.initial]
    · simp [Network.initial]
    · simp [Network.initial]
  · simp [Network.initial]

def setWatch (watches : Worker → Side → Watch) (lane : Worker) (side : Side) (watch : Watch) :
    Worker → Side → Watch := putWorker watches lane (putSide (watches lane) side watch)

def Network.advance (s : Network) (lane : Worker) (c : Channel) (op : Nat) : Network :=
  let channels := putWorker s.channels lane c
  { { { s with channels := channels } with
        watches := fun w side ↦ (s.watches w side).signal ((channels w).ready side) } with
    operations := put s.operations op none }

def Network.refresh (s : Network) : Network :=
  { s with watches := fun w side ↦ (s.watches w side).signal ((s.channels w).ready side) }

def Network.pollWake (s : Network) (lane : Worker) (side : Side) (generation : Nat) : Network :=
  let refreshed := fun w which ↦ (s.watches w which).signal ((s.channels w).ready which)
  { s with watches := setWatch refreshed lane side ((s.watches lane side).poll generation ((s.channels lane).ready side)) }

def Network.fail (s : Network) : Network :=
  { { { s with failed := true } with
        channels := fun lane ↦ { s.channels lane with failed := true } } with
    watches := fun lane side ↦ (s.watches lane side).signal true }

def Network.processingFinished (s : Network) (lane : Worker) (e : Entry)
    (pre post : List Entry) (store : RetainedControl.State) : Network :=
  { { { s with channels := putWorker s.channels lane (finishChannel (s.channels lane) e pre post) } with
      stores := putWorker s.stores lane.peer store } with
    dispatched := putWorker s.dispatched lane.peer (put (s.dispatched lane.peer) e.id false) }

def Network.dispatch (s : Network) (lane : Worker) (e : Entry)
    (capture : RetainedControl.Capture) (consumer : RetainedControl.Consumer) : Network :=
  { { s with stores := putWorker s.stores lane.peer ({ { s.stores lane.peer with active := some (capture, consumer) } with result := none }) } with
    dispatched := putWorker s.dispatched lane.peer (put (s.dispatched lane.peer) e.id true) }

def finishStore (store : RetainedControl.State) (capture : RetainedControl.Capture)
    (consumer : RetainedControl.Consumer) : RetainedControl.State :=
  { { { store with active := none } with completed := capture.owners ++ store.completed } with
    result := some (RetainedControl.respond consumer .finished) }

inductive NetworkStep : Network → Network → Prop where
  | prepare (s : Network) (worker : Worker) (live : s.backing = true)
      (uncommitted : s.committed = false) (healthy : s.failed = false)
      (unprepared : s.prepared worker = false) :
      NetworkStep s { s with prepared := putWorker s.prepared worker true }
  | abortPreparation (s : Network) (worker : Worker) (live : s.backing = true)
      (uncommitted : s.committed = false) (prepared : s.prepared worker = true) :
      NetworkStep s { s with prepared := putWorker s.prepared worker false }
  | commit (s : Network) (live : s.backing = true) (healthy : s.failed = false)
      (uncommitted : s.committed = false) (both : ∀ w, s.prepared w = true) :
      NetworkStep s { s with committed := true }
  | localStep (s : Network) (owner actor : Worker) (created : List Nat) (store : RetainedControl.State)
      (live : s.backing = true) (committed : s.committed = true) (healthy : s.failed = false)
      (same : actor = owner) (running : s.returned owner = false)
      (change : RetainedControl.Step (s.stores owner) created store)
      (noDispatchedFinish : ∀ capture consumer,
        (s.stores owner).active = some (capture, consumer) →
        s.dispatched owner capture.branch = true →
        ¬ (store.active = none ∧ store.result = some (RetainedControl.respond consumer .finished))) :
      NetworkStep s { s with stores := putWorker s.stores owner store }
  | dispatch (s : Network) (lane actor : Worker) (e : Entry)
      (capture : RetainedControl.Capture) (consumer : RetainedControl.Consumer)
      (live : s.backing = true) (committed : s.committed = true) (healthy : s.failed = false)
      (owner : actor = lane.peer) (running : s.returned actor = false)
      (held : e ∈ (s.channels lane).held) (notDispatched : s.dispatched actor e.id = false)
      (identity : capture.branch = e.id) (owned : e.id ∈ capture.owners)
      (noClause : (s.stores actor).clause = none) (driver : (s.stores actor).active = none)
      (admission : RetainedControl.Admit (s.stores actor) capture)
      (fresh : RetainedControl.RootFresh (s.stores actor) capture)
      (unique : RetainedControl.CaptureUnique capture)
      (interpretation : consumer.interpretation = (s.stores actor).interpretation)
      (kind : consumer.kind = .root) (openStore : (s.stores actor).closed = false)
      (storeHealthy : (s.stores actor).failed = false) :
      NetworkStep s (s.dispatch lane e capture consumer)
  | startOperation (s : Network) (lane actor : Worker) (side : Side)
      (live : s.backing = true) (committed : s.committed = true) (healthy : s.failed = false)
      (owner : actor = sideOwner lane side) (running : s.returned actor = false) :
      NetworkStep s { { s with operations := put s.operations s.opNext (some ⟨lane, side, actor⟩) } with
        opNext := s.opNext + 1 }
  | channel (s : Network) (id : Nat) (op : Operation) (c : Channel)
      (live : s.backing = true) (committed : s.committed = true)
      (current : s.operations id = some op) (owner : op.owner = sideOwner op.lane op.side)
      (running : s.returned op.owner = false) (change : ChannelStep op.side (s.channels op.lane) c) :
      NetworkStep s (s.advance op.lane c id)
  | finishProcessing (s : Network) (lane : Worker) (e : Entry) (pre post : List Entry)
      (capture : RetainedControl.Capture) (consumer : RetainedControl.Consumer)
      (live : s.backing = true) (committed : s.committed = true)
      (running : s.returned lane.peer = false) (found : (s.channels lane).held = pre ++ e :: post)
      (identity : capture.branch = e.id) (owned : e.id ∈ capture.owners)
      (dispatched : s.dispatched lane.peer e.id = true)
      (active : (s.stores lane.peer).active = some (capture, consumer))
      (ready : RetainedControl.ReadyToFinish capture) (healthy : (s.stores lane.peer).failed = false) :
      NetworkStep s (s.processingFinished lane e pre post
        (finishStore (s.stores lane.peer) capture consumer))
  | refuseWatch (s : Network) (lane actor : Worker) (side : Side)
      (live : s.backing = true) (committed : s.committed = true)
      (owner : actor = sideOwner lane side) (running : s.returned actor = false) :
      NetworkStep s s
  | register (s : Network) (lane actor : Worker) (side : Side)
      (live : s.backing = true) (committed : s.committed = true)
      (owner : actor = sideOwner lane side) (running : s.returned actor = false) :
      NetworkStep s { s with watches := setWatch s.watches lane side ((s.watches lane side).register ((s.channels lane).ready side)) }
  | poll (s : Network) (lane actor : Worker) (side : Side) (generation : Nat)
      (live : s.backing = true) (committed : s.committed = true)
      (owner : actor = sideOwner lane side) (running : s.returned actor = false)
      (current : ((s.watches lane side).signal ((s.channels lane).ready side)).pending generation = true) :
      NetworkStep s (s.pollWake lane side generation)
  | pollEmpty (s : Network) (actor : Worker) (live : s.backing = true)
      (committed : s.committed = true) (running : s.returned actor = false)
      (noPending : ∀ lane side, sideOwner lane side = actor → ∀ generation,
        ((s.watches lane side).signal ((s.channels lane).ready side)).pending generation = false) :
      NetworkStep s s.refresh
  | cancel (s : Network) (lane : Worker) (side : Side) (generation : Nat)
      (live : s.backing = true) (current : (s.watches lane side).active generation = true) :
      NetworkStep s { s with watches := setWatch s.watches lane side ((s.watches lane side).cancel generation) }
  | finishCallback (s : Network) (lane : Worker) (side : Side) (id generation : Nat)
      (live : s.backing = true) (current : (s.watches lane side).callbacks id = some generation) :
      NetworkStep s { s with watches := setWatch s.watches lane side ((s.watches lane side).completeCallback id) }
  | failure (s : Network) (live : s.backing = true) : NetworkStep s s.fail
  | returnWorker (s : Network) (worker : Worker)
      (live : s.backing = true) (committed : s.committed = true) (healthy : s.failed = false)
      (running : s.returned worker = false)
      (sealed : (s.channels worker).sealed = true)
      (endSeen : (s.channels worker.peer).observedEnd = true)
      (finished : (s.channels worker.peer).held = [])
      (empty : RetainedControl.NoWork (s.stores worker))
      (closeReady : (s.stores worker).closePhase = .idle ∨ (s.stores worker).closePhase = .finished)
      (openStore : (s.stores worker).closed = false) (storeHealthy : (s.stores worker).failed = false) :
      NetworkStep s { { s with returned := putWorker s.returned worker true } with
        stores := putWorker s.stores worker { s.stores worker with closed := true } }
  | release (s : Network) (live : s.backing = true) (ready : s.ReadyToRelease) :
      NetworkStep s { s with backing := false }

theorem channel_step_preserves_failure {side : Side} {a b : Channel}
    (step : ChannelStep side a b) (failed : a.failed = true) : b.failed = true := by
  cases step <;> simp_all

theorem set_watch_valid (allValid : ∀ w side, (ws w side).Valid) (watchValid : watch.Valid) :
    ∀ w side, (setWatch ws lane which watch w side).Valid := by
  intro w side
  by_cases hw : w = lane
  · subst w
    by_cases hs : side = which
    · subst side; simpa [setWatch, putWorker, putSide] using watchValid
    · simpa [setWatch, putWorker, putSide, hs] using allValid lane side
  · simpa [setWatch, putWorker, hw] using allValid w side

theorem clear_operation_finite (s : Network) (finite : ∀ k, s.opNext ≤ k → s.operations k = none)
    (id : Nat) : ∀ k, s.opNext ≤ k → put s.operations id none k = none := by
  intro k bound
  simp only [put]
  split
  · rfl
  · exact finite k bound

theorem network_advance_valid (s : Network) (valid : s.Valid) (id : Nat) (op : Operation)
    (c : Channel) (change : ChannelStep op.side (s.channels op.lane) c) :
    (s.advance op.lane c id).Valid := by
  rcases valid with ⟨channels, watches, operations, failed, committed, returned, owners, links, distinct⟩
  refine ⟨?_, ?_, ?_, ?_, committed, returned, owners, ?_, distinct⟩
  · intro w
    by_cases h : w = op.lane
    · subst w; simpa [Network.advance, putWorker] using channel_step_safe (channels op.lane) change
    · simpa [Network.advance, putWorker, h] using channels w
  · intro w side
    exact watch_signal_valid (s.watches w side) ((putWorker s.channels op.lane c w).ready side) (watches w side)
  · exact clear_operation_finite s operations id
  · intro fail w
    by_cases h : w = op.lane
    · subst w
      simpa [Network.advance, putWorker] using channel_step_preserves_failure change (failed fail op.lane)
    · simpa [Network.advance, putWorker, h] using failed fail w
  · intro w key flag
    obtain ⟨item, member, identity⟩ := links w key flag
    refine ⟨item, ?_, identity⟩
    by_cases h : w.peer = op.lane
    · have old : item ∈ (s.channels op.lane).held := by simpa [h] using member
      simpa [Network.advance, putWorker, h] using channel_step_preserves_held change item old
    · simpa [Network.advance, putWorker, h] using member

theorem network_refresh_valid (s : Network) (valid : s.Valid) : s.refresh.Valid := by
  rcases valid with ⟨channels, watches, operations, failed, committed, returned, owners, links, distinct⟩
  refine ⟨channels, ?_, operations, failed, committed, returned, owners, links, distinct⟩
  intro w side
  exact watch_signal_valid _ _ (watches w side)

theorem network_failed_valid (s : Network) (valid : s.Valid) : s.fail.Valid := by
  rcases valid with ⟨channels, watches, operations, failed, committed, returned, owners, links, distinct⟩
  refine ⟨?_, ?_, operations, ?_, committed, returned, owners, links, distinct⟩
  · intro w; exact channels w
  · intro w side
    exact watch_signal_valid (s.watches w side) true (watches w side)
  · simp [Network.fail]

theorem network_processing_valid (s : Network) (valid : s.Valid) (lane : Worker)
    (e : Entry) (pre post : List Entry) (store : RetainedControl.State)
    (found : (s.channels lane).held = pre ++ e :: post)
    (running : s.returned lane.peer = false)
    (storeStep : RetainedControl.Step (s.stores lane.peer) [] store) :
    (s.processingFinished lane e pre post store).Valid := by
  rcases valid with ⟨channels, watches, operations, failed, committed, returned, owners, links, distinct⟩
  refine ⟨?_, watches, operations, ?_, committed, ?_, ?_, ?_, ?_⟩
  · intro w
    by_cases h : w = lane
    · subst w
      simpa [Network.processingFinished, putWorker] using finish_channel_safe (s.channels lane) e pre post (channels lane) found
    · simpa [Network.processingFinished, putWorker, h] using channels w
  · intro fail w
    by_cases h : w = lane
    · subst w
      simpa [Network.processingFinished, finishChannel, putWorker] using failed fail lane
    · simpa [Network.processingFinished, putWorker, h] using failed fail w
  · intro w done
    by_cases h : w = lane.peer
    · subst w
      simp [Network.processingFinished, running] at done
    · simpa [Network.processingFinished, putWorker, h] using returned w done
  · intro w
    by_cases h : w = lane.peer
    · subst w
      simpa [Network.processingFinished, putWorker] using And.intro
        (RetainedControl.step_preserves_unique storeStep (owners lane.peer).1)
        ⟨RetainedControl.step_preserves_context storeStep (owners lane.peer).2.1,
         RetainedControl.step_preserves_slot_ids storeStep (owners lane.peer).2.2.1,
         RetainedControl.step_preserves_generation_bound storeStep (owners lane.peer).2.2.2⟩
    · simpa [Network.processingFinished, putWorker, h] using owners w
  · intro w key flag
    have prior : s.dispatched w key = true := by
      by_cases hw : w = lane.peer
      · subst w
        by_cases hk : key = e.id
        · subst key; simp [Network.processingFinished, putWorker, put] at flag
        · simpa [Network.processingFinished, putWorker, put, hk] using flag
      · simpa [Network.processingFinished, putWorker, hw] using flag
    obtain ⟨item, member, identity⟩ := links w key prior
    refine ⟨item, ?_, identity⟩
    by_cases hw : w.peer = lane
    · have same : w = lane.peer := by
        have tmp := congrArg Worker.peer hw
        simpa [Worker.peer_peer] using tmp
      subst w
      have distinct : item.id ≠ e.id := by
        intro eq
        have eqkey : key = e.id := identity.symm.trans eq
        subst key
        simp [Network.processingFinished, putWorker, put] at flag
        exact flag.1 eq
      have old : item ∈ (s.channels lane).held := by simpa [Worker.peer_peer] using member
      simpa [Network.processingFinished, putWorker, Worker.peer_peer] using
        finish_preserves_other (s.channels lane) e item pre post found old distinct
    · simpa [Network.processingFinished, putWorker, hw] using member
  · simpa [Network.processingFinished] using
      update_distinct_stores s.stores lane.peer store [] distinct storeStep

theorem network_dispatch_valid (s : Network) (valid : s.Valid) (lane : Worker) (e : Entry)
    (capture : RetainedControl.Capture) (consumer : RetainedControl.Consumer)
    (running : s.returned lane.peer = false) (held : e ∈ (s.channels lane).held)
    (step : RetainedControl.Step (s.stores lane.peer) capture.owners
      { { s.stores lane.peer with active := some (capture, consumer) } with result := none }) :
    (s.dispatch lane e capture consumer).Valid := by
  rcases valid with ⟨channels, watches, operations, failed, committed, returned, owners, links, distinct⟩
  refine ⟨channels, watches, operations, failed, committed, ?_, ?_, ?_, ?_⟩
  · intro w done
    by_cases h : w = lane.peer
    · subst w; simp [Network.dispatch, running] at done
    · simpa [Network.dispatch, putWorker, h] using returned w done
  · intro w
    by_cases h : w = lane.peer
    · subst w
      simpa [Network.dispatch, putWorker] using And.intro
        (RetainedControl.step_preserves_unique step (owners lane.peer).1)
        ⟨RetainedControl.step_preserves_context step (owners lane.peer).2.1,
         RetainedControl.step_preserves_slot_ids step (owners lane.peer).2.2.1,
         RetainedControl.step_preserves_generation_bound step (owners lane.peer).2.2.2⟩
    · simpa [Network.dispatch, putWorker, h] using owners w
  · intro w key flag
    by_cases hw : w = lane.peer
    · subst w
      by_cases hk : key = e.id
      · subst key
        exact ⟨e, by simpa [Network.dispatch, Worker.peer_peer] using held, rfl⟩
      · have prior : s.dispatched lane.peer key = true := by
          simpa [Network.dispatch, putWorker, put, hk] using flag
        simpa [Network.dispatch, Worker.peer_peer] using links lane.peer key prior
    · have prior : s.dispatched w key = true := by
        simpa [Network.dispatch, putWorker, hw] using flag
      simpa [Network.dispatch] using links w key prior
  · simpa [Network.dispatch] using
      update_distinct_stores s.stores lane.peer _ capture.owners distinct step

theorem network_step_safe {a b : Network} (safe : a.Safe) (step : NetworkStep a b) : b.Safe := by
  rcases safe with ⟨valid, released⟩
  cases step with
  | prepare worker live uncommitted healthy unprepared =>
    rcases valid with ⟨channels, watches, operations, failed, committed, returned, owners, links, distinct⟩
    refine ⟨⟨channels, watches, operations, failed, ?_, returned, owners, links, distinct⟩, ?_⟩
    · simp [uncommitted]
    · simp [live]
  | abortPreparation worker live uncommitted prepared =>
    rcases valid with ⟨channels, watches, operations, failed, committed, returned, owners, links, distinct⟩
    refine ⟨⟨channels, watches, operations, failed, ?_, returned, owners, links, distinct⟩, ?_⟩
    · simp [uncommitted]
    · simp [live]
  | commit live healthy uncommitted both =>
    rcases valid with ⟨channels, watches, operations, failed, committed, returned, owners, links, distinct⟩
    refine ⟨⟨channels, watches, operations, failed, ?_, returned, owners, links, distinct⟩, ?_⟩
    · simpa using both
    · simp [live]
  | localStep owner actor created store live committed healthy same running change noDispatchedFinish =>
    rcases valid with ⟨channels, watches, operations, failed, prepared, returned, owners, links, distinct⟩
    refine ⟨⟨channels, watches, operations, failed, prepared, ?_, ?_, links, ?_⟩, by simp [live]⟩
    · intro w done
      by_cases h : w = owner
      · subst w; simp [running] at done
      · simpa [putWorker, h] using returned w done
    · intro w
      by_cases h : w = owner
      · subst w
        simpa [putWorker] using And.intro
          (RetainedControl.step_preserves_unique change (owners owner).1)
          ⟨RetainedControl.step_preserves_context change (owners owner).2.1,
           RetainedControl.step_preserves_slot_ids change (owners owner).2.2.1,
           RetainedControl.step_preserves_generation_bound change (owners owner).2.2.2⟩
      · simpa [putWorker, h] using owners w
    · exact update_distinct_stores a.stores owner store created distinct change
  | dispatch lane actor e capture consumer live committed healthy owner running held notDispatched identity owned noClause driver admission fresh unique interpretation kind openStore storeHealthy =>
    subst actor
    have step := RetainedControl.Step.launch (a.stores lane.peer) capture consumer noClause driver admission fresh unique interpretation kind openStore storeHealthy
    exact ⟨network_dispatch_valid a valid lane e capture consumer running held (by simpa using step),
      by simp [Network.dispatch, live]⟩
  | startOperation lane actor side live committed healthy owner running =>
    rcases valid with ⟨channels, watches, operations, failed, prepared, returned, owners, links, distinct⟩
    refine ⟨⟨channels, watches, ?_, failed, prepared, returned, owners, links, distinct⟩, ?_⟩
    · intro k bound
      change a.opNext + 1 ≤ k at bound
      simp only [put]
      have ne : k ≠ a.opNext := by omega
      simp [ne, operations k (by omega)]
    · simp [live]
  | channel id op c live committed current owner running change =>
    exact ⟨network_advance_valid a valid id op c change, by simp [Network.advance, live]⟩
  | finishProcessing lane e pre post capture consumer live committed running found identity owned dispatched active ready healthy =>
    exact ⟨network_processing_valid a valid lane e pre post _ found running (by
      simpa [finishStore] using RetainedControl.Step.finish (a.stores lane.peer) capture consumer active ready healthy), by simp [Network.processingFinished, live]⟩
  | refuseWatch lane actor side live committed owner running => exact ⟨valid, released⟩
  | register lane actor side live committed owner running =>
    rcases valid with ⟨channels, watches, operations, failed, prepared, returned, owners, links, distinct⟩
    refine ⟨⟨channels, ?_, operations, failed, prepared, returned, owners, links, distinct⟩, ?_⟩
    · exact set_watch_valid watches (watch_register_valid _ _ (watches lane side))
    · simp [live]
  | poll lane actor side generation live committed owner running current =>
    rcases valid with ⟨channels, watches, operations, failed, prepared, returned, owners, links, distinct⟩
    refine ⟨⟨channels, ?_, operations, failed, prepared, returned, owners, links, distinct⟩, ?_⟩
    · simp only [Network.pollWake]
      apply set_watch_valid
      · intro w which
        exact watch_signal_valid _ _ (watches w which)
      · exact watch_poll_valid _ _ _ (watches lane side)
    · simp [Network.pollWake, live]
  | pollEmpty actor live committed running noPending =>
    exact ⟨network_refresh_valid a valid, by simp [Network.refresh, live]⟩
  | cancel lane side generation live current =>
    rcases valid with ⟨channels, watches, operations, failed, prepared, returned, owners, links, distinct⟩
    refine ⟨⟨channels, ?_, operations, failed, prepared, returned, owners, links, distinct⟩, ?_⟩
    · exact set_watch_valid watches (watch_cancel_valid _ generation (watches lane side))
    · simp [live]
  | finishCallback lane side id generation live current =>
    rcases valid with ⟨channels, watches, operations, failed, prepared, returned, owners, links, distinct⟩
    refine ⟨⟨channels, ?_, operations, failed, prepared, returned, owners, links, distinct⟩, ?_⟩
    · exact set_watch_valid watches (watch_complete_valid _ _ (watches lane side))
    · simp [live]
  | failure live => exact ⟨network_failed_valid a valid, by simp [Network.fail, live]⟩
  | returnWorker worker live committed healthy running sealed endSeen finished empty closeReady openStore storeHealthy =>
    rcases valid with ⟨channels, watches, operations, failed, prepared, returned, owners, links, distinct⟩
    refine ⟨⟨channels, watches, operations, failed, prepared, ?_, ?_, links, ?_⟩, by simp [live]⟩
    · intro w done
      by_cases h : w = worker
      · subst w; simp [putWorker]
      · simpa [putWorker, h] using returned w (by simpa [putWorker, h] using done)
    · intro w
      by_cases h : w = worker
      · subst w
        have storeStep := RetainedControl.Step.release (a.stores worker) empty closeReady openStore storeHealthy
        simpa [putWorker] using And.intro
          (RetainedControl.step_preserves_unique storeStep (owners worker).1)
          ⟨RetainedControl.step_preserves_context storeStep (owners worker).2.1,
           RetainedControl.step_preserves_slot_ids storeStep (owners worker).2.2.1,
           RetainedControl.step_preserves_generation_bound storeStep (owners worker).2.2.2⟩
      · simpa [putWorker, h] using owners w
    · exact update_distinct_stores a.stores worker _ [] distinct
        (RetainedControl.Step.release (a.stores worker) empty closeReady openStore storeHealthy)
  | release live ready => exact ⟨valid, by simpa [Network.ReadyToRelease] using ready⟩

inductive NetworkTrace : Network → Network → Prop where
  | refl (s) : NetworkTrace s s
  | next {a b c} : NetworkTrace a b → NetworkStep b c → NetworkTrace a c

theorem network_trace_safe {a b : Network} (safe : a.Safe) (trace : NetworkTrace a b) :
    b.Safe := by
  induction trace with
  | refl => exact safe
  | next _ step ih => exact network_step_safe ih step

theorem actual_c1_finish (store : RetainedControl.State) (capture : RetainedControl.Capture)
    (consumer : RetainedControl.Consumer) (active : store.active = some (capture, consumer))
    (ready : RetainedControl.ReadyToFinish capture) (healthy : store.failed = false) :
    RetainedControl.Step store [] (finishStore store capture consumer) := by
  simpa [finishStore] using RetainedControl.Step.finish store capture consumer active ready healthy

theorem actual_c1_release (store : RetainedControl.State) (empty : RetainedControl.NoWork store)
    (closeReady : store.closePhase = .idle ∨ store.closePhase = .finished)
    (openStore : store.closed = false) (healthy : store.failed = false) :
    RetainedControl.Step store [] { store with closed := true } :=
  RetainedControl.Step.release store empty closeReady openStore healthy

theorem observed_end_covers_accepted (c : Channel) (safe : c.Safe)
    (observed : c.observedEnd = true) : c.sealed = true ∧ c.accepted = c.received := by
  have status := safe.2.2.2.2.2 observed
  exact ⟨status.1, by simpa [status.2] using safe.2.1⟩

theorem failed_channel_no_new_acceptance {side : Side} {a b : Channel}
    (failed : a.failed = true) (step : ChannelStep side a b) : b.accepted = a.accepted := by
  cases step <;> simp_all

theorem terminal_channel_change_no_send (s : Network) (valid : s.Valid) (failed : s.failed = true)
    (op : Operation) (c : Channel) (step : ChannelStep op.side (s.channels op.lane) c) :
    c.accepted = (s.channels op.lane).accepted :=
  failed_channel_no_new_acceptance (valid.2.2.2.1 failed op.lane) step

theorem poll_signal_preserves_other_ready (w : Watch) (selected other : Nat) (ready : Bool)
    (different : other ≠ selected) (alreadyPending : w.pending other = true) :
    (w.poll selected ready).pending other = true :=
  watch_poll_preserves_other_pending w selected other ready different alreadyPending

theorem channel_update_signals_all_ready (s : Network) (lane : Worker) (c : Channel) (op : Nat)
    (worker : Worker) (side : Side) (generation : Nat)
    (active : (s.watches worker side).active generation = true)
    (ready : (putWorker s.channels lane c worker).ready side = true) :
    ((s.advance lane c op).watches worker side).pending generation = true := by
  simpa [Network.advance, ready] using signal_ready_pending (s.watches worker side) generation active

theorem terminal_watch_recheck (s : Network) (valid : s.Valid) (failed : s.failed = true)
    (lane : Worker) (side : Side) :
    ((s.watches lane side).register ((s.channels lane).ready side)).pending
      (s.watches lane side).next = true := by
  have h := valid.2.2.2.1 failed lane
  cases side <;> simpa [Channel.ready, h] using (late_terminal_registration (s.watches lane _)).2

theorem failure_signals_every_registration (s : Network) (lane : Worker) (side : Side) (g : Nat)
    (active : (s.watches lane side).active g = true) :
    (s.fail.watches lane side).pending g = true := by
  exact signal_ready_pending (s.watches lane side) g active

theorem terminal_active_not_empty (s : Network) (valid : s.Valid) (failed : s.failed = true)
    (actor lane : Worker) (side : Side) (generation : Nat)
    (owner : sideOwner lane side = actor) (active : (s.watches lane side).active generation = true) :
    ¬ (∀ w which, sideOwner w which = actor → ∀ g,
      ((s.watches w which).signal ((s.channels w).ready which)).pending g = false) := by
  intro empty
  have h := valid.2.2.2.1 failed lane
  have pending := empty lane side owner generation
  cases side <;> simp [Channel.ready, h, Watch.signal, active] at pending

theorem commit_requires_both_prepared (s : Network) (valid : s.Valid) (committed : s.committed = true) :
    ∀ worker, s.prepared worker = true := valid.2.2.2.2.1 committed

theorem operation_once (s : Network) (id : Nat) : put s.operations id none id = none := by
  simp [put]

theorem release_requires_end_and_no_work (s : Network) (safe : s.Safe)
    (released : s.backing = false) (lane : Worker) :
    (s.channels lane).sealed = true ∧ (s.channels lane).observedEnd = true ∧
      (s.channels lane).queue = [] ∧ (s.channels lane).held = [] :=
  (safe.2 released).2.2.2.1 lane

theorem release_no_live_operation (s : Network) (safe : s.Safe) (released : s.backing = false)
    (id : Nat) : s.operations id = none := (safe.2 released).2.2.2.2.1 id

theorem release_no_live_watch (s : Network) (safe : s.Safe) (released : s.backing = false)
    (lane : Worker) (side : Side) :
    (∀ g, (s.watches lane side).active g = false ∧ (s.watches lane side).pending g = false) ∧
      ∀ id, (s.watches lane side).callbacks id = none :=
  (safe.2 released).2.2.2.2.2.1 lane side

theorem returned_worker_has_closed_store (s : Network) (safe : s.Safe) (worker : Worker)
    (returned : s.returned worker = true) : (s.stores worker).closed = true :=
  safe.1.2.2.2.2.2.1 worker returned

theorem old_generation_not_reused (w : Watch) (g : Nat) (old : g < w.next) (ready : Bool) :
    (w.register ready).active g = w.active g := by
  simp [Watch.register, put, Nat.ne_of_lt old]

theorem cancelled_key_not_revived (w : Watch) (g : Nat) (old : g < w.next) (ready : Bool) :
    ((w.cancel g).register ready).active g = false := by
  simpa [Watch.cancel, put] using old_generation_not_reused (w.cancel g) g old ready

theorem signal_preserves_old_callback (w : Watch) (id : Nat) (_old : id < w.callbackNext)
    (ready : Bool) : (w.signal ready).callbacks id = w.callbacks id := by
  simp [Watch.signal]

theorem network_failed_stays_failed {a b : Network} (failed : a.failed = true)
    (step : NetworkStep a b) : b.failed = true := by
  cases step <;> simp_all [Network.advance, Network.processingFinished, Network.fail, Network.pollWake, Network.refresh]

theorem failed_step_preserves_acceptance {a b : Network} (valid : a.Valid)
    (failed : a.failed = true) (step : NetworkStep a b) :
    ∀ lane, (b.channels lane).accepted = (a.channels lane).accepted := by
  cases step with
  | channel id op c live committed current owner running change =>
    intro lane
    by_cases h : lane = op.lane
    · subst lane
      simpa [Network.advance, putWorker] using terminal_channel_change_no_send a valid failed op c change
    · simp [Network.advance, putWorker, h]
  | finishProcessing lane e pre post capture consumer live committed running found identity owned dispatched active ready healthy =>
    intro other
    by_cases h : other = lane
    · subst other; simp [Network.processingFinished, finishChannel, putWorker]
    · simp [Network.processingFinished, putWorker, h]
  | _ => simp_all [Network.fail, Network.pollWake, Network.refresh]

theorem terminal_failure_remains {a b : Network} (failed : a.failed = true)
    (trace : NetworkTrace a b) : b.failed = true := by
  induction trace with
  | refl => exact failed
  | next _ step ih => exact network_failed_stays_failed ih step

theorem terminal_trace_no_new_acceptance {a b : Network} (safe : a.Safe) (failed : a.failed = true)
    (trace : NetworkTrace a b) : ∀ lane, (b.channels lane).accepted = (a.channels lane).accepted := by
  induction trace with
  | refl => simp
  | next trace step ih =>
    intro lane
    rw [failed_step_preserves_acceptance (network_trace_safe safe trace).1
      (terminal_failure_remains failed trace) step lane]
    exact ih lane

theorem released_network_cannot_step (s t : Network) (released : s.backing = false)
    (step : NetworkStep s t) : False := by
  have live : s.backing = true := by cases step <;> assumption
  simp [released] at live

theorem completed_id_not_live (c : Channel) (safe : c.Safe) (done : Entry) (live : Entry)
    (doneMember : done ∈ c.done) (liveMember : live ∈ c.held) : done.id ≠ live.id := by
  rcases safe with ⟨_, fifo, _, unique, cover, _⟩
  have receivedUnique : (c.received.map Entry.id).Nodup := by
    rw [fifo, List.map_append] at unique
    exact (List.nodup_append.mp unique).1
  have both : ((c.done ++ c.held).map Entry.id).Nodup := (cover.map Entry.id).nodup receivedUnique
  rw [List.map_append] at both
  have disjoint := (List.nodup_append.mp both).2.2
  intro same
  exact disjoint done.id (List.mem_map_of_mem doneMember) live.id
    (List.mem_map_of_mem liveMember) same

theorem callback_live_was_issued (w : Watch) (valid : w.Valid) (id gen : Nat)
    (live : w.callbacks id = some gen) : id < w.callbackNext := by
  by_cases h : id < w.callbackNext
  · exact h
  · have vacant := valid.2.2 id (by omega)
    simp [vacant] at live

theorem completed_callback_not_reissued_by_signal (w : Watch) (valid : w.Valid) (id gen : Nat)
    (live : w.callbacks id = some gen) (ready : Bool) :
    ((w.completeCallback id).signal ready).callbacks id = none := by
  have old : id < (w.completeCallback id).callbackNext := callback_live_was_issued w valid id gen live
  rw [signal_preserves_old_callback _ id old]
  exact watch_completion_once w id

theorem completed_callback_not_reissued_by_poll (w : Watch) (valid : w.Valid) (id gen : Nat)
    (live : w.callbacks id = some gen) (registration : Nat) (ready : Bool) :
    ((w.completeCallback id).poll registration ready).callbacks id = none := by
  have old := callback_live_was_issued w valid id gen live
  simp [Watch.poll, Watch.completeCallback, put, Nat.ne_of_lt old]

theorem operation_live_was_issued (s : Network) (valid : s.Valid) (id : Nat) (op : Operation)
    (live : s.operations id = some op) : id < s.opNext := by
  by_cases h : id < s.opNext
  · exact h
  · have vacant := valid.2.2.1 id (by omega)
    simp [vacant] at live

end Ash.WorkerChannel

#print axioms Ash.WorkerChannel.channel_initial_safe
#print axioms Ash.WorkerChannel.channel_step_safe
#print axioms Ash.WorkerChannel.finish_channel_safe
#print axioms Ash.WorkerChannel.finished_entry_cannot_repeat
#print axioms Ash.WorkerChannel.channel_step_preserves_held
#print axioms Ash.WorkerChannel.finish_preserves_other
#print axioms Ash.WorkerChannel.watch_signal_valid
#print axioms Ash.WorkerChannel.watch_register_valid
#print axioms Ash.WorkerChannel.watch_cancel_valid
#print axioms Ash.WorkerChannel.watch_poll_valid
#print axioms Ash.WorkerChannel.watch_complete_valid
#print axioms Ash.WorkerChannel.watch_signal_fresh
#print axioms Ash.WorkerChannel.watch_completion_once
#print axioms Ash.WorkerChannel.watch_two_live
#print axioms Ash.WorkerChannel.watch_registration_fresh
#print axioms Ash.WorkerChannel.watch_two_ready
#print axioms Ash.WorkerChannel.watch_signal_coalesces
#print axioms Ash.WorkerChannel.watch_cancel_preserves_other
#print axioms Ash.WorkerChannel.watch_poll_preserves_other_pending
#print axioms Ash.WorkerChannel.watch_cancel_preserves_callbacks
#print axioms Ash.WorkerChannel.watch_poll_preserves_old_callbacks
#print axioms Ash.WorkerChannel.two_watches_poll_keeps_other
#print axioms Ash.WorkerChannel.two_watches_cancel_keeps_other
#print axioms Ash.WorkerChannel.watch_poll_transfers_one
#print axioms Ash.WorkerChannel.late_terminal_registration
#print axioms Ash.WorkerChannel.signal_ready_pending
#print axioms Ash.WorkerChannel.terminal_signal_all
#print axioms Ash.WorkerChannel.cancelled_generation_cannot_be_current
#print axioms Ash.WorkerChannel.Worker.peer_peer
#print axioms Ash.WorkerChannel.c1_store_identity
#print axioms Ash.WorkerChannel.update_distinct_stores
#print axioms Ash.WorkerChannel.network_initial_safe
#print axioms Ash.WorkerChannel.channel_step_preserves_failure
#print axioms Ash.WorkerChannel.set_watch_valid
#print axioms Ash.WorkerChannel.clear_operation_finite
#print axioms Ash.WorkerChannel.network_advance_valid
#print axioms Ash.WorkerChannel.network_refresh_valid
#print axioms Ash.WorkerChannel.network_failed_valid
#print axioms Ash.WorkerChannel.network_processing_valid
#print axioms Ash.WorkerChannel.network_dispatch_valid
#print axioms Ash.WorkerChannel.network_step_safe
#print axioms Ash.WorkerChannel.network_trace_safe
#print axioms Ash.WorkerChannel.actual_c1_finish
#print axioms Ash.WorkerChannel.actual_c1_release
#print axioms Ash.WorkerChannel.observed_end_covers_accepted
#print axioms Ash.WorkerChannel.failed_channel_no_new_acceptance
#print axioms Ash.WorkerChannel.terminal_channel_change_no_send
#print axioms Ash.WorkerChannel.poll_signal_preserves_other_ready
#print axioms Ash.WorkerChannel.channel_update_signals_all_ready
#print axioms Ash.WorkerChannel.terminal_watch_recheck
#print axioms Ash.WorkerChannel.failure_signals_every_registration
#print axioms Ash.WorkerChannel.terminal_active_not_empty
#print axioms Ash.WorkerChannel.commit_requires_both_prepared
#print axioms Ash.WorkerChannel.operation_once
#print axioms Ash.WorkerChannel.release_requires_end_and_no_work
#print axioms Ash.WorkerChannel.release_no_live_operation
#print axioms Ash.WorkerChannel.release_no_live_watch
#print axioms Ash.WorkerChannel.returned_worker_has_closed_store
#print axioms Ash.WorkerChannel.old_generation_not_reused
#print axioms Ash.WorkerChannel.cancelled_key_not_revived
#print axioms Ash.WorkerChannel.signal_preserves_old_callback
#print axioms Ash.WorkerChannel.network_failed_stays_failed
#print axioms Ash.WorkerChannel.failed_step_preserves_acceptance
#print axioms Ash.WorkerChannel.terminal_failure_remains
#print axioms Ash.WorkerChannel.terminal_trace_no_new_acceptance
#print axioms Ash.WorkerChannel.released_network_cannot_step
#print axioms Ash.WorkerChannel.completed_id_not_live
#print axioms Ash.WorkerChannel.callback_live_was_issued
#print axioms Ash.WorkerChannel.completed_callback_not_reissued_by_signal
#print axioms Ash.WorkerChannel.completed_callback_not_reissued_by_poll
#print axioms Ash.WorkerChannel.operation_live_was_issued
