import NetworkLedgerTokens

namespace Ash.NetworkLedger.Coupling

open Ash.NetworkLedger
open Ash.NetworkLedger.Reachability

/-- Replace exactly one actual ledger in the distinguished-root system. -/
inductive SystemReplace : System → System → Tracked → Tracked → Prop where
  | root (s : System) (next : Tracked) : SystemReplace s { s with root := next } s.root next
  | worker (s : System) (before after : List Tracked) (old next : Tracked)
      (workers : s.workers = before ++ old :: after) :
      SystemReplace s { s with workers := before ++ next :: after } old next

theorem replace_is_system_step {s t : System} {old next : Tracked}
    (replacement : SystemReplace s t old next) (localStep : LocalStep old next) : SystemStep s t := by
  cases replacement with
  | root => exact .root _ _ localStep
  | worker before after old next workers => exact .worker _ before after old next workers localStep

structure ProtocolState where
  system : System
  work : List WorkMessage
  acks : List AckMessage
  deriving Repr

def initialProtocol (owner : Nat) (others : List Nat) : ProtocolState :=
  ⟨initialSystem owner others, [], []⟩

/-- Each protocol step performs the actual modeled ledger and FIFO functions. -/
inductive ProtocolStep (completed : Id → Prop) : ProtocolState → ProtocolState → Prop where
  | register (s : ProtocolState) (next : System) (worker : Tracked) (parent : Id)
      (destination : Nat) (payload : List UInt8)
      (replace : SystemReplace s.system next worker
        (worker.run (.register parent destination payload))) :
      ProtocolStep completed s { s with system := next }
  | close (s : ProtocolState) (next : System) (worker : Tracked) (id : Id)
      (replace : SystemReplace s.system next worker (worker.run (.close id))) :
      ProtocolStep completed s { s with system := next }
  | retire (s : ProtocolState) (next : System) (worker : Tracked) (id : Id)
      (done : completed id) (replace : SystemReplace s.system next worker (worker.run (.retire id))) :
      ProtocolStep completed s { s with system := next }
  | publishWork (s : ProtocolState) (next : System) (worker : Tracked)
      (replace : SystemReplace s.system next worker (publishWork ⟨worker, s.work⟩).current) :
      ProtocolStep completed s { s with system := next, work := (publishWork ⟨worker, s.work⟩).flight }
  | deliverWork (s : ProtocolState) (next : System) (worker : Tracked)
      (replace : SystemReplace s.system next worker (deliverWork ⟨worker, s.work⟩).receiver) :
      ProtocolStep completed s { s with system := next, work := (deliverWork ⟨worker, s.work⟩).flight }
  | publishAck (s : ProtocolState) (next : System) (worker : Tracked)
      (replace : SystemReplace s.system next worker (publishAck ⟨worker, s.acks⟩).current) :
      ProtocolStep completed s { s with system := next, acks := (publishAck ⟨worker, s.acks⟩).flight }
  | deliverAck (s : ProtocolState) (next : System) (worker : Tracked)
      (replace : SystemReplace s.system next worker (deliverAck ⟨worker, s.acks⟩).receiver) :
      ProtocolStep completed s { s with system := next, acks := (deliverAck ⟨worker, s.acks⟩).flight }

theorem protocol_step_projects {completed : Id → Prop} {s t : ProtocolState}
    (step : ProtocolStep completed s t) : SystemStep s.system t.system := by
  cases step with
  | register next worker parent destination payload replace =>
    exact replace_is_system_step replace (LocalStep.action worker (.register parent destination payload))
  | close next worker id replace => exact replace_is_system_step replace (LocalStep.action worker (.close id))
  | retire next worker id done replace => exact replace_is_system_step replace (LocalStep.action worker (.retire id))
  | publishWork next worker replace => exact replace_is_system_step replace (publish_work_local_step worker _)
  | deliverWork next worker replace => exact replace_is_system_step replace (deliver_work_local_step worker _)
  | publishAck next worker replace => exact replace_is_system_step replace (publish_ack_local_step worker _)
  | deliverAck next worker replace => exact replace_is_system_step replace (deliver_ack_local_step worker _)

inductive ProtocolTrace (completed : Id → Prop) : ProtocolState → ProtocolState → Prop where
  | refl (s : ProtocolState) : ProtocolTrace completed s s
  | next {s t u : ProtocolState} : ProtocolTrace completed s t → ProtocolStep completed t u →
      ProtocolTrace completed s u

theorem protocol_trace_projects {completed : Id → Prop} {s t : ProtocolState}
    (trace : ProtocolTrace completed s t) : SystemTrace s.system t.system := by
  induction trace with
  | refl => exact .refl _
  | next history step ih => exact .next ih (protocol_step_projects step)

theorem initialized_protocol_graph_unique (owner : Nat) (others : List Nat)
    (distinct : (owner :: others).Nodup) (completed : Id → Prop) {s : ProtocolState}
    (trace : ProtocolTrace completed (initialProtocol owner others) s) :
    Unique Edge.child (trackedGraph (s.system.root :: s.system.workers)) := by
  exact initialized_trace_graph_unique owner others distinct (protocol_trace_projects trace)

theorem initialized_protocol_quiet_no_root_edge (owner : Nat) (others : List Nat)
    (completed : Id → Prop) {s : ProtocolState}
    (trace : ProtocolTrace completed (initialProtocol owner others) s)
    (quiet : probeRoot s.system.root.ledger = true) :
    ∀ e ∈ trackedGraph (s.system.root :: s.system.workers), e.parent ≠ .root := by
  have result := initialized_trace_quiet_no_root_edge owner others s.system (protocol_trace_projects trace) quiet
  simpa [tracked_graph_is_ledger_graph] using result

theorem retire_tokens_perm (l : Ledger) (id : Id) : (ledgerTokens (retire l id)).Perm (ledgerTokens l) := by
  cases found : lookup Record.id id l.records with
  | none => simp [retire, found]
  | some r =>
    cases parent : r.parent with
    | none => simp [retire, found, parent]
    | some address =>
      by_cases ready : r.phase = .closed ∧ r.children = [] ∧ id ≠ .root
      · exact retirement_moves_record_token l id r address found parent ready.1 ready.2.1 ready.2.2
      · simp [retire, found, parent, ready]

theorem replace_lists {s t : System} {old next : Tracked}
    (replacement : SystemReplace s t old next) :
    ∃ before after, s.root :: s.workers = before ++ old :: after ∧
      t.root :: t.workers = before ++ next :: after := by
  cases replacement with
  | root => exact ⟨[], s.workers, by simp, by simp⟩
  | worker before after old next workers =>
    exact ⟨s.root :: before, after, by simp [workers], by simp⟩

def ProtocolState.tokens (s : ProtocolState) : List Id :=
  protocolTokens ((s.system.root :: s.system.workers).map Tracked.ledger) s.work s.acks

theorem replacement_tokens_perm {s t : System} {old next : Tracked}
    (replacement : SystemReplace s t old next) (work : List WorkMessage) (acks : List AckMessage)
    (localPerm : (ledgerTokens next.ledger).Perm (ledgerTokens old.ledger)) :
    (protocolTokens ((t.root :: t.workers).map Tracked.ledger) work acks).Perm
      (protocolTokens ((s.root :: s.workers).map Tracked.ledger) work acks) := by
  obtain ⟨before, after, oldSplit, newSplit⟩ := replace_lists replacement
  rw [oldSplit, newSplit]
  let pre := before.flatMap (fun w => ledgerTokens w.ledger)
  let post := after.flatMap (fun w => ledgerTokens w.ledger)
  have lifted := ((localPerm.append_right post).append_left pre).append_right
    (work.map WorkMessage.id ++ acks.map AckMessage.child)
  simpa [protocolTokens, List.map_append, List.flatMap_append, List.flatMap_map,
    Function.comp_def, pre, post, List.append_assoc] using lifted

theorem close_step_tokens {s t : ProtocolState} (worker : Tracked) (id : Id)
    (replace : SystemReplace s.system t.system worker (worker.run (.close id)))
    (work : t.work = s.work) (acks : t.acks = s.acks) : t.tokens.Perm s.tokens := by
  have localPerm : (ledgerTokens (worker.run (.close id)).ledger).Perm (ledgerTokens worker.ledger) := by
    simp only [Tracked.run, close_tokens]
    exact List.Perm.refl _
  simpa [ProtocolState.tokens, work, acks] using replacement_tokens_perm replace s.work s.acks localPerm

theorem retire_step_tokens {s t : ProtocolState} (worker : Tracked) (id : Id)
    (replace : SystemReplace s.system t.system worker (worker.run (.retire id)))
    (work : t.work = s.work) (acks : t.acks = s.acks) : t.tokens.Perm s.tokens := by
  simpa [ProtocolState.tokens, work, acks, Tracked.run] using
    replacement_tokens_perm replace s.work s.acks (retire_tokens_perm worker.ledger id)

theorem replacement_work_tokens_perm {s t : System} {old next : Tracked}
    (replacement : SystemReplace s t old next) (oldWork newWork : List WorkMessage) (acks : List AckMessage)
    (localPerm : (ledgerTokens next.ledger ++ newWork.map WorkMessage.id).Perm
      (ledgerTokens old.ledger ++ oldWork.map WorkMessage.id)) :
    (protocolTokens ((t.root :: t.workers).map Tracked.ledger) newWork acks).Perm
      (protocolTokens ((s.root :: s.workers).map Tracked.ledger) oldWork acks) := by
  obtain ⟨before, after, oldSplit, newSplit⟩ := replace_lists replacement
  rw [oldSplit, newSplit]
  let pre := before.flatMap (fun w => ledgerTokens w.ledger)
  let post := after.flatMap (fun w => ledgerTokens w.ledger)
  let tail := acks.map AckMessage.child
  have newMove := (((show (post ++ newWork.map WorkMessage.id).Perm (newWork.map WorkMessage.id ++ post) from List.perm_append_comm).append_left
    (ledgerTokens next.ledger)).append_left pre).append_right tail
  have localLift := ((localPerm.append_right post).append_left pre).append_right tail
  have oldMove := (((show (oldWork.map WorkMessage.id ++ post).Perm (post ++ oldWork.map WorkMessage.id) from List.perm_append_comm).append_left
    (ledgerTokens old.ledger)).append_left pre).append_right tail
  have combined := newMove.trans (by simpa [List.append_assoc] using localLift)
  have combined := combined.trans (by simpa [List.append_assoc] using oldMove)
  simpa [protocolTokens, List.map_append, List.flatMap_append, List.flatMap_map,
    Function.comp_def, pre, post, tail, List.append_assoc] using combined

theorem publish_work_step_tokens {s t : ProtocolState} (worker : Tracked)
    (replace : SystemReplace s.system t.system worker (publishWork ⟨worker, s.work⟩).current)
    (work : t.work = (publishWork ⟨worker, s.work⟩).flight) (acks : t.acks = s.acks) :
    t.tokens.Perm s.tokens := by
  have localPerm := publish_work_moves_token ⟨worker, s.work⟩
  simp only [ProtocolState.tokens, acks]
  apply replacement_work_tokens_perm replace s.work t.work s.acks
  simpa [publicationTokens, work] using localPerm

theorem deliver_work_step_tokens {s t : ProtocolState} (worker : Tracked)
    (replace : SystemReplace s.system t.system worker (deliverWork ⟨worker, s.work⟩).receiver)
    (work : t.work = (deliverWork ⟨worker, s.work⟩).flight) (acks : t.acks = s.acks) :
    t.tokens.Perm s.tokens := by
  have localEq := deliver_work_moves_token ⟨worker, s.work⟩
  simp only [ProtocolState.tokens, acks]
  apply replacement_work_tokens_perm replace s.work t.work s.acks
  apply List.Perm.of_eq
  simpa [deliveryTokens, work] using localEq

theorem replacement_ack_tokens_perm {s t : System} {old next : Tracked}
    (replacement : SystemReplace s t old next) (work : List WorkMessage) (oldAcks newAcks : List AckMessage)
    (localPerm : (ledgerTokens next.ledger ++ newAcks.map AckMessage.child).Perm
      (ledgerTokens old.ledger ++ oldAcks.map AckMessage.child)) :
    (protocolTokens ((t.root :: t.workers).map Tracked.ledger) work newAcks).Perm
      (protocolTokens ((s.root :: s.workers).map Tracked.ledger) work oldAcks) := by
  obtain ⟨before, after, oldSplit, newSplit⟩ := replace_lists replacement
  rw [oldSplit, newSplit]
  let pre := before.flatMap (fun w => ledgerTokens w.ledger)
  let post := after.flatMap (fun w => ledgerTokens w.ledger) ++ work.map WorkMessage.id
  have newMove := ((show (post ++ newAcks.map AckMessage.child).Perm (newAcks.map AckMessage.child ++ post)
    from List.perm_append_comm).append_left (ledgerTokens next.ledger)).append_left pre
  have localLift := (localPerm.append_right post).append_left pre
  have oldMove := ((show (oldAcks.map AckMessage.child ++ post).Perm (post ++ oldAcks.map AckMessage.child)
    from List.perm_append_comm).append_left (ledgerTokens old.ledger)).append_left pre
  have combined := newMove.trans (by simpa [List.append_assoc] using localLift)
  have combined := combined.trans (by simpa [List.append_assoc] using oldMove)
  simpa [protocolTokens, List.map_append, List.flatMap_append, List.flatMap_map,
    Function.comp_def, pre, post, List.append_assoc] using combined

theorem publish_ack_step_tokens {s t : ProtocolState} (worker : Tracked)
    (replace : SystemReplace s.system t.system worker (publishAck ⟨worker, s.acks⟩).current)
    (work : t.work = s.work) (acks : t.acks = (publishAck ⟨worker, s.acks⟩).flight) :
    t.tokens.Perm s.tokens := by
  have localPerm := publish_ack_moves_token ⟨worker, s.acks⟩
  simp only [ProtocolState.tokens, work]
  apply replacement_ack_tokens_perm replace s.work s.acks t.acks
  simpa [ackPublicationTokens, acks] using localPerm

theorem deliver_ack_tokens_sublist (state : AckDeliveryState) :
    (ackDeliveryTokens (deliverAck state)).Sublist (ackDeliveryTokens state) := by
  cases queued : state.flight with
  | nil => simp [ackDeliveryTokens, deliverAck, queued]
  | cons head tail =>
    by_cases ready : head.parent.worker = state.receiver.ledger.owner
    · simp only [ackDeliveryTokens, deliverAck, queued]
      rw [if_pos ready]
      simp only [ack_tokens, List.map_cons]
      exact (List.Sublist.cons head.child (List.Sublist.refl (tail.map AckMessage.child))).append_left
        (ledgerTokens state.receiver.ledger)
    · simp only [ackDeliveryTokens, deliverAck, queued]
      rw [if_neg ready]
      simp [queued]

theorem replacement_ack_tokens_nodup {s t : System} {old next : Tracked}
    (replacement : SystemReplace s t old next) (work : List WorkMessage) (oldAcks newAcks : List AckMessage)
    (localSub : (ledgerTokens next.ledger ++ newAcks.map AckMessage.child).Sublist
      (ledgerTokens old.ledger ++ oldAcks.map AckMessage.child))
    (unique : (protocolTokens ((s.root :: s.workers).map Tracked.ledger) work oldAcks).Nodup) :
    (protocolTokens ((t.root :: t.workers).map Tracked.ledger) work newAcks).Nodup := by
  obtain ⟨before, after, oldSplit, newSplit⟩ := replace_lists replacement
  rw [oldSplit] at unique
  rw [newSplit]
  let pre := before.flatMap (fun w => ledgerTokens w.ledger)
  let post := after.flatMap (fun w => ledgerTokens w.ledger) ++ work.map WorkMessage.id
  have oldMove := ((show (post ++ oldAcks.map AckMessage.child).Perm (oldAcks.map AckMessage.child ++ post)
    from List.perm_append_comm).append_left (ledgerTokens old.ledger)).append_left pre
  have source : (pre ++ ledgerTokens old.ledger ++ post ++ oldAcks.map AckMessage.child).Nodup := by
    simpa [protocolTokens, List.map_append, List.flatMap_append, List.flatMap_map,
      Function.comp_def, pre, post, List.append_assoc] using unique
  have reordered := oldMove.nodup (by simpa [List.append_assoc] using source)
  have sub := (localSub.append_right post).append_left pre
  have kept := sub.nodup (by simpa [List.append_assoc] using reordered)
  have newMove := ((show (post ++ newAcks.map AckMessage.child).Perm (newAcks.map AckMessage.child ++ post)
    from List.perm_append_comm).append_left (ledgerTokens next.ledger)).append_left pre
  have destination := newMove.symm.nodup (by simpa [List.append_assoc] using kept)
  simpa [protocolTokens, List.map_append, List.flatMap_append, List.flatMap_map,
    Function.comp_def, pre, post, List.append_assoc] using destination

theorem deliver_ack_step_tokens_unique {s t : ProtocolState} (worker : Tracked)
    (replace : SystemReplace s.system t.system worker (deliverAck ⟨worker, s.acks⟩).receiver)
    (work : t.work = s.work) (acks : t.acks = (deliverAck ⟨worker, s.acks⟩).flight)
    (unique : s.tokens.Nodup) : t.tokens.Nodup := by
  have sub := deliver_ack_tokens_sublist ⟨worker, s.acks⟩
  simp only [ProtocolState.tokens, work] at *
  apply replacement_ack_tokens_nodup replace s.work s.acks t.acks
  · simpa [ackDeliveryTokens, acks] using sub
  · exact unique

theorem replacement_tokens_add_perm {s t : System} {old next : Tracked}
    (replacement : SystemReplace s t old next) (work : List WorkMessage) (acks : List AckMessage) (id : Id)
    (localPerm : (ledgerTokens next.ledger).Perm (ledgerTokens old.ledger ++ [id])) :
    (protocolTokens ((t.root :: t.workers).map Tracked.ledger) work acks).Perm
      (protocolTokens ((s.root :: s.workers).map Tracked.ledger) work acks ++ [id]) := by
  obtain ⟨before, after, oldSplit, newSplit⟩ := replace_lists replacement
  rw [oldSplit, newSplit]
  let pre := before.flatMap (fun w => ledgerTokens w.ledger)
  let post := after.flatMap (fun w => ledgerTokens w.ledger) ++
    work.map WorkMessage.id ++ acks.map AckMessage.child
  have localLift := (localPerm.append_right post).append_left pre
  have move := (List.perm_middle (a := id) (l₁ := pre ++ ledgerTokens old.ledger)
    (l₂ := post)).trans (List.perm_append_singleton id (pre ++ ledgerTokens old.ledger ++ post)).symm
  have combined := localLift.trans (by simpa [List.append_assoc] using move)
  simpa [protocolTokens, List.map_append, List.flatMap_append, List.flatMap_map,
    Function.comp_def, pre, post, List.append_assoc] using combined

def ProtocolState.TokensCovered (s : ProtocolState) : Prop :=
  ∀ id ∈ s.tokens, ∃ edge ∈ trackedGraph (s.system.root :: s.system.workers), edge.child = id

theorem replace_old_member {s t : System} {old next : Tracked}
    (replacement : SystemReplace s t old next) : old ∈ s.root :: s.workers := by
  obtain ⟨before, after, split, _⟩ := replace_lists replacement
  rw [split]
  simp

theorem register_step_tokens_unique (owner : Nat) (others : List Nat)
    (distinct : (owner :: others).Nodup) (completed : Id → Prop) {s t : ProtocolState}
    (trace : ProtocolTrace completed (initialProtocol owner others) s)
    (worker : Tracked) (p : Id) (destination : Nat) (payload : List UInt8)
    (replace : SystemReplace s.system t.system worker (worker.run (.register p destination payload)))
    (work : t.work = s.work) (acks : t.acks = s.acks)
    (unique : s.tokens.Nodup) (covered : s.TokensCovered) : t.tokens.Nodup := by
  cases found : lookup Record.id p worker.ledger.records with
  | none =>
    have rejected := register_missing worker.ledger p destination payload found
    have localPerm : (ledgerTokens (worker.run (.register p destination payload)).ledger).Perm
        (ledgerTokens worker.ledger) := by simp [Tracked.run, Tracked.register, rejected]
    have perm := replacement_tokens_perm replace s.work s.acks localPerm
    simpa [ProtocolState.tokens, work, acks] using perm.symm.nodup unique
  | some r =>
    cases phase : r.phase with
    | closed =>
      have rejected := register_closed worker.ledger p destination payload r found phase
      have localPerm : (ledgerTokens (worker.run (.register p destination payload)).ledger).Perm
          (ledgerTokens worker.ledger) := by simp [Tracked.run, Tracked.register, rejected]
      have perm := replacement_tokens_perm replace s.work s.acks localPerm
      simpa [ProtocolState.tokens, work, acks] using perm.symm.nodup unique
    | «open» =>
      have member := replace_old_member replace
      have freshGraph := initialized_trace_global_fresh owner others distinct s.system
        (protocol_trace_projects trace) worker member
      have freshToken : Id.work worker.ledger.owner worker.ledger.next ∉ s.tokens := by
        intro tokenMember
        obtain ⟨edge, edgeMember, equal⟩ := covered _ tokenMember
        exact freshGraph edge edgeMember equal
      have localPerm : (ledgerTokens (worker.run (.register p destination payload)).ledger).Perm
          (ledgerTokens worker.ledger ++ [.work worker.ledger.owner worker.ledger.next]) := by
        have result := register_open worker.ledger p destination payload r found phase
        simpa [Tracked.run, Tracked.register, result] using
          registration_adds_token worker.ledger p destination payload r found phase
      have perm := replacement_tokens_add_perm replace s.work s.acks _ localPerm
      have extended : (s.tokens ++ [Id.work worker.ledger.owner worker.ledger.next]).Nodup := by
        simpa [Unique, insert] using insert_unique (fun id : Id => id)
          (.work worker.ledger.owner worker.ledger.next) s.tokens (by simpa [Unique] using unique)
          (by simpa using freshToken)
      simpa [ProtocolState.tokens, work, acks] using perm.symm.nodup extended

/-- All step cases preserve token uniqueness if current tokens are graph-backed. -/
theorem protocol_step_tokens_unique (owner : Nat) (others : List Nat)
    (distinct : (owner :: others).Nodup) (completed : Id → Prop) {s t : ProtocolState}
    (trace : ProtocolTrace completed (initialProtocol owner others) s)
    (step : ProtocolStep completed s t) (unique : s.tokens.Nodup) (covered : s.TokensCovered) :
    t.tokens.Nodup := by
  cases step with
  | register next worker parent destination payload replace =>
    exact register_step_tokens_unique owner others distinct completed trace worker parent destination payload
      replace rfl rfl unique covered
  | close next worker id replace =>
    exact (close_step_tokens (s := s) (t := { s with system := next }) worker id replace rfl rfl).symm.nodup unique
  | retire next worker id done replace =>
    exact (retire_step_tokens (s := s) (t := { s with system := next }) worker id replace rfl rfl).symm.nodup unique
  | publishWork next worker replace =>
    exact (publish_work_step_tokens (s := s) (t := { s with system := next, work := (publishWork ⟨worker, s.work⟩).flight }) worker replace rfl rfl).symm.nodup unique
  | deliverWork next worker replace =>
    exact (deliver_work_step_tokens (s := s) (t := { s with system := next, work := (deliverWork ⟨worker, s.work⟩).flight }) worker replace rfl rfl).symm.nodup unique
  | publishAck next worker replace =>
    exact (publish_ack_step_tokens (s := s) (t := { s with system := next, acks := (publishAck ⟨worker, s.acks⟩).flight }) worker replace rfl rfl).symm.nodup unique
  | deliverAck next worker replace =>
    exact deliver_ack_step_tokens_unique (s := s) worker replace rfl rfl unique

theorem replacement_graph_perm {s t : System} {old next : Tracked}
    (replacement : SystemReplace s t old next)
    (localPerm : (ledgerEdges next.ledger).Perm (ledgerEdges old.ledger)) :
    (trackedGraph (t.root :: t.workers)).Perm (trackedGraph (s.root :: s.workers)) := by
  obtain ⟨before, after, oldSplit, newSplit⟩ := replace_lists replacement
  rw [oldSplit, newSplit]
  have lifted := (localPerm.append_right (trackedGraph after)).append_left (trackedGraph before)
  simpa [trackedGraph, List.flatMap_append, List.append_assoc] using lifted

theorem covered_by_permutation {s t : ProtocolState}
    (tokens : t.tokens.Perm s.tokens)
    (graph : (trackedGraph (t.system.root :: t.system.workers)).Perm
      (trackedGraph (s.system.root :: s.system.workers)))
    (covered : s.TokensCovered) : t.TokensCovered := by
  intro id member
  obtain ⟨edge, edgeMember, equal⟩ := covered id (tokens.mem_iff.mp member)
  exact ⟨edge, graph.mem_iff.mpr edgeMember, equal⟩

theorem publish_work_graph (worker : Tracked) (messages : List WorkMessage) :
    ledgerEdges (publishWork ⟨worker, messages⟩).current.ledger = ledgerEdges worker.ledger := by
  cases queued : worker.ledger.outputs with
  | nil => simp [publishWork, takeOutput, queued]
  | cons head tail =>
    cases head <;> simp [publishWork, takeOutput, queued, ledgerEdges]

theorem publish_ack_graph (worker : Tracked) (messages : List AckMessage) :
    ledgerEdges (publishAck ⟨worker, messages⟩).current.ledger = ledgerEdges worker.ledger := by
  cases queued : worker.ledger.outputs with
  | nil => simp [publishAck, takeOutput, queued]
  | cons head tail =>
    cases head <;> simp [publishAck, takeOutput, queued, ledgerEdges]

theorem deliver_work_graph (worker : Tracked) (messages : List WorkMessage) :
    ledgerEdges (deliverWork ⟨worker, messages⟩).receiver.ledger = ledgerEdges worker.ledger := by
  cases queued : messages with
  | nil => simp [deliverWork]
  | cons head tail =>
    by_cases ready : head.destination = worker.ledger.owner ∧ head.id ≠ .root ∧
        head.id ∉ worker.ledger.records.map Record.id
    · simp only [deliverWork]
      rw [if_pos ready]
      exact install_edges_equal worker.ledger head.id head.parent
    · simp only [deliverWork]
      rw [if_neg ready]

theorem replacement_graph_add_perm {s t : System} {old next : Tracked}
    (replacement : SystemReplace s t old next) (edge : Edge)
    (localPerm : (ledgerEdges next.ledger).Perm (ledgerEdges old.ledger ++ [edge])) :
    (trackedGraph (t.root :: t.workers)).Perm (trackedGraph (s.root :: s.workers) ++ [edge]) := by
  obtain ⟨before, after, oldSplit, newSplit⟩ := replace_lists replacement
  rw [oldSplit, newSplit]
  let pre := trackedGraph before
  let post := trackedGraph after
  have localLift := (localPerm.append_right post).append_left pre
  have move := (List.perm_middle (a := edge) (l₁ := pre ++ ledgerEdges old.ledger)
    (l₂ := post)).trans (List.perm_append_singleton edge (pre ++ ledgerEdges old.ledger ++ post)).symm
  have combined := localLift.trans (by simpa [List.append_assoc] using move)
  simpa [trackedGraph, List.flatMap_append, pre, post, List.append_assoc] using combined

theorem register_step_tokens_covered {s t : ProtocolState} (worker : Tracked) (p : Id)
    (destination : Nat) (payload : List UInt8)
    (replace : SystemReplace s.system t.system worker (worker.run (.register p destination payload)))
    (work : t.work = s.work) (acks : t.acks = s.acks) (covered : s.TokensCovered) :
    t.TokensCovered := by
  cases found : lookup Record.id p worker.ledger.records with
  | none =>
    have rejected := register_missing worker.ledger p destination payload found
    have same : worker.run (.register p destination payload) = worker := by
      simp [Tracked.run, Tracked.register, rejected]
    have tokenPerm := replacement_tokens_perm replace s.work s.acks (by simp [same])
    have graphPerm := replacement_graph_perm replace (by simp [same])
    apply covered_by_permutation (s := s)
    · simpa [ProtocolState.tokens, work, acks] using tokenPerm
    · exact graphPerm
    · exact covered
  | some r =>
    cases phase : r.phase with
    | closed =>
      have rejected := register_closed worker.ledger p destination payload r found phase
      have same : worker.run (.register p destination payload) = worker := by
        simp [Tracked.run, Tracked.register, rejected]
      have tokenPerm := replacement_tokens_perm replace s.work s.acks (by simp [same])
      have graphPerm := replacement_graph_perm replace (by simp [same])
      apply covered_by_permutation (s := s)
      · simpa [ProtocolState.tokens, work, acks] using tokenPerm
      · exact graphPerm
      · exact covered
    | «open» =>
      let id := Id.work worker.ledger.owner worker.ledger.next
      let added : Edge := ⟨p, id, destination⟩
      have result := register_open worker.ledger p destination payload r found phase
      have localTokens : (ledgerTokens (worker.run (.register p destination payload)).ledger).Perm
          (ledgerTokens worker.ledger ++ [id]) := by
        simpa [Tracked.run, Tracked.register, result, id] using
          registration_adds_token worker.ledger p destination payload r found phase
      have localEdges : (ledgerEdges (worker.run (.register p destination payload)).ledger).Perm
          (ledgerEdges worker.ledger ++ [added]) := by
        simpa [Tracked.run, Tracked.register, result, added, id] using
          register_edges_perm worker.ledger p destination payload r found phase
      have tokenPerm := replacement_tokens_add_perm replace s.work s.acks id localTokens
      have graphPerm := replacement_graph_add_perm replace added localEdges
      intro token member
      have inOldOrAdded : token ∈ s.tokens ++ [id] := by
        have inPerm := tokenPerm.mem_iff.mp (by simpa [ProtocolState.tokens, work, acks] using member)
        simpa [ProtocolState.tokens] using inPerm
      rcases List.mem_append.mp inOldOrAdded with old | new
      · obtain ⟨edge, edgeMember, equal⟩ := covered token old
        refine ⟨edge, graphPerm.mem_iff.mpr ?_, equal⟩
        exact List.mem_append_left _ edgeMember
      · have tokenId : token = id := by simpa using new
        subst token
        refine ⟨added, graphPerm.mem_iff.mpr ?_, rfl⟩
        simp

theorem replacement_graph_preserves_other {s t : System} {old next : Tracked}
    (replacement : SystemReplace s t old next) (id : Id)
    (localPreserve : ∀ edge ∈ ledgerEdges old.ledger, edge.child ≠ id → edge ∈ ledgerEdges next.ledger)
    (edge : Edge) (oldMember : edge ∈ trackedGraph (s.root :: s.workers))
    (different : edge.child ≠ id) : edge ∈ trackedGraph (t.root :: t.workers) := by
  obtain ⟨before, after, oldSplit, newSplit⟩ := replace_lists replacement
  rw [oldSplit] at oldMember
  rw [newSplit]
  simp only [trackedGraph, List.flatMap_append, List.flatMap_cons, List.mem_append] at oldMember ⊢
  rcases oldMember with beforeMember | oldMember | afterMember
  · exact Or.inl beforeMember
  · exact Or.inr (Or.inl (localPreserve edge oldMember different))
  · exact Or.inr (Or.inr afterMember)

theorem delivered_ack_token_facts {s t : ProtocolState} (worker : Tracked) (message : AckMessage)
    (tail : List AckMessage) (queued : s.acks = message :: tail)
    (destination : message.parent.worker = worker.ledger.owner)
    (replace : SystemReplace s.system t.system worker (deliverAck ⟨worker, s.acks⟩).receiver)
    (work : t.work = s.work) (acks : t.acks = tail) (unique : s.tokens.Nodup) :
    ∀ id ∈ t.tokens, id ∈ s.tokens ∧ id ≠ message.child := by
  have localPerm : (ledgerTokens (deliverAck ⟨worker, s.acks⟩).receiver.ledger).Perm
      (ledgerTokens worker.ledger) := by
    simp only [deliverAck, queued]
    rw [if_pos destination]
    simp [ack_tokens]
  have perm := replacement_tokens_perm replace s.work tail localPerm
  let base := ((s.system.root :: s.system.workers).map Tracked.ledger).flatMap ledgerTokens ++
    s.work.map WorkMessage.id
  have source : (base ++ message.child :: tail.map AckMessage.child).Nodup := by
    simpa [ProtocolState.tokens, protocolTokens, queued, base, List.append_assoc] using unique
  have parts := List.nodup_append.mp source
  have absentTail := (List.nodup_cons.mp parts.2.1).1
  have absentBase : message.child ∉ base := by
    intro inBase
    exact (parts.2.2 message.child inBase message.child (by simp)) rfl
  intro id member
  have remaining : id ∈ base ++ tail.map AckMessage.child := by
    have translated := perm.mem_iff.mp (by simpa [ProtocolState.tokens, work, acks] using member)
    simpa [protocolTokens, base, List.append_assoc] using translated
  constructor
  · have earlier : id ∈ base ++ message.child :: tail.map AckMessage.child := by
      rcases List.mem_append.mp remaining with inBase | inTail
      · exact List.mem_append_left _ inBase
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ inTail)
    simpa [ProtocolState.tokens, protocolTokens, queued, base, List.append_assoc] using earlier
  · intro equal
    subst id
    rcases List.mem_append.mp remaining with inBase | inTail
    · exact absentBase inBase
    · exact absentTail inTail

theorem deliver_ack_step_tokens_covered {s t : ProtocolState} (worker : Tracked)
    (replace : SystemReplace s.system t.system worker (deliverAck ⟨worker, s.acks⟩).receiver)
    (work : t.work = s.work) (acks : t.acks = (deliverAck ⟨worker, s.acks⟩).flight)
    (unique : s.tokens.Nodup) (covered : s.TokensCovered) : t.TokensCovered := by
  cases queued : s.acks with
  | nil =>
    have same : (deliverAck ⟨worker, s.acks⟩).receiver = worker := by simp [deliverAck, queued]
    have sameAcks : t.acks = s.acks := by simpa [deliverAck, queued] using acks
    have tokenPerm := replacement_tokens_perm replace s.work s.acks (by simp [same])
    have graphPerm := replacement_graph_perm replace (by simp [same])
    exact covered_by_permutation (by simpa [ProtocolState.tokens, work, sameAcks] using tokenPerm) graphPerm covered
  | cons message tail =>
    by_cases destination : message.parent.worker = worker.ledger.owner
    · have newAcks : t.acks = tail := by
        simp only [deliverAck, queued, destination, ↓reduceIte] at acks
        exact acks
      have tokenFacts := delivered_ack_token_facts worker message tail queued destination replace work newAcks unique
      intro id member
      obtain ⟨oldMember, different⟩ := tokenFacts id member
      obtain ⟨edge, oldEdge, equal⟩ := covered id oldMember
      refine ⟨edge, ?_, equal⟩
      apply replacement_graph_preserves_other replace message.child
      · intro candidate candidateOld candidateDifferent
        simp only [deliverAck, queued]
        rw [if_pos destination]
        exact acknowledge_preserves_other_edges worker.ledger message.parent.id message.child message.source
          candidate candidateDifferent candidateOld
      · exact oldEdge
      · simpa [equal] using different
    · have same : (deliverAck ⟨worker, s.acks⟩).receiver = worker := by
        simp only [deliverAck, queued]
        rw [if_neg destination]
      have sameAcks : t.acks = s.acks := by
        simp only [deliverAck, queued] at acks
        rw [if_neg destination] at acks
        simpa [queued] using acks
      have tokenPerm := replacement_tokens_perm replace s.work s.acks (by simp [same])
      have graphPerm := replacement_graph_perm replace (by simp [same])
      exact covered_by_permutation (by simpa [ProtocolState.tokens, work, sameAcks] using tokenPerm) graphPerm covered

theorem protocol_step_tokens_covered {completed : Id → Prop} {s t : ProtocolState}
    (step : ProtocolStep completed s t) (unique : s.tokens.Nodup) (covered : s.TokensCovered) :
    t.TokensCovered := by
  cases step with
  | register next worker parent destination payload replace =>
    exact register_step_tokens_covered worker parent destination payload replace rfl rfl covered
  | close next worker id replace =>
    apply covered_by_permutation (s := s)
    · exact close_step_tokens worker id replace rfl rfl
    · apply replacement_graph_perm replace
      simp [Tracked.run, close_edges_equal]
    · exact covered
  | retire next worker id done replace =>
    apply covered_by_permutation (s := s)
    · exact retire_step_tokens worker id replace rfl rfl
    · apply replacement_graph_perm replace
      simp [Tracked.run, retire_edges_equal]
    · exact covered
  | publishWork next worker replace =>
    apply covered_by_permutation (s := s)
    · exact publish_work_step_tokens worker replace rfl rfl
    · apply replacement_graph_perm replace
      simp [publish_work_graph]
    · exact covered
  | deliverWork next worker replace =>
    apply covered_by_permutation (s := s)
    · exact deliver_work_step_tokens worker replace rfl rfl
    · apply replacement_graph_perm replace
      simp [deliver_work_graph]
    · exact covered
  | publishAck next worker replace =>
    apply covered_by_permutation (s := s)
    · exact publish_ack_step_tokens worker replace rfl rfl
    · apply replacement_graph_perm replace
      simp [publish_ack_graph]
    · exact covered
  | deliverAck next worker replace =>
    exact deliver_ack_step_tokens_covered worker replace rfl rfl unique covered

/-- Token uniqueness and token-to-edge coverage are derived together from initialization. -/
theorem initialized_protocol_token_invariants (owner : Nat) (others : List Nat)
    (distinct : (owner :: others).Nodup) (completed : Id → Prop) {s : ProtocolState}
    (trace : ProtocolTrace completed (initialProtocol owner others) s) :
    s.tokens.Nodup ∧ s.TokensCovered := by
  induction trace with
  | refl =>
    have empty : (initialProtocol owner others).tokens = [] := by
      exact initialized_protocol_tokens_empty owner others
    refine ⟨by simp [empty], ?_⟩
    intro id member
    simp [empty] at member
  | next history step ih =>
    exact ⟨protocol_step_tokens_unique owner others distinct completed history step ih.1 ih.2,
      protocol_step_tokens_covered step ih.1 ih.2⟩

theorem replacement_graph_sublist {s t : System} {old next : Tracked}
    (replacement : SystemReplace s t old next)
    (localSub : (ledgerEdges next.ledger).Sublist (ledgerEdges old.ledger)) :
    (trackedGraph (t.root :: t.workers)).Sublist (trackedGraph (s.root :: s.workers)) := by
  obtain ⟨before, after, oldSplit, newSplit⟩ := replace_lists replacement
  rw [oldSplit, newSplit]
  have lifted := (localSub.append_right (trackedGraph after)).append_left (trackedGraph before)
  simpa [trackedGraph, List.flatMap_append, List.append_assoc] using lifted

def GraphRooted (graph : List Edge) : Prop := ∀ edge ∈ graph, Rooted graph edge.child

theorem rooted_after_restricted_removal (old new : List Edge) (id : Id)
    (unique : Unique Edge.child old) (leaf : Leaf old id)
    (subset : new.Sublist old)
    (retained : ∀ edge ∈ old, edge.child ≠ id → edge ∈ new)
    (rooted : GraphRooted old) : GraphRooted new := by
  intro edge newMember
  have oldMember := subset.mem newMember
  by_cases same : edge.child = id
  · have contains : ∀ x ∈ old, x ∈ new := by
      intro x xmem
      by_cases different : x.child ≠ id
      · exact retained x xmem different
      · have xId : x.child = id := by
          by_cases equality : x.child = id
          · exact equality
          · exact False.elim (different equality)
        have sameKey : x.child = edge.child := xId.trans same.symm
        have equal := unique_keys_injective Edge.child old x edge unique xmem oldMember sameKey
        simpa [equal] using newMember
    exact rooted_mono old new edge.child contains (rooted edge oldMember)
  · let removed : Edge := ⟨.root, id, 0⟩
    have surviving := rooted_after_leaf_removal old removed edge.child unique (by simpa [removed] using leaf)
      (rooted edge oldMember) (by simpa [removed] using same)
    apply rooted_mono (erase Edge.child id old) new edge.child _ surviving
    intro x member
    have oldAndDifferent := (erase_membership Edge.child id old x unique).mp member
    exact retained x oldAndDifferent.1 oldAndDifferent.2

theorem initialized_trace_inflight_nonroot_leaf (owner : Nat) (others : List Nat) {s : System}
    (trace : SystemTrace (initialSystem owner others) s) (work : List WorkMessage)
    (acks : List AckMessage)
    (unique : (protocolTokens ((s.root :: s.workers).map Tracked.ledger) work acks).Nodup)
    (message : AckMessage) (inFlight : message ∈ acks) (nonroot : message.child ≠ .root) :
    Leaf (trackedGraph (s.root :: s.workers)) message.child := by
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

theorem initialized_protocol_record_rooted (owner : Nat) (others : List Nat)
    (distinct : (owner :: others).Nodup) (completed : Id → Prop) {s : ProtocolState}
    (trace : ProtocolTrace completed (initialProtocol owner others) s)
    (rooted : GraphRooted (trackedGraph (s.system.root :: s.system.workers)))
    (worker : Tracked) (member : worker ∈ s.system.root :: s.system.workers)
    (record : Record) (recordMember : record ∈ worker.ledger.records) :
    Rooted (trackedGraph (s.system.root :: s.system.workers)) record.id := by
  by_cases root : record.id = .root
  · rw [root]; exact .root
  · have shaped := system_trace_shaped (initial_system_shaped owner others) (protocol_trace_projects trace)
    have workerShape : ParentShape worker.ledger := by
      rcases List.mem_cons.mp member with same | rest
      · subst worker; exact shaped.1
      · exact shaped.2 worker rest
    obtain ⟨parent, field⟩ := workerShape record recordMember root
    have ledgerMember : worker.ledger ∈ (s.system.root :: s.system.workers).map Tracked.ledger :=
      List.mem_map.mpr ⟨worker, member, rfl⟩
    have recordToken := running_record_token _ worker.ledger record parent ledgerMember recordMember field
    have tokenMember : record.id ∈ s.tokens := by
      simp only [ProtocolState.tokens, protocolTokens, List.mem_append]
      exact Or.inl (Or.inl recordToken)
    have covered := (initialized_protocol_token_invariants owner others distinct completed trace).2
    obtain ⟨edge, edgeMember, equal⟩ := covered record.id tokenMember
    rw [← equal]
    exact rooted edge edgeMember

theorem graph_rooted_perm {old new : List Edge} (permutation : new.Perm old)
    (rooted : GraphRooted old) : GraphRooted new := by
  intro edge member
  have oldMember := permutation.mem_iff.mp member
  exact rooted_mono old new edge.child (fun e mem => permutation.mem_iff.mpr mem) (rooted edge oldMember)

theorem graph_rooted_add (graph : List Edge) (edge : Edge) (rooted : GraphRooted graph)
    (parent : Rooted graph edge.parent) : GraphRooted (graph ++ [edge]) := by
  intro item member
  rcases List.mem_append.mp member with old | added
  · exact rooted_mono graph (graph ++ [edge]) item.child (fun e mem => List.mem_append_left _ mem)
      (rooted item old)
  · simp only [List.mem_singleton] at added
    subst item
    exact rooted_register graph edge.parent edge.child edge.destination parent

theorem register_step_graph_rooted (owner : Nat) (others : List Nat)
    (distinct : (owner :: others).Nodup) (completed : Id → Prop) {s t : ProtocolState}
    (trace : ProtocolTrace completed (initialProtocol owner others) s)
    (worker : Tracked) (p : Id) (destination : Nat) (payload : List UInt8)
    (replace : SystemReplace s.system t.system worker (worker.run (.register p destination payload)))
    (rooted : GraphRooted (trackedGraph (s.system.root :: s.system.workers))) :
    GraphRooted (trackedGraph (t.system.root :: t.system.workers)) := by
  cases found : lookup Record.id p worker.ledger.records with
  | none =>
    have rejected := register_missing worker.ledger p destination payload found
    have same : worker.run (.register p destination payload) = worker := by
      simp [Tracked.run, Tracked.register, rejected]
    exact graph_rooted_perm (replacement_graph_perm replace (by simp [same])) rooted
  | some r =>
    cases phase : r.phase with
    | closed =>
      have rejected := register_closed worker.ledger p destination payload r found phase
      have same : worker.run (.register p destination payload) = worker := by
        simp [Tracked.run, Tracked.register, rejected]
      exact graph_rooted_perm (replacement_graph_perm replace (by simp [same])) rooted
    | «open» =>
      let edge : Edge := ⟨p, .work worker.ledger.owner worker.ledger.next, destination⟩
      have info := lookup_sound Record.id p worker.ledger.records r found
      have parent := initialized_protocol_record_rooted owner others distinct completed trace rooted
        worker (replace_old_member replace) r info.1
      have parentRooted : Rooted (trackedGraph (s.system.root :: s.system.workers)) p := by
        simpa [info.2] using parent
      have result := register_open worker.ledger p destination payload r found phase
      have localPerm : (ledgerEdges (worker.run (.register p destination payload)).ledger).Perm
          (ledgerEdges worker.ledger ++ [edge]) := by
        simpa [Tracked.run, Tracked.register, result, edge] using
          register_edges_perm worker.ledger p destination payload r found phase
      have perm := replacement_graph_add_perm replace edge localPerm
      exact graph_rooted_perm perm (graph_rooted_add _ edge rooted parentRooted)

theorem deliver_ack_step_graph_rooted (owner : Nat) (others : List Nat)
    (distinct : (owner :: others).Nodup) (completed : Id → Prop) {s t : ProtocolState}
    (trace : ProtocolTrace completed (initialProtocol owner others) s)
    (worker : Tracked)
    (replace : SystemReplace s.system t.system worker (deliverAck ⟨worker, s.acks⟩).receiver)
    (rooted : GraphRooted (trackedGraph (s.system.root :: s.system.workers))) :
    GraphRooted (trackedGraph (t.system.root :: t.system.workers)) := by
  cases queued : s.acks with
  | nil =>
    have same : (deliverAck ⟨worker, s.acks⟩).receiver = worker := by simp [deliverAck, queued]
    exact graph_rooted_perm (replacement_graph_perm replace (by simp [same])) rooted
  | cons message tail =>
    by_cases destination : message.parent.worker = worker.ledger.owner
    · have sub : (ledgerEdges (deliverAck ⟨worker, s.acks⟩).receiver.ledger).Sublist
          (ledgerEdges worker.ledger) := by
        simp only [deliverAck, queued]
        rw [if_pos destination]
        exact acknowledge_edges_sublist worker.ledger message.parent.id message.child message.source
      have graphSub := replacement_graph_sublist replace sub
      have retained : ∀ edge ∈ trackedGraph (s.system.root :: s.system.workers),
          edge.child ≠ message.child → edge ∈ trackedGraph (t.system.root :: t.system.workers) := by
        intro edge oldMember different
        apply replacement_graph_preserves_other replace message.child _ edge oldMember different
        intro candidate oldCandidate candidateDifferent
        simp only [deliverAck, queued]
        rw [if_pos destination]
        exact acknowledge_preserves_other_edges worker.ledger message.parent.id message.child message.source
          candidate candidateDifferent oldCandidate
      by_cases root : message.child = .root
      · have contains : ∀ edge ∈ trackedGraph (s.system.root :: s.system.workers),
            edge ∈ trackedGraph (t.system.root :: t.system.workers) := by
          intro edge member
          apply retained edge member
          simpa [root] using initialized_trace_graph_nonroot owner others (protocol_trace_projects trace) edge member
        intro edge member
        have oldMember := graphSub.mem member
        exact rooted_mono _ _ edge.child contains (rooted edge oldMember)
      · have uniqueGraph := initialized_protocol_graph_unique owner others distinct completed trace
        have uniqueTokens := (initialized_protocol_token_invariants owner others distinct completed trace).1
        have inFlight : message ∈ s.acks := by simp [queued]
        have leaf := initialized_trace_inflight_nonroot_leaf owner others (protocol_trace_projects trace)
          s.work s.acks uniqueTokens message inFlight root
        exact rooted_after_restricted_removal _ _ message.child uniqueGraph leaf graphSub retained rooted
    · have same : (deliverAck ⟨worker, s.acks⟩).receiver = worker := by
        simp only [deliverAck, queued]
        rw [if_neg destination]
      exact graph_rooted_perm (replacement_graph_perm replace (by simp [same])) rooted

theorem protocol_step_graph_rooted (owner : Nat) (others : List Nat)
    (distinct : (owner :: others).Nodup) (completed : Id → Prop) {s t : ProtocolState}
    (trace : ProtocolTrace completed (initialProtocol owner others) s)
    (step : ProtocolStep completed s t)
    (rooted : GraphRooted (trackedGraph (s.system.root :: s.system.workers))) :
    GraphRooted (trackedGraph (t.system.root :: t.system.workers)) := by
  cases step with
  | register next worker parent destination payload replace =>
    exact register_step_graph_rooted owner others distinct completed trace worker parent destination payload replace rooted
  | close next worker id replace =>
    exact graph_rooted_perm (replacement_graph_perm replace (by simp [Tracked.run, close_edges_equal])) rooted
  | retire next worker id done replace =>
    exact graph_rooted_perm (replacement_graph_perm replace (by simp [Tracked.run, retire_edges_equal])) rooted
  | publishWork next worker replace =>
    exact graph_rooted_perm (replacement_graph_perm replace (by simp [publish_work_graph])) rooted
  | deliverWork next worker replace =>
    exact graph_rooted_perm (replacement_graph_perm replace (by simp [deliver_work_graph])) rooted
  | publishAck next worker replace =>
    exact graph_rooted_perm (replacement_graph_perm replace (by simp [publish_ack_graph])) rooted
  | deliverAck next worker replace =>
    exact deliver_ack_step_graph_rooted owner others distinct completed trace worker replace rooted

theorem initialized_protocol_graph_rooted (owner : Nat) (others : List Nat)
    (distinct : (owner :: others).Nodup) (completed : Id → Prop) {s : ProtocolState}
    (trace : ProtocolTrace completed (initialProtocol owner others) s) :
    GraphRooted (trackedGraph (s.system.root :: s.system.workers)) := by
  induction trace with
  | refl => simp [initialProtocol, initial_graph_empty, GraphRooted]
  | next history step ih => exact protocol_step_graph_rooted owner others distinct completed history step ih

/-- A true current root probe leaves no modeled pending, running or in-flight token. -/
theorem initialized_protocol_quiet_tokens_empty (owner : Nat) (others : List Nat)
    (distinct : (owner :: others).Nodup) (completed : Id → Prop) {s : ProtocolState}
    (trace : ProtocolTrace completed (initialProtocol owner others) s)
    (quiet : probeRoot s.system.root.ledger = true) : s.tokens = [] := by
  have covered := (initialized_protocol_token_invariants owner others distinct completed trace).2
  have rooted := initialized_protocol_graph_rooted owner others distinct completed trace
  have noRootEdge := initialized_protocol_quiet_no_root_edge owner others completed trace quiet
  cases tokens : s.tokens with
  | nil => rfl
  | cons id tail =>
    have member : id ∈ s.tokens := by simp [tokens]
    obtain ⟨edge, edgeMember, equal⟩ := covered id member
    have nonroot := initialized_trace_graph_nonroot owner others (protocol_trace_projects trace) edge edgeMember
    obtain ⟨rootEdge, rootMember, atRoot⟩ :=
      rooted_has_root_edge _ edge.child (rooted edge edgeMember) nonroot
    exact False.elim (noRootEdge rootEdge rootMember atRoot)

theorem quiet_flights_empty (s : ProtocolState) (empty : s.tokens = []) :
    s.work = [] ∧ s.acks = [] := by
  have pieces : ledgerTokens s.system.root.ledger = [] ∧
      (∀ a ∈ s.system.workers, ledgerTokens a.ledger = []) ∧ s.work = [] ∧ s.acks = [] := by
    simpa [ProtocolState.tokens, protocolTokens, List.append_eq_nil_iff, and_assoc] using empty
  exact ⟨pieces.2.2.1, pieces.2.2.2⟩

theorem quiet_worker_outputs_empty (s : ProtocolState) (empty : s.tokens = [])
    (worker : Tracked) (member : worker ∈ s.system.root :: s.system.workers) :
    worker.ledger.outputs = [] := by
  cases outputs : worker.ledger.outputs with
  | nil => rfl
  | cons output tail =>
    have ledgerMember : worker.ledger ∈ (s.system.root :: s.system.workers).map Tracked.ledger :=
      List.mem_map.mpr ⟨worker, member, rfl⟩
    have tokenMember : outputToken output ∈ s.tokens := by
      simp only [ProtocolState.tokens, protocolTokens, List.mem_append]
      apply Or.inl
      apply Or.inl
      apply List.mem_flatMap.mpr
      refine ⟨worker.ledger, ledgerMember, ?_⟩
      simp only [ledgerTokens, List.mem_append]
      exact Or.inl (List.mem_map.mpr ⟨output, by simp [outputs], rfl⟩)
    simp [empty] at tokenMember

theorem quiet_no_parented_record (s : ProtocolState) (empty : s.tokens = [])
    (worker : Tracked) (member : worker ∈ s.system.root :: s.system.workers)
    (record : Record) (recordMember : record ∈ worker.ledger.records) : record.parent = none := by
  cases field : record.parent with
  | none => rfl
  | some parent =>
    have ledgerMember : worker.ledger ∈ (s.system.root :: s.system.workers).map Tracked.ledger :=
      List.mem_map.mpr ⟨worker, member, rfl⟩
    have token := running_record_token _ worker.ledger record parent ledgerMember recordMember field
    have tokenMember : record.id ∈ s.tokens := by
      simp only [ProtocolState.tokens, protocolTokens, List.mem_append]
      exact Or.inl (Or.inl token)
    simp [empty] at tokenMember

theorem initialized_protocol_quiet_record (owner : Nat) (others : List Nat)
    (distinct : (owner :: others).Nodup) (completed : Id → Prop) {s : ProtocolState}
    (trace : ProtocolTrace completed (initialProtocol owner others) s)
    (quiet : probeRoot s.system.root.ledger = true) (worker : Tracked)
    (member : worker ∈ s.system.root :: s.system.workers) (record : Record)
    (recordMember : record ∈ worker.ledger.records) :
    record.id = .root ∧ record.phase = .closed ∧ record.children = [] := by
  have empty := initialized_protocol_quiet_tokens_empty owner others distinct completed trace quiet
  have noParent := quiet_no_parented_record s empty worker member record recordMember
  have shaped := system_trace_shaped (initial_system_shaped owner others) (protocol_trace_projects trace)
  have workerShape : ParentShape worker.ledger := by
    rcases List.mem_cons.mp member with same | rest
    · subst worker; exact shaped.1
    · exact shaped.2 worker rest
  have recordRoot : record.id = .root := by
    by_cases isRoot : record.id = .root
    · exact isRoot
    · obtain ⟨parent, field⟩ := workerShape record recordMember isRoot
      simp [noParent] at field
  have valid := system_trace_valid (initial_system_valid owner others) (protocol_trace_projects trace)
  have confined := system_root_confined s.system valid
  have ledgerMember : worker.ledger ∈ s.system.root.ledger :: s.system.workers.map Tracked.ledger := by
    simpa using List.mem_map.mpr ⟨worker, member, rfl⟩
  have sameLedger : worker.ledger = s.system.root.ledger := by
    by_cases same : worker.ledger = s.system.root.ledger
    · exact same
    · exact False.elim (confined.2 worker.ledger ledgerMember same record recordMember recordRoot)
  obtain ⟨rootRecord, found, closed, children⟩ := quiet_probe_is_closed_empty s.system.root.ledger quiet
  have rootInfo := lookup_sound Record.id .root s.system.root.ledger.records rootRecord found
  have recordInRoot : record ∈ s.system.root.ledger.records := by simpa [sameLedger] using recordMember
  have sameRecord : record = rootRecord := unique_keys_injective Record.id _ record rootRecord
    valid.1.1.2.1 recordInRoot rootInfo.1 (recordRoot.trans rootInfo.2.symm)
  subst record
  exact ⟨rootInfo.2, closed, children⟩

theorem initialized_protocol_quiet_lookup (owner : Nat) (others : List Nat)
    (distinct : (owner :: others).Nodup) (completed : Id → Prop) {s : ProtocolState}
    (trace : ProtocolTrace completed (initialProtocol owner others) s)
    (quiet : probeRoot s.system.root.ledger = true) (worker : Tracked)
    (member : worker ∈ s.system.root :: s.system.workers) (id : Id) (record : Record)
    (found : lookup Record.id id worker.ledger.records = some record) :
    id = .root ∧ record.phase = .closed ∧ record.children = [] := by
  have info := lookup_sound Record.id id worker.ledger.records record found
  have shape := initialized_protocol_quiet_record owner others distinct completed trace quiet worker member record info.1
  exact ⟨info.2.symm.trans shape.1, shape.2⟩

theorem quiet_worker_action_unchanged (owner : Nat) (others : List Nat)
    (distinct : (owner :: others).Nodup) (completed : Id → Prop) {s : ProtocolState}
    (trace : ProtocolTrace completed (initialProtocol owner others) s)
    (quiet : probeRoot s.system.root.ledger = true) (worker : Tracked)
    (member : worker ∈ s.system.root :: s.system.workers) (action : Action) :
    worker.run action = worker := by
  cases action with
  | register p destination payload =>
    cases found : lookup Record.id p worker.ledger.records with
    | none => simp [Tracked.run, Tracked.register, register_missing worker.ledger p destination payload found]
    | some r =>
      have facts := initialized_protocol_quiet_lookup owner others distinct completed trace quiet worker member p r found
      have rejected := register_closed worker.ledger p destination payload r found facts.2.1
      simp [Tracked.run, Tracked.register, rejected]
  | close id =>
    cases found : lookup Record.id id worker.ledger.records with
    | none => simp [Tracked.run, close, found]
    | some r =>
      have facts := initialized_protocol_quiet_lookup owner others distinct completed trace quiet worker member id r found
      simp [Tracked.run, close, found, facts.2.1]
  | retire id =>
    cases found : lookup Record.id id worker.ledger.records with
    | none => simp [Tracked.run, retire_missing worker.ledger id found]
    | some r =>
      have facts := initialized_protocol_quiet_lookup owner others distinct completed trace quiet worker member id r found
      simp [Tracked.run, facts.1, retire_root]
  | ack p child peer =>
    cases found : lookup Record.id p worker.ledger.records with
    | none => simp [Tracked.run, acknowledge_missing_parent worker.ledger p child peer found]
    | some r =>
      have facts := initialized_protocol_quiet_lookup owner others distinct completed trace quiet worker member p r found
      simp [Tracked.run, acknowledge, found, facts.2.2, lookup]

theorem replacement_same {s t : System} {worker : Tracked}
    (replace : SystemReplace s t worker worker) : t = s := by
  cases replace with
  | root => rfl
  | worker before after old next workers =>
    cases s with
    | mk root ledgers =>
      simp only at workers
      simp [workers]

theorem initialized_protocol_quiet_step_stable (owner : Nat) (others : List Nat)
    (distinct : (owner :: others).Nodup) (completed : Id → Prop) {s t : ProtocolState}
    (trace : ProtocolTrace completed (initialProtocol owner others) s)
    (quiet : probeRoot s.system.root.ledger = true) (step : ProtocolStep completed s t) : t = s := by
  have empty := initialized_protocol_quiet_tokens_empty owner others distinct completed trace quiet
  have flights := quiet_flights_empty s empty
  cases step with
  | register next worker parent destination payload replace =>
    have same := quiet_worker_action_unchanged owner others distinct completed trace quiet worker
      (replace_old_member replace) (.register parent destination payload)
    rw [same] at replace
    have eq := replacement_same replace
    cases s
    simp_all
  | close next worker id replace =>
    have same := quiet_worker_action_unchanged owner others distinct completed trace quiet worker
      (replace_old_member replace) (.close id)
    rw [same] at replace
    have eq := replacement_same replace
    cases s
    simp_all
  | retire next worker id done replace =>
    have same := quiet_worker_action_unchanged owner others distinct completed trace quiet worker
      (replace_old_member replace) (.retire id)
    rw [same] at replace
    have eq := replacement_same replace
    cases s
    simp_all
  | publishWork next worker replace =>
    have outputs := quiet_worker_outputs_empty s empty worker (replace_old_member replace)
    have same : publishWork ⟨worker, s.work⟩ = ⟨worker, s.work⟩ := by
      simp [publishWork, takeOutput, outputs]
    rw [same] at replace
    have eq := replacement_same replace
    cases s
    simp_all
  | deliverWork next worker replace =>
    have same : deliverWork ⟨worker, s.work⟩ = ⟨worker, s.work⟩ := by
      simp [deliverWork, flights.1]
    rw [same] at replace
    have eq := replacement_same replace
    cases s
    simp_all
  | publishAck next worker replace =>
    have outputs := quiet_worker_outputs_empty s empty worker (replace_old_member replace)
    have same : publishAck ⟨worker, s.acks⟩ = ⟨worker, s.acks⟩ := by
      simp [publishAck, takeOutput, outputs]
    rw [same] at replace
    have eq := replacement_same replace
    cases s
    simp_all
  | deliverAck next worker replace =>
    have same : deliverAck ⟨worker, s.acks⟩ = ⟨worker, s.acks⟩ := by
      simp [deliverAck, flights.2]
    rw [same] at replace
    have eq := replacement_same replace
    cases s
    simp_all

/-- Stability is for this finite model and its explicit completion premise. -/
theorem initialized_protocol_quiet_trace_stable (owner : Nat) (others : List Nat)
    (distinct : (owner :: others).Nodup) (completed : Id → Prop) {s t : ProtocolState}
    (prior : ProtocolTrace completed (initialProtocol owner others) s)
    (quiet : probeRoot s.system.root.ledger = true) (suffix : ProtocolTrace completed s t) : t = s := by
  induction suffix with
  | refl => rfl
  | next history step ih =>
    subst_vars
    exact initialized_protocol_quiet_step_stable owner others distinct completed prior quiet step

end Ash.NetworkLedger.Coupling
