/-
Finite local retained-control experiment. The ownership lists model structural
completion owners, not source values or a Rust representation. External
support, interpreter equivalence, and admission are explicit assumptions.
-/
namespace Ash.RetainedControl

inductive CleanupPhase where
  | armed | running | finished
  deriving DecidableEq, Repr

inductive NestedPhase where
  | live | consumed
  deriving DecidableEq, Repr

inductive ClosePhase where
  | idle | armed | running | finished
  deriving DecidableEq, Repr

structure Capture where
  branch : Nat
  owners : List Nat
  outsideSupport : List Nat
  outsideCompletion : List Nat
  exported : List Nat
  interpretation : Nat
  nested : List NestedPhase
  cleanup : CleanupPhase
  savedResult : Nat
  deriving DecidableEq, Repr

inductive SlotPhase where
  | vacant | live (capture : Capture) | spent
  deriving DecidableEq, Repr

structure Slot where
  id : Nat
  generation : Nat
  phase : SlotPhase
  deriving DecidableEq, Repr

structure Key where
  store : Nat
  slot : Nat
  generation : Nat
  deriving DecidableEq, Repr

inductive Answer where
  | suspended (key : Key)
  | finished
  deriving DecidableEq, Repr

inductive ConsumerKind where
  | root | continued
  deriving DecidableEq, Repr

structure Consumer where
  id : Nat
  interpretation : Nat
  kind : ConsumerKind
  deriving DecidableEq, Repr

inductive Delivery where
  | root (answer : Answer)
  | someAnswer (answer : Answer)
  | noCapture
  deriving DecidableEq, Repr

def respond (consumer : Consumer) (answer : Answer) : Nat × Delivery :=
  (consumer.id, match consumer.kind with
    | .root => .root answer
    | .continued => .someAnswer answer)

structure State where
  storeId : Nat
  storeOwner : Nat
  interpretation : Nat
  maxGeneration : Nat
  support : List Nat
  outsideCompletion : List Nat
  clause : Option (Capture × Consumer)
  slots : List Slot
  active : Option (Capture × Consumer)
  completed : List Nat
  disposed : List Nat
  leaked : List Nat
  result : Option (Nat × Delivery)
  adminSuffixClear : Bool
  closePhase : ClosePhase
  closed : Bool
  failed : Bool
  incomplete : Bool
  deriving Repr

/-- Admission is about the actual closure, not the proposed successor state. -/
def Admit (s : State) (c : Capture) : Prop :=
  c.branch ∈ c.owners ∧ s.storeOwner ∉ c.owners ∧ c.interpretation = s.interpretation ∧
  (∀ x, x ∈ c.outsideSupport → x ∈ s.support ∧ x ∉ c.owners) ∧
  (∀ x, x ∈ c.outsideCompletion → x ∈ s.outsideCompletion ∧ x ∉ c.owners) ∧
  (∀ x, x ∈ s.support → x ∉ c.owners) ∧
  (∀ x, x ∈ s.outsideCompletion → x ∉ c.owners) ∧
  (∀ x, x ∈ c.exported → x ∉ c.owners)

def slotOwners (slot : Slot) : List Nat :=
  match slot.phase with
  | .live c => c.owners
  | _ => []

def optionOwners (entry : Option (Capture × Consumer)) : List Nat :=
  match entry with
  | none => []
  | some (c, _) => c.owners

def liveOwners (s : State) : List Nat :=
  optionOwners s.clause ++ s.slots.flatMap slotOwners ++ optionOwners s.active

def allOwners (s : State) : List Nat :=
  liveOwners s ++ s.completed ++ s.disposed ++ s.leaked

/-- Every represented structural owner occurs at most once, including retired owners. -/
def Unique (s : State) : Prop :=
  ∀ owner, ((allOwners s).count owner) ≤ 1

def NoWork (s : State) : Prop := liveOwners s = []

def ReadyToFinish (c : Capture) : Prop :=
  c.cleanup = .finished ∧ ∀ phase, phase ∈ c.nested → phase = .consumed

def RootFresh (s : State) (c : Capture) : Prop :=
  ∀ owner, owner ∈ c.owners → owner ∉ allOwners s

def CaptureUnique (c : Capture) : Prop :=
  ∀ owner, c.owners.count owner ≤ 1

def SlotIdsUnique (s : State) : Prop := (s.slots.map Slot.id).Nodup

def GenerationBounded (s : State) : Prop :=
  ∀ slot, slot ∈ s.slots → slot.generation ≤ s.maxGeneration

def ContextSafe (s : State) : Prop :=
  (∀ c d, s.clause = some (c, d) → Admit s c ∧ d.interpretation = s.interpretation) ∧
  (∀ slot, slot ∈ s.slots → ∀ c, slot.phase = .live c → Admit s c) ∧
  (∀ c d, s.active = some (c, d) → Admit s c ∧ d.interpretation = s.interpretation)

def LiveKey (s : State) (key : Key) : Prop :=
  key.store = s.storeId ∧ ∃ slot c, slot ∈ s.slots ∧ slot.id = key.slot ∧
    slot.generation = key.generation ∧ slot.phase = .live c

/-- A spent key can only meet its spent generation or a later generation. -/
def SpentKey (s : State) (key : Key) : Prop :=
  key.store = s.storeId ∧ ∀ slot, slot ∈ s.slots → slot.id = key.slot →
    key.generation < slot.generation ∨
      (key.generation = slot.generation ∧ slot.phase = .spent)

/-- The local steps move actual payloads; none assumes safety of its successor. -/
inductive Step : State → List Nat → State → Prop where
  | refuse (s : State) : Step s [] s
  | launch (s : State) (c : Capture) (d : Consumer)
      (noClause : s.clause = none) (driver : s.active = none)
      (admission : Admit s c) (fresh : RootFresh s c) (unique : CaptureUnique c)
      (interpretation : d.interpretation = s.interpretation) (kind : d.kind = .root)
      (openStore : s.closed = false) (notFailed : s.failed = false) :
      Step s c.owners { s with active := some (c, d), result := none }
  | retain (s : State) (pre post : List Slot) (old : Slot) (c : Capture) (d : Consumer)
      (clause : s.clause = some (c, d)) (driver : s.active = none)
      (slots : s.slots = pre ++ old :: post) (free : old.phase = .vacant)
      (admission : Admit s c) (administrative : s.adminSuffixClear = true)
      (openStore : s.closed = false) (notFailed : s.failed = false) :
      Step s [] { s with
        clause := none
        slots := pre ++ { old with phase := .live c } :: post
        result := some (respond d (.suspended ⟨s.storeId, old.id, old.generation⟩)) }
  | restore (s : State) (pre post : List Slot) (old : Slot) (c : Capture) (d : Consumer)
      (key : Key)
      (noClause : s.clause = none) (driver : s.active = none)
      (slots : s.slots = pre ++ old :: post) (live : old.phase = .live c)
      (storeMatch : key.store = s.storeId) (slotMatch : key.slot = old.id)
      (generationMatch : key.generation = old.generation)
      (interpretation : c.interpretation = d.interpretation) (kind : d.kind = .continued)
      (openStore : s.closed = false) (notFailed : s.failed = false) :
      Step s [] { s with
        slots := pre ++ { old with phase := .spent } :: post
        active := some (c, d)
        result := none }
  | missing (s : State) (key : Key) (d : Consumer)
      (noClause : s.clause = none) (driver : s.active = none)
      (storeMatch : key.store = s.storeId) (absent : ¬ LiveKey s key)
      (interpretation : d.interpretation = s.interpretation) (kind : d.kind = .continued)
      (openStore : s.closed = false) (notFailed : s.failed = false) :
      Step s [] { s with result := some (d.id, .noCapture) }
  | checkpoint (s : State) (c : Capture) (d : Consumer)
      (active : s.active = some (c, d)) (noClause : s.clause = none)
      (notFailed : s.failed = false) :
      Step s [] { s with active := none, clause := some (c, d) }
  | startCleanup (s : State) (c : Capture) (d : Consumer)
      (active : s.active = some (c, d)) (armed : c.cleanup = .armed)
      (notFailed : s.failed = false) :
      Step s [] { s with active := some ({ c with cleanup := .running }, d) }
  | finishCleanup (s : State) (c : Capture) (d : Consumer)
      (active : s.active = some (c, d)) (running : c.cleanup = .running)
      (notFailed : s.failed = false) :
      Step s [] { s with active := some ({ c with cleanup := .finished }, d) }
  | consumeNested (s : State) (c : Capture) (d : Consumer) (pre post : List NestedPhase)
      (active : s.active = some (c, d)) (nested : c.nested = pre ++ .live :: post)
      (notFailed : s.failed = false) :
      Step s [] { s with active := some ({ c with nested := pre ++ .consumed :: post }, d) }
  | finish (s : State) (c : Capture) (d : Consumer)
      (active : s.active = some (c, d)) (ready : ReadyToFinish c)
      (notFailed : s.failed = false) :
      Step s [] { s with
        active := none
        completed := c.owners ++ s.completed
        result := some (respond d .finished) }
  | recycle (s : State) (pre post : List Slot) (old : Slot)
      (slots : s.slots = pre ++ old :: post) (spent : old.phase = .spent)
      (space : old.generation < s.maxGeneration) (noClause : s.clause = none)
      (driver : s.active = none) (openStore : s.closed = false) (notFailed : s.failed = false) :
      Step s [] { s with slots := pre ++ { old with
        generation := old.generation + 1
        phase := .vacant } :: post }
  | startOuterClose (s : State) (armed : s.closePhase = .armed)
      (noClause : s.clause = none) (driver : s.active = none)
      (openStore : s.closed = false) (notFailed : s.failed = false) :
      Step s [] { s with closePhase := .running }
  | finishOuterClose (s : State) (running : s.closePhase = .running) (empty : NoWork s)
      (notFailed : s.failed = false) : Step s [] { s with closePhase := .finished }
  | release (s : State) (empty : NoWork s)
      (closeReady : s.closePhase = .idle ∨ s.closePhase = .finished)
      (openStore : s.closed = false)
      (notFailed : s.failed = false) :
      Step s [] { s with closed := true }
  | beginFailure (s : State) : Step s [] { s with failed := true }
  | disposeSlot (s : State) (pre post : List Slot) (old : Slot) (c : Capture)
      (failed : s.failed = true) (slots : s.slots = pre ++ old :: post)
      (live : old.phase = .live c) :
      Step s [] { s with
        slots := pre ++ { old with phase := .spent } :: post
        disposed := c.owners ++ s.disposed }
  | disposeClause (s : State) (c : Capture) (d : Consumer)
      (failed : s.failed = true) (clause : s.clause = some (c, d)) :
      Step s [] { s with clause := none, disposed := c.owners ++ s.disposed }
  | disposeActive (s : State) (c : Capture) (d : Consumer)
      (failed : s.failed = true) (active : s.active = some (c, d)) :
      Step s [] { s with active := none, disposed := c.owners ++ s.disposed }
  | finishDisposal (s : State) (failed : s.failed = true) :
      Step s [] { s with
        clause := none
        slots := []
        active := none
        disposed := liveOwners s ++ s.disposed }
  | refuseDisposal (s : State) (failed : s.failed = true) :
      Step s [] { s with
        clause := none
        slots := []
        active := none
        leaked := liveOwners s ++ s.leaked
        incomplete := true }

theorem step_accounting {s t : State} {created : List Nat}
    (step : Step s created t) (owner : Nat) :
    (allOwners t).count owner = (allOwners s).count owner + created.count owner := by
  cases step <;>
    simp_all [allOwners, liveOwners, optionOwners, slotOwners, List.flatMap_append,
      List.count_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem step_preserves_unique {s t : State} {created : List Nat}
    (step : Step s created t) (unique : Unique s) : Unique t := by
  intro owner
  rw [step_accounting step owner]
  cases step with
  | launch c d noClause driver admission fresh localUnique interpretation kind openStore notFailed =>
      by_cases member : owner ∈ c.owners
      · have priorZero : (allOwners s).count owner = 0 :=
          List.count_eq_zero_of_not_mem (fresh owner member)
        simpa [priorZero] using localUnique owner
      · have newZero : c.owners.count owner = 0 := List.count_eq_zero_of_not_mem member
        simpa [newZero] using unique owner
  | refuse => simpa using unique owner
  | retain pre post old c d clause driver slots free admission administrative openStore notFailed =>
      simpa using unique owner
  | restore pre post old c d key noClause driver slots live storeMatch slotMatch generationMatch
      interpretation kind openStore notFailed =>
      simpa using unique owner
  | missing key d noClause driver storeMatch absent interpretation kind openStore notFailed =>
      simpa using unique owner
  | checkpoint c d active noClause notFailed => simpa using unique owner
  | startCleanup c d active armed notFailed => simpa using unique owner
  | finishCleanup c d active running notFailed => simpa using unique owner
  | consumeNested c d pre post active nested notFailed => simpa using unique owner
  | finish c d active ready notFailed => simpa using unique owner
  | recycle pre post old slots spent space noClause driver openStore notFailed =>
      simpa using unique owner
  | startOuterClose armed noClause driver openStore notFailed => simpa using unique owner
  | finishOuterClose running empty notFailed => simpa using unique owner
  | release empty closeReady openStore notFailed => simpa using unique owner
  | beginFailure => simpa using unique owner
  | disposeSlot pre post old c failed slots live => simpa using unique owner
  | disposeClause c d failed clause => simpa using unique owner
  | disposeActive c d failed active => simpa using unique owner
  | finishDisposal failed => simpa using unique owner
  | refuseDisposal failed => simpa using unique owner

theorem step_preserves_slot_ids {s t : State} {created : List Nat}
    (step : Step s created t) (unique : SlotIdsUnique s) : SlotIdsUnique t := by
  cases step <;> simp_all [SlotIdsUnique, List.map_append]

theorem step_preserves_generation_bound {s t : State} {created : List Nat}
    (step : Step s created t) (bounded : GenerationBounded s) : GenerationBounded t := by
  cases step <;> simp_all [GenerationBounded, List.mem_append, List.mem_cons]
  all_goals
    intro slot member
    rcases member with before | same | after
    · exact bounded slot (Or.inl before)
    · subst slot
      have prior := bounded _ (Or.inr (Or.inl rfl))
      simp_all
      all_goals omega
    · exact bounded slot (Or.inr (Or.inr after))

theorem normal_step_preserves_capacity {s t : State} {created : List Nat}
    (step : Step s created t) (before : s.failed = false) (after : t.failed = false) :
    s.slots.length = t.slots.length := by
  cases step <;> simp_all [List.length_append]

inductive Trace : State → State → Prop where
  | refl (s : State) : Trace s s
  | next {s t u : State} {created : List Nat}
      (prior : Trace s t) (step : Step t created u) : Trace s u

theorem trace_preserves_unique {s t : State} (trace : Trace s t) (unique : Unique s) :
    Unique t := by
  induction trace with
  | refl => exact unique
  | next prior step ih => exact step_preserves_unique step ih

theorem trace_preserves_slot_ids {s t : State} (trace : Trace s t) (unique : SlotIdsUnique s) :
    SlotIdsUnique t := by
  induction trace with
  | refl => exact unique
  | next prior step ih => exact step_preserves_slot_ids step ih

theorem trace_preserves_generation_bound {s t : State} (trace : Trace s t)
    (bounded : GenerationBounded s) : GenerationBounded t := by
  induction trace with
  | refl => exact bounded
  | next prior step ih => exact step_preserves_generation_bound step ih

theorem spent_key_is_not_live (s : State) (key : Key) (spent : SpentKey s key) :
    ¬ LiveKey s key := by
  intro live
  rcases live with ⟨_, slot, c, member, sameId, sameGeneration, phase⟩
  rcases spent.2 slot member sameId with newer | ⟨same, wasSpent⟩
  · simp [sameGeneration] at newer
  · rw [phase] at wasSpent
    cases wasSpent

theorem restored_key_spent (s : State) (pre post : List Slot) (old : Slot)
    (c : Capture) (d : Consumer) (key : Key)
    (unique : SlotIdsUnique s) (slots : s.slots = pre ++ old :: post)
    (storeMatch : key.store = s.storeId) (slotMatch : key.slot = old.id)
    (generationMatch : key.generation = old.generation) :
    SpentKey { s with
      slots := pre ++ { old with phase := .spent } :: post
      active := some (c, d)
      result := none } key := by
  have ids : ((pre.map Slot.id) ++ old.id :: (post.map Slot.id)).Nodup := by
    simpa [SlotIdsUnique, slots, List.map_append] using unique
  have noPre : old.id ∉ pre.map Slot.id := by
    intro member
    exact (List.nodup_append.mp ids).2.2 old.id member old.id (by simp) rfl
  have noPost : old.id ∉ post.map Slot.id := by
    exact (List.nodup_cons.mp (List.nodup_append.mp ids).2.1).1
  refine ⟨storeMatch, ?_⟩
  intro candidate member sameId
  simp only [List.mem_append, List.mem_cons] at member
  rcases member with before | same | after
  · apply False.elim
    apply noPre
    apply List.mem_map.mpr
    exact ⟨candidate, before, sameId.trans slotMatch⟩
  · subst candidate
    exact Or.inr ⟨generationMatch, rfl⟩
  · apply False.elim
    apply noPost
    apply List.mem_map.mpr
    exact ⟨candidate, after, sameId.trans slotMatch⟩

theorem step_preserves_spent_key {s t : State} {created : List Nat} (key : Key)
    (step : Step s created t) (spent : SpentKey s key) : SpentKey t key := by
  cases step <;> simp_all [SpentKey, List.mem_append, List.mem_cons]
  all_goals
    intro slot member sameId
    rcases member with before | same | after
    · exact spent.2 slot (Or.inl before) sameId
    · subst slot
      have prior := spent.2 _ (Or.inr (Or.inl rfl)) sameId
      simp_all
      all_goals omega
    · exact spent.2 slot (Or.inr (Or.inr after)) sameId

theorem trace_preserves_spent_key {s t : State} (key : Key) (trace : Trace s t)
    (spent : SpentKey s key) : SpentKey t key := by
  induction trace with
  | refl => exact spent
  | next prior step ih => exact step_preserves_spent_key key step ih

theorem restore_cannot_replay (s : State) (pre post : List Slot) (old : Slot)
    (c : Capture) (d : Consumer) (key : Key) (later : State)
    (unique : SlotIdsUnique s) (slots : s.slots = pre ++ old :: post)
    (storeMatch : key.store = s.storeId) (slotMatch : key.slot = old.id)
    (generationMatch : key.generation = old.generation)
    (trace : Trace { s with
      slots := pre ++ { old with phase := .spent } :: post
      active := some (c, d)
      result := none } later) :
    ¬ LiveKey later key := by
  apply spent_key_is_not_live
  apply trace_preserves_spent_key key trace
  exact restored_key_spent s pre post old c d key unique slots storeMatch slotMatch generationMatch

theorem restore_requires_live_key (s : State) (pre post : List Slot) (old : Slot)
    (c : Capture) (key : Key) (slots : s.slots = pre ++ old :: post)
    (live : old.phase = .live c) (storeMatch : key.store = s.storeId)
    (slotMatch : key.slot = old.id) (generationMatch : key.generation = old.generation) :
    LiveKey s key := by
  refine ⟨storeMatch, old, c, ?_, slotMatch.symm, generationMatch.symm, live⟩
  rw [slots]
  simp

theorem source_release_predecessor {s t : State} {created : List Nat}
    (step : Step s created t) (openStore : s.closed = false) (closed : t.closed = true)
    (notFailed : s.failed = false) : NoWork s := by
  cases step <;> simp_all [NoWork]

theorem actual_finish_requires_completion {s t : State} {created : List Nat}
    (c : Capture) (d : Consumer) (active : s.active = some (c, d))
    (before : s.result = none) (step : Step s created t)
    (returned : t.result = some (respond d .finished)) (inactive : t.active = none) :
    ReadyToFinish c := by
  cases step <;> simp_all [respond]

theorem running_drain_is_not_skipped {s t : State} {created : List Nat}
    (step : Step s created t) (running : s.closePhase = .running) :
    t.closePhase = .running ∨ (t.closePhase = .finished ∧ NoWork s) := by
  cases step <;> simp_all

theorem admission_excludes_self (s : State) (c : Capture) (admitted : Admit s c) :
    s.storeOwner ∉ c.owners := admitted.2.1

theorem admission_keeps_outside_completion (s : State) (c : Capture) (admitted : Admit s c)
    (owner : Nat) (required : owner ∈ c.outsideCompletion) : owner ∈ s.outsideCompletion :=
  (admitted.2.2.2.2.1 owner required).1

theorem admission_rejects_local_escape (s : State) (c : Capture) (admitted : Admit s c)
    (owner : Nat) (exported : owner ∈ c.exported) : owner ∉ c.owners :=
  admitted.2.2.2.2.2.2.2 owner exported

theorem no_work_excludes_clause (s : State) (safe : ContextSafe s) (empty : NoWork s)
    (c : Capture) (d : Consumer) : s.clause ≠ some (c, d) := by
  intro found
  have branch := (safe.1 c d found).1.1
  have member : c.branch ∈ liveOwners s := by
    simp [liveOwners, optionOwners, found, branch]
  rw [empty] at member
  cases member

theorem no_work_excludes_active (s : State) (safe : ContextSafe s) (empty : NoWork s)
    (c : Capture) (d : Consumer) : s.active ≠ some (c, d) := by
  intro found
  have branch := (safe.2.2 c d found).1.1
  have member : c.branch ∈ liveOwners s := by
    simp [liveOwners, optionOwners, found, branch]
  rw [empty] at member
  cases member

theorem no_work_excludes_slot (s : State) (safe : ContextSafe s) (empty : NoWork s)
    (slot : Slot) (member : slot ∈ s.slots) (c : Capture) : slot.phase ≠ .live c := by
  intro live
  have branch := (safe.2.1 slot member c live).1
  have inSlots : c.branch ∈ s.slots.flatMap slotOwners := by
    apply List.mem_flatMap.mpr
    refine ⟨slot, member, ?_⟩
    simpa [slotOwners, live] using branch
  have inWork : c.branch ∈ liveOwners s := by
    simp [liveOwners, inSlots]
  rw [empty] at inWork
  cases inWork

private theorem slots_replace_admissible
    {s : State} (pre post : List Slot) (old replacement : Slot)
    (slots : s.slots = pre ++ old :: post)
    (safe : ∀ slot, slot ∈ s.slots → ∀ c, slot.phase = .live c → Admit s c)
    (middle : ∀ c, replacement.phase = .live c → Admit s c) :
    ∀ slot, slot ∈ pre ++ replacement :: post →
      ∀ c, slot.phase = .live c → Admit s c := by
  intro slot member c live
  simp only [List.mem_append, List.mem_cons] at member
  rcases member with before | same | after
  · exact safe slot (by simp [slots, before]) c live
  · subst slot
    exact middle c live
  · exact safe slot (by simp [slots, after]) c live

private theorem option_admissible {s : State} {c : Capture} {d : Consumer}
    (admitted : Admit s c) (interpretation : d.interpretation = s.interpretation) :
    ∀ x y, some (c, d) = some (x, y) →
      Admit s x ∧ y.interpretation = s.interpretation := by
  intro x y eq
  have pair := Option.some.inj eq
  have sameCapture : c = x := congrArg Prod.fst pair
  have sameConsumer : d = y := congrArg Prod.snd pair
  subst x
  subst y
  exact ⟨admitted, interpretation⟩

theorem step_preserves_context {s t : State} {created : List Nat}
    (step : Step s created t) (safe : ContextSafe s) : ContextSafe t := by
  rcases safe with ⟨clauseSafe, slotsSafe, activeSafe⟩
  cases step with
  | refuse =>
      exact ⟨clauseSafe, slotsSafe, activeSafe⟩
  | launch c d noClause driver admission fresh localUnique interpretation kind openStore notFailed =>
      exact ⟨clauseSafe, slotsSafe, option_admissible admission interpretation⟩
  | retain pre post old c d clause driver slots free admission administrative openStore notFailed =>
      refine ⟨?_, ?_, activeSafe⟩
      · intro x y impossible
        cases impossible
      · apply slots_replace_admissible pre post old { old with phase := .live c } slots slotsSafe
        intro x live
        have same : c = x := by simpa using live
        subst x
        exact admission
  | restore pre post old c d key noClause driver slots live storeMatch slotMatch generationMatch
      interpretation kind openStore notFailed =>
      have member : old ∈ s.slots := by simp [slots]
      have admitted : Admit s c := slotsSafe old member c live
      have consumerSafe : d.interpretation = s.interpretation :=
        interpretation.symm.trans admitted.2.2.1
      refine ⟨clauseSafe, ?_, option_admissible admitted consumerSafe⟩
      apply slots_replace_admissible pre post old { old with phase := .spent } slots slotsSafe
      intro x impossible
      cases impossible
  | missing key d noClause driver storeMatch absent interpretation kind openStore notFailed =>
      exact ⟨clauseSafe, slotsSafe, activeSafe⟩
  | checkpoint c d active noClause notFailed =>
      have prior := activeSafe c d active
      refine ⟨option_admissible prior.1 prior.2, slotsSafe, ?_⟩
      intro x y impossible
      cases impossible
  | startCleanup c d active armed notFailed =>
      have prior := activeSafe c d active
      have updated : Admit s { c with cleanup := .running } := by
        change Admit s c
        exact prior.1
      exact ⟨clauseSafe, slotsSafe, option_admissible updated prior.2⟩
  | finishCleanup c d active running notFailed =>
      have prior := activeSafe c d active
      have updated : Admit s { c with cleanup := .finished } := by
        change Admit s c
        exact prior.1
      exact ⟨clauseSafe, slotsSafe, option_admissible updated prior.2⟩
  | consumeNested c d pre post active nested notFailed =>
      have prior := activeSafe c d active
      have updated : Admit s { c with nested := pre ++ .consumed :: post } := by
        change Admit s c
        exact prior.1
      exact ⟨clauseSafe, slotsSafe, option_admissible updated prior.2⟩
  | finish c d active ready notFailed =>
      refine ⟨clauseSafe, slotsSafe, ?_⟩
      intro x y impossible
      cases impossible
  | recycle pre post old slots spent space noClause driver openStore notFailed =>
      refine ⟨clauseSafe, ?_, activeSafe⟩
      apply slots_replace_admissible pre post old
        { old with generation := old.generation + 1, phase := .vacant } slots slotsSafe
      intro x impossible
      cases impossible
  | startOuterClose armed noClause driver openStore notFailed =>
      exact ⟨clauseSafe, slotsSafe, activeSafe⟩
  | finishOuterClose running empty notFailed =>
      exact ⟨clauseSafe, slotsSafe, activeSafe⟩
  | release empty closeReady openStore notFailed =>
      exact ⟨clauseSafe, slotsSafe, activeSafe⟩
  | beginFailure =>
      exact ⟨clauseSafe, slotsSafe, activeSafe⟩
  | disposeSlot pre post old c failed slots live =>
      refine ⟨clauseSafe, ?_, activeSafe⟩
      apply slots_replace_admissible pre post old { old with phase := .spent } slots slotsSafe
      intro x impossible
      cases impossible
  | disposeClause c d failed clause =>
      refine ⟨?_, slotsSafe, activeSafe⟩
      intro x y impossible
      cases impossible
  | disposeActive c d failed active =>
      refine ⟨clauseSafe, slotsSafe, ?_⟩
      intro x y impossible
      cases impossible
  | finishDisposal failed =>
      refine ⟨?_, ?_, ?_⟩
      · intro x y impossible
        cases impossible
      · intro slot member
        simp at member
      · intro x y impossible
        cases impossible
  | refuseDisposal failed =>
      refine ⟨?_, ?_, ?_⟩
      · intro x y impossible
        cases impossible
      · intro slot member
        simp at member
      · intro x y impossible
        cases impossible

theorem trace_preserves_context {s t : State} (trace : Trace s t) (safe : ContextSafe s) :
    ContextSafe t := by
  induction trace with
  | refl => exact safe
  | next prior step ih => exact step_preserves_context step ih

end Ash.RetainedControl

#print axioms Ash.RetainedControl.step_accounting
#print axioms Ash.RetainedControl.step_preserves_unique
#print axioms Ash.RetainedControl.trace_preserves_unique
#print axioms Ash.RetainedControl.trace_preserves_slot_ids
#print axioms Ash.RetainedControl.trace_preserves_generation_bound
#print axioms Ash.RetainedControl.normal_step_preserves_capacity
#print axioms Ash.RetainedControl.restore_cannot_replay
#print axioms Ash.RetainedControl.restore_requires_live_key
#print axioms Ash.RetainedControl.source_release_predecessor
#print axioms Ash.RetainedControl.actual_finish_requires_completion
#print axioms Ash.RetainedControl.running_drain_is_not_skipped
#print axioms Ash.RetainedControl.no_work_excludes_clause
#print axioms Ash.RetainedControl.no_work_excludes_active
#print axioms Ash.RetainedControl.no_work_excludes_slot
#print axioms Ash.RetainedControl.admission_excludes_self
#print axioms Ash.RetainedControl.admission_keeps_outside_completion
#print axioms Ash.RetainedControl.admission_rejects_local_escape
#print axioms Ash.RetainedControl.trace_preserves_context
