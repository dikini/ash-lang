import RegionModel

/-
Finite views and owned completion refine the construction kernel. Layout tables
stand for validated typed field metadata, not a source-forgeable capability.
The module contract supplies physical storage; no native-memory theorem is claimed.
-/
namespace Ash.Regions

variable {nr no nt : Nat}

/-- Whole values use graph reachability; inline views keep the container residency. -/
structure View (no : Nat) where
  object : Fin no
  inlinePart : Option Nat := none
  deriving DecidableEq

abbrev Layout (nr no : Nat) := Fin no → List (List (Fin nr))

def ViewSafe (layout : Layout nr no) (s : State nr no nt) (v : View no) : Prop :=
  ∃ o, s.objects v.object = some o ∧ Ready o ∧ Live s o.region ∧
    match v.inlinePart with
    | none => s.exposed v.object = true
    | some part => s.publishedOnce v.object = true ∧
      ∃ deps, (layout v.object)[part]? = some deps ∧ DependenciesLive s deps

def RootsSafe (layout : Layout nr no) (s : State nr no nt)
    (roots : Fin no → Option (View no)) : Prop :=
  ∀ i v, roots i = some v → ViewSafe layout s v

/-- Updating a private object cannot change an already usable view of that slot. -/
theorem view_private_update (layout : Layout nr no) (s next : State nr no nt)
    (regions : next.regions = s.regions)
    (flags : ∀ i, s.exposed i = true → next.exposed i = true)
    (history : ∀ i, s.publishedOnce i = true → next.publishedOnce i = true)
    (unchanged : ∀ i o, s.objects i = some o → Ready o → next.objects i = some o)
    (v : View no) (safe : ViewSafe layout s v) : ViewSafe layout next v := by
  rcases safe with ⟨o, found, ready, resident, part⟩
  refine ⟨o, unchanged v.object o found ready, ready, ?_, ?_⟩
  · simpa [Live, regions] using resident
  · cases kind : v.inlinePart with
    | none => exact flags v.object (by simpa [kind] using part)
    | some p =>
      have old : s.publishedOnce v.object = true ∧
          ∃ deps, (layout v.object)[p]? = some deps ∧ DependenciesLive s deps := by
        simpa [kind] using part
      exact ⟨history v.object old.1, by simpa [DependenciesLive, Live, regions] using old.2⟩

theorem view_reserve (layout : Layout nr no) (s : State nr no nt)
    (i : Fin no) (r : Fin nr) (fresh : s.objects i = none)
    (v : View no) (safe : ViewSafe layout s v) : ViewSafe layout (reserve s i r) v := by
  apply view_private_update layout s (reserve s i r) rfl (fun _ h => h) (fun _ h => h) _ v safe
  intro j o found _
  have different : j ≠ i := by intro eq; subst j; simp [fresh] at found
  simpa [reserve, replace, different] using found

theorem view_initialize (layout : Layout nr no) (s : State nr no nt)
    (i : Fin no) (o : Object nr no) (deps : List (Fin nr)) (fields : List (Fin no))
    (found : s.objects i = some o) (pending : o.phase = .pending)
    (v : View no) (safe : ViewSafe layout s v) :
    ViewSafe layout (initializeSlot s i o deps fields) v := by
  apply view_private_update layout s (initializeSlot s i o deps fields) rfl (fun _ h => h) (fun _ h => h) _ v safe
  intro j old atSlot ready
  have different : j ≠ i := by
    intro eq
    subst j
    have same : old = o := Option.some.inj (atSlot.symm.trans found)
    subst old
    simp [Ready, pending] at ready
  simpa [initializeSlot, replace, different] using atSlot

def NoWholeRoots (roots : Fin no → Option (View no)) (group : List (Fin no)) : Prop :=
  ∀ i v, roots i = some v → v.inlinePart = none → v.object ∉ group

theorem view_drop (layout : Layout nr no) (s : State nr no nt)
    (group : List (Fin no)) (v : View no) (safe : ViewSafe layout s v)
    (whole : v.inlinePart = none → v.object ∉ group) :
    ViewSafe layout (dropAccess s group) v := by
  rcases safe with ⟨o, found, ready, resident, part⟩
  refine ⟨o, found, ready, resident, ?_⟩
  cases kind : v.inlinePart with
  | none => simpa [dropAccess, whole kind, kind] using part
  | some p => simpa [kind, DependenciesLive, Live, dropAccess] using part

def ViewAvoids (layout : Layout nr no) (s : State nr no nt)
    (r : Fin nr) (v : View no) : Prop :=
  ∀ o, s.objects v.object = some o → o.region ≠ r ∧
    ∀ p deps, v.inlinePart = some p → (layout v.object)[p]? = some deps → r ∉ deps

theorem view_close (layout : Layout nr no) (s : State nr no nt)
    (r : Fin nr) (info : Region nr) (v : View no) (safe : ViewSafe layout s v)
    (avoids : ViewAvoids layout s r v) : ViewSafe layout (closeRegion s r info) v := by
  rcases safe with ⟨o, found, ready, resident, part⟩
  have localFacts := avoids o found
  refine ⟨o, by simp [closeRegion, found, localFacts.1], ready,
    close_keeps_other_live s r o.region info localFacts.1 resident, ?_⟩
  cases kind : v.inlinePart with
  | none =>
    have visible : s.exposed v.object = true := by simpa [kind] using part
    simp [closeRegion, found, localFacts.1, visible]
  | some p =>
    rcases (show s.publishedOnce v.object = true ∧
        ∃ deps, (layout v.object)[p]? = some deps ∧ DependenciesLive s deps
      from by simpa [kind] using part) with ⟨published, deps, actual, live⟩
    refine ⟨published, deps, actual, ?_⟩
    intro q member
    have different : q ≠ r := fun eq => localFacts.2 p deps kind actual (eq ▸ member)
    exact close_keeps_other_live s r q info different (live q member)

/-- Projections cannot turn an inline port back into a whole callable value. -/
def WholeView (i : Fin no) : View no := ⟨i, none⟩

theorem whole_view_safe (layout : Layout nr no) (s : State nr no nt)
    (valid : Valid s) (publicGraph : PublicationSafe s) (i : Fin no)
    (visible : s.exposed i = true) : ViewSafe layout s (WholeView i) := by
  rcases publicGraph i visible with ⟨o, found, ready, _⟩
  exact ⟨o, found, ready, valid.1 i o found (by rcases ready with h | h <;> simp [h]), visible⟩

theorem inline_view_safe (layout : Layout nr no) (s : State nr no nt)
    (v : View no) (source : ViewSafe layout s v) (part : Nat) (deps : List (Fin nr))
    (actual : (layout v.object)[part]? = some deps) (live : DependenciesLive s deps)
    (published : s.publishedOnce v.object = true) :
    ViewSafe layout s ⟨v.object, some part⟩ := by
  rcases source with ⟨o, found, ready, resident, _⟩
  exact ⟨o, found, ready, resident, published, deps, actual, live⟩

/-- Roots name usable aliases; removing a root neither moves nor releases its backing. -/
def setRoot (roots : Fin no → Option (View no)) (i : Fin no) (v : Option (View no)) :=
  replace roots i v

theorem set_root_safe (layout : Layout nr no) (s : State nr no nt)
    (roots : Fin no → Option (View no)) (i : Fin no) (v : View no)
    (safe : RootsSafe layout s roots) (admitted : ViewSafe layout s v) :
    RootsSafe layout s (setRoot roots i (some v)) := by
  intro j candidate found
  by_cases same : j = i
  · subst j
    simp [setRoot, replace] at found
    subst candidate
    exact admitted
  · exact safe j candidate (by simpa [setRoot, replace, same] using found)

theorem drop_root_safe (layout : Layout nr no) (s : State nr no nt)
    (roots : Fin no → Option (View no)) (i : Fin no)
    (safe : RootsSafe layout s roots) : RootsSafe layout s (setRoot roots i none) := by
  intro j v found
  by_cases same : j = i
  · subst j; simp [setRoot, replace] at found
  · exact safe j v (by simpa [setRoot, replace, same] using found)


inductive ReleasePhase where
  | waiting | running | returned
  deriving DecidableEq

/-- The cursor retains the exact action order and the fixed release association. -/
structure CloseCursor (nr : Nat) where
  owner : Fin nr
  association : Association
  initial : List Nat
  completed : List Nat := []
  action : Option Nat := none
  remaining : List Nat
  release : ReleasePhase := .waiting
  deriving DecidableEq

def CursorOrdered (c : CloseCursor nr) : Prop :=
  c.initial = c.completed ++ c.action.toList ++ c.remaining ∧
  (c.release ≠ .waiting → c.action = none ∧ c.remaining = [])

def startAction (c : CloseCursor nr) (a : Nat) (rest : List Nat) : CloseCursor nr :=
  { c with action := some a, remaining := rest }

def finishAction (c : CloseCursor nr) (a : Nat) : CloseCursor nr :=
  { c with action := none, completed := c.completed ++ [a] }

def startRelease (c : CloseCursor nr) : CloseCursor nr := { c with release := .running }
def returnRelease (c : CloseCursor nr) : CloseCursor nr := { c with release := .returned }

theorem start_action_ordered (c : CloseCursor nr) (a : Nat) (rest : List Nat)
    (ordered : CursorOrdered c) (idle : c.action = none) (head : c.remaining = a :: rest)
    (notReleased : c.release = .waiting) : CursorOrdered (startAction c a rest) := by
  refine ⟨?_, ?_⟩
  · simpa [startAction, idle, head, List.append_assoc] using ordered.1
  · intro impossible
    exact False.elim (impossible notReleased)

theorem finish_action_ordered (c : CloseCursor nr) (a : Nat)
    (ordered : CursorOrdered c) (running : c.action = some a) :
    CursorOrdered (finishAction c a) := by
  refine ⟨?_, ?_⟩
  · simpa [finishAction, running, List.append_assoc] using ordered.1
  · intro released
    have absent := (ordered.2 released).1
    simp [running] at absent

theorem start_release_ordered (c : CloseCursor nr) (ordered : CursorOrdered c)
    (idle : c.action = none) (empty : c.remaining = []) :
    CursorOrdered (startRelease c) := by
  exact ⟨ordered.1, fun _ => ⟨idle, empty⟩⟩

theorem return_release_ordered (c : CloseCursor nr) (ordered : CursorOrdered c)
    (running : c.release = .running) : CursorOrdered (returnRelease c) := by
  exact ⟨ordered.1, fun _ => ordered.2 (by simp [running])⟩

inductive CleanupStep : CloseCursor nr → CloseCursor nr → Prop where
  | start (c : CloseCursor nr) (a : Nat) (rest : List Nat)
      (idle : c.action = none) (head : c.remaining = a :: rest)
      (notReleased : c.release = .waiting) : CleanupStep c (startAction c a rest)
  | finish (c : CloseCursor nr) (a : Nat) (running : c.action = some a) :
      CleanupStep c (finishAction c a)
  | release (c : CloseCursor nr) (idle : c.action = none) (empty : c.remaining = [])
      (notReleased : c.release = .waiting) : CleanupStep c (startRelease c)
  | returned (c : CloseCursor nr) (running : c.release = .running) :
      CleanupStep c (returnRelease c)

theorem cleanup_step_preserves (c next : CloseCursor nr) (ordered : CursorOrdered c)
    (step : CleanupStep c next) : CursorOrdered next := by
  cases step with
  | start a rest idle head waiting => exact start_action_ordered c a rest ordered idle head waiting
  | finish a running => exact finish_action_ordered c a ordered running
  | release idle empty _ => exact start_release_ordered c ordered idle empty
  | returned running => exact return_release_ordered c ordered running

theorem cleanup_keeps_pair (c next : CloseCursor nr) (step : CleanupStep c next) :
    next.owner = c.owner ∧ next.association = c.association := by
  cases step <;> exact ⟨rfl, rfl⟩

def CursorComplete (c : CloseCursor nr) : Prop :=
  c.action = none ∧ c.remaining = [] ∧ c.release = .returned

theorem complete_cleanup_has_run_every_action (c : CloseCursor nr)
    (ordered : CursorOrdered c) (complete : CursorComplete c) :
    c.initial = c.completed := by
  simpa [complete.1, complete.2.1] using ordered.1

/-- A cursor is moved with its owner, never copied or abandoned by discard. -/
def CursorSafe (s : State nr no nt) (c : CloseCursor nr) : Prop :=
  CursorOrdered c ∧ ∃ info, s.regions c.owner = some info ∧ info.phase = .live ∧
    c.association = info.association

def OwnersLive (s : State nr no nt) : Prop := ∀ r, Owns s r → Live s r

def ParentsLive (s : State nr no nt) : Prop :=
  ∀ r info parent, s.regions r = some info →
    (info.phase = .preparing ∨ info.phase = .live) → info.parent = some parent → Live s parent

theorem capture_keeps_live_owners (s : State nr no nt) (t : Fin nt)
    (inside outside : List (Fin nr)) (handler : Option (Fin nr)) (cut : Nat)
    (live : OwnersLive s) (fresh : s.tickets t = none)
    (split : s.completionOrder = inside ++ outside) :
    OwnersLive (capture s t inside outside handler cut) := by
  intro r owned
  exact live r ((capture_conserves_owners s t inside outside handler cut fresh split r).mp owned)

theorem resume_keeps_live_owners (s : State nr no nt) (t : Fin nt)
    (c : Captured nr no) (live : OwnersLive s) (ticket : s.tickets t = some c) :
    OwnersLive (resume s t c) := by
  intro r owned
  exact live r ((resume_conserves_owners s t c ticket r).mp owned)

def NoLiveChild (s : State nr no nt) (r : Fin nr) : Prop :=
  ∀ q info, s.regions q = some info →
    (info.phase = .preparing ∨ info.phase = .live) → info.parent ≠ some r

theorem close_preserves_parents (s : State nr no nt) (r : Fin nr) (info : Region nr)
    (safe : ParentsLive s) (children : NoLiveChild s r) :
    ParentsLive (closeRegion s r info) := by
  intro q child parent found live enclosing
  have different : q ≠ r := by
    intro eq
    subst q
    simp [closeRegion, replace] at found
    subst child
    simp at live
  have old : s.regions q = some child := by simpa [closeRegion, replace, different] using found
  have parentOther : parent ≠ r := fun eq => children q child old live (eq ▸ enclosing)
  exact close_keeps_other_live s r parent info parentOther (safe q child parent old live enclosing)

theorem finish_close_keeps_live_owners (s : State nr no nt) (r : Fin nr) (info : Region nr)
    (rest : List (Fin nr)) (unique : OwnersUnique s) (live : OwnersLive s)
    (top : s.completionOrder = r :: rest) :
    OwnersLive (finishClose s r info rest) := by
  intro q owned
  have old : Owns s q := by
    rcases owned with active | saved
    · exact Or.inl (top ▸ List.mem_cons_of_mem r active)
    · exact Or.inr saved
  have different : q ≠ r := by
    intro eq
    subst q
    rcases owned with active | ⟨t, c, found, member⟩
    · exact (List.nodup_cons.mp (top ▸ unique.1)).1 active
    · exact (unique.2 t c found).2.1 r member (top ▸ List.mem_cons_self)
  exact close_keeps_other_live s r q info different (live q old)


/-- Cursor records remain keyed by their unique owner while its segment is captured. -/
structure Machine (nr no nt : Nat) where
  heap : State nr no nt
  roots : Fin no → Option (View no) := fun _ => none
  closing : Fin nr → Option (CloseCursor nr) := fun _ => none

/-- Backing under an in-flight release is unavailable to source operations. -/
def OwnerAvailable (m : Machine nr no nt) (r : Fin nr) : Prop :=
  ∀ c, m.closing r = some c → c.release ≠ .running

def ViewAvailable (layout : Layout nr no) (m : Machine nr no nt) (v : View no) : Prop :=
  ∀ o, m.heap.objects v.object = some o → OwnerAvailable m o.region ∧
    match v.inlinePart with
    | none => ∀ r, r ∈ o.required → OwnerAvailable m r
    | some part => ∀ deps, (layout v.object)[part]? = some deps →
        ∀ r, r ∈ deps → OwnerAvailable m r

/-- Bind either a still-available whole value or an exact previously retained view. -/
def ViewOrigin (m : Machine nr no nt) (v : View no) : Prop :=
  m.heap.exposed v.object = true ∨ ∃ slot, m.roots slot = some v

def ClosingSafe (m : Machine nr no nt) : Prop :=
  ∀ r c, m.closing r = some c → c.owner = r ∧ CursorSafe m.heap c ∧ Owns m.heap r

/-- The complete finite safety predicate separates physical storage from usable roots. -/
def MachineSafe (layout : Layout nr no) (m : Machine nr no nt) : Prop :=
  Invariant m.heap ∧ RootsSafe layout m.heap m.roots ∧ OwnersLive m.heap ∧
    ParentsLive m.heap ∧ ClosingSafe m

def RootAdmission (roots : Fin no → Option (View no)) (s next : State nr no nt) : Prop :=
  ∀ k v, roots k = some v → v.inlinePart = none → s.exposed v.object = true →
    next.exposed v.object = true

theorem construction_preserves_roots (layout : Layout nr no) (s next : State nr no nt)
    (roots : Fin no → Option (View no)) (safe : RootsSafe layout s roots)
    (step : ConstructionStep s next) (admitted : RootAdmission roots s next) :
    RootsSafe layout next roots := by
  intro k v found
  have old := safe k v found
  cases step with
  | request i request owner _ _ _ _ _ _ _ => exact old
  | supply i request reply continuation _ _ _ _ fresh _ =>
      exact view_reserve layout s i request.owner fresh v old
  | initializeSlot i o deps fields found pending _ _ =>
      exact view_initialize layout s i o deps fields found pending v old
  | publish group _ =>
      apply view_private_update layout s (publishGroup s group) rfl
        (fun i visible => by simp [publishGroup, visible])
        (fun i published => by simp [publishGroup, published]) (fun _ _ h _ => h) v old
  | drop group _ =>
      apply view_drop layout s group v old
      intro whole member
      have visible : s.exposed v.object = true := by
        rcases old with ⟨o, objectFound, ready, resident, part⟩
        simpa [whole] using part
      have retained := admitted k v found whole visible
      simp [dropAccess, member] at retained

theorem construction_preserves_machine (layout : Layout nr no) (m : Machine nr no nt)
    (next : State nr no nt) (safe : MachineSafe layout m)
    (step : ConstructionStep m.heap next) (admitted : RootAdmission m.roots m.heap next) :
    MachineSafe layout { m with heap := next } := by
  rcases safe with ⟨kernel, roots, live, parents, closing⟩
  refine ⟨construction_step_preserves m.heap next kernel step,
    construction_preserves_roots layout m.heap next m.roots roots step admitted, ?_, ?_, ?_⟩
  · cases step <;> exact live
  · cases step <;> exact parents
  · intro r c found
    have old := closing r c found
    cases step <;> exact old

/-- Alias creation duplicates a view, never a physical allocation or completion owner. -/
def bindView (m : Machine nr no nt) (slot : Fin no) (view : View no) : Machine nr no nt :=
  { m with roots := setRoot m.roots slot (some view) }

def unbindView (m : Machine nr no nt) (slot : Fin no) : Machine nr no nt :=
  { m with roots := setRoot m.roots slot none }

theorem bind_view_preserves (layout : Layout nr no) (m : Machine nr no nt)
    (slot : Fin no) (view : View no) (safe : MachineSafe layout m)
    (localView : ViewSafe layout m.heap view) : MachineSafe layout (bindView m slot view) := by
  exact ⟨safe.1, set_root_safe layout m.heap m.roots slot view safe.2.1 localView,
    safe.2.2.1, safe.2.2.2.1, safe.2.2.2.2⟩

theorem unbind_view_preserves (layout : Layout nr no) (m : Machine nr no nt)
    (slot : Fin no) (safe : MachineSafe layout m) : MachineSafe layout (unbindView m slot) := by
  exact ⟨safe.1, drop_root_safe layout m.heap m.roots slot safe.2.1,
    safe.2.2.1, safe.2.2.2.1, safe.2.2.2.2⟩

def beginClose (m : Machine nr no nt) (r : Fin nr) (info : Region nr)
    (actions : List Nat) : Machine nr no nt :=
  let cursor : CloseCursor nr :=
    { owner := r, association := info.association, initial := actions, remaining := actions }
  { m with closing := replace m.closing r (some cursor) }

theorem begin_close_preserves (layout : Layout nr no) (m : Machine nr no nt)
    (r : Fin nr) (info : Region nr) (rest : List (Fin nr)) (actions : List Nat)
    (safe : MachineSafe layout m) (found : m.heap.regions r = some info)
    (live : info.phase = .live) (top : m.heap.completionOrder = r :: rest) :
    MachineSafe layout (beginClose m r info actions) := by
  refine ⟨safe.1, safe.2.1, safe.2.2.1, safe.2.2.2.1, ?_⟩
  intro q c atSlot
  by_cases same : q = r
  · subst q
    simp [beginClose, replace] at atSlot
    subst c
    exact ⟨rfl, ⟨⟨by simp, by simp⟩, info, found, live, rfl⟩,
      Or.inl (top ▸ List.mem_cons_self)⟩
  · exact safe.2.2.2.2 q c (by simpa [beginClose, replace, same] using atSlot)

def advanceCleanup (m : Machine nr no nt) (r : Fin nr) (next : CloseCursor nr) :
    Machine nr no nt := { m with closing := replace m.closing r (some next) }

theorem advance_cleanup_preserves (layout : Layout nr no) (m : Machine nr no nt)
    (r : Fin nr) (c next : CloseCursor nr) (safe : MachineSafe layout m)
    (found : m.closing r = some c) (step : CleanupStep c next) :
    MachineSafe layout (advanceCleanup m r next) := by
  have old := safe.2.2.2.2 r c found
  have pair := cleanup_keeps_pair c next step
  refine ⟨safe.1, safe.2.1, safe.2.2.1, safe.2.2.2.1, ?_⟩
  intro q cursor atSlot
  by_cases same : q = r
  · subst q
    simp [advanceCleanup, replace] at atSlot
    subst cursor
    rcases old.2.1 with ⟨ordered, info, ownerFound, live, association⟩
    exact ⟨pair.1.trans old.1,
      ⟨cleanup_step_preserves c next ordered step, info,
        by simpa [advanceCleanup, pair.1] using ownerFound, live, pair.2.trans association⟩, old.2.2⟩
  · exact safe.2.2.2.2 q cursor (by simpa [advanceCleanup, replace, same] using atSlot)

/-- Active stepping requires the owner in this segment; captured cursors cannot be stepped. -/
def ActiveCursor (m : Machine nr no nt) (r : Fin nr) : Prop :=
  r ∈ m.heap.completionOrder


def captureMachine (m : Machine nr no nt) (t : Fin nt)
    (inside outside : List (Fin nr)) (handler : Option (Fin nr)) (cut : Nat) :
    Machine nr no nt := { m with heap := capture m.heap t inside outside handler cut }

def resumeMachine (m : Machine nr no nt) (t : Fin nt) (c : Captured nr no) :
    Machine nr no nt := { m with heap := resume m.heap t c }

theorem capture_machine_preserves (layout : Layout nr no) (m : Machine nr no nt)
    (t : Fin nt) (inside outside : List (Fin nr)) (handler : Option (Fin nr)) (cut : Nat)
    (safe : MachineSafe layout m) (fresh : m.heap.tickets t = none)
    (split : m.heap.completionOrder = inside ++ outside)
    (handlerLive : OptionLive m.heap handler) :
    MachineSafe layout (captureMachine m t inside outside handler cut) := by
  refine ⟨capture_preserves_invariant m.heap t inside outside handler cut safe.1 fresh split handlerLive,
    safe.2.1, capture_keeps_live_owners m.heap t inside outside handler cut safe.2.2.1 fresh split,
    safe.2.2.2.1, ?_⟩
  intro r c found
  have old := safe.2.2.2.2 r c found
  exact ⟨old.1, old.2.1,
    (capture_conserves_owners m.heap t inside outside handler cut fresh split r).mpr old.2.2⟩

theorem resume_machine_preserves (layout : Layout nr no) (m : Machine nr no nt)
    (t : Fin nt) (c : Captured nr no) (safe : MachineSafe layout m)
    (ticket : m.heap.tickets t = some c) : MachineSafe layout (resumeMachine m t c) := by
  refine ⟨resume_preserves_invariant m.heap t c safe.1 ticket, safe.2.1,
    resume_keeps_live_owners m.heap t c safe.2.2.1 ticket, safe.2.2.2.1, ?_⟩
  intro r cursor found
  have old := safe.2.2.2.2 r cursor found
  exact ⟨old.1, old.2.1, (resume_conserves_owners m.heap t c ticket r).mpr old.2.2⟩

/-- Discard schedules the captured owners for ordinary close, preserving the outside clause. -/
def discardSegment (s : State nr no nt) (t : Fin nt) (c : Captured nr no) : State nr no nt :=
  { s with completionOrder := c.completionOrder ++ s.completionOrder,
           tickets := replace s.tickets t none }

def discardMachine (m : Machine nr no nt) (t : Fin nt) (c : Captured nr no) :
    Machine nr no nt := { m with heap := discardSegment m.heap t c }

def DiscardAllowed (m : Machine nr no nt) (c : Captured nr no) : Prop :=
  (∀ r, r ∈ c.completionOrder → m.closing r = none) ∧
  ∀ p, c.pending = some p → m.heap.objects p.object = none

theorem discard_machine_preserves (layout : Layout nr no) (m : Machine nr no nt)
    (t : Fin nt) (c : Captured nr no) (safe : MachineSafe layout m)
    (ticket : m.heap.tickets t = some c) : MachineSafe layout (discardMachine m t c) := by
  have unique := resume_preserves_ownership m.heap t c safe.1.2.2.2.1 ticket
  have owners := resume_keeps_live_owners m.heap t c safe.2.2.1 ticket
  have oldContexts := safe.1.2.2.2.2
  have saved : SavedContextsSafe (discardSegment m.heap t c) := by
    refine ⟨oldContexts.1, oldContexts.2.1, ?_, oldContexts.2.2.2⟩
    intro u d found
    have different : u ≠ t := by intro same; subst u; simp [discardSegment, replace] at found
    exact oldContexts.2.2.1 u d (by simpa [discardSegment, replace, different] using found)
  refine ⟨⟨safe.1.1, safe.1.2.1, safe.1.2.2.1, unique, saved⟩,
    safe.2.1, owners, safe.2.2.2.1, ?_⟩
  intro r cursor found
  have old := safe.2.2.2.2 r cursor found
  exact ⟨old.1, old.2.1, (resume_conserves_owners m.heap t c ticket r).mpr old.2.2⟩

/-- Finishing a region consumes its cursor and one completion owner, not data edges. -/
def completeMachineClose (m : Machine nr no nt) (r : Fin nr) (info : Region nr)
    (rest : List (Fin nr)) : Machine nr no nt :=
  { m with heap := finishClose m.heap r info rest, closing := replace m.closing r none }

theorem complete_machine_close_preserves (layout : Layout nr no) (m : Machine nr no nt)
    (r : Fin nr) (info : Region nr) (rest : List (Fin nr)) (safe : MachineSafe layout m)
    (region : m.heap.regions r = some info) (top : m.heap.completionOrder = r :: rest)
    (contexts : NoClosingContext m.heap r)
    (uses : NoOutsideUsableDependency m.heap r) (children : NoLiveChild m.heap r)
    (views : ∀ i v, m.roots i = some v → ViewAvoids layout m.heap r v) :
    MachineSafe layout (completeMachineClose m r info rest) := by
  refine ⟨finish_close_preserves m.heap r info rest safe.1 region top contexts uses, ?_,
    finish_close_keeps_live_owners m.heap r info rest safe.1.2.2.2.1 safe.2.2.1 top,
    close_preserves_parents m.heap r info safe.2.2.2.1 children, ?_⟩
  · intro i v found
    exact view_close layout m.heap r info v (safe.2.1 i v found) (views i v found)
  · intro q c found
    have different : q ≠ r := by intro same; subst q; simp [completeMachineClose, replace] at found
    have oldFound : m.closing q = some c := by
      simpa [completeMachineClose, replace, different] using found
    rcases safe.2.2.2.2 q c oldFound with ⟨owner, cursorSafe, owned⟩
    rcases cursorSafe with ⟨ordered, provider, atOwner, live, pair⟩
    have providerOther : c.owner ≠ r := by simpa [owner] using different
    have stillOwned : Owns (finishClose m.heap r info rest) q := by
      rcases owned with active | captured
      · have membership : q ∈ r :: rest := top ▸ active
        rcases List.mem_cons.mp membership with same | member
        · exact False.elim (different same)
        · exact Or.inl member
      · exact Or.inr captured
    exact ⟨owner, ⟨ordered, provider,
      by simpa [completeMachineClose, finishClose, closeRegion, replace, providerOther] using atOwner, live, pair⟩,
      stillOwned⟩


/-- Only an inactive prospective identity may receive its preparation/live record. -/
def updateRegion (s : State nr no nt) (r : Fin nr) (info : Region nr) : State nr no nt :=
  { s with regions := replace s.regions r (some info) }

theorem update_keeps_live (s : State nr no nt) (r q : Fin nr) (info : Region nr)
    (inactive : ¬ Live s r) (live : Live s q) : Live (updateRegion s r info) q := by
  have different : q ≠ r := fun eq => inactive (eq ▸ live)
  rcases live with ⟨old, found, phase⟩
  exact ⟨old, by simpa [updateRegion, replace, different] using found, phase⟩

theorem update_option_live (s : State nr no nt) (r : Fin nr) (info : Region nr)
    (inactive : ¬ Live s r) (context : Option (Fin nr)) (safe : OptionLive s context) :
    OptionLive (updateRegion s r info) context := by
  intro q found
  exact update_keeps_live s r q info inactive (safe q found)

theorem update_pending_live (s : State nr no nt) (r : Fin nr) (info : Region nr)
    (inactive : ¬ Live s r) (pending : Option (Pending nr no)) (safe : PendingLive s pending) :
    PendingLive (updateRegion s r info) pending := by
  intro p found
  have old := safe p found
  exact ⟨update_keeps_live s r p.selected info inactive old.1,
    update_option_live s r info inactive p.continuationContext old.2⟩

theorem update_contexts (s : State nr no nt) (r : Fin nr) (info : Region nr)
    (inactive : ¬ Live s r) (safe : SavedContextsSafe s) :
    SavedContextsSafe (updateRegion s r info) := by
  refine ⟨update_option_live s r info inactive s.selected safe.1,
    update_pending_live s r info inactive s.pending safe.2.1, ?_, ?_⟩
  · intro t c found
    have old := safe.2.2.1 t c found
    exact ⟨update_option_live s r info inactive c.selected old.1,
      update_pending_live s r info inactive c.pending old.2⟩
  · intro frame member
    have old := safe.2.2.2 frame member
    exact ⟨update_option_live s r info inactive frame.1 old.1,
      update_pending_live s r info inactive frame.2 old.2⟩

theorem update_kernel (s : State nr no nt) (r : Fin nr) (info : Region nr)
    (invariant : Invariant s) (inactive : ¬ Live s r)
    (ordered : ∀ parent, info.parent = some parent → parent.val < r.val) :
    Invariant (updateRegion s r info) := by
  rcases invariant with ⟨valid, publicGraph, backing, unique, saved⟩
  have objects : ObjectsSafe (updateRegion s r info) := by
    intro i o found active
    exact update_keeps_live s r o.region info inactive (valid.1 i o found active)
  have owners : OwnersOrdered (updateRegion s r info) := by
    intro q candidate parent found enclosing
    by_cases same : q = r
    · subst q
      simp [updateRegion, replace] at found
      subst candidate
      exact ordered parent enclosing
    · exact valid.2.1 q candidate parent (by simpa [updateRegion, replace, same] using found) enclosing
  have contexts := update_contexts s r info inactive saved
  refine ⟨⟨objects, owners, contexts.1⟩, ?_, ?_, unique, contexts⟩
  · intro i visible
    rcases publicGraph i visible with ⟨o, found, ready, deps, fields⟩
    exact ⟨o, found, ready, fun q member => update_keeps_live s r q info inactive (deps q member), fields⟩
  · intro i o found active
    rcases backing i o found active with ⟨req, reply, atRequest, supplied, owner, admitted⟩
    rcases admitted with ⟨target, identity, extent, align, aligned, provider, atOwner, live, pair⟩
    have different : req.owner ≠ r := by
      intro same
      exact inactive (same ▸ (show Live s req.owner from ⟨provider, atOwner, live⟩))
    exact ⟨req, reply, atRequest, supplied, owner, target, identity, extent, align, aligned,
      provider, by simpa [updateRegion, replace, different] using atOwner, live, pair⟩

theorem update_view (layout : Layout nr no) (s : State nr no nt) (r : Fin nr)
    (info : Region nr) (inactive : ¬ Live s r) (v : View no) (safe : ViewSafe layout s v) :
    ViewSafe layout (updateRegion s r info) v := by
  rcases safe with ⟨o, found, ready, resident, part⟩
  refine ⟨o, found, ready, update_keeps_live s r o.region info inactive resident, ?_⟩
  cases kind : v.inlinePart with
  | none => simpa [kind, updateRegion] using part
  | some p =>
    rcases (show s.publishedOnce v.object = true ∧
        ∃ deps, (layout v.object)[p]? = some deps ∧ DependenciesLive s deps
      from by simpa [kind] using part) with ⟨published, deps, actual, live⟩
    exact ⟨published, deps, actual, fun q member => update_keeps_live s r q info inactive (live q member)⟩

def updateMachineRegion (m : Machine nr no nt) (r : Fin nr) (info : Region nr) :
    Machine nr no nt := { m with heap := updateRegion m.heap r info }

theorem update_machine_region_preserves (layout : Layout nr no) (m : Machine nr no nt)
    (r : Fin nr) (info : Region nr) (safe : MachineSafe layout m) (inactive : ¬ Live m.heap r)
    (ordered : ∀ parent, info.parent = some parent → parent.val < r.val)
    (parentLive : ∀ parent, info.parent = some parent → Live m.heap parent) :
    MachineSafe layout (updateMachineRegion m r info) := by
  refine ⟨update_kernel m.heap r info safe.1 inactive ordered, ?_, ?_, ?_, ?_⟩
  · intro i v found
    exact update_view layout m.heap r info inactive v (safe.2.1 i v found)
  · intro q owned
    exact update_keeps_live m.heap r q info inactive (safe.2.2.1 q owned)
  · intro q candidate parent found live enclosing
    by_cases same : q = r
    · subst q
      simp [updateMachineRegion, updateRegion, replace] at found
      subst candidate
      exact update_keeps_live m.heap r parent info inactive (parentLive parent enclosing)
    · have old : m.heap.regions q = some candidate := by
        simpa [updateMachineRegion, updateRegion, replace, same] using found
      exact update_keeps_live m.heap r parent info inactive (safe.2.2.2.1 q candidate parent old live enclosing)
  · intro q c found
    rcases safe.2.2.2.2 q c found with ⟨owner, cursorSafe, owned⟩
    rcases cursorSafe with ⟨order, provider, atOwner, live, pair⟩
    have different : c.owner ≠ r := by
      intro same
      exact inactive (same ▸ (show Live m.heap c.owner from ⟨provider, atOwner, live⟩))
    exact ⟨owner, ⟨order, provider,
      by simpa [updateMachineRegion, updateRegion, replace, different] using atOwner, live, pair⟩, owned⟩

/-- Publication adds exactly the reserved activation as a new live owner. -/
def activate (m : Machine nr no nt) (r : Fin nr) : Machine nr no nt :=
  { m with heap := { m.heap with selected := some r, completionOrder := r :: m.heap.completionOrder } }

theorem activate_preserves (layout : Layout nr no) (m : Machine nr no nt) (r : Fin nr)
    (safe : MachineSafe layout m) (live : Live m.heap r) (fresh : ¬ Owns m.heap r) :
    MachineSafe layout (activate m r) := by
  rcases safe with ⟨⟨valid, publicGraph, backing, unique, contexts⟩, roots, owners, parents, closing⟩
  have newUnique : OwnersUnique (activate m r).heap := by
    refine ⟨List.nodup_cons.mpr ⟨fun member => fresh (Or.inl member), unique.1⟩, ?_⟩
    intro t c found
    have old := unique.2 t c found
    refine ⟨old.1, ?_, old.2.2⟩
    intro q member active
    rcases List.mem_cons.mp active with same | rest
    · subst q
      exact fresh (Or.inr ⟨t, c, found, member⟩)
    · exact old.2.1 q member rest
  refine ⟨⟨⟨valid.1, valid.2.1, ?_⟩, publicGraph, backing, newUnique,
    ⟨?_, contexts.2.1, contexts.2.2.1, contexts.2.2.2⟩⟩, roots, ?_, parents, ?_⟩
  · intro q selected
    have same : r = q := Option.some.inj selected
    exact same ▸ live
  · intro q selected
    have same : r = q := Option.some.inj selected
    exact same ▸ live
  · intro q owned
    rcases owned with active | captured
    · rcases List.mem_cons.mp active with same | old
      · exact same ▸ live
      · exact owners q (Or.inl old)
    · exact owners q (Or.inr captured)
  · intro q c found
    have old := closing q c found
    refine ⟨old.1, old.2.1, ?_⟩
    rcases old.2.2 with active | captured
    · exact Or.inl (List.mem_cons_of_mem r active)
    · exact Or.inr captured


def selectMachine (m : Machine nr no nt) (r : Fin nr) : Machine nr no nt :=
  { m with heap := select m.heap r }

theorem select_machine_preserves (layout : Layout nr no) (m : Machine nr no nt)
    (r : Fin nr) (safe : MachineSafe layout m) (live : Live m.heap r) :
    MachineSafe layout (selectMachine m r) := by
  rcases safe.1 with ⟨valid, publicGraph, backing, unique, contexts⟩
  have selected : OptionLive m.heap (some r) := by
    intro q eq
    exact (Option.some.inj eq) ▸ live
  exact ⟨⟨select_preserves m.heap r valid live, publicGraph, backing, unique,
    selected, contexts.2.1, contexts.2.2.1, contexts.2.2.2⟩,
    safe.2.1, safe.2.2.1, safe.2.2.2.1, safe.2.2.2.2⟩

/-- Entering a nested provider service saves the existing request rather than forbidding it. -/
def suspendService (s : State nr no nt) : State nr no nt :=
  { s with pending := none, returnContexts := (s.selected, s.pending) :: s.returnContexts,
           returnCuts := s.currentCut :: s.returnCuts }

def suspendMachine (m : Machine nr no nt) : Machine nr no nt :=
  { m with heap := suspendService m.heap }

theorem suspend_machine_preserves (layout : Layout nr no) (m : Machine nr no nt)
    (safe : MachineSafe layout m) : MachineSafe layout (suspendMachine m) := by
  rcases safe.1 with ⟨valid, publicGraph, backing, unique, contexts⟩
  have saved : SavedContextsSafe (suspendService m.heap) := by
    refine ⟨contexts.1, ?_, contexts.2.2.1, ?_⟩
    · intro p found
      cases found
    · intro frame member
      rcases List.mem_cons.mp member with same | old
      · subst frame
        exact ⟨contexts.1, contexts.2.1⟩
      · exact contexts.2.2.2 frame old
  exact ⟨⟨valid, publicGraph, backing, unique, saved⟩, safe.2.1, safe.2.2.1,
    safe.2.2.2.1, safe.2.2.2.2⟩

def returnMachine (m : Machine nr no nt)
    (frame : Option (Fin nr) × Option (Pending nr no))
    (rest : List (Option (Fin nr) × Option (Pending nr no))) (cut : Nat) (cuts : List Nat) :
    Machine nr no nt := { m with heap := returnToCaller m.heap frame rest cut cuts }

theorem return_machine_preserves (layout : Layout nr no) (m : Machine nr no nt)
    (frame : Option (Fin nr) × Option (Pending nr no))
    (rest : List (Option (Fin nr) × Option (Pending nr no))) (cut : Nat) (cuts : List Nat)
    (safe : MachineSafe layout m) (top : m.heap.returnContexts = frame :: rest) :
    MachineSafe layout (returnMachine m frame rest cut cuts) := by
  rcases safe.1 with ⟨valid, publicGraph, backing, unique, contexts⟩
  have saved := return_restores_safe_context m.heap frame rest cut cuts contexts top
  exact ⟨⟨⟨valid.1, valid.2.1, saved.1⟩, publicGraph, backing, unique, saved⟩,
    safe.2.1, safe.2.2.1, safe.2.2.2.1, safe.2.2.2.2⟩

def refuseMachine (m : Machine nr no nt) (i : Fin no) : Machine nr no nt :=
  { m with heap := refuse m.heap i }

theorem refuse_machine_preserves (layout : Layout nr no) (m : Machine nr no nt)
    (i : Fin no) (o : Object nr no) (safe : MachineSafe layout m)
    (found : m.heap.objects i = some o) (pending : o.phase = .pending) :
    MachineSafe layout (refuseMachine m i) := by
  rcases safe.1 with ⟨valid, publicGraph, backing, unique, contexts⟩
  have roots : RootsSafe layout (refuse m.heap i) m.roots := by
    intro k v atRoot
    apply view_private_update layout m.heap (refuse m.heap i) rfl (fun _ h => h) (fun _ h => h) _ v (safe.2.1 k v atRoot)
    intro j old atSlot ready
    have different : j ≠ i := by
      intro eq
      subst j
      have same : old = o := Option.some.inj (atSlot.symm.trans found)
      subst old
      simp [Ready, pending] at ready
    simpa [refuse, replace, different] using atSlot
  have saved : SavedContextsSafe (refuse m.heap i) := by
    refine ⟨contexts.1, ?_, contexts.2.2.1, contexts.2.2.2⟩
    intro p atPending
    cases atPending
  exact ⟨⟨refuse_preserves m.heap i valid,
    refusal_preserves_publication m.heap i o publicGraph found pending,
    refusal_preserves_backing m.heap i backing, unique, saved⟩,
    roots, safe.2.2.1, safe.2.2.2.1, safe.2.2.2.2⟩


/-- Refusal before backing supply creates no successful record and changes no prior object. -/
theorem refuse_empty_machine_preserves (layout : Layout nr no) (m : Machine nr no nt)
    (i : Fin no) (safe : MachineSafe layout m) (fresh : m.heap.objects i = none) :
    MachineSafe layout (refuseMachine m i) := by
  have objects : (refuse m.heap i).objects = m.heap.objects := by
    funext j
    by_cases same : j = i
    · subst j; simp [refuse, replace, fresh]
    · simp [refuse, replace, same]
  have old := safe.1
  have saved : SavedContextsSafe (refuse m.heap i) := by
    refine ⟨old.2.2.2.2.1, ?_, old.2.2.2.2.2.2.1, old.2.2.2.2.2.2.2⟩
    intro p atPending
    cases atPending
  refine ⟨⟨refuse_preserves m.heap i old.1, ?_,
    refusal_preserves_backing m.heap i old.2.2.1, old.2.2.2.1, saved⟩,
    ?_, safe.2.2.1, safe.2.2.2.1, safe.2.2.2.2⟩
  · exact private_update_preserves_publication m.heap (refuse m.heap i) old.2.1 rfl rfl
      (fun j _ => congrFun objects j)
  · intro k v found
    exact view_private_update layout m.heap (refuse m.heap i) rfl (fun _ h => h) (fun _ h => h)
      (fun j o atSlot _ => (congrFun objects j).trans atSlot) v (safe.2.1 k v found)


/-- Live entry publishes exactly the prepared identity; preceding selection is not its parent. -/
def enterLive (m : Machine nr no nt) (r : Fin nr) (prepared : Region nr)
    (pair : Association) : Machine nr no nt :=
  activate (updateMachineRegion m r { prepared with phase := .live, association := pair }) r

theorem enter_live_preserves (layout : Layout nr no) (m : Machine nr no nt)
    (r : Fin nr) (prepared : Region nr) (pair : Association) (safe : MachineSafe layout m)
    (found : m.heap.regions r = some prepared) (phase : prepared.phase = .preparing)
    (parentLive : ∀ parent, prepared.parent = some parent → Live m.heap parent) :
    MachineSafe layout (enterLive m r prepared pair) := by
  have inactive : ¬ Live m.heap r := by
    intro live
    rcases live with ⟨other, same, live⟩
    have eq : other = prepared := Option.some.inj (same.symm.trans found)
    subst other
    simp [phase] at live
  have fresh : ¬ Owns m.heap r := fun owned => inactive (safe.2.2.1 r owned)
  have updated := update_machine_region_preserves layout m r
    { prepared with phase := .live, association := pair } safe inactive
    (fun parent enclosing => safe.1.1.2.1 r prepared parent found enclosing) parentLive
  apply activate_preserves layout _ r updated
  · exact ⟨{ prepared with phase := .live, association := pair }, by simp [updateMachineRegion, updateRegion, replace], rfl⟩
  · exact fresh

/-- Freshness is independent of host success, and prevents reusing an old backing identity. -/
def FreshBacking (s : State nr no nt) (i : Fin no) : Prop := s.backing i = none

/-- A successful call/use checks its actual view; it never changes existing residency. -/
def Usable (layout : Layout nr no) (m : Machine nr no nt) (slot : Fin no) : Prop :=
  ∃ view, m.roots slot = some view ∧ ViewSafe layout m.heap view


end Ash.Regions

#print axioms Ash.Regions.view_private_update
#print axioms Ash.Regions.view_reserve
#print axioms Ash.Regions.view_initialize
#print axioms Ash.Regions.view_drop
#print axioms Ash.Regions.view_close
#print axioms Ash.Regions.whole_view_safe
#print axioms Ash.Regions.inline_view_safe
#print axioms Ash.Regions.set_root_safe
#print axioms Ash.Regions.drop_root_safe

#print axioms Ash.Regions.cleanup_step_preserves
#print axioms Ash.Regions.cleanup_keeps_pair
#print axioms Ash.Regions.complete_cleanup_has_run_every_action
#print axioms Ash.Regions.capture_keeps_live_owners
#print axioms Ash.Regions.resume_keeps_live_owners
#print axioms Ash.Regions.close_preserves_parents
#print axioms Ash.Regions.finish_close_keeps_live_owners

#print axioms Ash.Regions.construction_preserves_machine
#print axioms Ash.Regions.bind_view_preserves
#print axioms Ash.Regions.unbind_view_preserves
#print axioms Ash.Regions.begin_close_preserves
#print axioms Ash.Regions.advance_cleanup_preserves

#print axioms Ash.Regions.capture_machine_preserves
#print axioms Ash.Regions.resume_machine_preserves
#print axioms Ash.Regions.discard_machine_preserves
#print axioms Ash.Regions.complete_machine_close_preserves

#print axioms Ash.Regions.update_machine_region_preserves
#print axioms Ash.Regions.activate_preserves

#print axioms Ash.Regions.select_machine_preserves
#print axioms Ash.Regions.suspend_machine_preserves
#print axioms Ash.Regions.return_machine_preserves
#print axioms Ash.Regions.refuse_machine_preserves
#print axioms Ash.Regions.enter_live_preserves

#print axioms Ash.Regions.refuse_empty_machine_preserves
