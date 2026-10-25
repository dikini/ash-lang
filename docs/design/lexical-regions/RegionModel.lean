/-
Bounded region-construction model, R1 draft. No source/runtime correspondence
claim yet. Physical storage supply and successful release satisfy a module
contract; this model does not prove a native allocator or compiler.
-/
namespace Ash.Regions

inductive RegionPhase where
  | preparing | live | closing | closed
  deriving DecidableEq

inductive ObjectPhase where
  | pending | initialized | published | retired
  deriving DecidableEq

structure Association where
  allocateImplementation : Nat
  releaseImplementation : Nat
  stateIdentity : Nat
  discipline : Nat
  deriving DecidableEq

structure Region (nr : Nat) where
  phase : RegionPhase
  association : Association
  parent : Option (Fin nr)
  precedingContext : Option (Fin nr) := none
  providerCut : Nat := 0
  deriving DecidableEq

structure Object (nr no : Nat) where
  region : Fin nr
  phase : ObjectPhase
  required : List (Fin nr)
  fields : List (Fin no)
  initializer : Nat
  deriving DecidableEq

/-- Independent allocation metadata; no field value or closure payload crosses this boundary. -/
structure Requirements (nr : Nat) where
  owner : Fin nr
  extent : Nat
  alignment : Nat
  deriving DecidableEq

/-- An abstract actual backing reply, interpreted under the stated module contract. -/
structure Backing (nr no : Nat) where
  owner : Fin nr
  identity : Fin no
  association : Association
  extent : Nat
  alignment : Nat
  deriving DecidableEq

structure Pending (nr no : Nat) where
  object : Fin no
  selected : Fin nr
  nextInitializer : Nat
  operandHistory : Nat
  continuationContext : Option (Fin nr) := none
  continuationCut : Nat := 0
  deriving DecidableEq

structure Captured (nr no : Nat) where
  selected : Option (Fin nr)
  pending : Option (Pending nr no)
  completionOrder : List (Fin nr)
  cut : Nat := 0
  frames : List (Option (Fin nr) × Option (Pending nr no)) := []
  frameCuts : List Nat := []
  deriving DecidableEq

structure State (nr no nt : Nat) where
  regions : Fin nr → Option (Region nr)
  objects : Fin no → Option (Object nr no)
  selected : Option (Fin nr)
  pending : Option (Pending nr no)
  tickets : Fin nt → Option (Captured nr no)
  completionOrder : List (Fin nr)
  operandHistory : Nat
  exposed : Fin no → Bool := fun _ => false
  returnContexts : List (Option (Fin nr) × Option (Pending nr no)) := []
  requirements : Fin no → Option (Requirements nr) := fun _ => none
  backing : Fin no → Option (Backing nr no) := fun _ => none
  currentCut : Nat := 0
  liveCuts : List Nat := [0]
  returnCuts : List Nat := []
  publishedOnce : Fin no → Bool := fun _ => false
  cleanupActions : Fin nr → List Nat := fun _ => []

variable {nr no nt : Nat}

def replace [DecidableEq α] (f : α → β) (i : α) (v : β) : α → β :=
  fun j => if j = i then v else f j

def Live (s : State nr no nt) (r : Fin nr) : Prop :=
  ∃ info, s.regions r = some info ∧ info.phase = .live

def DependenciesLive (s : State nr no nt) (deps : List (Fin nr)) : Prop :=
  ∀ r, r ∈ deps → Live s r

def ObjectsSafe (s : State nr no nt) : Prop :=
  ∀ i o, s.objects i = some o → o.phase ≠ .retired →
    Live s o.region

def OwnersOrdered (s : State nr no nt) : Prop :=
  ∀ r info parent, s.regions r = some info → info.parent = some parent →
    parent.val < r.val

def Readable (s : State nr no nt) (i : Fin no) : Prop :=
  ∃ o, s.objects i = some o ∧ (o.phase = .initialized ∨ o.phase = .published)

def ContextSafe (s : State nr no nt) : Prop :=
  ∀ r, s.selected = some r → Live s r

def Valid (s : State nr no nt) : Prop :=
  ObjectsSafe s ∧ OwnersOrdered s ∧ ContextSafe s

def reserve (s : State nr no nt) (i : Fin no) (r : Fin nr) : State nr no nt :=
  { s with objects := replace s.objects i (some ⟨r, .pending, [], [], 0⟩) }

/-- Supply admits a fresh private slot, not an initialized Ash value. -/
theorem reserve_preserves (s : State nr no nt) (i : Fin no) (r : Fin nr)
    (valid : Valid s) (live : Live s r) : Valid (reserve s i r) := by
  rcases valid with ⟨objects, owners, context⟩
  refine ⟨?_, owners, context⟩
  intro j o found active
  by_cases same : j = i
  · subst j
    simp [reserve, replace] at found
    subst o
    exact live
  · simp [reserve, replace, same] at found
    exact objects j o found active

/-- Initialization records local fields/dependencies without publishing a root. -/
def initializeSlot (s : State nr no nt) (i : Fin no) (o : Object nr no)
    (deps : List (Fin nr)) (fields : List (Fin no)) : State nr no nt :=
  { s with objects := (replace s.objects i
      (some { o with phase := .initialized, required := deps, fields := fields,
                     initializer := o.initializer + 1 })) }

theorem initialize_preserves (s : State nr no nt) (i : Fin no) (o : Object nr no)
    (deps : List (Fin nr)) (fields : List (Fin no))
    (valid : Valid s) (found : s.objects i = some o) (pending : o.phase = .pending)
    (_safeDeps : DependenciesLive s deps) : Valid (initializeSlot s i o deps fields) := by
  rcases valid with ⟨objects, owners, context⟩
  have resident := objects i o found (by simp [pending])
  refine ⟨?_, owners, context⟩
  intro j candidate atSlot active
  by_cases same : j = i
  · subst j
    simp [initializeSlot, replace] at atSlot
    subst candidate
    exact resident
  · simp [initializeSlot, replace, same] at atSlot
    exact objects j candidate atSlot active

/-- Refusal discards only pending private construction; published slots stay exact. -/
def refuse (s : State nr no nt) (i : Fin no) : State nr no nt :=
  { s with objects := replace s.objects i none, pending := none }

theorem refuse_preserves (s : State nr no nt) (i : Fin no)
    (valid : Valid s) : Valid (refuse s i) := by
  rcases valid with ⟨objects, owners, context⟩
  refine ⟨?_, owners, context⟩
  intro j o found active
  by_cases same : j = i
  · subst j; simp [refuse, replace] at found
  · simp [refuse, replace, same] at found
    exact objects j o found active

theorem refusal_keeps_previous (s : State nr no nt) (i j : Fin no)
    (different : j ≠ i) : (refuse s i).objects j = s.objects j := by
  simp [refuse, replace, different]

theorem refusal_keeps_operand_history (s : State nr no nt) (i : Fin no) :
    (refuse s i).operandHistory = s.operandHistory := rfl

/-- Selection changes fresh allocation context only, never object residency. -/
def select (s : State nr no nt) (r : Fin nr) : State nr no nt :=
  { s with selected := some r }

theorem select_preserves (s : State nr no nt) (r : Fin nr)
    (valid : Valid s) (live : Live s r) : Valid (select s r) := by
  rcases valid with ⟨objects, owners, _⟩
  refine ⟨objects, owners, ?_⟩
  intro q selected
  have same : r = q := Option.some.inj selected
  subst q
  exact live

theorem selection_keeps_residency (s : State nr no nt) (r : Fin nr) :
    (select s r).objects = s.objects := rfl

/-- Restoring an already captured context consumes its ticket once. -/
def resume (s : State nr no nt) (t : Fin nt) (c : Captured nr no) : State nr no nt :=
  { s with selected := c.selected, pending := c.pending,
           completionOrder := c.completionOrder ++ s.completionOrder,
           returnContexts := (s.selected, s.pending) :: s.returnContexts,
           returnCuts := s.currentCut :: s.returnCuts, currentCut := c.cut,
           tickets := replace s.tickets t none }

theorem resume_consumes_ticket (s : State nr no nt) (t : Fin nt) (c : Captured nr no) :
    (resume s t c).tickets t = none := by simp [resume, replace]

theorem resume_preserves (s : State nr no nt) (t : Fin nt) (c : Captured nr no)
    (valid : Valid s) (context : ∀ r, c.selected = some r → Live s r) :
    Valid (resume s t c) := by
  exact ⟨valid.1, valid.2.1, context⟩

/-- Ownership is a position in the active segment or exactly one captured ticket. -/
def OwnersUnique (s : State nr no nt) : Prop :=
  s.completionOrder.Nodup ∧ ∀ t c, s.tickets t = some c →
    c.completionOrder.Nodup ∧
    (∀ r, r ∈ c.completionOrder → r ∉ s.completionOrder) ∧
    (∀ u d, u ≠ t → s.tickets u = some d →
      ∀ r, r ∈ c.completionOrder → r ∉ d.completionOrder)

def capture (s : State nr no nt) (t : Fin nt) (inside outside : List (Fin nr))
    (handlerContext : Option (Fin nr)) (handlerCut : Nat) : State nr no nt :=
  let captured : Captured nr no :=
    { selected := s.selected, pending := s.pending, completionOrder := inside, cut := s.currentCut }
  { s with selected := handlerContext, pending := none, completionOrder := outside,
           currentCut := handlerCut, tickets := replace s.tickets t (some captured) }

theorem capture_preserves_ownership (s : State nr no nt) (t : Fin nt)
    (inside outside : List (Fin nr)) (handler : Option (Fin nr)) (handlerCut : Nat)
    (unique : OwnersUnique s) (_fresh : s.tickets t = none)
    (split : s.completionOrder = inside ++ outside) :
    OwnersUnique (capture s t inside outside handler handlerCut) := by
  have segments := List.nodup_append.mp (split ▸ unique.1)
  refine ⟨segments.2.1, ?_⟩
  intro u c found
  by_cases same : u = t
  · subst u
    simp [capture, replace] at found
    subst c
    refine ⟨segments.1, ?_, ?_⟩
    · intro r member outer
      exact segments.2.2 r member r outer rfl
    · intro v d different atSlot r member inOther
      have oldSlot : s.tickets v = some d := by
        simpa [capture, replace, different] using atSlot
      have disjoint := (unique.2 v d oldSlot).2.1
      exact disjoint r inOther (split ▸ List.mem_append_left outside member)
  · have oldSlot : s.tickets u = some c := by simpa [capture, replace, same] using found
    rcases unique.2 u c oldSlot with ⟨nodup, outsideActive, outsideOther⟩
    refine ⟨nodup, ?_, ?_⟩
    · intro r member inOutside
      exact outsideActive r member (split ▸ List.mem_append_right inside inOutside)
    · intro v d different atSlot r member
      by_cases atNew : v = t
      · subst v
        simp [capture, replace] at atSlot
        subst d
        intro inInside
        exact outsideActive r member (split ▸ List.mem_append_left outside inInside)
      · have oldOther : s.tickets v = some d := by
          simpa [capture, replace, atNew] using atSlot
        exact outsideOther v d different oldOther r member

theorem resume_preserves_ownership (s : State nr no nt) (t : Fin nt)
    (c : Captured nr no) (unique : OwnersUnique s) (ticket : s.tickets t = some c) :
    OwnersUnique (resume s t c) := by
  rcases unique.2 t c ticket with ⟨capturedNodup, notActive, notOther⟩
  refine ⟨List.nodup_append.mpr ⟨capturedNodup, unique.1, ?_⟩, ?_⟩
  · intro r member q active equal
    subst q
    exact notActive r member active
  · intro u d found
    have different : u ≠ t := by
      intro same
      subst u
      simp [resume, replace] at found
    have oldSlot : s.tickets u = some d := by simpa [resume, replace, different] using found
    rcases unique.2 u d oldSlot with ⟨nodup, outsideActive, outsideOther⟩
    refine ⟨nodup, ?_, ?_⟩
    · intro r member inJoined
      rcases List.mem_append.mp inJoined with captured | active
      · exact notOther u d different oldSlot r captured member
      · exact outsideActive r member active
    · intro v e differentOwner atSlot r member
      have notConsumed : v ≠ t := by
        intro same
        subst v
        simp [resume, replace] at atSlot
      have oldOther : s.tickets v = some e := by
        simpa [resume, replace, notConsumed] using atSlot
      exact outsideOther v e differentOwner oldOther r member

/-- Resume retains the resumer's owned outside segment rather than overwriting it. -/
theorem resume_keeps_outside_owners (s : State nr no nt) (t : Fin nt)
    (c : Captured nr no) (r : Fin nr) (outside : r ∈ s.completionOrder) :
    r ∈ (resume s t c).completionOrder := List.mem_append_right _ outside

theorem resume_saves_caller_context (s : State nr no nt) (t : Fin nt)
    (c : Captured nr no) :
    (resume s t c).returnContexts.head? = some (s.selected, s.pending) := rfl

def OptionLive (s : State nr no nt) (context : Option (Fin nr)) : Prop :=
  ∀ r, context = some r → Live s r

def PendingLive (s : State nr no nt) (pending : Option (Pending nr no)) : Prop :=
  ∀ p, pending = some p → Live s p.selected ∧ OptionLive s p.continuationContext

/-- Every dormant selected owner remains live; capture grants no lifetime extension. -/
def SavedContextsSafe (s : State nr no nt) : Prop :=
  OptionLive s s.selected ∧ PendingLive s s.pending ∧
  (∀ t c, s.tickets t = some c → OptionLive s c.selected ∧ PendingLive s c.pending) ∧
  ∀ frame, frame ∈ s.returnContexts → OptionLive s frame.1 ∧ PendingLive s frame.2

theorem capture_preserves_contexts (s : State nr no nt) (t : Fin nt)
    (inside outside : List (Fin nr)) (handler : Option (Fin nr)) (handlerCut : Nat)
    (safe : SavedContextsSafe s) (handlerLive : OptionLive s handler) :
    SavedContextsSafe (capture s t inside outside handler handlerCut) := by
  refine ⟨handlerLive, ?_, ?_, ?_⟩
  · intro p found
    simp [capture] at found
  · intro u c found
    by_cases same : u = t
    · subst u
      simp [capture, replace] at found
      subst c
      exact ⟨safe.1, safe.2.1⟩
    · have oldSlot : s.tickets u = some c := by simpa [capture, replace, same] using found
      exact safe.2.2.1 u c oldSlot
  · exact safe.2.2.2

theorem resume_preserves_contexts (s : State nr no nt) (t : Fin nt)
    (c : Captured nr no) (safe : SavedContextsSafe s) (ticket : s.tickets t = some c) :
    SavedContextsSafe (resume s t c) := by
  have restored := safe.2.2.1 t c ticket
  refine ⟨restored.1, restored.2, ?_, ?_⟩
  · intro u d found
    have different : u ≠ t := by
      intro same
      subst u
      simp [resume, replace] at found
    have oldSlot : s.tickets u = some d := by simpa [resume, replace, different] using found
    exact safe.2.2.1 u d oldSlot
  · intro frame member
    rcases List.mem_cons.mp member with same | old
    · subst frame
      exact ⟨safe.1, safe.2.1⟩
    · exact safe.2.2.2 frame old

def returnToCaller (s : State nr no nt)
    (frame : Option (Fin nr) × Option (Pending nr no))
    (rest : List (Option (Fin nr) × Option (Pending nr no))) (cut : Nat) (cutRest : List Nat) :
    State nr no nt :=
  { s with selected := frame.1, pending := frame.2, returnContexts := rest,
           currentCut := cut, returnCuts := cutRest }

theorem return_restores_safe_context (s : State nr no nt)
    (frame : Option (Fin nr) × Option (Pending nr no))
    (rest : List (Option (Fin nr) × Option (Pending nr no))) (cut : Nat) (cutRest : List Nat)
    (safe : SavedContextsSafe s) (top : s.returnContexts = frame :: rest) :
    SavedContextsSafe (returnToCaller s frame rest cut cutRest) := by
  have frameSafe := safe.2.2.2 frame (top ▸ List.mem_cons_self)
  refine ⟨frameSafe.1, frameSafe.2, safe.2.2.1, ?_⟩
  intro other member
  exact safe.2.2.2 other (top ▸ List.mem_cons_of_mem frame member)

def Owns (s : State nr no nt) (r : Fin nr) : Prop :=
  r ∈ s.completionOrder ∨ ∃ t c, s.tickets t = some c ∧ r ∈ c.completionOrder

theorem capture_conserves_owners (s : State nr no nt) (t : Fin nt)
    (inside outside : List (Fin nr)) (handler : Option (Fin nr)) (handlerCut : Nat)
    (fresh : s.tickets t = none) (split : s.completionOrder = inside ++ outside)
    (r : Fin nr) : Owns (capture s t inside outside handler handlerCut) r ↔ Owns s r := by
  constructor
  · intro owned
    rcases owned with active | ⟨u, c, found, member⟩
    · exact Or.inl (split ▸ List.mem_append_right inside active)
    · by_cases same : u = t
      · subst u
        simp [capture, replace] at found
        subst c
        exact Or.inl (split ▸ List.mem_append_left outside member)
      · have oldSlot : s.tickets u = some c := by simpa [capture, replace, same] using found
        exact Or.inr ⟨u, c, oldSlot, member⟩
  · intro owned
    rcases owned with active | ⟨u, c, found, member⟩
    · have joined : r ∈ inside ++ outside := split ▸ active
      rcases List.mem_append.mp joined with inner | outer
      · exact Or.inr ⟨t, { selected := s.selected, pending := s.pending, completionOrder := inside, cut := s.currentCut },
          by simp [capture, replace], inner⟩
      · exact Or.inl outer
    · have different : u ≠ t := by
        intro same
        subst u
        simp [fresh] at found
      exact Or.inr ⟨u, c, by simpa [capture, replace, different] using found, member⟩

theorem resume_conserves_owners (s : State nr no nt) (t : Fin nt)
    (c : Captured nr no) (ticket : s.tickets t = some c) (r : Fin nr) :
    Owns (resume s t c) r ↔ Owns s r := by
  constructor
  · intro owned
    rcases owned with active | ⟨u, d, found, member⟩
    · rcases List.mem_append.mp active with inner | outer
      · exact Or.inr ⟨t, c, ticket, inner⟩
      · exact Or.inl outer
    · have different : u ≠ t := by
        intro same
        subst u
        simp [resume, replace] at found
      exact Or.inr ⟨u, d, by simpa [resume, replace, different] using found, member⟩
  · intro owned
    rcases owned with active | ⟨u, d, found, member⟩
    · exact Or.inl (List.mem_append_right c.completionOrder active)
    · by_cases same : u = t
      · subst u
        have eq : d = c := Option.some.inj (found.symm.trans ticket)
        subst d
        exact Or.inl (List.mem_append_left s.completionOrder member)
      · exact Or.inr ⟨u, d, by simpa [resume, replace, same] using found, member⟩

def Ready (o : Object nr no) : Prop :=
  o.phase = .initialized ∨ o.phase = .published

/-- Public graph closure includes every reachable field and its region dependency. -/
def PublicationSafe (s : State nr no nt) : Prop :=
  ∀ i, s.exposed i = true → ∃ o, s.objects i = some o ∧ Ready o ∧ DependenciesLive s o.required ∧
    ∀ j, j ∈ o.fields → s.exposed j = true ∧
      ∃ target, s.objects j = some target ∧
        (target.region = o.region ∨ target.region ∈ o.required)

theorem public_not_pending (s : State nr no nt) (safe : PublicationSafe s)
    (i : Fin no) (o : Object nr no) (found : s.objects i = some o)
    (pending : o.phase = .pending) : s.exposed i = false := by
  cases flag : s.exposed i with
  | false => rfl
  | true =>
    rcases safe i flag with ⟨other, same, ready, _⟩
    have eq : other = o := Option.some.inj (same.symm.trans found)
    subst other
    simp [Ready, pending] at ready

/-- A private slot update preserves the entire preexisting exposed graph. -/
theorem private_update_preserves_publication (s next : State nr no nt)
    (safe : PublicationSafe s) (flags : next.exposed = s.exposed)
    (regions : next.regions = s.regions) (unchanged : ∀ i, s.exposed i = true → next.objects i = s.objects i) :
    PublicationSafe next := by
  intro i visible
  have oldFlag : s.exposed i = true := by simpa [flags] using visible
  rcases safe i oldFlag with ⟨o, found, ready, deps, fields⟩
  refine ⟨o, (unchanged i oldFlag).trans found, ready, (by simpa [DependenciesLive, Live, regions] using deps), ?_⟩
  intro j member
  rcases fields j member with ⟨publicField, target, targetFound, dependency⟩
  exact ⟨by simpa [flags] using publicField,
         target, (unchanged j publicField).trans targetFound, dependency⟩

theorem reserve_preserves_publication (s : State nr no nt) (i : Fin no) (r : Fin nr)
    (safe : PublicationSafe s) (fresh : s.objects i = none) :
    PublicationSafe (reserve s i r) := by
  apply private_update_preserves_publication s (reserve s i r) safe rfl rfl
  intro j visible
  have different : j ≠ i := by
    intro same
    subst j
    rcases safe i visible with ⟨o, found, _⟩
    simp [fresh] at found
  simp [reserve, replace, different]

theorem initialize_preserves_publication (s : State nr no nt) (i : Fin no)
    (o : Object nr no) (deps : List (Fin nr)) (fields : List (Fin no))
    (safe : PublicationSafe s) (found : s.objects i = some o)
    (pending : o.phase = .pending) :
    PublicationSafe (initializeSlot s i o deps fields) := by
  have privateSlot := public_not_pending s safe i o found pending
  apply private_update_preserves_publication s (initializeSlot s i o deps fields) safe rfl rfl
  intro j visible
  have different : j ≠ i := by
    intro same
    subst j
    simp [privateSlot] at visible
  simp [initializeSlot, replace, different]

theorem refusal_preserves_publication (s : State nr no nt) (i : Fin no)
    (o : Object nr no) (safe : PublicationSafe s) (found : s.objects i = some o)
    (pending : o.phase = .pending) : PublicationSafe (refuse s i) := by
  have privateSlot := public_not_pending s safe i o found pending
  apply private_update_preserves_publication s (refuse s i) safe rfl rfl
  intro j visible
  have different : j ≠ i := by
    intro same
    subst j
    simp [privateSlot] at visible
  simp [refuse, replace, different]

/-- Local publication admission closes a finite initialized graph, including cycles. -/
def GroupReady (s : State nr no nt) (group : List (Fin no)) : Prop :=
  (∀ i, i ∈ group → s.publishedOnce i = false) ∧ ∀ i, i ∈ group → ∃ o, s.objects i = some o ∧ Ready o ∧ DependenciesLive s o.required ∧
    ∀ j, j ∈ o.fields → (s.exposed j = true ∨ j ∈ group) ∧
      ∃ target, s.objects j = some target ∧
        (target.region = o.region ∨ target.region ∈ o.required)

def publishGroup (s : State nr no nt) (group : List (Fin no)) : State nr no nt :=
  { s with exposed := fun i => if i ∈ group then true else s.exposed i,
           publishedOnce := fun i => if i ∈ group then true else s.publishedOnce i }

theorem publish_group_preserves (s : State nr no nt) (group : List (Fin no))
    (safe : PublicationSafe s) (ready : GroupReady s group) :
    PublicationSafe (publishGroup s group) := by
  intro i visible
  by_cases member : i ∈ group
  · rcases ready.2 i member with ⟨o, found, initialized, deps, fields⟩
    refine ⟨o, found, initialized, deps, ?_⟩
    intro j field
    rcases fields j field with ⟨available, target, targetFound, dependency⟩
    refine ⟨?_, target, targetFound, dependency⟩
    rcases available with old | new
    · simp [publishGroup, old]
    · simp [publishGroup, new]
  · have old : s.exposed i = true := by simpa [publishGroup, member] using visible
    rcases safe i old with ⟨o, found, initialized, deps, fields⟩
    refine ⟨o, found, initialized, deps, ?_⟩
    intro j field
    rcases fields j field with ⟨available, target, targetFound, dependency⟩
    exact ⟨by simp [publishGroup, available], target, targetFound, dependency⟩

theorem public_read_is_initialized (s : State nr no nt) (safe : PublicationSafe s)
    (i : Fin no) (visible : s.exposed i = true) : Readable s i := by
  rcases safe i visible with ⟨o, found, ready, _⟩
  exact ⟨o, found, ready⟩

/-- Bulk release retires the selected region's objects, without following data edges. -/
def closeRegion (s : State nr no nt) (r : Fin nr) (info : Region nr) : State nr no nt :=
  { s with regions := replace s.regions r (some { info with phase := .closed }),
           objects := fun i => (s.objects i).map fun o =>
             if o.region = r then { o with phase := .retired } else o,
           exposed := fun i => match s.objects i with
             | none => false
             | some o => if o.region = r then false else s.exposed i }

theorem close_keeps_other_live (s : State nr no nt) (r q : Fin nr) (info : Region nr)
    (different : q ≠ r) (live : Live s q) : Live (closeRegion s r info) q := by
  rcases live with ⟨other, found, phase⟩
  exact ⟨other, by simp [closeRegion, replace, different, found], phase⟩

theorem close_preserves (s : State nr no nt) (r : Fin nr) (info : Region nr)
    (valid : Valid s) (region : s.regions r = some info)
    (notSelected : s.selected ≠ some r) : Valid (closeRegion s r info) := by
  rcases valid with ⟨objects, owners, context⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i o found active
    cases original : s.objects i with
    | none => simp [closeRegion, original] at found
    | some old =>
      by_cases owns : old.region = r
      · simp [closeRegion, original, owns] at found
        subst o
        exact False.elim (active rfl)
      · simp [closeRegion, original, owns] at found
        subst o
        exact close_keeps_other_live s r old.region info owns (objects i old original active)
  · intro q other parent found enclosing
    by_cases same : q = r
    · subst q
      simp [closeRegion, replace] at found
      subst other
      exact owners r info parent region enclosing
    · simp [closeRegion, replace, same] at found
      exact owners q other parent found enclosing
  · intro q selected
    have different : q ≠ r := by
      intro same
      subst q
      exact notSelected selected
    exact close_keeps_other_live s r q info different (context q selected)

theorem close_retires_owned (s : State nr no nt) (r : Fin nr) (info : Region nr)
    (i : Fin no) (o : Object nr no) (found : s.objects i = some o) (owns : o.region = r) :
    (closeRegion s r info).objects i = some { o with phase := .retired } := by
  simp [closeRegion, found, owns]

theorem close_preserves_other_objects (s : State nr no nt) (r : Fin nr) (info : Region nr)
    (i : Fin no) (o : Object nr no) (found : s.objects i = some o) (other : o.region ≠ r) :
    (closeRegion s r info).objects i = some o := by simp [closeRegion, found, other]

theorem close_keeps_allocator_association (s : State nr no nt) (r : Fin nr)
    (info : Region nr) :
    ∃ closed, (closeRegion s r info).regions r = some closed ∧
      closed.association = info.association := by
  exact ⟨{ info with phase := .closed }, by simp [closeRegion, replace], rfl⟩

/-- Dropping all usable aliases revokes access, but does not free or move backing. -/
def dropAccess (s : State nr no nt) (group : List (Fin no)) : State nr no nt :=
  { s with exposed := fun i => if i ∈ group then false else s.exposed i }

def NoIncomingUse (s : State nr no nt) (group : List (Fin no)) : Prop :=
  ∀ i o, s.exposed i = true → i ∉ group → s.objects i = some o →
    ∀ j, j ∈ o.fields → j ∉ group

theorem drop_access_preserves (s : State nr no nt) (group : List (Fin no))
    (safe : PublicationSafe s) (noIncoming : NoIncomingUse s group) :
    PublicationSafe (dropAccess s group) := by
  intro i visible
  have outside : i ∉ group := by
    intro member
    simp [dropAccess, member] at visible
  have oldFlag : s.exposed i = true := by simpa [dropAccess, outside] using visible
  rcases safe i oldFlag with ⟨o, found, ready, deps, fields⟩
  refine ⟨o, found, ready, deps, ?_⟩
  intro j field
  rcases fields j field with ⟨available, target, targetFound, dependency⟩
  have outsideField := noIncoming i o oldFlag outside found j field
  exact ⟨by simp [dropAccess, outsideField, available], target, targetFound, dependency⟩

theorem dropped_record_stays_physical (s : State nr no nt) (group : List (Fin no)) :
    (dropAccess s group).objects = s.objects ∧ (dropAccess s group).backing = s.backing :=
  ⟨rfl, rfl⟩

/-- Only still-usable outside dependencies block region close; dead records may remain. -/
def NoOutsideUsableDependency (s : State nr no nt) (r : Fin nr) : Prop :=
  ∀ i o, s.exposed i = true → s.objects i = some o → o.region ≠ r → r ∉ o.required

theorem close_preserves_publication (s : State nr no nt) (r : Fin nr) (info : Region nr)
    (safe : PublicationSafe s) (noDependents : NoOutsideUsableDependency s r) :
    PublicationSafe (closeRegion s r info) := by
  intro i visible
  cases original : s.objects i with
  | none => simp [closeRegion, original] at visible
  | some o =>
    have outside : o.region ≠ r := by
      intro same
      simp [closeRegion, original, same] at visible
    have oldFlag : s.exposed i = true := by
      simpa [closeRegion, original, outside] using visible
    rcases safe i oldFlag with ⟨old, found, ready, deps, fields⟩
    have eq : old = o := Option.some.inj (found.symm.trans original)
    subst old
    have excludes := noDependents i o oldFlag original outside
    refine ⟨o, by simp [closeRegion, original, outside], ready, ?_, ?_⟩
    · intro q member
      have different : q ≠ r := by
        intro same
        subst q
        exact excludes member
      exact close_keeps_other_live s r q info different (deps q member)
    · intro j field
      rcases fields j field with ⟨available, target, targetFound, dependency⟩
      have targetOutside : target.region ≠ r := by
        intro same
        rcases dependency with sameRegion | required
        · exact outside (sameRegion.symm.trans same)
        · exact excludes (same ▸ required)
      exact ⟨by simp [closeRegion, targetFound, targetOutside, available], target,
        by simp [closeRegion, targetFound, targetOutside], dependency⟩

def ReplyAdmitted (s : State nr no nt) (i : Fin no)
    (request : Requirements nr) (reply : Backing nr no) : Prop :=
  reply.owner = request.owner ∧ reply.identity = i ∧
  request.extent ≤ reply.extent ∧ 0 < request.alignment ∧
  reply.alignment = request.alignment ∧
  ∃ info, s.regions request.owner = some info ∧ info.phase = .live ∧
    reply.association = info.association

/-- Active records are backed by a matching descriptor, not merely a capacity debit. -/
def BackingSafe (s : State nr no nt) : Prop :=
  ∀ i o, s.objects i = some o → o.phase ≠ .retired →
    ∃ request reply, s.requirements i = some request ∧ s.backing i = some reply ∧
      o.region = request.owner ∧ ReplyAdmitted s i request reply

def requestStorage (s : State nr no nt) (i : Fin no) (request : Requirements nr)
    (owner : Region nr) : State nr no nt :=
  { s with requirements := replace s.requirements i (some request),
           pending := some { object := i, selected := request.owner, nextInitializer := 0,
                             operandHistory := s.operandHistory,
                             continuationContext := s.selected, continuationCut := s.currentCut },
           selected := owner.precedingContext, currentCut := owner.providerCut }

def supplyStorage (s : State nr no nt) (i : Fin no)
    (request : Requirements nr) (reply : Backing nr no) (continuation : Pending nr no) :
    State nr no nt :=
  { (reserve s i request.owner) with
      backing := replace s.backing i (some reply)
      pending := none
      selected := continuation.continuationContext
      currentCut := continuation.continuationCut }

theorem request_preserves_backing (s : State nr no nt) (i : Fin no)
    (request : Requirements nr) (ownerInfo : Region nr)
    (safe : BackingSafe s) (fresh : s.objects i = none) :
    BackingSafe (requestStorage s i request ownerInfo) := by
  intro j o found active
  have different : j ≠ i := by
    intro same
    subst j
    simp [requestStorage, fresh] at found
  rcases safe j o found active with ⟨oldRequest, reply, requirements, backing, owner, admitted⟩
  exact ⟨oldRequest, reply, by simpa [requestStorage, replace, different] using requirements,
    backing, owner, admitted⟩

theorem supply_preserves_backing (s : State nr no nt) (i : Fin no)
    (request : Requirements nr) (reply : Backing nr no) (continuation : Pending nr no)
    (safe : BackingSafe s) (registered : s.requirements i = some request)
    (admitted : ReplyAdmitted s i request reply) :
    BackingSafe (supplyStorage s i request reply continuation) := by
  intro j o found active
  by_cases same : j = i
  · subst j
    simp [supplyStorage, reserve, replace] at found
    subst o
    exact ⟨request, reply, registered, by simp [supplyStorage, replace], rfl, admitted⟩
  · have oldSlot : s.objects j = some o := by
      simpa [supplyStorage, reserve, replace, same] using found
    rcases safe j o oldSlot active with ⟨oldRequest, oldReply, requirements, backing, owner, old⟩
    exact ⟨oldRequest, oldReply, requirements,
      by simpa [supplyStorage, replace, same] using backing, owner, old⟩

theorem initialize_preserves_backing (s : State nr no nt) (i : Fin no)
    (o : Object nr no) (deps : List (Fin nr)) (fields : List (Fin no))
    (safe : BackingSafe s) (found : s.objects i = some o) (pending : o.phase = .pending) :
    BackingSafe (initializeSlot s i o deps fields) := by
  intro j candidate atSlot active
  by_cases same : j = i
  · subst j
    simp [initializeSlot, replace] at atSlot
    subst candidate
    exact safe i o found (by simp [pending])
  · have oldSlot : s.objects j = some candidate := by
      simpa [initializeSlot, replace, same] using atSlot
    exact safe j candidate oldSlot active

theorem refusal_preserves_backing (s : State nr no nt) (i : Fin no)
    (safe : BackingSafe s) : BackingSafe (refuse s i) := by
  intro j o found active
  by_cases same : j = i
  · subst j
    simp [refuse, replace] at found
  · have oldSlot : s.objects j = some o := by simpa [refuse, replace, same] using found
    exact safe j o oldSlot active

theorem request_preserves_contexts (s : State nr no nt) (i : Fin no)
    (request : Requirements nr) (owner : Region nr)
    (safe : SavedContextsSafe s) (targetLive : Live s request.owner)
    (callbackLive : OptionLive s owner.precedingContext) :
    SavedContextsSafe (requestStorage s i request owner) := by
  refine ⟨callbackLive, ?_, safe.2.2.1, safe.2.2.2⟩
  intro pending found
  simp [requestStorage] at found
  subst pending
  exact ⟨targetLive, safe.1⟩

theorem supply_preserves_contexts (s : State nr no nt) (i : Fin no)
    (request : Requirements nr) (reply : Backing nr no) (continuation : Pending nr no)
    (safe : SavedContextsSafe s) (pending : s.pending = some continuation) :
    SavedContextsSafe (supplyStorage s i request reply continuation) := by
  have restored := (safe.2.1 continuation pending).2
  refine ⟨restored, ?_, safe.2.2.1, safe.2.2.2⟩
  intro p found
  simp [supplyStorage] at found

/-- The callback uses the owner's preceding context and returns to the exact caller. -/
theorem request_callback_context (s : State nr no nt) (i : Fin no)
    (request : Requirements nr) (owner : Region nr) :
    (requestStorage s i request owner).selected = owner.precedingContext ∧
    (requestStorage s i request owner).currentCut = owner.providerCut := ⟨rfl, rfl⟩

theorem supply_returns_to_caller (s : State nr no nt) (i : Fin no)
    (request : Requirements nr) (reply : Backing nr no) (continuation : Pending nr no) :
    (supplyStorage s i request reply continuation).selected = continuation.continuationContext ∧
    (supplyStorage s i request reply continuation).currentCut = continuation.continuationCut :=
  ⟨rfl, rfl⟩

/-- Admission facts concern the touched slots, actual owner and local guarded fields. -/
inductive ConstructionStep : State nr no nt → State nr no nt → Prop where
  | request (s : State nr no nt) (i : Fin no) (request : Requirements nr) (owner : Region nr)
      (noPending : s.pending = none) (freshRequest : s.requirements i = none)
      (freshObject : s.objects i = none) (foundOwner : s.regions request.owner = some owner)
      (live : owner.phase = .live) (callbackLive : OptionLive s owner.precedingContext)
      (cutPresent : owner.providerCut ∈ s.liveCuts) :
      ConstructionStep s (requestStorage s i request owner)
  | supply (s : State nr no nt) (i : Fin no) (request : Requirements nr)
      (reply : Backing nr no) (continuation : Pending nr no)
      (pending : s.pending = some continuation) (sameSlot : continuation.object = i)
      (sameTarget : continuation.selected = request.owner)
      (registered : s.requirements i = some request) (freshObject : s.objects i = none)
      (admitted : ReplyAdmitted s i request reply) :
      ConstructionStep s (supplyStorage s i request reply continuation)
  | initializeSlot (s : State nr no nt) (i : Fin no) (o : Object nr no)
      (deps : List (Fin nr)) (fields : List (Fin no))
      (found : s.objects i = some o) (pending : o.phase = .pending)
      (dependencies : DependenciesLive s deps)
      (guardedFields : ∀ j, j ∈ fields → ∃ target, s.objects j = some target) :
      ConstructionStep s (initializeSlot s i o deps fields)
  | publish (s : State nr no nt) (group : List (Fin no)) (ready : GroupReady s group) :
      ConstructionStep s (publishGroup s group)
  | drop (s : State nr no nt) (group : List (Fin no)) (noIncoming : NoIncomingUse s group) :
      ConstructionStep s (dropAccess s group)

inductive ConstructionTrace : State nr no nt → State nr no nt → Prop where
  | refl (s) : ConstructionTrace s s
  | next (s mid finish) (step : ConstructionStep s mid) (rest : ConstructionTrace mid finish) :
      ConstructionTrace s finish

/-- Physical ownership, usable graph dependencies and control ownership remain separate. -/
def Invariant (s : State nr no nt) : Prop :=
  Valid s ∧ PublicationSafe s ∧ BackingSafe s ∧ OwnersUnique s ∧ SavedContextsSafe s

theorem construction_step_preserves (s next : State nr no nt)
    (invariant : Invariant s) (step : ConstructionStep s next) : Invariant next := by
  rcases invariant with ⟨valid, exposed, backing, unique, contexts⟩
  cases step with
  | request i request owner _ _ fresh found phase callback _ =>
      have target : Live s request.owner := ⟨owner, found, phase⟩
      refine ⟨⟨valid.1, valid.2.1, callback⟩, exposed,
        request_preserves_backing s i request owner backing fresh, unique, ?_⟩
      exact request_preserves_contexts s i request owner contexts target callback
  | supply i request reply continuation pending _ _ registered fresh admitted =>
      rcases admitted.2.2.2.2.2 with ⟨owner, found, phase, _⟩
      have target : Live s request.owner := ⟨owner, found, phase⟩
      have resident := reserve_preserves s i request.owner valid target
      have restored := (contexts.2.1 continuation pending).2
      refine ⟨⟨resident.1, resident.2.1, restored⟩,
        reserve_preserves_publication s i request.owner exposed fresh,
        supply_preserves_backing s i request reply continuation backing registered admitted,
        unique, ?_⟩
      exact supply_preserves_contexts s i request reply continuation contexts pending
  | initializeSlot i o deps fields found pending safeDeps _ =>
      exact ⟨initialize_preserves s i o deps fields valid found pending safeDeps,
        initialize_preserves_publication s i o deps fields exposed found pending,
        initialize_preserves_backing s i o deps fields backing found pending, unique, contexts⟩
  | publish group ready =>
      exact ⟨valid, publish_group_preserves s group exposed ready, backing, unique, contexts⟩
  | drop group noIncoming =>
      exact ⟨valid, drop_access_preserves s group exposed noIncoming, backing, unique, contexts⟩

theorem construction_trace_preserves (s finish : State nr no nt)
    (invariant : Invariant s) (trace : ConstructionTrace s finish) : Invariant finish := by
  induction trace with
  | refl => exact invariant
  | next s mid finish step rest ih =>
      exact ih (construction_step_preserves s mid invariant step)


/-- A closed owner must not occur in active, captured or return-frame selection state. -/
def NoClosingContext (s : State nr no nt) (r : Fin nr) : Prop :=
  s.selected ≠ some r ∧
  (∀ p, s.pending = some p → p.selected ≠ r ∧ p.continuationContext ≠ some r) ∧
  (∀ t c, s.tickets t = some c → c.selected ≠ some r ∧
    ∀ p, c.pending = some p → p.selected ≠ r ∧ p.continuationContext ≠ some r) ∧
  ∀ frame, frame ∈ s.returnContexts → frame.1 ≠ some r ∧
    ∀ p, frame.2 = some p → p.selected ≠ r ∧ p.continuationContext ≠ some r

theorem close_option_live (s : State nr no nt) (r : Fin nr) (info : Region nr)
    (context : Option (Fin nr)) (safe : OptionLive s context)
    (avoids : context ≠ some r) : OptionLive (closeRegion s r info) context := by
  intro q selected
  have different : q ≠ r := fun same => avoids (same ▸ selected)
  exact close_keeps_other_live s r q info different (safe q selected)

theorem close_pending_live (s : State nr no nt) (r : Fin nr) (info : Region nr)
    (pending : Option (Pending nr no)) (safe : PendingLive s pending)
    (avoids : ∀ p, pending = some p → p.selected ≠ r ∧ p.continuationContext ≠ some r) :
    PendingLive (closeRegion s r info) pending := by
  intro p found
  have old := safe p found
  have absent := avoids p found
  exact ⟨close_keeps_other_live s r p.selected info absent.1 old.1,
    close_option_live s r info p.continuationContext old.2 absent.2⟩

theorem close_preserves_contexts (s : State nr no nt) (r : Fin nr) (info : Region nr)
    (safe : SavedContextsSafe s) (absent : NoClosingContext s r) :
    SavedContextsSafe (closeRegion s r info) := by
  refine ⟨close_option_live s r info s.selected safe.1 absent.1,
    close_pending_live s r info s.pending safe.2.1 absent.2.1, ?_, ?_⟩
  · intro t c found
    have old := safe.2.2.1 t c found
    have noOwner := absent.2.2.1 t c found
    exact ⟨close_option_live s r info c.selected old.1 noOwner.1,
      close_pending_live s r info c.pending old.2 noOwner.2⟩
  · intro frame member
    have old := safe.2.2.2 frame member
    have noOwner := absent.2.2.2 frame member
    exact ⟨close_option_live s r info frame.1 old.1 noOwner.1,
      close_pending_live s r info frame.2 old.2 noOwner.2⟩

theorem close_preserves_backing (s : State nr no nt) (r : Fin nr) (info : Region nr)
    (safe : BackingSafe s) : BackingSafe (closeRegion s r info) := by
  intro i o found active
  cases original : s.objects i with
  | none => simp [closeRegion, original] at found
  | some old =>
    by_cases same : old.region = r
    · simp [closeRegion, original, same] at found
      subst o
      exact False.elim (active rfl)
    · simp [closeRegion, original, same] at found
      subst o
      rcases safe i old original active with ⟨request, reply, req, supplied, owner, admitted⟩
      rcases admitted with ⟨target, identity, extent, align, aligned, provider, atOwner, phase, pair⟩
      have different : request.owner ≠ r := by simpa [← owner] using same
      exact ⟨request, reply, req, supplied, owner, target, identity, extent, align, aligned,
        provider, by simpa [closeRegion, replace, different] using atOwner, phase, pair⟩

/-- Pop exactly the innermost active completion owner after its release returns normally. -/
def finishClose (s : State nr no nt) (r : Fin nr) (info : Region nr)
    (remaining : List (Fin nr)) : State nr no nt :=
  { closeRegion s r info with completionOrder := remaining }

theorem finish_close_preserves_ownership (s : State nr no nt) (r : Fin nr)
    (info : Region nr) (remaining : List (Fin nr)) (unique : OwnersUnique s)
    (top : s.completionOrder = r :: remaining) :
    OwnersUnique (finishClose s r info remaining) := by
  have tail : remaining.Nodup := (List.nodup_cons.mp (top ▸ unique.1)).2
  refine ⟨tail, ?_⟩
  intro t c found
  have old := unique.2 t c found
  refine ⟨old.1, ?_, old.2.2⟩
  intro q member inTail
  exact old.2.1 q member (top ▸ List.mem_cons_of_mem r inTail)

theorem finish_close_preserves (s : State nr no nt) (r : Fin nr) (info : Region nr)
    (remaining : List (Fin nr)) (invariant : Invariant s)
    (region : s.regions r = some info) (top : s.completionOrder = r :: remaining)
    (contexts : NoClosingContext s r) (uses : NoOutsideUsableDependency s r) :
    Invariant (finishClose s r info remaining) := by
  rcases invariant with ⟨valid, publicGraph, backing, unique, saved⟩
  exact ⟨close_preserves s r info valid region contexts.1,
    close_preserves_publication s r info publicGraph uses,
    close_preserves_backing s r info backing,
    finish_close_preserves_ownership s r info remaining unique top,
    close_preserves_contexts s r info saved contexts⟩

/-- Capture and resume preserve the whole construction kernel, not just physical residency. -/
theorem capture_preserves_invariant (s : State nr no nt) (t : Fin nt)
    (inside outside : List (Fin nr)) (handler : Option (Fin nr)) (cut : Nat)
    (invariant : Invariant s) (fresh : s.tickets t = none)
    (split : s.completionOrder = inside ++ outside) (handlerLive : OptionLive s handler) :
    Invariant (capture s t inside outside handler cut) := by
  rcases invariant with ⟨valid, publicGraph, backing, unique, saved⟩
  exact ⟨⟨valid.1, valid.2.1, handlerLive⟩, publicGraph, backing,
    capture_preserves_ownership s t inside outside handler cut unique fresh split,
    capture_preserves_contexts s t inside outside handler cut saved handlerLive⟩

theorem resume_preserves_invariant (s : State nr no nt) (t : Fin nt)
    (c : Captured nr no) (invariant : Invariant s) (ticket : s.tickets t = some c) :
    Invariant (resume s t c) := by
  rcases invariant with ⟨valid, publicGraph, backing, unique, saved⟩
  exact ⟨resume_preserves s t c valid (saved.2.2.1 t c ticket).1,
    publicGraph, backing, resume_preserves_ownership s t c unique ticket,
    resume_preserves_contexts s t c saved ticket⟩

/-- A private pending object cannot be read merely because storage exists. -/
theorem pending_not_readable (s : State nr no nt) (i : Fin no) (o : Object nr no)
    (found : s.objects i = some o) (pending : o.phase = .pending) : ¬ Readable s i := by
  intro readable
  rcases readable with ⟨other, same, phase⟩
  have eq : other = o := Option.some.inj (same.symm.trans found)
  subst other
  simp [pending] at phase

end Ash.Regions

#print axioms Ash.Regions.pending_not_readable


#print axioms Ash.Regions.reserve_preserves
#print axioms Ash.Regions.initialize_preserves
#print axioms Ash.Regions.refuse_preserves
#print axioms Ash.Regions.refusal_keeps_previous
#print axioms Ash.Regions.refusal_keeps_operand_history
#print axioms Ash.Regions.select_preserves
#print axioms Ash.Regions.selection_keeps_residency
#print axioms Ash.Regions.resume_consumes_ticket
#print axioms Ash.Regions.resume_preserves

#print axioms Ash.Regions.close_preserves
#print axioms Ash.Regions.close_retires_owned
#print axioms Ash.Regions.close_preserves_other_objects
#print axioms Ash.Regions.close_keeps_allocator_association

#print axioms Ash.Regions.reserve_preserves_publication
#print axioms Ash.Regions.initialize_preserves_publication
#print axioms Ash.Regions.refusal_preserves_publication
#print axioms Ash.Regions.publish_group_preserves
#print axioms Ash.Regions.public_read_is_initialized

#print axioms Ash.Regions.capture_preserves_ownership
#print axioms Ash.Regions.resume_preserves_ownership
#print axioms Ash.Regions.resume_keeps_outside_owners
#print axioms Ash.Regions.resume_saves_caller_context

#print axioms Ash.Regions.capture_conserves_owners
#print axioms Ash.Regions.resume_conserves_owners

#print axioms Ash.Regions.capture_preserves_contexts
#print axioms Ash.Regions.resume_preserves_contexts
#print axioms Ash.Regions.return_restores_safe_context

#print axioms Ash.Regions.request_preserves_backing
#print axioms Ash.Regions.supply_preserves_backing
#print axioms Ash.Regions.initialize_preserves_backing
#print axioms Ash.Regions.refusal_preserves_backing

#print axioms Ash.Regions.drop_access_preserves
#print axioms Ash.Regions.dropped_record_stays_physical
#print axioms Ash.Regions.close_preserves_publication

#print axioms Ash.Regions.request_preserves_contexts
#print axioms Ash.Regions.supply_preserves_contexts
#print axioms Ash.Regions.request_callback_context
#print axioms Ash.Regions.supply_returns_to_caller

#print axioms Ash.Regions.construction_step_preserves
#print axioms Ash.Regions.construction_trace_preserves

#print axioms Ash.Regions.finish_close_preserves
#print axioms Ash.Regions.capture_preserves_invariant
#print axioms Ash.Regions.resume_preserves_invariant
