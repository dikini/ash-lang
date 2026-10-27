import RegionFrames

/- Complete bounded transition composition; provider and Core admission assumptions
are individual local guards, never the safety of the entire successor state. -/
namespace Ash.Regions

variable {nr no nt : Nat}

def Safe (layout : Layout nr no) (m : Machine nr no nt) : Prop :=
  MachineSafe layout m ∧ TicketFramesSafe m.heap

def saveMachineFrames (m : Machine nr no nt) (t : Fin nt) (c : Captured nr no)
    (inside outside : List (Option (Fin nr) × Option (Pending nr no)))
    (insideCuts outsideCuts : List Nat) : Machine nr no nt :=
  { m with heap := saveFrames m.heap t c inside outside insideCuts outsideCuts }

theorem save_machine_frames_preserves (layout : Layout nr no) (m : Machine nr no nt)
    (t : Fin nt) (c : Captured nr no)
    (inside outside : List (Option (Fin nr) × Option (Pending nr no)))
    (insideCuts outsideCuts : List Nat) (safe : Safe layout m)
    (ticket : m.heap.tickets t = some c) (split : m.heap.returnContexts = inside ++ outside) :
    Safe layout (saveMachineFrames m t c inside outside insideCuts outsideCuts) := by
  rcases safe with ⟨machine, frames⟩
  rcases machine.1 with ⟨valid, publicGraph, backing, unique, contexts⟩
  have saved := save_frames_contexts m.heap t c inside outside insideCuts outsideCuts ticket contexts split
  refine ⟨⟨⟨valid, publicGraph, backing,
    save_frames_unique m.heap t c inside outside insideCuts outsideCuts ticket unique, saved⟩,
    machine.2.1, ?_, machine.2.2.2.1, ?_⟩,
    save_frames_safe m.heap t c inside outside insideCuts outsideCuts ticket contexts frames split⟩
  · intro r owned
    exact machine.2.2.1 r ((save_frames_owners m.heap t c inside outside insideCuts outsideCuts ticket r).mp owned)
  · intro r cursor found
    have old := machine.2.2.2.2 r cursor found
    exact ⟨old.1, old.2.1,
      (save_frames_owners m.heap t c inside outside insideCuts outsideCuts ticket r).mpr old.2.2⟩

def captureFull (m : Machine nr no nt) (t : Fin nt)
    (innerOwners outerOwners : List (Fin nr)) (handler : Option (Fin nr)) (cut : Nat)
    (inside outside : List (Option (Fin nr) × Option (Pending nr no)))
    (insideCuts outsideCuts : List Nat) : Machine nr no nt :=
  let captured : Captured nr no :=
    { selected := m.heap.selected, pending := m.heap.pending,
      completionOrder := innerOwners, cut := m.heap.currentCut }
  saveMachineFrames (captureMachine m t innerOwners outerOwners handler cut)
    t captured inside outside insideCuts outsideCuts

theorem capture_full_preserves (layout : Layout nr no) (m : Machine nr no nt)
    (t : Fin nt) (innerOwners outerOwners : List (Fin nr)) (handler : Option (Fin nr)) (cut : Nat)
    (inside outside : List (Option (Fin nr) × Option (Pending nr no)))
    (insideCuts outsideCuts : List Nat) (safe : Safe layout m)
    (fresh : m.heap.tickets t = none) (owners : m.heap.completionOrder = innerOwners ++ outerOwners)
    (handlerLive : OptionLive m.heap handler) (split : m.heap.returnContexts = inside ++ outside) :
    Safe layout (captureFull m t innerOwners outerOwners handler cut inside outside insideCuts outsideCuts) := by
  have base := capture_machine_preserves layout m t innerOwners outerOwners handler cut safe.1 fresh owners handlerLive
  have ticketFrames : TicketFramesSafe (captureMachine m t innerOwners outerOwners handler cut).heap := by
    intro u c found frame member
    by_cases same : u = t
    · subst u
      simp [captureMachine, capture, replace] at found
      subst c
      cases member
    · exact safe.2 u c (by simpa [captureMachine, capture, replace, same] using found) frame member
  apply save_machine_frames_preserves layout _ t _ inside outside insideCuts outsideCuts ⟨base, ticketFrames⟩
  · simp [captureMachine, capture, replace]
  · exact split

def resumeFull (m : Machine nr no nt) (t : Fin nt) (c : Captured nr no) : Machine nr no nt :=
  { m with heap := restoreFrames m.heap t c }

theorem resume_full_preserves (layout : Layout nr no) (m : Machine nr no nt)
    (t : Fin nt) (c : Captured nr no) (safe : Safe layout m)
    (ticket : m.heap.tickets t = some c) : Safe layout (resumeFull m t c) := by
  have base := resume_machine_preserves layout m t c safe.1 ticket
  have contexts := restore_frames_contexts m.heap t c safe.1.1.2.2.2.2 safe.2 ticket
  refine ⟨⟨⟨base.1.1, base.1.2.1, base.1.2.2.1, base.1.2.2.2.1, contexts⟩,
    base.2.1, base.2.2.1, base.2.2.2.1, base.2.2.2.2⟩,
    restore_frames_tickets m.heap t c safe.2⟩

/-- Closing also checks views saved in captured service-frame prefixes. -/
def CapturedFramesAvoid (s : State nr no nt) (r : Fin nr) : Prop :=
  ∀ t c, s.tickets t = some c → ∀ frame, frame ∈ c.frames →
    frame.1 ≠ some r ∧ ∀ p, frame.2 = some p → p.selected ≠ r ∧ p.continuationContext ≠ some r

/-- A live/preparing owner retains its operational provider context, unlike dead object bits. -/
def ServiceContextsSafe (s : State nr no nt) : Prop :=
  ∀ r info, s.regions r = some info →
    (info.phase = .preparing ∨ info.phase = .live) → OptionLive s info.precedingContext

def NoProviderContext (s : State nr no nt) (r : Fin nr) : Prop :=
  ∀ q info, s.regions q = some info →
    (info.phase = .preparing ∨ info.phase = .live) → info.precedingContext ≠ some r

/-- These are current local release obligations, not successor-state safety. -/
structure ReleaseReady (layout : Layout nr no) (m : Machine nr no nt) (r : Fin nr) : Prop where
  contexts : NoClosingContext m.heap r
  uses : NoOutsideUsableDependency m.heap r
  children : NoLiveChild m.heap r
  views : ∀ i v, m.roots i = some v → ViewAvoids layout m.heap r v
  frames : CapturedFramesAvoid m.heap r
  providers : NoProviderContext m.heap r

def ReleaseReturning (c : CloseCursor nr) : Prop :=
  c.action = none ∧ c.remaining = [] ∧ c.release = .running

theorem close_full_frames (s : State nr no nt) (r : Fin nr) (info : Region nr)
    (safe : TicketFramesSafe s) (absent : CapturedFramesAvoid s r) :
    TicketFramesSafe (closeRegion s r info) := by
  intro t c found frame member
  have old := safe t c found frame member
  have avoids := absent t c found frame member
  exact ⟨close_option_live s r info frame.1 old.1 avoids.1,
    close_pending_live s r info frame.2 old.2 avoids.2⟩

theorem update_full_frames (s : State nr no nt) (r : Fin nr) (info : Region nr)
    (safe : TicketFramesSafe s) (inactive : ¬ Live s r) :
    TicketFramesSafe (updateRegion s r info) := by
  intro t c found frame member
  have old := safe t c found frame member
  exact ⟨update_option_live s r info inactive frame.1 old.1,
    update_pending_live s r info inactive frame.2 old.2⟩

theorem construction_full_preserves (layout : Layout nr no) (m : Machine nr no nt)
    (next : State nr no nt) (safe : Safe layout m) (step : ConstructionStep m.heap next)
    (roots : RootAdmission m.roots m.heap next) : Safe layout { m with heap := next } := by
  refine ⟨construction_preserves_machine layout m next safe.1 step roots, ?_⟩
  cases step <;> exact safe.2

/-- Discard may abandon private requests, but not an initialized object or unfinished close. -/
def FramesDiscardAllowed (s : State nr no nt) (c : Captured nr no) : Prop :=
  ∀ frame, frame ∈ c.frames → ∀ p, frame.2 = some p → s.objects p.object = none

/-- Concrete admitted transitions. No constructor takes Safe of its successor as a premise. -/
inductive Transition (layout : Layout nr no) : Machine nr no nt → Machine nr no nt → Prop where
  | prepare (m : Machine nr no nt) (r : Fin nr) (info : Region nr)
      (fresh : m.heap.regions r = none) (phase : info.phase = .preparing)
      (savedContext : info.precedingContext = m.heap.selected)
      (savedCut : info.providerCut = m.heap.currentCut)
      (ordered : ∀ parent, info.parent = some parent → parent.val < r.val)
      (parentLive : ∀ parent, info.parent = some parent → Live m.heap parent)
      (available : ∀ q, info.precedingContext = some q → OwnerAvailable m q) :
      Transition layout m (updateMachineRegion m r info)
  | enter (m : Machine nr no nt) (r : Fin nr) (info : Region nr) (pair : Association)
      (found : m.heap.regions r = some info) (phase : info.phase = .preparing)
      (parentLive : ∀ parent, info.parent = some parent → Live m.heap parent) :
      Transition layout m (enterLive m r info pair)
  | abortPrepare (m : Machine nr no nt) (r : Fin nr) (info : Region nr)
      (found : m.heap.regions r = some info) (phase : info.phase = .preparing) :
      Transition layout m (updateMachineRegion m r { info with phase := .closed })
  | request (m : Machine nr no nt) (i : Fin no) (request : Requirements nr) (owner : Region nr)
      (admitted : ConstructionStep m.heap (requestStorage m.heap i request owner))
      (freshBacking : FreshBacking m.heap i) (available : OwnerAvailable m request.owner) :
      Transition layout m { m with heap := requestStorage m.heap i request owner }
  | supply (m : Machine nr no nt) (i : Fin no) (request : Requirements nr)
      (reply : Backing nr no) (continuation : Pending nr no)
      (admitted : ConstructionStep m.heap (supplyStorage m.heap i request reply continuation))
      (freshBacking : FreshBacking m.heap i) (available : OwnerAvailable m request.owner) :
      Transition layout m { m with heap := supplyStorage m.heap i request reply continuation }
  | initializeSlot (m : Machine nr no nt) (i : Fin no) (o : Object nr no)
      (deps : List (Fin nr)) (fields : List (Fin no))
      (admitted : ConstructionStep m.heap (initializeSlot m.heap i o deps fields))
      (available : OwnerAvailable m o.region) :
      Transition layout m { m with heap := initializeSlot m.heap i o deps fields }
  | publish (m : Machine nr no nt) (group : List (Fin no)) (ready : GroupReady m.heap group)
      (privateGroup : ∀ i, i ∈ group → m.heap.exposed i = false)
      (available : ∀ i o, i ∈ group → m.heap.objects i = some o → OwnerAvailable m o.region) :
      Transition layout m { m with heap := publishGroup m.heap group }
  | dropAccess (m : Machine nr no nt) (group : List (Fin no))
      (noIncoming : NoIncomingUse m.heap group) (noRoots : NoWholeRoots m.roots group) :
      Transition layout m { m with heap := Ash.Regions.dropAccess m.heap group }
  | bind (m : Machine nr no nt) (slot : Fin no) (view : View no)
      (localView : ViewSafe layout m.heap view) (origin : ViewOrigin m view)
      (available : ViewAvailable layout m view) :
      Transition layout m (bindView m slot view)
  | unbind (m : Machine nr no nt) (slot : Fin no) : Transition layout m (unbindView m slot)
  | use (m : Machine nr no nt) (slot : Fin no) (usable : Usable layout m slot)
      (available : ∀ view, m.roots slot = some view → ViewAvailable layout m view) : Transition layout m m
  | call (m : Machine nr no nt) (slot : Fin no) (usable : Usable layout m slot)
      (available : ∀ view, m.roots slot = some view → ViewAvailable layout m view) : Transition layout m m
  | contextQuery (m : Machine nr no nt) (r : Fin nr) (selected : m.heap.selected = some r) (available : OwnerAvailable m r) :
      Transition layout m m
  | select (m : Machine nr no nt) (r : Fin nr) (live : Live m.heap r) (available : OwnerAvailable m r) :
      Transition layout m (selectMachine m r)
  | suspend (m : Machine nr no nt) : Transition layout m (suspendMachine m)
  | returnService (m : Machine nr no nt)
      (frame : Option (Fin nr) × Option (Pending nr no))
      (rest : List (Option (Fin nr) × Option (Pending nr no))) (cut : Nat) (cuts : List Nat)
      (top : m.heap.returnContexts = frame :: rest) (cutTop : m.heap.returnCuts = cut :: cuts)
      (noPending : m.heap.pending = none) : Transition layout m (returnMachine m frame rest cut cuts)
  | capture (m : Machine nr no nt) (t : Fin nt)
      (innerOwners outerOwners : List (Fin nr)) (handler : Option (Fin nr)) (cut : Nat)
      (inside outside : List (Option (Fin nr) × Option (Pending nr no)))
      (insideCuts outsideCuts : List Nat)
      (fresh : m.heap.tickets t = none)
      (owners : m.heap.completionOrder = innerOwners ++ outerOwners)
      (handlerLive : OptionLive m.heap handler)
      (frames : m.heap.returnContexts = inside ++ outside)
      (cuts : m.heap.returnCuts = insideCuts ++ outsideCuts)
      (frameCount : inside.length = insideCuts.length)
      (handlerAvailable : ∀ r, handler = some r → OwnerAvailable m r) :
      Transition layout m (captureFull m t innerOwners outerOwners handler cut inside outside insideCuts outsideCuts)
  | resume (m : Machine nr no nt) (t : Fin nt) (c : Captured nr no)
      (ticket : m.heap.tickets t = some c) : Transition layout m (resumeFull m t c)
  | discard (m : Machine nr no nt) (t : Fin nt) (c : Captured nr no)
      (ticket : m.heap.tickets t = some c) (admitted : DiscardAllowed m c)
      (privateFrames : FramesDiscardAllowed m.heap c) : Transition layout m (discardMachine m t c)
  | refuse (m : Machine nr no nt) (i : Fin no) (o : Object nr no)
      (found : m.heap.objects i = some o) (pending : o.phase = .pending)
      (noActiveRequest : m.heap.pending = none) : Transition layout m (refuseMachine m i)
  | refuseBeforeStorage (m : Machine nr no nt) (i : Fin no) (p : Pending nr no)
      (current : m.heap.pending = some p) (slot : p.object = i)
      (fresh : m.heap.objects i = none) (noBacking : m.heap.backing i = none) :
      Transition layout m (refuseMachine m i)
  | beginClose (m : Machine nr no nt) (r : Fin nr) (info : Region nr)
      (rest : List (Fin nr)) (actions : List Nat) (found : m.heap.regions r = some info)
      (live : info.phase = .live) (top : m.heap.completionOrder = r :: rest)
      (fresh : m.closing r = none) (recorded : actions = m.heap.cleanupActions r) :
      Transition layout m (Ash.Regions.beginClose m r info actions)
  | cleanup (m : Machine nr no nt) (r : Fin nr) (c next : CloseCursor nr)
      (found : m.closing r = some c) (active : ActiveCursor m r) (step : CleanupStep c next)
      (notReturned : next.release ≠ .returned)
      (beforeRelease : next.release = .running → ReleaseReady layout m r) :
      Transition layout m (advanceCleanup m r next)
  | finishClose (m : Machine nr no nt) (r : Fin nr) (info : Region nr) (rest : List (Fin nr))
      (c : CloseCursor nr) (cursor : m.closing r = some c) (returning : ReleaseReturning c)
      (region : m.heap.regions r = some info) (top : m.heap.completionOrder = r :: rest)
      (beforeReturn : ReleaseReady layout m r) :
      Transition layout m (completeMachineClose m r info rest)

theorem transition_preserves (layout : Layout nr no) (m next : Machine nr no nt)
    (safe : Safe layout m) (step : Transition layout m next) : Safe layout next := by
  cases step with
  | prepare r info fresh _ _ _ ordered parents _ =>
      have inactive : ¬ Live m.heap r := by rintro ⟨other, found, _⟩; simp [fresh] at found
      exact ⟨update_machine_region_preserves layout m r info safe.1 inactive ordered parents,
        update_full_frames m.heap r info safe.2 inactive⟩
  | enter r info pair found phase parents =>
      have inactive : ¬ Live m.heap r := by
        rintro ⟨other, atSlot, live⟩
        have same : other = info := Option.some.inj (atSlot.symm.trans found)
        subst other
        simp [phase] at live
      exact ⟨enter_live_preserves layout m r info pair safe.1 found phase parents,
        update_full_frames m.heap r { info with phase := .live, association := pair } safe.2 inactive⟩
  | abortPrepare r info found phase =>
      have inactive : ¬ Live m.heap r := by
        rintro ⟨other, atSlot, live⟩
        have same : other = info := Option.some.inj (atSlot.symm.trans found)
        subst other
        simp [phase] at live
      exact ⟨update_machine_region_preserves layout m r { info with phase := .closed } safe.1 inactive
          (fun parent enclosing => safe.1.1.1.2.1 r info parent found enclosing)
          (fun parent enclosing => safe.1.2.2.2.1 r info parent found (Or.inl phase) enclosing),
        update_full_frames m.heap r { info with phase := .closed } safe.2 inactive⟩
  | request i req owner admitted _ _ =>
      exact construction_full_preserves layout m _ safe admitted (fun _ _ _ _ visible => visible)
  | supply i req reply continuation admitted _ _ =>
      exact construction_full_preserves layout m _ safe admitted (fun _ _ _ _ visible => visible)
  | initializeSlot i o deps fields admitted _ =>
      exact construction_full_preserves layout m _ safe admitted (fun _ _ _ _ visible => visible)
  | publish group ready _ _ =>
      apply construction_full_preserves layout m _ safe (.publish m.heap group ready)
      intro i v _ _ visible
      simp [publishGroup, visible]
  | dropAccess group noIncoming noRoots =>
      apply construction_full_preserves layout m _ safe (.drop m.heap group noIncoming)
      intro i v found whole visible
      simp [Ash.Regions.dropAccess, noRoots i v found whole, visible]
  | bind slot view localView _ _ => exact ⟨bind_view_preserves layout m slot view safe.1 localView, safe.2⟩
  | unbind slot => exact ⟨unbind_view_preserves layout m slot safe.1, safe.2⟩
  | use _ _ _ => exact safe
  | call _ _ _ => exact safe
  | contextQuery _ _ _ => exact safe
  | select r live _ => exact ⟨select_machine_preserves layout m r safe.1 live, safe.2⟩
  | suspend => exact ⟨suspend_machine_preserves layout m safe.1, safe.2⟩
  | returnService frame rest cut cuts top _ _ =>
      exact ⟨return_machine_preserves layout m frame rest cut cuts safe.1 top, safe.2⟩
  | capture t inner outer handler cut inside outside insideCuts outsideCuts fresh owners handlerLive frames _ _ _ =>
      exact capture_full_preserves layout m t inner outer handler cut inside outside insideCuts outsideCuts
        safe fresh owners handlerLive frames
  | resume t c ticket => exact resume_full_preserves layout m t c safe ticket
  | discard t c ticket _ _ =>
      refine ⟨discard_machine_preserves layout m t c safe.1 ticket, ?_⟩
      intro u d found frame member
      have different : u ≠ t := by intro same; subst u; simp [discardMachine, discardSegment, replace] at found
      exact safe.2 u d (by simpa [discardMachine, discardSegment, replace, different] using found) frame member
  | refuse i o found pending _ => exact ⟨refuse_machine_preserves layout m i o safe.1 found pending, safe.2⟩
  | refuseBeforeStorage i p _ _ fresh _ =>
      exact ⟨refuse_empty_machine_preserves layout m i safe.1 fresh, safe.2⟩
  | beginClose r info rest actions found live top _ _ =>
      exact ⟨begin_close_preserves layout m r info rest actions safe.1 found live top, safe.2⟩
  | cleanup r c next found _ step _ _ =>
      exact ⟨advance_cleanup_preserves layout m r c next safe.1 found step, safe.2⟩
  | finishClose r info rest c _ _ region top ready =>
      exact ⟨complete_machine_close_preserves layout m r info rest safe.1 region top
          ready.contexts ready.uses ready.children ready.views,
        close_full_frames m.heap r info safe.2 ready.frames⟩

inductive Trace (layout : Layout nr no) : Machine nr no nt → Machine nr no nt → Prop where
  | refl (m) : Trace layout m m
  | next (m mid finish) (step : Transition layout m mid) (rest : Trace layout mid finish) :
      Trace layout m finish

theorem trace_preserves (layout : Layout nr no) (m finish : Machine nr no nt)
    (safe : Safe layout m) (trace : Trace layout m finish) : Safe layout finish := by
  induction trace with
  | refl => exact safe
  | next m mid finish step rest ih => exact ih (transition_preserves layout m mid safe step)

end Ash.Regions

#print axioms Ash.Regions.save_machine_frames_preserves
#print axioms Ash.Regions.capture_full_preserves
#print axioms Ash.Regions.resume_full_preserves
#print axioms Ash.Regions.close_full_frames
#print axioms Ash.Regions.update_full_frames
#print axioms Ash.Regions.construction_full_preserves
#print axioms Ash.Regions.transition_preserves
#print axioms Ash.Regions.trace_preserves
