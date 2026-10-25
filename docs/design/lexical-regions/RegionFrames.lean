import RegionControl

/- A captured segment owns its service-frame prefix; outside frames stay in place. -/
namespace Ash.Regions

variable {nr no nt : Nat}

def FrameSafe (s : State nr no nt) (frame : Option (Fin nr) × Option (Pending nr no)) : Prop :=
  OptionLive s frame.1 ∧ PendingLive s frame.2

def TicketFramesSafe (s : State nr no nt) : Prop :=
  ∀ t c, s.tickets t = some c → ∀ frame, frame ∈ c.frames → FrameSafe s frame

/-- Only saved-frame metadata changes; selected context and completion ownership stay exact. -/
def saveFrames (s : State nr no nt) (t : Fin nt) (c : Captured nr no)
    (inside outside : List (Option (Fin nr) × Option (Pending nr no)))
    (insideCuts outsideCuts : List Nat) : State nr no nt :=
  let captured := { c with frames := inside, frameCuts := insideCuts }
  { s with returnContexts := outside, returnCuts := outsideCuts,
           tickets := replace s.tickets t (some captured) }

theorem save_frames_owners (s : State nr no nt) (t : Fin nt) (c : Captured nr no)
    (inside outside : List (Option (Fin nr) × Option (Pending nr no)))
    (insideCuts outsideCuts : List Nat) (ticket : s.tickets t = some c) (r : Fin nr) :
    Owns (saveFrames s t c inside outside insideCuts outsideCuts) r ↔ Owns s r := by
  constructor
  · intro owned
    rcases owned with active | ⟨u, d, found, member⟩
    · exact Or.inl active
    · by_cases same : u = t
      · subst u
        simp [saveFrames, replace] at found
        subst d
        exact Or.inr ⟨t, c, ticket, member⟩
      · exact Or.inr ⟨u, d, by simpa [saveFrames, replace, same] using found, member⟩
  · intro owned
    rcases owned with active | ⟨u, d, found, member⟩
    · exact Or.inl active
    · by_cases same : u = t
      · subst u
        have eq : d = c := Option.some.inj (found.symm.trans ticket)
        subst d
        exact Or.inr ⟨t, { c with frames := inside, frameCuts := insideCuts },
          by simp [saveFrames, replace], member⟩
      · exact Or.inr ⟨u, d, by simpa [saveFrames, replace, same] using found, member⟩

theorem save_frames_unique (s : State nr no nt) (t : Fin nt) (c : Captured nr no)
    (inside outside : List (Option (Fin nr) × Option (Pending nr no)))
    (insideCuts outsideCuts : List Nat) (ticket : s.tickets t = some c)
    (unique : OwnersUnique s) :
    OwnersUnique (saveFrames s t c inside outside insideCuts outsideCuts) := by
  refine ⟨unique.1, ?_⟩
  intro u d found
  by_cases same : u = t
  · subst u
    simp [saveFrames, replace] at found
    subst d
    have old := unique.2 t c ticket
    refine ⟨old.1, old.2.1, ?_⟩
    intro v e different atSlot r member inOther
    have oldSlot : s.tickets v = some e := by simpa [saveFrames, replace, different] using atSlot
    exact old.2.2 v e different oldSlot r member inOther
  · have oldSlot : s.tickets u = some d := by simpa [saveFrames, replace, same] using found
    have old := unique.2 u d oldSlot
    refine ⟨old.1, old.2.1, ?_⟩
    intro v e different atSlot r member inOther
    by_cases newSlot : v = t
    · subst v
      simp [saveFrames, replace] at atSlot
      subst e
      exact old.2.2 t c different ticket r member inOther
    · exact old.2.2 v e different (by simpa [saveFrames, replace, newSlot] using atSlot) r member inOther

theorem save_frames_contexts (s : State nr no nt) (t : Fin nt) (c : Captured nr no)
    (inside outside : List (Option (Fin nr) × Option (Pending nr no)))
    (insideCuts outsideCuts : List Nat) (ticket : s.tickets t = some c)
    (safe : SavedContextsSafe s) (split : s.returnContexts = inside ++ outside) :
    SavedContextsSafe (saveFrames s t c inside outside insideCuts outsideCuts) := by
  refine ⟨safe.1, safe.2.1, ?_, ?_⟩
  · intro u d found
    by_cases same : u = t
    · subst u
      simp [saveFrames, replace] at found
      subst d
      exact safe.2.2.1 t c ticket
    · exact safe.2.2.1 u d (by simpa [saveFrames, replace, same] using found)
  · intro frame member
    exact safe.2.2.2 frame (split ▸ List.mem_append_right inside member)

theorem save_frames_safe (s : State nr no nt) (t : Fin nt) (c : Captured nr no)
    (inside outside : List (Option (Fin nr) × Option (Pending nr no)))
    (insideCuts outsideCuts : List Nat) (_ticket : s.tickets t = some c)
    (safe : SavedContextsSafe s) (previous : TicketFramesSafe s)
    (split : s.returnContexts = inside ++ outside) :
    TicketFramesSafe (saveFrames s t c inside outside insideCuts outsideCuts) := by
  intro u d found frame member
  by_cases same : u = t
  · subst u
    simp [saveFrames, replace] at found
    subst d
    exact safe.2.2.2 frame (split ▸ List.mem_append_left outside member)
  · exact previous u d (by simpa [saveFrames, replace, same] using found) frame member

/-- Restore the captured frame prefix above the one-shot return to the resumer. -/
def restoreFrames (s : State nr no nt) (t : Fin nt) (c : Captured nr no) : State nr no nt :=
  { resume s t c with returnContexts := c.frames ++ (s.selected, s.pending) :: s.returnContexts,
                      returnCuts := c.frameCuts ++ s.currentCut :: s.returnCuts }

theorem restore_frames_contexts (s : State nr no nt) (t : Fin nt) (c : Captured nr no)
    (safe : SavedContextsSafe s) (frames : TicketFramesSafe s) (ticket : s.tickets t = some c) :
    SavedContextsSafe (restoreFrames s t c) := by
  have restored := safe.2.2.1 t c ticket
  refine ⟨restored.1, restored.2, ?_, ?_⟩
  · intro u d found
    have different : u ≠ t := by intro same; subst u; simp [restoreFrames, resume, replace] at found
    exact safe.2.2.1 u d (by simpa [restoreFrames, resume, replace, different] using found)
  · intro frame member
    rcases List.mem_append.mp member with captured | active
    · exact frames t c ticket frame captured
    · rcases List.mem_cons.mp active with same | old
      · subst frame
        exact ⟨safe.1, safe.2.1⟩
      · exact safe.2.2.2 frame old

theorem restore_frames_tickets (s : State nr no nt) (t : Fin nt) (c : Captured nr no)
    (safe : TicketFramesSafe s) : TicketFramesSafe (restoreFrames s t c) := by
  intro u d found frame member
  have different : u ≠ t := by intro same; subst u; simp [restoreFrames, resume, replace] at found
  exact safe u d (by simpa [restoreFrames, resume, replace, different] using found) frame member

/-- The outer pending identity/progress and caller context are restored, not re-evaluated. -/
theorem nested_service_roundtrip (s : State nr no nt) :
    returnToCaller (suspendService s) (s.selected, s.pending) s.returnContexts
      s.currentCut s.returnCuts = s := by
  cases s
  rfl

theorem restored_frame_prefix (s : State nr no nt) (t : Fin nt) (c : Captured nr no) :
    (restoreFrames s t c).returnContexts =
      c.frames ++ (s.selected, s.pending) :: s.returnContexts := rfl

end Ash.Regions

#print axioms Ash.Regions.save_frames_owners
#print axioms Ash.Regions.save_frames_unique
#print axioms Ash.Regions.save_frames_contexts
#print axioms Ash.Regions.save_frames_safe
#print axioms Ash.Regions.restore_frames_contexts
#print axioms Ash.Regions.restore_frames_tickets
#print axioms Ash.Regions.nested_service_roundtrip
#print axioms Ash.Regions.restored_frame_prefix
