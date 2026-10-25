import RegionTransitions

namespace Ash.Regions
variable {nr no nt : Nat}

/-- Once live, the full pair/state/discipline remains fixed, including after close. -/
theorem transition_keeps_published_pair (layout : Layout nr no) (m next : Machine nr no nt)
    (step : Transition layout m next) (r : Fin nr) (old : Region nr)
    (found : m.heap.regions r = some old) (live : old.phase = .live) :
    ∃ info, next.heap.regions r = some info ∧ info.association = old.association := by
  cases step <;> try exact ⟨old, found, rfl⟩
  case prepare target info fresh _ _ _ _ _ _ =>
    have different : r ≠ target := by intro same; subst r; simp [fresh] at found
    exact ⟨old, by simpa [updateMachineRegion, updateRegion, replace, different] using found, rfl⟩
  case enter target info pair atTarget phase _ =>
    have different : r ≠ target := by
      intro same
      subst r
      have eq : old = info := Option.some.inj (found.symm.trans atTarget)
      subst old
      simp [phase] at live
    exact ⟨old, by simpa [enterLive, activate, updateMachineRegion, updateRegion, replace, different] using found, rfl⟩
  case abortPrepare target info atTarget phase =>
    have different : r ≠ target := by
      intro same
      subst r
      have eq : old = info := Option.some.inj (found.symm.trans atTarget)
      subst old
      simp [phase] at live
    exact ⟨old, by simpa [updateMachineRegion, updateRegion, replace, different] using found, rfl⟩
  case finishClose target info rest c _ _ atTarget _ _ =>
    by_cases same : r = target
    · subst r
      have eq : old = info := Option.some.inj (found.symm.trans atTarget)
      subst old
      exact ⟨{ info with phase := .closed }, by simp [completeMachineClose, finishClose, closeRegion, replace], rfl⟩
    · exact ⟨old, by simpa [completeMachineClose, finishClose, closeRegion, replace, same] using found, rfl⟩

theorem context_query_is_live (layout : Layout nr no) (m : Machine nr no nt)
    (safe : Safe layout m) (r : Fin nr) (selected : m.heap.selected = some r) :
    Live m.heap r := safe.1.1.1.2.2 r selected

/-- Stored private progress is restored exactly, rather than rerunning operands. -/
theorem resumed_pending_exact (s : State nr no nt) (t : Fin nt) (c : Captured nr no) :
    (restoreFrames s t c).pending = c.pending ∧
    (restoreFrames s t c).operandHistory = s.operandHistory ∧
    (restoreFrames s t c).objects = s.objects := ⟨rfl, rfl, rfl⟩

/-- A one-shot capability cannot be used twice without a different fresh capture. -/
theorem full_resume_consumes (s : State nr no nt) (t : Fin nt) (c : Captured nr no) :
    (restoreFrames s t c).tickets t = none := by simp [restoreFrames, resume, replace]

/-- No usable whole or inline view can read a supplied but pending record. -/
theorem private_pending_has_no_view (layout : Layout nr no) (s : State nr no nt)
    (i : Fin no) (o : Object nr no) (found : s.objects i = some o) (pending : o.phase = .pending)
    (view : View no) (sameObject : view.object = i) : ¬ ViewSafe layout s view := by
  rintro ⟨other, atSlot, ready, _⟩
  rw [sameObject, found] at atSlot
  have eq : o = other := Option.some.inj atSlot
  subst other
  simp [Ready, pending] at ready

/-- Distinct registered IDs stand for contractually disjoint physical backing. -/
theorem distinct_registration_ids (s : State nr no nt) (i j : Fin no)
    (a b : Backing nr no) (ra rb : Requirements nr)
    (first : ReplyAdmitted s i ra a) (second : ReplyAdmitted s j rb b) (different : i ≠ j) :
    a.identity ≠ b.identity := by
  simpa [first.2.1, second.2.1] using different

end Ash.Regions

#print axioms Ash.Regions.transition_keeps_published_pair
#print axioms Ash.Regions.context_query_is_live
#print axioms Ash.Regions.resumed_pending_exact
#print axioms Ash.Regions.full_resume_consumes
#print axioms Ash.Regions.private_pending_has_no_view
#print axioms Ash.Regions.distinct_registration_ids
