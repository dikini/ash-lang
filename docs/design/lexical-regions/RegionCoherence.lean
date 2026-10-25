import RegionProperties

namespace Ash.Regions
variable {nr no nt : Nat}

/-- Preparing and live service records retain operational views, not arbitrary dead bytes. -/
theorem update_service_contexts (s : State nr no nt) (r : Fin nr) (info : Region nr)
    (safe : ServiceContextsSafe s) (inactive : ¬ Live s r)
    (setup : (info.phase = .preparing ∨ info.phase = .live) → OptionLive s info.precedingContext) :
    ServiceContextsSafe (updateRegion s r info) := by
  intro q provider found active
  by_cases same : q = r
  · subst q
    simp [updateRegion, replace] at found
    subst provider
    exact update_option_live s r info inactive info.precedingContext (setup active)
  · have old : s.regions q = some provider := by simpa [updateRegion, replace, same] using found
    exact update_option_live s r info inactive provider.precedingContext (safe q provider old active)

theorem close_service_contexts (s : State nr no nt) (r : Fin nr) (info : Region nr)
    (safe : ServiceContextsSafe s) (absent : NoProviderContext s r) :
    ServiceContextsSafe (closeRegion s r info) := by
  intro q provider found active
  have different : q ≠ r := by
    intro same
    subst q
    simp [closeRegion, replace] at found
    subst provider
    simp at active
  have old : s.regions q = some provider := by simpa [closeRegion, replace, different] using found
  exact close_option_live s r info provider.precedingContext (safe q provider old active)
    (absent q provider old active)

theorem transition_service_contexts (layout : Layout nr no) (m next : Machine nr no nt)
    (safe : Safe layout m) (services : ServiceContextsSafe m.heap)
    (step : Transition layout m next) : ServiceContextsSafe next.heap := by
  cases step <;> try exact services
  case prepare r info fresh phase savedContext _ _ _ _ =>
    have inactive : ¬ Live m.heap r := by rintro ⟨other, found, _⟩; simp [fresh] at found
    apply update_service_contexts m.heap r info services inactive
    intro _
    simpa [savedContext] using safe.1.1.2.2.2.2.1
  case enter r info pair found phase _ =>
    have inactive : ¬ Live m.heap r := by
      rintro ⟨other, atSlot, live⟩
      have same : other = info := Option.some.inj (atSlot.symm.trans found)
      subst other
      simp [phase] at live
    exact update_service_contexts m.heap r { info with phase := .live, association := pair }
      services inactive (fun _ => services r info found (Or.inl phase))
  case abortPrepare r info found phase =>
    have inactive : ¬ Live m.heap r := by
      rintro ⟨other, atSlot, live⟩
      have same : other = info := Option.some.inj (atSlot.symm.trans found)
      subst other
      simp [phase] at live
    apply update_service_contexts m.heap r { info with phase := .closed } services inactive
    intro impossible
    simp at impossible
  case finishClose r info rest c _ _ _ _ ready =>
    exact close_service_contexts m.heap r info services ready.providers

def NoReturnedCursors (m : Machine nr no nt) : Prop :=
  ∀ r c, m.closing r = some c → c.release ≠ .returned

theorem transition_no_returned_cursor (layout : Layout nr no) (m next : Machine nr no nt)
    (noneReturned : NoReturnedCursors m) (step : Transition layout m next) :
    NoReturnedCursors next := by
  cases step <;> try exact noneReturned
  case beginClose r info rest actions _ _ _ _ _ =>
    intro q c found
    by_cases same : q = r
    · subst q
      simp [beginClose, replace] at found
      subst c
      intro impossible
      cases impossible
    · exact noneReturned q c (by simpa [beginClose, replace, same] using found)
  case cleanup r c cursor _ _ _ notReturned _ =>
    intro q candidate found
    by_cases same : q = r
    · subst q
      simp [advanceCleanup, replace] at found
      subst candidate
      exact notReturned
    · exact noneReturned q candidate (by simpa [advanceCleanup, replace, same] using found)
  case finishClose r info rest c _ _ _ _ _ =>
    intro q cursor found
    have different : q ≠ r := by intro same; subst q; simp [completeMachineClose, replace] at found
    exact noneReturned q cursor (by simpa [completeMachineClose, replace, different] using found)

/-- The overall state predicate includes retained service views and excludes returned/live gaps. -/
def Coherent (layout : Layout nr no) (m : Machine nr no nt) : Prop :=
  Safe layout m ∧ ServiceContextsSafe m.heap ∧ NoReturnedCursors m

theorem transition_coherent_preserves (layout : Layout nr no) (m next : Machine nr no nt)
    (coherent : Coherent layout m) (step : Transition layout m next) : Coherent layout next :=
  ⟨transition_preserves layout m next coherent.1 step,
    transition_service_contexts layout m next coherent.1 coherent.2.1 step,
    transition_no_returned_cursor layout m next coherent.2.2 step⟩

theorem trace_coherent_preserves (layout : Layout nr no) (m finish : Machine nr no nt)
    (coherent : Coherent layout m) (trace : Trace layout m finish) : Coherent layout finish := by
  induction trace with
  | refl => exact coherent
  | next m mid finish step rest ih => exact ih (transition_coherent_preserves layout m mid coherent step)

/-- Running release denies access even though retirement waits for its normal successful return. -/
theorem running_release_unavailable (m : Machine nr no nt) (r : Fin nr) (c : CloseCursor nr)
    (found : m.closing r = some c) (running : c.release = .running) : ¬ OwnerAvailable m r :=
  fun available => (available c found) running

theorem publication_history_persists_after_drop (s : State nr no nt) (group drop : List (Fin no))
    (i : Fin no) (member : i ∈ group) :
    (dropAccess (publishGroup s group) drop).publishedOnce i = true := by
  simp [dropAccess, publishGroup, member]

theorem published_record_cannot_republish (s : State nr no nt) (group drop : List (Fin no))
    (i : Fin no) (member : i ∈ group) :
    ¬ GroupReady (dropAccess (publishGroup s group) drop) [i] := by
  intro ready
  have fresh := ready.1 i (List.mem_singleton_self i)
  simp [publication_history_persists_after_drop s group drop i member] at fresh

end Ash.Regions

#print axioms Ash.Regions.update_service_contexts
#print axioms Ash.Regions.close_service_contexts
#print axioms Ash.Regions.transition_service_contexts
#print axioms Ash.Regions.transition_no_returned_cursor
#print axioms Ash.Regions.transition_coherent_preserves
#print axioms Ash.Regions.trace_coherent_preserves
#print axioms Ash.Regions.running_release_unavailable
#print axioms Ash.Regions.publication_history_persists_after_drop
#print axioms Ash.Regions.published_record_cannot_republish
