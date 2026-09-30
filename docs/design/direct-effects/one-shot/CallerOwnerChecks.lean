import OwnerOfferContexts

/-! Factor an outward capture's owner check through a locally closed prefix.
Existing usage and unique-ownership judgments supply the separation premises.
This is the callable-boundary composition result, not a proof that every
function execution maintains the required local interface. -/
namespace Ash.OneShot.CallerOwnerChecks
open ScopedExecution

/-- An internally used prefix cannot change a later region's owner decision
when that region cannot refer to the prefix's owners. Reuse ordered composition. -/
theorem internal_prefix_neutral {first second : Control}
    (internal : InternalUses first.liveTickets first.pending)
    (separate : ∀ owner ∈ second.pending, owner ∉ first.liveTickets) :
    CaptureOwnerChecks.checkOwnerUses disposes (first.append second) =
      CaptureOwnerChecks.checkOwnerUses disposes second := by
  apply Bool.eq_iff_iff.mpr
  rw [CaptureOwnerChecks.composition_iff, CaptureOwnerChecks.check_owner_uses_iff]
  constructor
  · intro checked mode
    apply OpenOwnerUses.internal_of_subset
    intro owner pending
    exact (List.mem_append.mp (internalUses_subset (checked mode).2 pending)).resolve_left
      (separate owner pending)
  · intro checked mode
    exact ⟨OpenOwnerUses.internal_of_subset (fun _ pending =>
        List.mem_append_left _ (internalUses_subset internal pending)),
      OpenOwnerUses.internal_of_subset (fun _ pending =>
        List.mem_append_right _ (internalUses_subset (checked mode) pending))⟩

theorem selected_prefix_neutral {first second : Control}
    (internal : InternalUses first.liveTickets first.pending)
    (separate : ∀ owner ∈ second.pending, owner ∉ first.liveTickets) :
    CaptureOwnerChecks.checkSelected table operation (first.append second) =
      CaptureOwnerChecks.checkSelected table operation second := by
  unfold CaptureOwnerChecks.checkSelected
  cases found : ProtectionContracts.lookup operation table with
  | none => rfl
  | some offered => exact internal_prefix_neutral internal separate

/-- Empty external usage is structural evidence of local ownership closure;
no new induction over captured ownership is needed. -/
theorem closed_prefix_internal (runtime : StackUsage policy tickets callee [] demand) :
    InternalUses callee.erase.liveTickets callee.erase.pending := by
  apply OpenOwnerUses.internal_of_subset
  simpa only [List.append_nil] using OpenOwnerUses.pending_access runtime

/-- Usage bounds the caller capture's pending names by its own region and
surviving tail. Global unique ownership separates both from the callee prefix. -/
theorem caller_pending_separate {callee : Stack}
    (runtime : StackUsage policy tickets capture (activeTickets tail) demand)
    (unique : (ownedTickets (callee.append (capture.append tail))).Nodup) :
    ∀ owner ∈ capture.erase.pending, owner ∉ callee.erase.liveTickets := by
  rw [owned_tickets_append] at unique
  have distinct := (List.nodup_append.mp unique).2.2
  intro owner pending localOwner
  have later : owner ∈ ownedTickets (capture.append tail) := by
    rw [owned_tickets_append]
    rcases List.mem_append.mp (OpenOwnerUses.pending_access runtime pending) with captured | surviving
    · exact List.mem_append_left _ (recursive_live_tickets_owned capture captured)
    · exact List.mem_append_right _ (active_tickets_owned tail surviving)
  exact distinct owner (recursive_live_tickets_owned callee localOwner) owner later rfl

theorem scoped_selected_neutral
    (localUsage : StackUsage localPolicy localTickets callee [] localDemand)
    (callerUsage : StackUsage policy tickets capture (activeTickets tail) callerDemand)
    (unique : (ownedTickets (callee.append (capture.append tail))).Nodup) :
    CaptureOwnerChecks.checkSelected table operation (callee.append capture).erase =
      CaptureOwnerChecks.checkSelected table operation capture.erase := by
  simpa only [erase_append] using selected_prefix_neutral
    (table := table) (operation := operation) (closed_prefix_internal localUsage)
    (caller_pending_separate callerUsage unique)

/-- Extend an existing actual cut through a prefix that does not interpret
this request. Only this structural cut extension needs a new induction. -/
theorem prepend_cut {callee : Stack} (cut : HandlerCut requested caller capture tail handler)
    (unresolved : callee.erase.resolve requested = none) :
    HandlerCut requested (callee.append caller) (callee.append capture) tail handler := by
  induction callee with
  | nil => exact cut
  | push frame rest ih =>
      have first : frame.erase.resolve requested = none := by
        cases found : frame.erase.resolve requested <;> simp_all [Stack.erase, Control.resolve]
      have next : rest.erase.resolve requested = none := by
        simpa only [Stack.erase, Control.resolve, first] using unresolved
      exact .push _ _ _ _ _ (ScopedTyping.frame_target_miss_of_resolution_none frame.erase first) (ih next)
  | live owner input answer saved scope rest ihSaved ihRest =>
      exact .live _ _ _ _ _ _ _ _ _ (ihRest unresolved)
  | spent owner answer scope rest ih => exact .spent _ _ _ _ _ _ _ (ih unresolved)

/-- At an outward request the actual selected capability has the same
owner check with or without the locally closed callee region. All extra
premises are existing structural usage, resolution and ownership judgments. -/
theorem outward_owner_check
    (localUsage : StackUsage localPolicy localTickets callee [] localDemand)
    (callerUsage : StackUsage policy tickets caller [] callerDemand)
    (unique : (ownedTickets (callee.append caller)).Nodup)
    (cut : HandlerCut requested caller capture tail handler)
    (unresolved : callee.erase.resolve requested = none) :
    OwnerOfferContexts.checkOwner requested operation (OwnerOfferContexts.ofStack tables (callee.append caller)) =
      OwnerOfferContexts.checkOwner requested operation (OwnerOfferContexts.ofStack tables caller) := by
  rw [OwnerOfferContexts.check_cut (prepend_cut cut unresolved), OwnerOfferContexts.check_cut cut]
  obtain ⟨interface, remaining, same, rest, accessible⟩ := OpenOwnerUses.capture_interface cut callerUsage
  have captured : StackUsage policy tickets capture (activeTickets tail) interface.demand := by
    simpa only [List.append_nil] using interface.source
  rw [handler_cut_reconstructs cut] at unique
  exact scoped_selected_neutral localUsage captured unique

namespace Examples
open ControlUsageExamples (abandonedTicket)

def localPart : Stack := .live 3 .unit .unit abandonedTicket .none .nil

theorem local_interface : ∃ demand,
    StackUsage ControlUsageExamples.policy ControlUsageExamples.tickets localPart [] demand := by
  obtain ⟨currentDemand, controlDemand, code, control, accessible, balance, unique⟩ :=
    ControlUsageExamples.internal_ticket_disposal_source
  exact ⟨controlDemand, control⟩

/-- Reuse the earlier outside-owner obstruction and a separate existing
nested-owned region. Adding that region cannot make disposal skip owner 9. -/
theorem outside_obstruction_survives :
    OwnerOfferContexts.checkOwner OpenOwnerUses.Examples.handled 0
      (OwnerOfferContexts.ofStack (fun _ => CaptureOwnerChecks.Examples.disposalTable)
        (localPart.append OpenOwnerUses.Examples.whole)) = false := by
  obtain ⟨localDemand, localUsage⟩ := local_interface
  obtain ⟨currentDemand, callerDemand, code, callerUsage, accessible, balance, unique⟩ :=
    OpenOwnerUses.Examples.request_usage
  rw [outward_owner_check localUsage callerUsage (by decide)
    OpenOwnerUses.Examples.selected_cut (by decide)]
  rw [OwnerOfferContexts.check_cut OpenOwnerUses.Examples.selected_cut]
  exact CaptureOwnerChecks.Examples.smaller_cut_rejects

end Examples
end Ash.OneShot.CallerOwnerChecks

#print axioms Ash.OneShot.CallerOwnerChecks.internal_prefix_neutral
#print axioms Ash.OneShot.CallerOwnerChecks.selected_prefix_neutral
#print axioms Ash.OneShot.CallerOwnerChecks.closed_prefix_internal
#print axioms Ash.OneShot.CallerOwnerChecks.caller_pending_separate
#print axioms Ash.OneShot.CallerOwnerChecks.scoped_selected_neutral
#print axioms Ash.OneShot.CallerOwnerChecks.prepend_cut
#print axioms Ash.OneShot.CallerOwnerChecks.outward_owner_check
#print axioms Ash.OneShot.CallerOwnerChecks.Examples.local_interface
#print axioms Ash.OneShot.CallerOwnerChecks.Examples.outside_obstruction_survives
