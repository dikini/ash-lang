import DeclaredSourceRequests
import OpenOwnerUses

/-! Finite, capture-sensitive checks for outside continuation obligations.
This connects the existing internal-use checker to a selected handler's
capability. It does not replace protection, callback checks or effect budgets,
and is not yet inferred for every future source capture. -/
namespace Ash.OneShot.CaptureOwnerChecks
open ScopedExpressions ScopedExecution CoherentSourceTypes ProtectionContracts
open DeclaredSourceStates (CheckedState)

/-- Resumption preserves pending work. Disposal additionally requires every
pending owner to belong to the actual recursively owned captured region. -/
def checkOwnerUses (disposes : Bool) (capture : Control) : Bool :=
  !disposes || ClosingAdmission.checkInternalUses capture.liveTickets capture.pending

theorem check_owner_uses_iff : checkOwnerUses disposes capture = true ↔
    (disposes = true → InternalUses capture.liveTickets capture.pending) := by
  cases disposes <;> simp [checkOwnerUses, ClosingAdmission.check_internal_uses_iff]

/-- The operation's actual table entry determines which capability is checked.
A missing entry cannot be used to pass this check. -/
def checkSelected (table : List (Nat × ClauseContract)) (operation : Nat) (capture : Control) : Bool :=
  match lookup operation table with
  | none => false
  | some offered => checkOwnerUses offered.dispose capture

theorem selected_iff (found : lookup operation table = some offered) :
    checkSelected table operation capture = true ↔
      (offered.dispose = true → InternalUses capture.liveTickets capture.pending) := by
  simp only [checkSelected, found, check_owner_uses_iff]

/-- Reuse the established equivalence with externally demanded owners. The
separation premise comes from the existing unique-ownership capture theorem. -/
theorem selected_external_iff
    (found : lookup operation table = some offered)
    (interface : OpenOwnerUses.Interface policy tickets capture outside)
    (separate : ∀ owner ∈ ownedTickets capture, owner ∉ outside) :
    checkSelected table operation capture.erase = true ↔
      (offered.dispose = true → interface.external = []) := by
  rw [selected_iff found]
  exact forall_congr' (fun _ => (OpenOwnerUses.external_empty_iff_internal interface.source separate).symm)

/-- Source-use evidence identifies an actual obstruction; the successful
selected check must therefore deny disposal. -/
theorem selected_denies_external
    (found : lookup operation table = some offered)
    (interface : OpenOwnerUses.Interface policy tickets capture outside)
    (present : owner ∈ interface.external)
    (checked : checkSelected table operation capture.erase = true) : offered.dispose = false := by
  have blocked := OpenOwnerUses.outside_use_blocks_internal interface present
  cases mode : offered.dispose with
  | false => rfl
  | true => exact False.elim (blocked ((selected_iff found).mp checked mode))

/-- Projection through ordered composition is shared by both pending-use and
owned-boundary accounting. The runtime order itself is unchanged. -/
theorem append_projections (first second : Control) :
    (first.append second).pending = first.pending ++ second.pending ∧
    (first.append second).liveTickets = first.liveTickets ++ second.liveTickets := by
  induction first <;> simp_all [Control.append, Control.pending, Control.liveTickets, List.append_assoc]

/-- Each side's pending work is checked against the combined owned region.
A rejection at a smaller cut need not survive when the cut includes its owner. -/
theorem composition_iff (first second : Control) : checkOwnerUses disposes (first.append second) = true ↔
    (disposes = true →
      InternalUses (first.liveTickets ++ second.liveTickets) first.pending ∧
      InternalUses (first.liveTickets ++ second.liveTickets) second.pending) := by
  rw [check_owner_uses_iff, (append_projections first second).1, (append_projections first second).2]
  apply forall_congr'
  intro _
  constructor
  · intro internal
    have parts := List.append_subset.mp (internalUses_subset internal)
    exact ⟨OpenOwnerUses.internal_of_subset parts.1, OpenOwnerUses.internal_of_subset parts.2⟩
  · rintro ⟨first, second⟩
    exact OpenOwnerUses.internal_of_subset (List.append_subset.mpr ⟨internalUses_subset first, internalUses_subset second⟩)

/-- At an outside-owner cut the finite selected check supplies exactly the
mode restriction needed by the already proved source-capture path. -/
theorem capture_outside_request
    (source : CheckedState operations policy contracts tables world outside scope
      (.perform (Instantiation.freezeEffect requested) operation operand) whole output demand row)
    (cut : HandlerCut requested whole capture tail handler)
    (isValue : operand.IsValue) (fresh : contracts owner = none)
    (external : ¬ InternalUses capture.erase.liveTickets capture.erase.pending)
    (checked : checkSelected (tables handler) operation capture.erase = true) :
    ∃ (contract : Owners.Contract) (after : Configuration) (nextDemand : List Nat) (nextRow : Footprint),
      contract.closeRow = none ∧
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩ after [.ticket owner] [] ∧
      CheckedState operations policy (contracts.insert owner contract) tables world outside
        after.scope after.expression after.stack output nextDemand nextRow ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack = owner :: ownedTickets whole := by
  apply DeclaredSourceRequests.capture_without_disposal_from_checked_request source cut isValue fresh (Or.inr external)
  cases found : lookup operation (tables handler) with
  | none => simp [checkSelected, found] at checked
  | some offered =>
    have denied : offered.dispose = false := by
      cases mode : offered.dispose with
      | false => rfl
      | true => exact False.elim (external ((selected_iff found).mp checked mode))
    simp only [Option.map_some, denied]

namespace Examples
open OpenOwnerUses.Examples (capture whole localHandler)

def disposalTable : List (Nat × ClauseContract) := [(0, ⟨true, some [], none⟩)]

def farHandler : HandlerData := ⟨73, .user 73 [], OpenOwnerUses.Examples.clauses, .none, .integer, rfl⟩
def farTail : Stack := .push (.handler farHandler) .nil
def expanded : Stack := whole.append farTail

theorem smaller_actual_cut : HandlerCut OpenOwnerUses.Examples.handled expanded capture
    (OpenOwnerUses.Examples.tail.append farTail) localHandler :=
  .push _ _ _ _ _ (by decide) (.hit localHandler _ rfl)

theorem larger_actual_cut : HandlerCut farHandler.effectInst expanded expanded .nil farHandler :=
  .push _ _ _ _ _ (by decide) (.push _ _ _ _ _ (by decide)
    (.live _ _ _ _ _ _ _ _ _ (.hit farHandler .nil rfl)))

theorem smaller_cut_rejects : checkSelected disposalTable 0 capture.erase = false := by decide

theorem larger_cut_accepts : checkSelected disposalTable 0 expanded.erase = true := by decide

theorem same_pending_work : capture.erase.pending = expanded.erase.pending := by decide

/-- This is deliberately an ownership-check example only. Passing it does
not supply protection, callback compatibility or a closing effect budget. -/
theorem resumption_preserves_outside_use :
    checkSelected ([(0, ⟨false, some [], some []⟩)] : List (Nat × ClauseContract)) 0 capture.erase = true := by decide

/-- The ordinary effect/protection check can pass this same request while
its outside-owner check rejects disposal. The latter is not redundant. -/
theorem effect_check_does_not_check_owners :
    checkRequest (CallableProtectionFrames.contextOf (fun _ => disposalTable) expanded)
      ⟨OpenOwnerUses.Examples.handled, 0, false⟩ = true ∧
    checkSelected disposalTable 0 capture.erase = false :=
  ⟨by decide, smaller_cut_rejects⟩

end Examples
end Ash.OneShot.CaptureOwnerChecks

#print axioms Ash.OneShot.CaptureOwnerChecks.check_owner_uses_iff
#print axioms Ash.OneShot.CaptureOwnerChecks.selected_iff
#print axioms Ash.OneShot.CaptureOwnerChecks.selected_external_iff
#print axioms Ash.OneShot.CaptureOwnerChecks.selected_denies_external
#print axioms Ash.OneShot.CaptureOwnerChecks.append_projections
#print axioms Ash.OneShot.CaptureOwnerChecks.composition_iff
#print axioms Ash.OneShot.CaptureOwnerChecks.capture_outside_request
#print axioms Ash.OneShot.CaptureOwnerChecks.Examples.smaller_actual_cut
#print axioms Ash.OneShot.CaptureOwnerChecks.Examples.larger_actual_cut
#print axioms Ash.OneShot.CaptureOwnerChecks.Examples.smaller_cut_rejects
#print axioms Ash.OneShot.CaptureOwnerChecks.Examples.larger_cut_accepts
#print axioms Ash.OneShot.CaptureOwnerChecks.Examples.same_pending_work
#print axioms Ash.OneShot.CaptureOwnerChecks.Examples.resumption_preserves_outside_use

#print axioms Ash.OneShot.CaptureOwnerChecks.Examples.effect_check_does_not_check_owners
