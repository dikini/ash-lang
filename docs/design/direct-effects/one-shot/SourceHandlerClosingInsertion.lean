import SourceHandlerSelection

/-! Connect exact selected captures to the finite closing-interference check.
Composition uses the existing recursive source scopes and closing judgment;
no whole-source successor check is assumed. -/
namespace Ash.OneShot.SourceHandlerClosingInsertion
open ScopedExpressions ProtectionContracts
open SourceDependencyCapture
open SourceRecursiveRoutes (Shape Closing)
open SourceHandlerRequirements (reaches)

theorem normal_append (front tail : Scope) :
    (front.append tail).shape.normal = front.shape.normal ++ tail.shape.normal := by
  induction front <;> simp_all [Scope.append, Scope.shape, Shape.normal]

theorem closing_append (front tail : Scope) :
    (front.append tail).shape.closing = front.shape.closing ++ tail.shape.closing := by
  induction front <;> simp_all [Scope.append, Scope.shape, Shape.closing, List.append_assoc]

/-- The prefix's callbacks use the tail's original and closing projections.
Saved branches remain in the same place and receive the same full suffix. -/
theorem closing_append_iff (front tail : Scope) :
    Closing outward (front.append tail).shape original surviving ↔
      Closing outward front.shape (tail.shape.normal ++ original) (tail.shape.closing ++ surviving) ∧
      Closing outward tail.shape original surviving := by
  induction front generalizing original surviving with
  | nil => exact ⟨fun checked => ⟨.nil, checked⟩, And.right⟩
  | plain dependencies rest ih | running rest ih =>
      constructor
      · intro checked
        cases checked with
        | plain next => obtain ⟨first, second⟩ := ih.mp next; exact ⟨.plain first, second⟩
      · rintro ⟨first, second⟩
        cases first with | plain next => exact .plain (ih.mpr ⟨next, second⟩)
  | handler effect table families rest ih =>
      constructor
      · intro checked
        cases checked with
        | handler next => obtain ⟨first, second⟩ := ih.mp next; exact ⟨.handler first, second⟩
      · rintro ⟨first, second⟩
        cases first with | handler next => exact .handler (ih.mpr ⟨next, second⟩)
  | cell identity rest ih =>
      constructor
      · intro checked
        cases checked with
        | cell next => obtain ⟨first, second⟩ := ih.mp next; exact ⟨.cell first, second⟩
      · rintro ⟨first, second⟩
        cases first with | cell next => exact .cell (ih.mpr ⟨next, second⟩)
  | spent owner rest ih =>
      constructor
      · intro checked
        cases checked with
        | spent next => obtain ⟨first, second⟩ := ih.mp next; exact ⟨.spent first, second⟩
      · rintro ⟨first, second⟩
        cases first with | spent next => exact .spent (ih.mpr ⟨next, second⟩)
  | cleanup needs callback rest ih =>
      constructor
      · intro checked
        cases checked with
        | cleanup routes next =>
            obtain ⟨first, second⟩ := ih.mp next
            exact ⟨.cleanup (by simpa only [normal_append, closing_append, List.append_assoc] using routes) first, second⟩
      · rintro ⟨first, second⟩
        cases first with
        | cleanup routes next =>
            exact .cleanup (by simpa only [normal_append, closing_append, List.append_assoc] using routes)
              (ih.mpr ⟨next, second⟩)
  | live owner saved rest ihSaved ihRest =>
      constructor
      · intro checked
        cases checked with
        | live inside outside =>
            obtain ⟨first, second⟩ := ihRest.mp outside
            exact ⟨.live (by simpa only [normal_append, closing_append, List.append_assoc] using inside) first, second⟩
      · rintro ⟨first, second⟩
        cases first with
        | live inside outside =>
            exact .live (by simpa only [normal_append, closing_append, List.append_assoc] using inside)
              (ihRest.mpr ⟨outside, second⟩)

theorem closing_handler_iff : Closing outward (.handler effect rest) original surviving ↔
    Closing outward rest original surviving := by
  constructor
  · intro checked; cases checked with | handler next => exact next
  · exact Closing.handler

/-- Exact interference inside an actual captured scope. Only callbacks in
the prefix before the insertion can acquire the new interpretation. -/
theorem inserted_closing_iff (front tail : Scope) :
    Closing outward (front.append (.handler effect table families tail)).shape original surviving ↔
      Closing outward (front.append tail).shape original surviving ∧
        SourceHandlerInterference.Shielded effect front.shape [] := by
  rw [closing_append_iff, closing_append_iff]
  simp only [Scope.shape, Shape.normal, Shape.closing, List.cons_append, closing_handler_iff]
  have interference := SourceHandlerInterference.closing_insert_iff front.shape []
    (outward := outward) (effect := effect) (original := tail.shape.normal ++ original)
    (surviving := tail.shape.closing ++ surviving)
  simp only [List.nil_append] at interference
  rw [interference]
  exact ⟨fun ⟨⟨first, safe⟩, second⟩ => ⟨⟨first, second⟩, safe⟩,
    fun ⟨⟨first, second⟩, safe⟩ => ⟨⟨first, safe⟩, second⟩⟩

theorem check_closing_inserted (front tail : Scope) :
    checkClosing outward (front.append (.handler effect table families tail)).shape original surviving =
      (checkClosing outward (front.append tail).shape original surviving &&
        SourceHandlerInterference.check effect front.shape []) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, check_closing_iff, SourceHandlerInterference.check_iff]
  exact inserted_closing_iff front tail

theorem inserted_held (front : Scope) :
    (front.append (.handler effect table families tail)).held = (front.append tail).held := by
  induction front <;> simp_all [Scope.append, Scope.held]

/-- A different-effect handler entering an existing capture keeps the
selected contract and protection mode. For a disposing clause, the finite
prefix interference check supplies precisely the additional closing premise. -/
theorem bypassed_guard_transport
    (passed : reaches requested front = true) (different : requested ≠ effect)
    (found : select requested operation outside = some (.handler captured tail contract modes))
    (checked : CaptureGuard outward (front.append outside) requested operation)
    (shielded : contract.dispose = true → SourceHandlerInterference.check effect front.shape [] = true) :
    CaptureGuard outward (front.append (.handler effect table families outside)) requested operation := by
  have before := SourceHandlerSelection.selected_outside passed found
  have after := SourceHandlerSelection.inserted_bypassed (table := table) (families := families) passed different found
  cases checked with
  | builtin actual => cases Option.some.inj (before.symm.trans actual)
  | handler actual permission row body closing =>
      cases Option.some.inj (before.symm.trans actual)
      have held := inserted_held (effect := effect) (table := table) (families := families) (tail := captured) front
      exact .handler after (held ▸ permission) (held ▸ row) (held ▸ body)
        (fun disposes => (inserted_closing_iff front captured).mpr
          ⟨closing disposes, SourceHandlerInterference.check_iff.mp (shielded disposes)⟩)

namespace Examples
open SourceDependencyCapture.Examples (resumeTable resumeDependencies disposeTable disposeDependencies)

private def F : Instance := .cell 4
private def G : Instance := .user 5 []
private def waiting : Scope := .handler G disposeTable disposeDependencies .nil
private def shielded : Scope := .cleanup [F] .pure (.cell 4 .nil)
private def exposed : Scope := .cleanup [F] .pure .nil

/-- The inserted handler shares the callback's effect, but a nearer builtin
keeps the original interpretation and permits the existing disposing capture. -/
theorem shielded_guard :
    checkCapture [] (shielded.append (.handler F resumeTable resumeDependencies waiting)) G 0 = true := by
  apply check_capture_iff.mpr
  exact bypassed_guard_transport (front := shielded) (outside := waiting) rfl (by decide) rfl
    (check_capture_iff.mp rfl) (fun _ => rfl)

/-- Even a complete resumptive inserted handler can invalidate a different
operation's disposing capture by intercepting an armed callback's effect. -/
theorem exposed_guard_rejected : checkCapture [F] (exposed.append waiting) G 0 = true ∧
    checkCapture [F] (exposed.append (.handler F resumeTable resumeDependencies waiting)) G 0 = false :=
  ⟨rfl, rfl⟩

end Examples

end Ash.OneShot.SourceHandlerClosingInsertion

#print axioms Ash.OneShot.SourceHandlerClosingInsertion.normal_append
#print axioms Ash.OneShot.SourceHandlerClosingInsertion.closing_append
#print axioms Ash.OneShot.SourceHandlerClosingInsertion.closing_append_iff
#print axioms Ash.OneShot.SourceHandlerClosingInsertion.closing_handler_iff
#print axioms Ash.OneShot.SourceHandlerClosingInsertion.inserted_closing_iff
#print axioms Ash.OneShot.SourceHandlerClosingInsertion.check_closing_inserted
#print axioms Ash.OneShot.SourceHandlerClosingInsertion.inserted_held
#print axioms Ash.OneShot.SourceHandlerClosingInsertion.bypassed_guard_transport
#print axioms Ash.OneShot.SourceHandlerClosingInsertion.Examples.shielded_guard
#print axioms Ash.OneShot.SourceHandlerClosingInsertion.Examples.exposed_guard_rejected
