import OneShot

/-! Structural request and one-shot restoration interface for DN-0033.

This module packages the existing structural judgments at the request boundary.
It does not derive payload annotations from expressions, and its abstract close
plans are separate from the lexical runtime's cleanup admission. -/

namespace Ash.OneShot

variable {i : Instance} {whole cap tail front : Control}
  {payloadAccess ambient : List Nat} {q r a : Ty} {k : Nat}

/-- An admitted source cut, a well-formed predecessor and a fresh ticket
construct the live one-shot boundary.  Operand access remains an explicit
outside-support premise through `CaptureAdmission`. -/
theorem structural_capture
    (admission : CaptureAdmission i whole cap tail payloadAccess ambient)
    (valid : WellFormed whole q r ambient)
    (fresh : k ∉ whole.ticketNames) :
    ∃ a,
      WellFormed (Control.live k q a cap tail) a r ambient ∧
      payloadAccess ⊆ (Control.live k q a cap tail).visible ++ ambient ∧
      (Control.live k q a cap tail).owners = Owner.ticket k :: whole.owners := by
  cases admission with
  | checked selection payload =>
      obtain ⟨a, live⟩ := capture_wellFormed selection valid fresh
      exact ⟨a, live,
        admitted_capture_payload_available (.checked selection payload),
        capture_owner_accounting (sourceCut_is_cut selection)⟩

/-- Resumption uses the actual well-formed clause prefix.  It restores the
entire saved segment above that prefix, consumes exactly the selected ticket,
and preserves the full structural invariant. -/
theorem structural_resume
    (valid : WellFormed (front.append (Control.live k q a cap tail)) a r ambient) :
    WellFormed (cap.append (front.append (Control.spent k a tail))) q r ambient ∧
      (front.append (Control.live k q a cap tail)).owners.Perm
        (Owner.ticket k :: (cap.append (front.append (Control.spent k a tail))).owners) ∧
      Owner.ticket k ∉ (cap.append (front.append (Control.spent k a tail))).owners := by
  exact ⟨resume_wellFormed valid,
    resume_owner_accounting front cap tail,
    resume_removes_ticket valid.unique⟩

/-- Disposal is checked against the actual clause prefix.  Its materialized
close plan preserves the structural invariant and the raw flow accounts for
the fresh close owner and the consumed ticket exactly. -/
theorem structural_discard
    (valid : WellFormed (front.append (Control.live k q a cap tail)) .unit r ambient)
    (admitted : Discardable cap (front.append (Control.spent k a tail)) plan)
    (fresh : Owner.close closeId ∉
      (front.append (Control.live k q a cap tail)).owners) :
    WellFormed ((planControl plan).append (.push (closeFrame closeId)
        (front.append (Control.spent k a tail)))) .unit r ambient ∧
      ((front.append (Control.live k q a cap tail)).owners ++ [Owner.close closeId]).Perm
        (((planControl plan).append (.push (closeFrame closeId)
          (front.append (Control.spent k a tail)))).owners ++ [Owner.ticket k]) := by
  have next := discard_wellFormed valid admitted fresh
  cases admitted with
  | checked closing uses =>
      have flow : Flow (front.append (Control.live k q a cap tail))
          ((planControl plan).append (.push (closeFrame closeId)
            (front.append (Control.spent k a tail))))
          [Owner.close closeId] [Owner.ticket k] :=
        .discard k closeId q a front cap tail plan (closes_constructs_raw_plan closing)
      exact ⟨next, flow_accounting flow⟩

/-- Finite structural execution preserves the ownership ledger.  Consequently
completion is unique, live and completed owners are disjoint, and a terminal
empty control has completed every issued owner. -/
theorem structural_execution_ownership
    (steps : Steps initial final) (initialLedger : Ledger initial) :
    Ledger final ∧
      final.completed.Nodup ∧
      (∀ owner, owner ∈ final.control.owners → owner ∉ final.completed) ∧
      (final.control = .nil → final.issued.Perm final.completed) := by
  have finalLedger := steps_preserve_ledger steps initialLedger
  refine ⟨finalLedger, ledger_no_double_completion finalLedger,
    fun owner live => ledger_no_live_completed_alias finalLedger live, ?_⟩
  intro terminal
  simpa [terminal, Control.owners] using finalLedger.1

end Ash.OneShot

#print axioms Ash.OneShot.structural_capture
#print axioms Ash.OneShot.structural_resume
#print axioms Ash.OneShot.structural_discard
#print axioms Ash.OneShot.structural_execution_ownership
