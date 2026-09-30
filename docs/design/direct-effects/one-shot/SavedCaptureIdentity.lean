import SourceOwnerClosure

/-! A historically issued ticket cannot acquire a different saved capture.
This connects the existing capture-location and uniqueness judgments across
actual execution. It does not assert that a discarded capture remains live,
and it does not add access or source-admission premises to raw transitions. -/
namespace Ash.OneShot.SavedCaptureIdentity
open ScopedExpressions ScopedExecution
open SourceTemplates (CapturedIn)

theorem located_append {first second : Stack} :
    CapturedIn owner capture (first.append second) ↔
      CapturedIn owner capture first ∨ CapturedIn owner capture second := by
  induction first with
  | nil =>
      constructor
      · exact Or.inr
      · intro located; rcases located with impossible | located
        · cases impossible
        · exact located
  | push frame rest ih =>
      constructor
      · intro located; cases located with
        | push located =>
            rcases ih.mp located with here | later
            · exact Or.inl (.push here)
            · exact Or.inr later
      · intro located; rcases located with here | later
        · cases here with | push here => exact .push (ih.mpr (Or.inl here))
        · exact RecursiveRecords.located_below _ later
  | live boundary input answer saved scope rest ihSaved ihRest =>
      constructor
      · intro located; cases located with
        | here => exact Or.inl .here
        | saved located => exact Or.inl (.saved located)
        | tail located =>
            rcases ihRest.mp located with here | later
            · exact Or.inl (.tail here)
            · exact Or.inr later
      · intro located; rcases located with here | later
        · cases here with
          | here => exact .here
          | saved located => exact .saved located
          | tail located => exact .tail (ihRest.mpr (Or.inl located))
        · exact RecursiveRecords.located_below _ later
  | spent boundary answer scope rest ih =>
      constructor
      · intro located; cases located with
        | spent located =>
            rcases ih.mp located with here | later
            · exact Or.inl (.spent here)
            · exact Or.inr later
      · intro located; rcases located with here | later
        · cases here with | spent here => exact .spent (ih.mpr (Or.inl here))
        · exact RecursiveRecords.located_below _ later

theorem closing_has_no_capture (plan : List CloseEntry) :
    ¬ CapturedIn owner capture (closeControl scope plan) := by
  induction plan with
  | nil => intro located; cases located
  | cons entry rest ih => intro located; cases located with
      | push located => exact ih located

/-- Cell writes traverse the active spine, never a dormant capture. -/
theorem cell_update_origin (update : CellUpdate identity old new before after)
    (located : CapturedIn owner capture after) : CapturedIn owner capture before := by
  induction update with
  | hit => cases located with | push located => exact .push located
  | push miss next ih => cases located with | push located => exact .push (ih located)
  | live next ih => cases located with
      | here => exact .here
      | saved located => exact .saved located
      | tail located => exact .tail (ih located)
  | spent next ih => cases located with | spent located => exact .spent (ih located)

/-- Every surviving old capture was already present before the step, with
the same executable saved stack. Allocation is the only possible new origin. -/
theorem raw_step_origin (step : RawStep before after created discharged)
    (old : Owner.ticket owner ∉ created)
    (located : CapturedIn owner capture after.stack) :
    CapturedIn owner capture before.stack := by
  cases step with
  | focus | enterHandler | enterCell | enterCleanup => cases located with
      | push located => exact located
  | plug | leaveHandler | leaveCell | finishCleanup | finishClose | retire => exact .push located
  | bind | beta | ifTrue | ifFalse => exact located
  | startCleanup => cases located with | push located => exact .push located
  | leaveClause => exact .spent located
  | capture requested operation parameter binder ticket operand body scope whole cap tail handler
      input cut selected closed environment =>
      rw [handler_cut_reconstructs cut]
      cases located with
      | here => exact False.elim (old List.mem_cons_self)
      | saved located => exact located_append.mpr (Or.inl located)
      | tail located => exact located_append.mpr (Or.inr located)
  | resume binder ticket scope caller input answer front cap tail value closed resolved =>
      rcases located_append.mp located with saved | later
      · exact RecursiveRecords.located_below front (.saved saved)
      · rcases located_append.mp later with earlier | later
        · exact located_append.mpr (Or.inl earlier)
        · cases later with | spent later => exact RecursiveRecords.located_below front (.tail later)
  | discard binder ticket closeId scope caller input answer front cap tail plan resolved built =>
      rcases located_append.mp located with closing | surviving
      · exact False.elim (closing_has_no_capture plan closing)
      · cases surviving with
        | push surviving =>
            rcases located_append.mp surviving with earlier | later
            · exact located_append.mpr (Or.inl earlier)
            · cases later with | spent later => exact RecursiveRecords.located_below front (.tail later)
  | readCell identity payload scope before after update => exact cell_update_origin update located
  | writeCell identity old new scope before after update => exact cell_update_origin update located

/-- Allocation freshness prevents an issued identity from being reused.
This induction transports capture provenance, not ownership preservation. -/
theorem run_origin (steps : RunSteps before after)
    (issued : Owner.ticket owner ∈ before.issued)
    (located : CapturedIn owner capture after.configuration.stack) :
    CapturedIn owner capture before.configuration.stack := by
  induction steps with
  | refl => exact located
  | next first rest ih =>
      cases first with
      | event middle created discharged raw fresh =>
          have old : Owner.ticket owner ∉ created := fun member =>
            (List.nodup_append.mp fresh).2.2 _ issued _ member rfl
          exact raw_step_origin raw old (ih (List.mem_append_left _ issued) located)

/-- Reuse uniqueness at the initial stack after transporting the later
location backward. No bound on nesting or intervening steps is imposed. -/
theorem same_capture (steps : RunSteps before after)
    (issued : Owner.ticket owner ∈ before.issued)
    (unique : (ownedTickets before.configuration.stack).Nodup)
    (initial : CapturedIn owner original before.configuration.stack)
    (later : CapturedIn owner current after.configuration.stack) : original = current :=
  SourceTemplates.captured_in_unique unique initial (run_origin steps issued later)

/-- The existing usage and historical registry supply issuance and uniqueness,
so a checked caller needs no separate capture-identity certificate. -/
theorem checked_same_capture (steps : NamedAccessSteps ambient before after)
    (usage : ConfigurationUsage policy tickets before.execution.configuration)
    (registry : UsageRegistryHistory tickets before.execution.issued)
    (initial : CapturedIn owner original before.execution.configuration.stack)
    (later : CapturedIn owner current after.execution.configuration.stack) : original = current := by
  obtain ⟨currentDemand, controlDemand, code, control, access, balance, unique⟩ := usage
  obtain ⟨rights, known⟩ := owned_tickets_registered control (SourceTemplates.captured_in_owned initial)
  exact same_capture (named_steps_execute (named_access_steps_have_names steps))
    ((registry owner).mp ⟨rights, known⟩) unique initial later

/-- The endpoint may expose any saved stack under the original ticket.
Historical capture identity derives its local-prefix decomposition; the
existing caller-run theorem then derives full and local resumption usage. -/
theorem caller_run_resume {localStack callerCapture current front tail : Stack}
    (steps : NamedAccessSteps ambient before after)
    (localUsage : ConfigurationUsage policy tickets
      ⟨.perform requested operation operand, localScope, localStack⟩)
    (operandValue : operand.IsValue)
    (ledger : Ledger before.execution.erase)
    (history : NameHistory before.execution before.activations)
    (access : AccessValid before.execution.configuration ambient)
    (usage : ConfigurationUsage policy tickets before.execution.configuration)
    (registry : UsageRegistryHistory tickets before.execution.issued)
    (captured : CapturedIn owner (localStack.append callerCapture) before.execution.configuration.stack)
    (endpoint : after.execution.configuration =
      ⟨.resume binder value, replyScope,
        front.append (.live owner input answer current callerScope tail)⟩)
    (resolved : replyScope.resolve binder = some owner)
    (closed : ClosedValue value) :
    ∃ afterTickets,
      RawStep after.execution.configuration
        ⟨value, replyScope, current.append (front.append (.spent owner answer callerScope tail))⟩
        [] [.ticket owner] ∧
      ConfigurationUsage policy afterTickets
        ⟨value, replyScope, current.append (front.append (.spent owner answer callerScope tail))⟩ ∧
      ConfigurationUsage policy afterTickets ⟨value, replyScope, localStack⟩ := by
  have later : CapturedIn owner current after.execution.configuration.stack :=
    endpoint.symm ▸ RecursiveRecords.located_below front CapturedIn.here
  have same := checked_same_capture steps usage registry captured later
  subst current
  exact SourceOwnerClosure.caller_run_resume_local_usage steps localUsage operandValue
    ledger history access usage registry endpoint resolved closed

end Ash.OneShot.SavedCaptureIdentity

#print axioms Ash.OneShot.SavedCaptureIdentity.located_append
#print axioms Ash.OneShot.SavedCaptureIdentity.closing_has_no_capture
#print axioms Ash.OneShot.SavedCaptureIdentity.cell_update_origin
#print axioms Ash.OneShot.SavedCaptureIdentity.raw_step_origin
#print axioms Ash.OneShot.SavedCaptureIdentity.run_origin
#print axioms Ash.OneShot.SavedCaptureIdentity.same_capture
#print axioms Ash.OneShot.SavedCaptureIdentity.checked_same_capture
#print axioms Ash.OneShot.SavedCaptureIdentity.caller_run_resume
