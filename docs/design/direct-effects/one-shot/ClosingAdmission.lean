import ClosingRequirements

/-!
Executable structural closing admission for a concrete captured control and its
surviving outside control. Soundness and completeness are by induction, including
both recursive branches of live captures. Source admission and preservation of
these conditions at future capture points remain separate obligations.
-/

namespace Ash.OneShot.ClosingAdmission

variable {control : Control}

def checkRequests (original surviving : Control) (requests : List Instance) : Bool :=
  requests.all fun request => match original.resolve request with
    | none => false
    | some target => surviving.resolve request == some target

theorem check_requests_iff : checkRequests original surviving requests = true ↔
    SameRequests original surviving requests := by
  induction requests with
  | nil => exact ⟨fun _ => .nil, fun _ => rfl⟩
  | cons request rest ih =>
      simp only [checkRequests, List.all_cons, Bool.and_eq_true] at *
      constructor
      · rintro ⟨current, next⟩
        cases before : original.resolve request with
        | none => simp [before] at current
        | some target =>
            exact .cons request rest target before (by simpa [before] using current) (ih.mp next)
      · intro checked
        cases checked with
        | cons _ _ target before after next => exact ⟨by simp [before, after], ih.mpr next⟩

def checkAction (frame : Frame) (rest original surviving : Control) (plan : List CloseItem) : Bool :=
  frame.pending.isEmpty &&
    frame.access.all (fun resource => ((planControl plan).append surviving).visible.contains resource) &&
    checkRequests (rest.append original) ((planControl plan).append surviving) frame.requests

theorem check_action_iff : checkAction frame rest original surviving plan = true ↔
    frame.pending = [] ∧
      frame.access ⊆ ((planControl plan).append surviving).visible ∧
      SameRequests (rest.append original) ((planControl plan).append surviving) frame.requests := by
  simp only [checkAction, Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true,
    List.contains_eq_mem, decide_eq_true_eq, check_requests_iff]
  constructor
  · rintro ⟨⟨pending, access⟩, requests⟩
    exact ⟨pending, fun _ member => access _ member, requests⟩
  · rintro ⟨pending, access, requests⟩
    exact ⟨⟨pending, fun _ member => access member⟩, requests⟩

/-- Check the suffix first, so callbacks and nested captures are checked against
    the actual remaining close control, in the existing Closes order. -/
def checkedPlan : Control → Control → Control → Option (List CloseItem)
  | .nil, _, _ => some []
  | .push frame rest, original, surviving =>
      match checkedPlan rest original surviving with
      | none => none
      | some plan => match frame.kind with
          | .bind | .handler _ _ => some plan
          | .resource identity => some (.release identity :: plan)
          | .armed identity =>
              if checkAction frame rest original surviving plan then
                some (.invoke identity frame.access frame.requests :: plan)
              else none
          | _ => none
  | .live owner _ _ saved rest, original, surviving =>
      match checkedPlan rest original surviving with
      | none => none
      | some outside =>
          match checkedPlan saved (rest.append original) ((planControl outside).append surviving) with
          | none => none
          | some inside => some (inside ++ .retire owner :: outside)
  | .spent _ _ rest, original, surviving => checkedPlan rest original surviving

theorem checked_plan_sound (control : Control)
    (accepted : checkedPlan control original surviving = some plan) :
    Closes control original surviving plan := by
  induction control generalizing original surviving plan with
  | nil => cases accepted; exact .nil _ _
  | push frame rest ih =>
      cases next : checkedPlan rest original surviving with
      | none => simp [checkedPlan, next] at accepted
      | some suffix =>
          have closed := ih next
          cases kind : frame.kind <;> simp only [checkedPlan, next, kind] at accepted
          case bind => cases accepted; exact .bind _ _ _ _ _ kind closed
          case handler effect activation => cases accepted; exact .handler _ _ _ _ _ _ _ kind closed
          case resource identity => cases accepted; exact .resource _ _ _ _ _ _ kind closed
          case armed identity =>
            split at accepted
            next checks =>
              cases accepted
              obtain ⟨pending, access, requests⟩ := check_action_iff.mp checks
              exact .armed _ _ _ _ _ _ kind pending access requests closed
            next => cases accepted
          all_goals cases accepted
  | live owner input answer saved rest ihSaved ihRest =>
      cases outside : checkedPlan rest original surviving with
      | none => simp [checkedPlan, outside] at accepted
      | some suffix =>
          cases inside : checkedPlan saved (rest.append original) ((planControl suffix).append surviving) with
          | none => simp [checkedPlan, outside, inside] at accepted
          | some inner =>
              simp only [checkedPlan, outside, inside, Option.some.injEq] at accepted
              subst plan
              exact .live _ _ _ _ _ _ _ _ _ (ihSaved inside) (ihRest outside)
  | spent owner answer rest ih => exact .spent _ _ _ _ _ _ (ih accepted)

theorem checked_plan_complete (closed : Closes control original surviving plan) :
    checkedPlan control original surviving = some plan := by
  induction closed with
  | nil => rfl
  | bind frame rest original surviving plan kind next ih
  | handler frame effect activation rest original surviving plan kind next ih
  | resource frame identity rest original surviving plan kind next ih => simp [checkedPlan, ih, kind]
  | armed frame identity rest original surviving plan kind pending access requests next ih =>
      simp [checkedPlan, ih, kind, check_action_iff.mpr ⟨pending, access, requests⟩]
  | live owner input answer saved rest original surviving inside outside capture next ihSaved ihRest =>
      simp [checkedPlan, ihRest, ihSaved]
  | spent owner answer rest original surviving plan next ih => exact ih

theorem checked_plan_iff : checkedPlan control original surviving = some plan ↔
    Closes control original surviving plan := ⟨checked_plan_sound control, checked_plan_complete⟩

theorem checked_plan_matches_raw
    (accepted : checkedPlan control original surviving = some plan) : rawPlan control = some plan :=
  closes_constructs_raw_plan (checked_plan_iff.mp accepted)

def checkInternalUses (owned uses : List Nat) : Bool := uses.all fun owner => owned.contains owner

theorem check_internal_uses_iff : checkInternalUses owned uses = true ↔ InternalUses owned uses := by
  induction uses with
  | nil => exact ⟨fun _ => .nil, fun _ => rfl⟩
  | cons owner rest ih =>
      simp only [checkInternalUses, List.all_cons, Bool.and_eq_true, List.contains_eq_mem,
        decide_eq_true_eq] at *
      exact ⟨fun ⟨inside, next⟩ => .cons owner rest inside (ih.mp next),
        fun checked => by cases checked with | cons _ _ inside next => exact ⟨inside, ih.mpr next⟩⟩

/-- Checks abandonment of pending ticket work separately from callback closing.
    This does not grant the caller's disposal permission. -/
def checkedDisposal (control outer : Control) : Option (List CloseItem) :=
  if checkInternalUses control.liveTickets control.pending then checkedPlan control outer outer else none

theorem checked_disposal_iff : checkedDisposal control outer = some plan ↔
    Discardable control outer plan := by
  constructor
  · intro accepted
    unfold checkedDisposal at accepted
    split at accepted
    next uses => exact .checked (checked_plan_iff.mp accepted) (check_internal_uses_iff.mp uses)
    next => cases accepted
  · intro checked
    cases checked with
    | checked closing uses =>
        simp [checkedDisposal, check_internal_uses_iff.mpr uses, checked_plan_complete closing]

theorem checked_disposal_accounting
    (accepted : checkedDisposal control outer = some plan) :
    (planOwners plan).Perm control.owners ∧ control.protected = [] :=
  ⟨discard_accounts_for_every_owner (checked_disposal_iff.mp accepted),
    discard_preserves_protected (checked_disposal_iff.mp accepted)⟩

open ScopedExecution ScopedPorts

/-- The independent structural and effect checks meet at the actual captured
    stack. The outer control must be the concrete surviving disposal context. -/
def checkCaptured (stack : Stack) (outer : Control) (closing : List Instance) : Bool :=
  ClosingRequirements.checkClosingEffects stack closing && (checkedDisposal stack.erase outer).isSome

theorem check_captured_iff
    (contents : StackTyped signature tickets world stack input result) :
    checkCaptured stack outer closing = true ↔
      ∃ plan, makePlan stack = some plan ∧ PlanTyped signature world closing plan ∧
        Discardable stack.erase outer (plan.map CloseEntry.erase) := by
  constructor
  · intro accepted
    simp only [checkCaptured, Bool.and_eq_true] at accepted
    obtain ⟨effects, access⟩ := accepted
    obtain ⟨plan, built, typed⟩ := close_ready_constructs_plan
      ((ClosingRequirements.check_closing_effects_iff contents).mp effects)
    cases checked : checkedDisposal stack.erase outer with
    | none => simp [checked] at access
    | some actual =>
        have disposal := checked_disposal_iff.mp checked
        have raw : rawPlan stack.erase = some actual := by
          cases disposal with | checked closed _ => exact closes_constructs_raw_plan closed
        have erases := make_plan_erases stack
        rw [built, raw] at erases
        have same : plan.map CloseEntry.erase = actual := Option.some.inj erases
        exact ⟨plan, built, typed, same ▸ disposal⟩
  · rintro ⟨plan, built, typed, disposal⟩
    simp only [checkCaptured, Bool.and_eq_true]
    exact ⟨(ClosingRequirements.check_closing_effects_iff contents).mpr
      (ClosingRequirements.generated_plan_supplies_readiness stack built typed),
      by simp [checked_disposal_iff.mpr disposal]⟩

/-- Successful combined checking constructs a real plan with complete owner
    accounting. Ownership uniqueness is still an independent input invariant. -/
theorem checked_capture_constructs_plan
    (contents : StackTyped signature tickets world stack input result)
    (accepted : checkCaptured stack outer closing = true) :
    ∃ plan, makePlan stack = some plan ∧ PlanTyped signature world closing plan ∧
      Discardable stack.erase outer (plan.map CloseEntry.erase) ∧
      (planOwners (plan.map CloseEntry.erase)).Perm stack.erase.owners ∧ stack.erase.protected = [] := by
  obtain ⟨plan, built, typed, disposal⟩ := (check_captured_iff contents).mp accepted
  exact ⟨plan, built, typed, disposal, discard_accounts_for_every_owner disposal,
    discard_preserves_protected disposal⟩

namespace Examples

def effect : Instance := .user 0 []
def callback : Frame := ⟨.armed 7, .unit, .unit, [], [], [effect]⟩
def outer : Control := .push ⟨.handler effect 22, .unit, .unit, [], [], []⟩ .nil

theorem same_activation_accepted : checkedDisposal (.push callback .nil) outer =
    some [.invoke 7 [] [effect]] := by decide

theorem different_activation_rejected : checkedDisposal
    (.push callback (.push ⟨.handler effect 11, .unit, .unit, [], [], []⟩ .nil)) outer = none := by decide

def resourceCallback : Frame := ⟨.armed 7, .unit, .unit, [4], [], [.cell 4]⟩
def resource : Frame := ⟨.resource 4, .unit, .unit, [], [], []⟩

theorem retained_resource_accepted : checkedDisposal
    (.push resourceCallback (.push resource .nil)) .nil =
      some [.invoke 7 [4] [.cell 4], .release 4] := by decide

theorem released_resource_rejected : checkedDisposal
    (.push resource (.push resourceCallback .nil)) .nil = none := by decide

theorem outside_ticket_rejected : checkedDisposal
    (.push ⟨.bind, .unit, .unit, [], [8], []⟩ .nil) .nil = none := by decide

theorem nested_owned_ticket_accepted : checkedDisposal
    (.live 9 .unit .unit
      (.push ⟨.bind, .unit, .unit, [], [8], []⟩ (.live 8 .unit .unit .nil .nil)) .nil) .nil =
      some [.retire 8, .retire 9] := by decide

theorem nested_protection_rejected : checkedDisposal
    (.live 8 .unit .unit (.push ⟨.running 7, .unit, .unit, [], [], []⟩ .nil) .nil) .nil = none := by decide

theorem typed_capture_accepted : checkCaptured ScopedPorts.CompletionExamples.captured .nil [] = true := by decide

end Examples

end Ash.OneShot.ClosingAdmission

#print axioms Ash.OneShot.ClosingAdmission.check_requests_iff
#print axioms Ash.OneShot.ClosingAdmission.check_action_iff
#print axioms Ash.OneShot.ClosingAdmission.checked_plan_sound
#print axioms Ash.OneShot.ClosingAdmission.checked_plan_complete
#print axioms Ash.OneShot.ClosingAdmission.checked_plan_iff
#print axioms Ash.OneShot.ClosingAdmission.checked_plan_matches_raw
#print axioms Ash.OneShot.ClosingAdmission.check_internal_uses_iff
#print axioms Ash.OneShot.ClosingAdmission.checked_disposal_iff
#print axioms Ash.OneShot.ClosingAdmission.checked_disposal_accounting
#print axioms Ash.OneShot.ClosingAdmission.check_captured_iff
#print axioms Ash.OneShot.ClosingAdmission.checked_capture_constructs_plan
#print axioms Ash.OneShot.ClosingAdmission.Examples.same_activation_accepted
#print axioms Ash.OneShot.ClosingAdmission.Examples.different_activation_rejected
#print axioms Ash.OneShot.ClosingAdmission.Examples.retained_resource_accepted
#print axioms Ash.OneShot.ClosingAdmission.Examples.released_resource_rejected
#print axioms Ash.OneShot.ClosingAdmission.Examples.outside_ticket_rejected
#print axioms Ash.OneShot.ClosingAdmission.Examples.nested_owned_ticket_accepted
#print axioms Ash.OneShot.ClosingAdmission.Examples.nested_protection_rejected
#print axioms Ash.OneShot.ClosingAdmission.Examples.typed_capture_accepted
