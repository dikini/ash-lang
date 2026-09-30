import OpenOwnerUses

/-!
Named owner phases refine the existing ordered interpretation context. The
projection is derived from actual stacks. Consumption updates the waiting
caller; resumption also restores the capture before that caller. These are
context-transition proofs, not a complete phase/effect source invariant.
-/

namespace Ash.OneShot.OwnerPhases
open ScopedExpressions ScopedExecution ProtectionContracts
open CallableProtectionFrames (Tables contextOf pushContext)

inductive Entry where
  | ordinary : ProtectionContracts.Layer → Entry
  | live : Nat → Bool → Entry
  | spent : Nat → Entry
  deriving DecidableEq, Repr

abbrev Context := List Entry

def project : Context → ProtectionContracts.Context
  | [] => []
  | .ordinary layer :: rest => layer :: project rest
  | .live _ held :: rest => .barrier held :: project rest
  | .spent _ :: rest => project rest

def names : Context → List Nat
  | [] => []
  | .ordinary _ :: rest => names rest
  | .live owner _ :: rest | .spent owner :: rest => owner :: names rest

def frameEntry (tables : Tables) (frame : ExecFrame) : Entry := match frame with
  | .handler data => .ordinary (.handler data.effectInst data.activation (tables data))
  | .cell identity _ _ _ => .ordinary (.builtin identity)
  | _ => .ordinary (.barrier (ProtectionContexts.frameProtected frame.erase))

def ofStack (tables : Tables) : Stack → Context
  | .nil => []
  | .push frame rest => frameEntry tables frame :: ofStack tables rest
  | .live owner _ _ saved _ rest =>
      .live owner (ProtectionContexts.protectedMode saved.erase) :: ofStack tables rest
  | .spent owner _ _ rest => .spent owner :: ofStack tables rest

/-- Consume the first matching owner. A spent match rejects another use;
    ordinary interpretations and unrelated owners retain their positions. -/
def consume (owner : Nat) : Context → Option Context
  | [] => none
  | .ordinary layer :: rest => (consume owner rest).map (.ordinary layer :: ·)
  | .live other held :: rest =>
      if owner = other then some (.spent other :: rest)
      else (consume owner rest).map (.live other held :: ·)
  | .spent other :: rest =>
      if owner = other then none
      else (consume owner rest).map (.spent other :: ·)

/-- Structural one-shot phase change, independent of operation permissions. -/
inductive Consumes (owner : Nat) : Context → Context → Prop where
  | hit : Consumes owner (.live owner held :: rest) (.spent owner :: rest)
  | ordinary (next : Consumes owner before after) :
      Consumes owner (.ordinary layer :: before) (.ordinary layer :: after)
  | live (different : owner ≠ other) (next : Consumes owner before after) :
      Consumes owner (.live other held :: before) (.live other held :: after)
  | spent (different : owner ≠ other) (next : Consumes owner before after) :
      Consumes owner (.spent other :: before) (.spent other :: after)

theorem consumes_sound (step : Consumes owner before after) : consume owner before = some after := by
  induction step <;> simp_all [consume]

theorem consumes_complete (checked : consume owner before = some after) : Consumes owner before after := by
  induction before generalizing after with
  | nil => simp [consume] at checked
  | cons entry rest ih =>
      cases entry with
      | ordinary layer =>
          cases found : consume owner rest <;> simp [consume, found] at checked
          subst after
          exact .ordinary (ih found)
      | live other held =>
          by_cases same : owner = other
          · subst other
            simp [consume] at checked
            subst after
            exact .hit
          · cases found : consume owner rest <;> simp [consume, same, found] at checked
            subst after
            exact .live same (ih found)
      | spent other =>
          by_cases same : owner = other
          · simp [consume, same] at checked
          · cases found : consume owner rest <;> simp [consume, same, found] at checked
            subst after
            exact .spent same (ih found)

theorem consumes_iff : Consumes owner before after ↔ consume owner before = some after :=
  ⟨consumes_sound, consumes_complete⟩

theorem consumes_unique (first : Consumes owner before after) (second : Consumes owner before other) :
    after = other := Option.some.inj ((consumes_sound first).symm.trans (consumes_sound second))

theorem consumes_once (step : Consumes owner before after) : consume owner after = none := by
  induction step <;> simp_all [consume]

theorem consumes_names (step : Consumes owner before after) : names after = names before := by
  induction step <;> simp_all [names]

@[simp] theorem project_append (front tail : Context) : project (front ++ tail) = project front ++ project tail := by
  induction front with
  | nil => rfl
  | cons entry rest ih => cases entry <;> simp [project, ih]

@[simp] theorem names_append (front tail : Context) : names (front ++ tail) = names front ++ names tail := by
  induction front with
  | nil => rfl
  | cons entry rest ih => cases entry <;> simp [names, ih]

theorem frame_project (tables : Tables) (frame : ExecFrame) (tail : Context) :
    project (frameEntry tables frame :: tail) = pushContext tables frame (project tail) := by
  cases frame <;> rfl

theorem project_stack (tables : Tables) (stack : Stack) : project (ofStack tables stack) = contextOf tables stack := by
  induction stack with
  | nil => rfl
  | push frame rest ih => simp only [ofStack, frame_project, contextOf, ih]
  | live owner input answer saved scope rest ihSaved ihRest => simp only [ofStack, project, contextOf, ihRest]
  | spent owner answer scope rest ih => exact ih

@[simp] theorem stack_append (tables : Tables) (front tail : Stack) :
    ofStack tables (front.append tail) = ofStack tables front ++ ofStack tables tail := by
  induction front <;> simp_all [Stack.append, ofStack]

/-- Only active live/spent markers occur here. Dormant owners and retirement
    names remain accounted for by the stronger runtime name history. -/
theorem stack_names_subset (tables : Tables) (stack : Stack) : names (ofStack tables stack) ⊆ stack.erase.ticketNames := by
  induction stack with
  | nil => simp [ofStack, names]
  | push frame rest ih =>
      cases frame <;> simp_all [ofStack, frameEntry, names, Stack.erase, Control.ticketNames,
        ExecFrame.erase, PlainData.erase, HandlerData.erase, ActionData.erase, closeFrame, CloseItem.frame]
  | live owner input answer saved scope rest ihSaved ihRest =>
      intro name member
      simp only [ofStack, names, List.mem_cons] at member
      rcases member with same | member
      · simp [Stack.erase, Control.ticketNames, same]
      · exact List.mem_cons_of_mem owner (List.mem_append_right _ (ihRest member))
  | spent owner answer scope rest ih =>
      intro name member
      simp only [ofStack, names, List.mem_cons] at member
      rcases member with same | member
      · simp [Stack.erase, Control.ticketNames, same]
      · exact List.mem_cons_of_mem owner (ih member)

theorem consume_absent (absent : owner ∉ names context) : consume owner context = none := by
  induction context with
  | nil => rfl
  | cons entry rest ih => cases entry <;> simp_all [names, consume]

theorem consume_through (absent : owner ∉ names front) :
    consume owner (front ++ tail) = (consume owner tail).map (front ++ ·) := by
  induction front with
  | nil => simp
  | cons entry rest ih =>
      cases entry <;> simp_all [names, consume, Option.map_map, Function.comp_def]

theorem consume_boundary (absent : owner ∉ names front) :
    consume owner (front ++ .live owner held :: tail) = some (front ++ .spent owner :: tail) := by
  simp [consume_through absent, consume]

section Runtime

variable {front capture tail : Stack} {issued completed : List Owner}

theorem owner_absent_from_front
    (unique : (front.append (.live owner input answer capture scope tail)).erase.ticketNames.Nodup) :
    owner ∉ front.erase.ticketNames := by
  have disjoint := (List.nodup_append.mp (show
    (front.erase.ticketNames ++ owner :: (capture.erase.ticketNames ++ tail.erase.ticketNames)).Nodup from
      by simpa [Stack.erase, Control.ticketNames] using unique)).2.2
  intro member
  exact disjoint owner member owner (by simp) rfl

theorem consume_stack
    (unique : (front.append (.live owner input answer capture scope tail)).erase.ticketNames.Nodup) :
    consume owner (ofStack tables (front.append (.live owner input answer capture scope tail))) =
      some (ofStack tables (front.append (.spent owner answer scope tail))) := by
  have absent : owner ∉ names (ofStack tables front) := fun member =>
    owner_absent_from_front unique (stack_names_subset tables front member)
  simpa [ofStack] using (consume_boundary (held := ProtectionContexts.protectedMode capture.erase)
    (tail := ofStack tables tail) absent)

/-- Capture decomposition is independent of depth and of the frame kinds crossed. -/
theorem capture_context (cut : HandlerCut requested whole capture tail handler) :
    ofStack tables whole = ofStack tables capture ++ ofStack tables tail := by
  rw [handler_cut_reconstructs cut, stack_append]

/-- Resuming restores the capture before the updated caller. Merely dropping
    the owner's barrier would omit active protection in the restored capture. -/
theorem resume_context
    (unique : (front.append (.live owner input answer capture scope tail)).erase.ticketNames.Nodup) :
    (consume owner (ofStack tables (front.append (.live owner input answer capture scope tail)))).map
      (ofStack tables capture ++ ·) =
    some (ofStack tables (capture.append (front.append (.spent owner answer scope tail)))) := by
  rw [consume_stack unique]
  simp

theorem resume_requirements
    (unique : (front.append (.live owner input answer capture scope tail)).erase.ticketNames.Nodup)
    (updated : consume owner (ofStack tables (front.append (.live owner input answer capture scope tail))) = some waiting) :
    ProtectionResiduals.checkResidual (project waiting)
      (ProtectionResiduals.residualize (project (ofStack tables capture)) row) =
    checkFootprint (contextOf tables (capture.append (front.append (.spent owner answer scope tail)))) row := by
  have same := Option.some.inj (updated.symm.trans (consume_stack unique))
  subst waiting
  rw [ProtectionResiduals.residual_check, project_stack, project_stack]
  simp only [ProtectionResiduals.context_append]

theorem owner_absent_from_capture
    (unique : (front.append (.live owner input answer capture scope tail)).erase.ticketNames.Nodup) :
    owner ∉ capture.erase.ticketNames := by
  have suffix := (List.nodup_append.mp (show
    (front.erase.ticketNames ++ owner :: (capture.erase.ticketNames ++ tail.erase.ticketNames)).Nodup from
      by simpa [Stack.erase, Control.ticketNames] using unique)).2.1
  exact fun member => (List.nodup_cons.mp suffix).1 (List.mem_append_left _ member)

theorem restored_owner_consumed
    (unique : (front.append (.live owner input answer capture scope tail)).erase.ticketNames.Nodup) :
    consume owner (ofStack tables (capture.append (front.append (.spent owner answer scope tail)))) = none := by
  have absent : owner ∉ names (ofStack tables capture) := fun member =>
    owner_absent_from_capture unique (stack_names_subset tables capture member)
  rw [stack_append, consume_through absent]
  have once := consumes_once (consumes_complete (consume_stack (tables := tables) unique))
  rw [once]
  rfl

/-- The context update shares the actual resumption and existing ownership,
    support, type, callable-result and name-history invariant. -/
theorem resume_joint
    (valid : CompletionJoint.Valid declarations policy registry ambient
      ⟨⟨⟨.resume binder value, scope, front.append (.live owner input answer capture caller tail)⟩,
        issued, completed⟩, activations⟩ result outgoing bound)
    (resolved : scope.resolve binder = some owner) (isValue : value.IsValue) (tables : Tables) :
    let before : NamedState := ⟨⟨⟨.resume binder value, scope,
      front.append (.live owner input answer capture caller tail)⟩, issued, completed⟩, activations⟩
    let after : Configuration := ⟨value, scope, capture.append (front.append (.spent owner answer caller tail))⟩
    NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [] [.ticket owner]) ∧
    CompletionJoint.Valid declarations policy registry ambient
      (ScopedPortJoint.advanceState before after [] [.ticket owner]) result outgoing bound ∧
    ∃ waiting, Consumes owner (ofStack tables before.execution.configuration.stack) waiting ∧
      ofStack tables after.stack = ofStack tables capture ++ waiting ∧
      consume owner (ofStack tables after.stack) = none ∧
      ∀ row, ProtectionResiduals.checkResidual (project waiting)
        (ProtectionResiduals.residualize (project (ofStack tables capture)) row) =
        checkFootprint (contextOf tables after.stack) row := by
  have unique := (history_gives_distinct_names valid.joint.names valid.joint.ledger).1
  obtain ⟨step, preserved⟩ := CompletionJoint.resume_preserves valid resolved isValue
  refine ⟨step, preserved, ofStack tables (front.append (.spent owner answer caller tail)),
    consumes_complete (consume_stack unique), ?_, restored_owner_consumed unique, ?_⟩
  · exact stack_append ..
  · intro row
    exact resume_requirements unique (consume_stack unique)

/-- Disposal uses the same caller phase update, then installs the actual
    closing plan and its protection barrier. This joins structural usage only;
    resource support and callback effect admission are separate obligations. -/
theorem discard_usage_context
    (beforeUsage : ConfigurationUsage policy tickets
      ⟨.discard binder, scope, front.append (.live owner input answer capture caller tail)⟩)
    (unique : (front.append (.live owner input answer capture caller tail)).erase.ticketNames.Nodup)
    (interface : OpenOwnerUses.Interface policy tickets capture (activeTickets tail))
    (empty : interface.external = []) (resolved : scope.resolve binder = some owner)
    (built : makePlan capture = some plan) (tables : Tables) :
    let before : Configuration := ⟨.discard binder, scope,
      front.append (.live owner input answer capture caller tail)⟩
    let after : Configuration := ⟨.unit, scope, (closeControl scope plan).append
      (.push (.closing closeId scope) (front.append (.spent owner answer caller tail)))⟩
    RawStep before after [.close closeId] [.ticket owner] ∧
    ConfigurationUsage policy tickets after ∧
    ∃ waiting, Consumes owner (ofStack tables before.stack) waiting ∧
      ofStack tables after.stack = ofStack tables (closeControl scope plan) ++
        frameEntry tables (.closing closeId scope) :: waiting ∧
      ∀ row, ProtectionResiduals.checkResidual (.barrier true :: project waiting)
        (ProtectionResiduals.residualize (project (ofStack tables (closeControl scope plan))) row) =
        checkFootprint (contextOf tables after.stack) row := by
  refine ⟨.discard binder owner closeId scope caller input answer front capture tail plan resolved built,
    OpenOwnerUses.discard_usage beforeUsage interface empty resolved built,
    ofStack tables (front.append (.spent owner answer caller tail)),
    consumes_complete (consume_stack unique), ?_, ?_⟩
  · simp only [stack_append, ofStack]
  · intro row
    rw [ProtectionResiduals.residual_check, project_stack, project_stack]
    simp only [ProtectionResiduals.context_append, contextOf, pushContext,
      ProtectionContexts.frameProtected, ExecFrame.erase, closeFrame]

end Runtime

namespace Examples

open CallableProtection.Examples (unit_closed)

theorem saved_closed : ClosedValue (.integer 17) := ⟨trivial, rfl, by simp [Code.dependencies]⟩
def action : ActionData :=
  ⟨55, .lambda 1 .unit, ⟨trivial, rfl, by simp [Code.dependencies, Syntax.without]⟩, .none, .integer, []⟩
def handler : HandlerData := ⟨71, .user 71 [], .cons 0 1 10 (.discard 10) .nil, .none, .integer, rfl⟩
def tables : Tables := fun _ => [(0, ⟨true, some [], none⟩)]
def capture : Stack := .push (.running action (.integer 17) saved_closed) .nil
def tail : Stack := .push (.handler handler) .nil
def before : Configuration := ⟨.resume 10 .unit, .ticket 10 9, .live 9 .unit .integer capture .none tail⟩
def after : Configuration := ⟨.unit, .ticket 10 9, capture.append (.spent 9 .integer .none tail)⟩
def finished : Configuration := ⟨.integer 17, .none, .spent 9 .integer .none tail⟩
def demand : Demand := ⟨.user 71 [], 0, false⟩

theorem actual_resume : RawStep before after [] [.ticket 9] :=
  .resume 10 9 (.ticket 10 9) .none .unit .integer .nil capture tail .unit unit_closed rfl

theorem actual_cleanup_completion : RawStep after finished [] [.cleanup 55] :=
  .finishCleanup action (.integer 17) saved_closed (.ticket 10 9) (.spent 9 .integer .none tail)

theorem waiting_update :
    consume 9 (ofStack tables before.stack) = some (ofStack tables finished.stack) := by decide

theorem restored_protection :
    project (ofStack tables after.stack) = .barrier true :: project (ofStack tables finished.stack) := rfl

theorem request_rejected_before : checkRequest (project (ofStack tables before.stack)) demand = false := by decide

theorem request_rejected_during_restored_cleanup :
    checkRequest (project (ofStack tables after.stack)) demand = false := by decide

theorem request_accepted_after_cleanup :
    checkRequest (project (ofStack tables finished.stack)) demand = true := by decide

theorem protected_capture_has_no_close_plan : makePlan capture = none := rfl

theorem consumed_owner_cannot_resume_again : consume 9 (ofStack tables after.stack) = none := by decide

/-- The earlier open capture keeps owner 9 outside while consuming owner 19.
    The named context is derived from that same actual raw step. -/
theorem open_capture_update :
    (consume 19 (ofStack OpenOwnerUses.Examples.tables OpenOwnerUses.Examples.beforeResume.stack)).map
      (ofStack OpenOwnerUses.Examples.tables OpenOwnerUses.Examples.capture ++ ·) =
    some (ofStack OpenOwnerUses.Examples.tables OpenOwnerUses.Examples.afterResume.stack) := by decide

theorem open_capture_outside_owner_retained :
    names (ofStack OpenOwnerUses.Examples.tables OpenOwnerUses.Examples.afterResume.stack) = [19, 9] := rfl

end Examples
end Ash.OneShot.OwnerPhases

#print axioms Ash.OneShot.OwnerPhases.consumes_sound
#print axioms Ash.OneShot.OwnerPhases.consumes_complete
#print axioms Ash.OneShot.OwnerPhases.consumes_iff
#print axioms Ash.OneShot.OwnerPhases.consumes_unique
#print axioms Ash.OneShot.OwnerPhases.consumes_once
#print axioms Ash.OneShot.OwnerPhases.consumes_names
#print axioms Ash.OneShot.OwnerPhases.project_append
#print axioms Ash.OneShot.OwnerPhases.names_append
#print axioms Ash.OneShot.OwnerPhases.frame_project
#print axioms Ash.OneShot.OwnerPhases.project_stack
#print axioms Ash.OneShot.OwnerPhases.stack_append
#print axioms Ash.OneShot.OwnerPhases.stack_names_subset
#print axioms Ash.OneShot.OwnerPhases.consume_absent
#print axioms Ash.OneShot.OwnerPhases.consume_through
#print axioms Ash.OneShot.OwnerPhases.consume_boundary
#print axioms Ash.OneShot.OwnerPhases.owner_absent_from_front
#print axioms Ash.OneShot.OwnerPhases.consume_stack
#print axioms Ash.OneShot.OwnerPhases.capture_context
#print axioms Ash.OneShot.OwnerPhases.resume_context
#print axioms Ash.OneShot.OwnerPhases.resume_requirements
#print axioms Ash.OneShot.OwnerPhases.owner_absent_from_capture
#print axioms Ash.OneShot.OwnerPhases.restored_owner_consumed
#print axioms Ash.OneShot.OwnerPhases.resume_joint
#print axioms Ash.OneShot.OwnerPhases.discard_usage_context
#print axioms Ash.OneShot.OwnerPhases.Examples.saved_closed
#print axioms Ash.OneShot.OwnerPhases.Examples.actual_resume
#print axioms Ash.OneShot.OwnerPhases.Examples.actual_cleanup_completion
#print axioms Ash.OneShot.OwnerPhases.Examples.waiting_update
#print axioms Ash.OneShot.OwnerPhases.Examples.restored_protection
#print axioms Ash.OneShot.OwnerPhases.Examples.request_rejected_before
#print axioms Ash.OneShot.OwnerPhases.Examples.request_rejected_during_restored_cleanup
#print axioms Ash.OneShot.OwnerPhases.Examples.request_accepted_after_cleanup
#print axioms Ash.OneShot.OwnerPhases.Examples.protected_capture_has_no_close_plan
#print axioms Ash.OneShot.OwnerPhases.Examples.consumed_owner_cannot_resume_again
#print axioms Ash.OneShot.OwnerPhases.Examples.open_capture_update
#print axioms Ash.OneShot.OwnerPhases.Examples.open_capture_outside_owner_retained
