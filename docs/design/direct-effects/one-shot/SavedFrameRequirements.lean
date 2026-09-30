import PhaseBoundaries

/-!
Requirements of actual saved frame code, interpreted at each frame's remaining
suffix. The source evidence here covers ordinary callable contexts and cleanup
callbacks. Contexts that themselves consume a ticket still need integration
with the phase judgment. No execution progress is inferred from these rows.
-/

namespace Ash.OneShot.SavedFrameRequirements
open ScopedExpressions ScopedExecution CallableProtection ProtectionContracts ProtectionResiduals
open CallableProtectionFrames (Tables contextOf ContextSummarizes)

/-- These are requirements of code run when the frame is reached, after the
    frame above it has returned. Armed cleanup adds its own running protection.
    Running cleanup's saved result is a value, not another invocation. -/
inductive FrameSource (operations : Operations) : ExecFrame → Footprint → Prop where
  | plain (source : ContextSummarizes operations environment plain.context input output row) :
      FrameSource operations (.plain plain) row
  | handler : FrameSource operations (.handler handler) []
  | cell : FrameSource operations (.cell identity payload scope answer) []
  | armed (callback : Summarizes operations environment action.action (.function .scalar .scalar latent) []) :
      FrameSource operations (.armed action) (qualify true latent)
  | running (saved : Summarizes operations environment value contract []) :
      FrameSource operations (.running action value closed) []
  | closing : FrameSource operations (.closing identity scope) []
  | retiring : FrameSource operations (.retiring owner) []

/-- Dormant captures retain source evidence separately. Their pending code is
    not counted as already executing in the enclosing stack. -/
inductive Sources (operations : Operations) : Stack → Prop where
  | nil : Sources operations .nil
  | push (frame : FrameSource operations entry row) (rest : Sources operations tail) :
      Sources operations (.push entry tail)
  | live (saved : Sources operations capture) (rest : Sources operations tail) :
      Sources operations (.live owner input answer capture scope tail)
  | spent (rest : Sources operations tail) : Sources operations (.spent owner answer scope tail)

/-- Each frame exports through its own remaining suffix. This is not a single
    footprint checked at the top of the original capture. -/
inductive Rows (operations : Operations) (tables : Tables) : Stack → Footprint → Prop where
  | nil : Rows operations tables .nil []
  | push (frame : FrameSource operations entry frameRow)
      (exported : residualize (contextOf tables tail) frameRow = some outward)
      (rest : Rows operations tables tail remaining) :
      Rows operations tables (.push entry tail) (outward ++ remaining)
  | live (saved : Sources operations capture) (rest : Rows operations tables tail row) :
      Rows operations tables (.live owner input answer capture scope tail) row
  | spent (rest : Rows operations tables tail row) : Rows operations tables (.spent owner answer scope tail) row

/-- Requirements checked at actual frame positions, with an arbitrary
    receiving context outside the saved prefix. -/
inductive Checked (operations : Operations) (tables : Tables) (outside : ProtectionContracts.Context) : Stack → Prop where
  | nil : Checked operations tables outside .nil
  | push (frame : FrameSource operations entry frameRow)
      (accepted : checkFootprint (contextOf tables tail ++ outside) frameRow = true)
      (rest : Checked operations tables outside tail) :
      Checked operations tables outside (.push entry tail)
  | live (saved : Sources operations capture) (rest : Checked operations tables outside tail) :
      Checked operations tables outside (.live owner input answer capture scope tail)
  | spent (rest : Checked operations tables outside tail) :
      Checked operations tables outside (.spent owner answer scope tail)

variable {front tail stack : Stack}

theorem rows_sources (rows : Rows operations tables stack row) : Sources operations stack := by
  induction rows with
  | nil => exact .nil
  | push frame exported rest ih => exact .push frame ih
  | live saved rest ih => exact .live saved ih
  | spent rest ih => exact .spent ih

theorem rows_checked (rows : Rows operations tables stack row) (accepted : checkFootprint outside row = true) :
    Checked operations tables outside stack := by
  induction rows with
  | nil => exact .nil
  | push frame exported rest ih =>
      rw [check_footprint_append, Bool.and_eq_true_iff] at accepted
      refine .push frame ?_ (ih accepted.2)
      rw [← residual_check, exported]
      exact accepted.1
  | live saved rest ih => exact .live saved (ih accepted)
  | spent rest ih => exact .spent (ih accepted)

theorem checked_rows (checked : Checked operations tables outside stack) :
    ∃ row, Rows operations tables stack row ∧ checkFootprint outside row = true := by
  induction checked with
  | nil => exact ⟨[], .nil, rfl⟩
  | push frame accepted rest ih =>
      obtain ⟨outward, exported, admitted⟩ := residual_admitted_iff.mp accepted
      obtain ⟨remaining, rows, checked⟩ := ih
      exact ⟨outward ++ remaining, .push frame exported rows,
        by simp only [check_footprint_append, admitted, checked, Bool.and_self]⟩
  | live saved rest ih => obtain ⟨row, rows, checked⟩ := ih; exact ⟨row, .live saved rows, checked⟩
  | spent rest ih => obtain ⟨row, rows, checked⟩ := ih; exact ⟨row, .spent rows, checked⟩

theorem checked_iff_rows : Checked operations tables outside stack ↔
    ∃ row, Rows operations tables stack row ∧ checkFootprint outside row = true :=
  ⟨checked_rows, fun ⟨_, rows, accepted⟩ => rows_checked rows accepted⟩

theorem sources_append (first : Sources operations front) (second : Sources operations tail) :
    Sources operations (front.append tail) := by
  induction first with
  | nil => exact second
  | push frame rest ih => exact .push frame ih
  | live saved rest ihSaved ihRest => exact .live saved ihRest
  | spent rest ih => exact .spent ih

theorem checked_append (first : Checked operations tables (contextOf tables tail ++ outside) front)
    (second : Checked operations tables outside tail) : Checked operations tables outside (front.append tail) := by
  induction first with
  | nil => exact second
  | push frame accepted rest ih =>
      exact .push frame (by simpa only [context_append, List.append_assoc] using accepted) ih
  | live saved rest ih => exact .live saved ih
  | spent rest ih => exact .spent ih

theorem checked_decompose (checked : Checked operations tables outside (front.append tail)) :
    Checked operations tables (contextOf tables tail ++ outside) front ∧ Checked operations tables outside tail := by
  induction front with
  | nil => exact ⟨.nil, checked⟩
  | push frame rest ih => cases checked with
      | push source accepted remaining =>
          obtain ⟨inside, outsideChecked⟩ := ih remaining
          exact ⟨.push source (by simpa only [context_append, List.append_assoc] using accepted) inside, outsideChecked⟩
  | live owner input answer saved scope rest ihSaved ihRest => cases checked with
      | live dormant remaining =>
          obtain ⟨inside, outsideChecked⟩ := ihRest remaining
          exact ⟨.live dormant inside, outsideChecked⟩
  | spent owner answer scope rest ih => cases checked with
      | spent remaining => obtain ⟨inside, outsideChecked⟩ := ih remaining; exact ⟨.spent inside, outsideChecked⟩

/-- Actual handler cuts supply the frame rows of their saved prefix. The
    captured row is derived from retained code and each remaining suffix. -/
theorem capture_rows (cut : HandlerCut requested whole capture tail handler)
    (checked : Checked operations tables outside whole) :
    ∃ row, Rows operations tables capture row ∧
      checkFootprint (contextOf tables tail ++ outside) row = true ∧ Checked operations tables outside tail := by
  rw [handler_cut_reconstructs cut] at checked
  obtain ⟨inside, rest⟩ := checked_decompose checked
  obtain ⟨row, rows, accepted⟩ := checked_rows inside
  exact ⟨row, rows, accepted, rest⟩

/-- Resuming into a new caller checks the derived capture row at that caller.
    It also checks the caller's own future code separately. -/
theorem resume_recomposition (captured : Rows operations tables capture row)
    (accepted : checkFootprint (contextOf tables (front.append tail) ++ outside) row = true)
    (caller : Checked operations tables outside (front.append tail)) :
    Checked operations tables outside (capture.append (front.append (.spent owner answer scope tail))) := by
  obtain ⟨inside, rest⟩ := checked_decompose caller
  have waiting : Checked operations tables outside (front.append (.spent owner answer scope tail)) :=
    checked_append (by exact inside) (.spent rest)
  apply checked_append (rows_checked captured _) waiting
  simpa only [context_append, contextOf] using accepted

/-- A plain frame's row supplies the existing local plug certificate at the
    actual surviving tail. Full hole and result contracts stay in the source
    context derivation; these are not reconstructed from effect rows. -/
theorem plain_pending (checked : Checked operations tables [] (.push (.plain plain) tail)) :
    ∃ environment input output, CallableProtectionFrames.Pending operations tables environment plain tail input output := by
  cases checked with
  | push source accepted rest => cases source with
      | plain context => exact ⟨_, _, _, _, context, by simpa only [List.append_nil] using accepted⟩

theorem armed_pending (checked : Checked operations tables [] (.push (.armed action) tail)) :
    CallableProtectionFrames.Armed operations tables action tail := by
  cases checked with
  | push source accepted rest => cases source with
      | armed callback =>
          exact ⟨_, _, callback, by simpa only [List.append_nil, check_qualified] using accepted⟩

theorem source_resume_checks_caller
    (source : ClauseProtection.Derives operations policy ticket (contextOf tables front) environment
      .available (.resume ticket.binder value) .consumed ticket.answer row)
    (accepted : checkFootprint (contextOf tables tail) row = true) (isValue : value.IsValue) :
    checkFootprint (contextOf tables (front.append tail)) ticket.resumeRow = true := by
  cases source with
  | resume allowed operand exported =>
      obtain ⟨_, _, empty⟩ := ClauseProtection.value_summary operand isValue
      rw [empty, List.nil_append] at accepted
      rw [context_append, ← residual_check, exported]
      exact accepted

/-- The resumed row now comes from actual frame source derivations, and the
    phase rule checks it at the new waiting caller. The named step preserves
    the same existing ownership/type invariant. -/
theorem resume_joint
    (valid : CompletionJoint.Valid declarations policy registry ambient
      ⟨⟨⟨.resume ticket.binder value, scope,
        front.append (.live owner input answer capture caller tail)⟩, issued, completed⟩, activations⟩
      result outgoing bound)
    (source : ClauseProtection.Derives operations policy ticket (contextOf tables front) environment
      .available (.resume ticket.binder value) .consumed ticket.answer row)
    (captured : Rows operations tables capture ticket.resumeRow)
    (accepted : checkFootprint (contextOf tables tail) row = true)
    (waiting : Checked operations tables [] (front.append tail))
    (resolved : scope.resolve ticket.binder = some owner) (isValue : value.IsValue) :
    let before : NamedState := ⟨⟨⟨.resume ticket.binder value, scope,
      front.append (.live owner input answer capture caller tail)⟩, issued, completed⟩, activations⟩
    let after : Configuration := ⟨value, scope, capture.append (front.append (.spent owner answer caller tail))⟩
    NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [] [.ticket owner]) ∧
      CompletionJoint.Valid declarations policy registry ambient
        (ScopedPortJoint.advanceState before after [] [.ticket owner]) result outgoing bound ∧
      Checked operations tables [] after.stack := by
  obtain ⟨step, nextValid⟩ := CompletionJoint.resume_preserves valid resolved isValue
  have checkedCaller := source_resume_checks_caller source accepted isValue
  exact ⟨step, nextValid, resume_recomposition captured (by simpa only [List.append_nil] using checkedCaller) waiting⟩

namespace Examples

def operations : Operations := fun _ _ => some (.scalar, .scalar)
def tables : Tables := fun _ => []
def readCode : Code := .perform (Instantiation.freezeEffect (.cell 42)) 0 (.resourceRef (.activation 42))
def readFrame : PlainData := ⟨.bind 9 readCode, .none, .unit, .integer, [], rfl⟩
def demand : Footprint := [⟨.cell 42, 0, false⟩]
def beforeRelease : Stack := .push (.plain readFrame) (.push (.cell 42 8 .none .integer) .nil)
def afterRelease : Stack := .push (.cell 42 8 .none .integer) (.push (.plain readFrame) .nil)

theorem read_frame_source : FrameSource operations (.plain readFrame) demand :=
  FrameSource.plain (environment := .empty) (input := .scalar) (output := .scalar) (.bind (.perform rfl .reference))

theorem before_release_rows : Rows operations tables beforeRelease [] := by
  apply Rows.push (outward := []) read_frame_source
  · decide
  · exact .push .cell rfl .nil

theorem after_release_rows : Rows operations tables afterRelease demand :=
  .push .cell (residual_empty _) (.push read_frame_source rfl .nil)

theorem provider_position_matters :
    checkFootprint [] ([] : Footprint) = true ∧ checkFootprint [] demand = false ∧
    checkFootprint (contextOf tables afterRelease) demand = true := by decide

theorem released_provider_cannot_check_suffix : ¬ Checked operations tables [] afterRelease := by
  intro checked
  cases checked with
  | push cellSource cellAccepted remaining => cases remaining with
      | push source accepted rest => cases source with
          | plain context => cases context with
              | bind body =>
                  have impossible := CallableProtection.actual_request_admitted
                    (show CheckedAt operations _ [] readCode _ from ⟨_, body, accepted⟩)
                  contradiction

def dormant : Stack := .live 5 .unit .unit beforeRelease .none .nil

theorem dormant_rows : Rows operations tables dormant [] :=
  .live (rows_sources before_release_rows) .nil

theorem dormant_provider_is_not_active : checkFootprint (contextOf tables dormant) demand = false := by decide

theorem cleanup_frame_source : FrameSource operations (.armed DisposalProtection.Examples.cellAction)
    (qualify true demand) :=
  FrameSource.armed (environment := .empty) (.lambda (.bind (.perform rfl .reference) .unit))

theorem cleanup_without_provider_exports_protected_row :
    Rows operations tables (.push (.armed DisposalProtection.Examples.cellAction) .nil) (qualify true demand) :=
  .push cleanup_frame_source rfl .nil

theorem cleanup_with_remaining_provider_is_ready :
    CallableProtectionFrames.Armed operations tables DisposalProtection.Examples.cellAction
      (.push (.cell 42 8 .none .unit) .nil) := by
  apply armed_pending
  apply rows_checked (row := []) _ rfl
  apply Rows.push (outward := []) cleanup_frame_source
  · decide
  · exact .push .cell rfl .nil

open CallableFrames.Examples (captured outside clauseBody s1 functionType)
open CallableContracts.Examples (identity scalar)
open GenerativeFrames.Examples (declarations)
open CallableJoint.CaptureExample (policy initial atRequest liveState source_enters_request)
open PhaseBoundaries.Examples (phaseTicket functionContract)

theorem callable_capture_rows : Rows operations tables captured [] :=
  .push (FrameSource.plain (environment := .empty) (input := .scalar) (output := functionContract)
    (.bind (.lambda (.variable rfl)))) (residual_empty _)
    (.push .handler rfl .nil)

theorem callable_outside_rows : Rows operations tables outside [] := by
  have frame : FrameSource operations (.plain CallableFrames.Examples.outsideCall) [] :=
    FrameSource.plain (environment := .empty) (input := functionContract) (output := .scalar)
      (ContextSummarizes.appFunction (latent := []) .integer)
  exact .push frame rfl .nil

theorem actual_resume_has_checked_saved_frames : ∃ state registry,
    NamedAccessSteps [] initial state ∧
    CompletionJoint.Valid declarations policy registry [] state .integer [] scalar ∧
    Checked operations tables [] state.execution.configuration.stack ∧
    state.execution.configuration.expression = .integer 17 ∧ Owner.ticket 5 ∈ state.execution.completed := by
  obtain ⟨registry, row, captureStep, capturedValid, _, _, _⟩ := PhaseBoundaries.Examples.capture_joined
  have position : Focus clauseBody (.resume 10 (.integer 17)) (.bind 4 (.variable 4)) :=
    .bind (by intro impossible; cases impossible)
  obtain ⟨plain, shape, savedScope, focusStep, focusedValid⟩ := CompletionJoint.focus_preserves capturedValid position
  have waiting : Checked operations tables [] ((Stack.push (.plain plain) .nil).append outside) := by
    apply rows_checked (row := []) _ rfl
    exact .push (FrameSource.plain (environment := .empty) (input := functionContract) (output := functionContract)
      (by rw [shape]; exact .bind (.variable rfl)))
      (residual_empty _) callable_outside_rows
  have source : ClauseProtection.Derives operations policy (phaseTicket false)
      (contextOf tables (.push (.plain plain) .nil)) CallableProtection.Environment.empty
      .available (.resume 10 (.integer 17)) .consumed functionContract [] := by
    have argument : ClauseProtection.Derives operations policy (phaseTicket false)
        (contextOf tables (.push (.plain plain) .nil)) CallableProtection.Environment.empty
        .available (.integer 17) .available .scalar [] := .stable .integer rfl
    exact ClauseProtection.Derives.resume (ticket := phaseTicket false) (resumedRow := []) rfl argument rfl
  obtain ⟨resumeStep, resumedValid, checked⟩ := resume_joint (front := .push (.plain plain) .nil)
    focusedValid source callable_capture_rows (by decide) waiting rfl trivial
  refine ⟨_, registry, ?_, resumedValid, checked, rfl, ?_⟩
  · exact CallableJoint.execution_append source_enters_request.1
      (.next captureStep (.next focusStep (.next resumeStep (.refl _))))
  · simp [ScopedPortJoint.advanceState]

end Examples

end Ash.OneShot.SavedFrameRequirements

#print axioms Ash.OneShot.SavedFrameRequirements.rows_sources
#print axioms Ash.OneShot.SavedFrameRequirements.rows_checked
#print axioms Ash.OneShot.SavedFrameRequirements.checked_rows
#print axioms Ash.OneShot.SavedFrameRequirements.checked_iff_rows
#print axioms Ash.OneShot.SavedFrameRequirements.sources_append
#print axioms Ash.OneShot.SavedFrameRequirements.checked_append
#print axioms Ash.OneShot.SavedFrameRequirements.checked_decompose
#print axioms Ash.OneShot.SavedFrameRequirements.capture_rows
#print axioms Ash.OneShot.SavedFrameRequirements.resume_recomposition
#print axioms Ash.OneShot.SavedFrameRequirements.plain_pending
#print axioms Ash.OneShot.SavedFrameRequirements.armed_pending
#print axioms Ash.OneShot.SavedFrameRequirements.source_resume_checks_caller
#print axioms Ash.OneShot.SavedFrameRequirements.resume_joint
#print axioms Ash.OneShot.SavedFrameRequirements.Examples.read_frame_source
#print axioms Ash.OneShot.SavedFrameRequirements.Examples.before_release_rows
#print axioms Ash.OneShot.SavedFrameRequirements.Examples.after_release_rows
#print axioms Ash.OneShot.SavedFrameRequirements.Examples.provider_position_matters
#print axioms Ash.OneShot.SavedFrameRequirements.Examples.released_provider_cannot_check_suffix
#print axioms Ash.OneShot.SavedFrameRequirements.Examples.dormant_rows
#print axioms Ash.OneShot.SavedFrameRequirements.Examples.dormant_provider_is_not_active
#print axioms Ash.OneShot.SavedFrameRequirements.Examples.cleanup_frame_source
#print axioms Ash.OneShot.SavedFrameRequirements.Examples.cleanup_without_provider_exports_protected_row
#print axioms Ash.OneShot.SavedFrameRequirements.Examples.cleanup_with_remaining_provider_is_ready
#print axioms Ash.OneShot.SavedFrameRequirements.Examples.callable_capture_rows
#print axioms Ash.OneShot.SavedFrameRequirements.Examples.callable_outside_rows
#print axioms Ash.OneShot.SavedFrameRequirements.Examples.actual_resume_has_checked_saved_frames
