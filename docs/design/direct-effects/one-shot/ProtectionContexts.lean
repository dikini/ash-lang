import ClosingAdmission

/-!
Ordered interpretation contexts with two incoming protection modes. This is the
context-realization component of source capture admission, not a complete source
typing judgment. Protection includes recursively owned dormant continuations.
-/

namespace Ash.OneShot.ProtectionContexts

variable {control : Control}

def frameProtected (frame : Frame) : Bool := match frame.kind with
  | .running _ | .closing _ | .finishing _ | .retiring _ => true
  | _ => false

def protectedMode : Control → Bool
  | .nil => false
  | .push frame rest => frameProtected frame || protectedMode rest
  | .live _ _ _ saved rest => protectedMode saved || protectedMode rest
  | .spent _ _ rest => protectedMode rest

theorem protected_mode_iff : protectedMode control = true ↔ control.protected ≠ [] := by
  induction control with
  | nil => simp [protectedMode, Control.protected]
  | push frame rest ih => cases kind : frame.kind <;>
      simp_all [protectedMode, frameProtected, Control.protected]
  | live owner input answer saved rest ihSaved ihRest =>
      simp_all [protectedMode, Control.protected]
      by_cases empty : saved.protected = [] <;> simp [empty]
  | spent owner answer rest ih => exact ih

@[simp] theorem protected_mode_append (front tail : Control) :
    protectedMode (front.append tail) = (protectedMode front || protectedMode tail) := by
  induction front with
  | nil => rfl
  | push frame rest ih => simp [Control.append, protectedMode, ih, Bool.or_assoc]
  | live owner input answer saved rest ihSaved ihRest =>
      simp [Control.append, protectedMode, ihRest, Bool.or_assoc]
  | spent owner answer rest ih => exact ih

inductive Entry where
  | interpretation : Instance → Target → Entry
  | barrier : Bool → Entry
  deriving DecidableEq, Repr

abbrev Context := List Entry

def pushFrame (frame : Frame) (tail : Context) : Context := match frame.kind with
  | .handler effect activation => .interpretation effect (.source activation) :: tail
  | .resource identity => .interpretation (.cell identity) (.builtin identity) :: tail
  | _ => .barrier (frameProtected frame) :: tail

/-- Dormant interpretations are not active. Their protection remains owned by
    the live boundary and therefore contributes a barrier at that boundary. -/
def contextOf : Control → Context
  | .nil => []
  | .push frame rest => pushFrame frame (contextOf rest)
  | .live _ _ _ saved rest => .barrier (protectedMode saved) :: contextOf rest
  | .spent _ _ rest => contextOf rest

def select (requested : Instance) : Context → Bool → Option (Target × Bool)
  | [], _ => none
  | .barrier held :: rest, incoming => select requested rest (incoming || held)
  | .interpretation effect target :: rest, incoming =>
      if requested = effect then some (target, incoming) else select requested rest incoming

theorem select_miss (frame : Frame) (miss : frame.target ≠ some requested) :
    select requested (pushFrame frame tail) incoming =
      select requested tail (incoming || frameProtected frame) := by
  rcases frame with ⟨kind, input, output, access, pending, requests⟩
  cases kind <;> simp_all [pushFrame, select, Frame.target, frameProtected, eq_comm]

theorem select_target (control : Control) :
    (select requested (contextOf control) incoming).map Prod.fst = control.resolve requested := by
  induction control generalizing incoming with
  | nil => rfl
  | push frame rest ih =>
      cases kind : frame.kind <;> simp [contextOf, pushFrame, select, Control.resolve,
        Frame.resolve, kind, ih]
      all_goals split
      all_goals first | rfl | exact ih
  | live owner input answer saved rest ihSaved ihRest =>
      exact ihRest
  | spent owner answer rest ih => exact ih

/-- A concrete source cut receives exactly the protection of its captured
    prefix. Both active protected frames and dormant owned captures count. -/
theorem source_cut_mode (cut : SourceCut requested whole capture tail) :
    ∃ activation, ∀ incoming,
      select requested (contextOf whole) incoming =
        some (.source activation, incoming || protectedMode capture) := by
  induction cut with
  | hit frame activation tail kind =>
      exact ⟨activation, fun incoming => by simp [contextOf, pushFrame, kind,
        select, protectedMode, frameProtected]⟩
  | push frame rest capture tail miss next ih =>
      obtain ⟨activation, selected⟩ := ih
      exact ⟨activation, fun incoming => by
        rw [contextOf, select_miss frame miss, selected]
        simp [protectedMode, Bool.or_assoc]⟩
  | live owner input answer saved rest capture tail next ih =>
      obtain ⟨activation, selected⟩ := ih
      exact ⟨activation, fun incoming => by
        simp only [contextOf, select, selected, protectedMode, Bool.or_assoc]⟩
  | spent owner answer rest capture tail next ih => exact ih

theorem scoped_cut_mode
    (cut : ScopedExecution.HandlerCut requested whole capture tail handler) :
    ∀ incoming, select requested (contextOf whole.erase) incoming =
      some (.source handler.activation, incoming || protectedMode capture.erase) := by
  induction cut with
  | hit handler tail same =>
      intro incoming
      simp [ScopedExecution.Stack.erase, ScopedExecution.ExecFrame.erase,
        ScopedExecution.HandlerData.erase, contextOf, pushFrame, select, same,
        protectedMode, frameProtected]
  | push frame rest capture tail handler miss next ih =>
      intro incoming
      change select requested (pushFrame frame.erase (contextOf rest.erase)) incoming = _
      rw [select_miss frame.erase miss, ih]
      simp [ScopedExecution.Stack.erase, protectedMode, Bool.or_assoc]
  | live owner input answer saved scope rest capture tail handler next ih =>
      intro incoming
      simp only [ScopedExecution.Stack.erase, contextOf, select, ih, protectedMode, Bool.or_assoc]
  | spent owner answer scope rest capture tail handler next ih => exact ih

/-- Capture transports the mode into the selected clause's live owner. It
    cannot disappear merely because the running frame is no longer active. -/
theorem clause_entry_mode :
    contextOf (.live owner input answer capture tail) =
      .barrier (protectedMode capture) :: contextOf tail := rfl

theorem capture_preserves_protection (cut : SourceCut requested whole capture tail) :
    protectedMode (.live owner input answer capture tail) = protectedMode whole := by
  rw [cut_decompose (sourceCut_is_cut cut), protected_mode_append]
  rfl

theorem resume_preserves_protection (capture front tail : Control) :
    protectedMode (capture.append (front.append (.spent owner answer tail))) =
      protectedMode (front.append (.live owner input answer capture tail)) := by
  simp [protectedMode, Bool.or_left_comm]

/-- This is a necessary mode condition on a selected clause contract. Other
    closing requirements and the clause body's propagated mode remain separate. -/
def SupportsMode (dispose held : Bool) : Prop := held = true → dispose = false

theorem protected_selection_forbids_disposal
    (cut : SourceCut requested whole capture tail)
    (selected : select requested (contextOf whole) false = some (target, mode))
    (supported : SupportsMode dispose mode) (held : capture.protected ≠ []) : dispose = false := by
  obtain ⟨activation, exactMode⟩ := source_cut_mode cut
  have same := (exactMode false).symm.trans selected
  have modes := congrArg (fun value => value.map Prod.snd) same
  simp only [Bool.false_or, Option.map_some, Option.some.injEq] at modes
  exact supported (modes ▸ protected_mode_iff.mpr held)

namespace Examples

def effectE : Instance := .user 0 []
def effectF : Instance := .user 1 []
def running : Frame := ⟨.running 7, .unit, .unit, [], [], []⟩
def handlerE : Frame := ⟨.handler effectE 11, .unit, .unit, [], [], []⟩
def handlerF : Frame := ⟨.handler effectF 22, .unit, .unit, [], [], []⟩
def savedE : Control := .push running (.push handlerE .nil)
def clauseE : Control := .push ⟨.bind, .unit, .unit, [], [8], []⟩
  (.live 8 .unit .unit savedE (.push handlerF .nil))
def captureF : Control := .push ⟨.bind, .unit, .unit, [], [8], []⟩
  (.live 8 .unit .unit savedE (.push handlerF .nil))

theorem forwarded_cut : SourceCut effectF clauseE captureF .nil := by
  refine .push _ _ _ _ (by decide) ?_
  exact .live _ _ _ _ _ _ _ (.hit handlerF 22 .nil rfl)

/-- An inner handler stops before the running frame and can support an
    unprotected capture even while cleanup is executing. -/
theorem inner_handler_unprotected : select effectE
    (contextOf (.push handlerE (.push running .nil))) false = some (.source 11, false) := by decide

theorem outward_callback_protected : select effectE (contextOf savedE) false =
    some (.source 11, true) := by decide

/-- The E clause's outward F request captures E's dormant running cleanup. -/
theorem forwarded_clause_protected : select effectF (contextOf clauseE) false =
    some (.source 22, true) := by decide

theorem internal_pending_work_passes :
    ClosingAdmission.checkInternalUses captureF.liveTickets captureF.pending = true := by decide

theorem forwarded_disposal_rejected : ClosingAdmission.checkedDisposal captureF .nil = none := by decide

theorem spent_marker_adds_no_protection : select effectF
    (contextOf (.spent 8 .unit (.push handlerF .nil))) false = some (.source 22, false) := by decide

end Examples

end Ash.OneShot.ProtectionContexts

#print axioms Ash.OneShot.ProtectionContexts.protected_mode_iff
#print axioms Ash.OneShot.ProtectionContexts.protected_mode_append
#print axioms Ash.OneShot.ProtectionContexts.select_miss
#print axioms Ash.OneShot.ProtectionContexts.select_target
#print axioms Ash.OneShot.ProtectionContexts.source_cut_mode
#print axioms Ash.OneShot.ProtectionContexts.scoped_cut_mode
#print axioms Ash.OneShot.ProtectionContexts.clause_entry_mode
#print axioms Ash.OneShot.ProtectionContexts.capture_preserves_protection
#print axioms Ash.OneShot.ProtectionContexts.resume_preserves_protection
#print axioms Ash.OneShot.ProtectionContexts.protected_selection_forbids_disposal
#print axioms Ash.OneShot.ProtectionContexts.Examples.inner_handler_unprotected
#print axioms Ash.OneShot.ProtectionContexts.Examples.forwarded_cut
#print axioms Ash.OneShot.ProtectionContexts.Examples.outward_callback_protected
#print axioms Ash.OneShot.ProtectionContexts.Examples.forwarded_clause_protected
#print axioms Ash.OneShot.ProtectionContexts.Examples.internal_pending_work_passes
#print axioms Ash.OneShot.ProtectionContexts.Examples.forwarded_disposal_rejected
#print axioms Ash.OneShot.ProtectionContexts.Examples.spent_marker_adds_no_protection
