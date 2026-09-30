import CaptureOwnerChecks

/-! Ordered interpretation summaries retaining pending continuation uses.
These are analysis data for the existing control stack, not computation syntax.
Forgetting ownership recovers the established protection context. Selection
retains exactly the owner information of the actual handler cut. -/
namespace Ash.OneShot.OwnerUseContexts

structure Uses where
  owned : List Nat
  pending : List Nat
  deriving DecidableEq, Repr

def Uses.append (first second : Uses) : Uses :=
  ⟨first.owned ++ second.owned, first.pending ++ second.pending⟩

def usesOf (control : Control) : Uses := ⟨control.liveTickets, control.pending⟩

structure Entry where
  interpretation : ProtectionContexts.Entry
  uses : Uses
  deriving DecidableEq, Repr

abbrev Context := List Entry

def frameEntry (frame : Frame) : Entry :=
  let interpretation := match frame.kind with
    | .handler effect activation => ProtectionContexts.Entry.interpretation effect (.source activation)
    | .resource identity => .interpretation (.cell identity) (.builtin identity)
    | _ => .barrier (ProtectionContexts.frameProtected frame)
  ⟨interpretation, ⟨[], frame.pending⟩⟩

/-- A live boundary contributes ownership and pending work of its dormant
capture, while its dormant interpreters remain inactive. -/
def contextOf : Control → Context
  | .nil => []
  | .push frame rest => frameEntry frame :: contextOf rest
  | .live owner _ _ saved rest =>
      ⟨.barrier (ProtectionContexts.protectedMode saved), ⟨owner :: saved.liveTickets, saved.pending⟩⟩ :: contextOf rest
  | .spent _ _ rest => contextOf rest

def forget (context : Context) : ProtectionContexts.Context := context.map Entry.interpretation

structure Selection where
  target : Target
  uses : Uses
  held : Bool
  deriving DecidableEq, Repr

def prependUses (uses : Uses) (held : Bool) (result : Selection) : Selection :=
  ⟨result.target, uses.append result.uses, held || result.held⟩

def select (requested : Instance) : Context → Option Selection
  | [] => none
  | entry :: rest => match entry.interpretation with
    | .barrier held => (select requested rest).map (prependUses entry.uses held)
    | .interpretation effect target =>
        if requested = effect then some ⟨target, entry.uses, false⟩
        else (select requested rest).map (prependUses entry.uses false)

theorem forget_control (control : Control) : forget (contextOf control) = ProtectionContexts.contextOf control := by
  induction control with
  | nil => rfl
  | push frame rest ih =>
    cases kind : frame.kind <;> simp [contextOf, forget, frameEntry, kind,
      ProtectionContexts.contextOf, ProtectionContexts.pushFrame, forget] at * <;> exact ih
  | live owner input answer saved rest ihSaved ihRest =>
    simpa only [contextOf, forget, List.map_cons, ProtectionContexts.contextOf] using congrArg
      (List.cons (.barrier (ProtectionContexts.protectedMode saved))) ihRest
  | spent owner answer rest ih => exact ih

/-- The richer summary selects exactly the previous target and protection
mode. Ownership information does not change nearest-exact interpretation. -/
theorem select_projection (context : Context) :
    (select requested context).map (fun result => (result.target, incoming || result.held)) =
      ProtectionContexts.select requested (forget context) incoming := by
  induction context generalizing incoming with
  | nil => rfl
  | cons entry rest ih =>
    cases entry with
    | mk interpretation uses => cases interpretation with
      | barrier held =>
        have next := ih (incoming := incoming || held)
        cases found : select requested rest with
        | none => simpa [select, forget, found, ProtectionContexts.select] using next
        | some result => simpa [select, forget, found, ProtectionContexts.select,
            prependUses, Bool.or_assoc] using next
      | interpretation effect target =>
        by_cases same : requested = effect
        · simp [select, forget, ProtectionContexts.select, same]
        · simpa only [select, forget, List.map_cons, ProtectionContexts.select, same, if_false,
            Option.map_map, Function.comp_def, prependUses, Bool.false_or] using ih (incoming := incoming)

theorem select_target (control : Control) :
    (select requested (contextOf control)).map Selection.target = control.resolve requested := by
  have projected := congrArg (Option.map Prod.fst) (select_projection (requested := requested) (incoming := false) (contextOf control))
  simpa only [Option.map_map, Function.comp_def, forget_control, ProtectionContexts.select_target] using projected

theorem frame_miss (miss : frame.target ≠ some requested) :
    select requested (frameEntry frame :: tail) =
      (select requested tail).map (prependUses ⟨[], frame.pending⟩ (ProtectionContexts.frameProtected frame)) := by
  cases frame with
  | mk kind input output access pending requests =>
    cases kind <;> simp_all [select, frameEntry, Frame.target, ProtectionContexts.frameProtected, eq_comm]

/-- The existing source-cut derivation supplies the capture boundary. Only
its additional ownership projections are accumulated here. -/
theorem source_cut (cut : SourceCut requested whole capture tail) :
    ∃ activation, select requested (contextOf whole) =
      some ⟨.source activation, usesOf capture, ProtectionContexts.protectedMode capture⟩ := by
  induction cut with
  | hit frame activation tail kind =>
    exact ⟨activation, by simp [contextOf, frameEntry, kind, select, usesOf,
      Control.pending, Control.liveTickets, ProtectionContexts.protectedMode, ProtectionContexts.frameProtected]⟩
  | push frame rest capture tail miss next ih =>
    obtain ⟨activation, selected⟩ := ih
    exact ⟨activation, by simp only [contextOf, frame_miss miss, selected, Option.map_some,
      prependUses, Uses.append, usesOf, Control.liveTickets, Control.pending,
      ProtectionContexts.protectedMode, List.nil_append]⟩
  | live owner input answer saved rest capture tail next ih =>
    obtain ⟨activation, selected⟩ := ih
    exact ⟨activation, by simp only [contextOf, select, selected, Option.map_some,
      prependUses, Uses.append, usesOf, Control.liveTickets, Control.pending,
      ProtectionContexts.protectedMode, List.cons_append]⟩
  | spent owner answer rest capture tail next ih => exact ih

theorem scoped_cut (cut : ScopedExecution.HandlerCut requested whole capture tail handler) :
    select requested (contextOf whole.erase) =
      some ⟨.source handler.activation, usesOf capture.erase, ProtectionContexts.protectedMode capture.erase⟩ := by
  obtain ⟨activation, selected⟩ := source_cut (ScopedExecution.handler_cut_erases cut)
  have projected := select_projection (requested := requested) (incoming := false) (contextOf whole.erase)
  rw [selected, forget_control, ProtectionContexts.scoped_cut_mode cut] at projected
  have same : activation = handler.activation := by simpa using congrArg (fun result => result.map (fun pair => pair.1)) projected
  subst activation
  exact selected

/-- Reuse the established per-cut owner check on the selected summary. -/
def check (requested : Instance) (disposes : Bool) (context : Context) : Bool :=
  match select requested context with
  | none => false
  | some result => !disposes || ClosingAdmission.checkInternalUses result.uses.owned result.uses.pending

theorem scoped_check (cut : ScopedExecution.HandlerCut requested whole capture tail handler) :
    check requested disposes (contextOf whole.erase) = CaptureOwnerChecks.checkOwnerUses disposes capture.erase := by
  simp only [check, scoped_cut cut, CaptureOwnerChecks.checkOwnerUses, usesOf]

theorem context_append (first second : Control) :
    contextOf (first.append second) = contextOf first ++ contextOf second := by
  induction first <;> simp_all [Control.append, contextOf]

/-- The table and owner checks share the operation selected by the ordinary
effect analysis; the context query supplies its exact captured owner summary. -/
def checkSelected (table : List (Nat × ProtectionContracts.ClauseContract))
    (operation : Nat) (requested : Instance) (context : Context) : Bool :=
  match ProtectionContracts.lookup operation table with
  | none => false
  | some offered => check requested offered.dispose context

theorem scoped_selected_check (cut : ScopedExecution.HandlerCut requested whole capture tail handler) :
    checkSelected table operation requested (contextOf whole.erase) =
      CaptureOwnerChecks.checkSelected table operation capture.erase := by
  unfold checkSelected CaptureOwnerChecks.checkSelected
  cases found : ProtectionContracts.lookup operation table with
  | none => rfl
  | some offered => exact scoped_check cut

/-- Existing hereditary capture preservation consumes the summary check.
This establishes the runtime meaning of such source-summary evidence, not
its derivation for every possible future invocation. -/
theorem capture_outside_from_summary
    (source : DeclaredSourceStates.CheckedState operations policy contracts tables world outside scope
      (.perform (Instantiation.freezeEffect requested) operation operand) whole output demand row)
    (cut : ScopedExecution.HandlerCut requested whole capture tail handler)
    (isValue : operand.IsValue) (fresh : contracts owner = none)
    (external : ¬ InternalUses capture.erase.liveTickets capture.erase.pending)
    (checked : checkSelected (tables handler) operation requested (contextOf whole.erase) = true) :
    ∃ (contract : CoherentSourceTypes.Owners.Contract) (after : ScopedExecution.Configuration)
      (nextDemand : List Nat) (nextRow : ProtectionContracts.Footprint),
      contract.closeRow = none ∧
      ScopedExecution.RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩ after [.ticket owner] [] ∧
      DeclaredSourceStates.CheckedState operations policy (contracts.insert owner contract) tables world outside
        after.scope after.expression after.stack output nextDemand nextRow ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ScopedExecution.ownedTickets after.stack = owner :: ScopedExecution.ownedTickets whole := by
  apply CaptureOwnerChecks.capture_outside_request source cut isValue fresh external
  rw [← scoped_selected_check cut]
  exact checked

/-- Source focusing computes the pending-owner entry from the syntactic
context and its scope translation. Reuse the existing hereditary focus proof;
no independently chosen pending-use annotation is supplied. -/
theorem source_focus_summary
    (source : DeclaredSourceStates.CheckedState operations policy contracts tables world outside scope
      whole stack output demand row)
    (focus : ScopedExecution.Focus whole child position) :
    ∃ plain : ScopedExecution.PlainData,
      ScopedExecution.RawStep ⟨whole, scope, stack⟩ ⟨child, scope, .push (.plain plain) stack⟩ [] [] ∧
      DeclaredSourceStates.CheckedState operations policy contracts tables world outside scope child
        (.push (.plain plain) stack) output demand row ∧
      scope.translate position.dependencies = some plain.pending ∧
      contextOf (ScopedExecution.Stack.erase (.push (.plain plain) stack)) =
        ⟨.barrier false, ⟨[], plain.pending⟩⟩ :: contextOf stack.erase := by
  obtain ⟨plain, step, checked, contextSame, scopeSame, trace⟩ :=
    DeclaredSourceStates.focus_preserves source focus
  refine ⟨plain, step, checked, ?_, rfl⟩
  simpa only [contextSame, scopeSame] using plain.translated

end Ash.OneShot.OwnerUseContexts

#print axioms Ash.OneShot.OwnerUseContexts.forget_control
#print axioms Ash.OneShot.OwnerUseContexts.select_projection
#print axioms Ash.OneShot.OwnerUseContexts.select_target
#print axioms Ash.OneShot.OwnerUseContexts.frame_miss
#print axioms Ash.OneShot.OwnerUseContexts.source_cut
#print axioms Ash.OneShot.OwnerUseContexts.scoped_cut
#print axioms Ash.OneShot.OwnerUseContexts.scoped_check
#print axioms Ash.OneShot.OwnerUseContexts.context_append

#print axioms Ash.OneShot.OwnerUseContexts.scoped_selected_check
#print axioms Ash.OneShot.OwnerUseContexts.capture_outside_from_summary

#print axioms Ash.OneShot.OwnerUseContexts.source_focus_summary
