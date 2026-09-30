import SourceScheduledInstallationTransport

/-! Installed handler declaration support for the one-shot experiment. -/

namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.ParameterSensitiveBoundary
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Value Operations)

/-- Finite support of the actual body. A parameter contributes its port only
where it occurs free; ticket variables contribute no resource support. -/
def bodySupport (parameter : Nat) (input : Value) (body : Code) : List Nat :=
  ScopedPorts.Support.evaluate
    (ScopedPorts.Support.extend ScopedPorts.Support.empty parameter input.erase.erase.port.resources)
    body.dependencies

/-- This is the substitution lemma already used by source annotations. The
only new calculation is the exact per-declaration support list above. -/
theorem substituted_body_support
    {ports : OperationRows operations} {owners : ContractRows contracts}
    {environmentRows : EnvironmentRows environment}
    (authenticated : Auth operations policy ports owners environmentRows
      (source : SourcePlannedSources.Expression operations policy contracts world allowed scope environment
        operand input demand requirements checking) inputRows rows)
    (closed : ClosedValue operand)
    (bound : bodySupport parameter input body ⊆ available) :
    Syntax.resourceDependencies (body.subst parameter operand).dependencies ⊆ available := by
  have support := (ScopedPorts.Support.substitution_support_bound (environment := ScopedPorts.Support.empty)
    body parameter closed (authenticated.value_support closed.1)).trans bound
  simpa only [ScopedPorts.Support.empty_evaluation] using support


end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.ParameterSensitiveBoundary
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.ParameterSensitiveBoundary.substituted_body_support

namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.ParameterSensitiveBoundary
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Operations)

/-- Canonical finite static annotation. Missing operation entries contribute
no input-port assumption; actual selection below requires the same typed lookup. -/
def declarationSupport (operations : Operations) (effect : Instance) : Clauses → List Nat
  | .nil => []
  | .cons operation parameter _ body rest =>
      (match operations effect operation with
       | none => []
       | some (input, _) => bodySupport parameter input body) ++ declarationSupport operations effect rest

theorem declarationSupport_selected
    (selected : ClauseAt operation clauses parameter binder body)
    (known : operations effect operation = some (input, output)) :
    bodySupport parameter input body ⊆ declarationSupport operations effect clauses := by
  induction selected with
  | hit =>
      simp only [declarationSupport, known]
      exact List.subset_append_left _ _
  | pass different rest ih => exact ih.trans (List.subset_append_right _ _)

/-- A proof-only view of physical control. It preserves every frame kind and
resource scope; only handler declaration support is checked by this view. -/
def frameView (operations : Operations) (entry : ExecFrame) : Frame :=
  { entry.erase with access := match entry with
      | .handler handler => declarationSupport operations handler.effectInst handler.clauses
      | _ => [] }

def stackView (operations : Operations) : Stack → Control
  | .nil => .nil
  | .push entry tail => .push (frameView operations entry) (stackView operations tail)
  | .live owner input answer saved _ tail => .live owner input answer (stackView operations saved) (stackView operations tail)
  | .spent owner answer _ tail => .spent owner answer (stackView operations tail)

theorem frameView_visible (entry : ExecFrame) : (frameView operations entry).visible = entry.erase.visible := rfl
theorem frameView_target (entry : ExecFrame) : (frameView operations entry).target = entry.erase.target := rfl

theorem stackView_visible (stack : Stack) : (stackView operations stack).visible = stack.erase.visible := by
  induction stack with
  | nil => rfl
  | push entry tail ih => exact congrArg (entry.erase.visible ++ ·) ih
  | live owner input answer saved scope tail ihSaved ihTail => exact ihTail
  | spent owner answer scope tail ih => exact ih

theorem stackView_append (front tail : Stack) :
    stackView operations (front.append tail) = (stackView operations front).append (stackView operations tail) := by
  induction front <;> simp_all [stackView, Stack.append, Control.append]

theorem cut_support_view
    (cut : HandlerCut requested whole captured tail handler) :
    Ash.OneShot.Cut requested (stackView operations whole) (stackView operations captured) (stackView operations tail) := by
  induction cut with
  | hit handler tail same => exact .hit _ _ (by simpa [frameView, ExecFrame.erase, HandlerData.erase, Frame.target] using same)
  | push frame rest cap tail handler miss next ih => exact .push _ _ _ _ miss ih
  | live owner input answer saved scope rest captured tail handler next ih => exact .live _ _ _ _ _ _ _ ih
  | spent owner answer scope rest captured tail handler next ih => exact .spent _ _ _ _ _ ih

theorem selected_support
    (cut : HandlerCut requested whole captured tail handler)
    (supported : Supported (stackView operations whole) ambient) :
    declarationSupport operations handler.effectInst handler.clauses ⊆ tail.erase.visible ++ ambient := by
  induction cut with
  | hit handler tail same => cases supported with
    | push frame rest ambient next access => simpa only [stackView_visible, frameView] using access
  | push frame rest captured tail handler miss next ih => cases supported with
    | push frame rest ambient next access => exact ih next
  | live owner input answer saved scope rest captured tail handler next ih => cases supported with
    | live owner input answer saved rest ambient capture next => exact ih next
  | spent owner answer scope rest captured tail handler next ih => cases supported with
    | spent owner answer rest ambient next => exact ih next

theorem install_support
    (supported : Supported (stackView operations tail) ambient)
    (checked : declarationSupport operations handler.effectInst handler.clauses ⊆ tail.erase.visible ++ ambient) :
    Supported (stackView operations (.push (.handler handler) tail)) ambient :=
  .push _ _ _ supported (by simpa only [stackView_visible, frameView] using checked)

theorem capture_support
    (cut : HandlerCut requested whole captured tail handler)
    (supported : Supported (stackView operations whole) ambient) :
    Supported (stackView operations (.live owner input answer captured caller tail)) ambient :=
  capture_preserves_support (cut_support_view cut) supported

theorem resume_support {front captured tail : Stack}
    (supported : Supported (stackView operations (front.append (.live owner input answer captured caller tail))) ambient) :
    Supported (stackView operations (captured.append (front.append (.spent owner answer caller tail)))) ambient := by
  simpa only [stackView_append, stackView] using resume_preserves_support
    (by simpa only [stackView_append, stackView] using supported)

/-- The six administrative unwind cases reuse the same structural support
argument. No declaration annotation is recomputed at a later receiver. -/
theorem advance_support (step : LexicalUnwind.Advance before after discharged)
    (supported : Supported (stackView operations before) ambient) :
    Supported (stackView operations after) ambient := by
  cases step with
  | plain | handler | cell | retire => cases supported with
    | push frame rest ambient next access => exact next
  | spent => cases supported with
    | spent owner answer rest ambient next => exact next
  | live => cases supported with
    | live owner input answer saved rest ambient capture next =>
      rw [stackView_append]
      apply supported_append
      · simpa [stackView, frameView, ExecFrame.erase, CloseItem.frame, Control.visible, Frame.visible] using capture
      · exact .push _ _ _ next (List.nil_subset _)

private theorem cut_effect (cut : HandlerCut requested whole captured tail handler) :
    handler.effectInst = requested := by
  induction cut <;> assumption

/-- The common-state resource facet can consume the retained support view
without an extra public capture-boundary premise. -/
theorem capture_access_from_view
    {ports : OperationRows operations} {owners : ContractRows contracts}
    {environmentRows : EnvironmentRows environment}
    (authenticated : Auth operations policy ports owners environmentRows
      (source : SourcePlannedSources.Expression operations policy contracts world allowed scope environment
        operand input demand requirements checking) inputRows rows)
    (known : operations requested operation = some (input, output))
    (closed : ClosedValue operand)
    (cut : HandlerCut requested whole captured tail handler)
    (selected : ClauseAt operation handler.clauses parameter binder body)
    (retained : Supported (stackView operations whole) ambient)
    (control : Supported whole.erase ambient) :
    AccessValid ⟨body.subst parameter operand, .ticket binder owner,
      .live owner result handler.answer captured handler.scope tail⟩ ambient := by
  have effectSame := cut_effect cut
  have bound := (declarationSupport_selected selected known).trans
    (by simpa only [effectSame] using selected_support cut retained)
  refine ⟨capture_preserves_support (sourceCut_is_cut (handler_cut_erases cut)) control, ?_⟩
  exact substituted_body_support authenticated closed bound

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.ParameterSensitiveBoundary
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.ParameterSensitiveBoundary.declarationSupport_selected
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.ParameterSensitiveBoundary.selected_support
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.ParameterSensitiveBoundary.install_support
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.ParameterSensitiveBoundary.capture_support
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.ParameterSensitiveBoundary.resume_support
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.ParameterSensitiveBoundary.advance_support

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.ParameterSensitiveBoundary.capture_access_from_view

namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open ScopedExpressions ScopedExecution ProtectionContracts
open ParameterSensitiveBoundary

private theorem empty_port_support : LambdaPortCaptureSupport.portSupport (fun _ => none) = ScopedPorts.Support.empty := rfl

/-- Authentication ties every actual installed clause to the finite annotation
stored in the same declaration rows. The installation environment is empty. -/
theorem AuthDeclarations.canonical_support
    {ports : OperationRows operations} {owners : ContractRows contracts}
    {environmentRows : EnvironmentRows (fun _ => none)}
    {plans : SourceDeclarationPlans.ClausePlans clauses families}
    {answerRows : ValueRows answer} {rows : ClauseRows (SourcePlanSignatures.clauseSignatures plans)}
    {source : SourcePlannedSources.Declarations operations policy contracts world (fun _ => none) allowed effect answer clauses table plans}
    (checked : AuthDeclarations operations policy ports owners environmentRows answerRows source rows) :
    declarationSupport operations effect clauses ⊆ rows.resourceSupport := by
  induction clauses using Clauses.rec (motive_1 := fun _ => True) generalizing table families with
  | nil => cases checked; exact List.nil_subset _
  | cons operation parameter binder code rest ihCode ihRest =>
    cases checked with
    | cons ordinary protectedMode rest support =>
      have previous := ihRest rest
      change declarationSupport operations effect (.cons operation parameter binder code _) ⊆ _ ++ _
      simp_all only [declarationSupport, bodySupport, LambdaPortCaptureSupport.portSupport_extend, empty_port_support]
      intro name member
      rcases List.mem_append.mp member with member | member
      · exact List.mem_append_left _ (support member)
      · exact List.mem_append_right _ (previous member)
  | _ => trivial

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.AuthDeclarations.canonical_support
namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.ParameterSensitiveBoundary
open ScopedExpressions ScopedExecution ProtectionContracts Instantiation
open SourcePlannedTyping (Operations)

/-- The only new support obligation is local to installing a handler. The
source checker supplies it before the transition. -/
def InstallationReady (operations : Operations) (ambient : List Nat)
    (machine : LexicalUnwind.Machine) : Prop :=
  ∀ (handler : HandlerData) body tail,
    machine = .eval ⟨.handle (freezeEffect handler.effectInst) body handler.clauses, handler.scope, tail⟩ →
    declarationSupport operations handler.effectInst handler.clauses ⊆ tail.erase.visible ++ ambient

theorem cell_update_view (update : CellUpdate identity old new before after) :
    stackView operations before = stackView operations after := by
  induction update <;> simp_all [stackView, frameView, ExecFrame.erase]

theorem discard_support {front cap tail : Stack}
    (supported : Supported (stackView operations (front.append (.live owner input answer cap caller tail))) ambient) :
    Supported (stackView operations (cap.append (.push (.closing identity scope)
      (front.append (.spent owner answer caller tail))))) ambient := by
  have resumed := resume_support supported
  rw [stackView_append] at resumed
  obtain ⟨saved, rest⟩ := supported_decompose (stackView operations cap) resumed
  simp only [stackView_append, stackView]
  apply supported_append
  · simpa [stackView_append, stackView, Control.visible, frameView, ExecFrame.erase, closeFrame, Frame.visible, List.append_assoc] using saved
  · exact .push _ _ _ (by simpa only [stackView_append, stackView] using rest) (List.nil_subset _)

/-- All 32 lexical transition cases preserve installed declaration support.
The local installation premise is derived from source evidence by the state
layer; capture, resumption, and abandonment reuse structural support lemmas. -/
theorem transition_support
    (step : LexicalUnwind.Transition before after created discharged)
    (supported : Supported (stackView operations before.stack) ambient)
    (ready : InstallationReady operations ambient before) :
    Supported (stackView operations after.stack) ambient := by
  cases step with
  | evaluate raw allowed =>
    cases raw with
    | bind | beta | ifTrue | ifFalse => exact supported
    | enterHandler handler body tail => exact install_support supported (ready handler body tail rfl)
    | focus | enterCell | enterCleanup => exact .push _ _ _ supported (List.nil_subset _)
    | plug | leaveHandler | leaveCell | finishCleanup | finishClose | retire =>
      cases supported with
      | push frame rest ambient next access => exact next
    | startCleanup => cases supported with
      | push frame rest ambient next access => exact .push _ _ _ next (List.nil_subset _)
    | capture requested operation parameter binder ticket operand body scope whole cap tail handler operationResult selection clause closed environmentReady =>
      exact capture_support selection supported
    | resume => exact resume_support supported
    | discard => exact False.elim allowed
    | leaveClause => cases supported with
      | spent owner answer rest ambient next => exact next
    | readCell identity payload scope before after selected => exact (cell_update_view selected) ▸ supported
    | writeCell identity old new scope before after selected => exact (cell_update_view selected) ▸ supported
  | advance step => exact advance_support step supported
  | startCleanup => cases supported with
    | push frame rest ambient next access => exact .push _ _ _ next (List.nil_subset _)
  | finishCleanup | finishClose | retireValue | closeValue => cases supported with
    | push frame rest ambient next access => exact next
  | discard => exact discard_support supported

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.ParameterSensitiveBoundary
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.ParameterSensitiveBoundary.cell_update_view
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.ParameterSensitiveBoundary.discard_support
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.ParameterSensitiveBoundary.transition_support

namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport
open ScopedExpressions ScopedExecution ProtectionContracts
open ParameterSensitiveBoundary

theorem admitted_handler_support
    (current : SourceAdmission.Admitted operations policy contracts ports owners (fun _ => none) emptyRows
      world installations allowed outward runtimeScope actions phases budget tables families context stack
      (.handle (Instantiation.freezeEffect effect) code arms) result demand requirements checking resultRows rows)
    (checked : CodeChecked ambient outward current.certificate) :
    declarationSupport operations effect arms ⊆ stack.erase.visible ++ ambient := by
  generalize frozen : Instantiation.freezeEffect effect = syntaxEffect at current
  rcases current with ⟨previous, certificate⟩
  change CodeChecked ambient outward certificate at checked
  rcases previous with ⟨source, authenticated, localCheck, cleanupBudget, contextSource⟩
  cases authenticated with
  | handler bodyAuth declarationsAuth =>
    cases freeze_effect_injective frozen
    have bound := declarationsAuth.canonical_support.trans checked.handler_supported
    simpa only [contextSource.matching.erases.visible_resources] using bound

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.admitted_handler_support

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.ParameterSensitiveBoundary.frameView_visible
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.ParameterSensitiveBoundary.frameView_target
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.ParameterSensitiveBoundary.stackView_visible
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.ParameterSensitiveBoundary.stackView_append
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.ParameterSensitiveBoundary.cut_support_view
