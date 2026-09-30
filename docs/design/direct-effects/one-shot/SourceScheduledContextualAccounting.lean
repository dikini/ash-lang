import SourceScheduledExecutableValueGap

/-! Authenticated regression for the contextual value-root rule. The generic
accounting interpretation, sequencing laws and ownership proofs live with
ExecutionRoot in SourceScheduledCleanupInterfaces. The fixture below reuses the
exact source site whose ordinary pending requirements overcount skipped code.
It establishes checked root and common source admission, not initial reachability
or preservation for every transition.
-/

namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.AccountingExample
open ScopedExpressions ScopedExecution ProtectionContracts
open RecursiveRequirements (Requirements)
open AuthenticatedResumeExample AuthenticatedBindResumeExample

def root : Requirements [0, 1] := bindRoot

/-- The main source fixture supplies the same continuation interpretation. -/
theorem program_run : Accounting.Run [] [] programRows parentContext root := programRun

/-- A returned value runs its pending caller through the same interpretation. -/
theorem value_wait : Accounting.Wait [] [] ValuePendingDiagnostic.site.context .ordinary root :=
  .plain program_run

theorem value_run : Accounting.Run [] [] ValuePendingDiagnostic.site.rows ValuePendingDiagnostic.site.context root :=
  .pure value_wait

/-- Adding a pure initializer leaves this executable root unchanged. -/
theorem initialized_program_run : Accounting.Run [] [] (.sequence Rows.pure programRows) parentContext root :=
  (Accounting.silent_prefix_iff .pure Rows.pure programRows).mpr program_run

theorem root_checked : RecursiveRequirements.Checked (annotateDisposalStore resumes) []
    (OwnerPhaseTransitions.available (ownedTickets parentStack)) (annotateDisposals root) [] :=
  bindRootChecked

/-- Existing source admission and the corrected finite check are independent. -/
theorem authenticated_value_interpretation :
    Accounting.Run [] [] ValuePendingDiagnostic.site.rows ValuePendingDiagnostic.site.context (root : Requirements [0, 1]) ∧
    RecursiveRequirements.Checked (annotateDisposalStore resumes) []
      (OwnerPhaseTransitions.available (ownedTickets ValuePendingDiagnostic.site.stack)) (annotateDisposals root) [] :=
  ⟨value_run, root_checked⟩

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.AccountingExample
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.AccountingExample.program_run
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.AccountingExample.authenticated_value_interpretation

namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.AccountingExample
open ScopedExpressions ScopedExecution ProtectionContracts

/-- The authenticated diagnostic now obtains exact physical ownership from the
generic theorem, rather than a separate calculation of this example's demand. -/
theorem authenticated_value_owned :
    ([0, 1] : List Nat).Perm (ownedTickets ValuePendingDiagnostic.site.stack) :=
  value_run.stack_owned ValuePendingDiagnostic.site.coherent.forget.source (by decide)
    (disposal_annotation root) root_checked

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.AccountingExample
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.AccountingExample.authenticated_value_owned

namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.AccountingExample
open ScopedExpressions ScopedExecution ProtectionContracts
open RecursiveRequirements (Requirements)
open AuthenticatedResumeExample AuthenticatedBindResumeExample

/-- Contextual value accounting supplies an actual root at the existing site. -/
theorem authenticated_value_root :
    ExecutionRoot operations policy contracts tables families required [] actions
      (OwnerPhaseTransitions.available (ownedTickets parentStack)) [] [] resumes [] ports owners emptyRows
      (.value .unit) (.value .unit) ValuePendingDiagnostic.site (root : Requirements [0, 1]) ∧
    RecursiveRequirements.Checked (annotateDisposalStore resumes) []
      (OwnerPhaseTransitions.available (ownedTickets ValuePendingDiagnostic.site.stack)) (annotateDisposals root) [] :=
  ⟨.contextualValue trivial value_wait, root_checked⟩

/-- The same site satisfies the actual common source judgment. This is a
source-admission regression, not an initial reachability or full-state theorem. -/
theorem authenticated_value_source :
    ExecutableSource [] operations policy contracts tables families required [] actions annotations [] []
      resumes resumes [] ports owners emptyRows (.value .unit) (.value .unit)
      (.eval ⟨ValuePendingDiagnostic.site.expression, ValuePendingDiagnostic.site.runtimeScope,
        ValuePendingDiagnostic.site.stack⟩) := by
  apply ExecutableSource.eval ValuePendingDiagnostic.site rfl authenticated_value_root.1
    ?_ .original root_checked (List.Subset.refl _)
  exact .plain (.live rfl (.running .nil) (.live (by simp [annotations]) .nil (.running .nil)))

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.AccountingExample
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.AccountingExample.authenticated_value_root
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.AccountingExample.authenticated_value_source

namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.AccountingExample
open ScopedExpressions ScopedExecution ProtectionContracts
open RecursiveRequirements (Requirements Checked)
open AuthenticatedResumeExample AuthenticatedBindResumeExample

/-- The diagnosed value takes its actual plug and bind steps with authenticated
source and checked contextual accounting retained throughout the two steps. -/
theorem plug_bind_accounted :
    ∃ plugged next : ExecutionSite [] operations policy contracts tables families required [] actions
        (OwnerPhaseTransitions.available (ownedTickets parentStack)) [] [] resumes [] ports owners emptyRows
        (.value .unit) (.value .unit),
    ∃ demand, ∃ requirements : Requirements demand, ∃ row,
      RawStep ⟨ValuePendingDiagnostic.site.expression, ValuePendingDiagnostic.site.runtimeScope,
        ValuePendingDiagnostic.site.stack⟩ ⟨plugged.expression, plugged.runtimeScope, plugged.stack⟩ [] [] ∧
      Accounting.Run [] [] plugged.rows plugged.context root ∧
      RawStep ⟨plugged.expression, plugged.runtimeScope, plugged.stack⟩
        ⟨next.expression, next.runtimeScope, next.stack⟩ [] [] ∧
      next.expression = program ∧ next.runtimeScope = runtimeScope ∧ next.stack = parentStack ∧
      Accounting.Run [] [] next.rows next.context requirements ∧ ([0, 1] : List Nat).Perm demand ∧
      Checked (annotateDisposalStore resumes) [] (OwnerPhaseTransitions.available (ownedTickets parentStack))
        (annotateDisposals requirements) row ∧ row ⊆ [] := by
  obtain ⟨plugged, expressionEq, scopeEq, stackEq, interpreted, _bound, plugStep⟩ :=
    ValuePendingDiagnostic.site.plug_accounting
      ⟨trivial, rfl, by simp [ValuePendingDiagnostic.site, Code.dependencies]⟩ rfl value_wait
  have ready : RecursiveExpressions.Ready plugged.expression := by
    rw [expressionEq]
    exact .bind trivial
  have bindStep : RawStep ⟨plugged.expression, plugged.runtimeScope, plugged.stack⟩
      ⟨program, runtimeScope, parentStack⟩ [] [] := by
    rw [expressionEq, scopeEq, stackEq]
    exact ValuePendingDiagnostic.ready_bind_to_program
  obtain ⟨next, demand, requirements, row, nextExpression, nextScope, nextStack,
    _sameContext, nextRun, sameDemand, checked, bounded, _created, _completed⟩ :=
    plugged.computation_accounting ready bindStep interpreted root_checked
  refine ⟨plugged, next, demand, requirements, row, plugStep, interpreted, ?_,
    nextExpression, nextScope, nextStack, nextRun, sameDemand, checked, bounded⟩
  simpa only [nextExpression, nextScope, nextStack] using bindStep

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.AccountingExample
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.AccountingExample.plug_bind_accounted

namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.AccountingExample
open ScopedExpressions ScopedExecution ProtectionContracts
open RecursiveRequirements (Requirements Checked)
open AuthenticatedResumeExample AuthenticatedBindResumeExample

/-- Scalar records may be absent while the actual captured source is retained. -/
def noScalarRecords : ExecutionSite [] operations policy contracts tables families required [] actions
    (OwnerPhaseTransitions.available (ownedTickets parentStack)) [] [] [] [] ports owners emptyRows
    (.value .unit) (.value .unit) :=
  { childSite with
    coherent := by
      simpa only [resumes, RecursiveTransport.removeOwner, if_true] using (childSite.coherent.remove_records 0) }

theorem no_scalar_run : Accounting.Run [] [] noScalarRecords.rows noScalarRecords.context root := by
  have interpreted := program_run
  cases interpreted with | sequence first => exact first

theorem no_scalar_check : Checked [] [] (OwnerPhaseTransitions.available (ownedTickets parentStack))
    (annotateDisposals root) [] := by
  apply RecursiveRequirements.evaluate_sound
  simp [root, bindRoot, empty, parentStack, captured, tail, ownedTickets, annotateDisposals,
    RecursiveRequirements.evaluate, RecursiveRequirements.evaluateFuel, PhaseRechecking.checkOwners, OwnerPhaseTransitions.available,
    OwnerPhaseTransitions.spendAll, OwnerPhaseTransitions.spend, OwnerSource.exportAt,
    ProtectionResiduals.residual_empty, ProtectionResiduals.merge]

/-- The actual ready resume has a checked successor even without a scalar
record; the original saved source supplies reconstruction in unwind mode. -/
theorem resume_without_scalar_lookup :
    ∃ owner, ∃ next : ExecutionSite [] operations policy contracts tables families required [] actions
        (OwnerPhaseTransitions.spend (OwnerPhaseTransitions.available (ownedTickets parentStack)) owner)
        [] [] (RecursiveTransport.removeOwner owner []) [] ports owners emptyRows (.value .unit) (.value .unit),
    ∃ demand, ∃ requirements : Requirements demand,
      next.expression = .unit ∧
      ExecutionRoot operations policy contracts tables families required [] actions
        (OwnerPhaseTransitions.spend (OwnerPhaseTransitions.available (ownedTickets parentStack)) owner)
        [] [] (RecursiveTransport.removeOwner owner []) [] ports owners emptyRows
        (.value .unit) (.value .unit) next requirements ∧
      Checked (annotateDisposalStore (RecursiveTransport.removeOwner owner [])) []
        (OwnerPhaseTransitions.spend (OwnerPhaseTransitions.available (ownedTickets parentStack)) owner)
        (annotateDisposals requirements) [] ∧
      [0, 1] = owner :: demand ∧
      RawStep ⟨noScalarRecords.expression, noScalarRecords.runtimeScope, noScalarRecords.stack⟩
        ⟨next.expression, next.runtimeScope, next.stack⟩ [] [.ticket owner] := by
  obtain ⟨owner, next, demand, requirements, expression, _scope, rooted, checked, owners, _bound, raw⟩ :=
    noScalarRecords.resume_accounting_successor (entries := []) rfl
      ⟨trivial, rfl, by simp [ScopedExpressions.Code.dependencies]⟩ no_scalar_run no_scalar_check
  exact ⟨owner, next, demand, requirements, expression, rooted, checked, owners, raw⟩

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.AccountingExample
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.AccountingExample.resume_without_scalar_lookup

namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.AccountingExample
open ScopedExpressions ScopedExecution ProtectionContracts
open AuthenticatedResumeExample AuthenticatedBindResumeExample

/-- The scalar-free ready site is admitted by the actual common source
judgment, independently of the separately proved successor construction. -/
theorem no_scalar_source :
    ExecutableSource [] operations policy contracts tables families required [] actions annotations [] []
      [] [] [] ports owners emptyRows (.value .unit) (.value .unit)
      (.eval ⟨noScalarRecords.expression, noScalarRecords.runtimeScope, noScalarRecords.stack⟩) := by
  apply ExecutableSource.eval (annotatedStore := []) noScalarRecords rfl (.contextual no_scalar_run)
    ?_ .original no_scalar_check (List.Subset.refl _)
  exact .plain (.live rfl (.running .nil) (.live (by simp [annotations]) .nil (.running .nil)))

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.AccountingExample
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.AccountingExample.no_scalar_source

namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Accounting
open ScopedExpressions ScopedExecution ProtectionContracts
open RecursiveRequirements (Requirements Checked)

/-- The pure callback runs behind the ordinary completion boundary. -/
theorem pure_cleanup_ordinary :
    Wait [] [] (Context.cleanup (needs := []) [] Rows.pure Context.nil) .ordinary
      (Requirements.request [] []) :=
  .cleanup (.pure (.normal .nil))

/-- Unwind cleanup runs its callback normally and then resumes unwinding. -/
theorem pure_cleanup_unwind :
    Wait [] [] (Context.cleanup (needs := []) [] Rows.pure Context.nil) .unwind
      (Requirements.request [] []) :=
  .cleanup (.pure (.unwinding .nil))

/-- Installation places the callback around the body, without executing it early. -/
theorem install_pure_cleanup :
    Run [] [] (Rows.cleanup (needs := []) [] Rows.pure Rows.pure) Context.nil
      (Requirements.request [] []) :=
  .installCleanup (.pure pure_cleanup_ordinary)

theorem pure_cleanup_root_checked :
    Checked [] [] (OwnerPhaseTransitions.available []) (Requirements.request [] []) [] := by
  apply RecursiveRequirements.evaluate_sound
  simp [RecursiveRequirements.evaluate, RecursiveRequirements.evaluateFuel,
    OwnerSource.exportAt, ProtectionResiduals.residual_empty]

/-- A pure frame added in the retained caller transports either callback mode. -/
theorem pure_cleanup_waiting_frame (mode : LexicalUnwind.UseMode) :
    Wait [] [] (Context.cleanup (needs := []) [] Rows.pure (Context.plain Rows.pure Context.nil)) mode
      (Requirements.request [] []) := by
  have original : Wait [] [] (Context.cleanup (needs := []) [] Rows.pure Context.nil) mode
      (Requirements.request [] []) := by
    cases mode
    · exact pure_cleanup_ordinary
    · exact pure_cleanup_unwind
  exact original.pure_history (.cleanup _ (.add (.same _)))

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Accounting
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Accounting.pure_cleanup_ordinary
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Accounting.pure_cleanup_unwind
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Accounting.install_pure_cleanup
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Accounting.pure_cleanup_root_checked
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Accounting.pure_cleanup_waiting_frame

namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Accounting.IndexedExamples
open ScopedExpressions ScopedExecution ProtectionContracts
open RecursiveRequirements (Requirements)

def handlerRows := Rows.handler (effect := Instance.user 3 []) (table := [])
  (required := []) ClauseRows.nil Rows.pure

def resourceRows := Rows.resource (fun _ => Rows.pure)
def emptyRoot : Requirements [] := .request [] []

theorem handler_interpreted : Run [4] [7] handlerRows Context.nil emptyRoot :=
  .installHandler (fun _ _ => .pure (.handler .nil))

theorem resource_interpreted : Run [4] [7] resourceRows Context.nil emptyRoot :=
  .installResource (fun _ _ => .pure (.cell .nil))

/-- Growth changes only the domains from which fresh names are selected. -/
theorem handler_grown : Run [4, 5] [7, 8] handlerRows Context.nil emptyRoot :=
  handler_interpreted.mono (by simp) (by simp)

theorem resource_grown : Run [4, 5] [7, 8] resourceRows Context.nil emptyRoot :=
  resource_interpreted.mono (by simp) (by simp)

/-- Every name fresh for the actual installation history selects its body. -/
theorem handler_any_fresh (activation : Nat) (fresh : activation ∉ [7, 8]) :
    Run [4, 5] (activation :: [7, 8]) Rows.pure
      (Context.handler (effect := Instance.user 3 []) (table := []) activation ClauseRows.nil Context.nil) emptyRoot :=
  handler_grown.enter_handler fresh

/-- Every name fresh for the actual resource world selects its family instance. -/
theorem resource_any_fresh (identity : Nat) (fresh : identity ∉ [4, 5]) :
    Run ([4, 5] ++ [identity]) [7, 8] Rows.pure
      (Context.cell (identity := identity) Context.nil) emptyRoot :=
  resource_grown.enter_resource fresh

/-- Handler freshness does not silently exclude resource identities. -/
theorem handler_may_use_world_number :
    Run [4, 5] [4, 7, 8] Rows.pure
      (Context.handler (effect := Instance.user 3 []) (table := []) 4 ClauseRows.nil Context.nil) emptyRoot :=
  handler_any_fresh 4 (by decide)

/-- Resource freshness does not silently exclude installation identities. -/
theorem resource_may_use_installation_number :
    Run [4, 5, 7] [7, 8] Rows.pure (Context.cell (identity := 7) Context.nil) emptyRoot :=
  resource_any_fresh 7 (by decide)

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Accounting.IndexedExamples
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Accounting.IndexedExamples.handler_any_fresh
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Accounting.IndexedExamples.resource_any_fresh
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Accounting.IndexedExamples.handler_may_use_world_number
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Accounting.IndexedExamples.resource_may_use_installation_number

namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Accounting.LocalOwnerExamples
open ScopedExpressions ScopedExecution ProtectionContracts
open RecursiveRequirements (Requirements Checked LocalOwner)
open OwnerPhaseTransitions (available)

def effect : Instance := .user 3 []
def offered : ClauseContract := ⟨false, some [], none⟩
def declarations : ClauseRows
    (.cons (operation := 0) ⟨true, false⟩ (.available (fun owner => .invoke (key := ⟨owner, .resume⟩))) .unavailable .nil) :=
  .cons (.available (fun _ => .invoke)) .unavailable .nil
def captured := Context.handler (effect := effect) (table := [(0, offered)]) 2 declarations .nil
def tail := Context.retiring 13 Context.nil
def whole := Context.handler (effect := effect) (table := [(0, offered)]) 2 declarations tail
def emptyRoot : Requirements [] := .request [] []
def localRoot : Requirements [7, 13] := .sequence (.retire 7) (.sequence (.spent 7) (.sequence (.retire 13) emptyRoot))
def outerRoot : Requirements [13] := .sequence emptyRoot (.sequence emptyRoot (.sequence (.retire 13) emptyRoot))

theorem selected : Cut effect 0 whole captured tail offered
    (some (fun owner => .invoke ⟨owner, .resume⟩), none) := rfl

/-- Resuming the bound owner retains the unrelated outer owner until its own
retirement, and revisits only a spent marker for the consumed local owner. -/
theorem body_interpreted : Run [] [2] (Rows.invoke (key := ⟨7, .resume⟩))
    (Context.live (owner := 7) (resumeDemand := []) captured tail) localRoot := by
  apply Run.resume (front := Context.nil) (captured := captured) (tail := tail)
  · exact .hit
  · exact .handler (.spent (.retiring .nil))

theorem local_discharged : LocalOwner 7 .available localRoot outerRoot .consumed :=
  .sequence .retireSelf (.sequence .spentSelf (.sequence (.retireOther (by decide)) .empty))

theorem outer_checked : Checked [] [] (available whole.owned) outerRoot [] := by
  apply RecursiveRequirements.evaluate_sound
  simp [outerRoot, emptyRoot, whole, tail, Context.owned, RecursiveRequirements.evaluate,
    RecursiveRequirements.evaluateFuel, available, OwnerPhaseTransitions.spendAll,
    PhaseRechecking.checkOwners, OwnerSource.exportAt,
    ProtectionResiduals.residual_empty, ProtectionResiduals.merge]

theorem capture_derived_check_and_balance :
    Checked [] [] (available (Context.live (owner := 7) (resumeDemand := []) captured tail).owned) localRoot [] ∧
      [13].Perm whole.owned :=
  body_interpreted.capture_owned selected local_discharged (by simp [whole, tail, Context.owned])
    (by simp [whole, tail, Context.owned]) outer_checked

theorem omission_rejected : ¬ LocalOwner 7 .available emptyRoot emptyRoot .consumed := by
  intro binding
  have length := binding.demand_discharge.length_eq
  contradiction

theorem repeated_retirement_rejected :
    ¬ LocalOwner 7 .available (.sequence (.retire 7) (.retire 7))
      (.sequence emptyRoot emptyRoot) .consumed := by
  intro binding
  have length := binding.demand_discharge.length_eq
  contradiction

theorem premature_spent_rejected :
    ¬ LocalOwner 7 .available (.sequence (.spent 7) (.retire 7))
      (.sequence emptyRoot emptyRoot) .consumed := by
  intro binding
  have evaluated := binding.evaluate_eq (store := []) (receiving := []) (available [])
  simp [emptyRoot, RecursiveRequirements.evaluate, RecursiveRequirements.evaluateFuel,
    RecursiveRequirements.withPhase, OwnerPhaseTransitions.spendAll,
    OwnerSource.exportAt, ProtectionResiduals.residual_empty, ProtectionResiduals.merge] at evaluated

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Accounting.LocalOwnerExamples
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Accounting.LocalOwnerExamples.capture_derived_check_and_balance
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Accounting.LocalOwnerExamples.omission_rejected
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Accounting.LocalOwnerExamples.repeated_retirement_rejected
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Accounting.LocalOwnerExamples.premature_spent_rejected

namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Accounting.RequestExamples
open ScopedExpressions ScopedExecution ProtectionContracts
open RecursiveRequirements (Requirements Checked LocalOwner)
open OwnerPhaseTransitions (available)

def effect : Instance := .user 3 []
def offered : ClauseContract := ⟨false, some [], none⟩
def declarations : ClauseRows
    (.cons (operation := 0) ⟨true, false⟩ (.available (fun owner => .invoke (key := ⟨owner, .resume⟩))) .unavailable .nil) :=
  .cons (.available (fun _ => .invoke)) .unavailable .nil
def captured := Context.handler (effect := effect) (table := [(0, offered)]) 2 declarations .nil
def tail := Context.retiring 13 (Context.spent (owner := 17) Context.nil)
def whole := Context.handler (effect := effect) (table := [(0, offered)]) 2 declarations tail

def emptyRoot : Requirements [] := .request [] []
def localRoot (owner : Nat) (_resumeDemand : List Nat) : Requirements [owner, 13] :=
  .sequence (.retire owner) (.sequence (.spent owner) (.sequence (.retire 13) (.sequence (.spent 17) emptyRoot)))
def outerRoot : Requirements [13] :=
  .sequence emptyRoot (.sequence emptyRoot (.sequence (.retire 13) (.sequence (.spent 17) emptyRoot)))

theorem cut : Cut effect 0 whole captured tail offered
    (some (fun owner => .invoke ⟨owner, .resume⟩), none) := rfl

theorem selected : CapturedClauseRows effect 0 false captured
    (fun owner => Rows.invoke (key := ⟨owner, .resume⟩)) :=
  .selected .here .ordinary

/-- The local continuation is resumed once for every actual fresh marker name
and every supplied resume-demand annotation. Outer retirement/history remains. -/
theorem body_interpreted (owner : Nat) (resumeDemand : List Nat) :
    Run [] [2] (Rows.invoke (key := ⟨owner, .resume⟩))
      (Context.live (owner := owner) (resumeDemand := resumeDemand) captured tail)
      (localRoot owner resumeDemand) := by
  apply Run.resume (front := Context.nil) (captured := captured) (tail := tail)
  · exact .hit
  · exact .handler (.spent (.retiring (.spent .nil)))

theorem local_discharged (owner : Nat) (resumeDemand : List Nat)
    (fresh : owner ∉ whole.ticketNames) :
    LocalOwner owner .available (localRoot owner resumeDemand) outerRoot .consumed := by
  have absent : owner ≠ 13 ∧ owner ≠ 17 := by
    simpa [whole, tail, Context.ticketNames] using fresh
  exact .sequence .retireSelf (.sequence .spentSelf
    (.sequence (.retireOther (Ne.symm absent.1)) (.sequence (.spentOther (Ne.symm absent.2)) .empty)))

/-- The request rule consumes its exact retained selected row family as an
inductive premise and discharges only the newly bound owner. -/
theorem request_interpreted :
    Run [] [2] (Rows.request (effect := effect) (operation := 0)) whole outerRoot :=
  .request (localRoot := localRoot) cut selected
    (fun owner resumeDemand _fresh => body_interpreted owner resumeDemand) local_discharged

theorem outer_checked : Checked [] [] (available whole.owned) outerRoot [] := by
  apply RecursiveRequirements.evaluate_sound
  simp [outerRoot, emptyRoot, whole, tail, Context.owned, RecursiveRequirements.evaluate,
    RecursiveRequirements.evaluateFuel, available, OwnerPhaseTransitions.spendAll, OwnerPhaseTransitions.spend,
    PhaseRechecking.checkOwners, OwnerSource.exportAt,
    ProtectionResiduals.residual_empty, ProtectionResiduals.merge]

theorem request_preserves_outer_ownership : [13].Perm whole.owned :=
  request_interpreted.owned (by simp [whole, tail, Context.owned]) outer_checked

/-- A spent identity is outside ownership but is still excluded from the
request's fresh local-binder domain. -/
theorem spent_alias_excluded : 17 ∉ whole.owned ∧ 17 ∈ whole.ticketNames := by
  simp [whole, tail, Context.owned, Context.ticketNames]

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Accounting.RequestExamples
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Accounting.RequestExamples.request_interpreted
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Accounting.RequestExamples.request_preserves_outer_ownership
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Accounting.RequestExamples.spent_alias_excluded

namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Accounting.RequestExamples
open ScopedExpressions ScopedExecution ProtectionContracts
open RecursiveRequirements (Requirements Checked Store)
open OwnerPhaseTransitions (available)

/-- The checked predecessor supplies the local clause check in a changed record
store and receiver. The spent outer marker is still checked and owner 13 remains. -/
theorem allocated_body_checked (nextStore : Store) (nextReceiving : OwnerPhases.Context) :
    ∃ localDemand, ∃ localRoot : Requirements localDemand,
      Run [] [2] (Rows.invoke (key := ⟨7, .resume⟩))
        (Context.live (owner := 7) (resumeDemand := []) captured tail) localRoot ∧
      Checked nextStore nextReceiving
        (available (Context.live (owner := 7) (resumeDemand := []) captured tail).owned)
        (annotateDisposals localRoot) [] ∧ localDemand.Perm [7, 13] := by
  apply request_interpreted.request_checked_body cut selected 7 []
  · simp [whole, tail, Context.ticketNames]
  · simp [whole, tail, Context.owned]
  · simpa only [outerRoot, emptyRoot, annotateDisposals] using outer_checked

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Accounting.RequestExamples
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Accounting.RequestExamples.allocated_body_checked
