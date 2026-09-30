import SourceScheduledCleanupInterfaces

/-! Regression fixture for mode-sensitive value accounting. The ordinary pending
requirements count caller code skipped by the later unwind resume and therefore
fail their finite check. SourceScheduledContextualAccounting reuses this exact
site to supply a contextual value root and common source admission at [0, 1].
The actual plug and bind steps are retained below; no initial-reachability or
all-transition preservation claim follows from the fixture.
-/

namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.ValuePendingDiagnostic
open ScopedExpressions ScopedExecution ProtectionContracts
open RecursiveRequirements (Requirements)
open AuthenticatedResumeExample AuthenticatedBindResumeExample

theorem resumeSource (environment : SourcePlannedTyping.Environment) :
    SourcePlannedSources.Expression operations policy contracts [] [] runtimeScope environment
      (.resume 9 .unit) .unit [0] resumeReq (.sequence .pure (.invoke (key := ⟨0, .resume⟩))) :=
  .resume (show contracts 0 = some (contract 0) from rfl) rfl rfl .unit
    (by simp [contract]) (by intro x member; cases member)

theorem resumeAuth (environmentRows : EnvironmentRows environment) :
    Auth operations policy ports owners environmentRows (resumeSource environment) .unit currentRows := by
  apply Auth.resume (operand := SourcePlannedSources.Expression.unit)
    (known := show contracts 0 = some (contract 0) from rfl) (resolved := rfl)
    (permission := rfl) (admitted := by simp [contract]) (formed := by intro x member; cases member)
  exact .unit

theorem bodySource : SourcePlannedSources.Expression operations policy contracts [] [] runtimeScope
    (SourcePlannedTyping.Environment.extend (fun _ => none) 11 .unit) program .unit [0, 0] programReq
    (SourcePlanSignatures.signature programPlan) := .bind (resumeSource _) (resumeSource _)

theorem bodyAuth : Auth operations policy ports owners (emptyRows.extend 11 .unit)
    bodySource .unit programRows := .bind (resumeAuth _) (resumeAuth _)

def frame : PlainData := ⟨.bind 11 program, runtimeScope, .unit, .unit, [0, 0], rfl⟩
def stack : Stack := .push (.plain frame) parentStack
def context := Context.plain programRows parentContext
def requirements : Requirements [0, 0, 1] :=
  .sequence (programReq.prepend (OwnerPhases.ofStack tables parentStack)) liveReq

theorem frameSource : SourcePlannedSources.Context operations policy contracts [] (fun _ => none) [] runtimeScope
    frame.context .unit .unit [0, 0] programReq (SourcePlanSignatures.signature programPlan) := .bind bodySource

theorem frameAuth : AuthContext operations policy ports owners emptyRows frameSource .unit .unit programRows :=
  .bind bodyAuth

theorem pendingSource : Source stack (.value .unit) (.value .unit) [0, 0, 1] requirements
    (.plain (.sequence (.sequence .pure (.invoke ⟨0, .resume⟩)) (.sequence .pure (.invoke ⟨0, .resume⟩))) (.live 0 (.running .nil) (.live 1 .nil (.running .nil)))) :=
  .push (.ordinary (.plain (plain := frame) (input := .unit) (output := .unit) (demand := [0, 0])
    (requirements := programReq) (allowed := []) frameSource (.bound rfl) rfl rfl programCertified)) liveSource

theorem pendingRows : Rich pendingSource (.value .unit) (.value .unit) context :=
  .push (.ordinary (.plain (data := frame) (plan := programPlan) (source := frameSource) (rows := programRows)
    (inputRows := .unit) (outputRows := .unit) (scopeKnown := .bound rfl) (inputAnnotation := rfl) (outputAnnotation := rfl)
    (certified := programCertified) frameAuth)) liveRows

def site : ExecutionSite [] operations policy contracts tables families required [] actions
    (OwnerPhaseTransitions.available (ownedTickets parentStack)) [] [] resumes [] ports owners emptyRows
    (.value .unit) (.value .unit) where
  expression := .unit
  runtimeScope := runtimeScope
  stack := stack
  result := .unit
  resultRows := .unit
  allowed := []
  dependencies := .pure
  plan := .pure
  rows := .pure
  sourceDemand := []
  sourceRequirements := empty
  receiving := _
  hints := _
  context := context
  current := SourceAdmission.Admitted.of_source .unit .unit .pure pendingRows.forget.source
  certified := pureCertified
  scopeTyped := ⟨_, .bound rfl⟩
  pendingDemand := [0, 0, 1]
  pendingRequirements := requirements
  pending := pendingSource
  coherent := pendingRows
  retained := .plain (programCertificate.reindex_context parentContext.append_nil_pack.symm) pendingCertificate
  currentResource := .pure
  retainedResource := .plain
    (AuthenticatedBindResumeExample.site.currentResource.reindex_context parentContext.append_nil_pack.symm)
    AuthenticatedBindResumeExample.site.retainedResource

theorem current_value_root_unchecked :
    ¬ RecursiveRequirements.Checked entries receiving phases (annotateDisposals requirements) row :=
  legacy_demand_rejected

theorem plug_to_ready_bind : RawStep ⟨site.expression, site.runtimeScope, site.stack⟩
    ⟨.bind 11 .unit program, runtimeScope, parentStack⟩ [] [] :=
  .plug frame .unit ⟨trivial, rfl, by simp [Code.dependencies]⟩ runtimeScope parentStack

theorem ready_bind_to_program : RawStep ⟨.bind 11 .unit program, runtimeScope, parentStack⟩
    ⟨program, runtimeScope, parentStack⟩ [] [] := by
  simpa [program, Code.subst] using RawStep.bind 11 .unit program runtimeScope parentStack
    ⟨trivial, rfl, by simp [Code.dependencies]⟩ (by simp [program, ClosedExcept, Code.dependencies])

theorem program_checked :
    ExecutionRoot operations policy contracts tables families required [] actions
      (OwnerPhaseTransitions.available (ownedTickets parentStack)) [] [] resumes [] ports owners emptyRows
      (.value .unit) (.value .unit) AuthenticatedBindResumeExample.site (bindRoot : Requirements [0, 1]) ∧
    RecursiveRequirements.Checked (annotateDisposalStore resumes) []
      (OwnerPhaseTransitions.available (ownedTickets parentStack)) (annotateDisposals bindRoot) [] :=
  ⟨parentRoot, bindRootChecked⟩

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.ValuePendingDiagnostic
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.ValuePendingDiagnostic.site
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.ValuePendingDiagnostic.current_value_root_unchecked
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.ValuePendingDiagnostic.ready_bind_to_program

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.ValuePendingDiagnostic.plug_to_ready_bind
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.ValuePendingDiagnostic.program_checked
