import SourceScheduledPreservation
import SourceScheduledInitialHandlerExample

/-! A concrete admitted program exercises combined preservation across handler
installation and capture. This is a two-event interface regression, not a trace
safety or progress theorem. -/
namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.Examples
open ScopedExpressions ScopedExecution ProtectionContracts
open InitialAdmission InitialAdmission.HandledExample

def initial : Snapshot operations :=
  Snapshot.ofState (handled_discard_initial (tables := fun _ => [])
    (families := fun _ => .nil) (required := fun _ => []))

theorem initial_valid : Valid policy [] [] [] ports emptyRows .unit .unit initial :=
  valid_ofState (handled_discard_initial (tables := fun _ => [])
    (families := fun _ => .nil) (required := fun _ => []))

/-- Combined dispatch chooses the handler metadata, then consumes that exact
successor as the capture predecessor. The fresh ticket witnesses actual capture. -/
theorem admitted_install_capture :
    ∃ middle after : Snapshot operations,
      LexicalUnwind.Event initial.run.execution middle.run.execution ∧
      LexicalUnwind.Event middle.run.execution after.run.execution ∧
      Valid policy [] [] [] ports emptyRows .unit .unit after ∧
      after.run.execution.issued = [.ticket 0] := by
  let install : Request initial := .allocating (.installHandler (effect := effect)
    (body := .perform (Instantiation.freezeEffect effect) 0 .unit)
    (arms := SourceDeclarationPlans.HandledRequest.clauses 0) rfl)
  obtain ⟨middle, installed, realized, valid⟩ := preservation initial_valid install
  change Allocating.Realizes (.installHandler (effect := effect)
    (body := .perform (Instantiation.freezeEffect effect) 0 .unit)
    (arms := SourceDeclarationPlans.HandledRequest.clauses 0) rfl) middle at realized
  cases realized with
  | installHandler handler nextTables nextFamilies nextRequired fresh scope effectEq clauses agree =>
    have closed : ClosedValue Code.unit := ⟨trivial, rfl, by intro name member; cases member⟩
    obtain ⟨after, captured, captureRealized, final⟩ := preservation valid
      (.allocating (.capture (shape := rfl)
        (physical := HandlerCut.hit handler .nil effectEq) closed 0 (by decide) [] none))
    change Allocating.Realizes _ after at captureRealized
    cases captureRealized with
    | capture allocated inputRows answerRows captureScope saved rights next =>
      exact ⟨_, _, installed, captured, final, rfl⟩

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.Examples

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.Examples.initial
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.Examples.initial_valid

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.Examples.admitted_install_capture
