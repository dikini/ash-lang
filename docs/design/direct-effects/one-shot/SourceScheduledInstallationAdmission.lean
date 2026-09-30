import SourceScheduledCleanupInterfaces

/-! M0.2 structural installation admission for the one-shot experiment.
The fixed ambient list is an explicit resource allowance. The judgment decorates
existing Code/Pending derivations and reads their exact ClauseRows; separate
AuthDeclarations evidence authenticates those bounds against actual source.
The judgment and transport definitions live beside ExecutionSite so its evidence
uses the same source derivation. This module retains admission examples. -/

namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyChecks.Lexical (ReturnHints)
open SourceDependencyAnnotations (Dependencies ClauseDependencies)
open SourcePlanSignatures (Signature ClauseSignatures)
open OwnerPhaseTransitions (Phases)

namespace Examples

/-- These fixtures test the independent row-admission facet. Authentication of
clause syntax remains the separate AuthDeclarations judgment from M0.1. -/
def effect : Instance := .user 17 []
def declarations : ClauseRows (.cons (operation := 0) ⟨true, true⟩
    (.available (fun _ => .pure)) (.available (fun _ => .pure)) .nil) :=
  .cons (.available (fun _ => .pure)) (.available (fun _ => .pure)) .nil [7]
def table : List (Nat × ClauseContract) := [(0, ⟨false, some [], some []⟩)]

theorem installation {hints : ReturnHints scope} (context : Context hints) :
    SourceAdmission.Code outward actions budget phases world installations
      (.handler (effect := effect) (table := table) (required := []) declarations .pure) context :=
  .handler (fun _ _ => .pure)

theorem lexical_cell : CodeChecked [] outward
    (installation (actions := actions) (budget := budget) (phases := phases)
      (world := world) (installations := installations) (Context.cell (identity := 7) Context.nil)) := by
  apply CodeChecked.handler
  · simp [declarations, ClauseRows.resourceSupport, SourceDependencyCapture.Scope.visibleResources]
  · intro activation fresh
    exact .pure

theorem ambient_allowance : CodeChecked [7] outward
    (installation (actions := actions) (budget := budget) (phases := phases)
      (world := world) (installations := installations) Context.nil) := by
  apply CodeChecked.handler
  · simp [declarations, ClauseRows.resourceSupport, SourceDependencyCapture.Scope.visibleResources]
  · intro activation fresh
    exact .pure

/-- World membership alone is not lexical availability. -/
theorem world_is_not_receiver : ¬ CodeChecked [] outward
    (installation (actions := actions) (budget := budget) (phases := phases)
      (world := [7]) (installations := installations) Context.nil) := by
  intro checked
  have bound := checked.handler_supported
  simp [declarations, ClauseRows.resourceSupport, SourceDependencyCapture.Scope.visibleResources] at bound

/-- The captured cell is dormant; the selected clause can see only its tail. -/
theorem dormant_capture_is_not_receiver : ¬ CodeChecked [] outward
    (installation (actions := actions) (budget := budget) (phases := phases)
      (world := [7]) (installations := installations)
      (Context.live (owner := owner) (resumeDemand := []) (Context.cell (identity := 7) Context.nil) Context.nil)) := by
  intro checked
  have bound := checked.handler_supported
  simp [declarations, ClauseRows.resourceSupport, SourceDependencyCapture.Scope.visibleResources] at bound

/-- A waiting installation with unavailable resources is deliberately skipped
when its plain frame is unwound. -/
theorem unwind_skips_plain : PendingChecked [] outward
    (SourceAdmission.Pending.skipped (actions := actions) (budget := budget) (phases := phases)
      (world := [7]) (installations := installations)
      (rows := Rows.handler (effect := effect) (table := table) (required := []) declarations .pure)
      (SourceAdmission.Pending.nil (outside := Context.nil) (mode := .unwind))) := .skipped .nil

/-- The same nonempty declaration bound remains available under a second
installation, including when those nested rows occur as an application body. -/
theorem nested_application_rows :
    ∃ admitted : SourceAdmission.Code outward actions budget phases world installations
      (.sequence .pure (.sequence .pure
        (.handler (effect := effect) (table := table) (required := []) declarations
          (.handler (effect := effect) (table := table) (required := []) declarations .pure))))
      (Context.cell (identity := 7) Context.nil), CodeChecked [] outward admitted := by
  let admitted : SourceAdmission.Code outward actions budget phases world installations
      (.sequence .pure (.sequence .pure
        (.handler (effect := effect) (table := table) (required := []) declarations
          (.handler (effect := effect) (table := table) (required := []) declarations .pure))))
      (Context.cell (identity := 7) Context.nil) :=
    .sequence .pure (.sequence .pure (.handler (fun _ _ => .handler (fun _ _ => .pure))))
  refine ⟨admitted, ?_⟩
  apply CodeChecked.sequence (first := .pure)
    (second := .sequence .pure (.handler (fun _ _ => .handler (fun _ _ => .pure))))
  · exact .pure
  apply CodeChecked.sequence (first := .pure)
    (second := .handler (fun _ _ => .handler (fun _ _ => .pure)))
  · exact .pure
  apply CodeChecked.handler (body := fun _ _ => .handler (fun _ _ => .pure))
  · simp [declarations, ClauseRows.resourceSupport, SourceDependencyCapture.Scope.visibleResources]
  · intro outer freshOuter
    apply CodeChecked.handler (body := fun _ _ => .pure)
    · simp [declarations, ClauseRows.resourceSupport, SourceDependencyCapture.Scope.visibleResources]
    · intro inner freshInner
      exact .pure

end Examples

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.CodeChecked.handler_supported
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Examples.installation
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Examples.lexical_cell
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Examples.ambient_allowance
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Examples.world_is_not_receiver
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Examples.dormant_capture_is_not_receiver
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Examples.unwind_skips_plain
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Examples.nested_application_rows
