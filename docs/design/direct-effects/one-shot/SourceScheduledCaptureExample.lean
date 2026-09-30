import SourceScheduledCapture
import SourceScheduledInitialHandlerExample

/-! The admitted handler example reaches a complete capture successor through
handler installation and capture, using the public state endpoints. -/
namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.HandledExample
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Contract)
open RecursiveRequirements (Requirements)
open InstallationSupport

/-- Initial source admission supplies both transition predecessors. The result
retains the two operational events and the complete state after capture. -/
theorem admitted_capture :
    ∃ handler : HandlerData, ∃ tables : CallableProtectionFrames.Tables,
    ∃ families : SourceDependencyFrames.Families, ∃ required : SourceContextualRechecking.Required,
    ∃ allocated : Contract, ∃ inputRows : ValueRows allocated.input, ∃ answerRows : ValueRows allocated.answer,
    ∃ captureScope : SourceDependencyCapture.Scope, ∃ saved : Requirements allocated.resumeDemand,
    ∃ rights : Syntax.OneShotRights, ∃ next : Configuration,
      LexicalUnwind.Event (initialRun expression).execution
        ⟨.eval ⟨.perform (Instantiation.freezeEffect effect) 0 .unit, .none, .push (.handler handler) .nil⟩, [], []⟩ ∧
      LexicalUnwind.Event
        ⟨.eval ⟨.perform (Instantiation.freezeEffect effect) 0 .unit, .none, .push (.handler handler) .nil⟩, [], []⟩
        ⟨.eval next, [.ticket 0], []⟩ ∧
      InstallationState operations policy (contracts.insert 0 allocated) tables families required []
        (fun other => if other = 0 then some captureScope else annotations other) [] [] [handler.activation]
        [(⟨0, .resume⟩, ⟨allocated.resumeDemand, saved⟩)] []
        [(⟨0, .resume⟩, ⟨allocated.resumeDemand, saved⟩)] [] ports (owners.insert 0 inputRows answerRows)
        emptyRows (.value .unit) (.value .unit)
        ⟨⟨.eval next, [.ticket 0], []⟩, actions.insert 0 rights⟩ := by
  let initialTables : CallableProtectionFrames.Tables := fun _ => []
  let initialFamilies : SourceDependencyFrames.Families := fun _ => .nil
  let initialRequired : SourceContextualRechecking.Required := fun _ => []
  have initial := handled_discard_initial (tables := initialTables)
    (families := initialFamilies) (required := initialRequired)
  obtain ⟨handler, tables, families, required, _fresh, _scope, effectSame, _clauses, _agree, installed, state⟩ :=
    initial.install_handler
  have closed : ClosedValue Code.unit := ⟨trivial, rfl, by intro name member; cases member⟩
  obtain ⟨allocated, inputRows, answerRows, captureScope, saved, rights, next, captured, after⟩ :=
    state.capture_successor (HandlerCut.hit handler .nil effectSame) closed 0 (by decide) [] none
  exact ⟨handler, tables, families, required, allocated, inputRows, answerRows,
    captureScope, saved, rights, next, installed, captured, after⟩

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.HandledExample
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.HandledExample.admitted_capture
