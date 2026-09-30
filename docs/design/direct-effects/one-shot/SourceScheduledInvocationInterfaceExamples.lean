import SourceScheduledInvocationInterfaces

/-! Positive and negative source-plan examples for invocation interfaces.
These do not claim complete rich-expression or initial-program admission. -/
namespace Ash.OneShot.SourceScheduledInvocationInterfaceExamples
open SourceDependencyCapture.Examples (effectF resumeTable resumeDependencies)
open SourceDependencyHandlerGap (actions phases)
open SourceRetainedPlans (Forest)
open SourceContextualHints (Hints)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceScheduledRetainedInterfaces (Interfaces)
open SourceScheduledInvocationInterfaces
open SourceScheduledChecks (Local)

def savedHints : Hints (.plain (.request effectF 0) .nil) := .plain .nil
def saved : Forest savedHints := .plain .request .nil
def savedInterface : Interfaces world saved := .plain .nil [(effectF, 0)] .request .request .nil

def handlerHints : Hints (.handler effectF resumeTable resumeDependencies .nil) := .handler [] .nil
def handler : Forest handlerHints := .handler .nil
def handlerInterface : Interfaces world handler := .handler .nil .nil

def callerHints : Hints (.cleanup [effectF] (.request effectF 0)
    (.handler effectF resumeTable resumeDependencies .nil)) := .cleanup handlerHints
def caller : Forest callerHints := .cleanup .request handler
def callerInterface : Interfaces world caller :=
  .cleanup handler [(effectF, 0)] .request .request handlerInterface

/-- Both the saved request and the effectful caller cleanup are supplied by
the caller's newly installed handler. There is no outer waiting provider. -/
theorem caller_supplies_saved_request :
    Local [] actions phases [] (.invoke (key := ⟨19, .resume⟩))
      (caller.append (.live (owner := 19) saved .nil)) :=
  resume_from_interfaces (.cleanup (.handler .hit)) rfl rfl rfl
    savedInterface callerInterface .nil rfl rfl rfl

/-- Actual clause plans can install that handler and effectful cleanup around
the consuming invocation. Its inner handler has ordinary resumptive recipes. -/
def clauses : ScopedExpressions.Clauses := .cons 0 0 1 (.resume 1 .unit) .nil
def declarations : ClausePlans clauses resumeDependencies :=
  .cons (.available (fun _ => .sequence .pure .invoke))
    (.available (fun _ => .sequence .pure .invoke)) .nil

theorem declaration_recipes : SourcePlannedRecipeDeclarations.Declarations [] declarations :=
  .cons (.available (.silent .pure (.resume rfl)))
    (.available (.silent .pure (.resume rfl))) .nil

def clause (owner : Nat) := Plan.handler (effect := effectF) (table := resumeTable) [] declarations
  (.cleanup (needs := [effectF]) (.request (effect := effectF) (operation := 0))
    (.invoke (key := ⟨owner, .resume⟩)))

theorem handler_and_effectful_cleanup_clause :
    Local [] actions phases [] (clause 19) (.live (owner := 19) saved .nil) := by
  apply Local.handler declaration_recipes declaration_recipes.certified rfl
  apply Local.cleanup
  · exact caller_supplies_saved_request
  · exact SourceScheduledSourceInterfaces.compile .request .request rfl

def closingHints : Hints (.cleanup [effectF] (.request effectF 0) .nil) := .cleanup .nil
def closing : Forest closingHints := .cleanup .request .nil
def closingInterface : Interfaces world closing :=
  .cleanup .nil [(effectF, 0)] .request .request .nil
def disposeActions : Syntax.UsageTickets := fun _ => some ⟨false, true⟩

/-- The same source annotation generates callback admission at the actual
closing scope. The route and disposal permission are checked independently. -/
theorem caller_supplies_disposal_callback :
    Local [effectF] disposeActions phases [] (.invoke (key := ⟨19, .dispose⟩))
      (caller.append (.live (owner := 19) closing .nil)) :=
  dispose_from_interfaces (.cleanup (.handler .hit)) rfl rfl rfl rfl rfl
    closingInterface.callbacks closingInterface.callback_declarations
    callerInterface .nil rfl rfl rfl

/-- An empty nearer handler masks the outer provider. A successful owner
permission check cannot repair the missing operation in retained source. -/
theorem masking_handler_rejected :
    (savedInterface (world := [])).check
      (.handler effectF [] [] (.spent 19 (.handler effectF resumeTable resumeDependencies .nil))) = false := rfl

theorem missing_provider_rejected :
    (savedInterface (world := [])).check (.spent 19 .nil) = false := rfl

/-- Closing removes the saved handler, so a callback previously supplied by
that handler must be checked again. Normal admission alone is insufficient. -/
theorem normal_check_does_not_imply_closing_check :
    (callerInterface (world := [])).check .nil = true ∧
    (callerInterface (world := [])).callbacks.check .nil = false := ⟨rfl, rfl⟩

/-- Passing operation checks do not imply permission to resume. -/
theorem permission_independent :
    (savedInterface (world := [])).check
      (.cleanup [effectF] (.request effectF 0)
        (.handler effectF resumeTable resumeDependencies (.spent 19 .nil))) = true ∧
    SourceContextualInvocationHints.checkResume disposeActions phases 19
      (callerHints.append (.live (owner := 19) savedHints .nil)) = none := ⟨rfl, rfl⟩

/-- The established phase theorem rejects reuse even when every operation
interface still succeeds; no new proof of one-shot accounting is needed. -/
theorem spent_owner_rejected :
    SourceContextualInvocationHints.checkResume actions (OwnerPhaseTransitions.spend phases 19) 19
      (callerHints.append (.live (owner := 19) savedHints .nil)) = none :=
  SourceContextualInvocations.consumed_resume_rejected

end Ash.OneShot.SourceScheduledInvocationInterfaceExamples

#print axioms Ash.OneShot.SourceScheduledInvocationInterfaceExamples.caller_supplies_saved_request
#print axioms Ash.OneShot.SourceScheduledInvocationInterfaceExamples.declaration_recipes
#print axioms Ash.OneShot.SourceScheduledInvocationInterfaceExamples.handler_and_effectful_cleanup_clause
#print axioms Ash.OneShot.SourceScheduledInvocationInterfaceExamples.caller_supplies_disposal_callback
#print axioms Ash.OneShot.SourceScheduledInvocationInterfaceExamples.masking_handler_rejected
#print axioms Ash.OneShot.SourceScheduledInvocationInterfaceExamples.missing_provider_rejected
#print axioms Ash.OneShot.SourceScheduledInvocationInterfaceExamples.normal_check_does_not_imply_closing_check
#print axioms Ash.OneShot.SourceScheduledInvocationInterfaceExamples.permission_independent
#print axioms Ash.OneShot.SourceScheduledInvocationInterfaceExamples.spent_owner_rejected
