import SourceScheduledHandlerInterfaceAdmission
import SourceConsumingHandlerAdmissionExamples
import SourceScheduledInvocationInterfaceExamples
import SourceScheduledSourceRecheckingExamples

/-! Handler entry from finite original-source interfaces, plus exact-selection
counterexamples. The admitted clause still has independent continuation checks. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission.HandlerInterfaceExamples
open SourceConsumingClauseAnnotations (Body ClauseBounds)
open SourceScheduledRetainedInterfaces (Interfaces)
open SourceScheduledCapabilityAnnotations (Retained recipeLaws)
open SourceScheduledSourceRechecking (OperationSource ReceiverChange)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open SourceDependencyCapture.Examples (effectE resumeTable resumeDependencies)
open HandlerExamples (context saved whole waiting actions phases)
open SourceScheduledInvocationInterfaceExamples (declarations declaration_recipes)

def savedInterface : Interfaces [] saved := .plain .nil [(effectE, 0)] .request .request .nil

def bounds : ClauseBounds declarations :=
  .cons (.available ⟨[], []⟩) (.available ⟨[], []⟩) .nil

def clause := Plan.handler (effect := effectE) (table := resumeTable) [] declarations
  (.choice (.invoke (key := ⟨19, .resume⟩)) (.invoke (key := ⟨19, .dispose⟩)))
def body : Body [] 19 clause := .handler bounds declaration_recipes (.choice .resume .dispose)

/-- Original source is expanded, not replaced by a compact target witness. -/
theorem saved_view (permission) : OperationSource (context.resumption permission).val savedInterface := by
  let extracted := (OperationSource.extract (context.resumption permission).val).get (by rfl)
  exact extracted.property

/-- Both receiver changes are generated from source views and table checks. -/
theorem admitted : At (recipeLaws []) (fun evidence => evidence) body context :=
  .handler_interfaces bounds declaration_recipes
    (fun _ => savedInterface) saved_view (fun _ => rfl)
    (fun _ => .nil) (fun _ => .operations) (fun _ => rfl) (.choice .resume .dispose)

theorem checked : body.BoundCheck [] [] actions phases
    (.live 19 (.plain (.request effectE 0) .nil) (.handler effectE resumeTable resumeDependencies .nil))
    (.handler effectE resumeTable resumeDependencies .nil) .nil :=
  ⟨rfl, ⟨⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩⟩⟩

theorem scheduled : SourceScheduledChecks.Local [] actions phases [] clause whole :=
  admitted.scheduled checked

/-- A matching empty table is rejected at precisely the intercepted request. -/
theorem masking_rejected : SourceContextualHints.checkRequirements
    (.handler effectE [] [] .nil)
    (SourceHandlerRequirements.intercepted effectE savedInterface.exposed) = false := rfl

/-- Unrelated handlers need no capability for this saved request. This is
finite filtering, not a commutation or scope-exchange principle. -/
theorem unrelated_receiver : ReceiverChange [] actions (OwnerPhaseTransitions.spend phases 19)
    (context.resumption rfl).val
    (.handler (effect := .user 987 []) (table := []) (families := []) (required := [])
      (.spent (owner := 19) waiting)) :=
  (saved_view rfl).handler_here (context.resumption rfl).property rfl

/-- The primitive check cannot grant a second use of the bound continuation. -/
theorem consumed_rejected : ¬ body.BoundCheck [] [] actions (OwnerPhaseTransitions.spend phases 19)
    (.live 19 (.plain (.request effectE 0) .nil) (.handler effectE resumeTable resumeDependencies .nil))
    (.handler effectE resumeTable resumeDependencies .nil) .nil := by
  intro ready
  have available := ready.2.1.2.1
  change OwnerPhaseTransitions.spend phases 19 19 = .available at available
  simp [OwnerPhaseTransitions.spend] at available

namespace Callback

def saved := Forest.cleanup (needs := [effectE]) (.request (effect := effectE) (operation := 0)) .nil
def whole := Forest.live (owner := 19) saved waiting
def interface : Interfaces [] saved := .cleanup .nil [(effectE, 0)] .request .request .nil

def context : Context [] 19 [effectE] actions phases whole .nil saved waiting where
  cut := .hit
  before := .nil
  resumption := fun _ => ⟨.cleanup (.operations [(effectE, 0)] .request .request) (.operations .nil), ⟨rfl, rfl⟩⟩
  closing := fun _ => ⟨.cleanup (.operations [(effectE, 0)] .request .request) (.operations .nil), ⟨rfl, rfl⟩⟩
  disposal := fun _ => ⟨rfl, rfl⟩
  after := .handler (.operations .nil)
  tailReady := ⟨rfl, rfl⟩

/-- Both source views include a real callback. Closing insertion preserves
its protected running receiver and derives its operation requirement. -/
theorem admitted : At (recipeLaws [effectE]) (fun evidence => evidence) body context :=
  .handler_interfaces bounds declaration_recipes
    (fun _ => interface) (fun _ => .cleanup .operations) (fun _ => rfl)
    (fun _ => interface) (fun _ => .cleanup .operations) (fun _ => rfl) (.choice .resume .dispose)

theorem scheduled : SourceScheduledChecks.Local [effectE] actions phases [] clause whole := by
  apply admitted.scheduled (resumeRequired := []) (closeRequired := [])
  exact ⟨rfl, ⟨⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩⟩⟩

end Callback

/-- A disposing override fails the uniform interface test but remains admitted
by the already-proved richer fresh-capture path. The new rule does not remove it. -/
theorem disposing_uses_richer_path :
    SourceContextualHints.checkRequirements
      (.handler effectE SourceDependencyCapture.Examples.disposeTable
        SourceDependencyCapture.Examples.disposeDependencies .nil)
      (SourceHandlerRequirements.intercepted effectE savedInterface.exposed) = false ∧
    At (recipeLaws []) (fun evidence => evidence) HandlerExamples.body context :=
  ⟨rfl, HandlerExamples.admitted⟩

end Ash.OneShot.SourceConsumingCleanupAdmission.HandlerInterfaceExamples

namespace Ash.OneShot.SourceScheduledSourceRechecking.HandlerInterfaceBoundaryExamples
open SourceScheduledRetainedInterfaces (Interfaces)
open SourceScheduledCapabilityAnnotations (Retained)
open SourceRetainedPlans (Forest)
open SourceDependencyCapture.Examples (effectE resumeTable resumeDependencies)

def request := Forest.plain (.request (effect := effectE) (operation := 0)) .nil
def dormant := Forest.live (owner := 38) request .nil
def dormantInterface : Interfaces [] dormant :=
  .live .nil (.plain .nil [(effectE, 0)] .request .request .nil) .nil

/-- Dormant source is checked at its actual suffix; dormancy does not drop it. -/
theorem dormant_required : dormantInterface.exposed = [(effectE, 0)] := rfl

def shielded := Forest.plain (.request (effect := .cell 4) (operation := 0))
  (.cell (identity := 4) .nil)
def shieldedInterface : Interfaces [4] shielded :=
  .plain (.cell .nil) [(.cell 4, 0)] .request .request (.cell .nil)
def shieldedSource : Retained [4] shielded .nil :=
  .plain (.operations [(.cell 4, 0)] .request .request) (.cell (.operations .nil))

theorem shielded_view : OperationSource shieldedSource shieldedInterface := .plain (.cell .operations)

/-- The retained builtin supplies the request before the new empty matching
handler is reached. The exact finite test therefore admits this receiver. -/
theorem shielded_receiver : ReceiverChange [] (fun _ => none) (OwnerPhaseTransitions.available [])
    shieldedSource (.handler (effect := .cell 4) (table := []) (families := []) (required := []) .nil) :=
  shielded_view.handler_here ⟨rfl, rfl⟩ rfl

def dormantCell := Forest.live (owner := 38) (Forest.cell (identity := 4) .nil)
  (Forest.plain (.request (effect := .cell 4) (operation := 0)) .nil)
def dormantCellInterface : Interfaces [4] dormantCell :=
  .live (.plain .request .nil) (.cell .nil) (.plain .nil [(.cell 4, 0)] .request .request .nil)

/-- A cell in a dormant capture does not supply a sibling's active request. -/
theorem dormant_cell_not_shielding : dormantCellInterface.exposed = [(.cell 4, 0)] := rfl

/-- Extraction failure is not invalidity: this existing valid source has a
callback invoking an outside owner and must use the richer recursive path. -/
theorem invocation_source_retained :
    SourceScheduledSourceRechecking.Examples.original.Valid []
      SourceScheduledSourceRechecking.Examples.actions SourceScheduledSourceRechecking.Examples.phases ∧
    OperationSource.extract SourceScheduledSourceRechecking.Examples.original = none :=
  ⟨SourceScheduledSourceRechecking.Examples.original_valid, rfl⟩

end Ash.OneShot.SourceScheduledSourceRechecking.HandlerInterfaceBoundaryExamples

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.HandlerInterfaceExamples.saved_view
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.HandlerInterfaceExamples.admitted
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.HandlerInterfaceExamples.checked
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.HandlerInterfaceExamples.scheduled
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.HandlerInterfaceExamples.masking_rejected
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.HandlerInterfaceExamples.unrelated_receiver
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.HandlerInterfaceExamples.consumed_rejected
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.HandlerInterfaceBoundaryExamples.dormant_required
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.HandlerInterfaceBoundaryExamples.shielded_view
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.HandlerInterfaceBoundaryExamples.shielded_receiver
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.HandlerInterfaceBoundaryExamples.dormant_cell_not_shielding

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.HandlerInterfaceExamples.Callback.admitted
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.HandlerInterfaceExamples.Callback.scheduled

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.HandlerInterfaceExamples.disposing_uses_richer_path
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.HandlerInterfaceBoundaryExamples.invocation_source_retained
