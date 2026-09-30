import SourceConsumingCleanupAdmissionExamples

/-! Handler admission over a nonempty saved continuation. Installing a disposer
changes a saved request from a resumptive operation into a selected request.
The source derivation reconstructs its closing check before resuming the owner. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission.HandlerExamples
open SourceConsumingClauseAnnotations (Body ClauseBounds)
open SourceScheduledCapabilityAnnotations (Code Retained recipeLaws)
open SourceScheduledSourceRechecking (Expression ReceiverChange)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceContextualHints (Hints)
open SourceDependencyCapture.Examples
  (effectE resumeTable resumeDependencies disposeTable disposeDependencies)
open OwnerPhaseTransitions (Phases spend)

def actions : Syntax.UsageTickets := fun owner => if owner = 19 then some ⟨true, true⟩ else none
def phases : Phases := OwnerPhaseTransitions.available [19]
def waiting : Forest (Hints.handler (effect := effectE) (table := resumeTable)
    (families := resumeDependencies) [] .nil) := .handler .nil
def saved := Forest.plain (.request (effect := effectE) (operation := 0)) .nil
def whole := Forest.live (owner := 19) saved waiting

def savedRequest : Code [] (.request (effect := effectE) (operation := 0)) (.spent (owner := 19) waiting) :=
  .operations [(effectE, 0)] .request .request

def context : Context [] 19 [] actions phases whole .nil saved waiting where
  cut := .hit
  before := .nil
  resumption := fun _ => ⟨.plain savedRequest (.operations .nil), ⟨rfl, rfl⟩⟩
  closing := fun _ => ⟨.operations .nil, rfl⟩
  disposal := fun _ => ⟨rfl, rfl⟩
  after := .handler (.operations .nil)
  tailReady := ⟨rfl, rfl⟩

def clauses : ScopedExpressions.Clauses := .cons 0 1 9 (.discard 9) .nil
def plans : ClausePlans clauses disposeDependencies := .cons (.available (fun _ => .invoke)) .unavailable .nil
def bounds : ClauseBounds plans := .cons (.available ⟨[], []⟩) .unavailable .nil

theorem declared : SourcePlannedRecipeDeclarations.Declarations [] plans :=
  .cons (.available (.dispose rfl)) .unavailable .nil

def clause := Plan.handler (effect := effectE) (table := disposeTable) [] plans
  (.choice (.invoke (key := ⟨19, .resume⟩)) (.invoke (key := ⟨19, .dispose⟩)))
def body : Body [] 19 clause := .handler bounds declared (.choice .resume .dispose)

/-- Selection changes under the newly installed handler. The original request
has no disposal annotation; source callbacks and the new guard supply it. -/
theorem saved_rechecking (permission) : ReceiverChange [] actions (spend phases 19)
    (context.resumption permission).val
    (.handler (effect := effectE) (table := disposeTable) (families := disposeDependencies) (required := [])
      (.spent (owner := 19) waiting)) := by
  apply ReceiverChange.plain
  · exact Expression.freshInterfaces (.hit rfl rfl) (.spent (.handler .nil))
      (.spent (.handler .nil)) (.spent (.handler .nil)) (fun _ => rfl) (by decide)
      (fun _ => .handler .nil)
  · exact .operations .nil rfl

theorem closing_rechecking (permission) : ReceiverChange [] actions (spend phases 19)
    (context.closing permission).val
    (.running (.handler (effect := effectE) (table := disposeTable) (families := disposeDependencies) (required := [])
      (.spent (owner := 19) waiting))) := .operations .nil rfl

theorem admitted : At (recipeLaws []) (fun evidence => evidence) body context :=
  .handler bounds declared saved_rechecking closing_rechecking (.choice .resume .dispose)

theorem checked : body.BoundCheck [] [] actions phases
    (.live 19 (.plain (.request effectE 0) .nil) (.handler effectE resumeTable resumeDependencies .nil))
    (.handler effectE resumeTable resumeDependencies .nil) .nil := by
  exact ⟨rfl, ⟨⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩⟩⟩

theorem scheduled : SourceScheduledChecks.Local [] actions phases [] clause whole :=
  admitted.scheduled checked

/-- A masking interpretation fails the primitive operation check even though
its owner remains available. -/
theorem masking_rejected : SourceContextualHints.checkRequirements
    (.handler effectE [] [] (.spent 19 (.handler effectE resumeTable resumeDependencies .nil)))
    [(effectE, 0)] = false := rfl

/-- Reuse the cleanup/resource example under two nested handlers. The structural
handler rules compose with existing cleanup and fresh-resource rules. -/
def wrapped := Plan.handler (effect := effectE) (table := disposeTable) [] plans
  (Plan.handler (effect := .user 99 []) (table := disposeTable) [] plans Examples.resourceClause)
def wrappedBounds : ClauseBounds plans := .cons (.available ⟨[(.cell 4, 0)], []⟩) .unavailable .nil
def wrappedBody : Body [4] 19 wrapped := .handler wrappedBounds declared (.handler wrappedBounds declared Examples.resourceBody)

theorem wrapped_admitted : At (recipeLaws []) (fun evidence => evidence)
    wrappedBody (Examples.context Examples.phases) := by
  apply At.handler wrappedBounds declared (fun _ => .operations .nil rfl) (fun _ => .operations .nil rfl)
  apply At.handler wrappedBounds declared (fun _ => .empty) (fun _ => .empty)
  refine At.cleanupSource ?_ (fun _ => .empty) (fun _ => .empty) ?_
  · intro request member
    exact List.mem_singleton.mpr (congrArg Prod.fst (List.mem_singleton.mp member))
  · exact .resource (fun _ _ => .sequence (.choice .resume .dispose))

theorem wrapped_source : SourceConsumingClauseAnnotations.Admitted ⟨true, true⟩ [] [] wrappedBody [(.cell 4, 0)] :=
  .handler (.handler Examples.resource_source_admitted rfl (by decide)) rfl (by decide)

theorem wrapped_scheduled : SourceScheduledChecks.Local [] Examples.actions Examples.phases [4] wrapped Examples.whole :=
  wrapped_admitted.scheduled (wrapped_source.at_capture rfl rfl rfl)

end Ash.OneShot.SourceConsumingCleanupAdmission.HandlerExamples

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.HandlerExamples.declared
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.HandlerExamples.saved_rechecking
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.HandlerExamples.closing_rechecking
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.HandlerExamples.admitted
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.HandlerExamples.checked
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.HandlerExamples.scheduled
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.HandlerExamples.masking_rejected
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.HandlerExamples.wrapped_admitted

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.HandlerExamples.wrapped_source
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.HandlerExamples.wrapped_scheduled
