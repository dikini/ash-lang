import SourceScheduledInterceptAdmission

/-! New disposal capability is compiled from original normal callback evidence.
Counterexamples distinguish changed callback routing, missing operation supply
and a pending dependency on an owner outside the new capture. -/
namespace Ash.OneShot.SourceScheduledInterceptAdmission.Examples
open SourceDependencyCapture (Scope checkCapture)
open SourceContextualHints (Hints checkCapability)
open SourceRetainedPlans (Forest)
open SourceScheduledCapabilityAnnotations (Code DeclarationLaws)
open SourceScheduledCallbackInterfaces (Interfaces Declared)
open SourceScheduledCallbackRoutes (Covered normalCheck)
open SourceDependencyCapture.Examples
  (effectE effectF resumeTable resumeDependencies disposeTable disposeDependencies)
open SourceScheduledHandlerSelection (Intercept)
open SourceDependencyOwners (PendingWithin owners)

def waiting : Forest (Hints.handler (effect := effectE) (table := resumeTable) (families := resumeDependencies) []
    (.handler (effect := effectF) (table := resumeTable) (families := resumeDependencies) [] .nil)) :=
  .handler (.handler .nil)
def before := Forest.cleanup (needs := [effectF]) (.request (effect := effectF) (operation := 0)) waiting
def after := Forest.cleanup (needs := [effectF]) (.request (effect := effectF) (operation := 0))
  (.handler (effect := effectE) (table := disposeTable) (families := disposeDependencies) (required := []) waiting)
def saved := Forest.cleanup (needs := [effectF]) (.request (effect := effectF) (operation := 0))
  (.handler (effect := effectE) (table := disposeTable) (families := disposeDependencies) (required := []) .nil)

def source : Interfaces before := .cleanup waiting [(effectF, 0)] .request (.handler (.handler .nil))

theorem source_declared : Declared [] source := .cleanup .request (.handler (.handler .nil))
theorem source_covered : Covered source := .cleanup
  (by intro request member; exact List.mem_singleton.mpr (congrArg Prod.fst (List.mem_singleton.mp member)))
  (.handler (.handler .nil))
theorem original_normal : normalCheck source .nil = true := rfl

theorem intercepted : Intercept effectE 0 ⟨true, some [], none⟩
    (some SourceDependencyCapture.Examples.disposeFamily, none)
    disposeTable disposeDependencies [] before after saved waiting := .cleanup (.hit rfl rfl)

def oldRequest : Code [] (.request (effect := effectE) (operation := 0)) before :=
  .operations [(effectE, 0)] .request .request

theorem old_request_resumptive : oldRequest.Valid [effectF] actions phases := rfl

/-- No old disposal schedule is an input. Only the old whole callback metadata,
its normal check, the new guard and structural pending-owner bound are used. -/
theorem new_disposer : ∃ annotation : Code [] (.request (effect := effectE) (operation := 0)) after,
    annotation.Valid [effectF] actions phases :=
  Intercept.annotation (fun source => source) intercepted source source_declared source_covered
    (fun _ => original_normal) (by decide) (fun _ => .cleanup (.handler .nil))

theorem fresh_adaptation : SourceScheduledHandlerAdaptation.Adapt [effectF] actions
    (.handler effectE disposeTable disposeDependencies []) phases []
    (.request (effect := effectE) (operation := 0)) before after :=
  Intercept.adaptation intercepted source source_declared source_covered
    (fun _ => original_normal) (by decide) (fun _ => .cleanup (.handler .nil))

/-- The new disposer is intentionally not a resumptive request capability. -/
theorem control_capability_changed : checkCapability
    (.cleanup [effectF] (.request effectF 0) (.handler effectE disposeTable disposeDependencies
      (.handler effectE resumeTable resumeDependencies (.handler effectF resumeTable resumeDependencies .nil))))
    effectE 0 = false := rfl

def conflictingBefore := Forest.cleanup (needs := [effectE]) (.request (effect := effectE) (operation := 0)) waiting
def conflictingAfter := Forest.cleanup (needs := [effectE]) (.request (effect := effectE) (operation := 0))
  (.handler (effect := effectE) (table := disposeTable) (families := disposeDependencies) (required := []) waiting)
def conflictingSource : Interfaces conflictingBefore :=
  .cleanup waiting [(effectE, 0)] .request (.handler (.handler .nil))

/-- Normal availability holds before insertion. Closing the newly inserted
handler would remove the callback's interpretation, so the primitive guard fails. -/
theorem conflicting_route : normalCheck conflictingSource .nil = true ∧
    checkCapture [effectE] (.cleanup [effectE] (.request effectE 0)
      (.handler effectE disposeTable disposeDependencies
        (.handler effectE resumeTable resumeDependencies (.handler effectF resumeTable resumeDependencies .nil))))
      effectE 0 = false := ⟨rfl, rfl⟩

/-- Exporting an effect in the route judgment does not itself supply an
operation implementation. The normal source capability check is independent. -/
theorem missing_supply :
    checkCapture [effectF] (.cleanup [effectF] (.request effectF 0)
      (.handler effectE disposeTable disposeDependencies .nil)) effectE 0 = true ∧
    normalCheck (Interfaces.cleanup (needs := [effectF]) .nil [(effectF, 0)] .request .nil) .nil = false := ⟨by decide, rfl⟩

def outsideOwner : Forest (Hints.live (owner := 37) .nil
    (.handler (effect := effectE) (table := resumeTable) (families := resumeDependencies) [] .nil)) :=
  .live .nil (.handler .nil)
def invokingBefore := Forest.plain (.invoke (key := ⟨37, .resume⟩)) outsideOwner
def invokingAfter := Forest.plain (.invoke (key := ⟨37, .resume⟩))
  (.handler (effect := effectE) (table := disposeTable) (families := disposeDependencies) (required := []) outsideOwner)
def invokingSaved := Forest.plain (.invoke (key := ⟨37, .resume⟩))
  (.handler (effect := effectE) (table := disposeTable) (families := disposeDependencies) (required := []) .nil)

theorem invoking_intercept : Intercept effectE 0 ⟨true, some [], none⟩
    (some SourceDependencyCapture.Examples.disposeFamily, none)
    disposeTable disposeDependencies [] invokingBefore invokingAfter invokingSaved outsideOwner := .plain (.hit rfl rfl)

def invokingSource : Interfaces invokingBefore := .plain (.live (.handler .nil) .nil (.handler .nil))

/-- Callback metadata permits arbitrary discarded plain code. The separate
owner bound detects that this plain frame depends on the waiting owner 37. -/
theorem outside_owner_bound_rejected : normalCheck invokingSource .nil = true ∧
    ¬ PendingWithin [] (owners (.plain (.invoke ⟨37, .resume⟩) (.handler effectE disposeTable disposeDependencies .nil)))
      (.plain (.invoke ⟨37, .resume⟩) (.handler effectE disposeTable disposeDependencies .nil)) := by
  refine ⟨rfl, ?_⟩
  intro bounded
  cases bounded with
  | plain dependency rest => cases dependency with | invoke included => cases included

section
variable [declarations : SourceScheduledCapabilityAnnotations.DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]

/-- No different choice of target annotation can hide the owner-bound failure. -/
theorem outside_owner_annotation_rejected (laws : DeclarationLaws declarations admission certification [])
    (annotation : Code world (.request (effect := effectE) (operation := 0)) invokingAfter) :
    ¬ annotation.Valid [] actions phases := by
  intro ready
  have bound := SourceDependencySchemes.checked_request_owners
    ((annotation.compile_with laws ready).erase_with laws.projected).erase invoking_intercept.cut.erase.lookup rfl
  cases bound with
  | plain dependency rest => cases dependency with | invoke included => cases included

end
end Ash.OneShot.SourceScheduledInterceptAdmission.Examples

#print axioms Ash.OneShot.SourceScheduledInterceptAdmission.Examples.source_declared
#print axioms Ash.OneShot.SourceScheduledInterceptAdmission.Examples.source_covered
#print axioms Ash.OneShot.SourceScheduledInterceptAdmission.Examples.original_normal
#print axioms Ash.OneShot.SourceScheduledInterceptAdmission.Examples.intercepted
#print axioms Ash.OneShot.SourceScheduledInterceptAdmission.Examples.old_request_resumptive
#print axioms Ash.OneShot.SourceScheduledInterceptAdmission.Examples.new_disposer
#print axioms Ash.OneShot.SourceScheduledInterceptAdmission.Examples.fresh_adaptation
#print axioms Ash.OneShot.SourceScheduledInterceptAdmission.Examples.control_capability_changed
#print axioms Ash.OneShot.SourceScheduledInterceptAdmission.Examples.conflicting_route
#print axioms Ash.OneShot.SourceScheduledInterceptAdmission.Examples.missing_supply
#print axioms Ash.OneShot.SourceScheduledInterceptAdmission.Examples.invoking_intercept
#print axioms Ash.OneShot.SourceScheduledInterceptAdmission.Examples.outside_owner_bound_rejected
#print axioms Ash.OneShot.SourceScheduledInterceptAdmission.Examples.outside_owner_annotation_rejected
