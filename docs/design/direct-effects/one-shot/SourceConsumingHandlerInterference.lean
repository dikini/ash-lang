import SourceConsumingReinterpretationBounds
import SourceHandlerClosingInsertion

/-! A necessary boundary condition for extending consuming clauses to arbitrary
captured source. Operation availability and old source validity do not imply
closing-route preservation when a caller installs a handler. The existing exact
interference theorem supplies the missing finite structural condition. -/
namespace Ash.OneShot.SourceConsumingHandlerInterference
open SourceContextualHints (Hints)
open SourceDependencyCapture (Scope)
open SourceRetainedPlans (Forest)
open SourceScheduledCapabilityAnnotations (Code Retained DeclarationLaws)

/-- Any validated annotation of the intercepted boundary must satisfy the
existing finite shield check when the selected operation may dispose. This is
a necessity theorem, not a successful-target premise for source admission. -/
theorem selected_disposal_requires_shield
    [declarations : SourceScheduledCapabilityAnnotations.DeclarationPolicy]
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    (laws : DeclarationLaws declarations admission certification outward)
    {front tail : Scope}
    {hints : Hints scope} {forest : Forest hints}
    (annotation : Code world (.request (effect := requested) (operation := operation)) forest)
    (checked : annotation.Valid outward actions phases)
    (found : SourceDependencyCapture.select requested operation scope =
      some (.handler (front.append (.handler installed table families tail)) outside contract modes))
    (disposes : contract.dispose = true) :
    SourceHandlerInterference.check installed front.shape [] = true := by
  have scheduled := annotation.compile_with laws checked
  cases scheduled with
  | request guard closing =>
      obtain ⟨_, route, _⟩ := SourceDependencyCapture.disposing_capture
        (SourceDependencySchemes.checked_request guard) found disposes
      exact SourceHandlerInterference.check_iff.mpr
        ((SourceHandlerClosingInsertion.inserted_closing_iff front tail).mp route).2

/-- The missing closing condition has an exact finite interface. Existing
operation bounds need not be counted or changed into continuation permissions;
this list records callback routes exposed at the actual insertion boundary. -/
theorem closing_iff_boundary_exclusion (front tail : Scope)
    (checked : SourceDependencyCapture.checkClosing outward (front.append tail).shape original surviving = true) :
    SourceDependencyCapture.checkClosing outward
      (front.append (.handler installed table families tail)).shape original surviving = true ↔
      installed ∉ SourceHandlerInterference.exposed front.shape := by
  rw [SourceHandlerClosingInsertion.check_closing_inserted, checked, Bool.true_and,
    SourceHandlerInterference.check_summary]
  simp only [SourceRecursiveRoutes.scopeProviders, List.not_mem_nil, imp_false]

/-- A declaration can carry an over-approximation of the finite boundary
summary. Authenticating that bound and excluding the installed effect suffices
for this closing obligation; operation selection and scheduling stay separate. -/
theorem closing_from_boundary_bound (front tail : Scope)
    (checked : SourceDependencyCapture.checkClosing outward (front.append tail).shape original surviving = true)
    (covered : SourceHandlerInterference.exposed front.shape ⊆ bound)
    (separate : installed ∉ bound) :
    SourceDependencyCapture.checkClosing outward
      (front.append (.handler installed table families tail)).shape original surviving = true :=
  (closing_iff_boundary_exclusion front tail checked).mpr (fun member => separate (covered member))

/-- For a request that bypasses the new handler, authenticate its exposed
callback summary against the declared boundary list. The existing exact guard
transport then constructs the target capture guard. No target schedule is an
input; changes to requests intercepted by the new handler are a separate case. -/
theorem bypassed_guard_from_boundary_bound {front outside captured tail : Scope}
    (passed : SourceHandlerRequirements.reaches requested front = true)
    (different : requested ≠ installed)
    (found : SourceDependencyCapture.select requested operation outside =
      some (.handler captured tail contract modes))
    (checked : SourceDependencyCapture.CaptureGuard outward (front.append outside) requested operation)
    (covered : contract.dispose = true → SourceHandlerInterference.exposed front.shape ⊆ bound)
    (separate : installed ∉ bound) :
    SourceDependencyCapture.CaptureGuard outward
      (front.append (.handler installed table families outside)) requested operation := by
  apply SourceHandlerClosingInsertion.bypassed_guard_transport passed different found checked
  intro disposes
  apply (SourceHandlerInterference.check_summary front.shape).mpr
  intro member
  exact False.elim (separate (covered disposes member))

namespace Examples
open SourceDependencyCapture.Examples (resumeTable disposeTable disposeDependencies)
open SourceScheduledClauseHandlers.Examples (innerPlans innerFamilies inner_declarations)
open SourceConsumingClauseAnnotations
open SourceConsumingClauseAnnotations.ReinterpretationExamples (emptyBounds)

def callbackEffect : Instance := .cell 4
def outerEffect : Instance := .user 500 []
def disposingEffect : Instance := .user 501 []

def waitingHints : Hints (.cell 4 (.handler disposingEffect disposeTable disposeDependencies .nil)) :=
  .cell (.handler [] .nil)
def waiting : Forest waitingHints := .cell (.handler .nil)
def delimiterHints : Hints (.handler outerEffect resumeTable innerFamilies .nil) := .handler [] .nil
def delimiter : Forest delimiterHints := .handler .nil
def armedHints : Hints (.cleanup [callbackEffect] (.request callbackEffect 0)
    (.handler outerEffect resumeTable innerFamilies .nil)) := .cleanup delimiterHints
def armed : Forest armedHints := .cleanup .request delimiter
def savedHints : Hints (.plain (.request disposingEffect 0)
    (.cleanup [callbackEffect] (.request callbackEffect 0)
      (.handler outerEffect resumeTable innerFamilies .nil))) := .plain armedHints
def saved : Forest savedHints := .plain .request armed

def oldRequest : Code [4] (.request (effect := disposingEffect) (operation := 0)) (armed.append waiting) :=
  .selected (.cleanup (.handler (by decide) (.cell (by decide) (.hit rfl rfl))))
    (fun _ => .cleanup (.handler (.cell (.handler .nil))))
    (fun _ => .cleanup (.operations [(callbackEffect, 0)] .request .request) (.cell (.operations .nil)))

def source : Retained [4] saved waiting :=
  .plain oldRequest (.cleanup (.operations [(callbackEffect, 0)] .request .request)
    (.handler (.operations .nil)))

def actions : Syntax.UsageTickets := fun owner => if owner = 19 then some ⟨true, false⟩ else none
def phases : OwnerPhaseTransitions.Phases := OwnerPhaseTransitions.available [19]

theorem ticket_ready : actions 19 = some ⟨true, false⟩ ∧ phases 19 = .available := ⟨rfl, rfl⟩

/-- Before caller insertion the callback reaches the cell, which survives
the disposing capture. The actual effectful callback is retained and checked. -/
theorem source_valid : source.Valid [] actions phases := by
  exact ⟨⟨rfl, fun _ => ⟨rfl, rfl⟩⟩, rfl, rfl, rfl⟩

def operationInterface : SourceScheduledRetainedInterfaces.Interfaces [4] saved :=
  .plain armed [(disposingEffect, 0)] .request .request
    (.cleanup delimiter [(callbackEffect, 0)] .request .request (.handler .nil .nil))

/-- The earlier operation-interface route already rejects this input: its
external G operation is disposing, and the declared F-only bound omits G.
The example therefore does not contradict that generator's soundness. -/
theorem operation_route_rejects :
    operationInterface.check (.cell 4 (.handler disposingEffect disposeTable disposeDependencies .nil)) = false ∧
      ¬ operationInterface.exposed ⊆ [(callbackEffect, 0)] := by decide

def nextReceiver : Forest
    (Hints.handler (effect := callbackEffect) (table := resumeTable) (families := innerFamilies) []
      (.spent (owner := 19) waitingHints)) := .handler (.spent waiting)

/-- Both receivers supply the callback operation. Its availability does not
say whether the same provider survives disposal of the intervening frames. -/
theorem callback_available :
    SourceContextualHints.checkRequirements (.cell 4 (.handler disposingEffect disposeTable disposeDependencies .nil))
      [(callbackEffect, 0)] = true ∧
    SourceContextualHints.checkRequirements
      (.handler callbackEffect resumeTable innerFamilies (.spent 19 (.cell 4
        (.handler disposingEffect disposeTable disposeDependencies .nil)))) [(callbackEffect, 0)] = true := ⟨rfl, rfl⟩

def clausePlan := SourceDeclarationPlans.Plan.handler
  (effect := callbackEffect) (table := resumeTable) [] innerPlans
  (.sequence .pure (.invoke (key := ⟨19, .resume⟩)))
def clauseBody : Body [4] 19 clausePlan :=
  .handler emptyBounds inner_declarations (.sequence [] .pure .pure .resume)

/-- The old operation-bound admission accepts the caller's own syntax and
the operation it promises to supply. This alone is not capture admission. -/
theorem clause_admitted : Admitted ⟨true, false⟩ [(callbackEffect, 0)] [] clauseBody [] := by
  exact .handler (.sequence (.resume rfl)) rfl rfl

section
variable [declarations : SourceScheduledCapabilityAnnotations.DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]

/-- No replacement annotation can hide the changed callback route. Reuse
the compiler's necessary request guard rather than rejecting one particular
choice of source annotation. -/
theorem restored_source_rejected (laws : DeclarationLaws declarations admission certification [])
    (annotation : Retained world saved nextReceiver) :
    ¬ annotation.Valid [] actions phases := by
  intro checked
  have scheduled := annotation.compile_with laws checked
  cases scheduled with
  | plain request tail => cases request with
    | request guard closing =>
        have admitted := SourceDependencySchemes.checked_request guard
        change false = true at admitted
        cases admitted

/-- The consuming clause itself has no valid target annotation over this
saved source. This quantifies over all annotations, not only a proposed
generator, and uses the existing exact decomposition of resumption. -/
theorem clause_annotation_rejected
    (laws : DeclarationLaws declarations admission certification [])
    (annotation : Code world clausePlan (.live (owner := 19) saved waiting)) :
    ¬ annotation.Valid [] actions phases := by
  intro checked
  have scheduled := annotation.compile_with laws checked
  cases scheduled with
  | handler declarations certified supplied body =>
      cases body with
      | sequence operand invocation =>
          have inside := ((SourceScheduledScopedInvocations.resume_iff
            (SourceScheduledNeutral.OwnerCut.handler SourceScheduledNeutral.OwnerCut.hit)).mp invocation).2.1
          cases inside with
          | plain request tail => cases request with
            | request guard closing =>
                have admitted := SourceDependencySchemes.checked_request guard
                change false = true at admitted
                cases admitted

end

theorem shield_missing : SourceHandlerInterference.check callbackEffect
    (SourceDependencyCapture.Scope.shape (.cleanup [callbackEffect] (.request callbackEffect 0)
      (.handler outerEffect resumeTable innerFamilies .nil))) [] = false := rfl

theorem boundary_lists_callback : SourceHandlerInterference.exposed
    (SourceDependencyCapture.Scope.shape (.cleanup [callbackEffect] (.request callbackEffect 0)
      (.handler outerEffect resumeTable innerFamilies .nil))) = [callbackEffect] := rfl

/-- A builtin before the insertion shields an overlapping callback effect.
The boundary check allows this case; it does not ban all effect overlap. -/
theorem builtin_shields_overlap :
    SourceHandlerInterference.exposed (.cleanup [callbackEffect] (.cell 4 .nil)) = [] ∧
      SourceHandlerInterference.check callbackEffect (.cleanup [callbackEffect] (.cell 4 .nil)) [] = true := ⟨rfl, rfl⟩

end Examples
end Ash.OneShot.SourceConsumingHandlerInterference

#print axioms Ash.OneShot.SourceConsumingHandlerInterference.selected_disposal_requires_shield
#print axioms Ash.OneShot.SourceConsumingHandlerInterference.closing_iff_boundary_exclusion
#print axioms Ash.OneShot.SourceConsumingHandlerInterference.closing_from_boundary_bound
#print axioms Ash.OneShot.SourceConsumingHandlerInterference.bypassed_guard_from_boundary_bound
#print axioms Ash.OneShot.SourceConsumingHandlerInterference.Examples.source_valid
#print axioms Ash.OneShot.SourceConsumingHandlerInterference.Examples.ticket_ready
#print axioms Ash.OneShot.SourceConsumingHandlerInterference.Examples.operation_route_rejects
#print axioms Ash.OneShot.SourceConsumingHandlerInterference.Examples.callback_available
#print axioms Ash.OneShot.SourceConsumingHandlerInterference.Examples.clause_admitted
#print axioms Ash.OneShot.SourceConsumingHandlerInterference.Examples.restored_source_rejected
#print axioms Ash.OneShot.SourceConsumingHandlerInterference.Examples.clause_annotation_rejected
#print axioms Ash.OneShot.SourceConsumingHandlerInterference.Examples.shield_missing
#print axioms Ash.OneShot.SourceConsumingHandlerInterference.Examples.boundary_lists_callback
#print axioms Ash.OneShot.SourceConsumingHandlerInterference.Examples.builtin_shields_overlap
