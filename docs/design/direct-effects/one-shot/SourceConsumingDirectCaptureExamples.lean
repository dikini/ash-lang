import SourceConsumingDirectCapture
import SourceConsumingReinterpretationBounds

/-! A general captured branch invokes an owner in the waiting tail. The direct
generator derives the fresh outer capture from the original source checks;
the external owner's permission and spent state remain independently checked. -/
namespace Ash.OneShot.SourceConsumingClauseAnnotations.DirectCaptureExamples
open SourceContextualHints (Hints)
open SourceDependencyCapture (Scope)
open SourceRetainedPlans (Forest)
open SourceScheduledCapabilityAnnotations (Code Retained)
open SourceScheduledClauseHandlers.Examples (innerPlans innerFamilies innerClauses resumeBodies)
open SourceDependencyCapture.Examples (effectE resumeTable)
open SourceConsumingClauseAnnotations.ReinterpretationExamples (bodies declarations emptyBounds empty_declaration_admitted)

def waitingHints : Hints (.live 37 .nil .nil) := .live .nil .nil
def waiting : Forest waitingHints := .live .nil .nil
def delimiterHints : Hints (.handler effectE resumeTable innerFamilies .nil) := .handler [] .nil
def delimiter : Forest delimiterHints := .handler .nil
def branch := SourceDeclarationPlans.Plan.choice
  (.invoke (key := ⟨37, .resume⟩)) (.invoke (key := ⟨37, .resume⟩))
def savedHints : Hints (.plain (.choice (.invoke ⟨37, .resume⟩) (.invoke ⟨37, .resume⟩))
    (.handler effectE resumeTable innerFamilies .nil)) := .plain delimiterHints
def saved : Forest savedHints := .plain branch delimiter
def whole := saved.append waiting

def actions : Syntax.UsageTickets := fun owner => if owner = 37 then some ⟨true, false⟩ else none
def phases : OwnerPhaseTransitions.Phases := OwnerPhaseTransitions.available [37]

def outsideCall : Code [] (.invoke (key := ⟨37, .resume⟩)) (delimiter.append waiting) :=
  .resume (.handler .hit) (.operations .nil)
    (.operations (.handler .nil .nil)) (.operations .nil)

def source : Retained [] whole .nil :=
  .plain (.choice outsideCall outsideCall)
    (.handler (.live (.operations .nil) (.operations .nil)))

theorem source_valid : source.Valid [] actions phases := by
  simp [source, outsideCall, Retained.Valid, Code.Valid, SourceScheduledRetainedInterfaces.Interfaces.check,
    actions, phases, OwnerPhaseTransitions.available, SourceContextualHints.checkRequirements]

theorem owner_is_outside : SourceDependencyOwners.owners
    (.plain (.choice (.invoke ⟨37, .resume⟩) (.invoke ⟨37, .resume⟩))
      (.handler effectE resumeTable innerFamilies .nil)) = [] ∧
    SourceDependencyOwners.owners (.live 37 .nil .nil) = [37] := by decide

/-- An operation-only interface cannot account for either branch's owner use. -/
theorem operation_interface_rejected : ¬ Nonempty (SourceScheduledRetainedInterfaces.Interfaces [] saved) := by
  have impossible : ∀ {dependencies} {checking : SourcePlanSignatures.Signature dependencies} {required},
      SourceRequestFootprints.Footprint checking required →
      dependencies = .choice (.invoke ⟨37, .resume⟩) (.invoke ⟨37, .resume⟩) → False := by
    intro dependencies checking required footprint same
    induction footprint with
    | choice first second => cases same; exact first.no_invocation rfl
    | weaken body included ih => exact ih same
    | _ => cases same
  intro ⟨interface⟩
  cases interface with
  | plain rest required footprint declared tail => exact impossible footprint rfl

theorem direct_declarations : declarations.Direct :=
  ⟨fun _ => .sequence .resume, fun _ => .sequence .resume, trivial⟩

def request : Code [] (.request (effect := effectE) (operation := 0)) whole :=
  .operations [(effectE, 0)] .request .request

theorem request_valid : request.Valid [] actions phases := rfl

theorem generated_capture :
    ∃ certificate : SourceScheduledCaptureAnnotations.Capture [] 19 effectE 0 ⟨false, some [], some []⟩
      (some SourceScheduledClauseHandlers.Examples.resumeFamily, some SourceScheduledClauseHandlers.Examples.resumeFamily)
      innerPlans 2 3 (.resume 3 .unit) whole, certificate.Valid [] actions phases := by
  exact empty_declaration_admitted.capture_direct
    (SourceScheduledCapabilityAnnotations.recipeLaws []) (fun evidence => evidence) direct_declarations
    (.plain (.hit rfl rfl)) .ordinary source source_valid request request_valid
    (by intro impossible; cases impossible) rfl rfl (by decide)

def resourcePlan (owner : Nat) := SourceDeclarationPlans.Plan.resource (fun identity =>
  .sequence (.sequence .pure (.request (effect := .cell identity) (operation := 0)))
    (resumeBodies owner))

def resourceBody (owner : Nat) : Body [] owner (resourcePlan owner) :=
  .resource (fun identity _ => .sequence [(.cell identity, 0)]
    (.sequence .pure .request) (.sequence .pure .request) (.sequence [] .pure .pure .resume))

theorem resource_admitted : Admitted ⟨true, false⟩ [] [] (resourceBody owner) [] := by
  apply Admitted.resource
  intro identity fresh
  apply Admitted.weaken (.sequence (.sequence (.resume rfl)))
  intro request member
  simp only [List.append_nil] at member ⊢
  exact List.mem_cons.mpr (Or.inl (List.mem_singleton.mp member))

/-- A fresh cell and its read operation may surround consumption even when
the resumed source branches and calls an outside owner. The cell is inserted
through those calls by the existing provider proof. -/
theorem resource_capture_body :
    ∃ annotation : Code [] (resourcePlan 19) (.live (owner := 19) saved waiting),
      annotation.Valid [] (actions.insert 19 ⟨true, false⟩) (OwnerPhaseTransitions.introduce phases 19) := by
  have cut : SourceScheduledNeutral.Cut effectE 0 ⟨false, some [], some []⟩
      (some SourceScheduledClauseHandlers.Examples.resumeFamily, some SourceScheduledClauseHandlers.Examples.resumeFamily)
      whole saved waiting := .plain (.hit rfl rfl)
  obtain ⟨⟨inside, insideReady⟩, ⟨after, afterReady⟩⟩ :=
    SourceScheduledCapabilityAnnotations.retained_at_cut cut source source_valid
  have direct : (resourceBody 19).Direct := .resource (fun _ _ => .sequence (.sequence .resume))
  exact direct.capture_body (SourceScheduledCapabilityAnnotations.recipeLaws []) (fun evidence => evidence)
    resource_admitted inside after (fun _ => insideReady)
    (by intro impossible; cases impossible) (by intro impossible; cases impossible)
    afterReady rfl rfl (by decide)

def cleanupResourcePlan (owner : Nat) :=
  SourceDeclarationPlans.Plan.cleanup (needs := []) .pure (resourcePlan owner)

def cleanupResourceBody (owner : Nat) : Body [] owner (cleanupResourcePlan owner) :=
  .cleanup [] .pure .pure (resourceBody owner)

theorem cleanup_resource_admitted : Admitted ⟨true, false⟩ [] [] (cleanupResourceBody owner) [] :=
  .cleanup resource_admitted

/-- Pure cleanup and a fresh provider compose around a general saved branch
that invokes an outside continuation. Only original source checks are supplied. -/
theorem cleanup_resource_capture_body :
    ∃ annotation : Code [] (cleanupResourcePlan 19) (.live (owner := 19) saved waiting),
      annotation.Valid [] (actions.insert 19 ⟨true, false⟩) (OwnerPhaseTransitions.introduce phases 19) := by
  have cut : SourceScheduledNeutral.Cut effectE 0 ⟨false, some [], some []⟩
      (some SourceScheduledClauseHandlers.Examples.resumeFamily, some SourceScheduledClauseHandlers.Examples.resumeFamily)
      whole saved waiting := .plain (.hit rfl rfl)
  obtain ⟨⟨inside, insideReady⟩, ⟨after, afterReady⟩⟩ :=
    SourceScheduledCapabilityAnnotations.retained_at_cut cut source source_valid
  have direct : (cleanupResourceBody 19).Direct := .cleanup (.resource (fun _ _ => .sequence (.sequence .resume)))
  exact direct.capture_body (SourceScheduledCapabilityAnnotations.recipeLaws []) (fun evidence => evidence)
    cleanup_resource_admitted inside after (fun _ => insideReady)
    (by intro impossible; cases impossible) (by intro impossible; cases impossible)
    afterReady rfl rfl (by decide)

def cleanupDisposePlan (owner : Nat) := SourceDeclarationPlans.Plan.cleanup (needs := []) .pure
  (.invoke (key := ⟨owner, .dispose⟩))

def cleanupDisposeBody (owner : Nat) : Body [] owner (cleanupDisposePlan owner) :=
  .cleanup [] .pure .pure .dispose

/-- The same cleanup source constructor supports disposal. The general saved
branch is abandoned; its closing annotation is derived from its actual shape. -/
theorem cleanup_dispose_capture_body :
    ∃ annotation : Code [] (cleanupDisposePlan 19) (.live (owner := 19) saved waiting),
      annotation.Valid [] (actions.insert 19 ⟨false, true⟩) (OwnerPhaseTransitions.introduce phases 19) := by
  have cut : SourceScheduledNeutral.Cut effectE 0 ⟨false, some [], some []⟩
      (some SourceScheduledClauseHandlers.Examples.resumeFamily, some SourceScheduledClauseHandlers.Examples.resumeFamily)
      whole saved waiting := .plain (.hit rfl rfl)
  obtain ⟨⟨inside, insideReady⟩, ⟨after, afterReady⟩⟩ :=
    SourceScheduledCapabilityAnnotations.retained_at_cut cut source source_valid
  have admitted : Admitted ⟨false, true⟩ [] [] (cleanupDisposeBody 19) [] := .cleanup (.dispose rfl)
  have direct : (cleanupDisposeBody 19).Direct := .cleanup .dispose
  apply direct.capture_body (SourceScheduledCapabilityAnnotations.recipeLaws []) (fun evidence => evidence)
    admitted inside after (fun _ => insideReady) _ _ afterReady rfl rfl (by decide)
  · intro _
    exact ⟨.operations .nil, rfl⟩
  · intro _
    exact ⟨rfl, rfl⟩

/-- Registering cleanup does not confer disposal permission on a resume-only
continuation. The original admission-to-bound-check theorem supplies the denial. -/
theorem cleanup_does_not_grant_disposal :
    ¬ Admitted ⟨true, false⟩ [] [] (cleanupDisposeBody 19) [] := by
  intro admitted
  have checked := admitted.at_capture (captured := .nil) (waiting := .nil)
    (actions := fun _ => some ⟨true, false⟩) (phases := fun _ => .available) rfl rfl rfl
  exact Bool.noConfusion checked.1.1

/-- Introducing another owner does not make an already consumed outside
owner available to either saved branch. -/
theorem spent_outside_owner_rejected :
    ¬ source.Valid [] actions (OwnerPhaseTransitions.spend phases 37) := by
  intro checked
  have available := checked.1.1.2.1
  simp only [OwnerPhaseTransitions.spend_self] at available
  cases available

end Ash.OneShot.SourceConsumingClauseAnnotations.DirectCaptureExamples

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.DirectCaptureExamples.source_valid
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.DirectCaptureExamples.owner_is_outside
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.DirectCaptureExamples.operation_interface_rejected
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.DirectCaptureExamples.direct_declarations
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.DirectCaptureExamples.request_valid
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.DirectCaptureExamples.generated_capture
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.DirectCaptureExamples.resource_admitted
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.DirectCaptureExamples.resource_capture_body
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.DirectCaptureExamples.cleanup_resource_admitted
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.DirectCaptureExamples.cleanup_resource_capture_body
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.DirectCaptureExamples.cleanup_dispose_capture_body
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.DirectCaptureExamples.cleanup_does_not_grant_disposal
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.DirectCaptureExamples.spent_outside_owner_rejected
