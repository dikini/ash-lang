import SourceConsumingContextualCapture
import SourceScheduledCleanupReceiverPlans

/-! Structural cleanup admission over a saved outside-owner invocation.
The derivation supplies primitive registration checks directly and remains
valid when only capability-annotation witnesses at the same receiver change. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission.StructuralExamples
open SourceScheduledCapabilityAnnotations (Code Retained recipeLaws)
open SourceScheduledSourceRechecking (Expression ReceiverChange)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open SourceContextualHints (Hints)
open SourceConsumingClauseAnnotations (Body Admitted)
open OwnerPhaseTransitions (spend)

def actions : Syntax.UsageTickets := fun owner =>
  if owner = 19 ∨ owner = 37 then some ⟨true, false⟩ else none
def phases := OwnerPhaseTransitions.available [19, 37]
def waiting : Forest (Hints.live (owner := 37) .nil (.cell (identity := 4) .nil)) := .live .nil (.cell .nil)
def saved := Forest.plain (.invoke (key := ⟨37, .resume⟩)) .nil
def whole := Forest.live (owner := 19) saved waiting

def resumedCode : Code [4] (.invoke (key := ⟨37, .resume⟩)) (.spent (owner := 19) waiting) :=
  .resume (.spent .hit) (.operations .nil) (.operations (.spent .nil)) (.cell (.operations .nil))

def context : Context [4] 19 [] actions phases whole .nil saved waiting where
  cut := .hit
  before := .nil
  resumption := fun _ => ⟨.plain resumedCode (.operations .nil), ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩⟩
  closing := fun impossible => False.elim (Bool.noConfusion impossible)
  disposal := fun impossible => False.elim (Bool.noConfusion impossible)
  after := .live (.operations .nil) (.cell (.operations .nil))
  tailReady := ⟨rfl, rfl⟩

def callback := Plan.request (effect := .cell 4) (operation := 0)
def clause := Plan.cleanup (needs := [.cell 4]) callback (.invoke (key := ⟨19, .resume⟩))
def body : Body [4] 19 clause := .cleanup [(.cell 4, 0)] .request .request .resume

theorem resumption_rechecked (permission) : ReceiverChange [] actions (spend phases 19)
    (context.resumption permission).val
    (.cleanup (needs := [.cell 4]) callback (.spent (owner := 19) waiting)) := by
  apply ReceiverChange.plain
  · exact Expression.resume (.cleanup (.spent .hit)) (.operations .nil rfl)
      (.installCleanup [(.cell 4, 0)] .request .request rfl) .same
  · exact .operations .nil rfl

theorem admitted : At (recipeLaws []) (fun evidence => evidence) body context := by
  refine At.cleanupSource ?_ resumption_rechecked ?_ .resume
  · intro request member
    exact List.mem_singleton.mpr (congrArg Prod.fst (List.mem_singleton.mp member))
  · intro impossible
    exact False.elim (Bool.noConfusion impossible)

theorem source_admitted : Admitted ⟨true, false⟩ [] [] body [(.cell 4, 0)] := .cleanup (.resume rfl)

theorem checked : body.BoundCheck [] [] actions phases
    (.live 19 (.plain (.invoke ⟨37, .resume⟩) .nil) (.live 37 .nil (.cell 4 .nil)))
    (.live 37 .nil (.cell 4 .nil)) .nil := source_admitted.at_capture rfl rfl rfl

theorem scheduled : SourceScheduledChecks.Local [] actions phases [4] clause whole := admitted.scheduled checked

/-- An explicit checking plan keeps the only new obligation at the actual
callback receiver. Existing owner permissions and phases come from the source. -/
def resumedResult : SourceScheduledCleanupGeneration.CodeResult resumedCode
    (.cleanup (needs := [.cell 4]) callback (.spent (owner := 19) waiting)) :=
  ⟨.resume (.cleanup (.spent .hit)) (.operations .nil)
    (.cleanup (.operations [(.cell 4, 0)] .request .request) (.operations (.spent .nil)))
    (.cell (.operations .nil)),
    .operations (.running (.spent 19 (.spent 37 (.cell 4 .nil)))) [(.cell 4, 0)],
    (fun _ _ _ ready checked => ⟨ready.1, ready.2.1, rfl, ⟨checked, rfl⟩, ready.2.2.2.2⟩),
    fun _ _ _ _ checked => .resume (.cleanup (.spent .hit)) (.operations .nil rfl)
      (.installCleanup [(.cell 4, 0)] .request .request checked) .same⟩

def resumptionPlan (permission) : SourceScheduledCleanupGeneration.ReceiverPlan
    (context.resumption permission).val
    (.cleanup (needs := [.cell 4]) callback (.spent (owner := 19) waiting)) :=
  .plain resumedResult (.operations rfl)

theorem planned_checks (permission) : (resumptionPlan permission).checks.Holds [] := ⟨rfl, True.intro⟩

/-- Derive contextual admission from the plan and its primitive check. No
ReceiverChange witness is provided to this admission theorem. -/
theorem planned_admitted : At (recipeLaws []) (fun evidence => evidence) body context := by
  refine At.cleanup_planned ?_ resumptionPlan planned_checks ?_ ?_ .resume
  · intro request member
    exact List.mem_singleton.mpr (congrArg Prod.fst (List.mem_singleton.mp member))
  · intro impossible
    exact False.elim (Bool.noConfusion impossible)
  · intro impossible
    exact False.elim (Bool.noConfusion impossible)

theorem planned_scheduled : SourceScheduledChecks.Local [] actions phases [4] clause whole :=
  planned_admitted.scheduled checked

/-- The compiler of the derived receiver judgment retains exact original
metadata; the standalone generator's target annotation need not be chosen. -/
theorem planned_retention (permission) :
    ∃ annotation : Retained [4] saved
      (.cleanup (needs := [.cell 4]) callback (.spent (owner := 19) waiting)),
      annotation.Valid [] actions (spend phases 19) ∧
      SourceBoundSnapshots.Retained.ofCapability annotation =
        SourceBoundSnapshots.Retained.ofCapability (context.resumption permission).val :=
  ((resumptionPlan permission).rechecking (context.resumption permission).property (planned_checks permission)).compile_retaining
    (recipeLaws []) (fun evidence => evidence) (context.resumption permission).property

/-- This example has no explicit bound-bearing plans in its saved or waiting
forest, so every annotation has the same metadata. This is a property of this
source, not a general consequence of sharing a physical receiver. -/
private theorem saved_metadata {outside : Forest outsideHints} (source : Retained [4] saved outside) :
    SourceBoundSnapshots.Retained.ofCapability source = SourceBoundSnapshots.Retained.absent saved := by
  cases source with
  | operations => rfl
  | plain code tail =>
      rw [SourceScheduledSourceRechecking.retained_nil_eq tail]
      cases code <;> rfl

private theorem waiting_metadata {outside : Forest outsideHints} (source : Retained [4] waiting outside) :
    SourceBoundSnapshots.Retained.ofCapability source = SourceBoundSnapshots.Retained.absent waiting := by
  cases source with
  | operations => rfl
  | live inside tail =>
      rw [SourceScheduledSourceRechecking.retained_nil_eq inside]
      cases tail with
      | operations => rfl
      | cell rest => rw [SourceScheduledSourceRechecking.retained_nil_eq rest]; rfl

theorem every_annotation_bounds (other : Context [4] 19 [] actions phases whole .nil saved waiting) :
    context.BoundsAgree other := by
  refine ⟨fun permission => saved_metadata _, ?_, waiting_metadata _⟩
  intro impossible
  exact False.elim (Bool.noConfusion impossible)

theorem at_every_annotation (other : Context [4] 19 [] actions phases whole .nil saved waiting) :
    At (recipeLaws []) (fun evidence => evidence) body other :=
  .sameReceiver (Context.before_nil other).symm (every_annotation_bounds other) admitted

theorem every_annotation_scheduled (other : Context [4] 19 [] actions phases whole .nil saved waiting) :
    SourceScheduledChecks.Local [] actions phases [4] clause whole := by
  apply (at_every_annotation other).scheduled (resumeRequired := []) (closeRequired := [])
  simpa only [Context.before_nil] using checked

/-- The structural rule cannot grant the already-consumed outside owner. -/
theorem spent_outside_owner_rejected : ¬ resumedCode.Valid [] actions (spend (spend phases 19) 37) := by
  intro ready
  have available := ready.2.1
  simp [spend] at available

/-- Conditional soundness alone cannot guarantee a usable chosen check tree:
an always-false extra condition preserves the same annotation and soundness.
This does not claim that the existing classical choice actually chooses it. -/
theorem result_type_allows_rejection [SourceScheduledCapabilityAnnotations.DeclarationPolicy]
    {before : Forest beforeHints} {outside : Forest outsideHints}
    {after : Forest afterHints} {next : Forest nextHints} {source : Retained world before outside}
    (result : SourceScheduledCleanupGeneration.RetainedResult source after next) :
    ∃ other : SourceScheduledCleanupGeneration.RetainedResult source after next,
      other.annotation = result.annotation ∧ ¬ other.checks.Holds outward := by
  refine ⟨⟨result.annotation, .both result.checks (.operations .nil [(.user 9000 [], 0)]),
    (fun outward actions phases ready checked => result.sound outward actions phases ready checked.1),
    fun outward actions phases ready checked => result.rechecking outward actions phases ready checked.1⟩, rfl, ?_⟩
  intro checked
  have impossible : false = true := checked.2
  cases impossible

end Ash.OneShot.SourceConsumingCleanupAdmission.StructuralExamples

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.StructuralExamples.resumption_rechecked
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.StructuralExamples.admitted
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.StructuralExamples.source_admitted
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.StructuralExamples.checked
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.StructuralExamples.scheduled
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.StructuralExamples.at_every_annotation
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.StructuralExamples.every_annotation_scheduled
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.StructuralExamples.spent_outside_owner_rejected

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.StructuralExamples.result_type_allows_rejection

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.StructuralExamples.every_annotation_bounds

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.StructuralExamples.planned_checks
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.StructuralExamples.planned_admitted
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.StructuralExamples.planned_scheduled
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.StructuralExamples.planned_retention
