import SourceScheduledPrefixRecords
import SourceScheduledCallerDecomposition
import SourceScheduledSurvivingRequirements
import SourceScheduledRetainedRecompositionExamples
import SourceScheduledSourceRecheckingExamples

/-! Partial caller closing with a dormant callback, a nonempty saved body,
and a retained caller suffix. Discarded code uses a handler that closing erases;
surviving source is rechecked from its original annotations. -/
namespace Ash.OneShot.SourceScheduledSourceRechecking.PrefixClosingExamples
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open SourceScheduledCapabilityAnnotations (Code Retained recipeLaws)
open SourceBoundSnapshots.Retained (ofCapability)
open SourceDependencyCapture.Examples (resumeTable resumeDependencies)

private def effect : Instance := .user 81 []
private def shadow : Instance := .user 82 []
def actions : Syntax.UsageTickets := fun owner => if owner = 37 then some ⟨true, true⟩ else none
def phases := OwnerPhaseTransitions.available [19, 37]
def afterSpend := OwnerPhaseTransitions.spend phases 37

def retainedPlan := RecompositionExamples.plan
def shadowPlan := Plan.request (effect := shadow) (operation := 0)
def requestPlan := Plan.request (effect := effect) (operation := 0)
def dormant := Forest.cleanup (needs := []) retainedPlan .nil
def leading := Forest.running (Forest.plain shadowPlan
  (Forest.handler (effect := shadow) (table := resumeTable) (families := resumeDependencies) (required := [])
    (Forest.live (owner := 19) dormant .nil)))
def front := Forest.plain retainedPlan .nil
def saved := Forest.plain requestPlan .nil
def tail := Forest.handler (effect := effect) (table := resumeTable) (families := resumeDependencies) (required := []) .nil
def whole := front.append (Forest.live (owner := 37) saved tail)
def spentTail := Forest.spent (owner := 37) tail

theorem outsideCut : SourceScheduledNeutral.OwnerCut 37 whole front saved tail := .plain .hit

private def scopeOf {hints : Hints scope} (_forest : Forest hints) : SourceDependencyCapture.Scope := scope

theorem absent : 37 ∉ SourceDependencyOwners.owners (scopeOf leading) := by decide

/-- Both requests were available when the original saved annotation was checked. -/
def insideSource : Retained [] saved ((leading.append front).append spentTail) :=
  .plain (.operations [(effect, 0), (shadow, 0)] (.weaken .request (by simp)) .request) (.operations .nil)

def beforeSource : Retained [] (leading.append front) spentTail :=
  .running (.plain (.operations [(shadow, 0)] .request .request)
    (.handler (.live
      (.cleanup (RecompositionExamples.annotated (.running (front.append spentTail))) (.operations .nil))
      (.plain (RecompositionExamples.annotated spentTail) (.operations .nil)))))

def afterSource : Retained [] tail .nil := .handler (.operations .nil)

def source : Code [] (.invoke (key := ⟨37, .resume⟩)) (leading.append whole) :=
  .resume (outsideCut.prefix_without_owner leading (by decide)) insideSource beforeSource afterSource

theorem original_valid : source.Valid [] actions phases :=
  ⟨rfl, rfl, ⟨rfl, rfl⟩,
    ⟨rfl, rfl, ⟨RecompositionExamples.annotated_valid _, rfl⟩,
      RecompositionExamples.annotated_valid _, rfl⟩, rfl, rfl⟩

/-- Closing removes shadow, so reusing the old saved interface would fail. -/
theorem old_saved_requirements_fail : SourceContextualHints.checkRequirements
    (scopeOf ((leading.forClosing.append (.running front)).append spentTail))
    [(effect, 0), (shadow, 0)] = false := rfl

theorem inside_rechecked : ReceiverChange [] actions afterSpend insideSource
    ((leading.forClosing.append (.running front)).append spentTail) := by
  apply (SourceScheduledRecomposition.predicate_congr
    (SourceDependencyChecks.scope_append_assoc _ _ _)
    (SourcePlannedRecomposition.hints_append_assoc _ _ _)
    (SourceScheduledRecomposition.forest_append_assoc leading.forClosing (.running front) spentTail)
    (fun receiver => ReceiverChange [] actions afterSpend insideSource receiver)).mpr
  exact .request_any_closing leading (front.append spentTail)
    (SourceContextualRequirements.check_capability_iff.mp rfl)

theorem caller_rechecked : PrefixClosing [] actions afterSpend (suffix := front)
    leading beforeSource (.running front) spentTail :=
  .running (.plain (.handler (.live
    (.cleanup (.handler rfl (.operations rfl)) .empty)
    (.protect .same))))

theorem rechecked : Expression [] actions phases source (leading.forClosing.append (.running whole)) :=
  .resume_closing_caller leading outsideCut (by decide) inside_rechecked caller_rechecked

theorem generated : ∃ annotation : Code [] (.invoke (key := ⟨37, .resume⟩))
    (leading.forClosing.append (.running whole)),
    annotation.Valid [] actions phases ∧ SourcePlanBounds.ofCode annotation = SourcePlanBounds.ofCode source :=
  rechecked.compile_retaining (recipeLaws []) (fun evidence => evidence) original_valid

/-- Caller metadata remains admitted through the existing provenance relation. -/
theorem caller_admitted : ∃ annotation : Retained []
    (leading.forClosing.append (.running front)) spentTail,
    annotation.Valid [] actions afterSpend ∧ RetainedBounds beforeSource (ofCapability annotation) ∧
    (ofCapability annotation).Admitted := by
  apply caller_rechecked.compile_admitted (recipeLaws []) (fun evidence => evidence)
  · exact original_valid.2.2.2.1
  · exact .running (.plain (.absent .request) (.handler
      (.live (.cleanup (RecompositionExamples.annotated_bounds _) .nil)
        (.plain (RecompositionExamples.annotated_bounds _) .nil))))

/-- The saved body's current bounds survive its receiver change exactly. -/
theorem saved_metadata : ∃ annotation : Retained [] saved
    ((leading.forClosing.append (.running front)).append spentTail),
    annotation.Valid [] actions afterSpend ∧ ofCapability annotation = ofCapability insideSource :=
  inside_rechecked.compile_retaining (recipeLaws []) (fun evidence => evidence) original_valid.2.2.1

/-- Rechecking does not make a consumed outside continuation available again. -/
theorem consumed_rejected : ¬ source.Valid [] actions (OwnerPhaseTransitions.spend phases 37) := by
  intro ready
  have available := ready.2.1
  simp [OwnerPhaseTransitions.spend] at available

/-- Disposal shares the same nonempty caller transformation and retains a
nonempty closing body with explicit nested-handler metadata. -/
def disposingSaved := Forest.cleanup (needs := []) retainedPlan saved
def disposingWhole := front.append (Forest.live (owner := 37) disposingSaved tail)
theorem disposingCut : SourceScheduledNeutral.OwnerCut 37 disposingWhole front disposingSaved tail := .plain .hit

def closingSource : Retained [] disposingSaved.forClosing
    (.running ((leading.append front).append spentTail)) :=
  .cleanup (RecompositionExamples.annotated (.running (.running ((leading.append front).append spentTail))))
    (.operations .nil)

def disposingSource : Code [] (.invoke (key := ⟨37, .dispose⟩)) (leading.append disposingWhole) :=
  .dispose (disposingCut.prefix_without_owner leading (by decide)) closingSource beforeSource afterSource

theorem disposing_valid : disposingSource.Valid [] actions phases :=
  ⟨rfl, rfl, rfl, rfl, ⟨RecompositionExamples.annotated_valid _, rfl⟩,
    original_valid.2.2.2.1, original_valid.2.2.2.2⟩

theorem closing_rechecked : ReceiverChange [] actions afterSpend closingSource
    (.running ((leading.forClosing.append (.running front)).append spentTail)) :=
  .cleanup (.handler rfl (.operations rfl)) .empty

theorem disposing_rechecked : Expression [] actions phases disposingSource
    (leading.forClosing.append (.running disposingWhole)) :=
  .dispose_closing_caller leading disposingCut (by decide) closing_rechecked caller_rechecked

theorem disposing_generated : ∃ annotation : Code [] (.invoke (key := ⟨37, .dispose⟩))
    (leading.forClosing.append (.running disposingWhole)),
    annotation.Valid [] actions phases ∧
    SourcePlanBounds.ofCode annotation = SourcePlanBounds.ofCode disposingSource :=
  disposing_rechecked.compile_retaining (recipeLaws []) (fun evidence => evidence) disposing_valid

theorem closing_metadata : ∃ annotation : Retained [] disposingSaved.forClosing
    (.running ((leading.forClosing.append (.running front)).append spentTail)),
    annotation.Valid [] actions afterSpend ∧ ofCapability annotation = ofCapability closingSource :=
  closing_rechecked.compile_retaining (recipeLaws []) (fun evidence => evidence) disposing_valid.2.2.2.2.1

/-- If the saved body actually requests the erased handler, narrowing an old
conservative footprint cannot repair it. Original validity alone is insufficient. -/
def lostInside : Retained [] (.plain shadowPlan .nil) ((leading.append front).append spentTail) :=
  .plain (.operations [(shadow, 0)] .request .request) (.operations .nil)

theorem lost_original_valid : lostInside.Valid [] actions afterSpend := ⟨rfl, rfl⟩

theorem lost_no_target (annotation : Retained [] (.plain shadowPlan .nil)
    ((leading.forClosing.append (.running front)).append spentTail)) :
    ¬ annotation.Valid [] actions afterSpend := by
  intro ready
  have checked := annotation.compile_with (recipeLaws []) ready
  cases checked with
  | plain code rest => cases code with
    | request guarded scheduled =>
      have impossible := SourceDependencySchemes.checked_request guarded
      change false = true at impossible
      cases impossible

theorem lost_no_rechecking : ¬ ReceiverChange [] actions afterSpend lostInside
    ((leading.forClosing.append (.running front)).append spentTail) := by
  intro changed
  obtain ⟨annotation, valid, _⟩ := changed.compile_retaining (recipeLaws [])
    (fun evidence => evidence) lost_original_valid
  exact lost_no_target annotation valid

/-- The canonical output keeps the dormant callback and suffix bounds in their
original positions, drops the ordinary request/handler, and inserts protection
at the suffix boundary rather than around the whole caller. -/
def protectedCallerBounds : SourceBoundSnapshots.Retained []
    (leading.forClosing.append (.running front)) :=
  .running (.cleanup (SourcePlanBounds.ofCode (RecompositionExamples.annotated .nil))
    (.running (.running (.plain (SourcePlanBounds.ofCode (RecompositionExamples.annotated .nil)) .nil))))

theorem exact_protected_caller : ∃ annotation : Retained []
    (leading.forClosing.append (.running front)) spentTail,
    annotation.Valid [] actions afterSpend ∧ ofCapability annotation = protectedCallerBounds := by
  obtain ⟨annotation, boundary, valid, origin, kept⟩ := caller_rechecked.compile_retaining
    (recipeLaws []) (fun evidence => evidence) original_valid.2.2.2.1
  cases origin with
  | protect => exact ⟨annotation, valid, kept⟩

/-- Omitting the boundary marker retains the same suffix at the same split;
it does not change which prefix frames close or which code bounds survive. -/
theorem unprotected_caller : PrefixClosing [] actions afterSpend (suffix := front)
    leading beforeSource front spentTail :=
  .running (.plain (.handler (.live
    (.cleanup (.handler rfl (.operations rfl)) .empty)
    (.nil .same))))

def unprotectedCallerBounds : SourceBoundSnapshots.Retained []
    (leading.forClosing.append front) :=
  .running (.cleanup (SourcePlanBounds.ofCode (RecompositionExamples.annotated .nil))
    (.running (.plain (SourcePlanBounds.ofCode (RecompositionExamples.annotated .nil)) .nil)))

theorem exact_unprotected_caller : ∃ annotation : Retained []
    (leading.forClosing.append front) spentTail,
    annotation.Valid [] actions afterSpend ∧ ofCapability annotation = unprotectedCallerBounds := by
  obtain ⟨annotation, boundary, valid, origin, kept⟩ := unprotected_caller.compile_retaining
    (recipeLaws []) (fun evidence => evidence) original_valid.2.2.2.1
  cases origin with
  | same => exact ⟨annotation, valid, kept⟩

/-- Distinct payloads expose loss, duplication or reordering: discarded pending
source is 11, the dormant callback is 22, and the retained pending suffix is 33. -/
abbrev payloadFamily : SourceBoundSnapshots.RecordFamily [] := fun {_ _} _ => Nat

def originalRecords : (ofCapability beforeSource).Records payloadFamily :=
  .running (.plain 11 (.handler (.live (.cleanup 22 .nil) (.plain 33 .nil))))

def prefixRecords : ((ofCapability beforeSource).splitAt leading front).1.Records payloadFamily :=
  .running (.plain 11 (.handler (.live (.cleanup 22 .nil) .nil)))

def suffixRecords : ((ofCapability beforeSource).splitAt leading front).2.Records payloadFamily :=
  .plain 33 .nil

theorem original_record_split : HEq (prefixRecords.append suffixRecords) originalRecords := HEq.rfl

def protectedRecords : protectedCallerBounds.Records payloadFamily :=
  prefixRecords.forClosing.append (.running suffixRecords)

theorem exact_record_payloads : protectedRecords.entries.map (fun entry => entry.payload) = [22, 33] := rfl

/-- Actual source compilation and the canonical metadata identity carry those
same payloads into the generated caller annotation. -/
theorem compiled_record_payloads : ∃ annotation : Retained []
    (leading.forClosing.append (.running front)) spentTail,
    ∃ records : (ofCapability annotation).Records payloadFamily,
    annotation.Valid [] actions afterSpend ∧ records.entries.map (fun entry => entry.payload) = [22, 33] := by
  obtain ⟨annotation, valid, kept⟩ := exact_protected_caller
  refine ⟨annotation, kept.symm ▸ protectedRecords, valid, ?_⟩
  rw [SourceBoundSnapshots.Retained.Records.cast_entries]
  exact exact_record_payloads

end Ash.OneShot.SourceScheduledSourceRechecking.PrefixClosingExamples

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.PrefixClosingExamples.outsideCut
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.PrefixClosingExamples.absent
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.PrefixClosingExamples.original_valid
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.PrefixClosingExamples.old_saved_requirements_fail
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.PrefixClosingExamples.inside_rechecked
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.PrefixClosingExamples.caller_rechecked
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.PrefixClosingExamples.rechecked
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.PrefixClosingExamples.generated
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.PrefixClosingExamples.caller_admitted
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.PrefixClosingExamples.saved_metadata
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.PrefixClosingExamples.consumed_rejected

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.PrefixClosingExamples.disposingCut

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.PrefixClosingExamples.disposing_valid

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.PrefixClosingExamples.closing_rechecked

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.PrefixClosingExamples.disposing_rechecked

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.PrefixClosingExamples.disposing_generated

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.PrefixClosingExamples.closing_metadata

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.PrefixClosingExamples.lost_original_valid

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.PrefixClosingExamples.lost_no_target

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.PrefixClosingExamples.lost_no_rechecking

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.PrefixClosingExamples.exact_protected_caller

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.PrefixClosingExamples.unprotected_caller

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.PrefixClosingExamples.exact_unprotected_caller

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.PrefixClosingExamples.original_record_split

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.PrefixClosingExamples.exact_record_payloads

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.PrefixClosingExamples.compiled_record_payloads
