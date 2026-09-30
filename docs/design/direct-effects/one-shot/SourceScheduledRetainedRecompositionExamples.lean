import SourceScheduledSourceRechecking

/-! Recomposition keeps explicit handler bounds in callbacks, dormant code and
the suffix, including when the prefix was represented only by interfaces. -/
namespace Ash.OneShot.SourceScheduledSourceRechecking.RecompositionExamples
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceScheduledCapabilityAnnotations (Code Retained recipeLaws retained_append_retaining)
open SourceBoundSnapshots.Retained (ofCapability)

private def effect : Instance := .user 72 []
def plan := Plan.handler (effect := effect) (table := []) [] (.nil : ClausePlans .nil []) .pure

def annotated {hints : Hints scope} (forest : Forest hints) : Code [] plan forest :=
  .handler .nil (.operations [] .pure .pure) (some .nil)

theorem annotated_valid {hints : Hints scope} (forest : Forest hints) :
    (annotated forest).Valid [] actions phases := ⟨rfl, rfl⟩

def suffix := Forest.plain plan .nil
def suffixSource : Retained [] suffix .nil := .plain (annotated .nil) (.operations .nil)
theorem suffix_valid : suffixSource.Valid [] actions phases := ⟨annotated_valid _, rfl⟩

def dormant := Forest.plain plan .nil
def front := Forest.cleanup (needs := []) plan (.live (owner := 37) dormant .nil)
def frontSource : Retained [] front (suffix.append .nil) :=
  .cleanup (annotated (.running ((Forest.live (owner := 37) dormant .nil).append (suffix.append .nil))))
    (.live (.plain (annotated (Forest.nil.append (suffix.append .nil))) (.operations .nil)) (.operations .nil))

theorem front_valid : frontSource.Valid [] actions phases :=
  ⟨annotated_valid _, ⟨⟨annotated_valid _, rfl⟩, rfl⟩⟩

/-- The entire projected snapshot is retained, not just the current expression. -/
theorem joined_bounds : ∃ joined : Retained [] (front.append suffix) .nil,
    joined.Valid [] actions phases ∧ ofCapability joined = (ofCapability frontSource).append (ofCapability suffixSource) :=
  retained_append_retaining frontSource suffixSource front_valid suffix_valid

/-- An operation-only prefix must not erase the suffix's explicit bounds. -/
def operationFront := Forest.plain Plan.pure .nil
def operationSource : Retained [] operationFront (suffix.append .nil) :=
  .operations (.plain .nil [] .pure .pure .nil)

theorem operation_prefix_bounds : ∃ joined : Retained [] (operationFront.append suffix) .nil,
    joined.Valid [] actions phases ∧ ofCapability joined = (ofCapability operationSource).append (ofCapability suffixSource) :=
  retained_append_retaining operationSource suffixSource rfl suffix_valid

/-- Recompose closing callbacks from a dormant segment and its running tail.
The resulting forest is exactly the original live forest's closing form. -/
def callbackSegment := Forest.cleanup (needs := []) plan .nil

def liveSource : Retained [] (.live (owner := 37) callbackSegment callbackSegment) .nil :=
  .live (.cleanup (annotated (.running (callbackSegment.append .nil))) (.operations .nil))
    (.cleanup (annotated (.running .nil)) (.operations .nil))

theorem live_valid : liveSource.Valid [] actions phases :=
  ⟨⟨annotated_valid _, rfl⟩, annotated_valid _, rfl⟩

theorem closing_change : RetainedChange [] actions phases liveSource
    (callbackSegment.append (.running callbackSegment)) .nil := by
  apply RetainedChange.closeLive
  · apply RetainedChange.cleanup
    · exact .handler rfl (.operations rfl)
    · exact .empty
  · exact .same

theorem actual_closing_forest : (Forest.live (owner := 37) callbackSegment callbackSegment).forClosing =
    callbackSegment.append (.running callbackSegment) := rfl

theorem closing_compiled : ∃ joined : Retained [] (callbackSegment.append (.running callbackSegment)) .nil,
    joined.Valid [] actions phases ∧ RetainedBounds liveSource (ofCapability joined) :=
  closing_change.compile_retaining (recipeLaws []) (fun evidence => evidence) live_valid

theorem annotated_bounds {hints : Hints scope} (forest : Forest hints) :
    (SourcePlanBounds.ofCode (annotated forest)).Admitted := .bounded .nil .nil (.absent .pure)

theorem live_bounds : (ofCapability liveSource).Admitted :=
  .live (.cleanup (annotated_bounds _) .nil) (.cleanup (annotated_bounds _) .nil)

theorem closing_admitted : ∃ joined : Retained [] (callbackSegment.append (.running callbackSegment)) .nil,
    joined.Valid [] actions phases ∧ RetainedBounds liveSource (ofCapability joined) ∧ (ofCapability joined).Admitted :=
  closing_change.compile_admitted (recipeLaws []) (fun evidence => evidence) live_valid live_bounds

end Ash.OneShot.SourceScheduledSourceRechecking.RecompositionExamples

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.RecompositionExamples.annotated_valid
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.RecompositionExamples.suffix_valid
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.RecompositionExamples.front_valid
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.RecompositionExamples.joined_bounds
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.RecompositionExamples.operation_prefix_bounds
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.RecompositionExamples.live_valid
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.RecompositionExamples.closing_change
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.RecompositionExamples.closing_compiled

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.RecompositionExamples.actual_closing_forest
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.RecompositionExamples.annotated_bounds
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.RecompositionExamples.live_bounds
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.RecompositionExamples.closing_admitted
