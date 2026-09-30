import SourceScheduledRecomposition

/-! Rechecking changes the receiving interpretation and phase map while
retaining the exact typed source plans. Invocation rules supply the structural
pending check used here; no source is recovered from erased dependencies. -/
namespace Ash.OneShot.SourceScheduledFrames
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledChecks (Pending)

/-- The frame's actual retained plan determines its new local check. -/
theorem Frame.recheck {oldHints : Hints oldScope} {receiving : Forest oldHints}
    {restHints : Hints restScope} {rest : Forest restHints}
    {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
    (frame : Frame (evidence := evidence) operations policy contracts tables families required outward actions before world
      receiving entry input output demand requirements layer decorate decoratePlans incoming outgoing)
    (checked : Pending nextOutward actions after world (decoratePlans rest) outside) :
    Frame (evidence := evidence) operations policy contracts tables families required nextOutward actions after world
      (rest.append outside) entry input output demand requirements layer decorate decoratePlans incoming outgoing ∧
    Pending nextOutward actions after world rest outside := by
  cases frame with
  | plain context scope inputAnnotation outputAnnotation old => cases checked with
    | plain current tail => exact ⟨.plain context scope inputAnnotation outputAnnotation current, tail⟩
  | handler scope annotation clauses coverage unique declarations recipes oldSupplied capabilities modes => cases checked with
    | handler supplied tail => exact ⟨.handler scope annotation clauses coverage unique declarations recipes supplied capabilities modes, tail⟩
  | cell scope noEscape annotation interface => cases checked with
    | cell tail => exact ⟨.cell scope noEscape annotation interface, tail⟩
  | armed scope callback annotation interface old => cases checked with
    | cleanup current tail => exact ⟨.armed scope callback annotation interface current, tail⟩
  | running scope callback saved annotation interface => cases checked with
    | running tail => exact ⟨.running scope callback saved annotation interface, tail⟩
  | closing scope interface => cases checked with
    | running tail => exact ⟨.closing scope interface, tail⟩
  | retiring known interface => cases checked with
    | running tail => exact ⟨.retiring known interface, tail⟩

/-- Structural scheduling under the new suffix is sufficient to retain every
source witness, requirement and stored continuation template. -/
theorem Segment.recheck {hints : Hints scope} {forest : Forest hints}
    {oldHints : Hints oldScope} {oldOutside : Forest oldHints}
    {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
    (source : Segment (evidence := evidence) operations policy contracts tables families required actions outward before world
      stack input output demand requirements records forest oldOutside incoming outgoing)
    (checked : Pending nextOutward actions after world forest outside) :
    Segment (evidence := evidence) operations policy contracts tables families required actions nextOutward after world
      stack input output demand requirements records forest outside incoming outgoing := by
  induction source generalizing outsideScope with
  | nil bound => exact .nil bound
  | push head tail bound ih =>
      obtain ⟨headNext, tailCheck⟩ := head.recheck checked
      exact .push headNext (ih tailCheck) bound
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      cases checked with
      | live inside outside =>
        exact .live known actionKnown inputAnnotation answerAnnotation scope held (ihSaved inside) savedBound
          (ihTail outside) resume close bound
  | spent known annotation scope tail bound ih => cases checked with
    | spent outside => exact .spent known annotation scope (ih outside) bound

/-- Widen the external effect interface without changing retained plans. -/
theorem Segment.output_weaken
    (source : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      stack input output demand requirements records forest outside incoming outgoing)
    (larger : outgoing ⊆ nextOutgoing) :
    Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      stack input output demand requirements records forest outside incoming nextOutgoing := by
  induction source with
  | nil bound => exact .nil (List.Subset.trans bound larger)
  | push head tail bound ih => exact .push head (ih larger) bound
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      exact .live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound (ihTail larger) resume close bound
  | spent known annotation scope tail bound ih => exact .spent known annotation scope (ih larger) bound

end Ash.OneShot.SourceScheduledFrames

#print axioms Ash.OneShot.SourceScheduledFrames.Frame.recheck
#print axioms Ash.OneShot.SourceScheduledFrames.Segment.recheck

#print axioms Ash.OneShot.SourceScheduledFrames.Segment.output_weaken
