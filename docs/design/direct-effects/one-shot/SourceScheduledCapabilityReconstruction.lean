import SourceScheduledCapabilityCuts

/-! Reconstruct recursive source annotations from an existing structural
schedule. This recovers annotations of actual current code and retained plans;
it assumes no independently checked future source or resumed computation. -/
namespace Ash.OneShot.SourceScheduledCapabilityAnnotations
open ScopedExpressions
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open SourceScheduledChecks (Local Pending)
open SourceScheduledNeutral (OwnerCut)
open SourceContextualInvocationHints (Selection)

variable [declarationPolicy : DeclarationPolicy]

private theorem annotate_resume {hints : Hints scope} {forest : Forest hints} {selected : Selection}
    {front : Forest selected.front} {saved : Forest selected.saved} {tail : Forest selected.tail}
    (found : SourceContextualInvocationHints.findOwner owner hints = some selected)
    (access : SourceContextualInvocations.Resume actions phases owner hints (selected.resumed owner))
    (same : HEq forest (front.append (.live (owner := owner) saved tail)))
    (restored : ∃ annotation : Retained world (saved.append (front.append (.spent (owner := owner) tail))) .nil,
      annotation.Valid outward actions (OwnerPhaseTransitions.spend phases owner)) :
    ∃ annotation : Code world (.invoke (key := ⟨owner, .resume⟩)) forest,
      annotation.Valid outward actions phases := by
  obtain ⟨restored, restoredChecked⟩ := restored
  obtain ⟨⟨inside, insideChecked⟩, ⟨before, beforeChecked⟩, ⟨after, afterChecked⟩⟩ :=
    retained_resume_parts restored restoredChecked
  have cut := SourceScheduledNeutralChecks.owner_of_parts found same
  generalize selected.resumed owner = result at access
  cases access with
  | @checked selected' actual lower compatible =>
    generalize selected'.scopes.resumed owner = lowerResult at lower
    cases lower with
    | checked located known permission available =>
      refine ⟨.resume cut inside before after, ?_⟩
      exact ⟨by simp only [known, Option.any_some, permission], available,
        insideChecked, beforeChecked, afterChecked⟩

private theorem annotate_dispose {hints : Hints scope} {forest : Forest hints} {selected : Selection}
    {front : Forest selected.front} {saved : Forest selected.saved} {tail : Forest selected.tail}
    (found : SourceContextualInvocationHints.findOwner owner hints = some selected)
    (access : SourceContextualInvocations.Dispose outward actions phases owner hints (selected.disposed owner))
    (same : HEq forest (front.append (.live (owner := owner) saved tail)))
    (scheduled : ∃ annotation : Retained world
      (saved.forClosing.append (.running (front.append (.spent (owner := owner) tail)))) .nil,
      annotation.Valid outward actions (OwnerPhaseTransitions.spend phases owner)) :
    ∃ annotation : Code world (.invoke (key := ⟨owner, .dispose⟩)) forest,
      annotation.Valid outward actions phases := by
  obtain ⟨scheduled, scheduledChecked⟩ := scheduled
  obtain ⟨⟨closing, closingChecked⟩, ⟨before, beforeChecked⟩, ⟨after, afterChecked⟩⟩ :=
    retained_dispose_parts scheduled scheduledChecked
  have cut := SourceScheduledNeutralChecks.owner_of_parts found same
  generalize selected.disposed owner = result at access
  cases access with
  | checked actual lower compatible =>
    cases Option.some.inj (actual.symm.trans found)
    generalize selected.scopes.disposed owner = lowerResult at lower
    cases lower with
    | checked located known permission available unprotected closes =>
      have equal := Option.some.inj ((SourceContextualInvocationHints.selected_cut found).lookup.symm.trans located.lookup)
      cases equal
      refine ⟨.dispose cut closing before after, ?_⟩
      exact ⟨by simp only [known, Option.any_some, permission], available, unprotected,
        SourceDependencyCapture.check_closing_iff.mpr closes, closingChecked, beforeChecked, afterChecked⟩

private theorem annotate_request {hints : Hints scope} {forest : Forest hints}
    (checked : SourceDependencySchemes.Checked outward actions phases world (.request effect operation) scope)
    (scheduled : ∀ captured tail (saved : Hints captured) (waiting : Hints tail) contract modes,
      SourcePlannedCuts.Cut effect operation contract modes hints saved waiting →
      ∀ (savedPlans : Forest saved) (waitingPlans : Forest waiting),
      HEq forest (savedPlans.append waitingPlans) → contract.dispose = true →
      ∃ annotation : Retained world savedPlans.forClosing (.running waitingPlans), annotation.Valid outward actions phases) :
    ∃ annotation : Code world (.request (effect := effect) (operation := operation)) forest,
      annotation.Valid outward actions phases := by
  classical
  have guard := SourceDependencySchemes.checked_request checked
  cases SourceDependencyCapture.check_capture_iff.mp guard with
  | builtin found =>
      refine ⟨.operations [(effect, operation)] .request .request, ?_⟩
      simp only [Code.Valid, SourceContextualHints.checkRequirements, List.all_cons, List.all_nil,
        Bool.and_true, SourceContextualHints.checkCapability, found]
  | handler found permission row body closes =>
      obtain ⟨savedHints, waitingHints, plannedCut⟩ := SourcePlannedCuts.of_lookup hints found
      obtain ⟨saved, waiting, cut⟩ := SourceScheduledNeutral.of_cut plannedCut forest
      have closing := scheduled _ _ _ _ _ _ cut.erase saved waiting cut.forest
      let annotations := fun disposes => Classical.choose (closing disposes)
      refine ⟨.selected cut (fun disposes => SourceDependencySchemes.checked_request_owners checked found disposes) annotations,
        guard, ?_⟩
      exact fun disposes => Classical.choose_spec (closing disposes)

section
variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]

/-- Reconstruct annotations by mutual induction on current structural source
derivations. The only translation premise concerns handler declarations;
recursive code and retained contexts are reconstructed by the induction. -/
theorem annotate_all_with (outward : List Instance) (actions : Syntax.UsageTickets)
    (declarations : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      admission.accepts outward required plans → declarationPolicy.accepts required plans) :
    (∀ phases world {dependencies scope} {hints : Hints scope} (plan : Plan dependencies) (forest : Forest hints),
      Local outward actions phases world plan forest →
      ∃ annotation : Code world plan forest, annotation.Valid outward actions phases) ∧
    (∀ phases world {scope outside} {hints : Hints scope} {outsideHints : Hints outside}
      (forest : Forest hints) (outsideForest : Forest outsideHints),
      Pending outward actions phases world forest outsideForest →
      ∃ annotation : Retained world forest outsideForest, annotation.Valid outward actions phases) := by
  classical
  constructor
  all_goals first
    | (intro phases world dependencies scope hints plan forest checked
       apply Local.rec
         (motive_1 := fun phases world {dependencies scope hints} plan forest _ =>
           ∃ annotation : Code world plan forest, annotation.Valid outward actions phases)
         (motive_2 := fun phases world {scope outside hints outsideHints} forest outsideForest _ =>
           ∃ annotation : Retained world forest outsideForest, annotation.Valid outward actions phases)
         (t := checked))
    | (intro phases world scope outside hints outsideHints forest outsideForest checked
       apply Pending.rec
         (motive_1 := fun phases world {dependencies scope hints} plan forest _ =>
           ∃ annotation : Code world plan forest, annotation.Valid outward actions phases)
         (motive_2 := fun phases world {scope outside hints outsideHints} forest outsideForest _ =>
           ∃ annotation : Retained world forest outsideForest, annotation.Valid outward actions phases)
         (t := checked))
  all_goals intros
  all_goals first
    | exact ⟨.operations [] .pure .pure, rfl⟩
    | exact ⟨.operations .nil, rfl⟩
    | exact annotate_request ‹_› ‹_›
    | exact annotate_resume ‹_› ‹_› ‹_› ‹_›
    | exact annotate_dispose ‹_› ‹_› ‹_› ‹_›
    | (rename_i first second ihFirst ihSecond
       obtain ⟨a, ha⟩ := ihFirst
       obtain ⟨b, hb⟩ := ihSecond
       exact ⟨.sequence a b, ha, hb⟩)
    | (rename_i first second ihFirst ihSecond
       obtain ⟨a, ha⟩ := ihFirst
       obtain ⟨b, hb⟩ := ihSecond
       exact ⟨.choice a b, ha, hb⟩)
    | (rename_i recipes certified supplied body ih
       obtain ⟨annotation, checked⟩ := ih
       exact ⟨.handler (declarations recipes) annotation, supplied, checked⟩)
    | (rename_i body completion ihBody ihCompletion
       obtain ⟨a, ha⟩ := ihBody
       obtain ⟨b, hb⟩ := ihCompletion
       exact ⟨.cleanup a b, ha, hb⟩)
    | (rename_i body ih
       exact ⟨.resource (fun identity fresh => Classical.choose (ih identity fresh)),
         fun identity fresh => Classical.choose_spec (ih identity fresh)⟩)
    | (rename_i code tail ihCode ihTail
       obtain ⟨a, ha⟩ := ihCode
       obtain ⟨b, hb⟩ := ihTail
       exact ⟨.plain a b, ha, hb⟩)
    | (rename_i supplied tail ih
       obtain ⟨annotation, checked⟩ := ih
       exact ⟨.handler annotation, supplied, checked⟩)
    | (rename_i tail ih
       obtain ⟨annotation, checked⟩ := ih
       exact ⟨.cell annotation, checked⟩)
    | (rename_i completion tail ihCompletion ihTail
       obtain ⟨a, ha⟩ := ihCompletion
       obtain ⟨b, hb⟩ := ihTail
       exact ⟨.cleanup a b, ha, hb⟩)
    | (rename_i tail ih
       obtain ⟨annotation, checked⟩ := ih
       exact ⟨.running annotation, checked⟩)
    | (rename_i saved tail ihSaved ihTail
       obtain ⟨a, ha⟩ := ihSaved
       obtain ⟨b, hb⟩ := ihTail
       exact ⟨.live a b, ha, hb⟩)
    | (rename_i tail ih
       obtain ⟨annotation, checked⟩ := ih
       exact ⟨.spent annotation, checked⟩)

theorem local_annotated_iff
    (laws : DeclarationLaws declarationPolicy admission certification outward)
    (declarations : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      admission.accepts outward required plans → declarationPolicy.accepts required plans)
    {hints : Hints scope} {forest : Forest hints} {plan : Plan dependencies} :
    Local outward actions phases world plan forest ↔
      ∃ annotation : Code world plan forest, annotation.Valid outward actions phases := by
  constructor
  · exact (annotate_all_with outward actions declarations).1 phases world plan forest
  · rintro ⟨annotation, checked⟩
    exact annotation.compile_with laws checked

theorem pending_annotated_iff
    (laws : DeclarationLaws declarationPolicy admission certification outward)
    (declarations : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      admission.accepts outward required plans → declarationPolicy.accepts required plans)
    {hints : Hints scope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints} :
    Pending outward actions phases world forest outside ↔
      ∃ annotation : Retained world forest outside, annotation.Valid outward actions phases := by
  constructor
  · exact (annotate_all_with outward actions declarations).2 phases world forest outside
  · rintro ⟨annotation, checked⟩
    exact annotation.compile_with laws checked

/-- Recomposition reuses the established structural scheduling theorem. This
asserts existence of valid annotations, not preservation of optional bounds. -/
theorem retained_append_iff
    (laws : DeclarationLaws declarationPolicy admission certification outward)
    (declarations : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      admission.accepts outward required plans → declarationPolicy.accepts required plans)
    {firstHints : Hints firstScope} {secondHints : Hints secondScope} {outsideHints : Hints outsideScope}
    (first : Forest firstHints) (second : Forest secondHints) (outside : Forest outsideHints) :
    (∃ annotation : Retained world (first.append second) outside, annotation.Valid outward actions phases) ↔
      (∃ annotation : Retained world first (second.append outside), annotation.Valid outward actions phases) ∧
      (∃ annotation : Retained world second outside, annotation.Valid outward actions phases) := by
  rw [← pending_annotated_iff laws declarations, ← pending_annotated_iff laws declarations,
    ← pending_annotated_iff laws declarations]
  exact SourceScheduledRecomposition.pending_append_iff first second outside

/-- Source reconstruction and the actual cut provide both captured and waiting
annotations for every current structural retained derivation. -/
theorem annotations_at_cut
    (declarations : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      admission.accepts outward required plans → declarationPolicy.accepts required plans)
    {wholeHints : Hints wholeScope} {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {whole : Forest wholeHints} {saved : Forest savedHints} {waiting : Forest waitingHints}
    (cut : SourceScheduledNeutral.Cut effect operation contract modes whole saved waiting)
    (checked : Pending outward actions phases world whole .nil) :
    (∃ annotation : Retained world saved waiting, annotation.Valid outward actions phases) ∧
    (∃ annotation : Retained world waiting .nil, annotation.Valid outward actions phases) := by
  obtain ⟨annotation, valid⟩ := (annotate_all_with outward actions declarations).2 _ _ _ _ checked
  exact retained_at_cut cut annotation valid

end
end Ash.OneShot.SourceScheduledCapabilityAnnotations

#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.annotate_all_with
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.local_annotated_iff
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.pending_annotated_iff
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.retained_append_iff
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.annotations_at_cut
