import SourceScheduledCapabilityAnnotations
import SourceScheduledInterfaceCuts

/-! Split general retained capability annotations at an actual forest boundary.
Existing scope, hint, forest and operation-interface equations supply the
transport. The source annotation may contain branches and outside-owner calls. -/
namespace Ash.OneShot.SourceScheduledCapabilityAnnotations
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open SourceScheduledRetainedInterfaces (Interfaces)
open SourceScheduledRecomposition (predicate_congr forest_append_assoc forest_append_nil)
open SourceDependencyChecks (scope_append_assoc)
open SourcePlannedRecomposition (hints_append_assoc hints_append_nil)

variable [declarationPolicy : DeclarationPolicy]

theorem code_append_assoc {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {thirdHints : Hints thirdScope} (first : Forest firstHints) (second : Forest secondHints) (third : Forest thirdHints)
    {plan : Plan dependencies} :
    (∃ annotation : Code world plan ((first.append second).append third), annotation.Valid outward actions phases) ↔
    (∃ annotation : Code world plan (first.append (second.append third)), annotation.Valid outward actions phases) :=
  predicate_congr (scope_append_assoc _ _ _) (hints_append_assoc _ _ _) (forest_append_assoc first second third)
    (fun forest => ∃ annotation : Code world plan forest, annotation.Valid outward actions phases)

theorem running_code_append_assoc {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {thirdHints : Hints thirdScope} (first : Forest firstHints) (second : Forest secondHints) (third : Forest thirdHints)
    {plan : Plan dependencies} :
    (∃ annotation : Code world plan (.running ((first.append second).append third)), annotation.Valid outward actions phases) ↔
    (∃ annotation : Code world plan (.running (first.append (second.append third))), annotation.Valid outward actions phases) :=
  predicate_congr (scope_append_assoc _ _ _) (hints_append_assoc _ _ _) (forest_append_assoc first second third)
    (fun forest => ∃ annotation : Code world plan (.running forest), annotation.Valid outward actions phases)

theorem retained_receiver_assoc {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {thirdHints : Hints thirdScope} (first : Forest firstHints) (second : Forest secondHints) (third : Forest thirdHints)
    {savedHints : Hints savedScope} {saved : Forest savedHints} :
    (∃ annotation : Retained world saved ((first.append second).append third), annotation.Valid outward actions phases) ↔
    (∃ annotation : Retained world saved (first.append (second.append third)), annotation.Valid outward actions phases) :=
  predicate_congr (scope_append_assoc _ _ _) (hints_append_assoc _ _ _) (forest_append_assoc first second third)
    (fun outside => ∃ annotation : Retained world saved outside, annotation.Valid outward actions phases)

private theorem operations_split {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {outsideHints : Hints outsideScope} (first : Forest firstHints) (second : Forest secondHints)
    {outside : Forest outsideHints}
    (source : Interfaces world (first.append second)) (checked : source.check outsideScope = true) :
    (∃ annotation : Retained world first (second.append outside), annotation.Valid outward actions phases) ∧
    (∃ annotation : Retained world second outside, annotation.Valid outward actions phases) := by
  rw [← source.splitAt_append first second, Interfaces.check_append] at checked
  exact ⟨⟨.operations (source.splitAt first second).1, (Bool.and_eq_true_iff.mp checked).1⟩,
    ⟨.operations (source.splitAt first second).2, (Bool.and_eq_true_iff.mp checked).2⟩⟩

/-- A checked recursive annotation yields checked annotations for both exact
pieces. No source derivation or validity assumption about either result is supplied. -/
theorem retained_split {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {outsideHints : Hints outsideScope} (first : Forest firstHints) (second : Forest secondHints)
    {outside : Forest outsideHints}
    (source : Retained world (first.append second) outside) (checked : source.Valid outward actions phases) :
    (∃ annotation : Retained world first (second.append outside), annotation.Valid outward actions phases) ∧
    (∃ annotation : Retained world second outside, annotation.Valid outward actions phases) := by
  induction first with
  | nil => exact ⟨⟨.operations .nil, rfl⟩, source, checked⟩
  | plain plan rest ih => cases source with
    | operations interfaces => exact operations_split _ _ interfaces checked
    | plain code tail =>
      obtain ⟨⟨before, beforeChecked⟩, after⟩ := ih tail checked.2
      obtain ⟨code, codeChecked⟩ := (code_append_assoc rest second outside).mp ⟨code, checked.1⟩
      exact ⟨⟨.plain code before, codeChecked, beforeChecked⟩, after⟩
  | handler rest ih => cases source with
    | operations interfaces => exact operations_split _ _ interfaces checked
    | handler tail =>
      obtain ⟨⟨before, beforeChecked⟩, after⟩ := ih tail checked.2
      refine ⟨⟨.handler before, ?_, beforeChecked⟩, after⟩
      simpa only [scope_append_assoc] using checked.1
  | cell rest ih => cases source with
    | operations interfaces => exact operations_split _ _ interfaces checked
    | cell tail =>
      obtain ⟨⟨before, beforeChecked⟩, after⟩ := ih tail checked
      exact ⟨⟨.cell before, beforeChecked⟩, after⟩
  | cleanup plan rest ih => cases source with
    | operations interfaces => exact operations_split _ _ interfaces checked
    | cleanup code tail =>
      obtain ⟨⟨before, beforeChecked⟩, after⟩ := ih tail checked.2
      obtain ⟨code, codeChecked⟩ := (running_code_append_assoc rest second outside).mp ⟨code, checked.1⟩
      exact ⟨⟨.cleanup code before, codeChecked, beforeChecked⟩, after⟩
  | running rest ih => cases source with
    | operations interfaces => exact operations_split _ _ interfaces checked
    | running tail =>
      obtain ⟨⟨before, beforeChecked⟩, after⟩ := ih tail checked
      exact ⟨⟨.running before, beforeChecked⟩, after⟩
  | live saved rest ihSaved ih => cases source with
    | operations interfaces => exact operations_split _ _ interfaces checked
    | live dormant tail =>
      obtain ⟨⟨before, beforeChecked⟩, after⟩ := ih tail checked.2
      obtain ⟨dormant, dormantChecked⟩ := (retained_receiver_assoc rest second outside).mp ⟨dormant, checked.1⟩
      exact ⟨⟨.live dormant before, dormantChecked, beforeChecked⟩, after⟩
  | spent rest ih => cases source with
    | operations interfaces => exact operations_split _ _ interfaces checked
    | spent tail =>
      obtain ⟨⟨before, beforeChecked⟩, after⟩ := ih tail checked
      exact ⟨⟨.spent before, beforeChecked⟩, after⟩

theorem retained_receiver_nil {hints : Hints scope} {forest : Forest hints}
    {outsideHints : Hints outsideScope} (outside : Forest outsideHints) :
    (∃ annotation : Retained world forest (outside.append .nil), annotation.Valid outward actions phases) ↔
    (∃ annotation : Retained world forest outside, annotation.Valid outward actions phases) :=
  predicate_congr (SourceDependencyProjection.scope_append_nil _) (hints_append_nil _) (forest_append_nil outside)
    (fun receiver => ∃ annotation : Retained world forest receiver, annotation.Valid outward actions phases)

theorem retained_spent_tail {hints : Hints scope} {forest : Forest hints}
    {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
    (source : Retained world (.spent (owner := owner) forest) outside) (checked : source.Valid outward actions phases) :
    ∃ annotation : Retained world forest outside, annotation.Valid outward actions phases := by
  cases source with
  | operations interfaces => cases interfaces with
    | spent tail => exact ⟨.operations tail, checked⟩
  | spent tail => exact ⟨tail, checked⟩

theorem retained_running_tail {hints : Hints scope} {forest : Forest hints}
    {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
    (source : Retained world (.running forest) outside) (checked : source.Valid outward actions phases) :
    ∃ annotation : Retained world forest outside, annotation.Valid outward actions phases := by
  cases source with
  | operations interfaces => cases interfaces with
    | running tail => exact ⟨.operations tail, checked⟩
  | running tail => exact ⟨tail, checked⟩

/-- The restored annotation supplies the saved computation, caller prefix and
waiting tail at exactly the same spent phase. -/
theorem retained_resume_parts {frontHints : Hints frontScope} {savedHints : Hints savedScope}
    {tailHints : Hints tailScope} {front : Forest frontHints} {saved : Forest savedHints} {tail : Forest tailHints}
    (source : Retained world (saved.append (front.append (.spent (owner := owner) tail))) .nil)
    (checked : source.Valid outward actions phases) :
    (∃ annotation : Retained world saved (front.append (.spent (owner := owner) tail)), annotation.Valid outward actions phases) ∧
    (∃ annotation : Retained world front (.spent (owner := owner) tail), annotation.Valid outward actions phases) ∧
    (∃ annotation : Retained world tail .nil, annotation.Valid outward actions phases) := by
  obtain ⟨inside, ⟨caller, callerChecked⟩⟩ := retained_split saved _ source checked
  obtain ⟨before, ⟨after, afterChecked⟩⟩ := retained_split front _ caller callerChecked
  exact ⟨(retained_receiver_nil _).mp inside, (retained_receiver_nil _).mp before,
    retained_spent_tail after afterChecked⟩

/-- Closing uses the same split, retaining callback annotations and caller data. -/
theorem retained_dispose_parts {frontHints : Hints frontScope} {savedHints : Hints savedScope}
    {tailHints : Hints tailScope} {front : Forest frontHints} {saved : Forest savedHints} {tail : Forest tailHints}
    (source : Retained world (saved.forClosing.append (.running (front.append (.spent (owner := owner) tail)))) .nil)
    (checked : source.Valid outward actions phases) :
    (∃ annotation : Retained world saved.forClosing (.running (front.append (.spent (owner := owner) tail))), annotation.Valid outward actions phases) ∧
    (∃ annotation : Retained world front (.spent (owner := owner) tail), annotation.Valid outward actions phases) ∧
    (∃ annotation : Retained world tail .nil, annotation.Valid outward actions phases) := by
  obtain ⟨closing, ⟨caller, callerChecked⟩⟩ := retained_split saved.forClosing _ source checked
  obtain ⟨caller, callerChecked⟩ := retained_running_tail caller callerChecked
  obtain ⟨before, ⟨after, afterChecked⟩⟩ := retained_split front _ caller callerChecked
  exact ⟨(retained_receiver_nil _).mp closing, (retained_receiver_nil _).mp before,
    retained_spent_tail after afterChecked⟩

/-- Extract general source annotations at the actual selected handler boundary.
Both pieces come from the current whole annotation, not a check on a successor. -/
theorem retained_at_cut {wholeHints : Hints wholeScope} {savedHints : Hints savedScope}
    {waitingHints : Hints waitingScope} {whole : Forest wholeHints}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (cut : SourceScheduledNeutral.Cut effect operation contract modes whole saved waiting)
    (source : Retained world whole .nil) (checked : source.Valid outward actions phases) :
    (∃ annotation : Retained world saved waiting, annotation.Valid outward actions phases) ∧
    (∃ annotation : Retained world waiting .nil, annotation.Valid outward actions phases) := by
  obtain ⟨recomposed, valid⟩ :=
    (predicate_congr cut.erase.reconstruct_scope cut.erase.hints cut.forest
      (fun forest => ∃ annotation : Retained world forest .nil, annotation.Valid outward actions phases)).mp
        ⟨source, checked⟩
  obtain ⟨inside, after⟩ := retained_split saved waiting recomposed valid
  exact ⟨(retained_receiver_nil waiting).mp inside, after⟩

end Ash.OneShot.SourceScheduledCapabilityAnnotations

#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.code_append_assoc
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.running_code_append_assoc
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.retained_receiver_assoc
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.retained_split

#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.retained_receiver_nil

#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.retained_spent_tail

#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.retained_running_tail

#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.retained_resume_parts

#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.retained_dispose_parts
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.retained_at_cut
