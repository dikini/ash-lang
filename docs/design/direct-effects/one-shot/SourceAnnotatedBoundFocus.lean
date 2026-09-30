import SourcePlanBounds
import SourceAnnotatedRuntimeState
import SourceScheduledFocus

/-! Focus retains the exact source bounds with the existing child and pending
plans. All source focus forms use the established four signature splits;
metadata cannot invent a successful capability check or a new bound. -/
namespace Ash.OneShot.SourcePlanBounds
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (Signature signature)
open SourcePlannedSources (FocusSignature)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledChecks (Local)

/-- A record of which original source pieces move to the child and queue.
This is metadata decomposition, not an additional evaluation rule. -/
inductive Focused (world : List Nat) :
    {wholeDependencies childDependencies restDependencies : SourceDependencyAnnotations.Dependencies} →
    {whole : Plan wholeDependencies} → {child : Plan childDependencies} → {rest : Plan restDependencies} →
    Annotation world whole → Annotation world child → Annotation world rest → Prop where
  | pure (source : Annotation world .pure) :
      Focused world source (.absent (plan := .pure)) (.absent (plan := .pure))
  | sequence (source : Annotation world (.sequence first second)) :
      Focused world source source.first source.second
  | pairRight (source : Annotation world (.sequence first second)) :
      Focused world source source.second (.absent (plan := .pure))
  | appArgument (source : Annotation world (.sequence function (.sequence argument body))) :
      Focused world source source.second.first source.second.second

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]

/-- The four existing inversions retain actual clause-plan witnesses. The
pair-right case reuses neutral-frame check transport; its bound data do not
depend on that receiving frame. -/
theorem signature_checks_bounds {whole : Signature wholeDependencies}
    {child : Signature childDependencies} {rest : Signature restDependencies}
    (split : FocusSignature whole child rest) {plan : Plan wholeDependencies}
    {hints : Hints receiving} {forest : Forest hints}
    (same : signature plan = whole) (checked : Local outward actions phases world plan forest)
    (bounds : Annotation world plan) :
    ∃ childPlan : Plan childDependencies, ∃ restPlan : Plan restDependencies,
      ∃ childBounds : Annotation world childPlan, ∃ restBounds : Annotation world restPlan,
      signature childPlan = child ∧ signature restPlan = rest ∧
      Local outward actions phases world childPlan (.plain restPlan forest) ∧
      Local outward actions phases world restPlan forest ∧ Focused world bounds childBounds restBounds := by
  cases split with
  | pure => cases plan; exact ⟨.pure, .pure, .absent, .absent, rfl, rfl, .pure, .pure, .pure bounds⟩
  | sequence => cases plan with
    | sequence first second =>
        obtain ⟨firstSame, secondSame⟩ := Signature.sequence.inj same
        cases checked with
        | sequence firstCheck secondCheck =>
          exact ⟨first, second, bounds.first, bounds.second, firstSame, secondSame,
            firstCheck, secondCheck, .sequence bounds⟩
  | pairRight => cases plan with
    | sequence first second =>
        obtain ⟨firstSame, secondSame⟩ := Signature.sequence.inj same
        cases checked with
        | sequence firstCheck secondCheck =>
          exact ⟨second, .pure, bounds.second, .absent, secondSame, rfl,
            SourceScheduledNeutralChecks.local_transport secondCheck (.extra .refl), .pure, .pairRight bounds⟩
  | appArgument => cases plan with
    | sequence first remaining => cases remaining with
      | sequence argument body =>
          obtain ⟨firstSame, remainingSame⟩ := Signature.sequence.inj same
          obtain ⟨argumentSame, bodySame⟩ := Signature.sequence.inj remainingSame
          cases checked with
          | sequence firstCheck remainingCheck => cases remainingCheck with
            | sequence argumentCheck bodyCheck =>
              exact ⟨argument, body, bounds.second.first, bounds.second.second, argumentSame, bodySame,
                argumentCheck, bodyCheck, .appArgument bounds⟩

end Ash.OneShot.SourcePlanBounds


namespace Ash.OneShot.SourceBoundSnapshots
open SourceDeclarationPlans (Plan)
open SourcePlanBounds (Annotation)

/-- Focus selects the existing child and queued annotations and retains the
same pending tail. This relation records data movement on the actual step. -/
inductive Focused : Snapshot world → Snapshot world → Prop where
  | step (source : Snapshot world) {child : Plan childDependencies} {rest : Plan restDependencies}
      (childBounds : Annotation world child) (restBounds : Annotation world rest)
      (selected : SourcePlanBounds.Focused world source.current childBounds restBounds) :
      Focused source (source.focus child rest childBounds restBounds)

theorem Focused.forest {before after : Snapshot world} (step : Focused before after) :
    ∃ dependencies, ∃ rest : Plan dependencies,
      HEq after.forest (SourceRetainedPlans.Forest.plain rest before.forest) := by
  cases step
  exact ⟨_, _, HEq.rfl⟩

theorem Focused.pending {before after : Snapshot world} (step : Focused before after) :
    ∃ dependencies, ∃ rest : Plan dependencies, ∃ bounds : Annotation world rest,
      HEq after.pending (Retained.plain bounds before.pending) := by
  cases step
  exact ⟨_, _, _, HEq.rfl⟩

end Ash.OneShot.SourceBoundSnapshots

namespace Ash.OneShot.SourceAnnotatedRuntimeFocus
open SourcePlanBounds (Annotation Focused signature_checks_bounds)
open SourceDeclarationPlans (Plan)
open SourceDependencyAnnotations (Dependencies)
open SourcePlanSignatures (signature)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceAnnotatedSources (Expression Context focus_decompose)
open SourceScheduledChecks (Local)
open SourcePlannedTyping (Value)
open RecursiveRequirements (Requirements evaluate)
open ProtectionResiduals (merge)
open OwnerPhaseTransitions (spendAll)

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]

/-- Source typing, capability checks and bounds follow the same decomposition.
This covers all ten Focus constructors through their existing signature law. -/
theorem focus_checked_bounds {plan : Plan dependencies} {hints : Hints receiving} {forest : Forest hints}
    (source : Expression operations policy contracts world allowed scope environment whole output demand requirements (signature plan))
    (checked : Local outward actions phases world plan forest) (bounds : Annotation world plan)
    (focus : SourceAnnotatedCode.Focus whole child position) :
    ∃ (input : Value) (childDemand restDemand : List Nat) (current : Requirements childDemand) (rest : Requirements restDemand)
      (childDependencies restDependencies : Dependencies) (childPlan : Plan childDependencies) (restPlan : Plan restDependencies),
      ∃ childBounds : Annotation world childPlan, ∃ restBounds : Annotation world restPlan,
      Expression operations policy contracts world allowed scope environment child input childDemand current (signature childPlan) ∧
      Context operations policy contracts world environment allowed scope position input output restDemand rest (signature restPlan) ∧
      Local outward actions phases world childPlan (.plain restPlan forest) ∧
      Local outward actions phases world restPlan forest ∧ Focused world bounds childBounds restBounds ∧
      demand = childDemand ++ restDemand ∧
      ∀ store receiving before, evaluate store receiving before requirements =
        merge (evaluate store receiving before current) (evaluate store receiving (spendAll before childDemand) rest) := by
  obtain ⟨input, childDemand, restDemand, current, rest, childDependencies, restDependencies, childSignature, restSignature,
    childSource, context, split, sameDemand, evaluation⟩ := focus_decompose source focus
  obtain ⟨childPlan, restPlan, childBounds, restBounds, childSame, restSame, childCheck, restCheck, retained⟩ :=
    signature_checks_bounds split rfl checked bounds
  exact ⟨input, childDemand, restDemand, current, rest, childDependencies, restDependencies, childPlan, restPlan,
    childBounds, restBounds, by simpa only [childSame] using childSource,
    by simpa only [restSame] using context, childCheck, restCheck, retained, sameDemand, evaluation⟩

end Ash.OneShot.SourceAnnotatedRuntimeFocus

namespace Ash.OneShot.SourcePlanBounds.Examples
open SourceScheduledCapabilityAnnotations (Code)
open SourceScheduledCapabilityAnnotations.BoundExamples (nested ordinary protectedMode)

/-- The original annotation has a resource/cleanup/handler in pending code. -/
def source : Code [] (.sequence .pure (.resource (fun _ => .cleanup (needs := []) .pure
    (.handler (effect := SourceDependencyCapture.Examples.effectF)
      (table := SourceDependencyCapture.Examples.resumeTable) [] SourceScheduledClauseHandlers.Examples.innerPlans .pure)))) .nil :=
  .sequence (.operations [] .pure .pure) nested

theorem queued_origin : Focused [] (ofCode source) (.absent (plan := .pure)) (ofCode nested) := .sequence _

theorem queued_ordinary (change : SourcePlanRewriting.ClauseMap) :
    ((ofCode source).second.rewrite change).lookup (.resource 7 (.body .here)) 0 false = some (some ordinary) := by
  rw [Annotation.lookup_rewrite, Annotation.second_lookup, ofCode_lookup]
  rfl

theorem queued_protected (change : SourcePlanRewriting.ClauseMap) :
    ((ofCode source).second.rewrite change).lookup (.resource 7 (.body .here)) 0 true = some (some protectedMode) := by
  rw [Annotation.lookup_rewrite, Annotation.second_lookup, ofCode_lookup]
  rfl

theorem absent_stays_absent {plan : SourceDeclarationPlans.Plan dependencies}
    (change : SourcePlanRewriting.ClauseMap) :
    ((.absent : Annotation world plan).rewrite change).lookup path operation held = none := rfl

end Ash.OneShot.SourcePlanBounds.Examples

#print axioms Ash.OneShot.SourcePlanBounds.signature_checks_bounds
#print axioms Ash.OneShot.SourceAnnotatedRuntimeFocus.focus_checked_bounds
#print axioms Ash.OneShot.SourcePlanBounds.Examples.queued_origin
#print axioms Ash.OneShot.SourcePlanBounds.Examples.queued_ordinary
#print axioms Ash.OneShot.SourcePlanBounds.Examples.queued_protected
#print axioms Ash.OneShot.SourcePlanBounds.Examples.absent_stays_absent

#print axioms Ash.OneShot.SourceBoundSnapshots.Focused.forest
#print axioms Ash.OneShot.SourceBoundSnapshots.Focused.pending
