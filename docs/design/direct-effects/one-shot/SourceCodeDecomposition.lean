import SourceCodeRecords
import SourceAnnotatedBoundFocus
import SourceScheduledNeutralRetained
import SourceBoundReturns

/-! Recover actual source children from the existing computation metadata.
Compact operation annotations split their original finite interface; explicit
annotations expose their original children. No target-validity premise is used. -/
namespace Ash.OneShot.SourceRequestFootprints
open SourcePlanSignatures (Signature)

/-- Compound operation interfaces retain both child interfaces, including
under conservative requirement weakening. -/
theorem Footprint.components {checking : Signature dependencies}
    (source : Footprint checking required) :
    match checking with
    | .sequence first second | .choice first second =>
      ∃ firstRequired secondRequired, Footprint first firstRequired ∧
        Footprint second secondRequired ∧ firstRequired ++ secondRequired ⊆ required
    | _ => True := by
  induction source with
  | sequence first second _ _ | choice first second _ _ =>
      exact ⟨_, _, first, second, List.Subset.refl _⟩
  | weaken source included ih =>
      rename_i dependencies checking first second
      cases checking <;> try exact True.intro
      all_goals
        obtain ⟨first, second, firstSource, secondSource, contained⟩ := ih
        exact ⟨first, second, firstSource, secondSource, contained.trans included⟩
  | pure | request | handledRequest | handler | cleanup | resource => exact True.intro

end Ash.OneShot.SourceRequestFootprints

namespace Ash.OneShot.SourceScheduledCapabilityAnnotations
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceContextualHints (Hints checkRequirements)
open SourceRetainedPlans (Forest)
open SourcePlanBounds (Annotation ofCode)

variable [declarations : DeclarationPolicy]

theorem Code.sequence_parts {first : Plan firstDependencies} {second : Plan secondDependencies}
    {hints : Hints scope} {forest : Forest hints}
    (source : Code world (.sequence first second) forest)
    (ready : source.Valid outward actions phases) :
    ∃ left : Code world first (.plain second forest), ∃ right : Code world second forest,
      left.Valid outward actions phases ∧ right.Valid outward actions phases ∧
      ofCode left = (ofCode source).first ∧ ofCode right = (ofCode source).second := by
  cases source with
  | operations required footprint declared =>
      obtain ⟨leftRequired, rightRequired, left, right, included⟩ := footprint.components
      have supplied := SourceContextualRequirements.check_requirements_subset included ready
      simp only [checkRequirements, List.all_append, Bool.and_eq_true] at supplied
      obtain ⟨leftReady, rightReady⟩ := supplied
      cases declared with
      | sequence leftDeclared rightDeclared =>
        refine ⟨.operations leftRequired left leftDeclared, .operations rightRequired right rightDeclared,
          ?_, rightReady, rfl, rfl⟩
        exact SourceScheduledAdaptationCompilation.requirements_prefix
          (front := .plain _ .nil) (fun _ => rfl) leftReady
  | sequence left right => exact ⟨left, right, ready.1, ready.2, rfl, rfl⟩

theorem Code.choice_parts {first : Plan firstDependencies} {second : Plan secondDependencies}
    {hints : Hints scope} {forest : Forest hints}
    (source : Code world (.choice first second) forest)
    (ready : source.Valid outward actions phases) :
    ∃ left : Code world first forest, ∃ right : Code world second forest,
      left.Valid outward actions phases ∧ right.Valid outward actions phases ∧
      ofCode left = (ofCode source).left ∧ ofCode right = (ofCode source).right := by
  cases source with
  | operations required footprint declared =>
      obtain ⟨leftRequired, rightRequired, left, right, included⟩ := footprint.components
      have supplied := SourceContextualRequirements.check_requirements_subset included ready
      simp only [checkRequirements, List.all_append, Bool.and_eq_true] at supplied
      obtain ⟨leftReady, rightReady⟩ := supplied
      cases declared with
      | choice leftDeclared rightDeclared =>
        exact ⟨.operations leftRequired left leftDeclared, .operations rightRequired right rightDeclared,
          leftReady, rightReady, rfl, rfl⟩
  | choice left right => exact ⟨left, right, ready.1, ready.2, rfl, rfl⟩

theorem Code.reduced {plan : Plan dependencies} {next : Plan nextDependencies}
    {hints : Hints scope} {forest : Forest hints}
    (source : Code world plan forest) (ready : source.Valid outward actions phases)
    {bounds : Annotation world next}
    (step : SourcePlanBounds.Reduced world rule (ofCode source) bounds) :
    ∃ target : Code world next forest, target.Valid outward actions phases ∧ ofCode target = bounds := by
  cases step with
  | bind =>
      obtain ⟨_, right, _, rightReady, _, rightOrigin⟩ := source.sequence_parts ready
      exact ⟨right, rightReady, rightOrigin⟩
  | beta =>
      obtain ⟨_, remaining, _, remainingReady, _, remainingOrigin⟩ := source.sequence_parts ready
      obtain ⟨_, target, _, targetReady, _, targetOrigin⟩ := remaining.sequence_parts remainingReady
      exact ⟨target, targetReady, targetOrigin.trans (congrArg Annotation.second remainingOrigin)⟩
  | ifTrue =>
      obtain ⟨_, remaining, _, remainingReady, _, remainingOrigin⟩ := source.sequence_parts ready
      obtain ⟨target, _, targetReady, _, targetOrigin, _⟩ := remaining.choice_parts remainingReady
      exact ⟨target, targetReady, targetOrigin.trans (congrArg Annotation.left remainingOrigin)⟩
  | ifFalse =>
      obtain ⟨_, remaining, _, remainingReady, _, remainingOrigin⟩ := source.sequence_parts ready
      obtain ⟨_, target, _, targetReady, _, targetOrigin⟩ := remaining.choice_parts remainingReady
      exact ⟨target, targetReady, targetOrigin.trans (congrArg Annotation.right remainingOrigin)⟩

/-- Pure returned values prefix the retained code using the existing context
plan. The queued annotation is retained exactly beneath those pure prefixes. -/
def Code.plug {plan : Plan dependencies} {hints : Hints scope} {forest : Forest hints}
    (source : Code world plan forest) (position : SourceAnnotatedCode.Context) :
    Code world ((ofCode source).plug position).2.1 forest := by
  cases position <;> first
    | exact .sequence (.operations (plan := Plan.pure) [] .pure .pure) source
    | exact .sequence (.operations (plan := Plan.pure) [] .pure .pure)
        (.sequence (.operations (plan := Plan.pure) [] .pure .pure) source)

theorem Code.plug_valid {plan : Plan dependencies} {hints : Hints scope} {forest : Forest hints}
    (source : Code world plan forest) (position : SourceAnnotatedCode.Context)
    (ready : source.Valid outward actions phases) : (source.plug position).Valid outward actions phases := by
  cases position <;> first | exact ⟨rfl, ready⟩ | exact ⟨rfl, rfl, ready⟩

theorem Code.plug_bounds {plan : Plan dependencies} {hints : Hints scope} {forest : Forest hints}
    (source : Code world plan forest) (position : SourceAnnotatedCode.Context) :
    ofCode (source.plug position) = ((ofCode source).plug position).2.2 := by
  cases position <;> rfl

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]

theorem Code.focused
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {plan : Plan dependencies} {child : Plan childDependencies} {rest : Plan restDependencies}
    {hints : Hints scope} {forest : Forest hints}
    (source : Code world plan forest) (ready : source.Valid outward actions phases)
    {childBounds : Annotation world child} {restBounds : Annotation world rest}
    (step : SourcePlanBounds.Focused world (ofCode source) childBounds restBounds) :
    ∃ current : Code world child (.plain rest forest), ∃ queued : Code world rest forest,
      current.Valid outward actions phases ∧ queued.Valid outward actions phases ∧
      ofCode current = childBounds ∧ ofCode queued = restBounds := by
  cases step with
  | pure => exact ⟨.operations [] .pure .pure, .operations [] .pure .pure, rfl, rfl, rfl, rfl⟩
  | sequence => exact source.sequence_parts ready
  | pairRight =>
      obtain ⟨_, right, _, rightReady, _, rightOrigin⟩ := source.sequence_parts ready
      obtain ⟨current, currentReady, origin⟩ := right.expand_retaining laws project rightReady (.extra .refl)
      exact ⟨current, .operations [] .pure .pure, currentReady, rfl, origin.trans rightOrigin, rfl⟩
  | appArgument =>
      obtain ⟨_, remaining, _, remainingReady, _, remainingOrigin⟩ := source.sequence_parts ready
      obtain ⟨current, queued, currentReady, queuedReady, currentOrigin, queuedOrigin⟩ := remaining.sequence_parts remainingReady
      exact ⟨current, queued, currentReady, queuedReady,
        currentOrigin.trans (congrArg Annotation.first remainingOrigin),
        queuedOrigin.trans (congrArg Annotation.second remainingOrigin)⟩

end Ash.OneShot.SourceScheduledCapabilityAnnotations

#print axioms Ash.OneShot.SourceRequestFootprints.Footprint.components
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.sequence_parts
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.choice_parts
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.reduced
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.plug
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.plug_valid
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.plug_bounds
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.focused
