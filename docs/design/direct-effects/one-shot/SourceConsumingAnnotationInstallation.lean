import SourcePlanBounds
import SourceConsumingBoundInstallation

/-! Install the bounds carried by the actual source annotation. The partial
data function rejects absent metadata; declaration admission is checked
separately against precisely the extracted bounds. Existing installation,
lookup and execution proofs supply the runtime connection. -/
namespace Ash.OneShot.SourceConsumingStoredBounds
open SourceDeclarationPlans (Plan ClausePlans)
open SourceConsumingClauseAnnotations (ClauseBounds Declarations Bounded)
open SourceAnnotatedRuntime (Handler Stack)
open SourceScheduledCapabilityAnnotations (Code DeclarationPolicy)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledHandlers (register)

section
variable [nested : DeclarationPolicy]
variable {families : SourceDependencyCapture.Families}
variable {required : SourceContextualRechecking.Required}
variable {stack : Stack} (source : StackBounds families stack) (handler : Handler)
variable {plans : ClausePlans handler.clauses.erase clauseFamilies} {body : Plan dependencies}
variable {hints : Hints scope} {forest : Forest hints}
variable (annotation : Code world
  (.handler (effect := handler.effectInst) (table := table) declarationRequired plans body) forest)
variable (planBounds : SourcePlanBounds.Annotation world
  (.handler (effect := handler.effectInst) (table := table) declarationRequired plans body))
variable (fresh : handler.activation ∉ stack.erase.erase.activations)

/-- Queued metadata can install its recorded packet without retaining stale
capability cuts from the source's former receiving continuation. -/
def StackBounds.installFromPlanBounds :
    Option (StackBounds (register families handler.activation clauseFamilies) (.push (.handler handler) stack)) :=
  planBounds.handlerBounds.map (fun bounds => source.install handler plans bounds .bounded fresh)

/-- No alternative bound is an input. Missing metadata cannot produce a
bounded packet, including on the older operation-only annotation route. -/
def StackBounds.installFromAnnotation :
    Option (StackBounds (register families handler.activation clauseFamilies) (.push (.handler handler) stack)) :=
  source.installFromPlanBounds handler (SourcePlanBounds.ofCode annotation) fresh

theorem StackBounds.installFromAnnotation_recorded (bounds : ClauseBounds plans)
    (recorded : annotation.handlerBounds = some bounds) :
    source.installFromAnnotation handler annotation fresh = some (source.install handler plans bounds .bounded fresh) := by
  simp only [StackBounds.installFromAnnotation, StackBounds.installFromPlanBounds,
    SourcePlanBounds.ofCode_handlerBounds, recorded, Option.map_some]

theorem StackBounds.installFromAnnotation_absent (absent : annotation.handlerBounds = none) :
    source.installFromAnnotation handler annotation fresh = none := by
  simp only [StackBounds.installFromAnnotation, StackBounds.installFromPlanBounds,
    SourcePlanBounds.ofCode_handlerBounds, absent, Option.map_none]

theorem StackBounds.Admitted.enter_fromPlanBounds
    (admitted : source.Admitted world required)
    (bounds : ClauseBounds plans) (recorded : planBounds.handlerBounds = some bounds)
    (declarations : Declarations world plans) (checked : Bounded bounds declarations declarationRequired)
    (code : SourceAnnotatedCode.Term) :
    ∃ next,
      source.installFromPlanBounds handler planBounds fresh = some next ∧
      ScopedExecution.RawStep
        ⟨.handle (Instantiation.freezeEffect handler.effectInst) code.erase handler.clauses.erase, handler.scope, stack.erase⟩
        ⟨code.erase, handler.scope, .push (.handler handler.erase) stack.erase⟩ [] [] ∧
      next.Admitted world (register required handler.activation declarationRequired) ∧
      next.handlerAt handler.effectInst =
        some ⟨handler, HandlerBounds.installed (families := families) handler plans bounds .bounded⟩ := by
  have declaration := HandlerBounds.installed_bounded (families := families) (required := required)
    handler plans bounds declarations checked
  obtain ⟨step, retained⟩ := admitted.enter_handler handler plans bounds .bounded fresh declaration code
  exact ⟨source.install handler plans bounds .bounded fresh,
    by simp only [StackBounds.installFromPlanBounds, recorded, Option.map_some],
    step, retained, source.install_lookup handler plans bounds .bounded fresh⟩

/-- A successful extraction uses the exact recorded packet. Reuse the
existing structural declaration rule and actual handler-entry transition;
neither a successful successor nor a future capture is a premise. -/
theorem StackBounds.Admitted.enter_fromAnnotation
    (admitted : source.Admitted world required)
    (bounds : ClauseBounds plans) (recorded : annotation.handlerBounds = some bounds)
    (declarations : Declarations world plans) (checked : Bounded bounds declarations declarationRequired)
    (code : SourceAnnotatedCode.Term) :
    ∃ next,
      source.installFromAnnotation handler annotation fresh = some next ∧
      ScopedExecution.RawStep
        ⟨.handle (Instantiation.freezeEffect handler.effectInst) code.erase handler.clauses.erase, handler.scope, stack.erase⟩
        ⟨code.erase, handler.scope, .push (.handler handler.erase) stack.erase⟩ [] [] ∧
      next.Admitted world (register required handler.activation declarationRequired) ∧
      next.handlerAt handler.effectInst =
        some ⟨handler, HandlerBounds.installed (families := families) handler plans bounds .bounded⟩ := by
  exact StackBounds.Admitted.enter_fromPlanBounds source handler (SourcePlanBounds.ofCode annotation) fresh admitted bounds
    ((SourcePlanBounds.ofCode_handlerBounds annotation).trans recorded) declarations checked code

end

/-- At the source/runtime boundary, ordinary and protected lookup return the
same bounds. This is metadata coherence, not rich expression/plan coherence. -/
theorem HandlerBounds.installed_annotation_lookup
    {families : SourceDependencyCapture.Families} (handler : Handler)
    {plans : ClausePlans handler.clauses.erase clauseFamilies} {body : Plan dependencies}
    {hints : Hints scope} {forest : Forest hints}
    (annotation : Code world
      (.handler (effect := handler.effectInst) (table := table) declarationRequired plans body) forest)
    (bounds : ClauseBounds plans) (recorded : annotation.handlerBounds = some bounds) :
    annotation.boundAt [] operation held =
      some ((HandlerBounds.installed (families := families) handler plans bounds .bounded).bounds.lookup operation held) := by
  rw [Code.boundAt_handler, recorded, Option.map_some, HandlerBounds.installed_lookup]

end Ash.OneShot.SourceConsumingStoredBounds

#print axioms Ash.OneShot.SourceConsumingStoredBounds.StackBounds.installFromAnnotation_recorded
#print axioms Ash.OneShot.SourceConsumingStoredBounds.StackBounds.installFromAnnotation_absent
#print axioms Ash.OneShot.SourceConsumingStoredBounds.StackBounds.Admitted.enter_fromAnnotation
#print axioms Ash.OneShot.SourceConsumingStoredBounds.HandlerBounds.installed_annotation_lookup
#print axioms Ash.OneShot.SourceConsumingStoredBounds.StackBounds.Admitted.enter_fromPlanBounds
