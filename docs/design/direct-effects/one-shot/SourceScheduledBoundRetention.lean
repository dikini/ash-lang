import SourceScheduledAnnotationSubstitution
import SourceConsumingRecursiveClauses

/-! Exact bound-data retention in generated and rewritten source annotations.
Observation paths name existing annotation children; they add no calculus
syntax or execution rule. Runtime-state retention remains a separate invariant. -/
namespace Ash.OneShot.SourceScheduledCapabilityAnnotations
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceConsumingClauseAnnotations (Bounds ClauseBounds)
open SourcePlanRewriting (ClauseMap)

inductive BoundEdge where
  | first | second | body | callback | saved | caller | tail | closing
  | resource (identity : Nat)
  deriving DecidableEq

section
variable [declarationPolicy : DeclarationPolicy]

mutual
/-- The outer option distinguishes absent metadata from a recorded handler
whose selected offer is unavailable. Resource paths use the actual identity. -/
def Code.boundAt {world dependencies scope} {hints : Hints scope} {plan : Plan dependencies}
    {forest : Forest hints} (annotation : Code world plan forest)
    (path : List BoundEdge) (operation : Nat) (held : Bool) : Option (Option Bounds) :=
  match annotation, path with
  | .handler _ _ bounds, [] => bounds.map (fun recorded => recorded.lookup operation held)
  | .sequence first _, .first :: rest | .choice first _, .first :: rest => first.boundAt rest operation held
  | .sequence _ second, .second :: rest | .choice _ second, .second :: rest => second.boundAt rest operation held
  | .handler _ body _, .body :: rest | .cleanup body _, .body :: rest => body.boundAt rest operation held
  | .cleanup _ callback, .callback :: rest => callback.boundAt rest operation held
  | .resume _ saved _ _, .saved :: rest => saved.boundAt rest operation held
  | .resume _ _ caller _, .caller :: rest | .dispose _ _ caller _, .caller :: rest => caller.boundAt rest operation held
  | .resume _ _ _ tail, .tail :: rest | .dispose _ _ _ tail, .tail :: rest => tail.boundAt rest operation held
  | .dispose _ closing _ _, .closing :: rest => closing.boundAt rest operation held
  | .selected (contract := contract) _ _ closing, .closing :: rest =>
      if allowed : contract.dispose = true then (closing allowed).boundAt rest operation held else none
  | .resource body, .resource identity :: rest =>
      if fresh : identity ∉ world then (body identity fresh).boundAt rest operation held else none
  | _, _ => none

def Retained.boundAt {world scope outsideScope} {hints : Hints scope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints} (annotation : Retained world forest outside)
    (path : List BoundEdge) (operation : Nat) (held : Bool) : Option (Option Bounds) :=
  match annotation, path with
  | .plain code _, .body :: rest => code.boundAt rest operation held
  | .cleanup callback _, .callback :: rest => callback.boundAt rest operation held
  | .live saved _, .saved :: rest => saved.boundAt rest operation held
  | .plain _ tail, .tail :: rest | .cleanup _ tail, .tail :: rest | .live _ tail, .tail :: rest =>
      tail.boundAt rest operation held
  | .handler tail, .tail :: rest | .cell tail, .tail :: rest |
      .running tail, .tail :: rest | .spent tail, .tail :: rest => tail.boundAt rest operation held
  | _, _ => none
end
end

theorem Code.boundAt_cast {first second : Plan dependencies} {hints : Hints scope} {before after : Forest hints}
    (planSame : first = second) (forestSame : before = after) (annotation : Code world first before) :
    (annotation.cast planSame forestSame).boundAt path operation held = annotation.boundAt path operation held := by
  cases planSame; cases forestSame; rfl

theorem Retained.boundAt_cast {hints : Hints scope} {outsideHints : Hints outsideScope}
    {first second : Forest hints} {before after : Forest outsideHints}
    (forestSame : first = second) (outsideSame : before = after) (annotation : Retained world first before) :
    (annotation.cast forestSame outsideSame).boundAt path operation held = annotation.boundAt path operation held := by
  cases forestSame; cases outsideSame; rfl

/-- Every observation path keeps the exact ordinary/protected bounds,
including paths through recursive captures, cleanup and fresh resources. -/
theorem rewrite_bounds_all (change : ClauseMap) :
    (∀ world {dependencies scope} {hints : Hints scope} (plan : Plan dependencies) (forest : Forest hints)
      (annotation : Code world plan forest) path operation held,
      (annotation.rewrite change).boundAt path operation held = annotation.boundAt path operation held) ∧
    (∀ world {scope outsideScope} {hints : Hints scope} {outsideHints : Hints outsideScope}
      (forest : Forest hints) (outside : Forest outsideHints) (annotation : Retained world forest outside) path operation held,
      (annotation.rewrite change).boundAt path operation held = annotation.boundAt path operation held) := by
  have preserve (path : List BoundEdge) :
      (∀ world {dependencies scope} {hints : Hints scope} (plan : Plan dependencies) (forest : Forest hints)
        (annotation : Code world plan forest) operation held,
        (annotation.rewrite change).boundAt path operation held = annotation.boundAt path operation held) ∧
      (∀ world {scope outsideScope} {hints : Hints scope} {outsideHints : Hints outsideScope}
        (forest : Forest hints) (outside : Forest outsideHints) (annotation : Retained world forest outside) operation held,
        (annotation.rewrite change).boundAt path operation held = annotation.boundAt path operation held) := by
    induction path with
    | nil =>
        constructor
        all_goals intros
        all_goals rename_i annotation operation held
        all_goals cases annotation
        all_goals first
          | rfl
          | (dsimp only [Code.rewrite, Retained.rewrite, Code.boundAt, Retained.boundAt]
             simp only [Option.map_map, Function.comp_def, ClauseBounds.lookup_reindex])
    | cons edge path ih =>
        constructor
        all_goals intros
        all_goals rename_i annotation operation held
        all_goals cases annotation <;> cases edge
        all_goals first
          | rfl
          | (dsimp only [Code.rewrite, Retained.rewrite, Code.boundAt, Retained.boundAt]
             simp only [Code.boundAt_cast, Retained.boundAt_cast, ih.1, ih.2])
  constructor
  · intro world dependencies scope hints plan forest annotation path operation held
    exact (preserve path).1 world plan forest annotation operation held
  · intro world scope outsideScope hints outsideHints forest outside annotation path operation held
    exact (preserve path).2 world forest outside annotation operation held

theorem Code.boundAt_rewrite (change : ClauseMap) {hints : Hints scope} {plan : Plan dependencies}
    {forest : Forest hints} (annotation : Code world plan forest) :
    (annotation.rewrite change).boundAt path operation held = annotation.boundAt path operation held :=
  (rewrite_bounds_all change).1 world plan forest annotation path operation held

theorem Retained.boundAt_rewrite (change : ClauseMap) {hints : Hints scope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints} (annotation : Retained world forest outside) :
    (annotation.rewrite change).boundAt path operation held = annotation.boundAt path operation held :=
  (rewrite_bounds_all change).2 world forest outside annotation path operation held

theorem Code.handlerBounds_rewrite (change : ClauseMap) {hints : Hints scope} {forest : Forest hints}
    {plans : ClausePlans clauses families} {body : Plan dependencies}
    (annotation : Code world (.handler (effect := effect) (table := table) required plans body) forest) :
    (annotation.rewrite change).handlerBounds =
      annotation.handlerBounds.map (fun recorded => recorded.reindex (change.apply plans).2) := by
  cases annotation <;> rfl

theorem Code.boundAt_handler {hints : Hints scope} {forest : Forest hints}
    {plans : ClausePlans clauses families} {body : Plan dependencies}
    (annotation : Code world (.handler (effect := effect) (table := table) required plans body) forest) :
    annotation.boundAt [] operation held = annotation.handlerBounds.map (fun recorded => recorded.lookup operation held) := by
  cases annotation <;> rfl

/-- Closed substitution uses the same rewrite, so it retains exact bounds at
every nested source position as well as the previously proved validation. -/
theorem Code.boundAt_substitution {hints : Hints scope} {forest : Forest hints} {plan : Plan dependencies}
    (annotation : Code world plan forest) (closed : ScopedExpressions.ClosedValue value) :
    (annotation.rewrite (SourcePlanRewriting.substitution name value closed.1)).boundAt path operation held =
      annotation.boundAt path operation held :=
  annotation.boundAt_rewrite _

end Ash.OneShot.SourceScheduledCapabilityAnnotations

namespace Ash.OneShot.SourceConsumingClauseAnnotations
open SourceDeclarationPlans (Plan ClausePlans)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledRetainedInterfaces (Interfaces)
open SourceScheduledNeutral (OwnerCut)

section
variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]

/-- The syntax-directed generator retains the source's own bound data. -/
theorem Body.annotate_handler_bounds {plans : ClausePlans clauses families} {code : Plan dependencies}
    (bounds : ClauseBounds plans) (admitted : nested.accepts required plans) (body : Body world owner code)
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {whole : Forest wholeHints} {front : Forest frontHints} {saved : Forest savedHints} {tail : Forest tailHints}
    (cut : OwnerCut owner whole front saved tail)
    (inside : Interfaces world saved) (closing : Interfaces world saved.forClosing)
    (before : Interfaces world front) (after : Interfaces world tail) :
    ((Body.handler (effect := effect) (table := table) bounds admitted body).annotate
      cut inside closing before after).handlerBounds = some bounds := rfl

end

/-- Recursive captures use the same source bounds, independently of their
chain length and actual captured suffix. -/
theorem Body.annotateRecursive_handler_bounds {plans : ClausePlans clauses families} {code : Plan dependencies}
    (bounds : ClauseBounds plans)
    (admitted : SourceScheduledCapabilityAnnotations.recipePolicy.accepts required plans) (body : Body world owner code)
    (owners : List Nat) {terminalHints : Hints terminalScope} {terminal : Forest terminalHints}
    (source : Interfaces world terminal) {suffixHints : Hints suffixScope} {suffix : Forest suffixHints}
    (retained : Interfaces world suffix)
    (closing : Interfaces world ((SourceConsumingRecursiveBounds.chain owners terminal).append suffix).forClosing)
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope} {tailHints : Hints tailScope}
    {whole : Forest wholeHints} {front : Forest frontHints} {tail : Forest tailHints}
    (cut : OwnerCut owner whole front ((SourceConsumingRecursiveBounds.chain owners terminal).append suffix) tail)
    (before : Interfaces world front) (after : Interfaces world tail) :
    ((Body.handler (effect := effect) (table := table) bounds admitted body).annotateRecursive
      owners source retained closing cut before after).handlerBounds = some bounds := rfl

end Ash.OneShot.SourceConsumingClauseAnnotations

namespace Ash.OneShot.SourceScheduledCapabilityAnnotations.BoundExamples
open SourceConsumingClauseAnnotations (Bounds ClauseBounds)
open SourceScheduledClauseHandlers.Examples (innerPlans inner_declarations)
open SourceDependencyCapture.Examples (effectE effectF resumeTable)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)

def ordinary : Bounds := ⟨[(effectF, 0), (effectF, 0)], []⟩
def protectedMode : Bounds := ⟨[], [(effectE, 1)]⟩
def bounds : ClauseBounds innerPlans := .cons (.available ordinary) (.available protectedMode) .nil

def handler {hints : Hints scope} {forest : Forest hints} (metadata : Option (ClauseBounds innerPlans)) :
    Code world (.handler (effect := effectF) (table := resumeTable) [] innerPlans .pure) forest :=
  .handler inner_declarations (.operations [] .pure .pure) metadata

def nested : Code [] (.resource (fun _ => .cleanup (needs := []) .pure
    (.handler (effect := effectF) (table := resumeTable) [] innerPlans .pure))) .nil :=
  .resource (fun _ _ => .cleanup (handler (some bounds)) (.operations [] .pure .pure))

theorem nested_ordinary : nested.boundAt [.resource 7, .body] 0 false = some (some ordinary) := rfl
theorem nested_protected : nested.boundAt [.resource 7, .body] 0 true = some (some protectedMode) := rfl
theorem nested_missing_offer : nested.boundAt [.resource 7, .body] 1 false = some none := rfl

theorem nested_rewritten (change : SourcePlanRewriting.ClauseMap) :
    (nested.rewrite change).boundAt [.resource 7, .body] 0 false = some (some ordinary) := by
  rw [Code.boundAt_rewrite]
  exact nested_ordinary

theorem missing_metadata (change : SourcePlanRewriting.ClauseMap) :
    ((handler (world := []) (forest := .nil) none).rewrite change).boundAt [] 0 false = none := by
  rw [Code.boundAt_rewrite]
  rfl

end Ash.OneShot.SourceScheduledCapabilityAnnotations.BoundExamples

#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.rewrite_bounds_all
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.boundAt_rewrite
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Retained.boundAt_rewrite
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.handlerBounds_rewrite
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.boundAt_handler
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.boundAt_substitution
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Body.annotate_handler_bounds
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Body.annotateRecursive_handler_bounds
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.BoundExamples.nested_ordinary
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.BoundExamples.nested_protected
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.BoundExamples.nested_missing_offer
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.BoundExamples.nested_rewritten
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.BoundExamples.missing_metadata
