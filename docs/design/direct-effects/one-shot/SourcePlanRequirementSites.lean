import SourceRetainedPlanData
import SourceDependencyOwners

/-! Primitive source obligations and their actual syntactic positions.
These annotations precede declaration recipes and source checkers. Their
interpretation as checks remains in SourceScheduledRequirements. -/
namespace Ash.OneShot.SourceScheduledRequirements
open ScopedExpressions ProtectionContracts
open SourceDeclarationPlans (Plan ClausePlans)
open SourceDependencyAnnotations (Dependencies)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)

abbrev Receiving := SourceDependencyCapture.Scope

inductive Requirement where
  | request (effect : Instance) (operation : Nat)
  | resume (owner : Nat)
  | dispose (owner : Nat)
  | install (required : List SourceContextualHints.Requirement) (plans : ClausePlans clauses families)

/-- A source position determines its receiving context. Resource sites are
parameterized by a fresh identity; callback sites run under protection. -/
inductive Site : {dependencies : Dependencies} → Plan dependencies → List Nat →
    {scope : Receiving} → {hints : Hints scope} → Forest hints → Requirement → List Nat →
    {atScope : Receiving} → {atHints : Hints atScope} → Forest atHints → Prop where
  | request : Site (.request (effect := effect) (operation := operation)) world forest (.request effect operation) world forest
  | resume : Site (.invoke (key := ⟨owner, .resume⟩)) world forest (.resume owner) world forest
  | dispose : Site (.invoke (key := ⟨owner, .dispose⟩)) world forest (.dispose owner) world forest
  | install : Site (.handler (effect := effect) (table := table) required plans body) world forest
      (.install required plans) world forest
  | first : Site before world (.plain after forest) requirement atWorld atForest →
      Site (.sequence before after) world forest requirement atWorld atForest
  | second : Site after world forest requirement atWorld atForest →
      Site (.sequence before after) world forest requirement atWorld atForest
  | left : Site first world forest requirement atWorld atForest →
      Site (.choice first second) world forest requirement atWorld atForest
  | right : Site second world forest requirement atWorld atForest →
      Site (.choice first second) world forest requirement atWorld atForest
  | handler : Site body world (.handler (effect := effect) (table := table) (families := families) (required := required) forest)
        requirement atWorld atForest →
      Site (.handler (effect := effect) (table := table) (families := families) required plans body) world forest
        requirement atWorld atForest
  | cleanup : Site body world (.cleanup (needs := needs) callback forest) requirement atWorld atForest →
      Site (.cleanup (needs := needs) callback body) world forest requirement atWorld atForest
  | callback : Site callback world (.running forest) requirement atWorld atForest →
      Site (.cleanup (needs := needs) callback body) world forest requirement atWorld atForest
  | resource (fresh : identity ∉ world) :
      Site (body identity) (world ++ [identity]) (.cell (identity := identity) forest) requirement atWorld atForest →
      Site (.resource body) world forest requirement atWorld atForest

/-- Source positions can be generated before the receiving continuation is
known. Appending that continuation preserves every actual source frame. -/
theorem Site.append {hints : Hints scope} {forest : Forest hints}
    {atHints : Hints atScope} {atForest : Forest atHints}
    (site : Site plan world forest requirement atWorld atForest)
    {outsideHints : Hints outsideScope} (outside : Forest outsideHints) :
    Site plan world (forest.append outside) requirement atWorld (atForest.append outside) := by
  induction site with
  | request => exact .request
  | resume => exact .resume
  | dispose => exact .dispose
  | install => exact .install
  | first next ih => exact .first ih
  | second next ih => exact .second ih
  | left next ih => exact .left ih
  | right next ih => exact .right ih
  | handler next ih => exact .handler ih
  | cleanup next ih => exact .cleanup ih
  | callback next ih => exact .callback ih
  | resource fresh next ih => exact .resource fresh ih

/-- The source-generated caller context around a clause's original receiving
forest. Traversal adds pending code, handlers, resources or cleanup protection;
it never invents a live continuation boundary or replaces a saved forest. -/
inductive Context : {first second : Receiving} → {beforeHints : Hints first} → {afterHints : Hints second} →
    Forest beforeHints → Forest afterHints → Prop where
  | refl : Context forest forest
  | plain : Context before after → Context before (.plain plan after)
  | handler : Context before after →
      Context before (.handler (effect := effect) (table := table) (families := families) (required := required) after)
  | cell : Context before after → Context before (.cell (identity := identity) after)
  | cleanup : Context before after → Context before (.cleanup (needs := needs) plan after)
  | running : Context before after → Context before (.running after)

theorem Context.trans (first : Context before middle) (second : Context middle after) : Context before after := by
  induction second with
  | refl => exact first
  | plain next ih => exact .plain (ih first)
  | handler next ih => exact .handler (ih first)
  | cell next ih => exact .cell (ih first)
  | cleanup next ih => exact .cleanup (ih first)
  | running next ih => exact .running (ih first)

/-- Context generation needs only source syntax, including the body of a
newly installed handler. It assumes no admission of that body before entry. -/
theorem Site.context (site : Site plan world forest requirement atWorld atForest) : Context forest atForest := by
  induction site with
  | request | resume | dispose | install => exact .refl
  | first next ih => exact (Context.plain .refl).trans ih
  | second next ih | left next ih | right next ih => exact ih
  | handler next ih => exact (Context.handler .refl).trans ih
  | cleanup next ih => exact (Context.cleanup .refl).trans ih
  | callback next ih => exact (Context.running .refl).trans ih
  | resource fresh next ih => exact (Context.cell .refl).trans ih

/-- Entering source scopes does not allocate continuation owners. Owner
creation remains a runtime capture operation, distinct from pending references. -/
theorem Context.owners {beforeHints : Hints first} {afterHints : Hints second}
    {before : Forest beforeHints} {after : Forest afterHints} (context : Context before after) :
    SourceDependencyOwners.owners first = SourceDependencyOwners.owners second := by
  induction context with
  | refl => rfl
  | plain next ih | handler next ih | cell next ih | cleanup next ih | running next ih => exact ih

end Ash.OneShot.SourceScheduledRequirements

#print axioms Ash.OneShot.SourceScheduledRequirements.Context.trans
#print axioms Ash.OneShot.SourceScheduledRequirements.Site.context
#print axioms Ash.OneShot.SourceScheduledRequirements.Context.owners

namespace Ash.OneShot.SourcePlannedRecipeDeclarations
open ScopedExpressions
open SourceDeclarationPlans (Plan ModePlans ClausePlans)
open SourceDependencyAnnotations (Dependencies)

/-- This witnesses selection from the actual annotation. It is a structural
derivation of existing clause lookup, with no new dispatch algorithm. -/
inductive Selected (operation : Nat) : (held : Bool) → {clauses : Clauses} →
    {families : SourceDependencyAnnotations.ClauseDependencies} → ClausePlans clauses families →
    Nat → Nat → Code → {family : Nat → Dependencies} → (∀ owner, Plan (family owner)) → Prop where
  | ordinary : Selected operation false
      (.cons (operation := operation) (parameter := parameter) (binder := binder) (body := body)
        (.available plans) protectedMode rest) parameter binder body plans
  | protectedMode : Selected operation true
      (.cons (operation := operation) (parameter := parameter) (binder := binder) (body := body)
        ordinary (.available plans) rest) parameter binder body plans
  | pass (different : operation ≠ other)
      (next : Selected operation held rest parameter binder body plans) :
      Selected operation held (.cons (operation := other) ordinary protectedMode rest) parameter binder body plans

theorem Selected.clause {declarations : ClausePlans clauses families}
    (selected : Selected operation held declarations parameter binder body plans) :
    ScopedExecution.ClauseAt operation clauses parameter binder body := by
  induction selected with
  | ordinary | protectedMode => exact .hit
  | pass different next ih => exact .pass different ih

theorem Selected.lookup {family : Nat → Dependencies} {plans : ∀ owner, Plan (family owner)}
    {declarations : ClausePlans clauses families}
    (selected : Selected operation held declarations parameter binder body plans) :
    (SourceDependencyCapture.lookupDependencies operation families).bind
      (SourceDependencyCapture.modeDependencies held) = some family := by
  induction selected with
  | ordinary | protectedMode => simp [SourceDependencyCapture.lookupDependencies, SourceDependencyCapture.modeDependencies]
  | pass different next ih =>
      simpa only [SourceDependencyCapture.lookupDependencies, if_neg different] using ih

/-- Recover the actual offered plan from existing syntax and dependency lookup. -/
theorem selected_of_lookup {declarations : ClausePlans clauses families}
    (selected : ScopedExecution.ClauseAt operation clauses parameter binder body)
    (found : (SourceDependencyCapture.lookupDependencies operation families).bind
      (SourceDependencyCapture.modeDependencies held) = some family) :
    ∃ plans : ∀ owner, Plan (family owner), Selected operation held declarations parameter binder body plans := by
  induction selected generalizing families with
  | hit => cases declarations with
    | cons ordinary protectedMode rest =>
        simp only [SourceDependencyCapture.lookupDependencies, if_true, Option.bind_some] at found
        cases held with
        | false => cases ordinary with
          | unavailable => cases found
          | available plans => cases Option.some.inj found; exact ⟨plans, .ordinary⟩
        | true => cases protectedMode with
          | unavailable => cases found
          | available plans => cases Option.some.inj found; exact ⟨plans, .protectedMode⟩
  | pass different next ih => cases declarations with
    | cons ordinary protectedMode rest =>
        obtain ⟨plans, chosen⟩ := ih (declarations := rest)
          (by simpa only [SourceDependencyCapture.lookupDependencies, if_neg different] using found)
        exact ⟨plans, .pass different chosen⟩

end Ash.OneShot.SourcePlannedRecipeDeclarations

#print axioms Ash.OneShot.SourcePlannedRecipeDeclarations.Selected.clause
#print axioms Ash.OneShot.SourcePlannedRecipeDeclarations.Selected.lookup
#print axioms Ash.OneShot.SourcePlannedRecipeDeclarations.selected_of_lookup

#print axioms Ash.OneShot.SourceScheduledRequirements.Site.append
