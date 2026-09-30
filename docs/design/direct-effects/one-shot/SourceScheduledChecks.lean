import SourceRetainedPlans
import SourcePlannedRecipeCongruence

/-! Scheduling checks retain the actual plans in every pending frame. Handler
selection and continuation capabilities use the existing independent relations;
recomposition moves the retained plans without selecting replacements. -/
namespace Ash.OneShot.SourceScheduledChecks
open ScopedExpressions
open SourceDeclarationPlans (Plan ClausePlans)
open SourceContextualHints (Hints checkRequirements)
open SourceContextualInvocationHints (Selection)
open SourceContextualInvocations (Resume Dispose)
open SourcePlannedChecks (CertifiedClauses)
open SourceRetainedPlans (Forest closingForest)
abbrev Receiving := SourceDependencyCapture.Scope

/-- The declaration checker and recursive certification are independent
parameters. Their compatibility is proved when projecting scheduling checks. -/
class DeclarationPolicy where
  accepts : ∀ (_outward : List Instance) (_required : List SourceContextualHints.Requirement)
    {clauses : Clauses} {families : SourceDependencyAnnotations.ClauseDependencies}, ClausePlans clauses families → Prop

instance recipePolicy : DeclarationPolicy where
  accepts := fun _ required {_ _} plans => SourcePlannedRecipeDeclarations.Declarations required plans

/-- The scheduling declaration judgment implies the evidence retained by
certification. This is a pointwise source-judgment law, with no execution or
future-body premise. -/
class DeclarationProjection (admission : DeclarationPolicy)
    (certification : SourcePlannedChecks.DeclarationPolicy) : Prop where
  project : ∀ {outward clauses families required} {plans : ClausePlans clauses families},
    admission.accepts outward required plans → certification.accepts outward required plans

instance recipeProjection : DeclarationProjection recipePolicy SourcePlannedChecks.contextualPolicy where
  project := fun checked => SourcePlannedRecipeDeclarations.Declarations.erase checked

section
variable [admission : DeclarationPolicy] [certification : SourcePlannedChecks.DeclarationPolicy]

mutual
inductive Local (outward : List Instance) (actions : Syntax.UsageTickets)
    [admission : DeclarationPolicy] [certification : SourcePlannedChecks.DeclarationPolicy] :
    OwnerPhaseTransitions.Phases → List Nat → {dependencies : SourceDependencyAnnotations.Dependencies} →
      {scope : Receiving} → {hints : Hints scope} → Plan dependencies → Forest hints → Prop where
  | pure : Local outward actions phases world .pure forest
  | request {hints : Hints scope} {forest : Forest hints}
      (checked : SourceDependencySchemes.Checked outward actions phases world (.request effect operation) scope)
      (scheduled : ∀ captured tail (saved : Hints captured) (waiting : Hints tail) contract modes,
        SourcePlannedCuts.Cut effect operation contract modes hints saved waiting →
        ∀ (savedPlans : Forest saved) (waitingPlans : Forest waiting),
        HEq forest (savedPlans.append waitingPlans) → contract.dispose = true →
        Pending outward actions phases world savedPlans.forClosing (.running waitingPlans)) :
      Local outward actions phases world (.request (effect := effect) (operation := operation)) forest
  | resume {hints : Hints scope} {forest : Forest hints} {selected : Selection}
      {front : Forest selected.front} {saved : Forest selected.saved} {tail : Forest selected.tail}
      (found : SourceContextualInvocationHints.findOwner owner hints = some selected)
      (access : Resume actions phases owner hints (selected.resumed owner))
      (same : HEq forest (front.append (.live (owner := owner) saved tail)))
      (restored : Pending outward actions (OwnerPhaseTransitions.spend phases owner) world
        (saved.append (front.append (.spent (owner := owner) tail))) .nil) :
      Local outward actions phases world (.invoke (key := ⟨owner, .resume⟩)) forest
  | dispose {hints : Hints scope} {forest : Forest hints} {selected : Selection}
      {front : Forest selected.front} {saved : Forest selected.saved} {tail : Forest selected.tail}
      (found : SourceContextualInvocationHints.findOwner owner hints = some selected)
      (access : Dispose outward actions phases owner hints (selected.disposed owner))
      (same : HEq forest (front.append (.live (owner := owner) saved tail)))
      (scheduled : Pending outward actions (OwnerPhaseTransitions.spend phases owner) world
        (saved.forClosing.append (.running (front.append (.spent (owner := owner) tail)))) .nil) :
      Local outward actions phases world (.invoke (key := ⟨owner, .dispose⟩)) forest
  | sequence {after : Plan afterDep}
      (first : Local outward actions phases world before (.plain after forest))
      (second : Local outward actions phases world after forest) :
      Local outward actions phases world (.sequence before after) forest
  | choice : Local outward actions phases world first forest → Local outward actions phases world second forest →
      Local outward actions phases world (.choice first second) forest
  | handler {plans : ClausePlans clauses families} {hints : Hints scope} {forest : Forest hints}
      (recipes : admission.accepts outward required plans)
      (declarations : CertifiedClauses outward world plans)
      (supplied : checkRequirements scope required = true)
      (body : Local outward actions phases world code
        (.handler (effect := effect) (table := table) (families := families) (required := required) forest)) :
      Local outward actions phases world (.handler (effect := effect) (table := table) (clauses := clauses) required plans code) forest
  | cleanup {callback : Plan callbackDep}
      (body : Local outward actions phases world code (.cleanup (needs := needs) callback forest))
      (completion : Local outward actions phases world callback (.running forest)) :
      Local outward actions phases world (.cleanup (needs := needs) callback code) forest
  | resource (body : ∀ identity, identity ∉ world →
      Local outward actions phases (world ++ [identity]) (code identity) (.cell (identity := identity) forest)) :
      Local outward actions phases world (.resource code) forest

inductive Pending (outward : List Instance) (actions : Syntax.UsageTickets)
    [admission : DeclarationPolicy] [certification : SourcePlannedChecks.DeclarationPolicy] :
    OwnerPhaseTransitions.Phases → List Nat → {scope outside : Receiving} →
      {hints : Hints scope} → {outsideHints : Hints outside} → Forest hints → Forest outsideHints → Prop where
  | nil : Pending outward actions phases world .nil outside
  | plain {plan : Plan dependencies}
      (code : Local outward actions phases world plan (rest.append outside))
      (tail : Pending outward actions phases world rest outside) :
      Pending outward actions phases world (.plain plan rest) outside
  | handler {restHints : Hints restScope} {rest : Forest restHints}
      {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
      (supplied : checkRequirements (restScope.append outsideScope) required = true) :
      Pending outward actions phases world rest outside →
      Pending outward actions phases world (.handler (required := required) rest) outside
  | cell : Pending outward actions phases world rest outside → Pending outward actions phases world (.cell rest) outside
  | cleanup {plan : Plan dependencies}
      (completion : Local outward actions phases world plan (.running (rest.append outside)))
      (tail : Pending outward actions phases world rest outside) :
      Pending outward actions phases world (.cleanup plan rest) outside
  | running : Pending outward actions phases world rest outside → Pending outward actions phases world (.running rest) outside
  | live : Pending outward actions phases world saved (rest.append outside) → Pending outward actions phases world rest outside →
      Pending outward actions phases world (.live saved rest) outside
  | spent : Pending outward actions phases world rest outside → Pending outward actions phases world (.spent rest) outside
end

/-- Reuse all earlier capability and ownership results through the existing
planned checks. The request case splits the actual forest at the selected cut. -/
theorem erase_all_with (outward : List Instance) (actions : Syntax.UsageTickets)
    (translate : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → certification.accepts outward required plans) :
    (∀ phases world {dependencies scope} {hints : Hints scope} (plan : Plan dependencies) (forest : Forest hints),
      Local outward actions phases world plan forest → SourcePlannedChecks.Local outward actions phases world plan hints) ∧
    (∀ phases world {scope outside} {hints : Hints scope} {outsideHints : Hints outside}
      (forest : Forest hints) (outsideForest : Forest outsideHints),
      Pending outward actions phases world forest outsideForest →
        SourcePlannedChecks.Pending outward actions phases world hints outsideHints) := by
  constructor <;> intro phases world
  all_goals first
    | (intro dependencies scope hints plan forest checked
       apply Local.rec
         (motive_1 := fun phases world {dependencies scope hints} plan _ _ =>
           SourcePlannedChecks.Local outward actions phases world plan hints)
         (motive_2 := fun phases world {scope outside hints outsideHints} _ _ _ =>
           SourcePlannedChecks.Pending outward actions phases world hints outsideHints)
         (t := checked))
    | (intro scope outside hints outsideHints forest outsideForest checked
       apply Pending.rec
         (motive_1 := fun phases world {dependencies scope hints} plan _ _ =>
           SourcePlannedChecks.Local outward actions phases world plan hints)
         (motive_2 := fun phases world {scope outside hints outsideHints} _ _ _ =>
           SourcePlannedChecks.Pending outward actions phases world hints outsideHints)
         (t := checked))
  all_goals intros
  all_goals first
    | exact .pure
    | exact .nil
    | exact .resume ‹_› ‹_›
    | exact .dispose ‹_› ‹_›
    | exact .sequence ‹_› ‹_›
    | exact .choice ‹_› ‹_›
    | exact .handler (translate ‹_›) ‹_› ‹_› ‹_›
    | exact .handler ‹_›
    | exact .cleanup ‹_› ‹_›
    | exact .resource ‹_›
    | exact .plain ‹_› ‹_›
    | exact .cell ‹_›
    | exact .running ‹_›
    | exact .live ‹_› ‹_›
    | exact .spent ‹_›
    | skip
  all_goals
    rename_i requestScope requestPhases requestWorld effect operation hints forest guard scheduled ih
    apply SourcePlannedChecks.Local.request guard
    intro captured tail saved waiting contract modes same found disposes
    obtain ⟨actualSaved, actualWaiting, cut⟩ := SourcePlannedCuts.of_lookup hints found
    obtain ⟨rfl, rfl⟩ := cut.unique same
    obtain ⟨savedPlans, waitingPlans, exactPlans⟩ := SourceRetainedPlans.split_cut cut forest
    exact ih _ _ _ _ _ _ cut savedPlans waitingPlans exactPlans disposes

theorem Local.erase_with (translate : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → certification.accepts outward required plans) {plan : Plan dependencies} {hints : Hints scope} {forest : Forest hints}
    (checked : Local outward actions phases world plan forest) :
    SourcePlannedChecks.Local outward actions phases world plan hints :=
  (erase_all_with outward actions translate).1 phases world plan forest checked

theorem Pending.erase_with (translate : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → certification.accepts outward required plans) {hints : Hints scope} {outsideHints : Hints outside}
    {forest : Forest hints} {outsideForest : Forest outsideHints}
    (checked : Pending outward actions phases world forest outsideForest) :
    SourcePlannedChecks.Pending outward actions phases world hints outsideHints :=
  (erase_all_with outward actions translate).2 phases world forest outsideForest checked

/-- Every retained handler requirement is checked at its actual receiving
scope, including the suffix of a dormant continuation. -/
theorem Pending.compatible {hints : Hints scope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints}
    (checked : Pending outward actions phases world forest outside) :
    SourceContextualHintChecking.Compatible hints outsideScope := by
  induction forest generalizing outsideScope with
  | nil => exact .nil
  | plain plan rest ih => cases checked with | plain code tail => exact .plain (ih tail)
  | handler rest ih => cases checked with
    | handler supplied tail =>
        exact .handler (SourceContextualRequirements.check_requirements_iff.mp supplied) (ih tail)
  | cell rest ih => cases checked with | cell tail => exact .cell (ih tail)
  | cleanup plan rest ih => cases checked with | cleanup completion tail => exact .cleanup (ih tail)
  | running rest ih => cases checked with | running tail => exact .running (ih tail)
  | live saved rest ihSaved ihRest => cases checked with
    | live inside tail => exact .live (ihSaved inside) (ihRest tail)
  | spent rest ih => cases checked with | spent tail => exact .spent (ih tail)

end

theorem erase_all (outward : List Instance) (actions : Syntax.UsageTickets) :
    (∀ phases world {dependencies scope} {hints : Hints scope} (plan : Plan dependencies) (forest : Forest hints),
      Local outward actions phases world plan forest → SourcePlannedChecks.Local outward actions phases world plan hints) ∧
    (∀ phases world {scope outside} {hints : Hints scope} {outsideHints : Hints outside}
      (forest : Forest hints) (outsideForest : Forest outsideHints),
      Pending outward actions phases world forest outsideForest →
        SourcePlannedChecks.Pending outward actions phases world hints outsideHints) :=
  erase_all_with outward actions (fun checked => checked.erase)

theorem Local.erase [admission : DeclarationPolicy] [certification : SourcePlannedChecks.DeclarationPolicy]
    [projection : DeclarationProjection admission certification] {plan : Plan dependencies} {hints : Hints scope} {forest : Forest hints}
    (checked : Local outward actions phases world plan forest) :
    SourcePlannedChecks.Local outward actions phases world plan hints :=
  Local.erase_with (fun checked => DeclarationProjection.project checked) checked

theorem Pending.erase [admission : DeclarationPolicy] [certification : SourcePlannedChecks.DeclarationPolicy]
    [projection : DeclarationProjection admission certification] {hints : Hints scope} {outsideHints : Hints outside}
    {forest : Forest hints} {outsideForest : Forest outsideHints}
    (checked : Pending outward actions phases world forest outsideForest) :
    SourcePlannedChecks.Pending outward actions phases world hints outsideHints :=
  Pending.erase_with (fun checked => DeclarationProjection.project checked) checked

/-- A closing schedule checks each actual callback of the supplied annotation.
No signature or dependency-index conversion is needed. -/
theorem Pending.closing_checked {plans : SourcePlannedClosingPlans.Plans plan hints}
    {outside : Forest outsideHints}
    (checked : Pending outward actions phases world (closingForest plans) outside) :
    SourcePlannedClosingPlans.Checked outward actions phases world outsideHints plans := by
  induction plans with
  | nil => exact .nil
  | release rest ih => cases checked with | cell tail => exact .release (ih tail)
  | retire rest ih => cases checked with | running tail => exact .retire (ih tail)
  | invoke callback rest ih => cases checked with
    | cleanup completion tail => exact .invoke completion.erase (ih tail)

/-- Extract the scheduled closing prefix from a complete recomposed schedule.
The old local append identity removes the empty outside scope. -/
theorem Pending.closing_prefix_checked {plans : SourcePlannedClosingPlans.Plans plan hints}
    {outside : Forest outsideHints}
    (checked : Pending outward actions phases world ((closingForest plans).append outside) .nil) :
    SourcePlannedClosingPlans.Checked outward actions phases world outsideHints plans := by
  induction plans with
  | nil => exact .nil
  | release rest ih => cases checked with | cell tail => exact .release (ih tail)
  | retire rest ih => cases checked with | running tail => exact .retire (ih tail)
  | invoke callback rest ih => cases checked with
    | cleanup completion tail =>
        exact .invoke ((SourcePlannedRecomposition.local_append_nil _).mp completion.erase) (ih tail)

/-- Invocation scheduling refers to the actual selected owner and actual
retained pieces, independent of how their witnesses were originally supplied. -/
theorem Local.dispose_schedule {hints : Hints scope} {forest : Forest hints} {selected : Selection}
    {front : Forest selected.front} {saved : Forest selected.saved} {tail : Forest selected.tail}
    (checked : Local outward actions phases world (.invoke (key := ⟨owner, .dispose⟩)) forest)
    (found : SourceContextualInvocationHints.findOwner owner hints = some selected)
    (same : HEq forest (front.append (.live (owner := owner) saved tail))) :
    Pending outward actions (OwnerPhaseTransitions.spend phases owner) world
      (saved.forClosing.append (.running (front.append (.spent (owner := owner) tail)))) .nil := by
  cases checked with
  | dispose actual access actualSame scheduled =>
      cases Option.some.inj (actual.symm.trans found)
      obtain ⟨frontSame, liveSame⟩ := Forest.append_injective (eq_of_heq (actualSame.symm.trans same))
      obtain ⟨savedSame, tailSame⟩ := Forest.live.inj liveSame
      cases frontSame
      cases savedSame
      cases tailSame
      exact scheduled

end Ash.OneShot.SourceScheduledChecks

#print axioms Ash.OneShot.SourceScheduledChecks.erase_all
#print axioms Ash.OneShot.SourceScheduledChecks.erase_all_with
#print axioms Ash.OneShot.SourceScheduledChecks.Local.erase_with
#print axioms Ash.OneShot.SourceScheduledChecks.Pending.erase_with
#print axioms Ash.OneShot.SourceScheduledChecks.Local.erase
#print axioms Ash.OneShot.SourceScheduledChecks.Pending.erase
#print axioms Ash.OneShot.SourceScheduledChecks.Pending.closing_checked

#print axioms Ash.OneShot.SourceScheduledChecks.Pending.closing_prefix_checked
#print axioms Ash.OneShot.SourceScheduledChecks.Local.dispose_schedule

#print axioms Ash.OneShot.SourceScheduledChecks.Pending.compatible

#print axioms Ash.OneShot.SourceScheduledChecks.recipeProjection
