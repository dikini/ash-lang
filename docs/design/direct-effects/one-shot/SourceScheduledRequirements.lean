import SourcePlanRequirementSites
import SourceScheduledScopedInvocations

/-! Requirements at syntactic check sites. A site retains its actual receiving
forest and resource world. Sequencing, handlers, resources and both cleanup
branches derive those contexts structurally from the existing plan grammar.
This is checking annotation data, not another computation language. -/
namespace Ash.OneShot.SourceScheduledRequirements
open ScopedExpressions ProtectionContracts
open SourceDeclarationPlans (Plan ClausePlans)
open SourceDependencyAnnotations (Dependencies)
open SourceContextualHints (Hints checkRequirements)
open SourceRetainedPlans (Forest)
open SourceScheduledChecks (Local Pending)
open SourceContextualInvocationHints (Selection)
open SourceContextualInvocations (Resume Dispose)
open SourceScheduledNeutral (OwnerCut)
open OwnerPhaseTransitions (spend)
/-- Reuse an authenticated owner cut through the structurally generated
source context. Saved code and the original waiting tail remain identical. -/
theorem Context.owner_cut {hints : Hints scope} {forest : Forest hints}
    {atHints : Hints atScope} {atForest : Forest atHints}
    {frontHints : Hints frontScope} {front : Forest frontHints}
    {savedHints : Hints savedScope} {saved : Forest savedHints}
    {waitingHints : Hints waitingScope} {waiting : Forest waitingHints}
    (context : Context forest atForest) (cut : OwnerCut owner forest front saved waiting) :
    ∃ atFrontScope, ∃ atFrontHints : Hints atFrontScope, ∃ atFront : Forest atFrontHints,
      OwnerCut owner atForest atFront saved waiting := by
  induction context with
  | refl => exact ⟨_, _, _, cut⟩
  | plain next ih => obtain ⟨_, _, _, selected⟩ := ih cut; exact ⟨_, _, _, .plain selected⟩
  | handler next ih => obtain ⟨_, _, _, selected⟩ := ih cut; exact ⟨_, _, _, .handler selected⟩
  | cell next ih => obtain ⟨_, _, _, selected⟩ := ih cut; exact ⟨_, _, _, .cell selected⟩
  | cleanup next ih => obtain ⟨_, _, _, selected⟩ := ih cut; exact ⟨_, _, _, .cleanup selected⟩
  | running next ih => obtain ⟨_, _, _, selected⟩ := ih cut; exact ⟨_, _, _, .running selected⟩

/-- Source traversal changes the caller prefix, never the saved continuation
or its waiting tail. Reuse its proof-independent context annotation. -/
theorem Site.owner_cut {plan : Plan dependencies} {hints : Hints scope} {forest : Forest hints}
    {atHints : Hints atScope} {atForest : Forest atHints}
    {frontHints : Hints frontScope} {front : Forest frontHints}
    {savedHints : Hints savedScope} {saved : Forest savedHints}
    {waitingHints : Hints waitingScope} {waiting : Forest waitingHints}
    (site : Site plan world forest requirement atWorld atForest)
    (cut : OwnerCut owner forest front saved waiting) :
    ∃ atFrontScope, ∃ atFrontHints : Hints atFrontScope, ∃ atFront : Forest atFrontHints,
      OwnerCut owner atForest atFront saved waiting :=
  site.context.owner_cut cut

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]

/-- Each obligation uses the existing independent access, routing, scheduling
or declaration checks. No complete clause check or future state is a premise. -/
def Check (outward : List Instance) (actions : Syntax.UsageTickets) (phases : OwnerPhaseTransitions.Phases)
    (world : List Nat) {scope : Receiving} {hints : Hints scope} (forest : Forest hints) : Requirement → Prop
  | .request effect operation =>
      SourceDependencySchemes.Checked outward actions phases world (.request effect operation) scope ∧
      ∀ captured tail (savedHints : Hints captured) (waitingHints : Hints tail) contract modes,
        SourcePlannedCuts.Cut effect operation contract modes hints savedHints waitingHints →
        ∀ (saved : Forest savedHints) (waiting : Forest waitingHints), HEq forest (saved.append waiting) →
          contract.dispose = true → Pending outward actions phases world saved.forClosing (.running waiting)
  | .resume owner =>
      ∃ selected : Selection, ∃ (front : Forest selected.front) (saved : Forest selected.saved) (tail : Forest selected.tail),
        OwnerCut owner forest front saved tail ∧
        Resume actions phases owner hints (selected.resumed owner) ∧
        Pending outward actions (spend phases owner) world saved (front.append (.spent (owner := owner) tail)) ∧
        Pending outward actions (spend phases owner) world front (.spent (owner := owner) tail) ∧
        Pending outward actions (spend phases owner) world tail .nil
  | .dispose owner =>
      ∃ selected : Selection, ∃ (front : Forest selected.front) (saved : Forest selected.saved) (tail : Forest selected.tail),
        OwnerCut owner forest front saved tail ∧
        Dispose outward actions phases owner hints (selected.disposed owner) ∧
        Pending outward actions (spend phases owner) world saved.forClosing (.running (front.append (.spent (owner := owner) tail))) ∧
        Pending outward actions (spend phases owner) world front (.spent (owner := owner) tail) ∧
        Pending outward actions (spend phases owner) world tail .nil
  | .install required plans =>
      admission.accepts outward required plans ∧
      SourcePlannedChecks.CertifiedClauses outward world plans ∧ checkRequirements scope required = true

def Satisfied (outward : List Instance) (actions : Syntax.UsageTickets) (phases : OwnerPhaseTransitions.Phases)
    (world : List Nat) {dependencies : Dependencies} (plan : Plan dependencies)
    {scope : Receiving} {hints : Hints scope} (forest : Forest hints) : Prop :=
  ∀ {requirement atWorld atScope} {atHints : Hints atScope} {atForest : Forest atHints},
    Site plan world forest requirement atWorld atForest → Check outward actions phases atWorld atForest requirement

/-- Requirements compose by their actual source positions. In particular,
sequencing retains the suffix plan in the first computation's receiving forest. -/
theorem satisfied_sequence {first : Plan firstDep} {second : Plan secondDep} {forest : Forest hints} :
    Satisfied outward actions phases world (.sequence first second) forest ↔
      Satisfied outward actions phases world first (.plain second forest) ∧
      Satisfied outward actions phases world second forest := by
  constructor
  · intro supplied
    exact ⟨fun site => supplied (.first site), fun site => supplied (.second site)⟩
  · rintro ⟨first, second⟩ requirement atWorld atScope atHints atForest site
    cases site with
    | first site => exact first site
    | second site => exact second site

theorem satisfied_choice {first : Plan firstDep} {second : Plan secondDep} {forest : Forest hints} :
    Satisfied outward actions phases world (.choice first second) forest ↔
      Satisfied outward actions phases world first forest ∧ Satisfied outward actions phases world second forest := by
  constructor
  · intro supplied; exact ⟨fun site => supplied (.left site), fun site => supplied (.right site)⟩
  · rintro ⟨first, second⟩ requirement atWorld atScope atHints atForest site
    cases site with
    | left site => exact first site
    | right site => exact second site

theorem satisfied_handler {plans : ClausePlans clauses families} {body : Plan dependencies} {forest : Forest hints} :
    Satisfied outward actions phases world (.handler (effect := effect) (table := table) required plans body) forest ↔
      Check outward actions phases world forest (.install required plans) ∧
      Satisfied outward actions phases world body
        (.handler (effect := effect) (table := table) (families := families) (required := required) forest) := by
  constructor
  · intro supplied; exact ⟨supplied .install, fun site => supplied (.handler site)⟩
  · rintro ⟨installed, body⟩ requirement atWorld atScope atHints atForest site
    cases site with
    | install => exact installed
    | handler site => exact body site

theorem satisfied_cleanup {callback : Plan callbackDep} {body : Plan bodyDep} {forest : Forest hints} :
    Satisfied outward actions phases world (.cleanup (needs := needs) callback body) forest ↔
      Satisfied outward actions phases world body (.cleanup (needs := needs) callback forest) ∧
      Satisfied outward actions phases world callback (.running forest) := by
  constructor
  · intro supplied; exact ⟨fun site => supplied (.cleanup site), fun site => supplied (.callback site)⟩
  · rintro ⟨body, callback⟩ requirement atWorld atScope atHints atForest site
    cases site with
    | cleanup site => exact body site
    | callback site => exact callback site

theorem satisfied_resource {family : Nat → Dependencies} {body : ∀ identity, Plan (family identity)} {forest : Forest hints} :
    Satisfied outward actions phases world (.resource body) forest ↔
      ∀ identity, identity ∉ world →
        Satisfied outward actions phases (world ++ [identity]) (body identity) (.cell (identity := identity) forest) := by
  constructor
  · intro supplied identity fresh
    exact fun site => supplied (.resource fresh site)
  · intro supplied requirement atWorld atScope atHints atForest site
    cases site with | resource fresh site => exact supplied _ fresh site

theorem request_iff {hints : Hints scope} {forest : Forest hints} :
    Check outward actions phases world forest (.request effect operation) ↔
      Local outward actions phases world (.request (effect := effect) (operation := operation)) forest := by
  constructor
  · rintro ⟨guard, scheduled⟩; exact .request guard scheduled
  · intro checked; cases checked with | request guard scheduled => exact ⟨guard, scheduled⟩

theorem resume_iff {hints : Hints scope} {forest : Forest hints} :
    Check outward actions phases world forest (.resume owner) ↔
      Local outward actions phases world (.invoke (key := ⟨owner, .resume⟩)) forest := by
  constructor
  · rintro ⟨selected, front, saved, tail, cut, access, inside, before, after⟩
    exact (SourceScheduledScopedInvocations.resume_iff cut).mpr ⟨access, inside, before, after⟩
  · intro checked
    obtain ⟨selected, found⟩ : ∃ selected, SourceContextualInvocationHints.findOwner owner hints = some selected := by
      cases checked with | resume found access same pending => exact ⟨_, found⟩
    obtain ⟨front, saved, tail, cut⟩ := SourceScheduledNeutral.of_owner forest found
    exact ⟨selected, front, saved, tail, cut, (SourceScheduledScopedInvocations.resume_iff cut).mp checked⟩

theorem dispose_iff {hints : Hints scope} {forest : Forest hints} :
    Check outward actions phases world forest (.dispose owner) ↔
      Local outward actions phases world (.invoke (key := ⟨owner, .dispose⟩)) forest := by
  constructor
  · rintro ⟨selected, front, saved, tail, cut, access, closing, before, after⟩
    exact (SourceScheduledScopedInvocations.dispose_iff cut).mpr ⟨access, closing, before, after⟩
  · intro checked
    obtain ⟨selected, found⟩ : ∃ selected, SourceContextualInvocationHints.findOwner owner hints = some selected := by
      cases checked with | dispose found access same pending => exact ⟨_, found⟩
    obtain ⟨front, saved, tail, cut⟩ := SourceScheduledNeutral.of_owner forest found
    exact ⟨selected, front, saved, tail, cut, (SourceScheduledScopedInvocations.dispose_iff cut).mp checked⟩

/-- Every generated site inherits the check at its exact world and forest. -/
theorem necessary {plan : Plan dependencies} {hints : Hints scope} {forest : Forest hints}
    (checked : Local outward actions phases world plan forest) : Satisfied outward actions phases world plan forest := by
  intro requirement atWorld atScope atHints atForest site
  induction site with
  | request => exact request_iff.mpr checked
  | resume => exact resume_iff.mpr checked
  | dispose => exact dispose_iff.mpr checked
  | install => cases checked with | handler recipes declarations supplied body => exact ⟨recipes, declarations, supplied⟩
  | first site ih => cases checked with | sequence first second => exact ih first
  | second site ih => cases checked with | sequence first second => exact ih second
  | left site ih => cases checked with | choice left right => exact ih left
  | right site ih => cases checked with | choice left right => exact ih right
  | handler site ih => cases checked with | handler recipes declarations supplied body => exact ih body
  | cleanup site ih => cases checked with | cleanup body callback => exact ih body
  | callback site ih => cases checked with | cleanup body callback => exact ih callback
  | resource fresh site ih => cases checked with | resource body => exact ih (body _ fresh)

/-- Structural compilation covers the entire existing plan grammar. The
requirements supply individual sites, not a proof of the desired conclusion. -/
theorem compile (plan : Plan dependencies) (world : List Nat) {hints : Hints scope} (forest : Forest hints)
    (supplied : Satisfied outward actions phases world plan forest) : Local outward actions phases world plan forest := by
  cases plan with
  | pure => exact .pure
  | request => exact request_iff.mp (supplied .request)
  | invoke =>
      rename_i key
      cases key with | mk owner mode => cases mode with
        | resume => exact resume_iff.mp (supplied .resume)
        | dispose => exact dispose_iff.mp (supplied .dispose)
  | sequence first second =>
      exact .sequence (compile first world (.plain second forest) (fun site => supplied (.first site)))
        (compile second world forest (fun site => supplied (.second site)))
  | choice first second =>
      exact .choice (compile first world forest (fun site => supplied (.left site)))
        (compile second world forest (fun site => supplied (.right site)))
  | handler required plans body =>
      obtain ⟨recipes, declarations, installed⟩ := supplied .install
      exact .handler recipes declarations installed (compile body world _ (fun site => supplied (.handler site)))
  | cleanup callback body =>
      exact .cleanup (compile body world (.cleanup callback forest) (fun site => supplied (.cleanup site)))
        (compile callback world (.running forest) (fun site => supplied (.callback site)))
  | resource body =>
      exact .resource (fun identity fresh => compile (body identity) (world ++ [identity]) (.cell forest)
        (fun site => supplied (.resource fresh site)))
termination_by structural plan

theorem satisfied_iff {plan : Plan dependencies} {hints : Hints scope} {forest : Forest hints} :
    Satisfied outward actions phases world plan forest ↔ Local outward actions phases world plan forest :=
  ⟨compile plan world forest, necessary⟩

omit admission certification in
/-- Every actual check site is an instance of a source-local template whose
receiving forest is initially empty. The template retains all caller frames,
including handlers and protected callback entry, but no runtime capture. -/
theorem Site.factor {plan : Plan dependencies} {hints : Hints scope} {forest : Forest hints}
    {atHints : Hints atScope} {atForest : Forest atHints}
    (site : Site plan world forest requirement atWorld atForest) :
    ∃ frontScope, ∃ frontHints : Hints frontScope, ∃ front : Forest frontHints,
      Site plan world .nil requirement atWorld front ∧
      atScope = frontScope.append scope ∧ HEq atHints (frontHints.append hints) ∧
      HEq atForest (front.append forest) := by
  induction site with
  | request => exact ⟨_, _, .nil, .request, rfl, HEq.rfl, HEq.rfl⟩
  | resume => exact ⟨_, _, .nil, .resume, rfl, HEq.rfl, HEq.rfl⟩
  | dispose => exact ⟨_, _, .nil, .dispose, rfl, HEq.rfl, HEq.rfl⟩
  | install => exact ⟨_, _, .nil, .install, rfl, HEq.rfl, HEq.rfl⟩
  | @first beforeDep before world afterDep after scope hints forest requirement atWorld atScope atHints atForest next ih =>
      obtain ⟨frontScope, frontHints, front, source, scopes, annotations, plans⟩ := ih
      let frame : Forest (Hints.plain (dependencies := afterDep) .nil) := .plain after .nil
      exact ⟨_, _, front.append frame, .first (source.append frame),
        scopes.trans (SourceDependencyChecks.scope_append_assoc frontScope (.plain afterDep .nil) scope).symm,
        annotations.trans (SourcePlannedRecomposition.hints_append_assoc frontHints (Hints.plain (dependencies := afterDep) .nil) hints).symm,
        plans.trans (SourceScheduledRecomposition.forest_append_assoc front frame forest).symm⟩
  | second next ih =>
      obtain ⟨_, _, front, source, scopes, annotations, plans⟩ := ih
      exact ⟨_, _, front, .second source, scopes, annotations, plans⟩
  | left next ih =>
      obtain ⟨_, _, front, source, scopes, annotations, plans⟩ := ih
      exact ⟨_, _, front, .left source, scopes, annotations, plans⟩
  | right next ih =>
      obtain ⟨_, _, front, source, scopes, annotations, plans⟩ := ih
      exact ⟨_, _, front, .right source, scopes, annotations, plans⟩
  | @handler bodyDep body world effect table families required scope hints forest requirement atWorld atScope atHints atForest clauses declarations next ih =>
      obtain ⟨frontScope, frontHints, front, source, scopes, annotations, plans⟩ := ih
      let frame : Forest (Hints.handler (effect := effect) (table := table) (families := families) required .nil) := .handler .nil
      exact ⟨_, _, front.append frame, .handler (source.append frame),
        scopes.trans (SourceDependencyChecks.scope_append_assoc frontScope (.handler effect table families .nil) scope).symm,
        annotations.trans (SourcePlannedRecomposition.hints_append_assoc frontHints (Hints.handler (effect := effect) (table := table) (families := families) required .nil) hints).symm,
        plans.trans (SourceScheduledRecomposition.forest_append_assoc front frame forest).symm⟩
  | @cleanup bodyDep body world needs callbackDep callback scope hints forest requirement atWorld atScope atHints atForest next ih =>
      obtain ⟨frontScope, frontHints, front, source, scopes, annotations, plans⟩ := ih
      let frame : Forest (Hints.cleanup (needs := needs) (callback := callbackDep) .nil) := .cleanup callback .nil
      exact ⟨_, _, front.append frame, .cleanup (source.append frame),
        scopes.trans (SourceDependencyChecks.scope_append_assoc frontScope (.cleanup needs callbackDep .nil) scope).symm,
        annotations.trans (SourcePlannedRecomposition.hints_append_assoc frontHints (Hints.cleanup (needs := needs) (callback := callbackDep) .nil) hints).symm,
        plans.trans (SourceScheduledRecomposition.forest_append_assoc front frame forest).symm⟩
  | @callback callbackDep callback world scope hints forest requirement atWorld atScope atHints atForest needs bodyDep body next ih =>
      obtain ⟨frontScope, frontHints, front, source, scopes, annotations, plans⟩ := ih
      let frame : Forest (Hints.running .nil) := .running .nil
      exact ⟨_, _, front.append frame, .callback (source.append frame),
        scopes.trans (SourceDependencyChecks.scope_append_assoc frontScope (.running .nil) scope).symm,
        annotations.trans (SourcePlannedRecomposition.hints_append_assoc frontHints (Hints.running .nil) hints).symm,
        plans.trans (SourceScheduledRecomposition.forest_append_assoc front frame forest).symm⟩
  | @resource world identity family body scope hints forest requirement atWorld atScope atHints atForest fresh next ih =>
      obtain ⟨frontScope, frontHints, front, source, scopes, annotations, plans⟩ := ih
      let frame : Forest (Hints.cell (identity := identity) .nil) := .cell .nil
      exact ⟨_, _, front.append frame, .resource fresh (source.append frame),
        scopes.trans (SourceDependencyChecks.scope_append_assoc frontScope (.cell identity .nil) scope).symm,
        annotations.trans (SourcePlannedRecomposition.hints_append_assoc frontHints (Hints.cell (identity := identity) .nil) hints).symm,
        plans.trans (SourceScheduledRecomposition.forest_append_assoc front frame forest).symm⟩

/-- Source-local templates are necessary and sufficient for the existing
site checks at any receiving continuation. This is a compiler interface, not
an opaque constructor premise for a consuming declaration recipe. -/
theorem satisfied_iff_templates {plan : Plan dependencies} {hints : Hints scope} {forest : Forest hints} :
    Satisfied outward actions phases world plan forest ↔
      ∀ {requirement atWorld frontScope} {frontHints : Hints frontScope} {front : Forest frontHints},
        Site plan world .nil requirement atWorld front →
        Check outward actions phases atWorld (front.append forest) requirement := by
  constructor
  · intro checked requirement atWorld frontScope frontHints front source
    exact checked (source.append forest)
  · intro supplied requirement atWorld atScope atHints atForest site
    obtain ⟨frontScope, frontHints, front, source, scopes, annotations, plans⟩ := site.factor
    exact (SourceScheduledRecomposition.predicate_congr scopes annotations plans
      (fun receiving => Check outward actions phases atWorld receiving requirement)).mpr (supplied source)

/-- Compile the whole existing plan grammar from its source-local obligations;
no actual capture or whole target check is stored in the template syntax. -/
theorem compile_from_templates (plan : Plan dependencies) (world : List Nat)
    {hints : Hints scope} (forest : Forest hints)
    (supplied : ∀ {requirement atWorld frontScope} {frontHints : Hints frontScope} {front : Forest frontHints},
      Site plan world .nil requirement atWorld front →
      Check outward actions phases atWorld (front.append forest) requirement) :
    Local outward actions phases world plan forest :=
  compile plan world forest (satisfied_iff_templates.mpr supplied)

/-- A source-derived resume site checks the original saved continuation and
waiting tail. Only its caller prefix and resource world vary with the site. -/
theorem Site.resume_requirements {plan : Plan dependencies} {hints : Hints scope} {forest : Forest hints}
    {atHints : Hints atScope} {atForest : Forest atHints}
    {frontHints : Hints frontScope} {front : Forest frontHints}
    {savedHints : Hints savedScope} {saved : Forest savedHints}
    {waitingHints : Hints waitingScope} {waiting : Forest waitingHints}
    (site : Site plan world forest (.resume owner) atWorld atForest)
    (cut : OwnerCut owner forest front saved waiting) :
    ∃ atFrontScope, ∃ atFrontHints : Hints atFrontScope, ∃ atFront : Forest atFrontHints,
      OwnerCut owner atForest atFront saved waiting ∧
      (Check outward actions phases atWorld atForest (.resume owner) ↔
        Resume actions phases owner atHints
          (Selection.resumed owner ⟨⟨atFrontScope, savedScope, waitingScope⟩, atFrontHints, savedHints, waitingHints⟩) ∧
        Pending outward actions (spend phases owner) atWorld saved (atFront.append (.spent (owner := owner) waiting)) ∧
        Pending outward actions (spend phases owner) atWorld atFront (.spent (owner := owner) waiting) ∧
        Pending outward actions (spend phases owner) atWorld waiting .nil) := by
  obtain ⟨atFrontScope, atFrontHints, atFront, atCut⟩ := site.owner_cut cut
  exact ⟨atFrontScope, atFrontHints, atFront, atCut,
    resume_iff.trans (SourceScheduledScopedInvocations.resume_iff atCut)⟩

/-- A source-derived dispose site checks the original saved continuation and
waiting tail. Only its caller prefix and resource world vary with the site. -/
theorem Site.dispose_requirements {plan : Plan dependencies} {hints : Hints scope} {forest : Forest hints}
    {atHints : Hints atScope} {atForest : Forest atHints}
    {frontHints : Hints frontScope} {front : Forest frontHints}
    {savedHints : Hints savedScope} {saved : Forest savedHints}
    {waitingHints : Hints waitingScope} {waiting : Forest waitingHints}
    (site : Site plan world forest (.dispose owner) atWorld atForest)
    (cut : OwnerCut owner forest front saved waiting) :
    ∃ atFrontScope, ∃ atFrontHints : Hints atFrontScope, ∃ atFront : Forest atFrontHints,
      OwnerCut owner atForest atFront saved waiting ∧
      (Check outward actions phases atWorld atForest (.dispose owner) ↔
        Dispose outward actions phases owner atHints
          (Selection.disposed owner ⟨⟨atFrontScope, savedScope, waitingScope⟩, atFrontHints, savedHints, waitingHints⟩) ∧
        Pending outward actions (spend phases owner) atWorld saved.forClosing (.running (atFront.append (.spent (owner := owner) waiting))) ∧
        Pending outward actions (spend phases owner) atWorld atFront (.spent (owner := owner) waiting) ∧
        Pending outward actions (spend phases owner) atWorld waiting .nil) := by
  obtain ⟨atFrontScope, atFrontHints, atFront, atCut⟩ := site.owner_cut cut
  exact ⟨atFrontScope, atFrontHints, atFront, atCut,
    dispose_iff.trans (SourceScheduledScopedInvocations.dispose_iff atCut)⟩

end Ash.OneShot.SourceScheduledRequirements

#print axioms Ash.OneShot.SourceScheduledRequirements.request_iff
#print axioms Ash.OneShot.SourceScheduledRequirements.resume_iff
#print axioms Ash.OneShot.SourceScheduledRequirements.dispose_iff
#print axioms Ash.OneShot.SourceScheduledRequirements.necessary
#print axioms Ash.OneShot.SourceScheduledRequirements.compile
#print axioms Ash.OneShot.SourceScheduledRequirements.satisfied_iff

#print axioms Ash.OneShot.SourceScheduledRequirements.satisfied_sequence

#print axioms Ash.OneShot.SourceScheduledRequirements.satisfied_choice

#print axioms Ash.OneShot.SourceScheduledRequirements.satisfied_handler

#print axioms Ash.OneShot.SourceScheduledRequirements.satisfied_cleanup

#print axioms Ash.OneShot.SourceScheduledRequirements.satisfied_resource

#print axioms Ash.OneShot.SourceScheduledRequirements.Site.owner_cut
#print axioms Ash.OneShot.SourceScheduledRequirements.Site.resume_requirements
#print axioms Ash.OneShot.SourceScheduledRequirements.Site.dispose_requirements

#print axioms Ash.OneShot.SourceScheduledRequirements.Context.owner_cut

#print axioms Ash.OneShot.SourceScheduledRequirements.Site.factor

#print axioms Ash.OneShot.SourceScheduledRequirements.satisfied_iff_templates

#print axioms Ash.OneShot.SourceScheduledRequirements.compile_from_templates
