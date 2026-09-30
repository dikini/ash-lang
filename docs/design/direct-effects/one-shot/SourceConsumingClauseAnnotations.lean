import SourceScheduledCaptureAnnotations
import SourceScheduledInterfaceWorld
import SourceConsumingBoundData

/-! Syntax-directed annotation generation for consuming clauses. The declaration
retains a finite syntax derivation before any captured forest is known. Its
interpretation constructs owner cuts under caller handlers and cleanup frames;
independent checks account for the actual retained source after consumption. -/
namespace Ash.OneShot.SourceConsumingClauseAnnotations
open SourceDeclarationPlans (Plan ModePlans ClausePlans)
open SourcePlanSignatures (signature)
open SourceContextualHints (Hints checkRequirements)
open SourceDependencyCapture (Scope)
open SourceRetainedPlans (Forest)
open SourceScheduledCapabilityAnnotations (Code Retained DeclarationPolicy)
open SourceScheduledNeutral (OwnerCut)
open SourceScheduledRetainedInterfaces (Interfaces)
open SourceScheduledAdaptationCompilation (RequestFootprint)
open SourceScheduledSourceInterfaces (Declared)

section
variable [declarations : DeclarationPolicy]

/-- Source data contain no saved continuation, owner-cut witness, schedule or
successful body check. Prefixes and callbacks have operation interfaces;
continuation consumption is represented separately at the leaves. Handler
installation records the exact bounds for both offered modes. -/
inductive Body [declarations : DeclarationPolicy] : List Nat → Nat →
    {dependencies : SourceDependencyAnnotations.Dependencies} → Plan dependencies → Type where
  | resume : Body world owner (.invoke (key := ⟨owner, .resume⟩))
  | dispose : Body world owner (.invoke (key := ⟨owner, .dispose⟩))
  | sequence (required : List SourceContextualHints.Requirement)
      (footprint : RequestFootprint before required) (declared : Declared world (signature before))
      (rest : Body world owner after) : Body world owner (.sequence before after)
  | choice : Body world owner first → Body world owner second → Body world owner (.choice first second)
  | handler {plans : ClausePlans clauses families}
      (bounds : ClauseBounds plans) (admitted : declarations.accepts required plans) (body : Body world owner code) :
      Body world owner (.handler (effect := effect) (table := table) required plans code)
  | cleanup (required : List SourceContextualHints.Requirement)
      (footprint : RequestFootprint callback required) (declared : Declared world (signature callback))
      (body : Body world owner code) : Body world owner (.cleanup (needs := needs) callback code)
  | resource (body : ∀ identity, identity ∉ world → Body (world ++ [identity]) owner (code identity)) :
      Body world owner (.resource code)

/-- Every offered clause has a source derivation for its bound continuation.
This data precedes capture and contains no receiving-context check. -/
inductive Modes [declarations : DeclarationPolicy] (world : List Nat) :
    {family : Option (Nat → SourceDependencyAnnotations.Dependencies)} → ModePlans family → Type where
  | unavailable : Modes world .unavailable
  | available (bodies : ∀ owner, Body world owner (plans owner)) : Modes world (.available plans)

inductive Declarations [declarations : DeclarationPolicy] (world : List Nat) :
    {clauses : ScopedExpressions.Clauses} → {families : SourceDependencyAnnotations.ClauseDependencies} →
      ClausePlans clauses families → Type where
  | nil : Declarations world .nil
  | cons : Modes world ordinary → Modes world protectedMode → Declarations world rest →
      Declarations world (.cons (body := body) ordinary protectedMode rest)

/-- Retain the same clause derivation when intervening evaluation allocates
resources. The resource case reuses the existing fresh-world inclusion law. -/
def Body.world_weaken {plan : Plan dependencies} (body : Body world owner plan)
    (larger : world ⊆ next) : Body next owner plan :=
  match body with
  | .resume => .resume
  | .dispose => .dispose
  | .sequence required footprint declared rest =>
      .sequence required footprint (declared.world_weaken larger) (rest.world_weaken larger)
  | .choice first second => .choice (first.world_weaken larger) (second.world_weaken larger)
  | .handler bounds admitted body => .handler bounds admitted (body.world_weaken larger)
  | .cleanup required footprint declared body =>
      .cleanup required footprint (declared.world_weaken larger) (body.world_weaken larger)
  | .resource body =>
      .resource (fun identity fresh => (body identity (fun member => fresh (larger member))).world_weaken
        (ScopedExpressions.append_subset larger (List.Subset.refl _)))

def Modes.world_weaken {plans : ModePlans family} (modes : Modes world plans)
    (larger : world ⊆ next) : Modes next plans :=
  match modes with
  | .unavailable => .unavailable
  | .available bodies => .available (fun owner => (bodies owner).world_weaken larger)

def Declarations.world_weaken {plans : ClausePlans clauses families} (annotated : Declarations world plans)
    (larger : world ⊆ next) : Declarations next plans :=
  match annotated with
  | .nil => .nil
  | .cons ordinary protectedMode rest =>
      .cons (ordinary.world_weaken larger) (protectedMode.world_weaken larger) (rest.world_weaken larger)

/-- Selection reuses the established clause-order relation, including both
ordinary and protected modes. The selected body needs no old consuming recipe. -/
theorem Declarations.selected {plans : ClausePlans clauses families}
    (annotated : Declarations world plans)
    (selected : SourcePlannedRecipeDeclarations.Selected operation held plans parameter binder code bodies) :
    Nonempty (Body world owner (bodies owner)) := by
  induction selected with
  | ordinary => cases annotated with
    | cons ordinary protectedMode rest => cases ordinary with
      | available bodies => exact ⟨bodies owner⟩
  | protectedMode => cases annotated with
    | cons ordinary protectedMode rest => cases protectedMode with
      | available bodies => exact ⟨bodies owner⟩
  | pass different next ih => cases annotated with
    | cons ordinary protectedMode rest => exact ih rest

/-- Repeated operations add repeated syntax without spending continuation
rights. A single sequencing constructor covers every prefix. -/
def Body.requests {plan : Plan dependencies}
    (requests : List SourceContextualHints.Requirement) (body : Body world owner plan) :
    Body world owner (SourceScheduledClauseHandlers.requestPrefix requests plan) :=
  match requests with
  | [] => body
  | request :: remaining =>
      .sequence [request] (.sequence .pure .request) (.sequence .pure .request)
        (body.requests remaining)

/-- Instantiate the same source derivation at any actual capture and caller
prefix. Recursive constructors generate the owner cut and caller annotation. -/
def Body.annotate {plan : Plan dependencies} (body : Body world owner plan)
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    {saved : Forest savedHints} {tail : Forest tailHints}
    (cut : OwnerCut owner whole front saved tail)
    (inside : Interfaces world saved) (closing : Interfaces world saved.forClosing)
    (before : Interfaces world front) (after : Interfaces world tail) : Code world plan whole :=
  match body with
  | .resume => .resume cut (.operations inside) (.operations before) (.operations after)
  | .dispose => .dispose cut (.operations closing) (.operations before) (.operations after)
  | .sequence required footprint declared rest =>
      .sequence (.operations required footprint declared) (rest.annotate cut inside closing before after)
  | .choice first second =>
      .choice (first.annotate cut inside closing before after) (second.annotate cut inside closing before after)
  | .handler bounds admitted body =>
      .handler admitted (body.annotate (.handler cut) inside closing (.handler front before) after) (some bounds)
  | .cleanup required footprint declared body =>
      .cleanup (body.annotate (.cleanup cut) inside closing (.cleanup front required footprint declared before) after)
        (.operations required footprint declared)
  | .resource body =>
      .resource (fun identity fresh => (body identity fresh).annotate (.cell cut)
        (inside.world_weaken (List.subset_append_left _ _))
        (closing.world_weaken (List.subset_append_left _ _))
        (.cell (before.world_weaken (List.subset_append_left _ _)))
        (after.world_weaken (List.subset_append_left _ _)))

private def planDependencies {dependencies : SourceDependencyAnnotations.Dependencies}
    (_ : Plan dependencies) := dependencies

/-- Separate structural validation. Operations may repeat; their interface
checks availability. A continuation leaf also requires an available owner and
its own right, and checks the restored or closing source in its actual order. -/
def Body.Check {plan : Plan dependencies} (body : Body world owner plan)
    (outward : List Instance) (actions : Syntax.UsageTickets) (phases : OwnerPhaseTransitions.Phases)
    (receiving : Scope)
    {frontHints : Hints frontScope} {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {front : Forest frontHints} {saved : Forest savedHints} {tail : Forest tailHints}
    (inside : Interfaces world saved) (closing : Interfaces world saved.forClosing)
    (before : Interfaces world front) (after : Interfaces world tail) : Prop :=
  match body with
  | .resume =>
      (actions owner).any (fun rights => rights.resume) = true ∧ phases owner = .available ∧
      inside.check (frontScope.append (.spent owner tailScope)) = true ∧
      before.check (.spent owner tailScope) = true ∧ after.check .nil = true
  | .dispose =>
      (actions owner).any (fun rights => rights.dispose) = true ∧ phases owner = .available ∧
      savedScope.held = false ∧ SourceDependencyCapture.checkClosing outward savedScope.shape [] [] = true ∧
      closing.check (.running (frontScope.append (.spent owner tailScope))) = true ∧
      before.check (.spent owner tailScope) = true ∧ after.check .nil = true
  | .sequence (after := next) required _ _ rest =>
      checkRequirements (.plain (planDependencies next) receiving) required = true ∧
      rest.Check outward actions phases receiving inside closing before after
  | .choice first second =>
      first.Check outward actions phases receiving inside closing before after ∧
      second.Check outward actions phases receiving inside closing before after
  | .handler (effect := effect) (table := table) (families := families) (required := required) _ _ body =>
      checkRequirements receiving required = true ∧
      body.Check outward actions phases (.handler effect table families receiving)
        inside closing (.handler (effect := effect) (table := table) (families := families) (required := required) front before) after
  | .cleanup (needs := needs) (callback := callback) required footprint declared body =>
      body.Check outward actions phases (.cleanup needs (planDependencies callback) receiving)
        inside closing (.cleanup (needs := needs) front required footprint declared before) after ∧
      checkRequirements (.running receiving) required = true
  | .resource body => ∀ identity fresh,
      (body identity fresh).Check outward actions phases (.cell identity receiving)
        (inside.world_weaken (List.subset_append_left _ _))
        (closing.world_weaken (List.subset_append_left _ _))
        (.cell (identity := identity) (before.world_weaken (List.subset_append_left _ _)))
        (after.world_weaken (List.subset_append_left _ _))

/-- Every branch consumes this owner, so successful admission requires it
still to be available, regardless of the number of operation requests. -/
theorem Body.check_available {plan : Plan dependencies} (body : Body world owner plan)
    {frontHints : Hints frontScope} {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {front : Forest frontHints} {saved : Forest savedHints} {tail : Forest tailHints}
    {inside : Interfaces world saved} {closing : Interfaces world saved.forClosing}
    {before : Interfaces world front} {after : Interfaces world tail}
    (checked : body.Check outward actions phases receiving inside closing before after) :
    phases owner = .available := by
  induction body generalizing receiving frontScope with
  | resume | dispose => exact checked.2.1
  | sequence required footprint declared rest ih => exact ih checked.2
  | choice first second ihFirst ihSecond => exact ihFirst checked.1
  | handler bounds admitted body ih => exact ih checked.2
  | cleanup required footprint declared body ih => exact ih checked.1
  | resource body ih =>
      obtain ⟨identity, fresh⟩ := ScopedTyping.fresh_world_name _
      exact ih identity fresh (checked identity fresh)

/-- Resource allocation preserves an already admitted consuming derivation
and every retained operation interface. Only freshness ranges become smaller. -/
theorem Body.check_world_weaken {plan : Plan dependencies} (body : Body world owner plan)
    (larger : world ⊆ next)
    {frontHints : Hints frontScope} {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {front : Forest frontHints} {saved : Forest savedHints} {tail : Forest tailHints}
    {inside : Interfaces world saved} {closing : Interfaces world saved.forClosing}
    {before : Interfaces world front} {after : Interfaces world tail}
    (checked : body.Check outward actions phases receiving inside closing before after) :
    (body.world_weaken larger).Check outward actions phases receiving
      (inside.world_weaken larger) (closing.world_weaken larger)
      (before.world_weaken larger) (after.world_weaken larger) := by
  induction body generalizing receiving frontScope next with
  | resume | dispose =>
      simpa only [Body.world_weaken, Body.Check, Interfaces.check_world_weaken] using checked
  | sequence required footprint declared rest ih => exact ⟨checked.1, ih larger checked.2⟩
  | choice first second ihFirst ihSecond => exact ⟨ihFirst larger checked.1, ihSecond larger checked.2⟩
  | handler bounds admitted body ih => exact ⟨checked.1, ih larger checked.2⟩
  | cleanup required footprint declared body ih => exact ⟨ih larger checked.1, checked.2⟩
  | resource body ih =>
      intro identity fresh
      have oldFresh := fun member => fresh (larger member)
      have retained := ih identity oldFresh
        (ScopedExpressions.append_subset larger (List.Subset.refl [identity])) (checked identity oldFresh)
      simpa only [Body.world_weaken, Body.Check, Interfaces.world_weaken, Interfaces.world_weaken_trans] using retained

/-- Generation preserves exactly the independent checks, including rejection.
No successful Local/Pending check is an input to either side. -/
theorem Body.annotate_valid {plan : Plan dependencies} (body : Body world owner plan)
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    {saved : Forest savedHints} {tail : Forest tailHints}
    (cut : OwnerCut owner whole front saved tail)
    (inside : Interfaces world saved) (closing : Interfaces world saved.forClosing)
    (before : Interfaces world front) (after : Interfaces world tail) :
    (body.annotate cut inside closing before after).Valid outward actions phases ↔
      body.Check outward actions phases wholeScope inside closing before after := by
  induction body generalizing wholeScope frontScope with
  | resume | dispose => rfl
  | sequence required footprint declared rest ih =>
      exact and_congr Iff.rfl (ih cut inside closing before after)
  | choice first second ihFirst ihSecond =>
      exact and_congr (ihFirst cut inside closing before after) (ihSecond cut inside closing before after)
  | handler bounds admitted body ih =>
      exact and_congr Iff.rfl (ih (.handler cut) inside closing (.handler _ before) after)
  | cleanup required footprint declared body ih =>
      exact and_congr (ih (.cleanup cut) inside closing (.cleanup _ required footprint declared before) after) Iff.rfl
  | resource body ih =>
      apply forall_congr'
      intro identity
      apply forall_congr'
      intro fresh
      exact ih identity fresh (.cell cut)
        (inside.world_weaken (List.subset_append_left _ _))
        (closing.world_weaken (List.subset_append_left _ _))
        (.cell (before.world_weaken (List.subset_append_left _ _)))
        (after.world_weaken (List.subset_append_left _ _))

/-- Clause instantiation starts at the actual fresh live-owner boundary.
The existing annotation compiler proves scheduling by structural induction. -/
theorem Body.compile [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    (laws : SourceScheduledCapabilityAnnotations.DeclarationLaws declarations admission certification outward)
    {plan : Plan dependencies} (body : Body world owner plan)
    {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {saved : Forest savedHints} {tail : Forest tailHints}
    (inside : Interfaces world saved) (closing : Interfaces world saved.forClosing)
    (after : Interfaces world tail)
    (checked : body.Check outward actions phases (.live owner savedScope tailScope) inside closing .nil after) :
    SourceScheduledChecks.Local outward actions phases world plan (.live (owner := owner) saved tail) :=
  (body.annotate .hit inside closing .nil after).compile_with laws
    ((body.annotate_valid .hit inside closing .nil after).mpr checked)

end

namespace Examples
open SourceScheduledClauseHandlers.Examples
  (bodies outerPlans saved code noActions inner_declarations requests)

/-- This declaration is built before knowing any saved continuation. -/
def body (owner : Nat) : Body [] owner (bodies owner) :=
  .handler (.cons (.available ⟨[], []⟩) (.available ⟨[], []⟩) .nil) inner_declarations ((Body.sequence (before := Plan.pure) [] .pure .pure .resume).requests requests)

def declarations : Declarations [] outerPlans :=
  .cons (.available body) (.available body) .nil

/-- The new syntax derivation constructs the previous hand-written annotation. -/
theorem generated_annotation :
    (body 19).annotate (.hit (saved := saved) (tail := .nil)) (.handler .nil .nil) .nil .nil .nil =
      SourceScheduledCaptureAnnotations.Examples.bodyAnnotation := rfl

/-- Validation is generated from primitive checks at this actual capture. -/
theorem checked :
    (body 19).Check [] (noActions.insert 19 code.requiredActions)
      (OwnerPhaseTransitions.introduce OwnerPhaseTransitions.empty 19)
      (.live 19 (.handler SourceDependencyCapture.Examples.effectE
        SourceDependencyCapture.Examples.resumeTable
        SourceScheduledClauseHandlers.Examples.outerFamilies .nil) .nil)
      (show Interfaces [] saved from .handler .nil .nil) .nil .nil .nil := by
  exact ⟨rfl, ⟨rfl, ⟨rfl, ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩⟩⟩⟩

/-- The generated annotation supplies the same concrete capture admission. -/
theorem capture_valid :
    SourceScheduledCaptureAnnotations.Examples.admission.Valid [] noActions OwnerPhaseTransitions.empty := by
  change ((body 19).annotate (.hit (saved := saved) (tail := .nil))
    (.handler .nil .nil) .nil .nil .nil).Valid [] (noActions.insert 19 code.requiredActions)
      (OwnerPhaseTransitions.introduce OwnerPhaseTransitions.empty 19)
  exact ((body 19).annotate_valid .hit (.handler .nil .nil) .nil .nil .nil).mpr checked

/-- Effectful cleanup surrounds the resumption under the newly installed F
handler. Its callback must also be supplied in the protected running scope. -/
def cleanupPlan (owner : Nat) := Plan.handler
  (effect := SourceDependencyCapture.Examples.effectF)
  (table := SourceDependencyCapture.Examples.resumeTable) []
  SourceScheduledClauseHandlers.Examples.innerPlans
  (.cleanup (needs := [])
    (.request (effect := SourceDependencyCapture.Examples.effectF) (operation := 0))
    (.sequence .pure (.invoke (key := ⟨owner, .resume⟩))))

def cleanupBody (owner : Nat) : Body [] owner (cleanupPlan owner) :=
  .handler (.cons (.available ⟨[], []⟩) (.available ⟨[], []⟩) .nil) inner_declarations
    (.cleanup [(SourceDependencyCapture.Examples.effectF, 0)] .request .request
      (.sequence [] .pure .pure .resume))

theorem cleanup_checked :
    (cleanupBody 19).Check [] (noActions.insert 19 code.requiredActions)
      (OwnerPhaseTransitions.introduce OwnerPhaseTransitions.empty 19)
      (.live 19 (.handler SourceDependencyCapture.Examples.effectE
        SourceDependencyCapture.Examples.resumeTable
        SourceScheduledClauseHandlers.Examples.outerFamilies .nil) .nil)
      (show Interfaces [] saved from .handler .nil .nil) .nil .nil .nil := by
  exact ⟨rfl, ⟨⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩, rfl⟩⟩

/-- A resource introduced inside the clause supplies an effectful cleanup
callback around resumption. Its identity is fresh in each instantiated world. -/
def resourcePlan (owner : Nat) := Plan.resource (fun identity =>
  .cleanup (needs := []) (.request (effect := .cell identity) (operation := 0))
    (.sequence .pure (.invoke (key := ⟨owner, .resume⟩))))

def resourceBody (owner : Nat) : Body [] owner (resourcePlan owner) :=
  .resource (fun identity _ => .cleanup [(.cell identity, 0)] .request .request
    (.sequence [] .pure .pure .resume))

theorem resource_checked :
    (resourceBody 19).Check [] (noActions.insert 19 code.requiredActions)
      (OwnerPhaseTransitions.introduce OwnerPhaseTransitions.empty 19)
      (.live 19 (.handler SourceDependencyCapture.Examples.effectE
        SourceDependencyCapture.Examples.resumeTable
        SourceScheduledClauseHandlers.Examples.outerFamilies .nil) .nil)
      (show Interfaces [] saved from .handler .nil .nil) .nil .nil .nil := by
  intro identity fresh
  refine ⟨⟨rfl, ⟨rfl, rfl, rfl, ?_, rfl⟩⟩, ?_⟩
  · change (checkRequirements (.running (.cell identity (.spent 19 .nil))) [(.cell identity, 0)] && true) = true
    simp [SourceContextualHints.checkRequirements, SourceContextualHints.checkCapability,
      SourceDependencyCapture.select, SourceDependencyCapture.Selection.prepend]
  · change checkRequirements (.running (.cell identity (.live 19 _ .nil))) [(.cell identity, 0)] = true
    simp [SourceContextualHints.checkRequirements, SourceContextualHints.checkCapability,
      SourceDependencyCapture.select, SourceDependencyCapture.Selection.prepend]

/-- The source-generated resource annotation reaches the existing scheduler. -/
theorem resource_compiled :
    SourceScheduledChecks.Local [] (noActions.insert 19 code.requiredActions)
      (OwnerPhaseTransitions.introduce OwnerPhaseTransitions.empty 19) []
      (resourcePlan 19) (.live (owner := 19) saved .nil) :=
  (resourceBody 19).compile (SourceScheduledCapabilityAnnotations.recipeLaws [])
    (.handler .nil .nil) .nil .nil resource_checked

/-- Repeating an operation does not grant a second use of its continuation. -/
theorem consumed_rejected :
    ¬ (body 19).Check [] (noActions.insert 19 code.requiredActions) OwnerPhaseTransitions.empty
      (.live 19 (.handler SourceDependencyCapture.Examples.effectE
        SourceDependencyCapture.Examples.resumeTable
        SourceScheduledClauseHandlers.Examples.outerFamilies .nil) .nil)
      (show Interfaces [] saved from .handler .nil .nil) .nil .nil .nil := by
  intro checked
  have impossible := (body 19).check_available checked
  cases impossible

end Examples

end Ash.OneShot.SourceConsumingClauseAnnotations

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Body.annotate_valid
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Body.compile

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Declarations.selected
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Examples.generated_annotation
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Examples.checked
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Examples.capture_valid

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Body.check_available
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Examples.cleanup_checked
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Examples.consumed_rejected

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Body.check_world_weaken

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Examples.resource_checked
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Examples.resource_compiled
