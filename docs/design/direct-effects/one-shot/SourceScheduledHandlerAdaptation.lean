import SourceScheduledHandlerTransport
import SourceScheduledHandlerInvocations
import SourceDeclarationPolicyTransport

/-! Structural adaptation of existing source derivations. Every expression
and retained-frame rule refers to actual stored plans. Recursive premises are
adaptation derivations, never functions returning a target Local/Pending proof. -/
namespace Ash.OneShot.SourceScheduledHandlerAdaptation
open ScopedExpressions ProtectionContracts
open SourceDependencyCapture (Scope CaptureGuard)
open SourceContextualHints (Hints checkRequirements)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open SourceScheduledInterpretationInsertion (Interpretation Insertion Split)
open SourceScheduledChecks (Local Pending)
open SourceScheduledClosingCallbacks (Callbacks)
open SourceDependencyOwners (PendingWithin owners)

mutual
inductive Adapt (outward : List Instance) (actions : Syntax.UsageTickets) :
    Interpretation → OwnerPhaseTransitions.Phases → List Nat →
    {dependencies : SourceDependencyAnnotations.Dependencies} →
    {first second : Scope} → {beforeHints : Hints first} → {afterHints : Hints second} →
    Plan dependencies → Forest beforeHints → Forest afterHints → Prop where
  | same : Adapt outward actions frame phases world plan forest forest
  | pure : Adapt outward actions frame phases world .pure before after
  | capability {afterHints : Hints second} {after : Forest afterHints}
      (supplied : SourceContextualClauses.RequestCapability effect operation second) :
      Adapt outward actions frame phases world (.request (effect := effect) (operation := operation)) before after
  | fresh {afterHints : Hints second} {after : Forest afterHints}
      {savedHints : Hints captured} {waitingHints : Hints tail}
      {saved : Forest savedHints} {waiting : Forest waitingHints}
      (selected : SourceScheduledNeutral.Cut effect operation contract modes after saved waiting)
      (guarded : CaptureGuard outward second effect operation)
      (bounded : contract.dispose = true → PendingWithin world (owners captured) captured)
      (callbacks : contract.dispose = true → Callbacks outward actions phases world saved (.running waiting)) :
      Adapt outward actions frame phases world (.request (effect := effect) (operation := operation)) before after
  | request {beforeHints : Hints first} {afterHints : Hints second}
      {before : Forest beforeHints} {after : Forest afterHints}
      (oldCut : SourceScheduledNeutral.Cut effect operation contract modes before saved waiting)
      (nextCut : SourceScheduledNeutral.Cut effect operation contract modes after nextSaved nextWaiting)
      (pieces : Split (.handler installed table families required) saved waiting nextSaved nextWaiting)
      (guarded : CaptureGuard outward second effect operation)
      (closing : contract.dispose = true → Retained outward actions (.handler installed table families required) phases world
        saved.forClosing (.running waiting) nextSaved.forClosing (.running nextWaiting)) :
      Adapt outward actions (.handler installed table families required) phases world
        (.request (effect := effect) (operation := operation)) before after
  | resume {frontHints : Hints frontScope} {savedHints : Hints savedScope} {tailHints : Hints tailScope}
      {nextFrontHints : Hints nextFrontScope} {nextTailHints : Hints nextTailScope}
      {front : Forest frontHints} {saved : Forest savedHints} {tail : Forest tailHints}
      {nextFront : Forest nextFrontHints} {nextTail : Forest nextTailHints}
      (oldCut : SourceScheduledNeutral.OwnerCut owner before front saved tail)
      (nextCut : SourceScheduledNeutral.OwnerCut owner after nextFront saved nextTail)
      (pieces : Split (.handler effect table families required) front tail nextFront nextTail)
      (restored : Retained outward actions (.handler effect table families required) (OwnerPhaseTransitions.spend phases owner) world
        (saved.append (front.append (.spent (owner := owner) tail))) .nil
        (saved.append (nextFront.append (.spent (owner := owner) nextTail))) .nil) :
      Adapt outward actions (.handler effect table families required) phases world (.invoke (key := ⟨owner, .resume⟩)) before after
  | dispose {frontHints : Hints frontScope} {savedHints : Hints savedScope} {tailHints : Hints tailScope}
      {nextFrontHints : Hints nextFrontScope} {nextTailHints : Hints nextTailScope}
      {front : Forest frontHints} {saved : Forest savedHints} {tail : Forest tailHints}
      {nextFront : Forest nextFrontHints} {nextTail : Forest nextTailHints}
      (oldCut : SourceScheduledNeutral.OwnerCut owner before front saved tail)
      (nextCut : SourceScheduledNeutral.OwnerCut owner after nextFront saved nextTail)
      (pieces : Split (.handler effect table families required) front tail nextFront nextTail)
      (scheduled : Retained outward actions (.handler effect table families required) (OwnerPhaseTransitions.spend phases owner) world
        (saved.forClosing.append (.running (front.append (.spent (owner := owner) tail)))) .nil
        (saved.forClosing.append (.running (nextFront.append (.spent (owner := owner) nextTail)))) .nil) :
      Adapt outward actions (.handler effect table families required) phases world (.invoke (key := ⟨owner, .dispose⟩)) before after
  | sequence {nextPlan : Plan nextDependencies}
      (first : Adapt outward actions frame phases world plan (.plain nextPlan before) (.plain nextPlan after))
      (second : Adapt outward actions frame phases world nextPlan before after) :
      Adapt outward actions frame phases world (.sequence plan nextPlan) before after
  | choice : Adapt outward actions frame phases world first before after →
      Adapt outward actions frame phases world second before after →
      Adapt outward actions frame phases world (.choice first second) before after
  | handler {plans : SourceDeclarationPlans.ClausePlans clauses families} {afterHints : Hints second} {after : Forest afterHints}
      (supplied : checkRequirements second required = true)
      (body : Adapt outward actions frame phases world code
        (.handler (effect := effect) (table := table) (families := families) (required := required) before)
        (.handler (effect := effect) (table := table) (families := families) (required := required) after)) :
      Adapt outward actions frame phases world (.handler (effect := effect) (table := table) required plans code) before after
  | cleanup {callback : Plan callbackDependencies}
      (body : Adapt outward actions frame phases world code (.cleanup (needs := needs) callback before) (.cleanup (needs := needs) callback after))
      (completion : Adapt outward actions frame phases world callback (.running before) (.running after)) :
      Adapt outward actions frame phases world (.cleanup (needs := needs) callback code) before after
  | resource (body : ∀ identity, identity ∉ world → Adapt outward actions frame phases (world ++ [identity])
      (code identity) (.cell (identity := identity) before) (.cell (identity := identity) after)) :
      Adapt outward actions frame phases world (.resource code) before after

inductive Retained (outward : List Instance) (actions : Syntax.UsageTickets) :
    Interpretation → OwnerPhaseTransitions.Phases → List Nat →
    {first outside second nextOutside : Scope} →
    {beforeHints : Hints first} → {outsideHints : Hints outside} →
    {afterHints : Hints second} → {nextOutsideHints : Hints nextOutside} →
    Forest beforeHints → Forest outsideHints → Forest afterHints → Forest nextOutsideHints → Prop where
  | same : Retained outward actions frame phases world forest outside forest outside
  | nil : Retained outward actions frame phases world .nil outside .nil nextOutside
  | install {hints : Hints scope} {forest : Forest hints} {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
      (supplied : checkRequirements (scope.append outsideScope) required = true) :
      Retained outward actions (.handler effect table families required) phases world forest outside
        (.handler (effect := effect) (table := table) (families := families) (required := required) forest) outside
  | plain {plan : Plan dependencies}
      (code : Adapt outward actions frame phases world plan (rest.append outside) (next.append nextOutside))
      (tail : Retained outward actions frame phases world rest outside next nextOutside) :
      Retained outward actions frame phases world (.plain plan rest) outside (.plain plan next) nextOutside
  | handler {nextHints : Hints nextScope} {next : Forest nextHints}
      {nextOutsideHints : Hints nextOutsideScope} {nextOutside : Forest nextOutsideHints}
      (supplied : checkRequirements (nextScope.append nextOutsideScope) required = true)
      (tail : Retained outward actions frame phases world rest outside next nextOutside) :
      Retained outward actions frame phases world
        (.handler (effect := effect) (table := table) (families := families) (required := required) rest) outside
        (.handler (effect := effect) (table := table) (families := families) (required := required) next) nextOutside
  | cell : Retained outward actions frame phases world rest outside next nextOutside →
      Retained outward actions frame phases world (.cell (identity := identity) rest) outside (.cell (identity := identity) next) nextOutside
  | cleanup {plan : Plan dependencies}
      (completion : Adapt outward actions frame phases world plan (.running (rest.append outside)) (.running (next.append nextOutside)))
      (tail : Retained outward actions frame phases world rest outside next nextOutside) :
      Retained outward actions frame phases world (.cleanup (needs := needs) plan rest) outside (.cleanup (needs := needs) plan next) nextOutside
  | running : Retained outward actions frame phases world rest outside next nextOutside →
      Retained outward actions frame phases world (.running rest) outside (.running next) nextOutside
  | live : Retained outward actions frame phases world saved (rest.append outside) nextSaved (next.append nextOutside) →
      Retained outward actions frame phases world rest outside next nextOutside →
      Retained outward actions frame phases world (.live (owner := owner) saved rest) outside (.live (owner := owner) nextSaved next) nextOutside
  | spent : Retained outward actions frame phases world rest outside next nextOutside →
      Retained outward actions frame phases world (.spent (owner := owner) rest) outside (.spent (owner := owner) next) nextOutside
end

/-- Mutual compilation consumes the old source derivation only at unchanged
or explicitly retained sites. All recursive adaptation premises are discharged
by induction; no callback-transformer assumption remains in this theorem. -/
theorem sound_all_with [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    [SourceScheduledChecks.DeclarationProjection admission certification]
    (outward : List Instance) (actions : Syntax.UsageTickets)
    (legacyAdmission : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      SourcePlannedRecipeDeclarations.Declarations required plans → admission.accepts outward required plans)
    (legacyCertification : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      SourceContextualRequirements.DeclarationRecipes outward clauses families required →
        certification.accepts outward required plans) :
    (∀ frame phases world {dependencies first second} {beforeHints : Hints first} {afterHints : Hints second}
      (plan : Plan dependencies) (before : Forest beforeHints) (after : Forest afterHints),
      Adapt outward actions frame phases world plan before after →
      Local outward actions phases world plan before → Local outward actions phases world plan after) ∧
    (∀ frame phases world {first outside second nextOutside}
      {beforeHints : Hints first} {outsideHints : Hints outside} {afterHints : Hints second} {nextOutsideHints : Hints nextOutside}
      (before : Forest beforeHints) (outside : Forest outsideHints) (after : Forest afterHints) (nextOutside : Forest nextOutsideHints),
      Retained outward actions frame phases world before outside after nextOutside →
      Pending outward actions phases world before outside → Pending outward actions phases world after nextOutside) := by
  constructor
  all_goals first
    | (intro frame phases world dependencies first second beforeHints afterHints plan before after adapted
       apply Adapt.rec
         (motive_1 := fun frame phases world _ _ _ _ _ plan before after _ =>
           Local outward actions phases world plan before → Local outward actions phases world plan after)
         (motive_2 := fun frame phases world _ _ _ _ _ _ _ _ before outside after nextOutside _ =>
           Pending outward actions phases world before outside → Pending outward actions phases world after nextOutside)
         (t := adapted))
    | (intro frame phases world first outside second nextOutside beforeHints outsideHints afterHints nextOutsideHints
         before outside after nextOutside adapted
       apply Retained.rec
         (motive_1 := fun frame phases world _ _ _ _ _ plan before after _ =>
           Local outward actions phases world plan before → Local outward actions phases world plan after)
         (motive_2 := fun frame phases world _ _ _ _ _ _ _ _ before outside after nextOutside _ =>
           Pending outward actions phases world before outside → Pending outward actions phases world after nextOutside)
         (t := adapted))
  all_goals intros
  all_goals first
    | assumption
    | exact .pure
    | exact .nil
    | exact SourceScheduledScopedInvocations.request_from_capability ‹_›
    | (rename_i selected guarded bounded callbacks source
       exact SourceScheduledFreshRequests.request_from_schedule
         (fun source => SourceScheduledChecks.DeclarationProjection.project source) selected guarded bounded
         (fun disposes =>
           (SourceDeclarationPolicyTransport.scheduled_all SourceScheduledChecks.recipePolicy admission
             SourcePlannedChecks.contextualPolicy certification outward actions legacyAdmission legacyCertification).2
             _ _ _ _ ((callbacks disposes).schedule)))
    | exact .handler ‹_› ‹_›
    | (rename_i oldCut nextCut pieces guarded closing ih source
       apply SourceScheduledHandlerTransport.retained_request oldCut nextCut pieces source guarded
       intro disposes
       apply ih disposes
       cases source with
       | request lower scheduled => exact scheduled _ _ _ _ _ _ oldCut.erase _ _ oldCut.forest disposes)
    | (rename_i front saved tail nextFront nextTail oldCut nextCut pieces restored ih source
       obtain ⟨access, inside, caller, waiting⟩ := (SourceScheduledScopedInvocations.resume_iff oldCut).mp source
       have next := ih (SourceScheduledScopedInvocations.pending_resume_iff.mpr ⟨inside, caller, waiting⟩)
       have supplied := SourceHandlerInvocations.interface_of_check (pieces.resumed saved).erase
         ((SourceContextualHintChecking.check_iff _).mpr next.compatible)
       exact .resume nextCut.found
         (SourceHandlerInvocations.resume_admitted oldCut.found nextCut.found access supplied) nextCut.forest next)
    | (rename_i front saved tail nextFront nextTail oldCut nextCut pieces scheduled ih source
       obtain ⟨access, closing, caller, waiting⟩ := (SourceScheduledScopedInvocations.dispose_iff oldCut).mp source
       have next := ih (SourceScheduledScopedInvocations.pending_dispose_iff.mpr ⟨closing, caller, waiting⟩)
       have supplied := SourceHandlerInvocations.interface_of_check (pieces.disposed saved).erase
         ((SourceContextualHintChecking.check_iff _).mpr next.compatible)
       exact .dispose nextCut.found
         (SourceHandlerInvocations.dispose_admitted oldCut.found nextCut.found (pieces.owner _) access supplied) nextCut.forest next)
    | (rename_i first second ihFirst ihSecond source
       cases source with | sequence first second => exact .sequence (ihFirst first) (ihSecond second))
    | (rename_i first second ihFirst ihSecond source
       cases source with | choice first second => exact .choice (ihFirst first) (ihSecond second))
    | (rename_i supplied body ih source
       cases source with | handler recipes declarations oldSupplied checked => exact .handler recipes declarations supplied (ih checked))
    | (rename_i body completion ihBody ihCompletion source
       cases source with | cleanup body completion => exact .cleanup (ihBody body) (ihCompletion completion))
    | (rename_i body ih source
       cases source with | resource body => exact .resource (fun identity fresh => ih identity fresh (body identity fresh)))
    | (rename_i code tail ihCode ihTail source
       cases source with | plain code tail => exact .plain (ihCode code) (ihTail tail))
    | (rename_i supplied tail ih source
       cases source with | handler oldSupplied tail => exact .handler supplied (ih tail))
    | (rename_i tail ih source
       cases source with | cell tail => exact .cell (ih tail))
    | (rename_i completion tail ihCompletion ihTail source
       cases source with | cleanup completion tail => exact .cleanup (ihCompletion completion) (ihTail tail))
    | (rename_i tail ih source
       cases source with | running tail => exact .running (ih tail))
    | (rename_i saved tail ihSaved ihTail source
       cases source with | live saved tail => exact .live (ihSaved saved) (ihTail tail))
    | (rename_i tail ih source
       cases source with | spent tail => exact .spent (ih tail))

theorem sound_all (outward : List Instance) (actions : Syntax.UsageTickets) :
    (∀ frame phases world {dependencies first second} {beforeHints : Hints first} {afterHints : Hints second}
      (plan : Plan dependencies) (before : Forest beforeHints) (after : Forest afterHints),
      Adapt outward actions frame phases world plan before after →
      Local outward actions phases world plan before → Local outward actions phases world plan after) ∧
    (∀ frame phases world {first outside second nextOutside}
      {beforeHints : Hints first} {outsideHints : Hints outside} {afterHints : Hints second} {nextOutsideHints : Hints nextOutside}
      (before : Forest beforeHints) (outside : Forest outsideHints) (after : Forest afterHints) (nextOutside : Forest nextOutsideHints),
      Retained outward actions frame phases world before outside after nextOutside →
      Pending outward actions phases world before outside → Pending outward actions phases world after nextOutside) :=
  sound_all_with outward actions (fun checked => checked) (fun checked => checked)

theorem Adapt.sound_with [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    [SourceScheduledChecks.DeclarationProjection admission certification]
    (legacyAdmission : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      SourcePlannedRecipeDeclarations.Declarations required plans → admission.accepts outward required plans)
    (legacyCertification : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      SourceContextualRequirements.DeclarationRecipes outward clauses families required →
        certification.accepts outward required plans)
    {plan : Plan dependencies} {beforeHints : Hints first} {afterHints : Hints second}
    {before : Forest beforeHints} {after : Forest afterHints}
    (adapted : Adapt outward actions frame phases world plan before after)
    (checked : Local outward actions phases world plan before) :
    Local outward actions phases world plan after :=
  (sound_all_with outward actions legacyAdmission legacyCertification).1 frame phases world plan before after adapted checked

theorem Retained.sound_with [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    [SourceScheduledChecks.DeclarationProjection admission certification]
    (legacyAdmission : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      SourcePlannedRecipeDeclarations.Declarations required plans → admission.accepts outward required plans)
    (legacyCertification : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      SourceContextualRequirements.DeclarationRecipes outward clauses families required →
        certification.accepts outward required plans)
    {beforeHints : Hints first} {outsideHints : Hints outsideScope}
    {afterHints : Hints second} {nextOutsideHints : Hints nextOutsideScope}
    {before : Forest beforeHints} {outside : Forest outsideHints} {after : Forest afterHints} {nextOutside : Forest nextOutsideHints}
    (adapted : Retained outward actions frame phases world before outside after nextOutside)
    (checked : Pending outward actions phases world before outside) :
    Pending outward actions phases world after nextOutside :=
  (sound_all_with outward actions legacyAdmission legacyCertification).2 frame phases world before outside after nextOutside adapted checked

theorem Adapt.sound {plan : Plan dependencies} {beforeHints : Hints first} {afterHints : Hints second}
    {before : Forest beforeHints} {after : Forest afterHints}
    (adapted : Adapt outward actions frame phases world plan before after)
    (checked : Local outward actions phases world plan before) :
    Local outward actions phases world plan after :=
  (sound_all outward actions).1 frame phases world plan before after adapted checked

theorem Retained.sound {beforeHints : Hints first} {outsideHints : Hints outsideScope}
    {afterHints : Hints second} {nextOutsideHints : Hints nextOutsideScope}
    {before : Forest beforeHints} {outside : Forest outsideHints} {after : Forest afterHints} {nextOutside : Forest nextOutsideHints}
    (adapted : Retained outward actions frame phases world before outside after nextOutside)
    (checked : Pending outward actions phases world before outside) :
    Pending outward actions phases world after nextOutside :=
  (sound_all outward actions).2 frame phases world before outside after nextOutside adapted checked

/-- Structural adaptation never creates, drops or duplicates a retained
continuation owner. The equality preserves order and multiplicity. Outside
scopes have their own indices and are not counted as captured ownership. -/
theorem Retained.owners_preserved {beforeHints : Hints first} {outsideHints : Hints outsideScope}
    {afterHints : Hints second} {nextOutsideHints : Hints nextOutsideScope}
    {before : Forest beforeHints} {outside : Forest outsideHints} {after : Forest afterHints} {nextOutside : Forest nextOutsideHints}
    (adapted : Retained outward actions frame phases world before outside after nextOutside) :
    owners first = owners second := by
  induction before generalizing second outsideScope nextOutsideScope with
  | nil => cases adapted <;> rfl
  | plain plan rest ih => cases adapted with
    | same | install supplied => rfl
    | plain code tail =>
        have same := ih tail
        exact same
  | handler rest ih => cases adapted with
    | same | install supplied => rfl
    | handler supplied tail =>
        have same := ih tail
        exact same
  | cell rest ih => cases adapted with
    | same | install supplied => rfl
    | cell tail =>
        have same := ih tail
        exact same
  | cleanup plan rest ih => cases adapted with
    | same | install supplied => rfl
    | cleanup completion tail =>
        have same := ih tail
        exact same
  | running rest ih => cases adapted with
    | same | install supplied => rfl
    | running tail =>
        have same := ih tail
        exact same
  | live saved rest ihSaved ihRest => cases adapted with
    | same | install supplied => rfl
    | live inside tail => simp only [owners, ihSaved inside, ihRest tail]
  | spent rest ih => cases adapted with
    | same | install supplied => rfl
    | spent tail =>
        have same := ih tail
        exact same

end Ash.OneShot.SourceScheduledHandlerAdaptation

#print axioms Ash.OneShot.SourceScheduledHandlerAdaptation.sound_all
#print axioms Ash.OneShot.SourceScheduledHandlerAdaptation.sound_all_with
#print axioms Ash.OneShot.SourceScheduledHandlerAdaptation.Adapt.sound_with
#print axioms Ash.OneShot.SourceScheduledHandlerAdaptation.Retained.sound_with
#print axioms Ash.OneShot.SourceScheduledHandlerAdaptation.Adapt.sound
#print axioms Ash.OneShot.SourceScheduledHandlerAdaptation.Retained.sound

#print axioms Ash.OneShot.SourceScheduledHandlerAdaptation.Retained.owners_preserved
