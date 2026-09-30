import SourceScheduledInterceptAdmission
import SourceScheduledRetainedBounds
import SourceScheduledSourceJoin
import SourceScheduledProviderRetention

/-! Structural rechecking of actual source annotations at changed receivers.
Rules retain original plans and declaration evidence, check primitive operations
and selections, and recurse through source annotations. A fresh interception
can close an original normal prefix containing continuation-using callbacks.
No rule takes target Local, Pending or Valid as a premise. -/
namespace Ash.OneShot.SourceScheduledSourceRechecking
open SourceDependencyCapture (Scope)
open SourceContextualHints (Hints checkRequirements)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceScheduledCapabilityAnnotations (Code Retained DeclarationPolicy DeclarationLaws)
open SourceScheduledNeutral (OwnerCut)
open SourceDependencyOwners (PendingWithin owners)
open OwnerPhaseTransitions (spend)

mutual
/-- Source transformation rules. The fresh-rich rule's validity premise is for
an original prefix at the original receiver, before handler insertion. Its
future closing evidence must be derived by the recursive retained rules. -/
inductive Expression [declarations : DeclarationPolicy] (outward : List Instance) (actions : Syntax.UsageTickets) :
    (phases : OwnerPhaseTransitions.Phases) → {world : List Nat} →
    {dependencies : SourceDependencyAnnotations.Dependencies} → {beforeScope afterScope : Scope} →
    {beforeHints : Hints beforeScope} → {afterHints : Hints afterScope} →
    {plan : Plan dependencies} → {before : Forest beforeHints} →
    Code world plan before → Forest afterHints → Prop where
  | same {forest : Forest hints} {source : Code world plan forest} :
      Expression outward actions phases source forest
  | operations {afterHints : Hints afterScope} {after : Forest afterHints}
      (supplied : checkRequirements afterScope required = true) :
      Expression outward actions phases (.operations required footprint declared) after
  | reinterface {afterHints : Hints afterScope} {after : Forest afterHints}
      (footprint : SourceScheduledAdaptationCompilation.RequestFootprint plan required)
      (supplied : checkRequirements afterScope required = true) :
      Expression outward actions phases (.operations (plan := plan) oldRequired oldFootprint declared) after
  | capability {beforeHints : Hints beforeScope} {afterHints : Hints afterScope}
      {before : Forest beforeHints} {after : Forest afterHints}
      {source : Code world (.request (effect := effect) (operation := operation)) before}
      (supplied : SourceContextualClauses.RequestCapability effect operation afterScope) :
      Expression outward actions phases source after
  /-- Check only the mode selected at the actual cut. A reusable capability
  remains stronger because it must supply both ordinary and protected modes. -/
  | nonDisposing {beforeHints : Hints beforeScope} {afterHints : Hints afterScope}
      {before : Forest beforeHints} {after : Forest afterHints}
      {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
      {saved : Forest savedHints} {waiting : Forest waitingHints}
      {source : Code world (.request (effect := effect) (operation := operation)) before}
      (cut : SourceScheduledNeutral.Cut effect operation contract modes after saved waiting)
      (guarded : SourceDependencyCapture.checkCapture outward afterScope effect operation = true)
      (denied : contract.dispose = false) :
      Expression outward actions phases source after
  | selected {afterHints : Hints afterScope} {after : Forest afterHints}
      {nextSavedHints : Hints nextSavedScope} {nextWaitingHints : Hints nextWaitingScope}
      {nextSaved : Forest nextSavedHints} {nextWaiting : Forest nextWaitingHints}
      (nextCut : SourceScheduledNeutral.Cut effect operation contract modes after nextSaved nextWaiting)
      (guarded : SourceDependencyCapture.checkCapture outward afterScope effect operation = true)
      (bounded : contract.dispose = true → PendingWithin world (owners nextSavedScope) nextSavedScope)
      (closing : ∀ disposes, RetainedChange outward actions phases (oldClosing disposes)
        nextSaved.forClosing (.running nextWaiting)) :
      Expression outward actions phases (.selected (world := world) (effect := effect) (operation := operation) (contract := contract) (modes := modes) oldCut oldBound oldClosing) after
  | freshInterfaces {beforeHints : Hints beforeScope} {afterHints : Hints afterScope}
      {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
      {before : Forest beforeHints} {after : Forest afterHints}
      {saved : Forest savedHints} {waiting : Forest waitingHints}
      {source : Code world (.request (effect := effect) (operation := operation)) before}
      (intercepted : SourceScheduledHandlerSelection.Intercept effect operation contract modes table families required
        before after saved waiting)
      (callbacks : SourceScheduledCallbackInterfaces.Interfaces before)
      (declared : SourceScheduledCallbackInterfaces.Declared world callbacks)
      (covered : SourceScheduledCallbackRoutes.Covered callbacks)
      (normal : contract.dispose = true → SourceScheduledCallbackRoutes.normalCheck callbacks .nil = true)
      (guarded : SourceDependencyCapture.checkCapture outward afterScope effect operation = true)
      (bounded : contract.dispose = true → PendingWithin world (owners savedScope) savedScope) :
      Expression outward actions phases source after
  | freshRich {frontHints : Hints frontScope} {waitingHints : Hints waitingScope}
      {afterHints : Hints afterScope}
      {front : Forest frontHints} {waiting : Forest waitingHints} {after : Forest afterHints}
      {source : Code world (.request (effect := effect) (operation := operation)) (front.append waiting)}
      (intercepted : SourceScheduledHandlerSelection.Intercept effect operation contract modes table families required
        (front.append waiting) after
        (front.append (.handler (effect := effect) (table := table) (families := families) (required := required) .nil)) waiting)
      (normal : Retained world front waiting)
      (original : contract.dispose = true → normal.Valid outward actions phases)
      (guarded : SourceDependencyCapture.checkCapture outward afterScope effect operation = true)
      (bounded : contract.dispose = true → PendingWithin world
        (owners (frontScope.append (.handler effect table families .nil)))
        (frontScope.append (.handler effect table families .nil)))
      (closing : ∀ _disposes : contract.dispose = true, RetainedChange outward actions phases normal
        (front.append (.handler (effect := effect) (table := table) (families := families) (required := required) .nil)).forClosing
        (.running waiting)) :
      Expression outward actions phases source after
  | resume {nextFrontHints : Hints nextFrontScope} {nextTailHints : Hints nextTailScope}
      {nextFront : Forest nextFrontHints} {nextTail : Forest nextTailHints}
      (nextCut : OwnerCut owner after nextFront saved nextTail)
      (inside : RetainedChange outward actions (spend phases owner) oldInside saved
        (nextFront.append (.spent (owner := owner) nextTail)))
      (before : RetainedChange outward actions (spend phases owner) oldBefore nextFront (.spent (owner := owner) nextTail))
      (tail : RetainedChange outward actions (spend phases owner) oldAfter nextTail .nil) :
      Expression outward actions phases (.resume (owner := owner) (saved := saved) oldCut oldInside oldBefore oldAfter) after
  | dispose {nextFrontHints : Hints nextFrontScope} {nextTailHints : Hints nextTailScope}
      {nextFront : Forest nextFrontHints} {nextTail : Forest nextTailHints}
      (nextCut : OwnerCut owner after nextFront saved nextTail)
      (closing : RetainedChange outward actions (spend phases owner) oldClosing saved.forClosing
        (.running (nextFront.append (.spent (owner := owner) nextTail))))
      (before : RetainedChange outward actions (spend phases owner) oldBefore nextFront (.spent (owner := owner) nextTail))
      (tail : RetainedChange outward actions (spend phases owner) oldAfter nextTail .nil) :
      Expression outward actions phases (.dispose (owner := owner) (saved := saved) oldCut oldClosing oldBefore oldAfter) after
  | sequence {before : Forest beforeHints}
      {first : Code world firstPlan (.plain secondPlan before)}
      {second : Code world secondPlan before} :
      Expression outward actions phases first (.plain secondPlan after) →
      Expression outward actions phases second after →
      Expression outward actions phases (.sequence (after := secondPlan) first second) after
  | choice : Expression outward actions phases first after → Expression outward actions phases second after →
      Expression outward actions phases (.choice first second) after
  | handler {afterHints : Hints afterScope} {after : Forest afterHints}
      {before : Forest beforeHints}
      {oldBody : Code world code (.handler (effect := effect) (table := table) (families := families) (required := required) before)}
      {plans : ClausePlans clauses families}
      {declared : declarations.accepts required plans}
      {bounds : Option (SourceConsumingClauseAnnotations.ClauseBounds plans)}
      (supplied : checkRequirements afterScope required = true)
      (body : Expression outward actions phases oldBody
        (.handler (effect := effect) (table := table) (families := families) (required := required) after)) :
      Expression outward actions phases (.handler (effect := effect) (table := table) (families := families) (required := required) declared oldBody bounds) after
  | cleanup {before : Forest beforeHints}
      {body : Code world code (.cleanup (needs := needs) callback before)}
      {completion : Code world callback (.running before)} :
      Expression outward actions phases body (.cleanup (needs := needs) callback after) →
      Expression outward actions phases completion (.running after) →
      Expression outward actions phases (.cleanup (callback := callback) (needs := needs) body completion) after
  | resource {world : List Nat} {families : Nat → SourceDependencyAnnotations.Dependencies}
      {plans : ∀ identity, Plan (families identity)}
      {beforeHints : Hints beforeScope} {afterHints : Hints afterScope}
      {before : Forest beforeHints} {after : Forest afterHints}
      {code : ∀ identity, identity ∉ world → Code (world ++ [identity]) (plans identity) (.cell (identity := identity) before)}
      (body : ∀ identity fresh, Expression outward actions phases (code identity fresh) (.cell (identity := identity) after)) :
      Expression outward actions phases (.resource code) after

/-- Retained rules also express closing: discarded plain/handler/spent frames
are removed, and dormant saved branches close before their running tails. -/
inductive RetainedChange [declarations : DeclarationPolicy] (outward : List Instance) (actions : Syntax.UsageTickets) :
    (phases : OwnerPhaseTransitions.Phases) → {world : List Nat} →
    {beforeScope outsideScope afterScope nextOutsideScope : Scope} →
    {beforeHints : Hints beforeScope} → {outsideHints : Hints outsideScope} →
    {afterHints : Hints afterScope} → {nextOutsideHints : Hints nextOutsideScope} →
    {before : Forest beforeHints} → {outside : Forest outsideHints} →
    Retained world before outside → Forest afterHints → Forest nextOutsideHints → Prop where
  | same {forest : Forest hints} {outside : Forest outsideHints}
      {source : Retained world forest outside} :
      RetainedChange outward actions phases source forest outside
  | operations {afterHints : Hints afterScope} {nextOutsideHints : Hints nextOutsideScope}
      {after : Forest afterHints} {nextOutside : Forest nextOutsideHints}
      (interfaces : SourceScheduledRetainedInterfaces.Interfaces world after)
      (supplied : interfaces.check nextOutsideScope = true) :
      RetainedChange outward actions phases (.operations (world := world) oldInterfaces) after nextOutside
  /-- Provider insertion reuses the established receiver-preservation law.
  Validation is for the original source, not a target or future execution. -/
  | provide {source : Retained world before outside}
      (ready : source.Valid outward actions phases)
      (previous : RetainedChange outward actions phases source after receiver)
      (inserted : SourceScheduledProviders.Insertion identity receiver next) :
      RetainedChange outward actions phases source after next
  | plain {rest : Forest restHints} {outside : Forest outsideHints}
      {code : Code world plan (rest.append outside)}
      {tail : Retained world rest outside} :
      Expression outward actions phases code (next.append nextOutside) →
      RetainedChange outward actions phases tail next nextOutside →
      RetainedChange outward actions phases (.plain (plan := plan) code tail) (.plain plan next) nextOutside
  | handler {nextHints : Hints nextScope} {nextOutsideHints : Hints nextOutsideScope}
      {next : Forest nextHints} {nextOutside : Forest nextOutsideHints}
      (supplied : checkRequirements (nextScope.append nextOutsideScope) required = true)
      (tail : RetainedChange outward actions phases oldTail next nextOutside) :
      RetainedChange outward actions phases (.handler (effect := effect) (table := table) (families := families) (required := required) oldTail)
        (.handler (effect := effect) (table := table) (families := families) (required := required) next) nextOutside
  | cell : RetainedChange outward actions phases tail next nextOutside →
      RetainedChange outward actions phases (.cell (identity := identity) tail) (.cell (identity := identity) next) nextOutside
  | cleanup {rest : Forest restHints} {outside : Forest outsideHints}
      {completion : Code world plan (.running (rest.append outside))}
      {tail : Retained world rest outside} :
      Expression outward actions phases completion (.running (next.append nextOutside)) →
      RetainedChange outward actions phases tail next nextOutside →
      RetainedChange outward actions phases (.cleanup (plan := plan) (needs := needs) completion tail) (.cleanup (needs := needs) plan next) nextOutside
  | running : RetainedChange outward actions phases tail next nextOutside →
      RetainedChange outward actions phases (.running tail) (.running next) nextOutside
  | live : RetainedChange outward actions phases saved nextSaved (next.append nextOutside) →
      RetainedChange outward actions phases tail next nextOutside →
      RetainedChange outward actions phases (.live (owner := owner) saved tail) (.live (owner := owner) nextSaved next) nextOutside
  | spent : RetainedChange outward actions phases tail next nextOutside →
      RetainedChange outward actions phases (.spent (owner := owner) tail) (.spent (owner := owner) next) nextOutside
  | install {beforeHints : Hints beforeScope} {outsideHints : Hints outsideScope}
      {before : Forest beforeHints} {outside : Forest outsideHints} {source : Retained world before outside}
      (supplied : checkRequirements (beforeScope.append outsideScope) required = true) :
      RetainedChange outward actions phases source
        (.handler (effect := effect) (table := table) (families := families) (required := required) before) outside
  | installCleanup {beforeHints : Hints beforeScope} {outsideHints : Hints outsideScope}
      {before : Forest beforeHints} {outside : Forest outsideHints} {source : Retained world before outside}
      (required : List SourceContextualHints.Requirement)
      (footprint : SourceScheduledAdaptationCompilation.RequestFootprint callback required)
      (declared : SourceScheduledSourceInterfaces.Declared world (SourcePlanSignatures.signature callback))
      (supplied : checkRequirements (Scope.running (beforeScope.append outsideScope)) required = true) :
      RetainedChange outward actions phases source (.cleanup (needs := needs) callback before) outside
  | dropPlain : RetainedChange outward actions phases tail next nextOutside →
      RetainedChange outward actions phases (.plain code tail) next nextOutside
  | dropHandler : RetainedChange outward actions phases tail next nextOutside →
      RetainedChange outward actions phases (.handler (effect := effect) (table := table) (families := families) (required := required) tail)
        next nextOutside
  | dropSpent : RetainedChange outward actions phases tail next nextOutside →
      RetainedChange outward actions phases (.spent (owner := owner) tail) next nextOutside
  | protect : RetainedChange outward actions phases source next nextOutside →
      RetainedChange outward actions phases source (.running next) nextOutside
  | closeLive : RetainedChange outward actions phases saved nextSaved ((Forest.running next).append nextOutside) →
      RetainedChange outward actions phases tail next nextOutside →
      RetainedChange outward actions phases (.live (owner := owner) saved tail)
        (nextSaved.append (.running next)) nextOutside
end

/-- Empty retained source has a unique annotation, even when an earlier
existential compiler selected it. This exposes its primitive checks again. -/
theorem retained_nil_eq [DeclarationPolicy] (source : Retained world .nil outside) :
    source = .operations .nil := by
  cases source with
  | operations interfaces => cases interfaces; rfl

theorem RetainedChange.empty [DeclarationPolicy] {source : Retained world .nil outside} :
    RetainedChange outward actions phases source .nil nextOutside := by
  rw [retained_nil_eq source]
  exact .operations .nil rfl

/-- A request has no current-syntax handler bounds, whether operation-only or
selected. Captured closing annotations are outside this projection. -/
private theorem request_bounds [DeclarationPolicy]
    {source : Code world (.request (effect := effect) (operation := operation)) forest} :
    SourcePlanBounds.ofCode source = .absent := by
  cases source <;> rfl

section
variable [declarations : DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]

set_option maxHeartbeats 800000 in
/-- Construct one annotation before validation, with independent interpretation
and continuation implications for that same output. Existing capability compilers
and the source-only join are reused; there is no whole-source success premise. -/
theorem compile_factors_retaining_all
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans) :
    (∀ phases world {dependencies beforeScope afterScope} {beforeHints : Hints beforeScope} {afterHints : Hints afterScope}
      (plan : Plan dependencies) (before : Forest beforeHints) (source : Code world plan before) (after : Forest afterHints),
      Expression outward actions phases source after →
        ∃ annotation : Code world plan after, (source.InterpretationChecks outward → annotation.InterpretationChecks outward) ∧
             (source.ContinuationChecks actions phases → annotation.ContinuationChecks actions phases) ∧
             SourcePlanBounds.ofCode annotation = SourcePlanBounds.ofCode source) ∧
    (∀ phases world {beforeScope outsideScope afterScope nextOutsideScope}
      {beforeHints : Hints beforeScope} {outsideHints : Hints outsideScope}
      {afterHints : Hints afterScope} {nextOutsideHints : Hints nextOutsideScope}
      (before : Forest beforeHints) (outside : Forest outsideHints) (source : Retained world before outside)
      (after : Forest afterHints) (nextOutside : Forest nextOutsideHints),
      RetainedChange outward actions phases source after nextOutside →
        ∃ annotation : Retained world after nextOutside, (source.InterpretationChecks outward → annotation.InterpretationChecks outward) ∧
             (source.ContinuationChecks actions phases → annotation.ContinuationChecks actions phases) ∧
             RetainedBounds source (SourceBoundSnapshots.Retained.ofCapability annotation)) := by
  constructor
  all_goals first
    | (intro phases world dependencies beforeScope afterScope beforeHints afterHints plan before source after changed
       apply Expression.rec
         (motive_1 := fun phases {world _ _ _ _ _} plan before source after _ =>
           ∃ annotation : Code world plan after, (source.InterpretationChecks outward → annotation.InterpretationChecks outward) ∧
             (source.ContinuationChecks actions phases → annotation.ContinuationChecks actions phases) ∧
             SourcePlanBounds.ofCode annotation = SourcePlanBounds.ofCode source)
         (motive_2 := fun phases {world _ _ _ _ _ _ _ _} before outside source after nextOutside _ =>
           ∃ annotation : Retained world after nextOutside, (source.InterpretationChecks outward → annotation.InterpretationChecks outward) ∧
             (source.ContinuationChecks actions phases → annotation.ContinuationChecks actions phases) ∧
             RetainedBounds source (SourceBoundSnapshots.Retained.ofCapability annotation))
         (t := changed))
    | (intro phases world beforeScope outsideScope afterScope nextOutsideScope beforeHints outsideHints afterHints nextOutsideHints
         before outside source after nextOutside changed
       apply RetainedChange.rec
         (motive_1 := fun phases {world _ _ _ _ _} plan before source after _ =>
           ∃ annotation : Code world plan after, (source.InterpretationChecks outward → annotation.InterpretationChecks outward) ∧
             (source.ContinuationChecks actions phases → annotation.ContinuationChecks actions phases) ∧
             SourcePlanBounds.ofCode annotation = SourcePlanBounds.ofCode source)
         (motive_2 := fun phases {world _ _ _ _ _ _ _ _} before outside source after nextOutside _ =>
           ∃ annotation : Retained world after nextOutside, (source.InterpretationChecks outward → annotation.InterpretationChecks outward) ∧
             (source.ContinuationChecks actions phases → annotation.ContinuationChecks actions phases) ∧
             RetainedBounds source (SourceBoundSnapshots.Retained.ofCapability annotation))
         (t := changed))
  all_goals intros
  all_goals first
    | exact ⟨_, (fun checked => checked), (fun checked => checked), rfl⟩
    | exact ⟨_, (fun checked => checked), (fun checked => checked), .same⟩
    | (rename_i footprint world declared afterHints after supplied
       exact ⟨.operations _ footprint declared, (fun _ => supplied), (fun _ => True.intro), rfl⟩)
    | (rename_i originalDeclaration afterHints after footprint supplied
       guard_hyp footprint : SourceScheduledAdaptationCompilation.RequestFootprint _ _
       exact ⟨.operations _ footprint originalDeclaration, (fun _ => supplied), (fun _ => True.intro), rfl⟩)
    | (rename_i supplied
       guard_hyp supplied : SourceContextualClauses.RequestCapability _ _ _
       refine ⟨.operations [_] .request .request, ?_, (fun _ => True.intro), request_bounds.trans request_bounds.symm⟩
       intro _
       apply SourceContextualRequirements.check_requirements_iff.mpr
       intro request member
       cases List.mem_singleton.mp member
       exact supplied)
    | (rename_i cut guarded denied
       guard_hyp denied : _ = false
       have impossible : ∀ permission : _ = true, False := fun permission =>
         Bool.noConfusion (denied.symm.trans permission)
       refine ⟨.selected cut (fun permission => False.elim (impossible permission))
         (fun permission => False.elim (impossible permission)),
         (fun _ => ⟨guarded, fun permission => False.elim (impossible permission)⟩),
         (fun _ permission => False.elim (impossible permission)), ?_⟩
       exact request_bounds.trans request_bounds.symm)
    | (rename_i nextCut guarded bounded closing ih
       exact ⟨.selected nextCut bounded (fun disposes => Classical.choose (ih disposes)),
         (fun checked => ⟨guarded, fun disposes => (Classical.choose_spec (ih disposes)).1 (checked.2 disposes)⟩),
         (fun checked disposes => (Classical.choose_spec (ih disposes)).2.1 (checked disposes)), rfl⟩)
    | (rename_i intercepted callbacks declared covered normal guarded bounded
       guard_hyp callbacks : SourceScheduledCallbackInterfaces.Interfaces _
       obtain ⟨annotation, valid⟩ := SourceScheduledInterceptAdmission.Intercept.annotation
         (fun source => project (laws.legacyAdmission source)) intercepted callbacks declared covered normal guarded bounded
       have factors := annotation.valid_iff_factors.mp valid
       exact ⟨annotation, (fun _ => factors.1), (fun _ => factors.2), request_bounds.trans request_bounds.symm⟩)
    | (rename_i intercepted normal original guarded bounded closing ih
       have factors := fun disposes => normal.valid_iff_factors.mp (original disposes)
       refine ⟨.selected intercepted.cut bounded (fun disposes => Classical.choose (ih disposes)),
         (fun _ => ⟨guarded, fun disposes => (Classical.choose_spec (ih disposes)).1 (factors disposes).1⟩),
         (fun _ disposes => (Classical.choose_spec (ih disposes)).2.1 (factors disposes).2), ?_⟩
       exact request_bounds.trans request_bounds.symm)
    | (rename_i nextCut inside before tail ihInside ihBefore ihTail
       obtain ⟨inside, insideEffects, insideControl, insideBounds⟩ := ihInside
       obtain ⟨before, beforeEffects, beforeControl, beforeBounds⟩ := ihBefore
       obtain ⟨tail, tailEffects, tailControl, tailBounds⟩ := ihTail
       exact ⟨.resume nextCut inside before tail,
         (fun checked => ⟨insideEffects checked.1, beforeEffects checked.2.1, tailEffects checked.2.2⟩),
         (fun checked => ⟨checked.1, checked.2.1, insideControl checked.2.2.1,
           beforeControl checked.2.2.2.1, tailControl checked.2.2.2.2⟩), rfl⟩)
    | (rename_i nextCut closing before tail ihClosing ihBefore ihTail
       obtain ⟨closing, closingEffects, closingControl, closingBounds⟩ := ihClosing
       obtain ⟨before, beforeEffects, beforeControl, beforeBounds⟩ := ihBefore
       obtain ⟨tail, tailEffects, tailControl, tailBounds⟩ := ihTail
       exact ⟨.dispose nextCut closing before tail,
         (fun checked => ⟨checked.1, closingEffects checked.2.1, beforeEffects checked.2.2.1, tailEffects checked.2.2.2⟩),
         (fun checked => ⟨checked.1, checked.2.1, checked.2.2.1, closingControl checked.2.2.2.1,
           beforeControl checked.2.2.2.2.1, tailControl checked.2.2.2.2.2⟩), rfl⟩)
    | (rename_i first second ihFirst ihSecond
       obtain ⟨first, firstEffects, firstControl, firstBounds⟩ := ihFirst
       obtain ⟨second, secondEffects, secondControl, secondBounds⟩ := ihSecond
       exact ⟨.sequence first second,
         (fun checked => ⟨firstEffects checked.1, secondEffects checked.2⟩),
         (fun checked => ⟨firstControl checked.1, secondControl checked.2⟩),
         by simp only [SourcePlanBounds.ofCode, firstBounds, secondBounds]⟩)
    | (rename_i first second ihFirst ihSecond
       obtain ⟨first, firstEffects, firstControl, firstBounds⟩ := ihFirst
       obtain ⟨second, secondEffects, secondControl, secondBounds⟩ := ihSecond
       exact ⟨.choice first second,
         (fun checked => ⟨firstEffects checked.1, secondEffects checked.2⟩),
         (fun checked => ⟨firstControl checked.1, secondControl checked.2⟩),
         by simp only [SourcePlanBounds.ofCode, firstBounds, secondBounds]⟩)
    | (rename_i declared bounds supplied body ih
       obtain ⟨body, bodyEffects, bodyControl, bodyBounds⟩ := ih
       exact ⟨.handler declared body bounds,
         (fun checked => ⟨supplied, bodyEffects checked.2⟩), bodyControl,
         congrArg (SourcePlanBounds.Annotation.handler bounds) bodyBounds⟩)
    | (rename_i body completion ihBody ihCompletion
       obtain ⟨body, bodyEffects, bodyControl, bodyBounds⟩ := ihBody
       obtain ⟨completion, completionEffects, completionControl, completionBounds⟩ := ihCompletion
       exact ⟨.cleanup body completion,
         (fun checked => ⟨bodyEffects checked.1, completionEffects checked.2⟩),
         (fun checked => ⟨bodyControl checked.1, completionControl checked.2⟩),
         by simp only [SourcePlanBounds.ofCode, bodyBounds, completionBounds]⟩)
    | (rename_i body ih
       refine ⟨.resource (fun identity fresh => Classical.choose (ih identity fresh)),
         (fun checked identity fresh => (Classical.choose_spec (ih identity fresh)).1 (checked identity fresh)),
         (fun checked identity fresh => (Classical.choose_spec (ih identity fresh)).2.1 (checked identity fresh)), ?_⟩
       exact congrArg SourcePlanBounds.Annotation.resource
         (funext fun identity => funext fun fresh => (Classical.choose_spec (ih identity fresh)).2.2))
    | (rename_i interfaces supplied
       exact ⟨.operations interfaces, (fun _ => supplied), (fun _ => True.intro), .operations interfaces⟩)
    | (rename_i ready previous inserted ih
       obtain ⟨middle, effects, control, bounds⟩ := ih
       have original := (Retained.valid_iff_factors _).mp ready
       have middleReady := middle.valid_iff_factors.mpr ⟨effects original.1, control original.2⟩
       obtain ⟨next, nextReady, kept⟩ := middle.provide_receiver_retaining laws project middleReady inserted
       have factors := next.valid_iff_factors.mp nextReady
       exact ⟨next, (fun _ => factors.1), (fun _ => factors.2), kept.symm ▸ bounds⟩)
    | (rename_i code tail ihCode ihTail
       obtain ⟨code, codeEffects, codeControl, codeBounds⟩ := ihCode
       obtain ⟨tail, tailEffects, tailControl, tailBounds⟩ := ihTail
       refine ⟨.plain code tail,
         (fun checked => ⟨codeEffects checked.1, tailEffects checked.2⟩),
         (fun checked => ⟨codeControl checked.1, tailControl checked.2⟩), ?_⟩
       change RetainedBounds _ (.plain (SourcePlanBounds.ofCode code) (SourceBoundSnapshots.Retained.ofCapability tail))
       rw [codeBounds]
       exact .plain tailBounds)
    | (rename_i supplied tail ih
       obtain ⟨tail, tailEffects, tailControl, tailBounds⟩ := ih
       exact ⟨.handler tail, (fun checked => ⟨supplied, tailEffects checked.2⟩), tailControl, .handler tailBounds⟩)
    | (rename_i tail ih
       obtain ⟨tail, tailEffects, tailControl, tailBounds⟩ := ih
       exact ⟨.cell tail, tailEffects, tailControl, .cell tailBounds⟩)
    | (rename_i completion tail ihCompletion ihTail
       obtain ⟨completion, completionEffects, completionControl, completionBounds⟩ := ihCompletion
       obtain ⟨tail, tailEffects, tailControl, tailBounds⟩ := ihTail
       refine ⟨.cleanup completion tail,
         (fun checked => ⟨completionEffects checked.1, tailEffects checked.2⟩),
         (fun checked => ⟨completionControl checked.1, tailControl checked.2⟩), ?_⟩
       change RetainedBounds _ (.cleanup (SourcePlanBounds.ofCode completion) (SourceBoundSnapshots.Retained.ofCapability tail))
       rw [completionBounds]
       exact .cleanup tailBounds)
    | (rename_i tail ih
       obtain ⟨tail, tailEffects, tailControl, tailBounds⟩ := ih
       exact ⟨.running tail, tailEffects, tailControl, .running tailBounds⟩)
    | (rename_i saved tail ihSaved ihTail
       obtain ⟨saved, savedEffects, savedControl, savedBounds⟩ := ihSaved
       obtain ⟨tail, tailEffects, tailControl, tailBounds⟩ := ihTail
       exact ⟨.live saved tail,
         (fun checked => ⟨savedEffects checked.1, tailEffects checked.2⟩),
         (fun checked => ⟨savedControl checked.1, tailControl checked.2⟩), .live savedBounds tailBounds⟩)
    | (rename_i tail ih
       obtain ⟨tail, tailEffects, tailControl, tailBounds⟩ := ih
       exact ⟨.spent tail, tailEffects, tailControl, .spent tailBounds⟩)
    | (rename_i before outside source supplied
       exact ⟨.handler source, (fun checked => ⟨supplied, checked⟩), (fun checked => checked), .install⟩)
    | (rename_i source required footprint declared supplied
       exact ⟨.cleanup (.operations required footprint declared) source,
         (fun checked => ⟨supplied, checked⟩), (fun checked => ⟨True.intro, checked⟩), .installCleanup declared⟩)
    | (rename_i tail ih
       obtain ⟨annotation, effects, control, bounds⟩ := ih
       exact ⟨.running annotation, effects, control, .protect bounds⟩)
    | (rename_i tail ih
       obtain ⟨annotation, effects, control, bounds⟩ := ih
       exact ⟨annotation, (fun checked => effects checked.2), (fun checked => control checked.2), .dropPlain bounds⟩)
    | (rename_i tail ih
       obtain ⟨annotation, effects, control, bounds⟩ := ih
       exact ⟨annotation, (fun checked => effects checked.2), control, .dropHandler bounds⟩)
    | (rename_i tail ih
       obtain ⟨annotation, effects, control, bounds⟩ := ih
       exact ⟨annotation, effects, control, .dropSpent bounds⟩)
    | (rename_i saved tail ihSaved ihTail
       obtain ⟨saved, savedEffects, savedControl, savedBounds⟩ := ihSaved
       obtain ⟨tail, tailEffects, tailControl, tailBounds⟩ := ihTail
       refine ⟨saved.joinSource (.running tail),
         (fun checked => (saved.joinSource_interpretations (.running tail)).mpr
           ⟨savedEffects checked.1, tailEffects checked.2⟩),
         (fun checked => (saved.joinSource_continuations (.running tail)).mpr
           ⟨savedControl checked.1, tailControl checked.2⟩), ?_⟩
       rw [Retained.joinSource_bounds]
       exact .closeLive savedBounds tailBounds)

/-- Combine both preservation implications for the same constructed annotation.
The original API is a projection of compilation before validation. -/
theorem compile_retaining_all
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans) :
    (∀ phases world {dependencies beforeScope afterScope} {beforeHints : Hints beforeScope} {afterHints : Hints afterScope}
      (plan : Plan dependencies) (before : Forest beforeHints) (source : Code world plan before) (after : Forest afterHints),
      Expression outward actions phases source after → source.Valid outward actions phases →
        ∃ annotation : Code world plan after, annotation.Valid outward actions phases ∧
             SourcePlanBounds.ofCode annotation = SourcePlanBounds.ofCode source) ∧
    (∀ phases world {beforeScope outsideScope afterScope nextOutsideScope}
      {beforeHints : Hints beforeScope} {outsideHints : Hints outsideScope}
      {afterHints : Hints afterScope} {nextOutsideHints : Hints nextOutsideScope}
      (before : Forest beforeHints) (outside : Forest outsideHints) (source : Retained world before outside)
      (after : Forest afterHints) (nextOutside : Forest nextOutsideHints),
      RetainedChange outward actions phases source after nextOutside → source.Valid outward actions phases →
        ∃ annotation : Retained world after nextOutside, annotation.Valid outward actions phases ∧
             RetainedBounds source (SourceBoundSnapshots.Retained.ofCapability annotation)) := by
  constructor
  · intro phases world dependencies beforeScope afterScope beforeHints afterHints plan before source after changed ready
    obtain ⟨annotation, effects, control, bounds⟩ := (compile_factors_retaining_all laws project).1 _ _ _ _ _ _ changed
    have factors := source.valid_iff_factors.mp ready
    exact ⟨annotation, annotation.valid_iff_factors.mpr ⟨effects factors.1, control factors.2⟩, bounds⟩
  · intro phases world beforeScope outsideScope afterScope nextOutsideScope beforeHints outsideHints afterHints nextOutsideHints
      before outside source after nextOutside changed ready
    obtain ⟨annotation, effects, control, bounds⟩ := (compile_factors_retaining_all laws project).2 _ _ _ _ _ _ _ changed
    have factors := source.valid_iff_factors.mp ready
    exact ⟨annotation, annotation.valid_iff_factors.mpr ⟨effects factors.1, control factors.2⟩, bounds⟩

/-- One annotated target carries both independent preservation implications.
The contextual rechecking derivation is still an input; original Valid is not. -/
theorem Expression.compile_factors_retaining
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {source : Code world plan before}
    (changed : Expression outward actions phases source after) :
    ∃ annotation : Code world plan after,
      (source.InterpretationChecks outward → annotation.InterpretationChecks outward) ∧
      (source.ContinuationChecks actions phases → annotation.ContinuationChecks actions phases) ∧
      SourcePlanBounds.ofCode annotation = SourcePlanBounds.ofCode source :=
  (compile_factors_retaining_all laws project).1 _ _ _ _ _ _ changed

theorem RetainedChange.compile_factors_retaining
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {source : Retained world before outside}
    (changed : RetainedChange outward actions phases source after nextOutside) :
    ∃ annotation : Retained world after nextOutside,
      (source.InterpretationChecks outward → annotation.InterpretationChecks outward) ∧
      (source.ContinuationChecks actions phases → annotation.ContinuationChecks actions phases) ∧
      RetainedBounds source (SourceBoundSnapshots.Retained.ofCapability annotation) :=
  (compile_factors_retaining_all laws project).2 _ _ _ _ _ _ _ changed

/-- The original validity-only API projects the stronger compiler result. -/
theorem compile_all
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans) :
    (∀ phases world {dependencies beforeScope afterScope} {beforeHints : Hints beforeScope} {afterHints : Hints afterScope}
      (plan : Plan dependencies) (before : Forest beforeHints) (source : Code world plan before) (after : Forest afterHints),
      Expression outward actions phases source after → source.Valid outward actions phases →
        ∃ annotation : Code world plan after, annotation.Valid outward actions phases) ∧
    (∀ phases world {beforeScope outsideScope afterScope nextOutsideScope}
      {beforeHints : Hints beforeScope} {outsideHints : Hints outsideScope}
      {afterHints : Hints afterScope} {nextOutsideHints : Hints nextOutsideScope}
      (before : Forest beforeHints) (outside : Forest outsideHints) (source : Retained world before outside)
      (after : Forest afterHints) (nextOutside : Forest nextOutsideHints),
      RetainedChange outward actions phases source after nextOutside → source.Valid outward actions phases →
        ∃ annotation : Retained world after nextOutside, annotation.Valid outward actions phases) := by
  constructor
  · intro phases world dependencies beforeScope afterScope beforeHints afterHints plan before source after changed ready
    obtain ⟨annotation, valid, _⟩ := (compile_retaining_all laws project).1 _ _ _ _ _ _ changed ready
    exact ⟨annotation, valid⟩
  · intro phases world beforeScope outsideScope afterScope nextOutsideScope beforeHints outsideHints afterHints nextOutsideHints
      before outside source after nextOutside changed ready
    obtain ⟨annotation, valid, _⟩ := (compile_retaining_all laws project).2 _ _ _ _ _ _ _ changed ready
    exact ⟨annotation, valid⟩

/-- Structural receiver rechecking retains the exact current-plan bounds.
This projection excludes saved/caller/closing annotations, which have separate
metadata obligations. -/
theorem Expression.compile_retaining
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {source : Code world plan before}
    (changed : Expression outward actions phases source after)
    (ready : source.Valid outward actions phases) :
    ∃ annotation : Code world plan after, annotation.Valid outward actions phases ∧
      SourcePlanBounds.ofCode annotation = SourcePlanBounds.ofCode source :=
  (compile_retaining_all laws project).1 _ _ _ _ _ _ changed ready

/-- Recheck an expression from its original annotation and structural rules. -/
theorem Expression.compile
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {source : Code world plan before}
    (changed : Expression outward actions phases source after)
    (ready : source.Valid outward actions phases) :
    ∃ annotation : Code world plan after, annotation.Valid outward actions phases :=
  (compile_all laws project).1 _ _ _ _ _ _ changed ready

/-- Compile retained rechecking with structural provenance of every resulting
bound field. Closing drops and installed frames are explicit in RetainedBounds. -/
theorem RetainedChange.compile_retaining
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {source : Retained world before outside}
    (changed : RetainedChange outward actions phases source after nextOutside)
    (ready : source.Valid outward actions phases) :
    ∃ annotation : Retained world after nextOutside, annotation.Valid outward actions phases ∧
      RetainedBounds source (SourceBoundSnapshots.Retained.ofCapability annotation) :=
  (compile_retaining_all laws project).2 _ _ _ _ _ _ _ changed ready

/-- Preserve both valid retained source and admission of its persistent
metadata, using the structural provenance returned by the same compiler. -/
theorem RetainedChange.compile_admitted
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {source : Retained world before outside}
    (changed : RetainedChange outward actions phases source after nextOutside)
    (ready : source.Valid outward actions phases)
    (original : (SourceBoundSnapshots.Retained.ofCapability source).Admitted) :
    ∃ annotation : Retained world after nextOutside, annotation.Valid outward actions phases ∧
      RetainedBounds source (SourceBoundSnapshots.Retained.ofCapability annotation) ∧
      (SourceBoundSnapshots.Retained.ofCapability annotation).Admitted := by
  obtain ⟨annotation, valid, bounds⟩ := changed.compile_retaining laws project ready
  exact ⟨annotation, valid, bounds, bounds.admitted original⟩

/-- Recompose a retained source using only its structural rechecking derivation. -/
theorem RetainedChange.compile
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {source : Retained world before outside}
    (changed : RetainedChange outward actions phases source after nextOutside)
    (ready : source.Valid outward actions phases) :
    ∃ annotation : Retained world after nextOutside, annotation.Valid outward actions phases :=
  (compile_all laws project).2 _ _ _ _ _ _ _ changed ready

end
end Ash.OneShot.SourceScheduledSourceRechecking

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.compile_all

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.Expression.compile
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.RetainedChange.compile

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.retained_nil_eq
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.RetainedChange.empty

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.compile_retaining_all
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.Expression.compile_retaining

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.RetainedChange.compile_retaining

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.RetainedChange.compile_admitted

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.compile_factors_retaining_all

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.Expression.compile_factors_retaining
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.RetainedChange.compile_factors_retaining
