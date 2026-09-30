import SourceScheduledHandlerAdaptation
import SourceRequestFootprints

/-! Generate retained adaptation from actual source positions and finite
handler-interface checks. The traversal constructs the complete retained
derivation, including dormant branches and callback protection. Its internal
induction argument is not a declaration field or a future-body admission rule. -/
namespace Ash.OneShot.SourceScheduledAdaptationCompilation
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open SourceDependencyCapture (Scope)
open SourceScheduledInterpretationInsertion (Insertion Split)
open SourceScheduledHandlerAdaptation (Adapt Retained)
open SourceScheduledPendingSites (Site)
open SourceContextualHints (Requirement checkRequirements)

/-- The interface is carried by the stable source signature. Actual plans
remain the witnesses consumed by adaptation and source typing. -/
abbrev RequestFootprint (plan : Plan dependencies) (required : List Requirement) : Prop :=
  SourceRequestFootprints.Footprint (SourcePlanSignatures.signature plan) required

/-- Preserve the existing request constructor spelling for clients. -/
theorem RequestFootprint.request :
    RequestFootprint (.request (effect := effect) (operation := operation)) [(effect, operation)] := SourceRequestFootprints.Footprint.request

theorem requirements_prefix {front : Scope}
    (passing : ∀ effect, SourceHandlerRequirements.reaches effect front = true)
    (supplied : checkRequirements scope required = true) :
    checkRequirements (front.append scope) required = true := by
  apply SourceContextualRequirements.check_requirements_iff.mpr
  intro request member
  exact SourceContextualRequirements.capability_prefix (passing _)
    (SourceContextualRequirements.check_requirements_iff.mp supplied request member)

theorem requirements_handler
    (internal : checkRequirements (.handler effect table families .nil)
      (SourceHandlerRequirements.intercepted effect required) = true)
    (supplied : checkRequirements scope
      (SourceHandlerRequirements.outwardRequirements (.handler effect table families .nil) required) = true) :
    checkRequirements (.handler effect table families scope) required = true := by
  apply List.all_eq_true.mpr
  intro request member
  rw [SourceHandlerRequirements.capability_handler]
  by_cases same : request.1 = effect
  · rw [if_pos same]
    exact List.all_eq_true.mp internal request (List.mem_filter.mpr ⟨member, by simpa using same⟩)
  · rw [if_neg same]
    exact List.all_eq_true.mp supplied request
      (List.mem_filter.mpr ⟨member, by simp [SourceHandlerRequirements.reaches, same]⟩)

theorem requirements_cell (identity : Nat)
    (supplied : checkRequirements scope required = true) :
    checkRequirements (.cell identity scope) ([(.cell identity, 0), (.cell identity, 1)] ++ required) = true := by
  apply SourceContextualRequirements.check_requirements_iff.mpr
  intro request member
  rcases List.mem_append.mp member with internal | external
  · rcases List.mem_cons.mp internal with rfl | internal
    · exact SourceContextualRequirements.provider_member (provided := [identity]) (by simp)
    · have same := List.mem_singleton.mp internal
      subst request
      exact SourceContextualRequirements.provider_member (provided := [identity]) (by simp)
  · exact SourceContextualRequirements.provider_capability [identity]
      (SourceContextualRequirements.check_requirements_iff.mp supplied request external)

/-- Generate the complete code adaptation by induction on its source
footprint. The only receiving-scope premise is a finite operation check.
Handler bodies and cleanup branches may be arbitrarily nested; resource
families are checked under their bound builtin interface. -/
theorem signature_adapt {plan : Plan dependencies}
    {checking : SourcePlanSignatures.Signature dependencies}
    {beforeHints : Hints first} {afterHints : Hints second}
    {before : Forest beforeHints} {after : Forest afterHints}
    (footprint : SourceRequestFootprints.Footprint checking required)
    (same : SourcePlanSignatures.signature plan = checking)
    (supplied : checkRequirements second required = true) :
    Adapt outward actions frame phases world plan before after := by
  induction footprint generalizing first second world with
  | pure => cases plan; exact .pure
  | request =>
      cases plan
      exact .capability (SourceContextualRequirements.check_requirements_iff.mp supplied _ List.mem_cons_self)
  | @handledRequest effect operation => cases plan with
    | handler required declarations body =>
      obtain ⟨rfl, declarationsSame, bodySame⟩ := SourcePlanSignatures.Signature.handler.inj same
      apply Adapt.handler rfl
      cases body with
      | sequence initial request =>
        cases initial
        cases request
        refine .sequence .pure ?_
        apply Adapt.fresh
          (contract := ⟨true, some [], none⟩)
          (modes := (some SourceDeclarationPlans.HandledRequest.family, none))
          (.hit (by simp [SourceDeclarationPlans.HandledRequest.table, ProtectionContracts.lookup])
            (by simp [SourceDeclarationPlans.HandledRequest.families, SourceDependencyCapture.lookupDependencies]))
        · exact .handler
            (capture := .handler effect (SourceDeclarationPlans.HandledRequest.table operation)
              (SourceDeclarationPlans.HandledRequest.families operation) .nil)
            (tail := second)
            (contract := ⟨true, some [], none⟩)
            (modes := (some SourceDeclarationPlans.HandledRequest.family, none))
            (by simp [SourceDependencyCapture.select, SourceDeclarationPlans.HandledRequest.table,
              SourceDeclarationPlans.HandledRequest.families, ProtectionContracts.lookup,
              SourceDependencyCapture.lookupDependencies]) rfl rfl rfl (fun _ => .handler .nil)
        · intro permission; exact .handler .nil
        · intro permission; exact .handler .nil
  | sequence left right ihLeft ihRight => cases plan with
    | sequence firstPlan secondPlan =>
      obtain ⟨firstSame, secondSame⟩ := SourcePlanSignatures.Signature.sequence.inj same
      simp only [checkRequirements, List.all_append, Bool.and_eq_true] at supplied
      obtain ⟨left, right⟩ := supplied
      exact .sequence (ihLeft firstSame (requirements_prefix (front := .plain _ .nil) (fun _ => rfl) left))
        (ihRight secondSame right)
  | choice left right ihLeft ihRight => cases plan with
    | choice firstPlan secondPlan =>
      obtain ⟨firstSame, secondSame⟩ := SourcePlanSignatures.Signature.choice.inj same
      simp only [checkRequirements, List.all_append, Bool.and_eq_true] at supplied
      obtain ⟨left, right⟩ := supplied
      exact .choice (ihLeft firstSame left) (ihRight secondSame right)
  | handler body internal ih => cases plan with
    | handler required declarations bodyPlan =>
      obtain ⟨rfl, _, bodySame⟩ := SourcePlanSignatures.Signature.handler.inj same
      simp only [checkRequirements, List.all_append, Bool.and_eq_true] at supplied
      obtain ⟨installed, requests⟩ := supplied
      exact .handler installed (ih bodySame (requirements_handler internal requests))
  | cleanup callback body ihCallback ihBody => cases plan with
    | cleanup callbackPlan bodyPlan =>
      obtain ⟨callbackSame, bodySame⟩ := SourcePlanSignatures.Signature.cleanup.inj same
      simp only [checkRequirements, List.all_append, Bool.and_eq_true] at supplied
      obtain ⟨callback, body⟩ := supplied
      exact .cleanup (ihBody bodySame (requirements_prefix (front := .cleanup _ _ .nil) (fun _ => rfl) body))
        (ihCallback callbackSame (requirements_prefix (front := .running .nil) (fun _ => rfl) callback))
  | resource body ih => cases plan with
    | resource plans =>
      exact .resource (fun identity fresh => ih identity
        (congrFun (SourcePlanSignatures.Signature.resource.inj same) identity) (requirements_cell identity supplied))
  | weaken body included ih => exact ih same (SourceContextualRequirements.check_requirements_subset included supplied)

/-- Plan checking is a projection of the signature interface compiler. -/
theorem RequestFootprint.adapt {plan : Plan dependencies}
    {beforeHints : Hints first} {afterHints : Hints second}
    {before : Forest beforeHints} {after : Forest afterHints}
    (footprint : RequestFootprint plan required)
    (supplied : checkRequirements second required = true) :
    Adapt outward actions frame phases world plan before after := signature_adapt footprint rfl supplied

/-- An operation list does not discharge continuation access, even when that
invocation has no operation effects. Those uses retain their separate rules. -/
theorem RequestFootprint.no_invocation {plan : Plan dependencies}
    (footprint : RequestFootprint plan required) (same : dependencies = .invoke key) : False :=
  SourceRequestFootprints.Footprint.no_invocation footprint same

/-- Actual clause witnesses may change while the source interface is retained. -/
theorem RequestFootprint.signature_congr {first second : Plan dependencies}
    (footprint : RequestFootprint first required)
    (same : SourcePlanSignatures.signature first = SourcePlanSignatures.signature second) :
    RequestFootprint second required := SourceRequestFootprints.Footprint.congr footprint same

/-- Changing the outside moves the same insertion through every actual
stored-code position. No target Local or Pending judgment is supplied. -/
theorem outside {hints : Hints scope} {forest : Forest hints}
    {beforeHints : Hints first} {afterHints : Hints second}
    {before : Forest beforeHints} {after : Forest afterHints}
    (changed : Insertion frame before after)
    (compatible : hints.check second = true)
    (transfer : ∀ {dependencies oldScope nextScope} {plan : Plan dependencies}
      {oldHints : Hints oldScope} {nextHints : Hints nextScope}
      (old : Forest oldHints) (next : Forest nextHints), Site forest before plan old → Site forest after plan next →
        Insertion frame old next → Adapt outward actions frame phases world plan old next) :
    Retained outward actions frame phases world forest before forest after := by
  induction forest generalizing first second with
  | nil => exact .nil
  | plain plan rest ih =>
      exact .plain (transfer _ _ .code .code (changed.prefix _))
        (ih changed compatible (fun old next site target inserted => transfer old next (.plain site) (.plain target) inserted))
  | handler rest ih =>
      obtain ⟨supplied, tail⟩ := Bool.and_eq_true_iff.mp compatible
      exact .handler supplied
        (ih changed tail (fun old next site target inserted => transfer old next (.handler site) (.handler target) inserted))
  | cell rest ih =>
      exact .cell (ih changed compatible (fun old next site target inserted => transfer old next (.cell site) (.cell target) inserted))
  | cleanup plan rest ih =>
      exact .cleanup (transfer _ _ .callback .callback (.running (changed.prefix _)))
        (ih changed compatible (fun old next site target inserted => transfer old next (.cleanup site) (.cleanup target) inserted))
  | running rest ih =>
      exact .running (ih changed compatible (fun old next site target inserted => transfer old next (.running site) (.running target) inserted))
  | live saved rest ihSaved ihRest =>
      obtain ⟨inside, tail⟩ := Bool.and_eq_true_iff.mp compatible
      exact .live
        (ihSaved (changed.prefix _) inside (fun old next site target inserted => transfer old next (.saved site) (.saved target) inserted))
        (ihRest changed tail (fun old next site target inserted => transfer old next (.live site) (.live target) inserted))
  | spent rest ih =>
      exact .spent (ih changed compatible (fun old next site target inserted => transfer old next (.spent site) (.spent target) inserted))

/-- Insertion within retained code stops at the installed handler. The
unaffected suffix is reused; only preceding code and dormant branches generate
adaptation obligations. Handler requirements are finite Boolean checks. -/
theorem inside {beforeHints : Hints first} {afterHints : Hints second}
    {before : Forest beforeHints} {after : Forest afterHints}
    {outsideHints : Hints outsideScope} {waiting : Forest outsideHints}
    (changed : Insertion (.handler effect table families required) before after)
    (compatible : afterHints.check outsideScope = true)
    (transfer : ∀ {dependencies oldScope nextScope} {plan : Plan dependencies}
      {oldHints : Hints oldScope} {nextHints : Hints nextScope}
      (old : Forest oldHints) (next : Forest nextHints), Site before waiting plan old → Site after waiting plan next →
        Insertion (.handler effect table families required) old next →
          Adapt outward actions (.handler effect table families required) phases world plan old next) :
    Retained outward actions (.handler effect table families required) phases world before waiting after waiting := by
  induction changed with
  | here => exact .install (Bool.and_eq_true_iff.mp compatible).1
  | plain changed ih =>
      exact .plain (transfer _ _ .code .code (changed.suffix _))
        (ih compatible (fun old next site target inserted => transfer old next (.plain site) (.plain target) inserted))
  | handler changed ih =>
      obtain ⟨supplied, tail⟩ := Bool.and_eq_true_iff.mp compatible
      exact .handler supplied
        (ih tail (fun old next site target inserted => transfer old next (.handler site) (.handler target) inserted))
  | cell changed ih =>
      exact .cell (ih compatible (fun old next site target inserted => transfer old next (.cell site) (.cell target) inserted))
  | cleanup changed ih =>
      exact .cleanup (transfer _ _ .callback .callback (.running (changed.suffix _)))
        (ih compatible (fun old next site target inserted => transfer old next (.cleanup site) (.cleanup target) inserted))
  | running changed ih =>
      exact .running (ih compatible (fun old next site target inserted => transfer old next (.running site) (.running target) inserted))
  | live changed ih =>
      obtain ⟨saved, tail⟩ := Bool.and_eq_true_iff.mp compatible
      exact .live
        (outside (changed.suffix _) saved (fun old next site target inserted => transfer old next (.saved site) (.saved target) inserted))
        (ih tail (fun old next site target inserted => transfer old next (.live site) (.live target) inserted))
  | spent changed ih =>
      exact .spent (ih compatible (fun old next site target inserted => transfer old next (.spent site) (.spent target) inserted))

/-- Compile either side of an authenticated capture or owner cut with the
same source-site induction argument. -/
theorem split {beforeHints : Hints first} {afterHints : Hints second}
    {beforeOutsideHints : Hints firstOutside} {afterOutsideHints : Hints secondOutside}
    {before : Forest beforeHints} {after : Forest afterHints}
    {beforeOutside : Forest beforeOutsideHints} {afterOutside : Forest afterOutsideHints}
    (changed : Split (.handler effect table families required) before beforeOutside after afterOutside)
    (compatible : afterHints.check secondOutside = true)
    (transfer : ∀ {dependencies oldScope nextScope} {plan : Plan dependencies}
      {oldHints : Hints oldScope} {nextHints : Hints nextScope}
      (old : Forest oldHints) (next : Forest nextHints), Site before beforeOutside plan old → Site after afterOutside plan next →
        Insertion (.handler effect table families required) old next →
          Adapt outward actions (.handler effect table families required) phases world plan old next) :
    Retained outward actions (.handler effect table families required) phases world before beforeOutside after afterOutside := by
  cases changed with
  | inside changed => exact inside changed compatible transfer
  | outside changed => exact outside changed compatible transfer

open SourceScheduledNeutral (OwnerCut)

/-- An inserted handler inside a capture contributes no closing action.
Transport its exact closing forest by the established equality theorem. -/
theorem closing_inside {beforeHints : Hints first} {afterHints : Hints second}
    {before : Forest beforeHints} {after : Forest afterHints}
    {outsideHints : Hints outsideScope} {waiting : Forest outsideHints}
    (changed : Insertion (.handler effect table families required) before after) :
    Retained outward actions (.handler effect table families required) phases world
      before.forClosing waiting after.forClosing waiting := by
  obtain ⟨sameScope, sameHints, sameForest⟩ := SourceScheduledHandlerTransport.closing_same changed
  exact (SourceScheduledRecomposition.predicate_congr sameScope sameHints sameForest
    (fun next => Retained outward actions (.handler effect table families required) phases world
      before.forClosing waiting next waiting)).mp .same

/-- Closing erases an inserted captured handler. If insertion instead changes
the waiting suffix, compile adaptations only at the original callback sites.
The closing forest has no installed-handler interface obligations. -/
theorem closing {savedHints : Hints captured} {waitingHints : Hints tail}
    {nextSavedHints : Hints nextCaptured} {nextWaitingHints : Hints nextTail}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    {nextSaved : Forest nextSavedHints} {nextWaiting : Forest nextWaitingHints}
    (pieces : Split (.handler effect table families required) saved waiting nextSaved nextWaiting)
    (transfer : ∀ {dependencies oldScope nextScope} {plan : Plan dependencies}
      {oldHints : Hints oldScope} {nextHints : Hints nextScope}
      (old : Forest oldHints) (next : Forest nextHints),
      Site saved.forClosing (.running waiting) plan old →
      Site nextSaved.forClosing (.running nextWaiting) plan next →
      Insertion (.handler effect table families required) old next →
      Adapt outward actions (.handler effect table families required) phases world plan old next) :
    Retained outward actions (.handler effect table families required) phases world
      saved.forClosing (.running waiting) nextSaved.forClosing (.running nextWaiting) := by
  cases pieces with
  | inside inserted => exact closing_inside inserted
  | outside inserted =>
      exact outside (.running inserted) (SourcePlannedRecomposition.closing_check _) transfer

/-- Reuse the old request's capture and owner evidence, including disposal.
The target capture guard is a finite check; callback adaptation is generated
by the shared closing traversal rather than supplied as a whole schedule. -/
theorem request {beforeHints : Hints first} {afterHints : Hints second}
    {savedHints : Hints captured} {waitingHints : Hints tail}
    {nextSavedHints : Hints nextCaptured} {nextWaitingHints : Hints nextTail}
    {before : Forest beforeHints} {after : Forest afterHints}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    {nextSaved : Forest nextSavedHints} {nextWaiting : Forest nextWaitingHints}
    (oldCut : SourceScheduledNeutral.Cut effect operation contract modes before saved waiting)
    (nextCut : SourceScheduledNeutral.Cut effect operation contract modes after nextSaved nextWaiting)
    (pieces : Split (.handler installed table families required) saved waiting nextSaved nextWaiting)
    (guarded : SourceDependencyCapture.checkCapture outward second effect operation = true)
    (transfer : contract.dispose = true →
      ∀ {dependencies oldScope nextScope} {plan : Plan dependencies}
      {oldHints : Hints oldScope} {nextHints : Hints nextScope}
      (old : Forest oldHints) (next : Forest nextHints),
      Site saved.forClosing (.running waiting) plan old →
      Site nextSaved.forClosing (.running nextWaiting) plan next →
      Insertion (.handler installed table families required) old next →
      Adapt outward actions (.handler installed table families required) phases world plan old next) :
    Adapt outward actions (.handler installed table families required) phases world
      (.request (effect := effect) (operation := operation)) before after :=
  .request oldCut nextCut pieces (SourceDependencyCapture.check_capture_iff.mp guarded)
    (fun disposes => closing pieces (transfer disposes))

/-- When insertion is captured, no callback adaptation input is needed.
Only the changed finite capture guard remains, including closing interference. -/
theorem request_inside {beforeHints : Hints first} {afterHints : Hints second}
    {savedHints : Hints captured} {nextSavedHints : Hints nextCaptured} {waitingHints : Hints tail}
    {before : Forest beforeHints} {after : Forest afterHints}
    {saved : Forest savedHints} {nextSaved : Forest nextSavedHints} {waiting : Forest waitingHints}
    (oldCut : SourceScheduledNeutral.Cut effect operation contract modes before saved waiting)
    (nextCut : SourceScheduledNeutral.Cut effect operation contract modes after nextSaved waiting)
    (changed : Insertion (.handler installed table families required) saved nextSaved)
    (guarded : SourceDependencyCapture.checkCapture outward second effect operation = true) :
    Adapt outward actions (.handler installed table families required) phases world
      (.request (effect := effect) (operation := operation)) before after :=
  .request oldCut nextCut (.inside changed) (SourceDependencyCapture.check_capture_iff.mp guarded)
    (fun _ => closing_inside changed)

variable {beforeHints : Hints first} {afterHints : Hints second}
  {frontHints : Hints frontScope} {savedHints : Hints savedScope} {tailHints : Hints tailScope}
  {nextFrontHints : Hints nextFrontScope} {nextTailHints : Hints nextTailScope}
  {before : Forest beforeHints} {after : Forest afterHints}
  {front : Forest frontHints} {saved : Forest savedHints} {tail : Forest tailHints}
  {nextFront : Forest nextFrontHints} {nextTail : Forest nextTailHints}

/-- Resume generates its retained derivation by the shared traversal. Inputs
are the selected owner, a finite declaration check, and adaptations at actual
stored source positions; the complete recomposed schedule is a conclusion. -/
theorem resume
    (oldCut : OwnerCut owner before front saved tail)
    (nextCut : OwnerCut owner after nextFront saved nextTail)
    (pieces : Split (.handler effect table families required) front tail nextFront nextTail)
    (compatible : (savedHints.append (nextFrontHints.append (.spent (owner := owner) nextTailHints))).check .nil = true)
    (transfer : ∀ {dependencies oldScope nextScope} {plan : Plan dependencies}
      {oldHints : Hints oldScope} {nextHints : Hints nextScope}
      (old : Forest oldHints) (next : Forest nextHints),
      Site (saved.append (front.append (.spent (owner := owner) tail))) .nil plan old →
      Site (saved.append (nextFront.append (.spent (owner := owner) nextTail))) .nil plan next →
      Insertion (.handler effect table families required) old next →
      Adapt outward actions (.handler effect table families required) (OwnerPhaseTransitions.spend phases owner) world plan old next) :
    Adapt outward actions (.handler effect table families required) phases world
      (.invoke (key := ⟨owner, .resume⟩)) before after :=
  .resume oldCut nextCut pieces (inside (pieces.resumed saved) compatible transfer)

/-- Disposal uses the identical compiler on the original closing forest.
Callback positions retain running protection and the spent owner phase. -/
theorem dispose
    (oldCut : OwnerCut owner before front saved tail)
    (nextCut : OwnerCut owner after nextFront saved nextTail)
    (pieces : Split (.handler effect table families required) front tail nextFront nextTail)
    (compatible : ((SourceContextualInvocationHints.forClosing savedHints).append
      (.running (nextFrontHints.append (.spent (owner := owner) nextTailHints)))).check .nil = true)
    (transfer : ∀ {dependencies oldScope nextScope} {plan : Plan dependencies}
      {oldHints : Hints oldScope} {nextHints : Hints nextScope}
      (old : Forest oldHints) (next : Forest nextHints),
      Site (saved.forClosing.append (.running (front.append (.spent (owner := owner) tail)))) .nil plan old →
      Site (saved.forClosing.append (.running (nextFront.append (.spent (owner := owner) nextTail)))) .nil plan next →
      Insertion (.handler effect table families required) old next →
      Adapt outward actions (.handler effect table families required) (OwnerPhaseTransitions.spend phases owner) world plan old next) :
    Adapt outward actions (.handler effect table families required) phases world
      (.invoke (key := ⟨owner, .dispose⟩)) before after :=
  .dispose oldCut nextCut pieces (inside (pieces.disposed saved) compatible transfer)

end Ash.OneShot.SourceScheduledAdaptationCompilation

#print axioms Ash.OneShot.SourceScheduledAdaptationCompilation.outside
#print axioms Ash.OneShot.SourceScheduledAdaptationCompilation.RequestFootprint.adapt
#print axioms Ash.OneShot.SourceScheduledAdaptationCompilation.RequestFootprint.no_invocation
#print axioms Ash.OneShot.SourceScheduledAdaptationCompilation.inside
#print axioms Ash.OneShot.SourceScheduledAdaptationCompilation.split
#print axioms Ash.OneShot.SourceScheduledAdaptationCompilation.resume
#print axioms Ash.OneShot.SourceScheduledAdaptationCompilation.dispose
#print axioms Ash.OneShot.SourceScheduledAdaptationCompilation.closing
#print axioms Ash.OneShot.SourceScheduledAdaptationCompilation.request
#print axioms Ash.OneShot.SourceScheduledAdaptationCompilation.closing_inside
#print axioms Ash.OneShot.SourceScheduledAdaptationCompilation.request_inside

#print axioms Ash.OneShot.SourceScheduledAdaptationCompilation.RequestFootprint.request
#print axioms Ash.OneShot.SourceScheduledAdaptationCompilation.signature_adapt
#print axioms Ash.OneShot.SourceScheduledAdaptationCompilation.RequestFootprint.signature_congr

#print axioms Ash.OneShot.SourceScheduledAdaptationCompilation.requirements_prefix

#print axioms Ash.OneShot.SourceScheduledAdaptationCompilation.requirements_handler

#print axioms Ash.OneShot.SourceScheduledAdaptationCompilation.requirements_cell


namespace Ash.OneShot.SourceScheduledAdaptationCompilation.Lexical.Recursive
open SourceDependencyChecks.Lexical (ReturnHints)
open SourceDependencyChecks.Lexical.ReturnHints.Recursive (Local)
open SourceContextualRequirements.Lexical.Recursive (request_checked handled_request_checked)
open SourceContextualHints (checkRequirements)
open SourcePlanSignatures (Signature)
open SourceRequestFootprints (Footprint)

/-- Compile an existing structural request footprint in the exact lexical
receiver. No callback execution or successor check is assumed. Explicit owner
invocations remain governed by their independent continuation capabilities. -/
theorem compile_footprint {checking : Signature dependencies} {hints : ReturnHints scope}
    (footprint : Footprint checking required)
    (supplied : checkRequirements scope required = true) :
    Local outward actions phases world dependencies hints := by
  induction footprint generalizing scope world with
  | pure => exact .pure
  | request =>
      exact request_checked (SourceContextualRequirements.check_requirements_iff.mp supplied _ List.mem_cons_self)
  | handledRequest => exact handled_request_checked
  | sequence left right ihLeft ihRight =>
      simp only [checkRequirements, List.all_append, Bool.and_eq_true] at supplied
      exact .sequence
        (ihLeft (requirements_prefix (front := .plain _ .nil) (fun _ => rfl) supplied.1))
        (ihRight supplied.2)
  | choice left right ihLeft ihRight =>
      simp only [checkRequirements, List.all_append, Bool.and_eq_true] at supplied
      exact .choice (ihLeft supplied.1) (ihRight supplied.2)
  | handler body internal ih =>
      simp only [checkRequirements, List.all_append, Bool.and_eq_true] at supplied
      exact .handler (ih (requirements_handler internal supplied.2))
  | cleanup callback body ihCallback ihBody =>
      simp only [checkRequirements, List.all_append, Bool.and_eq_true] at supplied
      exact .cleanup
        (ihBody (requirements_prefix (front := .cleanup _ _ .nil) (fun _ => rfl) supplied.2))
        (ihCallback (requirements_prefix (front := .running .nil) (fun _ => rfl) supplied.1))
  | resource body ih => exact .resource (fun identity _ => ih identity (requirements_cell identity supplied))
  | weaken body included ih => exact ih (SourceContextualRequirements.check_requirements_subset included supplied)

end Ash.OneShot.SourceScheduledAdaptationCompilation.Lexical.Recursive
#print axioms Ash.OneShot.SourceScheduledAdaptationCompilation.Lexical.Recursive.compile_footprint
