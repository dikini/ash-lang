import SourceConsumingRecursiveBounds

/-! Instantiate all existing consuming-clause constructors with recursive
captured resumption chains. Clause admission and the recursive continuation
checks remain independent; the existing capability compiler supplies scheduling.
This does not yet cover arbitrary recursive retained-source shapes. -/
namespace Ash.OneShot.SourceConsumingRecursiveBounds
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledRetainedInterfaces (Interfaces)

/-- Derive disposal callbacks from the same recursive source. Pending resume
calls are discarded; dormant captures close in the existing protected order. -/
def closingChain (owners : List Nat) {hints : Hints scope} {terminal : Forest hints}
    (source : Interfaces world terminal) : Interfaces world (chain owners terminal).forClosing :=
  match owners with
  | [] => source.forClosing
  | _ :: rest => (closingChain rest source).append (.running .nil)

def closingSuffix (owners : List Nat) {hints : Hints scope} {terminal : Forest hints}
    (source : Interfaces world terminal) {suffixHints : Hints suffixScope} {suffix : Forest suffixHints}
    (retained : Interfaces world suffix) : Interfaces world ((chain owners terminal).append suffix).forClosing :=
  match owners with
  | [] => (source.append retained).forClosing
  | _ :: rest => (closingChain rest source).append (.running retained.forClosing)

end Ash.OneShot.SourceConsumingRecursiveBounds

namespace Ash.OneShot.SourceConsumingClauseAnnotations
open SourceContextualHints (Hints checkRequirements)
open SourceDependencyCapture (Scope)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open SourceScheduledRetainedInterfaces (Interfaces)
open SourceScheduledCapabilityAnnotations (Code)
open SourceScheduledNeutral (OwnerCut)
open SourceConsumingRecursiveBounds (chain annotateSuffix)

/-- Generate source data without assuming any receiving-context check. The
same recursive saved source is retained under each syntactic caller prefix. -/
def Body.annotateRecursive {plan : Plan dependencies} (body : Body world owner plan)
    (owners : List Nat) {terminalHints : Hints terminalScope} {terminal : Forest terminalHints}
    (source : Interfaces world terminal) {suffixHints : Hints suffixScope} {suffix : Forest suffixHints}
    (retained : Interfaces world suffix)
    (closing : Interfaces world ((chain owners terminal).append suffix).forClosing)
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope} {tailHints : Hints tailScope}
    {whole : Forest wholeHints} {front : Forest frontHints} {tail : Forest tailHints}
    (cut : OwnerCut owner whole front ((chain owners terminal).append suffix) tail)
    (before : Interfaces world front) (after : Interfaces world tail) : Code world plan whole :=
  match body with
  | .resume => .resume cut (annotateSuffix owners source retained (before.append (.spent after)))
      (.operations before) (.operations after)
  | .dispose => .dispose cut (.operations closing) (.operations before) (.operations after)
  | .sequence required footprint declared rest =>
      .sequence (.operations required footprint declared)
        (rest.annotateRecursive owners source retained closing cut before after)
  | .choice first second =>
      .choice (first.annotateRecursive owners source retained closing cut before after)
        (second.annotateRecursive owners source retained closing cut before after)
  | .handler bounds evidence body =>
      .handler evidence (body.annotateRecursive owners source retained closing (.handler cut) (.handler _ before) after) (some bounds)
  | .cleanup required footprint declared body =>
      .cleanup (body.annotateRecursive owners source retained closing (.cleanup cut)
        (.cleanup _ required footprint declared before) after) (.operations required footprint declared)
  | .resource body =>
      .resource (fun identity fresh => (body identity fresh).annotateRecursive owners
        (source.world_weaken (List.subset_append_left _ _))
        (retained.world_weaken (List.subset_append_left _ _))
        (closing.world_weaken (List.subset_append_left _ _)) (.cell cut)
        (.cell (before.world_weaken (List.subset_append_left _ _)))
        (after.world_weaken (List.subset_append_left _ _)))

/-- The existing clause contract supplies each caller check. Recursive source
facts are needed only when resumption is permitted; disposal uses its own
closing interface, protection and route. No target schedule is a premise. -/
theorem Body.annotateRecursive_valid {plan : Plan dependencies} (body : Body world owner plan)
    (owners : List Nat) {terminalHints : Hints terminalScope} {terminal : Forest terminalHints}
    (source : Interfaces world terminal) {suffixHints : Hints suffixScope} {suffix : Forest suffixHints}
    (retained : Interfaces world suffix)
    (closing : Interfaces world ((chain owners terminal).append suffix).forClosing)
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope} {tailHints : Hints tailScope}
    {whole : Forest wholeHints} {front : Forest frontHints} {tail : Forest tailHints}
    (cut : OwnerCut owner whole front ((chain owners terminal).append suffix) tail)
    (before : Interfaces world front) (after : Interfaces world tail)
    (checked : body.BoundCheck resumeRequired closeRequired actions phases wholeScope tailScope before)
    (fresh : owner ∉ owners)
    (nested : (actions owner).any (fun rights => rights.resume) = true → owners.Nodup ∧
      ∀ actual ∈ owners, (actions actual).any (fun rights => rights.resume) = true ∧ phases actual = .available)
    (resumeReady : (actions owner).any (fun rights => rights.resume) = true →
      (source.append retained).check resumeOutside = true)
    (resumeBound : (actions owner).any (fun rights => rights.resume) = true →
      (source.append retained).exposed ⊆ resumeRequired)
    (closeReady : (actions owner).any (fun rights => rights.dispose) = true → closing.check closeOutside = true)
    (closeBound : (actions owner).any (fun rights => rights.dispose) = true → closing.exposed ⊆ closeRequired)
    (disposal : (actions owner).any (fun rights => rights.dispose) = true →
      ((SourceConsumingRecursiveBounds.chainScope owners terminalScope).append suffixScope).held = false ∧
        SourceDependencyCapture.checkClosing outward
          ((SourceConsumingRecursiveBounds.chainScope owners terminalScope).append suffixScope).shape [] [] = true)
    (tailReady : after.check .nil = true) :
    (body.annotateRecursive owners source retained closing cut before after).Valid outward actions phases := by
  induction body generalizing wholeScope frontScope with
  | @resume currentWorld currentOwner =>
      refine ⟨checked.1, checked.2.1, ?_, checked.2.2.2, tailReady⟩
      obtain ⟨unique, capabilities⟩ := nested checked.1
      refine SourceConsumingRecursiveBounds.annotateSuffix_valid_from_bound owners source retained _ unique
        (fun actual member => (capabilities actual member).1) ?_
        (resumeReady checked.1) (resumeBound checked.1) checked.2.2.1 ?_
      · intro actual member
        have different : actual ≠ currentOwner := fun same => fresh (same ▸ member)
        exact (OwnerPhaseTransitions.spend_other different).trans (capabilities actual member).2
      · rw [before.check_append (.spent after)]
        simpa only [Interfaces.check, SourceDependencyProjection.scope_append_nil] using
          Bool.and_eq_true_iff.mpr ⟨checked.2.2.2, tailReady⟩
  | dispose =>
      exact ⟨checked.1, checked.2.1, (disposal checked.1).1, (disposal checked.1).2,
        closing.check_from_bound (closeReady checked.1) (closeBound checked.1) checked.2.2.1,
        checked.2.2.2, tailReady⟩
  | sequence required footprint declared rest ih =>
      exact ⟨checked.1, ih source retained closing cut before after checked.2 fresh nested resumeReady resumeBound closeReady closeBound disposal tailReady⟩
  | choice first second ihFirst ihSecond =>
      exact ⟨ihFirst source retained closing cut before after checked.1 fresh nested resumeReady resumeBound closeReady closeBound disposal tailReady,
        ihSecond source retained closing cut before after checked.2 fresh nested resumeReady resumeBound closeReady closeBound disposal tailReady⟩
  | handler bounds evidence body ih =>
      exact ⟨checked.1, ih source retained closing (.handler cut) (.handler _ before) after checked.2 fresh nested
        resumeReady resumeBound closeReady closeBound disposal tailReady⟩
  | cleanup required footprint declared body ih =>
      exact ⟨ih source retained closing (.cleanup cut) (.cleanup _ required footprint declared before) after checked.1 fresh nested
        resumeReady resumeBound closeReady closeBound disposal tailReady, checked.2⟩
  | resource body ih =>
      intro identity allocated
      apply ih identity allocated
        (source.world_weaken (List.subset_append_left _ _))
        (retained.world_weaken (List.subset_append_left _ _))
        (closing.world_weaken (List.subset_append_left _ _))
        (.cell cut) (.cell (before.world_weaken (List.subset_append_left _ _)))
        (after.world_weaken (List.subset_append_left _ _)) (checked identity allocated) fresh nested
      · intro permission
        simpa only [← Interfaces.append_world_weaken, Interfaces.check_world_weaken] using resumeReady permission
      · intro permission
        simpa only [← Interfaces.append_world_weaken, Interfaces.exposed_world_weaken] using resumeBound permission
      · intro permission
        simpa only [Interfaces.check_world_weaken] using closeReady permission
      · intro permission
        simpa only [Interfaces.exposed_world_weaken] using closeBound permission
      · exact disposal
      · simpa only [Interfaces.check_world_weaken] using tailReady

/-- Select the actual structurally admitted clause and instantiate every one
of its constructors at the recursive capture. Closing annotations come from
that same source. Only the finite bounds for actions used by the clause are
checked, and the original normal annotation is needed only for resumption. -/
theorem Bounded.recursive_capture_body_nested
    {plans : SourceDeclarationPlans.ClausePlans clauses families}
    {annotations : Declarations world plans} {bounds : ClauseBounds plans}
    (admitted : Bounded bounds annotations required)
    (owners : List Nat) {terminalHints : Hints terminalScope} {terminal : Forest terminalHints}
    (source : Interfaces world terminal) {suffixHints : Hints suffixScope} {suffix : Forest suffixHints}
    (retained : Interfaces world suffix)
    {waitingHints : Hints waitingScope} {waiting : Forest waitingHints} (after : Interfaces world waiting)
    {originalHints : Hints originalScope} {original : Forest originalHints}
    (oldReceiver : Interfaces world original)
    (originalReady : code.requiredActions.resume = true →
      (annotateSuffix owners source retained oldReceiver).Valid outward actions phases)
    (fresh : owner ∉ owners)
    {wholeHints : Hints wholeScope} {whole : Forest wholeHints}
    (_cut : SourceScheduledNeutral.Cut effect operation offered modes whole ((chain owners terminal).append suffix) waiting)
    (selected : SourcePlannedRecipeDeclarations.Selected operation
      ((SourceConsumingRecursiveBounds.chainScope owners terminalScope).append suffixScope).held
      plans parameter binder code bodies)
    (checked : bounds.check operation
      ((SourceConsumingRecursiveBounds.chainScope owners terminalScope).append suffixScope).held code.requiredActions
      (source.append retained).exposed (SourceConsumingRecursiveBounds.closingSuffix owners source retained).exposed = true)
    (supplied : checkRequirements waitingScope required = true)
    (closeReady : code.requiredActions.dispose = true →
      (SourceConsumingRecursiveBounds.closingSuffix owners source retained).check closeOutside = true)
    (disposal : code.requiredActions.dispose = true →
      ((SourceConsumingRecursiveBounds.chainScope owners terminalScope).append suffixScope).held = false ∧
        SourceDependencyCapture.checkClosing outward
          ((SourceConsumingRecursiveBounds.chainScope owners terminalScope).append suffixScope).shape [] [] = true)
    (tailReady : after.check .nil = true) :
    ∃ body : Body world owner (bodies owner), body.Nested ∧
      (body.annotateRecursive owners source retained
        (SourceConsumingRecursiveBounds.closingSuffix owners source retained) .hit .nil after).Valid outward
        (actions.insert owner code.requiredActions) (OwnerPhaseTransitions.introduce phases owner) := by
  obtain ⟨contract, needed, body, found, sourceAdmission, included, nested⟩ := admitted.selected_nested (owner := owner) selected
  have boundsChecked := contract.check_iff code.requiredActions |>.mp
    (show contract.check code.requiredActions (source.append retained).exposed
        (SourceConsumingRecursiveBounds.closingSuffix owners source retained).exposed = true from by
      simpa only [ClauseBounds.check, found] using checked)
  refine ⟨body, nested, ?_⟩
  apply body.annotateRecursive_valid
  · exact sourceAdmission.at_capture (by simp [Syntax.UsageTickets.insert])
      (by simp [OwnerPhaseTransitions.introduce])
      (SourceContextualRequirements.check_requirements_subset included supplied)
  · exact fresh
  · intro permission
    have original := originalReady (by simpa [Syntax.UsageTickets.insert] using permission)
    have next := SourceConsumingRecursiveBounds.annotateSuffix_fresh_owner
      (rights := code.requiredActions) owners source retained oldReceiver original fresh
    have facts := SourceConsumingRecursiveBounds.annotateSuffix_facts owners source retained oldReceiver next
    exact ⟨facts.2.1, facts.2.2⟩
  · intro permission
    exact (SourceConsumingRecursiveBounds.annotateSuffix_facts owners source retained oldReceiver
      (originalReady (by simpa [Syntax.UsageTickets.insert] using permission))).1
  · intro permission
    exact boundsChecked.1 (by simpa [Syntax.UsageTickets.insert] using permission)
  · intro permission
    exact closeReady (by simpa [Syntax.UsageTickets.insert] using permission)
  · intro permission
    exact boundsChecked.2 (by simpa [Syntax.UsageTickets.insert] using permission)
  · intro permission
    exact disposal (by simpa [Syntax.UsageTickets.insert] using permission)
  · exact tailReady
theorem Bounded.recursive_capture_annotation
    {plans : SourceDeclarationPlans.ClausePlans clauses families}
    {annotations : Declarations world plans} {bounds : ClauseBounds plans}
    (admitted : Bounded bounds annotations required)
    (owners : List Nat) {terminalHints : Hints terminalScope} {terminal : Forest terminalHints}
    (source : Interfaces world terminal) {suffixHints : Hints suffixScope} {suffix : Forest suffixHints}
    (retained : Interfaces world suffix)
    {waitingHints : Hints waitingScope} {waiting : Forest waitingHints} (after : Interfaces world waiting)
    {originalHints : Hints originalScope} {original : Forest originalHints}
    (oldReceiver : Interfaces world original)
    (originalReady : code.requiredActions.resume = true →
      (annotateSuffix owners source retained oldReceiver).Valid outward actions phases)
    (fresh : owner ∉ owners)
    {wholeHints : Hints wholeScope} {whole : Forest wholeHints}
    (cut : SourceScheduledNeutral.Cut effect operation offered modes whole ((chain owners terminal).append suffix) waiting)
    (selected : SourcePlannedRecipeDeclarations.Selected operation
      ((SourceConsumingRecursiveBounds.chainScope owners terminalScope).append suffixScope).held
      plans parameter binder code bodies)
    (checked : bounds.check operation
      ((SourceConsumingRecursiveBounds.chainScope owners terminalScope).append suffixScope).held code.requiredActions
      (source.append retained).exposed (SourceConsumingRecursiveBounds.closingSuffix owners source retained).exposed = true)
    (supplied : checkRequirements waitingScope required = true)
    (closeReady : code.requiredActions.dispose = true →
      (SourceConsumingRecursiveBounds.closingSuffix owners source retained).check closeOutside = true)
    (disposal : code.requiredActions.dispose = true →
      ((SourceConsumingRecursiveBounds.chainScope owners terminalScope).append suffixScope).held = false ∧
        SourceDependencyCapture.checkClosing outward
          ((SourceConsumingRecursiveBounds.chainScope owners terminalScope).append suffixScope).shape [] [] = true)
    (tailReady : after.check .nil = true) :
    ∃ certificate : SourceScheduledCaptureAnnotations.Capture world owner effect operation offered modes
      plans parameter binder code whole, certificate.Valid outward actions phases := by
  obtain ⟨body, _, valid⟩ := admitted.recursive_capture_body_nested owners source retained after oldReceiver
    originalReady fresh cut selected checked supplied closeReady disposal tailReady
  exact ⟨.site cut selected (body.annotateRecursive owners source retained
    (SourceConsumingRecursiveBounds.closingSuffix owners source retained) .hit .nil after), valid⟩

end Ash.OneShot.SourceConsumingClauseAnnotations

namespace Ash.OneShot.SourceConsumingCaptureInput
open SourceContextualHints (Hints checkRequirements)
open SourceRetainedPlans (Forest)
open SourceScheduledRetainedInterfaces (Interfaces)
open SourceConsumingRecursiveBounds (chain annotateSuffix closingSuffix)
open SourceConsumingClauseAnnotations (ClauseBounds Bounded Declarations)

/-- Actual source data for the bounded allocator branch. The operation-only
case retains the previous whole-forest interface. The recursive case names
the exact saved forest and waiting tail, with no body-success proof stored. -/
inductive Source (world : List Nat) :
    {scope savedScope waitingScope : SourceDependencyCapture.Scope} →
    {hints : Hints scope} → {savedHints : Hints savedScope} → {waitingHints : Hints waitingScope} →
    Forest hints → Forest savedHints → Forest waitingHints → Type where
  | operations (source : Interfaces world whole) : Source world whole saved waiting
  | recursive (owners : List Nat)
      {terminalHints : Hints terminalScope} {terminal : Forest terminalHints}
      (source : Interfaces world terminal) {suffixHints : Hints suffixScope} {suffix : Forest suffixHints}
      (retained : Interfaces world suffix) {waitingHints : Hints waitingScope} {waiting : Forest waitingHints}
      (after : Interfaces world waiting) {originalHints : Hints originalScope} {original : Forest originalHints}
      (oldReceiver : Interfaces world original) :
      Source world whole ((chain owners terminal).append suffix) waiting

/-- Independent pre-capture source checks, finite bound membership and closing
protection. Neither branch assumes a valid future clause or successor state. -/
def Source.Check {hints : Hints scope} {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {whole : Forest hints} {saved : Forest savedHints} {waiting : Forest waitingHints}
    (input : Source world whole saved waiting) (outward : List Instance)
    (actions : Syntax.UsageTickets) (phases : OwnerPhaseTransitions.Phases) (owner : Nat)
    {plans : SourceDeclarationPlans.ClausePlans clauses families} (bounds : ClauseBounds plans)
    (rights : Syntax.OneShotRights)
    (cut : SourceScheduledNeutral.Cut effect operation offered modes whole saved waiting)
    (closeOutside : SourceDependencyCapture.Scope) : Prop :=
  match input with
  | .operations source =>
      source.check .nil = true ∧ bounds.checkSource rights source cut = true ∧
      (rights.dispose = true → (source.atCut cut).1.callbacks.check closeOutside = true) ∧
      (rights.dispose = true → savedScope.held = false ∧
        SourceDependencyCapture.checkClosing outward savedScope.shape [] [] = true)
  | .recursive owners source retained after oldReceiver =>
      (rights.resume = true → (annotateSuffix owners source retained oldReceiver).Valid outward actions phases) ∧
      owner ∉ owners ∧
      bounds.check operation savedScope.held rights
        (source.append retained).exposed (closingSuffix owners source retained).exposed = true ∧
      (rights.dispose = true → (closingSuffix owners source retained).check closeOutside = true) ∧
      (rights.dispose = true → savedScope.held = false ∧
        SourceDependencyCapture.checkClosing outward savedScope.shape [] [] = true) ∧
      after.check .nil = true

/-- Both source forms construct the same existing capture certificate from
the exact selected declaration bounds. No new typed allocation proof is needed. -/
theorem Source.capture_annotation
    {plans : SourceDeclarationPlans.ClausePlans clauses families}
    {annotations : Declarations world plans} {bounds : ClauseBounds plans}
    (admitted : Bounded bounds annotations required)
    {hints : Hints scope} {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {whole : Forest hints} {saved : Forest savedHints} {waiting : Forest waitingHints}
    (input : Source world whole saved waiting)
    (cut : SourceScheduledNeutral.Cut effect operation offered modes whole saved waiting)
    (selected : SourcePlannedRecipeDeclarations.Selected operation savedScope.held plans parameter binder code bodies)
    (checked : input.Check outward actions phases owner bounds code.requiredActions cut closeOutside)
    (supplied : checkRequirements waitingScope required = true) :
    ∃ certificate : SourceScheduledCaptureAnnotations.Capture world owner effect operation offered modes
      plans parameter binder code whole, certificate.Valid outward actions phases := by
  cases input with
  | operations source =>
      exact admitted.capture_from_source cut selected source checked.1 checked.2.1 supplied checked.2.2.1 checked.2.2.2
  | recursive owners source retained after oldReceiver =>
      exact admitted.recursive_capture_annotation owners source retained after oldReceiver checked.1 checked.2.1
        cut selected checked.2.2.1 supplied checked.2.2.2.1 checked.2.2.2.2.1 checked.2.2.2.2.2

end Ash.OneShot.SourceConsumingCaptureInput

namespace Ash.OneShot.SourceConsumingRecursiveClauses.Examples
open SourceContextualHints (Hints)
open SourceDependencyCapture (Scope)
open SourceRetainedPlans (Forest)
open SourceScheduledRetainedInterfaces (Interfaces)
open SourceConsumingClauseAnnotations
open SourceConsumingRecursiveBounds (chain closingSuffix annotateSuffix)
open SourceConsumingRecursiveBounds.Examples
  (source terminal receiver captureActions capturePhases)
open SourceConsumingClauseAnnotations.ReinterpretationExamples (effectG)
open SourceDependencyCapture.Examples (effectE effectF resumeTable)

/-- The nested F declaration exposes its G requirement in both offered modes.
Its source actually requests G, so the recipe and consuming bounds agree. -/
def innerCode : ScopedExpressions.Code :=
  .bind 5 (.perform (Instantiation.freezeEffect effectG) 0 .unit) (.resume 3 .unit)
def innerFamily (owner : Nat) : SourceDependencyAnnotations.Dependencies :=
  .sequence (.sequence .pure (.request effectG 0)) (.sequence .pure (.invoke ⟨owner, .resume⟩))
def innerBodies (owner : Nat) : SourceDeclarationPlans.Plan (innerFamily owner) :=
  .sequence (.sequence .pure .request) (.sequence .pure .invoke)
def innerClauses : ScopedExpressions.Clauses := .cons 0 2 3 innerCode .nil
def innerFamilies : SourceDependencyAnnotations.ClauseDependencies :=
  [(0, some innerFamily, some innerFamily)]
def innerPlans : SourceDeclarationPlans.ClausePlans innerClauses innerFamilies :=
  .cons (.available innerBodies) (.available innerBodies) .nil
def innerBody (owner : Nat) : Body [] owner (innerBodies owner) :=
  .sequence [(effectG, 0)] (.sequence .pure .request) (.sequence .pure .request)
    (.sequence [] .pure .pure .resume)
def innerSource : Declarations [] innerPlans := .cons (.available innerBody) (.available innerBody) .nil
def gBounds : ClauseBounds innerPlans :=
  .cons (.available ⟨[(effectG, 0)], []⟩) (.available ⟨[(effectG, 0)], []⟩) .nil

theorem inner_recipes : SourcePlannedRecipeDeclarations.Declarations [(effectG, 0), (effectG, 0)] innerPlans :=
  .cons (.available (.request (.silent .pure (.resume rfl))))
    (.available (.request (.silent .pure (.resume rfl)))) .nil

theorem inner_admitted : Bounded gBounds innerSource [(effectG, 0), (effectG, 0)] := by
  have mode : BoundedMode innerCode.requiredActions (.available ⟨[(effectG, 0)], []⟩)
      (.available innerBody) [(effectG, 0)] :=
    .available (.available (fun _ => .weaken (.sequence (.sequence (.resume rfl))) (by decide)))
      (fun _ => .sequence (.sequence .resume))
  exact .cons mode mode .nil

def clauseCode : ScopedExpressions.Code :=
  .handle (Instantiation.freezeEffect effectF) (.resume 9 .unit) innerClauses
def clauseBodies (owner : Nat) := SourceDeclarationPlans.Plan.handler (effect := effectF) (table := resumeTable)
  [(effectG, 0), (effectG, 0)] innerPlans (.sequence .pure (.invoke (key := ⟨owner, .resume⟩)))
def clauseFamilies : SourceDependencyAnnotations.ClauseDependencies :=
  [(0, some (fun owner => .handler effectF resumeTable innerFamilies (.sequence .pure (.invoke ⟨owner, .resume⟩))),
    some (fun owner => .handler effectF resumeTable innerFamilies (.sequence .pure (.invoke ⟨owner, .resume⟩))))]
def clauses : ScopedExpressions.Clauses := .cons 0 1 9 clauseCode .nil
def plans : SourceDeclarationPlans.ClausePlans clauses clauseFamilies :=
  .cons (.available clauseBodies) (.available clauseBodies) .nil

def clauseBody (owner : Nat) : Body [] owner (clauseBodies owner) :=
  .handler gBounds inner_recipes (.sequence [] .pure .pure .resume)
def declarations : Declarations [] plans := .cons (.available clauseBody) (.available clauseBody) .nil
def bounds : ClauseBounds plans :=
  .cons (.available ⟨[(effectF, 0), (effectG, 0)], []⟩)
    (.available ⟨[(effectF, 0), (effectG, 0)], []⟩) .nil

theorem admitted : Bounded bounds declarations [(effectG, 0), (effectG, 0)] := by
  have mode : BoundedMode clauseCode.requiredActions (.available ⟨[(effectF, 0), (effectG, 0)], []⟩)
      (.available clauseBody) [(effectG, 0)] :=
    .available (.available (fun _ => .weaken (.handler (.sequence (.resume rfl)) rfl rfl) (by decide)))
      (fun _ => .handler innerSource inner_admitted (.sequence .resume))
  exact .cons mode mode .nil

def suffixHints : Hints (.handler effectE resumeTable clauseFamilies .nil) :=
  .handler [(effectG, 0), (effectG, 0)] .nil
def suffix : Forest suffixHints := .handler .nil
def suffixSource : Interfaces [] suffix := .handler .nil .nil
def saved := (chain [23, 31] terminal).append suffix
def whole := saved.append (SourceConsumingRecursiveBounds.Examples.caller.append SourceConsumingRecursiveBounds.Examples.waiting)
def modes : SourcePlannedCuts.Modes := (SourceDependencyCapture.lookupDependencies 0 clauseFamilies).getD (none, none)

theorem original_ready : (annotateSuffix [23, 31] source suffixSource receiver).Valid [] captureActions capturePhases := by
  apply SourceConsumingRecursiveBounds.annotateSuffix_valid_from_bound
    (originalOutside := .handler effectF resumeTable SourceScheduledClauseHandlers.Examples.innerFamilies
      (.handler effectG resumeTable SourceScheduledClauseHandlers.Examples.innerFamilies .nil))
    (required := [(effectF, 0), (effectG, 0)])
  · decide
  · intro owner member
    simp only [captureActions, if_pos member, Option.any_some]
  · intro owner member
    exact if_pos member
  · rfl
  · decide
  · rfl
  · rfl

def captureSource : SourceConsumingCaptureInput.Source [] whole saved
    (SourceConsumingRecursiveBounds.Examples.caller.append SourceConsumingRecursiveBounds.Examples.waiting) :=
  .recursive [23, 31] source suffixSource receiver receiver

theorem physical_cut : SourceScheduledNeutral.Cut effectE 0 ⟨false, some [], some []⟩ modes whole saved
    (SourceConsumingRecursiveBounds.Examples.caller.append SourceConsumingRecursiveBounds.Examples.waiting) :=
  .plain (.live (.hit rfl rfl))

theorem input_checked : captureSource.Check [] captureActions capturePhases 19 bounds clauseCode.requiredActions physical_cut .nil := by
  refine ⟨fun _ => original_ready, by decide, rfl, ?_, ?_, rfl⟩
  all_goals intro impossible; cases impossible

/-- Unlike the earlier specialized handler proof, selection here reads the
actual Bounded derivation and generates the clause's complete source annotation. -/
theorem selected_recursive_capture :
    ∃ certificate : SourceScheduledCaptureAnnotations.Capture [] 19 effectE 0
      ⟨false, some [], some []⟩ modes plans 1 9 clauseCode whole,
      certificate.Valid [] captureActions capturePhases :=
  SourceConsumingCaptureInput.Source.capture_annotation admitted captureSource physical_cut .ordinary input_checked rfl

def emptyBounds : ClauseBounds plans := .cons (.available ⟨[], []⟩) (.available ⟨[], []⟩) .nil

/-- The allocator's recursive source input cannot bypass the selected packet's
finite bound even when every original permission and operation check succeeds. -/
theorem insufficient_bound_rejected :
    ¬ captureSource.Check [] captureActions capturePhases 19 emptyBounds clauseCode.requiredActions physical_cut .nil := by
  intro checked
  have impossible : false = true := checked.2.2.1
  cases impossible

def resumeActions : Syntax.UsageTickets := fun _ => some ⟨true, false⟩
def availablePhases : OwnerPhaseTransitions.Phases := fun _ => .available

/-- Every fresh resource opening retains the recursive source while a local
cell supplies the effectful cleanup callback around resumption. -/
theorem resource_clause_valid :
    ((SourceConsumingClauseAnnotations.Examples.resourceBody 19).annotateRecursive [23, 31]
      (Interfaces.nil (world := [])) .nil (closingSuffix [23, 31] .nil .nil) .hit .nil .nil).Valid
      [] resumeActions availablePhases := by
  apply Body.annotateRecursive_valid (resumeOutside := .nil) (closeOutside := .nil)
  · exact (AdmissionExamples.admitted_resource 19).at_capture rfl rfl rfl
  · decide
  · intro permission
    exact ⟨by decide, fun _ _ => ⟨rfl, rfl⟩⟩
  · intro permission
    rfl
  · intro permission
    exact List.Subset.refl _
  · intro impossible
    cases impossible
  · intro impossible
    cases impossible
  · intro impossible
    cases impossible
  · rfl

def callbackHints : Hints (.cleanup [effectG] (.request effectG 0) .nil) := .cleanup .nil
def callback : Forest callbackHints := .cleanup .request .nil
def callbackSource : Interfaces [] callback := .cleanup .nil [(effectG, 0)] .request .request .nil
def disposeActions : Syntax.UsageTickets := fun owner => if owner = 19 then some ⟨false, true⟩ else none
def disposeBody : Body [] 19 (.invoke (key := ⟨19, .dispose⟩)) := .dispose

/-- Disposal drops the nested pending resumes and runs the source-derived G
callback. No nested resume permission or successful normal annotation is needed. -/
theorem disposal_clause_valid :
    (disposeBody.annotateRecursive [23, 31] callbackSource (Interfaces.nil (world := []))
      (closingSuffix [23, 31] callbackSource .nil) .hit .nil SourceConsumingRecursiveBounds.Examples.waitingSource).Valid
      [effectG] disposeActions availablePhases ∧
      (disposeActions 23).any (fun rights => rights.resume) = false := by
  refine ⟨?_, rfl⟩
  apply Body.annotateRecursive_valid
    (resumeRequired := []) (closeRequired := [(effectG, 0)]) (resumeOutside := .nil)
    (closeOutside := .handler effectG resumeTable SourceScheduledClauseHandlers.Examples.innerFamilies .nil)
  · exact (show Admitted ⟨false, true⟩ [] [(effectG, 0)] disposeBody [(effectG, 0)] from .dispose rfl).at_capture rfl rfl rfl
  · decide
  · intro impossible
    cases impossible
  · intro impossible
    cases impossible
  · intro impossible
    cases impossible
  · intro permission
    rfl
  · intro permission
    exact List.Subset.refl _
  · intro permission
    exact ⟨rfl, rfl⟩
  · rfl

end Ash.OneShot.SourceConsumingRecursiveClauses.Examples

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Body.annotateRecursive_valid
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Bounded.recursive_capture_annotation
#print axioms Ash.OneShot.SourceConsumingCaptureInput.Source.capture_annotation
#print axioms Ash.OneShot.SourceConsumingRecursiveClauses.Examples.admitted
#print axioms Ash.OneShot.SourceConsumingRecursiveClauses.Examples.original_ready
#print axioms Ash.OneShot.SourceConsumingRecursiveClauses.Examples.physical_cut
#print axioms Ash.OneShot.SourceConsumingRecursiveClauses.Examples.input_checked
#print axioms Ash.OneShot.SourceConsumingRecursiveClauses.Examples.selected_recursive_capture
#print axioms Ash.OneShot.SourceConsumingRecursiveClauses.Examples.insufficient_bound_rejected
#print axioms Ash.OneShot.SourceConsumingRecursiveClauses.Examples.resource_clause_valid
#print axioms Ash.OneShot.SourceConsumingRecursiveClauses.Examples.disposal_clause_valid

#print axioms Ash.OneShot.SourceConsumingRecursiveClauses.Examples.inner_recipes
#print axioms Ash.OneShot.SourceConsumingRecursiveClauses.Examples.inner_admitted

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Bounded.recursive_capture_body_nested
