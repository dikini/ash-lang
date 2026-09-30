import SourceScheduledClauses
import SourceScheduledCallbackInterfaces

/-! Construct a handler-bearing consuming clause from its original capture.
Only the retained consumer is adapted from its old derivation. Newly supplied
requests are checked under the installed handler, not before installation.
These are capture-site rules; deriving their structural adaptation from a
general source declaration remains a separate admission obligation. -/
namespace Ash.OneShot.SourceScheduledClauseHandlers
open ScopedExpressions ProtectionContracts
open SourceDependencyAnnotations (Dependencies)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceContextualHints (Hints Requirement checkRequirements)
open SourceRetainedPlans (Forest)
open SourceScheduledChecks (Local Pending)
open OwnerPhaseTransitions (introduce)

/-- Ordinary sequencing annotations for a finite list of operation requests.
Repeated entries are repeated syntax, not counted operation permissions. -/
def prefixDependencies : List Requirement → Dependencies → Dependencies
  | [], rest => rest
  | (effect, operation) :: requests, rest =>
      .sequence (.sequence .pure (.request effect operation)) (prefixDependencies requests rest)

def requestPrefix (requests : List Requirement) (rest : Plan dependencies) :
    Plan (prefixDependencies requests dependencies) :=
  match requests with
  | [] => rest
  | _ :: requests => .sequence (.sequence .pure .request) (requestPrefix requests rest)

/-- Check newly introduced requests at their actual scope. The consumer's
existing check is reused, but the prefixed body need not have checked earlier. -/
theorem prefix_checked {hints : Hints scope} {forest : Forest hints} {rest : Plan dependencies}
    (checked : Local outward actions phases world rest forest)
    (supplied : checkRequirements scope requests = true) :
    Local outward actions phases world (requestPrefix requests rest) forest := by
  induction requests with
  | nil => exact checked
  | cons request requests ih =>
      have capabilities := SourceContextualRequirements.check_requirements_iff.mp supplied
      exact .sequence (.sequence .pure (SourceScheduledScopedInvocations.request_from_capability
        (SourceContextualRequirements.capability_plain (capabilities _ List.mem_cons_self))))
        (ih (SourceContextualRequirements.check_requirements_iff.mpr
          (fun item member => capabilities item (List.mem_cons_of_mem _ member))))

/-- Installing the handler and adding request syntax is separate from
transporting an existing consumer. `adapted` is a structural derivation over
retained plans, not a premise asserting success of the new whole body. -/
theorem handler_checked {hints : Hints scope} {forest : Forest hints}
    {rest : Plan dependencies} {declarations : ClausePlans clauses families}
    (checked : Local outward actions phases world rest forest)
    (adapted : SourceScheduledHandlerAdaptation.Adapt outward actions
      (.handler effect table families required) phases world rest forest
      (.handler (effect := effect) (table := table) (families := families) (required := required) forest))
    (recipes : SourcePlannedRecipeDeclarations.Declarations required declarations)
    (supplied : checkRequirements scope required = true)
    (requestsSupplied : checkRequirements (.handler effect table families scope) requests = true) :
    Local outward actions phases world
      (.handler (effect := effect) (table := table) required declarations (requestPrefix requests rest)) forest :=
  .handler recipes recipes.certified supplied (prefix_checked (adapted.sound checked) requestsSupplied)

/-- The old consumer check comes from the pre-capture request, retained source
and structural recipe. Newly introduced requests are checked only after the
new handler is installed. No old check of the complete handler body is assumed. -/
theorem capture_handler {family : Nat → Dependencies} {bodies : ∀ owner, Plan (family owner)}
    {declarations : ClausePlans clauses installedFamilies}
    {hints : Hints scope} {savedHints : Hints captured} {waitingHints : Hints tail}
    {forest : Forest hints} {saved : Forest savedHints} {waiting : Forest waitingHints}
    (recipe : SourcePlannedClauseRecipes.Recipe rights originalRequired bodies)
    (cut : SourceScheduledNeutral.Cut requested operation contract modes forest saved waiting)
    (request : Local outward actions phases world (.request (effect := requested) (operation := operation)) forest)
    (retained : Pending outward actions phases world forest .nil)
    (fresh : actions owner = none) (consumed : phases owner = .consumed)
    (permission : rights.dispose = true → contract.dispose = true)
    (originalSupplied : checkRequirements tail originalRequired = true)
    (recipes : SourcePlannedRecipeDeclarations.Declarations required declarations)
    (supplied : checkRequirements tail required = true)
    (requestsSupplied : checkRequirements (.handler installed table installedFamilies (.live owner captured tail)) requests = true)
    (adapted : SourceScheduledHandlerAdaptation.Adapt outward (actions.insert owner rights)
      (.handler installed table installedFamilies required) (introduce phases owner) world (bodies owner)
      (.live (owner := owner) saved waiting)
      (.handler (effect := installed) (table := table) (families := installedFamilies) (required := required)
        (.live (owner := owner) saved waiting))) :
    Local outward (actions.insert owner rights) (introduce phases owner) world
      (.handler (effect := installed) (table := table) required declarations (requestPrefix requests (bodies owner)))
      (.live (owner := owner) saved waiting) ∧
    Pending outward (actions.insert owner rights) (introduce phases owner) world
      (.live (owner := owner) saved waiting) .nil := by
  obtain ⟨body, live⟩ := SourceScheduledClauses.capture recipe cut request retained retained.compatible
    fresh consumed permission originalSupplied
  have installedRequirements : checkRequirements (.live owner captured tail) required = true := by
    apply SourceContextualRequirements.check_requirements_iff.mpr
    intro item member
    exact SourceContextualRequirements.capability_live
      (SourceContextualRequirements.check_requirements_iff.mp supplied item member)
  exact ⟨handler_checked body adapted recipes installedRequirements requestsSupplied, live⟩

/-- Clause selection authenticates the entire wrapper against the actual
declaration plan. Its original consumer recipe is only a subderivation; the
selected full clause is never required to pass that older recipe grammar. -/
theorem selected_capture_handler {family : Nat → Dependencies} {bodies : ∀ owner, Plan (family owner)}
    {declarations : ClausePlans clauses installedFamilies} {outerDeclarations : ClausePlans outerClauses outerFamilies}
    {hints : Hints scope} {savedHints : Hints captured} {waitingHints : Hints tail}
    {forest : Forest hints} {saved : Forest savedHints} {waiting : Forest waitingHints}
    (selected : SourcePlannedRecipeDeclarations.Selected operation captured.held outerDeclarations parameter binder code
      (fun owner => .handler (effect := installed) (table := table) required declarations (requestPrefix requests (bodies owner))))
    (declared : SourceDependencyCapture.lookupDependencies operation outerFamilies = some modes)
    (recipe : SourcePlannedClauseRecipes.Recipe code.requiredActions originalRequired bodies)
    (cut : SourceScheduledNeutral.Cut requested operation contract modes forest saved waiting)
    (request : Local outward actions phases world (.request (effect := requested) (operation := operation)) forest)
    (retained : Pending outward actions phases world forest .nil)
    (fresh : actions owner = none) (consumed : phases owner = .consumed)
    (permission : code.requiredActions.dispose = true → contract.dispose = true)
    (originalSupplied : checkRequirements tail originalRequired = true)
    (recipes : SourcePlannedRecipeDeclarations.Declarations required declarations)
    (supplied : checkRequirements tail required = true)
    (requestsSupplied : checkRequirements (.handler installed table installedFamilies (.live owner captured tail)) requests = true)
    (adapted : SourceScheduledHandlerAdaptation.Adapt outward (actions.insert owner code.requiredActions)
      (.handler installed table installedFamilies required) (introduce phases owner) world (bodies owner)
      (.live (owner := owner) saved waiting)
      (.handler (effect := installed) (table := table) (families := installedFamilies) (required := required)
        (.live (owner := owner) saved waiting))) :
    SourceDependencyCapture.modeDependencies captured.held modes =
      some (fun owner => .handler installed table installedFamilies (prefixDependencies requests (family owner))) ∧
    Local outward (actions.insert owner code.requiredActions) (introduce phases owner) world
      (.handler (effect := installed) (table := table) required declarations (requestPrefix requests (bodies owner)))
      (.live (owner := owner) saved waiting) ∧
    Pending outward (actions.insert owner code.requiredActions) (introduce phases owner) world
      (.live (owner := owner) saved waiting) .nil := by
  refine ⟨?_, capture_handler recipe cut request retained fresh consumed permission originalSupplied
    recipes supplied requestsSupplied adapted⟩
  simpa only [declared, Option.bind_some] using selected.lookup

theorem selected_unique {firstFamily secondFamily : Nat → Dependencies}
    {first : ∀ owner, Plan (firstFamily owner)} {second : ∀ owner, Plan (secondFamily owner)}
    {declarations : ClausePlans clauses families}
    (chosen : SourcePlannedRecipeDeclarations.Selected operation held declarations parameter binder code first)
    (other : SourcePlannedRecipeDeclarations.Selected operation held declarations parameter binder code second) :
    firstFamily = secondFamily ∧ HEq first second := by
  induction chosen generalizing secondFamily with
  | ordinary => cases other with
    | ordinary => exact ⟨rfl, HEq.rfl⟩
    | pass different next => exact False.elim (different rfl)
  | protectedMode => cases other with
    | protectedMode => exact ⟨rfl, HEq.rfl⟩
    | pass different next => exact False.elim (different rfl)
  | pass different next ih => cases other with
    | ordinary | protectedMode => exact False.elim (different rfl)
    | pass _ next => exact ih next

/-- Join structural capture checking to the source derivation of exactly the
selected handler-bearing clause. The existing selected-body theorem supplies
all type, effect, row and fresh-contract obligations; lookup uniqueness fixes
its plan to the wrapper already checked above. -/
theorem source_capture_handler {family : Nat → Dependencies} {bodies : ∀ owner, Plan (family owner)}
    {declarations : ClausePlans clauses installedFamilies} {outerDeclarations : ClausePlans outerClauses outerFamilies}
    {hints : Hints scope} {savedHints : Hints captured} {waitingHints : Hints tail}
    {forest : Forest hints} {saved : Forest savedHints} {waiting : Forest waitingHints}
    (source : SourcePlannedSources.Declarations operations policy contracts world environment allowed requested answer
      outerClauses outerTable outerDeclarations)
    (selected : SourcePlannedRecipeDeclarations.Selected operation captured.held outerDeclarations parameter binder code
      (fun owner => .handler (effect := installed) (table := table) required declarations (requestPrefix requests (bodies owner))))
    (found : lookup operation outerTable = some contract) (available : contract.row captured.held = some row)
    (declared : SourceDependencyCapture.lookupDependencies operation outerFamilies = some modes)
    (recipe : SourcePlannedClauseRecipes.Recipe code.requiredActions originalRequired bodies)
    (cut : SourceScheduledNeutral.Cut requested operation contract modes forest saved waiting)
    (request : Local outward actions phases world (.request (effect := requested) (operation := operation)) forest)
    (retained : Pending outward actions phases world forest .nil)
    (fresh : actions owner = none) (consumed : phases owner = .consumed)
    (permission : code.requiredActions.dispose = true → contract.dispose = true)
    (originalSupplied : checkRequirements tail originalRequired = true)
    (recipes : SourcePlannedRecipeDeclarations.Declarations required declarations)
    (supplied : checkRequirements tail required = true)
    (requestsSupplied : checkRequirements (.handler installed table installedFamilies (.live owner captured tail)) requests = true)
    (adapted : SourceScheduledHandlerAdaptation.Adapt outward (actions.insert owner code.requiredActions)
      (.handler installed table installedFamilies required) (introduce phases owner) world (bodies owner)
      (.live (owner := owner) saved waiting)
      (.handler (effect := installed) (table := table) (families := installedFamilies) (required := required)
        (.live (owner := owner) saved waiting))) :
    ∃ argument input resumeEffects closeEffects,
      operations requested operation = some (argument, input) ∧
      (code.requiredActions.resume = true → resumeEffects = allowed) ∧
      (code.requiredActions.dispose = true → closeEffects = allowed) ∧
      Local outward (actions.insert owner code.requiredActions) (introduce phases owner) world
        (.handler (effect := installed) (table := table) required declarations (requestPrefix requests (bodies owner)))
        (.live (owner := owner) saved waiting) ∧
      Pending outward (actions.insert owner code.requiredActions) (introduce phases owner) world
        (.live (owner := owner) saved waiting) .nil ∧
      ∀ (continuation : SourcePlannedTyping.Contract), contracts owner = none →
        continuation.input = input → continuation.answer = answer →
        continuation.resumeEffects = resumeEffects → continuation.closeEffects = closeEffects →
        continuation.held = captured.held → continuation.closeDemand.Perm continuation.resumeDemand →
        SourcePlannedSources.Body operations policy (contracts.insert owner continuation) world allowed (.ticket binder owner)
          (environment.extend parameter argument) code answer ⟨owner, continuation.erase.erase, contract.dispose, row⟩
          (SourcePlanSignatures.signature
            (.handler (effect := installed) (table := table) required declarations (requestPrefix requests (bodies owner)))) := by
  obtain ⟨argument, input, resumeEffects, closeEffects, actualFamily, actualBodies, known, resume, close, chosen, body⟩ :=
    SourcePlannedSelectedSources.selected_body source selected.clause found available
  obtain ⟨rfl, same⟩ := selected_unique selected chosen
  cases same
  obtain ⟨mode, checked, pending⟩ := selected_capture_handler selected declared recipe cut request retained fresh consumed
    permission originalSupplied recipes supplied requestsSupplied adapted
  exact ⟨argument, input, resumeEffects, closeEffects, known, resume, close, checked, pending, body owner⟩

namespace Examples
open SourceDependencyCapture.Examples (effectE effectF resumeTable)
open SourceScheduledHandlerAdaptation (Adapt Retained)

def resumeFamily (owner : Nat) : Dependencies := .sequence .pure (.invoke ⟨owner, .resume⟩)
def resumeBodies (owner : Nat) : Plan (resumeFamily owner) := .sequence .pure .invoke
def innerClauses : Clauses := .cons 0 2 3 (.resume 3 .unit) .nil
def innerFamilies : SourceDependencyAnnotations.ClauseDependencies := [(0, some resumeFamily, some resumeFamily)]
def innerPlans : ClausePlans innerClauses innerFamilies :=
  .cons (.available resumeBodies) (.available resumeBodies) .nil

theorem inner_declarations : SourcePlannedRecipeDeclarations.Declarations [] innerPlans :=
  .cons (.available (.silent .pure (.resume rfl))) (.available (.silent .pure (.resume rfl))) .nil

def requests : List Requirement := [(effectF, 0), (effectF, 0)]
def code : Code := .handle (Instantiation.freezeEffect effectF)
  (.bind 5 (.perform (Instantiation.freezeEffect effectF) 0 .unit)
    (.bind 6 (.perform (Instantiation.freezeEffect effectF) 0 .unit) (.resume 9 .unit))) innerClauses
def bodies (owner : Nat) := Plan.handler (effect := effectF) (table := resumeTable) [] innerPlans
  (requestPrefix requests (resumeBodies owner))
def outerFamilies : SourceDependencyAnnotations.ClauseDependencies :=
  [(0, some (fun owner => .handler effectF resumeTable innerFamilies (prefixDependencies requests (resumeFamily owner))),
    some (fun owner => .handler effectF resumeTable innerFamilies (prefixDependencies requests (resumeFamily owner))))]
def outerClauses : Clauses := .cons 0 1 9 code .nil
def outerPlans : ClausePlans outerClauses outerFamilies := .cons (.available bodies) (.available bodies) .nil
def savedHints : Hints (.handler effectE resumeTable outerFamilies .nil) := .handler [] .nil
def saved : Forest savedHints := .handler .nil
def noActions : Syntax.UsageTickets := fun _ => none

private theorem outer_request : Local [] noActions OwnerPhaseTransitions.empty []
    (.request (effect := effectE) (operation := 0)) saved :=
  SourceScheduledScopedInvocations.request_from_capability
    (SourceContextualRequirements.check_capability_iff.mp (by rfl))

/-- The selected clause installs F, uses its capability twice, then resumes
the outer E continuation beneath F. There is no F provider before capture.
The adaptation is built from the original retained handler and spent boundary. -/
theorem newly_supplied_requests_then_resume :
    Local [] (noActions.insert 19 code.requiredActions) (introduce OwnerPhaseTransitions.empty 19) []
      (bodies 19) (.live (owner := 19) saved .nil) ∧
    Pending [] (noActions.insert 19 code.requiredActions) (introduce OwnerPhaseTransitions.empty 19) []
      (.live (owner := 19) saved .nil) .nil := by
  have admitted := selected_capture_handler (owner := 19) (outerDeclarations := outerPlans)
    (SourcePlannedRecipeDeclarations.Selected.ordinary (plans := bodies) (rest := ClausePlans.nil))
    (by rfl) (SourcePlannedClauseRecipes.Recipe.silent .pure (.resume (by rfl)))
    (SourceScheduledNeutral.Cut.hit (rest := Forest.nil) (by rfl) (by rfl)) outer_request
    (Pending.handler (by rfl) Pending.nil) (by rfl) (by rfl)
    (by intro impossible; cases impossible) (by rfl) inner_declarations (by rfl) (by rfl)
    (show Adapt [] (noActions.insert 19 code.requiredActions) (.handler effectF resumeTable innerFamilies [])
      (introduce OwnerPhaseTransitions.empty 19) [] (resumeBodies 19) (.live (owner := 19) saved .nil)
      (.handler (effect := effectF) (table := resumeTable) (families := innerFamilies) (required := [])
        (.live (owner := 19) saved .nil)) from by
      apply Adapt.sequence .pure
      apply Adapt.resume .hit (.handler .hit) (.inside .here)
      exact Retained.handler (by rfl) (Retained.install (by rfl)))
  exact admitted.2

/-- The new capture rule does not hide the old declaration restriction: that
grammar has no constructor for this handler-bearing selected body. -/
private theorem recipe_no_handler {family : Nat → Dependencies} {plans : ∀ owner, Plan (family owner)}
    (recipe : SourcePlannedClauseRecipes.Recipe rights required plans provided) :
    ∀ owner, match family owner with
      | .handler _ _ _ _ => False
      | _ => True := by
  cases recipe <;> intro owner <;> trivial

theorem old_declaration_recipe_rejects_wrapper :
    ¬ SourcePlannedRecipeDeclarations.Declarations required outerPlans := by
  intro checked
  cases checked with
  | cons ordinary protectedMode rest => cases ordinary with
    | available recipe => exact recipe_no_handler recipe 19

def waitingHints : Hints (.handler effectF resumeTable innerFamilies .nil) := .handler [] .nil
def waiting : Forest waitingHints := .handler .nil
def requestingHints : Hints (.plain (.request effectF 0) (.handler effectE resumeTable outerFamilies .nil)) :=
  .plain savedHints
def requesting : Forest requestingHints := .plain .request saved

/-- The saved F request originally reaches the waiting F handler. After
resumption it reaches the newly installed F handler first. Structural request
adaptation supplies the new capability, including its protected mode. -/
theorem saved_request_reinterpreted :
    Local [] (noActions.insert 19 code.requiredActions) (introduce OwnerPhaseTransitions.empty 19) []
      (bodies 19) (.live (owner := 19) requesting waiting) ∧
    Pending [] (noActions.insert 19 code.requiredActions) (introduce OwnerPhaseTransitions.empty 19) []
      (.live (owner := 19) requesting waiting) .nil := by
  have oldRequest : Local [] noActions OwnerPhaseTransitions.empty []
      (.request (effect := effectE) (operation := 0)) (requesting.append waiting) :=
    SourceScheduledScopedInvocations.request_from_capability
      (SourceContextualRequirements.check_capability_iff.mp (by rfl))
  have retained : Pending [] noActions OwnerPhaseTransitions.empty [] (requesting.append waiting) .nil :=
    .plain (SourceScheduledScopedInvocations.request_from_capability
      (SourceContextualRequirements.check_capability_iff.mp (by rfl))) (.handler (by rfl) (.handler (by rfl) .nil))
  have admitted := selected_capture_handler (owner := 19) (outerDeclarations := outerPlans)
    (SourcePlannedRecipeDeclarations.Selected.ordinary (plans := bodies) (rest := ClausePlans.nil))
    (by rfl) (SourcePlannedClauseRecipes.Recipe.silent .pure (.resume (by rfl)))
    (SourceScheduledNeutral.Cut.plain (plan := Plan.request)
      (SourceScheduledNeutral.Cut.hit (rest := waiting) (by rfl) (by rfl))) oldRequest retained
    (by rfl) (by rfl) (by intro impossible; cases impossible) (by rfl) inner_declarations (by rfl) (by rfl)
    (show Adapt [] (noActions.insert 19 code.requiredActions) (.handler effectF resumeTable innerFamilies [])
      (introduce OwnerPhaseTransitions.empty 19) [] (resumeBodies 19) (.live (owner := 19) requesting waiting)
      (.handler (effect := effectF) (table := resumeTable) (families := innerFamilies) (required := [])
        (.live (owner := 19) requesting waiting)) from by
      apply Adapt.sequence .pure
      apply SourceScheduledAdaptationCompilation.resume .hit (.handler .hit) (.inside .here) (by rfl)
      intro dependencies oldScope nextScope plan oldHints nextHints old next source target changed
      cases target with
      | code => exact SourceScheduledAdaptationCompilation.RequestFootprint.request.adapt (by rfl)
      | plain next => cases next with
        | handler next => cases next with
          | handler next => cases next with
            | spent next => cases next with
              | handler next => cases next)
  exact admitted.2

def disposeCode : Code := .handle (Instantiation.freezeEffect effectF)
  (.bind 5 (.perform (Instantiation.freezeEffect effectF) 0 .unit) (.discard 9)) innerClauses
def disposeRequests : List Requirement := [(effectF, 0)]
def disposeBodies (owner : Nat) := Plan.handler (effect := effectF) (table := resumeTable) [] innerPlans
  (requestPrefix disposeRequests (Plan.invoke (key := ⟨owner, .dispose⟩)))
def disposeFamilies : SourceDependencyAnnotations.ClauseDependencies :=
  [(0, some (fun owner => .handler effectF resumeTable innerFamilies
    (prefixDependencies disposeRequests (.invoke ⟨owner, .dispose⟩))), none)]
def disposeClauses : Clauses := .cons 0 1 9 disposeCode .nil
def disposePlans : ClausePlans disposeClauses disposeFamilies := .cons (.available disposeBodies) .unavailable .nil
def closingHints : Hints (.cleanup [effectF] (.request effectF 0)
    (.handler effectE SourceDependencyCapture.Examples.disposeTable disposeFamilies .nil)) := .cleanup (.handler [] .nil)
def closing : Forest closingHints := .cleanup .request (.handler .nil)

/-- Disposal retains the actual effectful callback. Its F request is checked
under running protection with the new F handler in the caller; both modes are
provided by that handler. The callback source comes from the original capture. -/
theorem saved_callback_reinterpreted_on_disposal :
    Local [effectF] (noActions.insert 19 disposeCode.requiredActions) (introduce OwnerPhaseTransitions.empty 19) []
      (disposeBodies 19) (.live (owner := 19) closing waiting) ∧
    Pending [effectF] (noActions.insert 19 disposeCode.requiredActions) (introduce OwnerPhaseTransitions.empty 19) []
      (.live (owner := 19) closing waiting) .nil := by
  have cut : SourceScheduledNeutral.Cut effectE 0 ⟨true, some [], none⟩
      (some (fun owner => .handler effectF resumeTable innerFamilies
        (prefixDependencies disposeRequests (.invoke ⟨owner, .dispose⟩))), none)
      (closing.append waiting) closing waiting := .cleanup (.hit (by rfl) (by rfl))
  have retained : Pending [effectF] noActions OwnerPhaseTransitions.empty [] (closing.append waiting) .nil :=
    .cleanup (SourceScheduledScopedInvocations.request_from_capability
      (SourceContextualRequirements.check_capability_iff.mp (by rfl))) (.handler (by rfl) (.handler (by rfl) .nil))
  let interfaces : SourceScheduledCallbackInterfaces.Interfaces closing :=
    .cleanup (.handler .nil) [(effectF, 0)] .request (.handler .nil)
  have oldRequest : Local [effectF] noActions OwnerPhaseTransitions.empty []
      (.request (effect := effectE) (operation := 0)) (closing.append waiting) := by
    apply SourceScheduledFreshRequests.request_from_callbacks cut
    · exact SourceDependencyCapture.check_capture_iff.mp (by decide)
    · intro permitted; exact .cleanup (.handler .nil)
    · intro permitted
      exact interfaces.compile (.handler effectE SourceDependencyCapture.Examples.disposeTable disposeFamilies [])
        ((SourceScheduledRecomposition.pending_append_iff closing waiting .nil).mp retained).1
        (interfaces.check_iff.mpr (by rfl))
  have admitted := selected_capture_handler (owner := 19) (outerDeclarations := disposePlans)
    (SourcePlannedRecipeDeclarations.Selected.ordinary (plans := disposeBodies) (rest := ClausePlans.nil))
    (by rfl) (SourcePlannedClauseRecipes.Recipe.dispose (by rfl)) cut oldRequest retained
    (by rfl) (by rfl) (fun _ => rfl) (by rfl) inner_declarations (by rfl) (by rfl)
    (show Adapt [effectF] (noActions.insert 19 disposeCode.requiredActions) (.handler effectF resumeTable innerFamilies [])
      (introduce OwnerPhaseTransitions.empty 19) [] (Plan.invoke (key := ⟨19, .dispose⟩)) (.live (owner := 19) closing waiting)
      (.handler (effect := effectF) (table := resumeTable) (families := innerFamilies) (required := [])
        (.live (owner := 19) closing waiting)) from by
      apply SourceScheduledAdaptationCompilation.dispose .hit (.handler .hit) (.inside .here) (by rfl)
      intro dependencies oldScope nextScope plan oldHints nextHints old next source target changed
      cases target with
      | callback => exact SourceScheduledAdaptationCompilation.RequestFootprint.request.adapt (by rfl)
      | cleanup next => cases next with
        | running next => cases next with
          | handler next => cases next with
            | spent next => cases next with
              | handler next => cases next)
  exact admitted.2

open SourceScheduledAdaptationCompilation (RequestFootprint)

/-- A stored computation with its own handler and repeated effectful cleanup.
Only callback requests cross its outer interpretation boundary. -/
def nestedStoredPlan := Plan.cleanup (needs := [effectF])
  (.sequence (.request (effect := effectF) (operation := 0)) (.request (effect := effectF) (operation := 0)))
  (.handler (effect := effectF) (table := resumeTable) [] innerPlans
    (.choice (.request (effect := effectF) (operation := 0)) (.request (effect := effectF) (operation := 0))))

theorem nested_stored_footprint : RequestFootprint nestedStoredPlan [(effectF, 0), (effectF, 0)] :=
  .cleanup (callbackRequired := [(effectF, 0), (effectF, 0)]) (bodyRequired := [])
    (.sequence (firstRequired := [(effectF, 0)]) (secondRequired := [(effectF, 0)]) .request .request)
    (.handler (bodyRequired := [(effectF, 0), (effectF, 0)])
      (.choice (firstRequired := [(effectF, 0)]) (secondRequired := [(effectF, 0)]) .request .request) (by rfl))

/-- Induction generates adaptation of the entire nested stored computation
from the finite footprint. No individual Adapt or Retained tree is supplied. -/
theorem nested_stored_reinterpreted :
    Local [] noActions OwnerPhaseTransitions.empty [] nestedStoredPlan
      (.handler (effect := effectF) (table := resumeTable) (families := innerFamilies) (required := []) waiting) := by
  have checked : Local [] noActions OwnerPhaseTransitions.empty [] nestedStoredPlan waiting := by
    apply Local.cleanup
    · apply Local.handler inner_declarations inner_declarations.certified (by rfl)
      exact .choice
        (SourceScheduledScopedInvocations.request_from_capability
          (SourceContextualRequirements.check_capability_iff.mp (by rfl)))
        (SourceScheduledScopedInvocations.request_from_capability
          (SourceContextualRequirements.check_capability_iff.mp (by rfl)))
    · exact .sequence
        (SourceScheduledScopedInvocations.request_from_capability
          (SourceContextualRequirements.check_capability_iff.mp (by rfl)))
        (SourceScheduledScopedInvocations.request_from_capability
          (SourceContextualRequirements.check_capability_iff.mp (by rfl)))
  exact (nested_stored_footprint.adapt (frame := .handler effectF resumeTable innerFamilies []) (by rfl)).sound checked

/-- A resource binder contributes its own finite read/write interface. Its
fresh identity need not be enumerated in the outer operation list. -/
theorem resource_footprint : RequestFootprint
    (.resource (fun identity => .sequence (.request (effect := .cell identity) (operation := 0))
      (.request (effect := .cell identity) (operation := 1)))) [] :=
  .resource (fun identity => .sequence (firstRequired := [(.cell identity, 0)])
    (secondRequired := [(.cell identity, 1)]) .request .request)

theorem continuation_not_an_effect_requirement :
    ¬ RequestFootprint (.invoke (key := ⟨19, .resume⟩)) ([] : List Requirement) :=
  fun footprint => footprint.no_invocation rfl

/-- Insertion in a live owner's waiting suffix also rechecks its dormant
saved computation. The traversal finds that branch without a handwritten
Retained.live derivation. -/
theorem dormant_request_reinterpreted :
    Pending [] noActions OwnerPhaseTransitions.empty []
      (.live (owner := 27) (.plain (.request (effect := effectF) (operation := 0)) .nil)
        (.handler (effect := effectF) (table := resumeTable) (families := innerFamilies) (required := []) waiting)) .nil := by
  have original : Pending [] noActions OwnerPhaseTransitions.empty []
      (.live (owner := 27) (.plain (.request (effect := effectF) (operation := 0)) .nil) waiting) .nil :=
    .live (.plain (SourceScheduledScopedInvocations.request_from_capability
      (SourceContextualRequirements.check_capability_iff.mp (by rfl))) .nil) (.handler (by rfl) .nil)
  apply (SourceScheduledAdaptationCompilation.inside
    (SourceScheduledInterpretationInsertion.Insertion.live .here) (by rfl) ?_).sound original
  intro dependencies oldScope nextScope plan oldHints nextHints old next source target changed
  cases target with
  | saved next => cases next with
    | code => exact RequestFootprint.request.adapt (by rfl)
    | plain next => cases next
  | live next => cases next with
    | handler next => cases next with
      | handler next => cases next

end Examples

end Ash.OneShot.SourceScheduledClauseHandlers

#print axioms Ash.OneShot.SourceScheduledClauseHandlers.selected_unique

#print axioms Ash.OneShot.SourceScheduledClauseHandlers.prefix_checked
#print axioms Ash.OneShot.SourceScheduledClauseHandlers.handler_checked
#print axioms Ash.OneShot.SourceScheduledClauseHandlers.capture_handler
#print axioms Ash.OneShot.SourceScheduledClauseHandlers.selected_capture_handler
#print axioms Ash.OneShot.SourceScheduledClauseHandlers.source_capture_handler
#print axioms Ash.OneShot.SourceScheduledClauseHandlers.Examples.inner_declarations
#print axioms Ash.OneShot.SourceScheduledClauseHandlers.Examples.newly_supplied_requests_then_resume
#print axioms Ash.OneShot.SourceScheduledClauseHandlers.Examples.old_declaration_recipe_rejects_wrapper
#print axioms Ash.OneShot.SourceScheduledClauseHandlers.Examples.saved_request_reinterpreted
#print axioms Ash.OneShot.SourceScheduledClauseHandlers.Examples.saved_callback_reinterpreted_on_disposal
#print axioms Ash.OneShot.SourceScheduledClauseHandlers.Examples.nested_stored_footprint
#print axioms Ash.OneShot.SourceScheduledClauseHandlers.Examples.nested_stored_reinterpreted
#print axioms Ash.OneShot.SourceScheduledClauseHandlers.Examples.resource_footprint
#print axioms Ash.OneShot.SourceScheduledClauseHandlers.Examples.continuation_not_an_effect_requirement
#print axioms Ash.OneShot.SourceScheduledClauseHandlers.Examples.dormant_request_reinterpreted
