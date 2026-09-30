import SourceScheduledHandlerInterfaceExamples

/-! Interface evidence survives an arbitrary finite nesting of handlers. The
induction reuses the existing At compiler, bound checking and source-generation
proofs. It does not infer richer continuation rechecking from an effect list. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission.InterfaceNestingExamples
open SourceContextualHints (Hints checkRequirements)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open SourceDependencyAnnotations (Dependencies)
open SourceConsumingClauseAnnotations (Body Generated)
open SourceScheduledCapabilityAnnotations (Code recipeLaws)
open SourceDependencyCapture.Examples (effectE resumeTable resumeDependencies)
open SourceScheduledInvocationInterfaceExamples (declarations declaration_recipes)
open HandlerExamples (actions phases)
open HandlerInterfaceExamples (bounds)
open SourceHandlerRequirements (intercepted)

def nestedDependencies : Nat → Dependencies
  | 0 => .choice (.invoke ⟨19, .resume⟩) (.invoke ⟨19, .dispose⟩)
  | n + 1 => .handler effectE resumeTable resumeDependencies (nestedDependencies n)

def nestedPlan : (n : Nat) → Plan (nestedDependencies n)
  | 0 => .choice .invoke .invoke
  | n + 1 => .handler [] declarations (nestedPlan n)

def nestedBody {world : List Nat} : (n : Nat) → Body world 19 (nestedPlan n)
  | 0 => .choice .resume .dispose
  | n + 1 => .handler bounds declaration_recipes (nestedBody n)

/-- Induction is over the number of handlers, not over separately constructed
examples. The successor receives the same source interfaces and primitive checks. -/
theorem nested_admitted (n : Nat)
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (context : Context world 19 outward actions phases whole front saved waiting)
    (source : context.OperationSources)
    (resumeChecked : ∀ permission, checkRequirements (.handler effectE resumeTable resumeDependencies .nil)
      (intercepted effectE (source.resumption permission).exposed) = true)
    (closeChecked : ∀ permission, checkRequirements (.handler effectE resumeTable resumeDependencies .nil)
      (intercepted effectE (source.closing permission).exposed) = true) :
    At (recipeLaws outward) (fun evidence => evidence) (nestedBody n) context := by
  induction n generalizing wholeScope frontScope with
  | zero => exact .choice .resume .dispose
  | succ n ih =>
      apply At.handler_retaining_interfaces source bounds declaration_recipes resumeChecked closeChecked
      exact ih _ (source.after_handler (required := []) resumeChecked closeChecked) resumeChecked closeChecked

/-- Clause-side owner rights and phases are checked at every terminal action.
Each installed handler has an empty declaration requirement, so its caller
interface check reuses the original one. -/
theorem nested_checked (n : Nat) (receiving : SourceDependencyCapture.Scope)
    {frontHints : Hints frontScope} {front : Forest frontHints}
    (before : SourceScheduledRetainedInterfaces.Interfaces world front)
    (ready : before.check (.spent 19 waiting) = true) :
    (nestedBody n).BoundCheck [] [] actions phases receiving waiting before := by
  induction n generalizing receiving frontScope with
  | zero => exact ⟨⟨rfl, rfl, rfl, ready⟩, ⟨rfl, rfl, rfl, ready⟩⟩
  | succ n ih =>
      exact ⟨rfl, ih _ (.handler front before) (Bool.and_eq_true_iff.mpr ⟨rfl, ready⟩)⟩

def originalSources : HandlerExamples.context.OperationSources where
  resumption := fun _ => HandlerInterfaceExamples.savedInterface
  resumeSource := HandlerInterfaceExamples.saved_view
  closing := fun _ => .nil
  closeSource := fun _ => .operations

/-- The generated source retains the actual continuation/caller correspondence,
not just its current-code metadata, at every finite nesting depth. -/
theorem nested_generated (n : Nat) :
    ∃ annotation : Code [] (nestedPlan n) HandlerExamples.whole,
      annotation.Valid [] actions phases ∧
      Generated actions HandlerExamples.context.continuationBounds (nestedBody n) annotation :=
  (nested_admitted n HandlerExamples.context originalSources (fun _ => rfl) (fun _ => rfl)).generate_source
    (nested_checked n _ .nil rfl)

theorem nested_scheduled (n : Nat) :
    SourceScheduledChecks.Local [] actions phases [] (nestedPlan n) HandlerExamples.whole :=
  (nested_admitted n HandlerExamples.context originalSources (fun _ => rfl) (fun _ => rfl)).scheduled
    (nested_checked n _ .nil rfl)

def callbackSources : HandlerInterfaceExamples.Callback.context.OperationSources where
  resumption := fun _ => HandlerInterfaceExamples.Callback.interface
  resumeSource := fun _ => .cleanup .operations
  closing := fun _ => HandlerInterfaceExamples.Callback.interface
  closeSource := fun _ => .cleanup .operations

/-- The same induction applies when BOTH saved paths contain a real callback. -/
theorem callbacks_nested_scheduled (n : Nat) :
    SourceScheduledChecks.Local [effectE] actions phases [] (nestedPlan n)
      HandlerInterfaceExamples.Callback.whole :=
  (nested_admitted n HandlerInterfaceExamples.Callback.context callbackSources
    (fun _ => rfl) (fun _ => rfl)).scheduled (nested_checked n _ .nil rfl)

/-- The independently checked caller rights still reject a consumed owner,
regardless of the number of intervening interpretations. -/
theorem consumed_nested_rejected (n : Nat) (receiving : SourceDependencyCapture.Scope)
    {frontHints : Hints frontScope} {front : Forest frontHints}
    (before : SourceScheduledRetainedInterfaces.Interfaces world front) :
    ¬ (nestedBody n).BoundCheck [] [] actions (OwnerPhaseTransitions.spend phases 19)
      receiving waiting before := by
  induction n generalizing receiving frontScope with
  | zero =>
      intro ready
      have available := ready.1.2.1
      change OwnerPhaseTransitions.spend phases 19 19 = .available at available
      simp [OwnerPhaseTransitions.spend] at available
  | succ n ih => exact fun ready => ih _ _ ready.2

def otherEffect : Instance := .user 988 []

def mixedPlan (n : Nat) := Plan.handler (effect := otherEffect)
  (table := SourceDependencyCapture.Examples.disposeTable) [] HandlerExamples.plans (nestedPlan n)
def mixedBody (n : Nat) : Body [] 19 (mixedPlan n) :=
  .handler HandlerExamples.bounds HandlerExamples.declared (nestedBody n)

/-- An unrelated disposing table composes with the finite nesting. Its own
contract is not restricted to resumptive behavior; selection keeps it separate
from the E requests in the saved source. -/
theorem mixed_admitted (n : Nat) :
    At (recipeLaws []) (fun evidence => evidence) (mixedBody n) HandlerExamples.context := by
  apply At.handler_retaining_interfaces originalSources HandlerExamples.bounds HandlerExamples.declared
    (fun _ => rfl) (fun _ => rfl)
  exact nested_admitted n _
    (originalSources.after_handler (effect := otherEffect)
      (table := SourceDependencyCapture.Examples.disposeTable)
      (families := SourceDependencyCapture.Examples.disposeDependencies) (required := [])
      (fun _ => rfl) (fun _ => rfl)) (fun _ => rfl) (fun _ => rfl)

theorem mixed_generated (n : Nat) :
    ∃ annotation : Code [] (mixedPlan n) HandlerExamples.whole,
      annotation.Valid [] actions phases ∧
      Generated actions HandlerExamples.context.continuationBounds (mixedBody n) annotation := by
  apply (mixed_admitted n).generate_source (resumeRequired := []) (closeRequired := [])
  exact ⟨rfl, nested_checked n _ (.handler .nil .nil) rfl⟩

def interleavedPlan (n : Nat) := Plan.handler (effect := effectE) (table := resumeTable) [] declarations
  (Plan.cleanup (needs := [effectE]) (.request (effect := effectE) (operation := 0)) (nestedPlan n))
def interleavedBody (n : Nat) : Body [] 19 (interleavedPlan n) :=
  .handler bounds declaration_recipes (.cleanup [(effectE, 0)] .request .request (nestedBody n))

/-- Handler entry, effectful cleanup registration and further handler entries
compose using the retained source views, with no new receiver witness supplied. -/
theorem interleaved_admitted (n : Nat) :
    At (recipeLaws []) (fun evidence => evidence) (interleavedBody n) HandlerExamples.context := by
  apply At.handler_retaining_interfaces originalSources bounds declaration_recipes
    (fun _ => rfl) (fun _ => rfl)
  let underHandler := originalSources.after_handler (effect := effectE) (table := resumeTable)
    (families := resumeDependencies) (required := []) (fun _ => rfl) (fun _ => rfl)
  apply At.cleanup_retaining_interfaces underHandler
  · intro request member
    exact List.mem_singleton.mpr (congrArg Prod.fst (List.mem_singleton.mp member))
  · exact nested_admitted n _ (underHandler.after_cleanup
      (show SourceScheduledAdaptationCompilation.RequestFootprint
        (.request (effect := effectE) (operation := 0)) [(effectE, 0)] from .request)
      .request [effectE]) (fun _ => rfl) (fun _ => rfl)

theorem interleaved_generated (n : Nat) :
    ∃ annotation : Code [] (interleavedPlan n) HandlerExamples.whole,
      annotation.Valid [] actions phases ∧
      Generated actions HandlerExamples.context.continuationBounds (interleavedBody n) annotation := by
  apply (interleaved_admitted n).generate_source (resumeRequired := []) (closeRequired := [])
  exact ⟨rfl, ⟨nested_checked n _ _ rfl, rfl⟩⟩

def resourcePlan (n : Nat) := Plan.resource (fun identity =>
  Plan.sequence (.sequence .pure (.request (effect := .cell identity) (operation := 0))) (nestedPlan n))
def resourceBody (n : Nat) : Body [] 19 (resourcePlan n) := .resource (fun identity _ =>
  .sequence [(.cell identity, 0)] (.sequence .pure .request) (.sequence .pure .request) (nestedBody n))

/-- Resource entry supplies a real builtin request before the nested handlers.
The proof quantifies over every fresh identity in the existing resource rule. -/
theorem resource_admitted (n : Nat) :
    At (recipeLaws []) (fun evidence => evidence) (resourceBody n) HandlerExamples.context := by
  apply At.resource_retaining_interfaces originalSources
  intro identity _fresh
  exact .sequence (nested_admitted n _ (originalSources.after_resource identity)
    (fun _ => rfl) (fun _ => rfl))

theorem resource_generated (n : Nat) :
    ∃ annotation : Code [] (resourcePlan n) HandlerExamples.whole,
      annotation.Valid [] actions phases ∧
      Generated actions HandlerExamples.context.continuationBounds (resourceBody n) annotation := by
  apply (resource_admitted n).generate_source (resumeRequired := []) (closeRequired := [])
  intro identity _fresh
  refine ⟨?_, nested_checked n _ _ rfl⟩
  simp [SourceContextualHints.checkRequirements, SourceContextualHints.checkCapability,
    SourceDependencyCapture.select, SourceDependencyCapture.Selection.prepend]

def allEntriesPlan (n : Nat) := Plan.handler (effect := effectE) (table := resumeTable) [] declarations
  (Plan.cleanup (needs := [effectE]) (.request (effect := effectE) (operation := 0)) (resourcePlan n))
def allEntriesBody (n : Nat) : Body [] 19 (allEntriesPlan n) :=
  .handler bounds declaration_recipes (.cleanup [(effectE, 0)] .request .request (resourceBody n))

/-- All three entry forms compose before an actual fresh-cell request and
arbitrarily deep nested handlers. The same source evidence is threaded through. -/
theorem all_entries_admitted (n : Nat) :
    At (recipeLaws []) (fun evidence => evidence) (allEntriesBody n) HandlerExamples.context := by
  apply At.handler_retaining_interfaces originalSources bounds declaration_recipes
    (fun _ => rfl) (fun _ => rfl)
  let underHandler := originalSources.after_handler (effect := effectE) (table := resumeTable)
    (families := resumeDependencies) (required := []) (fun _ => rfl) (fun _ => rfl)
  apply At.cleanup_retaining_interfaces underHandler
  · intro request member
    exact List.mem_singleton.mpr (congrArg Prod.fst (List.mem_singleton.mp member))
  · let underCleanup := underHandler.after_cleanup
      (show SourceScheduledAdaptationCompilation.RequestFootprint
        (.request (effect := effectE) (operation := 0)) [(effectE, 0)] from .request) .request [effectE]
    apply At.resource_retaining_interfaces underCleanup
    intro identity _fresh
    exact .sequence (nested_admitted n _ (underCleanup.after_resource identity)
      (fun _ => rfl) (fun _ => rfl))

theorem all_entries_generated (n : Nat) :
    ∃ annotation : Code [] (allEntriesPlan n) HandlerExamples.whole,
      annotation.Valid [] actions phases ∧
      Generated actions HandlerExamples.context.continuationBounds (allEntriesBody n) annotation := by
  apply (all_entries_admitted n).generate_source (resumeRequired := []) (closeRequired := [])
  refine ⟨rfl, ⟨?_, rfl⟩⟩
  intro identity _fresh
  refine ⟨?_, nested_checked n _ _ rfl⟩
  simp [SourceContextualHints.checkRequirements, SourceContextualHints.checkCapability,
    SourceDependencyCapture.select, SourceDependencyCapture.Selection.prepend]

end Ash.OneShot.SourceConsumingCleanupAdmission.InterfaceNestingExamples

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.InterfaceNestingExamples.nested_admitted
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.InterfaceNestingExamples.nested_checked
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.InterfaceNestingExamples.nested_generated
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.InterfaceNestingExamples.nested_scheduled
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.InterfaceNestingExamples.callbacks_nested_scheduled
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.InterfaceNestingExamples.consumed_nested_rejected

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.InterfaceNestingExamples.mixed_admitted
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.InterfaceNestingExamples.mixed_generated

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.InterfaceNestingExamples.interleaved_admitted
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.InterfaceNestingExamples.interleaved_generated

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.InterfaceNestingExamples.resource_admitted
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.InterfaceNestingExamples.resource_generated
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.InterfaceNestingExamples.all_entries_admitted
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.InterfaceNestingExamples.all_entries_generated
