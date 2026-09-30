import SourceConsumingHandlerInterference

/-! Exact source obligations for adding an effectful cleanup callback to a
captured scope. Existing callbacks retain their routes; only the new callback
adds route obligations. Scheduling its code remains a separate source check. -/
namespace Ash.OneShot.SourceCleanupClosingInsertion
open SourceDependencyCapture
open SourceRecursiveRoutes (Shape Closing)
open SourceResourceRoutes (Route)
open SourceHandlerClosingInsertion (closing_append_iff)
open SourceDependencyOwners (owners PendingWithin)

/-- The callback observes the suffix after its registration point, in both
the original and closing interpretations. Prefix callbacks are unchanged. -/
theorem inserted_closing_iff (front tail : Scope) :
    Closing outward (front.append (.cleanup needs callback tail)).shape original surviving ↔
      Closing outward (front.append tail).shape original surviving ∧
        (∀ effect ∈ needs, ∃ target,
          Route outward (tail.shape.normal ++ original) effect target ∧
          Route outward (tail.shape.closing ++ surviving) effect target) := by
  rw [closing_append_iff, closing_append_iff]
  simp only [Scope.shape, Shape.normal, Shape.closing]
  constructor
  · rintro ⟨before, after⟩
    cases after with
    | cleanup routes rest => exact ⟨⟨before, rest⟩, routes⟩
  · rintro ⟨⟨before, after⟩, routes⟩
    exact ⟨before, .cleanup routes after⟩

/-- The new obligation is executable over the declared callback effects and
the actual suffix. It is not a successful whole-source successor check. -/
theorem check_closing_inserted (front tail : Scope) :
    checkClosing outward (front.append (.cleanup needs callback tail)).shape original surviving =
      (checkClosing outward (front.append tail).shape original surviving &&
        needs.all (sameRoute outward (tail.shape.normal ++ original) (tail.shape.closing ++ surviving))) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, check_closing_iff, List.all_eq_true, same_route_iff]
  exact inserted_closing_iff front tail

theorem inserted_held (front : Scope) :
    (front.append (.cleanup needs callback tail)).held = (front.append tail).held := by
  induction front <;> simp_all [Scope.append, Scope.held]

/-- Cleanup is not an interpretation delimiter. A selected outside handler
keeps its exact contract, modes and waiting suffix. -/
theorem selected_outside (passed : SourceHandlerRequirements.reaches requested front = true)
    (found : select requested operation outside = some (.handler captured tail contract modes)) :
    select requested operation (front.append (.cleanup needs callback outside)) =
      some (.handler (front.append (.cleanup needs callback captured)) tail contract modes) := by
  apply SourceHandlerSelection.selected_outside
    (selected := .handler (.cleanup needs callback captured) tail contract modes) passed
  simp only [select, found, Option.map_some, Selection.prepend]

/-- Exact finite factorization of the capture checker at the registration
site. Non-disposing requests acquire no extra closing obligation. -/
theorem check_capture_inserted (passed : SourceHandlerRequirements.reaches requested front = true)
    (found : select requested operation outside = some (.handler captured tail contract modes)) :
    checkCapture outward (front.append (.cleanup needs callback outside)) requested operation =
      (checkCapture outward (front.append outside) requested operation &&
        (!contract.dispose || needs.all (sameRoute outward captured.shape.normal captured.shape.closing))) := by
  have before := SourceHandlerSelection.selected_outside passed found
  have after := selected_outside (needs := needs) (callback := callback) passed found
  simp only [checkCapture, before, after, Selection.prepend, inserted_held,
    check_closing_inserted, List.append_nil]
  cases contract.dispose <;> simp [Bool.and_assoc]

/-- A later disposing capture requires precisely the new callback's matching
routes through the captured suffix. No new continuation right is introduced. -/
theorem guard_transport (passed : SourceHandlerRequirements.reaches requested front = true)
    (found : select requested operation outside = some (.handler captured tail contract modes))
    (checked : CaptureGuard outward (front.append outside) requested operation)
    (routes : contract.dispose = true → ∀ effect ∈ needs, ∃ target,
      Route outward captured.shape.normal effect target ∧
      Route outward captured.shape.closing effect target) :
    CaptureGuard outward (front.append (.cleanup needs callback outside)) requested operation := by
  have before := SourceHandlerSelection.selected_outside passed found
  have after := selected_outside (needs := needs) (callback := callback) passed found
  cases checked with
  | builtin actual => cases Option.some.inj (before.symm.trans actual)
  | handler actual permission row body closing =>
      cases Option.some.inj (before.symm.trans actual)
      have held := inserted_held (needs := needs) (callback := callback) (tail := captured) front
      refine .handler after (held ▸ permission) (held ▸ row) (held ▸ body) ?_
      intro disposes
      apply (inserted_closing_iff front captured).mpr
      exact ⟨closing disposes, by simpa only [List.append_nil] using routes disposes⟩

/-- Necessity at the same selected request. Merely knowing that the callback
operation is available in the original receiver is insufficient. -/
theorem guard_requires_routes (passed : SourceHandlerRequirements.reaches requested front = true)
    (found : select requested operation outside = some (.handler captured tail contract modes))
    (checked : CaptureGuard outward (front.append (.cleanup needs callback outside)) requested operation)
    (disposes : contract.dispose = true) :
    ∀ effect ∈ needs, ∃ target,
      Route outward captured.shape.normal effect target ∧
      Route outward captured.shape.closing effect target := by
  have after := selected_outside (needs := needs) (callback := callback) passed found
  cases checked with
  | builtin actual => cases Option.some.inj (after.symm.trans actual)
  | handler actual permission row body closing =>
      cases Option.some.inj (after.symm.trans actual)
      simpa only [List.append_nil] using
        ((inserted_closing_iff front captured).mp (closing disposes)).2

/-- Registration retains the exact continuation-owner inventory, including
order and multiplicity of dormant owners. Cleanup ownership is accounted for
separately by the existing runtime plan theorem. -/
theorem inserted_owners (front : Scope) :
    owners (front.append (.cleanup needs callback tail)) = owners (front.append tail) := by
  induction front <;> simp_all [Scope.append, owners]

/-- Existing pending code retains its owner bound. This judgment does not
check callback code; its declaration and scheduling checks remain necessary. -/
theorem pending_within (front : Scope)
    (checked : PendingWithin world owned (front.append tail)) :
    PendingWithin world owned (front.append (.cleanup needs callback tail)) := by
  induction front with
  | nil => exact .cleanup checked
  | plain code rest ih => cases checked with | plain code tail => exact .plain code (ih tail)
  | handler effect table families rest ih => cases checked with | handler tail => exact .handler (ih tail)
  | cell identity rest ih => cases checked with | cell tail => exact .cell (ih tail)
  | cleanup needs code rest ih => cases checked with | cleanup tail => exact .cleanup (ih tail)
  | running rest ih => cases checked with | running tail => exact .running (ih tail)
  | live owner saved rest ihSaved ihRest => cases checked with | live saved tail => exact .live saved (ihRest tail)
  | spent owner rest ih => cases checked with | spent tail => exact .spent (ih tail)

/-- Connect the new source rule to the existing runtime closing and ownership
proofs. The actual plan includes the registered callback and its cleanup owner;
resource support and typing are checked independently on that same stack. -/
theorem realized_interfaces
    {front tail : Scope}
    (realized : SourceRecursiveRoutes.Realizes (front.append (.cleanup needs callback tail)).shape stack plan)
    (closing : Closing outward (front.append tail).shape originalContext survivingContext)
    (routes : ∀ effect ∈ needs, ∃ target,
      Route outward (tail.shape.normal ++ originalContext) effect target ∧
      Route outward (tail.shape.closing ++ survivingContext) effect target)
    (originalScope : SourceRecursiveRoutes.Scope originalContext original)
    (survivingScope : SourceRecursiveRoutes.Scope survivingContext surviving)
    (supported : Supported stack.erase (original.visible ++ resources))
    (available : original.visible ⊆ surviving.visible ++ resources)
    (typed : ScopedPorts.StackTyped signature tickets world stack input output) :
    ScopedPorts.PlanTyped signature world (SourceRecursiveRoutes.scopeProviders survivingContext ++ outward) plan ∧
      Admission.OpenCloses stack.erase original surviving resources outward (plan.map ScopedExecution.CloseEntry.erase) ∧
      (planOwners (plan.map ScopedExecution.CloseEntry.erase)).Perm stack.erase.owners := by
  obtain ⟨planTyped, closes⟩ := realized.interfaces
    ((inserted_closing_iff front tail).mpr ⟨closing, routes⟩)
    originalScope survivingScope supported available typed
  exact ⟨planTyped, closes, realized.owner_accounting⟩

/-- Every validated request annotation must satisfy the new callback's route
condition at its selected disposing capture. This reuses the source compiler
and does not assume any particular annotation constructor. -/
theorem request_requires_routes
    [declarations : SourceScheduledCapabilityAnnotations.DeclarationPolicy]
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    (laws : SourceScheduledCapabilityAnnotations.DeclarationLaws declarations admission certification outward)
    {front outside captured tail : Scope}
    {hints : SourceContextualHints.Hints (front.append (.cleanup needs callback outside))}
    {forest : SourceRetainedPlans.Forest hints}
    (annotation : SourceScheduledCapabilityAnnotations.Code world
      (.request (effect := requested) (operation := operation)) forest)
    (checked : annotation.Valid outward actions phases)
    (passed : SourceHandlerRequirements.reaches requested front = true)
    (found : select requested operation outside = some (.handler captured tail contract modes))
    (disposes : contract.dispose = true) :
    ∀ effect ∈ needs, ∃ target,
      Route outward captured.shape.normal effect target ∧
      Route outward captured.shape.closing effect target := by
  have scheduled := annotation.compile_with laws checked
  cases scheduled with
  | request guard closing =>
      exact guard_requires_routes passed found
        (check_capture_iff.mp (SourceDependencySchemes.checked_request guard)) disposes

namespace Examples
open SourceDependencyCapture.Examples (resumeTable resumeDependencies disposeTable disposeDependencies)

def callbackEffect : Instance := .cell 4
def disposingEffect : Instance := .user 502 []
def delimiter : Scope := .handler disposingEffect disposeTable disposeDependencies .nil
def removedReceiver : Scope := .handler callbackEffect resumeTable resumeDependencies delimiter
def retainedReceiver : Scope := .cell 4 delimiter

def removedHints : SourceContextualHints.Hints removedReceiver := .handler [] (.handler [] .nil)
def removedForest : SourceRetainedPlans.Forest removedHints := .handler (.handler .nil)

def originalRequest : SourceScheduledCapabilityAnnotations.Code [4]
    (.request (effect := disposingEffect) (operation := 0)) removedForest :=
  .selected (.handler (by decide) (.hit rfl rfl))
    (fun _ => .handler (.handler .nil)) (fun _ => .operations .nil)

def callbackSource : SourceScheduledCapabilityAnnotations.Code [4]
    (.request (effect := callbackEffect) (operation := 0)) (.running removedForest) :=
  .operations [(callbackEffect, 0)] .request .request

/-- Both original source pieces validate independently. Their conjunction
does not establish safe insertion of the callback into the saved computation. -/
theorem original_pieces_valid :
    originalRequest.Valid [] actions phases ∧ callbackSource.Valid [] actions phases :=
  ⟨⟨rfl, fun _ => rfl⟩, rfl⟩

/-- The callback operation is available before capture, but its handler would
be removed during disposal. Availability alone cannot admit the new cleanup. -/
theorem available_callback_rejected :
    SourceContextualHints.checkRequirements removedReceiver [(callbackEffect, 0)] = true ∧
      checkCapture [] removedReceiver disposingEffect 0 = true ∧
      checkCapture [] (.cleanup [callbackEffect] (.request callbackEffect 0) removedReceiver) disposingEffect 0 = false :=
  ⟨rfl, rfl, rfl⟩

/-- A builtin in the captured suffix supplies the same callback before and
after closing. This is an effectful callback, not the pure-cleanup special case. -/
theorem retained_builtin_accepted :
    checkCapture [] (.cleanup [callbackEffect] (.request callbackEffect 0) retainedReceiver) disposingEffect 0 = true := by
  apply check_capture_iff.mpr
  apply guard_transport (front := .nil) (outside := retainedReceiver)
    (captured := retainedReceiver) (tail := .nil)
    (contract := ⟨true, some [], none⟩)
    (modes := (some SourceDependencyCapture.Examples.disposeFamily, none)) rfl rfl (check_capture_iff.mp rfl)
  intro _ effect member
  have same := List.mem_singleton.mp member
  exact ⟨some 4, .cell same, .cell same⟩

def retainedHints : SourceContextualHints.Hints retainedReceiver := .cell (.handler [] .nil)
def retainedForest : SourceRetainedPlans.Forest retainedHints := .cell (.handler .nil)

/-- Here the full selected-request annotation includes the effectful callback
schedule, in addition to the finite closing guard. -/
def retainedRequest : SourceScheduledCapabilityAnnotations.Code [4]
    (.request (effect := disposingEffect) (operation := 0))
    (.cleanup (needs := [callbackEffect]) (.request (effect := callbackEffect) (operation := 0)) retainedForest) :=
  .selected (.cleanup (.cell (by decide) (.hit rfl rfl)))
    (fun _ => .cleanup (.cell (.handler .nil)))
    (fun _ => .cleanup (.operations [(callbackEffect, 0)] .request .request) (.cell (.operations .nil)))

theorem retained_request_valid : retainedRequest.Valid [] actions phases :=
  ⟨retained_builtin_accepted, fun _ => ⟨rfl, rfl⟩⟩

/-- Changing the source annotation cannot repair the removed-handler example.
The rejection follows from the mandatory structural route premise. -/
theorem request_annotation_rejected
    [declarations : SourceScheduledCapabilityAnnotations.DeclarationPolicy]
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    (laws : SourceScheduledCapabilityAnnotations.DeclarationLaws declarations admission certification [])
    {hints : SourceContextualHints.Hints (.cleanup [callbackEffect] (.request callbackEffect 0) removedReceiver)}
    {forest : SourceRetainedPlans.Forest hints}
    (annotation : SourceScheduledCapabilityAnnotations.Code world
      (.request (effect := disposingEffect) (operation := 0)) forest) :
    ¬ annotation.Valid [] actions phases := by
  intro checked
  have scheduled := annotation.compile_with laws checked
  cases scheduled with
  | request guard closing =>
      have accepted := SourceDependencySchemes.checked_request guard
      change false = true at accepted
      cases accepted

end Examples

end Ash.OneShot.SourceCleanupClosingInsertion

#print axioms Ash.OneShot.SourceCleanupClosingInsertion.inserted_closing_iff
#print axioms Ash.OneShot.SourceCleanupClosingInsertion.check_closing_inserted
#print axioms Ash.OneShot.SourceCleanupClosingInsertion.inserted_held
#print axioms Ash.OneShot.SourceCleanupClosingInsertion.selected_outside
#print axioms Ash.OneShot.SourceCleanupClosingInsertion.check_capture_inserted
#print axioms Ash.OneShot.SourceCleanupClosingInsertion.guard_transport
#print axioms Ash.OneShot.SourceCleanupClosingInsertion.guard_requires_routes
#print axioms Ash.OneShot.SourceCleanupClosingInsertion.inserted_owners
#print axioms Ash.OneShot.SourceCleanupClosingInsertion.pending_within
#print axioms Ash.OneShot.SourceCleanupClosingInsertion.realized_interfaces
#print axioms Ash.OneShot.SourceCleanupClosingInsertion.request_requires_routes
#print axioms Ash.OneShot.SourceCleanupClosingInsertion.Examples.available_callback_rejected
#print axioms Ash.OneShot.SourceCleanupClosingInsertion.Examples.original_pieces_valid
#print axioms Ash.OneShot.SourceCleanupClosingInsertion.Examples.retained_builtin_accepted
#print axioms Ash.OneShot.SourceCleanupClosingInsertion.Examples.retained_request_valid
#print axioms Ash.OneShot.SourceCleanupClosingInsertion.Examples.request_annotation_rejected
