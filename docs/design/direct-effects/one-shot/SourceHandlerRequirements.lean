import SourceContextualHints

/-! Finite operation requirements at a retained scope's interpretation
boundary. Matching handlers block lookup even when an operation is absent.
The existing capability checker remains the authority for selected modes. -/
namespace Ash.OneShot.SourceHandlerRequirements
open ScopedExpressions
open SourceDependencyCapture
open SourceContextualHints (Hints Requirement checkCapability checkRequirements)

/-- Whether lookup can reach the outside of this active scope. Dormant saved
branches are not searched for an operation. -/
def reaches (effect : Instance) : Scope → Bool
  | .nil => true
  | .handler other _ _ rest => if effect = other then false else reaches effect rest
  | .cell identity rest => if effect = .cell identity then false else reaches effect rest
  | .plain _ rest | .cleanup _ _ rest | .running rest | .live _ _ rest | .spent _ rest => reaches effect rest

/-- Capability checking ignores the accumulated capture but keeps the exact
selected contract and its ordinary/protected dependency families. -/
theorem capability_prepend (found : select effect operation first =
    (select effect operation second).map (Selection.prepend layer)) :
    checkCapability first effect operation = checkCapability second effect operation := by
  unfold checkCapability
  rw [found]
  cases select effect operation second with
  | none => rfl
  | some selected => cases selected <;> rfl

/-- An active prefix either supplies the capability itself or passes lookup
to the outside. Failure at a matching handler is not a pass-through case. -/
theorem capability_append (front : Scope) :
    checkCapability (front.append outside) effect operation =
      if reaches effect front then checkCapability outside effect operation
      else checkCapability front effect operation := by
  induction front with
  | nil => rfl
  | handler other table families rest ih =>
      by_cases same : effect = other
      · simp only [Scope.append, reaches, if_pos same, Bool.false_eq_true, ↓reduceIte]
        unfold checkCapability
        simp only [select, if_pos same]
        cases ProtectionContracts.lookup operation table <;> cases lookupDependencies operation families <;> rfl
      · have first := capability_prepend (effect := effect) (operation := operation) (first := .handler other table families (rest.append outside))
          (second := rest.append outside) (layer := .handler other table families) (if_neg same)
        have second := capability_prepend (effect := effect) (operation := operation) (first := .handler other table families rest)
          (second := rest) (layer := .handler other table families) (if_neg same)
        simpa only [Scope.append, reaches, if_neg same, first, second] using ih
  | cell identity rest ih =>
      by_cases same : effect = .cell identity
      · simp [Scope.append, reaches, same, checkCapability, select]
      · have first := capability_prepend (effect := effect) (operation := operation) (first := .cell identity (rest.append outside))
          (second := rest.append outside) (layer := .cell identity) (if_neg same)
        have second := capability_prepend (effect := effect) (operation := operation) (first := .cell identity rest)
          (second := rest) (layer := .cell identity) (if_neg same)
        simpa only [Scope.append, reaches, if_neg same, first, second] using ih
  | plain dependencies rest ih =>
      have first := capability_prepend (effect := effect) (operation := operation) (first := .plain dependencies (rest.append outside)) (second := rest.append outside) rfl
      have second := capability_prepend (effect := effect) (operation := operation) (first := .plain dependencies rest) (second := rest) rfl
      simpa only [Scope.append, reaches, first, second] using ih
  | cleanup needs callback rest ih =>
      have first := capability_prepend (effect := effect) (operation := operation) (first := .cleanup needs callback (rest.append outside)) (second := rest.append outside) rfl
      have second := capability_prepend (effect := effect) (operation := operation) (first := .cleanup needs callback rest) (second := rest) rfl
      simpa only [Scope.append, reaches, first, second] using ih
  | running rest ih =>
      have first := capability_prepend (effect := effect) (operation := operation) (first := .running (rest.append outside)) (second := rest.append outside) rfl
      have second := capability_prepend (effect := effect) (operation := operation) (first := .running rest) (second := rest) rfl
      simpa only [Scope.append, reaches, first, second] using ih
  | live owner saved rest ihSaved ih =>
      have first := capability_prepend (effect := effect) (operation := operation) (first := .live owner saved (rest.append outside)) (second := rest.append outside) rfl
      have second := capability_prepend (effect := effect) (operation := operation) (first := .live owner saved rest) (second := rest) rfl
      simpa only [Scope.append, reaches, first, second] using ih
  | spent owner rest ih =>
      have first := capability_prepend (effect := effect) (operation := operation) (first := .spent owner (rest.append outside)) (second := rest.append outside) rfl
      have second := capability_prepend (effect := effect) (operation := operation) (first := .spent owner rest) (second := rest) rfl
      simpa only [Scope.append, reaches, first, second] using ih

/-- Filter a finite operation interface by actual active interpretation
scopes, retaining precisely the requests that reach the boundary. -/
def outwardRequirements (front : Scope) (required : List Requirement) : List Requirement :=
  required.filter (fun request => reaches request.1 front)

theorem requirements_outward
    (checked : checkRequirements (front.append outside) required = true) :
    checkRequirements outside (outwardRequirements front required) = true := by
  apply List.all_eq_true.mpr
  intro request member
  obtain ⟨included, passed⟩ := List.mem_filter.mp member
  have supplied := List.all_eq_true.mp checked request included
  simpa only [capability_append, passed, ↓reduceIte] using supplied

theorem requirements_transport
    (checked : checkRequirements (front.append before) required = true)
    (supplied : checkRequirements after (outwardRequirements front required) = true) :
    checkRequirements (front.append after) required = true := by
  apply List.all_eq_true.mpr
  intro request member
  by_cases passed : reaches request.1 front = true
  · simpa only [capability_append, passed, ↓reduceIte] using
      List.all_eq_true.mp supplied request (List.mem_filter.mpr ⟨member, passed⟩)
  · have old := List.all_eq_true.mp checked request member
    simpa only [capability_append, if_neg passed] using old

theorem requirements_replace_iff
    (checked : checkRequirements (front.append before) required = true) :
    checkRequirements (front.append after) required = true ↔
      checkRequirements after (outwardRequirements front required) = true :=
  ⟨requirements_outward, requirements_transport checked⟩

/-- Installed-handler requests exposed at the outer boundary. A saved
branch is analyzed at its actual receiving suffix; builtin shielding and
matching source handlers are retained when filtering requests. -/
def exposed : {scope : Scope} → Hints scope → List Requirement
  | _, .nil => []
  | _, .plain rest | _, .cell rest | _, .cleanup rest | _, .running rest | _, .spent rest => exposed rest
  | .handler _ _ _ restScope, .handler required rest => outwardRequirements restScope required ++ exposed rest
  | .live _ _ restScope, .live saved rest => outwardRequirements restScope (exposed saved) ++ exposed rest

theorem exposed_requirements (hints : Hints scope) (checked : hints.check outside = true) :
    checkRequirements outside (exposed hints) = true := by
  induction hints generalizing outside with
  | nil => rfl
  | plain rest ih | cell rest ih | cleanup rest ih | running rest ih | spent rest ih => exact ih checked
  | handler required rest ih =>
      simp only [Hints.check, Bool.and_eq_true] at checked
      simp only [exposed, checkRequirements, List.all_append, Bool.and_eq_true]
      exact ⟨requirements_outward checked.1, ih checked.2⟩
  | live saved rest ihSaved ihRest =>
      simp only [Hints.check, Bool.and_eq_true] at checked
      simp only [exposed, checkRequirements, List.all_append, Bool.and_eq_true]
      exact ⟨requirements_outward (ihSaved checked.1), ihRest checked.2⟩

theorem check_transport (hints : Hints scope) (checked : hints.check before = true)
    (supplied : checkRequirements after (exposed hints) = true) : hints.check after = true := by
  induction hints generalizing before after with
  | nil => rfl
  | plain rest ih | cell rest ih | cleanup rest ih | running rest ih | spent rest ih => exact ih checked supplied
  | handler required rest ih =>
      simp only [Hints.check, Bool.and_eq_true] at checked ⊢
      simp only [exposed, checkRequirements, List.all_append, Bool.and_eq_true] at supplied
      exact ⟨requirements_transport checked.1 supplied.1, ih checked.2 supplied.2⟩
  | live saved rest ihSaved ihRest =>
      simp only [Hints.check, Bool.and_eq_true] at checked ⊢
      simp only [exposed, checkRequirements, List.all_append, Bool.and_eq_true] at supplied
      exact ⟨ihSaved checked.1 (requirements_transport (exposed_requirements saved checked.1) supplied.1),
        ihRest checked.2 supplied.2⟩

/-- Once the retained scope's internal requirements are established, its
finite exposed interface exactly characterizes a replacement outside scope. -/
theorem check_replace_iff (hints : Hints scope) (checked : hints.check before = true) :
    hints.check after = true ↔ checkRequirements after (exposed hints) = true :=
  ⟨exposed_requirements hints, check_transport hints checked⟩

def intercepted (effect : Instance) (required : List Requirement) : List Requirement :=
  required.filter (fun request => decide (request.1 = effect))

theorem capability_handler :
    checkCapability (.handler installed table families outside) effect operation =
      if effect = installed then checkCapability (.handler installed table families .nil) effect operation
      else checkCapability outside effect operation := by
  have composed := capability_append (outside := outside) (effect := effect) (operation := operation)
    (.handler installed table families .nil)
  by_cases same : effect = installed <;> simpa only [Scope.append, reaches, same, Bool.false_eq_true, ↓reduceIte] using composed

/-- The inserted table must supply each intercepted operation with the same
independent capability required by the existing checker. Unrelated requests
retain their former outside interpretation. -/
theorem requirements_handler_insert
    (checked : checkRequirements outside required = true) :
    checkRequirements (.handler effect table families outside) required = true ↔
      checkRequirements (.handler effect table families .nil) (intercepted effect required) = true := by
  constructor
  · intro supplied
    apply List.all_eq_true.mpr
    intro request member
    obtain ⟨included, same⟩ := List.mem_filter.mp member
    have equal := of_decide_eq_true same
    have capability := List.all_eq_true.mp supplied request included
    rw [capability_handler, if_pos equal] at capability
    exact capability
  · intro supplied
    apply List.all_eq_true.mpr
    intro request member
    by_cases same : request.1 = effect
    · have localCapability := List.all_eq_true.mp supplied request
        (List.mem_filter.mpr ⟨member, by simpa using same⟩)
      rw [capability_handler, if_pos same]
      exact localCapability
    · rw [capability_handler, if_neg same]
      exact List.all_eq_true.mp checked request member

/-- Insert a handler at any position in the receiving context. Only exposed
requests that pass its preceding scope and match its effect need a new table
capability. Missing operations never fall through to the old outside. -/
theorem check_handler_insert (hints : Hints scope)
    (checked : hints.check (front.append outside) = true) :
    hints.check (front.append (.handler effect table families outside)) = true ↔
      checkRequirements (.handler effect table families .nil)
        (intercepted effect (outwardRequirements front (exposed hints))) = true := by
  have oldRequired := exposed_requirements hints checked
  rw [check_replace_iff hints checked, requirements_replace_iff oldRequired]
  exact requirements_handler_insert (requirements_outward oldRequired)

namespace Examples

private def F : Instance := .user 4 []
private def G : Instance := .user 5 []
private def table : List (Nat × ProtectionContracts.ClauseContract) := [(0, ⟨false, some [], some []⟩)]
private def families : SourceDependencyAnnotations.ClauseDependencies :=
  [(0, some (fun owner => .invoke ⟨owner, .resume⟩), some (fun owner => .invoke ⟨owner, .resume⟩))]
private def outside : Scope := .handler F table families .nil
private def waiting : Hints (.handler G table families .nil) := .handler [(F, 0)] .nil

theorem old_requirement_checked : waiting.check outside = true := rfl

/-- Identical complete capabilities may take over the operation; this does
not assert identity of the chosen handler or its behavior. -/
theorem complete_override : waiting.check (.handler F table families outside) = true := by
  apply (check_handler_insert waiting (front := .nil) old_requirement_checked).mpr
  rfl

theorem missing_operation_rejected : waiting.check (.handler F [] [] outside) = false := rfl

theorem missing_protected_mode_rejected :
    waiting.check (.handler F [(0, ⟨false, some [], none⟩)] families outside) = false := rfl

theorem disposing_capability_rejected :
    waiting.check (.handler F [(0, ⟨true, some [], some []⟩)] families outside) = false := rfl

private def dormant : Hints (.live 9 (.handler G table families .nil) .nil) := .live waiting .nil

theorem dormant_requirement_retained : exposed dormant = [(F, 0)] := rfl

theorem dormant_override_rejected : dormant.check (.handler F [] [] outside) = false := rfl

/-- A nearer builtin prevents the new incomplete handler from taking over
this cell operation. A dormant provider would not be on this lookup path. -/
private def cellWaiting : Hints (.handler G table families (.cell 7 .nil)) :=
  .handler [(.cell 7, 0)] (.cell .nil)

theorem builtin_shielded : exposed cellWaiting = [] ∧
    cellWaiting.check (.handler (.cell 7) [] [] .nil) = true := ⟨rfl, rfl⟩

private def dormantCell : Hints (.handler G table families (.live 9 (.cell 7 .nil) .nil)) :=
  .handler [(.cell 7, 0)] (.live (.cell .nil) .nil)

theorem dormant_builtin_does_not_shield : exposed dormantCell = [(.cell 7, 0)] ∧
    dormantCell.check (.cell 7 .nil) = true ∧
    dormantCell.check (.handler (.cell 7) [] [] (.cell 7 .nil)) = false := ⟨rfl, rfl, rfl⟩

private def blocked : Hints (.handler G table families (.handler F [] [] .nil)) :=
  .handler [(F, 0)] (.handler [] .nil)

/-- An empty exposed interface does not establish the internal checks:
a nearer incomplete handler still blocks the old valid outside provider. -/
theorem baseline_required : exposed blocked = [] ∧ blocked.check outside = false := ⟨rfl, rfl⟩

end Examples

end Ash.OneShot.SourceHandlerRequirements

#print axioms Ash.OneShot.SourceHandlerRequirements.capability_prepend
#print axioms Ash.OneShot.SourceHandlerRequirements.capability_append
#print axioms Ash.OneShot.SourceHandlerRequirements.requirements_outward
#print axioms Ash.OneShot.SourceHandlerRequirements.requirements_transport
#print axioms Ash.OneShot.SourceHandlerRequirements.requirements_replace_iff
#print axioms Ash.OneShot.SourceHandlerRequirements.exposed_requirements
#print axioms Ash.OneShot.SourceHandlerRequirements.check_transport
#print axioms Ash.OneShot.SourceHandlerRequirements.check_replace_iff
#print axioms Ash.OneShot.SourceHandlerRequirements.capability_handler
#print axioms Ash.OneShot.SourceHandlerRequirements.requirements_handler_insert
#print axioms Ash.OneShot.SourceHandlerRequirements.check_handler_insert
#print axioms Ash.OneShot.SourceHandlerRequirements.Examples.old_requirement_checked
#print axioms Ash.OneShot.SourceHandlerRequirements.Examples.complete_override
#print axioms Ash.OneShot.SourceHandlerRequirements.Examples.missing_operation_rejected
#print axioms Ash.OneShot.SourceHandlerRequirements.Examples.missing_protected_mode_rejected
#print axioms Ash.OneShot.SourceHandlerRequirements.Examples.disposing_capability_rejected
#print axioms Ash.OneShot.SourceHandlerRequirements.Examples.dormant_requirement_retained
#print axioms Ash.OneShot.SourceHandlerRequirements.Examples.dormant_override_rejected
#print axioms Ash.OneShot.SourceHandlerRequirements.Examples.builtin_shielded
#print axioms Ash.OneShot.SourceHandlerRequirements.Examples.dormant_builtin_does_not_shield
#print axioms Ash.OneShot.SourceHandlerRequirements.Examples.baseline_required
