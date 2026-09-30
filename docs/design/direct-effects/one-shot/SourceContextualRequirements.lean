import SourceContextualClauses
import SourceContextualHints
import SourceDependencyProviders
import SourceHandlerSelection
import SourceDeclarationPlans

/-! Finite operation requirements retained by contextual clause proofs.
Rechecking a receiving stack reconstructs the certificate from its structural
recipe. This is proof annotation data, not another computation syntax. Source
admission and storage of these recipes in the runtime invariant remain separate.
The request-prefix rule currently uses resume-only operation capabilities. -/
namespace Ash.OneShot.SourceContextualRequirements
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations (Dependencies ClauseDependencies)
open SourceDependencyCapture
open SourceContextualClauses (RequestCapability FamilyAt ModeAt DeclarationsAt)
abbrev Receiving := SourceDependencyCapture.Scope
export SourceContextualHints (Requirement checkCapability checkRequirements)

private theorem present_iff (value : Option α) : value.isSome = true ↔ ∃ item, value = some item := by
  cases value <;> simp

/-- The executable test checks exactly the independently defined operation
capability, including nearest lookup and both protection modes. -/
theorem check_capability_iff : checkCapability tail effect operation = true ↔ RequestCapability effect operation tail := by
  cases found : select effect operation tail with
  | none =>
      constructor
      · simp [checkCapability, found]
      · intro capability
        cases capability with
        | builtin actual | handler actual => rw [found] at actual; cases actual
  | some selected => cases selected with
      | builtin identity => exact ⟨fun _ => .builtin found, fun _ => by simp [checkCapability, found]⟩
      | handler captured outside contract modes =>
          constructor
          · intro checked
            simp only [checkCapability, found, Bool.and_eq_true, present_iff] at checked
            rcases checked with ⟨⟨⟨⟨resumesOnly, ordinaryRow⟩, protectedRow⟩, ordinaryBody⟩, protectedBody⟩
            have permission : contract.dispose = false := by
              cases actual : contract.dispose <;> simp_all
            exact .handler found permission
              (fun held => by cases held; exact ordinaryRow; exact protectedRow)
              (fun held => by cases held; exact ordinaryBody; exact protectedBody)
          · intro capability
            cases capability with
            | builtin actual => rw [found] at actual; cases Option.some.inj actual
            | handler actual permission rows bodies =>
                cases Option.some.inj (found.symm.trans actual)
                obtain ⟨r0, row0⟩ := rows false
                obtain ⟨r1, row1⟩ := rows true
                obtain ⟨f0, body0⟩ := bodies false
                obtain ⟨f1, body1⟩ := bodies true
                simp [checkCapability, found, permission, row0, row1, body0, body1]

theorem check_requirements_iff : checkRequirements tail required = true ↔
    ∀ request ∈ required, RequestCapability request.1 request.2 tail := by
  simp only [checkRequirements, List.all_eq_true, check_capability_iff]

/-- Requirements use membership, not multiplicity. This says nothing about
exchanging interpretations in the receiving stack or duplicating an owner. -/
theorem check_requirements_subset (included : first ⊆ second)
    (checked : checkRequirements tail second = true) : checkRequirements tail first = true :=
  check_requirements_iff.mpr (fun request member => check_requirements_iff.mp checked request (included member))

theorem check_requirements_equiv (same : ∀ request, request ∈ first ↔ request ∈ second) :
    checkRequirements tail first = true ↔ checkRequirements tail second = true :=
  ⟨check_requirements_subset (fun request member => (same request).mpr member),
    check_requirements_subset (fun request member => (same request).mp member)⟩

/-- An ordered local-provider prefix. Membership supplies a builtin operation;
this annotation does not authorize exchanging arbitrary interpretations. -/
def providerScope : List Nat → Receiving → Receiving
  | [], scope => scope
  | identity :: rest, scope => .cell identity (providerScope rest scope)

theorem provider_checked (provided : List Nat)
    (checked : SourceDependencySchemes.Checked outward actions phases world dependencies scope) :
    SourceDependencySchemes.Checked outward actions phases world dependencies (providerScope provided scope) := by
  induction provided with
  | nil => exact checked
  | cons identity rest ih =>
      exact SourceDependencyProviders.local_transport ih
        (hints := SourceDependencyNeutral.bare _) (.here (identity := identity))

theorem provider_capability (provided : List Nat)
    (capability : RequestCapability effect operation scope) :
    RequestCapability effect operation (providerScope provided scope) := by
  induction provided with
  | nil => exact capability
  | cons identity rest ih =>
      exact check_capability_iff.mp
        ((SourceProviderInsertion.Insertion.here (identity := identity)
          (before := SourceDependencyNeutral.bare _)).capability (check_capability_iff.mpr ih))

theorem provider_member (member : identity ∈ provided) :
    RequestCapability (.cell identity) operation (providerScope provided scope) := by
  induction provided with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with same | inside
      · subst first
        exact .builtin (identity := identity) (by simp [providerScope, select])
      · exact provider_capability [first] (ih inside)

/-- Any preceding scope through which this effect passes preserves the
selected operation capability. Lookup retains its full captured prefix. -/
theorem capability_prefix (passed : SourceHandlerRequirements.reaches effect front = true)
    (capability : RequestCapability effect operation scope) :
    RequestCapability effect operation (front.append scope) := by
  cases capability with
  | builtin found => exact .builtin (SourceHandlerSelection.selected_outside passed found)
  | handler found resumes rows bodies =>
      exact .handler (SourceHandlerSelection.selected_outside passed found) resumes rows bodies

theorem capability_plain (capability : RequestCapability effect operation scope) :
    RequestCapability effect operation (.plain dependencies scope) :=
  capability_prefix (front := .plain dependencies .nil) rfl capability

theorem capability_live (capability : RequestCapability effect operation scope) :
    RequestCapability effect operation (.live owner saved scope) :=
  capability_prefix (front := .live owner saved .nil) rfl capability

/-- A reusable operation capability checks a request at its actual receiving
scope. Its source-handler case cannot dispose the newly captured continuation. -/
theorem request_checked (capability : RequestCapability effect operation scope) :
    SourceDependencySchemes.Checked outward actions phases world (.request effect operation) scope := by
  cases capability with
  | builtin found =>
      rename_i identity
      have projected : select effect operation (SourceDependencyProjection.project scope) = some (.builtin identity) := by
        rw [SourceDependencyProjection.project_select, found]
        rfl
      refine SourceDependencyChecks.Local.request (.builtin projected) ?_ ?_
      · intro saved tail contract modes looked
        rw [projected] at looked
        cases looked
      · intro saved tail contract modes looked
        rw [projected] at looked
        cases looked
  | handler found resumes rows bodies =>
      rename_i captured tail contract modes
      have projected : select effect operation (SourceDependencyProjection.project scope) =
          some (.handler (SourceDependencyProjection.project captured) (SourceDependencyProjection.project tail) contract modes) := by
        rw [SourceDependencyProjection.project_select, found]
        rfl
      refine SourceDependencyChecks.Local.request_selected projected ?_ ?_ ?_
      · apply check_capture_iff.mpr
        obtain ⟨row, rowFound⟩ := rows _
        obtain ⟨family, bodyFound⟩ := bodies _
        exact .handler projected (by simp [modeCheck, resumes]) rowFound bodyFound
          (by intro impossible; simp [resumes] at impossible)
      · intro impossible; simp [resumes] at impossible
      · intro impossible; simp [resumes] at impossible

/-- Fresh local allocation extends the world of the same captured source.
Existing retained-source weakening supplies each field. -/
theorem capture_source_world
    (source : SourceDependencySchemes.CaptureSource outward actions phases world owner rights captured tail)
    (larger : world ⊆ nextWorld) :
    SourceDependencySchemes.CaptureSource outward actions phases nextWorld owner rights captured tail := by
  refine ⟨?_, ?_, ?_⟩
  · intro permission
    exact SourceDependencySchemes.pending_transport (source.saved permission)
      (fun _ available => available) (fun _ _ known => known) larger
  · exact SourceDependencySchemes.pending_transport source.waiting
      (fun _ available => available) (fun _ _ known => known) larger
  · intro permission
    obtain ⟨held, closes, scheduled⟩ := source.disposal permission
    exact ⟨held, closes, SourceDependencySchemes.pending_transport scheduled
      (fun _ available => available) (fun _ _ known => known) larger⟩

/-- This operation captures only its newly installed handler. The arbitrary
receiving suffix supplies neither its operation nor its closing obligations. -/
theorem handled_request_checked :
    SourceDependencySchemes.Checked outward actions phases world
      (SourceDeclarationPlans.HandledRequest.dependencies effect operation) scope := by
  open SourceDeclarationPlans.HandledRequest in
    have selected : select effect operation (.handler effect (table operation) (families operation)
        (SourceDependencyProjection.project scope)) =
        some (.handler (.handler effect (table operation) (families operation) .nil)
          (SourceDependencyProjection.project scope) ⟨true, some [], none⟩ (some family, none)) := by
      simp [select, table, families, lookup, lookupDependencies]
    exact .handler (.sequence .pure (SourceDependencyChecks.Local.request_selected selected
      (check_capture_iff.mpr (.handler selected rfl rfl rfl (fun _ => .handler .nil)))
      (fun _ => .nil) (fun _ => .handler .nil)))

/-- Each constructor records source structure and independent continuation
permission. No constructor accepts an arbitrary successful future-body proof.
Operation requirements use the existing single sequencing calculus. -/
inductive Recipe (outward : List Instance) (rights : Syntax.OneShotRights) :
    List Requirement → (Nat → Dependencies) → (provided : List Nat := []) → Prop where
  | resume (permission : rights.resume = true) :
      Recipe outward rights [] (fun owner => .invoke ⟨owner, .resume⟩) provided
  | dispose (permission : rights.dispose = true) :
      Recipe outward rights [] (fun owner => .invoke ⟨owner, .dispose⟩) provided
  | silent (recipe : Recipe outward rights required family provided) (silent : dependencies.Silent) :
      Recipe outward rights required (fun owner => .sequence dependencies (family owner)) provided
  | request (recipe : Recipe outward rights required family provided) :
      Recipe outward rights ((effect, operation) :: required)
        (fun owner => .sequence (.sequence .pure (.request effect operation)) (family owner)) provided
  | localRequest (member : identity ∈ provided) (recipe : Recipe outward rights required family provided) :
      Recipe outward rights required
        (fun owner => .sequence (.sequence .pure (.request (.cell identity) operation)) (family owner)) provided
  | handledRequest (recipe : Recipe outward rights required family provided) :
      Recipe outward rights required
        (fun owner => .sequence (SourceDeclarationPlans.HandledRequest.dependencies effect operation) (family owner)) provided
  | resource {family : Nat → Nat → Dependencies} (body : ∀ identity, Recipe outward rights required (fun owner => family owner identity) (identity :: provided)) :
      Recipe outward rights required (fun owner => .resource (family owner)) provided
  | cleanup (recipe : Recipe outward rights required family provided) :
      Recipe outward rights required (fun owner => .cleanup [] .pure (family owner)) provided
  | choice (left : Recipe outward rights firstRequired first provided) (right : Recipe outward rights secondRequired second provided) :
      Recipe outward rights (firstRequired ++ secondRequired) (fun owner => .choice (first owner) (second owner)) provided

/-- The local-provider index is interpreted as the actual ordered caller
prefix. Resource bodies may request that provider without exporting the request
to the original waiting tail. Captured-source checks are reused and weakened. -/
theorem Recipe.compile_providers (recipe : Recipe outward rights required family provided)
    (supplied : ∀ request ∈ required, RequestCapability request.1 request.2 tail)
    (known : actions owner = some rights) (available : phases owner = .available)
    (source : SourceDependencySchemes.CaptureSource outward actions phases world owner rights captured tail) :
    SourceDependencySchemes.Checked outward actions phases world (family owner)
      (providerScope provided (.live owner captured tail)) := by
  induction recipe generalizing world with
  | resume permission =>
      exact provider_checked _ ((SourceDependencySchemes.resume_family permission).instantiate known available source)
  | dispose permission =>
      exact provider_checked _ ((SourceDependencySchemes.dispose_family permission).instantiate known available source)
  | silent recipe empty ih => exact .sequence (.silent empty) (ih supplied source)
  | request recipe ih =>
      exact .sequence (.sequence .pure (request_checked (capability_plain
        (provider_capability _ (capability_live (supplied _ List.mem_cons_self))))))
        (ih (fun request member => supplied request (List.mem_cons_of_mem _ member)) source)
  | localRequest member recipe ih =>
      exact .sequence (.sequence .pure (request_checked (capability_plain (provider_member member)))) (ih supplied source)
  | handledRequest recipe ih =>
      exact .sequence (handled_request_checked (scope := .plain _ (providerScope _ (.live owner captured tail))))
        (ih supplied source)
  | resource body ih =>
      apply SourceDependencyChecks.Local.resource
      intro identity fresh
      exact ih identity supplied (capture_source_world source (List.subset_append_left _ _))
  | cleanup recipe ih => exact SourceDependencyNeutral.pure_cleanup (ih supplied source)
  | choice left right ihLeft ihRight =>
      exact .choice (ihLeft (fun request member => supplied request (List.mem_append_left _ member)) source)
        (ihRight (fun request member => supplied request (List.mem_append_right _ member)) source)

/-- Declarations start with no locally supplied resource. Their resource rules
introduce providers only inside the corresponding resource body. -/
theorem Recipe.compile (recipe : Recipe outward rights required family)
    (supplied : ∀ request ∈ required, RequestCapability request.1 request.2 tail) :
    FamilyAt outward rights family tail :=
  .checked (fun _ _ _ _ _ known available source => recipe.compile_providers supplied known available source)

theorem Recipe.recheck (recipe : Recipe outward rights required family)
    (checked : checkRequirements tail required = true) : FamilyAt outward rights family tail :=
  recipe.compile (check_requirements_iff.mp checked)

inductive ModeRecipe (outward : List Instance) (rights : Syntax.OneShotRights) :
    List Requirement → Option (Nat → Dependencies) → Prop where
  | unavailable : ModeRecipe outward rights [] none
  | available (recipe : Recipe outward rights required family) : ModeRecipe outward rights required (some family)

inductive DeclarationRecipes (outward : List Instance) :
    Clauses → ClauseDependencies → List Requirement → Prop where
  | nil : DeclarationRecipes outward .nil [] []
  | cons (ordinary : ModeRecipe outward body.requiredActions ordinaryRequired ordinaryFamily)
      (protectedMode : ModeRecipe outward body.requiredActions protectedRequired protectedFamily)
      (rest : DeclarationRecipes outward clauses families restRequired) :
      DeclarationRecipes outward (.cons operation parameter binder body clauses)
        ((operation, ordinaryFamily, protectedFamily) :: families)
        (ordinaryRequired ++ protectedRequired ++ restRequired)

theorem ModeRecipe.compile (recipe : ModeRecipe outward rights required family)
    (supplied : ∀ request ∈ required, RequestCapability request.1 request.2 tail) :
    ModeAt outward rights tail family := by
  cases recipe with
  | unavailable => exact .unavailable
  | available recipe => exact .available (recipe.compile supplied)

theorem DeclarationRecipes.compile (recipes : DeclarationRecipes outward clauses families required)
    (supplied : ∀ request ∈ required, RequestCapability request.1 request.2 tail) :
    DeclarationsAt outward tail clauses families := by
  induction recipes with
  | nil => exact .nil
  | cons ordinary protectedMode rest ih =>
      exact .cons
        (ordinary.compile (fun request member => supplied request (List.mem_append_left _ (List.mem_append_left _ member))))
        (protectedMode.compile (fun request member => supplied request (List.mem_append_left _ (List.mem_append_right _ member))))
        (ih (fun request member => supplied request (List.mem_append_right _ member)))

theorem DeclarationRecipes.recheck (recipes : DeclarationRecipes outward clauses families required)
    (checked : checkRequirements tail required = true) : DeclarationsAt outward tail clauses families :=
  recipes.compile (check_requirements_iff.mp checked)

namespace Examples

/-- Both offered modes retain the actual primitive consumption derivation. -/
theorem resume_declarations : DeclarationRecipes outward
    SourceDependencySchemes.Examples.resumeClauses SourceDependencyCapture.Examples.resumeDependencies [] :=
  .cons (.available (.silent (.resume rfl) .pure))
    (.available (.silent (.resume rfl) .pure)) .nil

/-- An arbitrary semantic family can prove checking without recording a
continuation action. Such evidence is no longer a recipe constructor. -/
theorem pure_semantic_family : SourceDependencySchemes.ClauseFamily outward rights (fun _ => .pure) :=
  .checked (fun _ _ _ _ _ _ _ _ _ => .pure)

/-- This negative case tests the admission boundary, not operational safety:
consuming recipes require an explicit consumption path. -/
theorem pure_not_a_consuming_recipe :
    ¬ Recipe outward rights required (fun _ => .pure) provided := by
  have notPure {family : Nat → Dependencies}
      (recipe : Recipe outward rights required family provided) : family 0 ≠ .pure := by
    cases recipe <;> simp
  intro recipe
  exact notPure recipe rfl

/-- Choice still admits either independently permitted one-shot action. -/
theorem mixed_consumption : Recipe outward ⟨true, true⟩ [] SourceDependencySchemes.Examples.mixedFamily :=
  .choice (.silent (.resume rfl) .pure) (.dispose rfl)

open SourceDependencyHandlerGap (effect rights family outside)

theorem clause_recipe : Recipe outward rights [(effect, 0)] family :=
  .request (.silent (.resume rfl) .pure)

theorem declaration_recipes : DeclarationRecipes outward
    SourceDependencyHandlerGap.clauses SourceDependencyHandlerGap.dependencies [(effect, 0)] :=
  .cons (ordinaryRequired := [(effect, 0)]) (.available clause_recipe) .unavailable .nil

def caller : Receiving → Receiving :=
  .handler (.user 103 []) [] [] ∘ .plain .pure

/-- A nonempty caller prefix can be checked at the new receiving stack.
Its unrelated handler and pending computation are retained in that stack. -/
theorem caller_rechecked : DeclarationsAt outward (caller (.spent 19 outside))
    SourceDependencyHandlerGap.clauses SourceDependencyHandlerGap.dependencies :=
  declaration_recipes.recheck (by decide)

/-- A compatible nearer interpretation may satisfy the same requirements;
the certificate is rebuilt for that interpretation, not silently transported. -/
theorem compatible_override : FamilyAt outward rights family
    (SourceDependencyCapture.Examples.handlerF outside) := clause_recipe.recheck (by decide)

theorem repeated_requirements : checkRequirements outside [(effect, 0), (effect, 0)] = true := by decide

theorem missing_operation_rejected : checkRequirements (.handler effect [] [] outside) [(effect, 0)] = false := by decide

theorem disposing_override_rejected : checkRequirements
    (.handler effect SourceDependencyCapture.Examples.disposeTable SourceDependencyCapture.Examples.disposeDependencies outside)
    [(effect, 0)] = false := by decide

end Examples
end Ash.OneShot.SourceContextualRequirements

#print axioms Ash.OneShot.SourceContextualRequirements.check_capability_iff
#print axioms Ash.OneShot.SourceContextualRequirements.check_requirements_iff
#print axioms Ash.OneShot.SourceContextualRequirements.check_requirements_subset
#print axioms Ash.OneShot.SourceContextualRequirements.check_requirements_equiv
#print axioms Ash.OneShot.SourceContextualRequirements.Recipe.compile
#print axioms Ash.OneShot.SourceContextualRequirements.Recipe.recheck
#print axioms Ash.OneShot.SourceContextualRequirements.ModeRecipe.compile
#print axioms Ash.OneShot.SourceContextualRequirements.DeclarationRecipes.compile
#print axioms Ash.OneShot.SourceContextualRequirements.DeclarationRecipes.recheck
#print axioms Ash.OneShot.SourceContextualRequirements.Examples.clause_recipe
#print axioms Ash.OneShot.SourceContextualRequirements.Examples.declaration_recipes
#print axioms Ash.OneShot.SourceContextualRequirements.Examples.caller_rechecked
#print axioms Ash.OneShot.SourceContextualRequirements.Examples.compatible_override
#print axioms Ash.OneShot.SourceContextualRequirements.Examples.repeated_requirements
#print axioms Ash.OneShot.SourceContextualRequirements.Examples.missing_operation_rejected
#print axioms Ash.OneShot.SourceContextualRequirements.Examples.disposing_override_rejected

#print axioms Ash.OneShot.SourceContextualRequirements.provider_checked

#print axioms Ash.OneShot.SourceContextualRequirements.provider_capability

#print axioms Ash.OneShot.SourceContextualRequirements.provider_member

#print axioms Ash.OneShot.SourceContextualRequirements.capability_plain

#print axioms Ash.OneShot.SourceContextualRequirements.capability_live

#print axioms Ash.OneShot.SourceContextualRequirements.request_checked

#print axioms Ash.OneShot.SourceContextualRequirements.capture_source_world

#print axioms Ash.OneShot.SourceContextualRequirements.Recipe.compile_providers

#print axioms Ash.OneShot.SourceContextualRequirements.capability_prefix

#print axioms Ash.OneShot.SourceContextualRequirements.handled_request_checked

#print axioms Ash.OneShot.SourceContextualRequirements.Examples.resume_declarations
#print axioms Ash.OneShot.SourceContextualRequirements.Examples.pure_semantic_family
#print axioms Ash.OneShot.SourceContextualRequirements.Examples.pure_not_a_consuming_recipe
#print axioms Ash.OneShot.SourceContextualRequirements.Examples.mixed_consumption

namespace Ash.OneShot.SourceContextualRequirements.Lexical
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations (Dependencies ClauseDependencies)
open SourceDependencyCapture
open SourceDependencyChecks.Lexical (Local)
open SourceDependencySchemes.Lexical (CaptureSource)
open SourceContextualClauses (RequestCapability)
open SourceContextualClauses.Lexical (FamilyAt ModeAt DeclarationsAt)

/-- The existing provider-prefix syntax and lookup laws are unchanged. -/
theorem provider_checked (provided : List Nat)
    (checked : Local outward actions phases world dependencies scope) :
    Local outward actions phases world dependencies (providerScope provided scope) := by
  induction provided with
  | nil => exact checked
  | cons identity rest ih =>
      exact SourceDependencyProviders.Lexical.local_transport ih
        (hints := SourceDependencyNeutral.bare _) (.here (identity := identity))

theorem request_checked (capability : RequestCapability effect operation scope) :
    Local outward actions phases world (.request effect operation) scope := by
  cases capability with
  | builtin found =>
      apply Local.request (.builtin found)
      all_goals
        intro saved tail contract modes looked disposes
        cases Option.some.inj (found.symm.trans looked)
  | handler found resumes rows bodies =>
      obtain ⟨row, rowFound⟩ := rows _
      obtain ⟨family, bodyFound⟩ := bodies _
      apply Local.request (.handler found (by simp [modeCheck, resumes]) rowFound bodyFound)
      all_goals
        intro saved tail contract modes looked disposes
        cases Option.some.inj (found.symm.trans looked)
        simp [resumes] at disposes

theorem capture_source_world
    (source : CaptureSource outward actions phases world owner rights captured tail)
    (larger : world ⊆ nextWorld) :
    CaptureSource outward actions phases nextWorld owner rights captured tail := by
  refine ⟨fun permission => (source.saved permission).world_weaken larger,
    source.waiting.world_weaken larger, ?_⟩
  intro permission
  obtain ⟨held, callbacks⟩ := source.disposal permission
  exact ⟨held, callbacks.world_weaken larger⟩

theorem handled_request_checked :
    Local outward actions phases world
      (SourceDeclarationPlans.HandledRequest.dependencies effect operation) scope := by
  open SourceDeclarationPlans.HandledRequest in
    have selected : select effect operation (.handler effect (table operation) (families operation) scope) =
        some (.handler (.handler effect (table operation) (families operation) .nil)
          scope ⟨true, some [], none⟩ (some family, none)) := by
      simp [select, table, families, lookup, lookupDependencies]
    apply Local.handler
    apply Local.sequence .pure
    apply Local.request (.handler selected rfl rfl rfl)
    · intro saved tail contract modes looked disposes
      cases Option.some.inj (selected.symm.trans looked)
      exact .handler .nil
    · intro saved tail contract modes looked disposes
      cases Option.some.inj (selected.symm.trans looked)
      exact .handler .nil

theorem pure_cleanup (body : Local outward actions phases world dependencies scope) :
    Local outward actions phases world (.cleanup [] .pure dependencies) scope :=
  .cleanup (SourceDependencyNeutral.Lexical.local_transport body
    (hints := SourceDependencyNeutral.bare _) (.completion .refl)) .pure

/-- Reuse every existing recipe constructor with the lexical source checks.
This compiles supplied structural annotations, not arbitrary source inference. -/
theorem compile_recipe_providers (recipe : Recipe outward rights required family provided)
    (supplied : ∀ request ∈ required, RequestCapability request.1 request.2 tail)
    (known : actions owner = some rights) (available : phases owner = .available)
    (source : CaptureSource outward actions phases world owner rights captured tail) :
    Local outward actions phases world (family owner)
      (providerScope provided (.live owner captured tail)) := by
  induction recipe generalizing world with
  | resume permission =>
      exact provider_checked _ ((SourceDependencySchemes.Lexical.resume_family permission).instantiate known available source)
  | dispose permission =>
      exact provider_checked _ ((SourceDependencySchemes.Lexical.dispose_family permission).instantiate known available source)
  | silent recipe empty ih => exact .sequence (.silent empty) (ih supplied source)
  | request recipe ih =>
      exact .sequence (.sequence .pure (request_checked (capability_plain
        (provider_capability _ (capability_live (supplied _ List.mem_cons_self))))))
        (ih (fun request member => supplied request (List.mem_cons_of_mem _ member)) source)
  | localRequest member recipe ih =>
      exact .sequence (.sequence .pure (request_checked (capability_plain (provider_member member)))) (ih supplied source)
  | handledRequest recipe ih =>
      exact .sequence (handled_request_checked (scope := .plain _ (providerScope _ (.live owner captured tail))))
        (ih supplied source)
  | resource body ih =>
      apply Local.resource
      intro identity fresh
      exact ih identity supplied (capture_source_world source (List.subset_append_left _ _))
  | cleanup recipe ih => exact pure_cleanup (ih supplied source)
  | choice left right ihLeft ihRight =>
      exact .choice (ihLeft (fun request member => supplied request (List.mem_append_left _ member)) source)
        (ihRight (fun request member => supplied request (List.mem_append_right _ member)) source)

theorem compile_recipe (recipe : Recipe outward rights required family)
    (supplied : ∀ request ∈ required, RequestCapability request.1 request.2 tail) :
    FamilyAt outward rights family tail :=
  .checked (fun _ _ _ _ _ known available source => compile_recipe_providers recipe supplied known available source)

theorem recheck_recipe (recipe : Recipe outward rights required family)
    (checked : checkRequirements tail required = true) : FamilyAt outward rights family tail :=
  compile_recipe recipe (check_requirements_iff.mp checked)

theorem compile_mode (recipe : ModeRecipe outward rights required family)
    (supplied : ∀ request ∈ required, RequestCapability request.1 request.2 tail) :
    ModeAt outward rights tail family := by
  cases recipe with
  | unavailable => exact .unavailable
  | available recipe => exact .available (compile_recipe recipe supplied)

theorem compile_declarations (recipes : DeclarationRecipes outward clauses families required)
    (supplied : ∀ request ∈ required, RequestCapability request.1 request.2 tail) :
    DeclarationsAt outward tail clauses families := by
  induction recipes with
  | nil => exact .nil
  | cons ordinary protectedMode rest ih =>
      exact .cons
        (compile_mode ordinary (fun request member => supplied request (List.mem_append_left _ (List.mem_append_left _ member))))
        (compile_mode protectedMode (fun request member => supplied request (List.mem_append_left _ (List.mem_append_right _ member))))
        (ih (fun request member => supplied request (List.mem_append_right _ member)))

theorem recheck_declarations (recipes : DeclarationRecipes outward clauses families required)
    (checked : checkRequirements tail required = true) : DeclarationsAt outward tail clauses families :=
  compile_declarations recipes (check_requirements_iff.mp checked)
end Ash.OneShot.SourceContextualRequirements.Lexical
#print axioms Ash.OneShot.SourceContextualRequirements.Lexical.provider_checked
#print axioms Ash.OneShot.SourceContextualRequirements.Lexical.request_checked
#print axioms Ash.OneShot.SourceContextualRequirements.Lexical.capture_source_world
#print axioms Ash.OneShot.SourceContextualRequirements.Lexical.handled_request_checked
#print axioms Ash.OneShot.SourceContextualRequirements.Lexical.pure_cleanup
#print axioms Ash.OneShot.SourceContextualRequirements.Lexical.compile_recipe_providers
#print axioms Ash.OneShot.SourceContextualRequirements.Lexical.compile_recipe
#print axioms Ash.OneShot.SourceContextualRequirements.Lexical.recheck_recipe
#print axioms Ash.OneShot.SourceContextualRequirements.Lexical.compile_mode
#print axioms Ash.OneShot.SourceContextualRequirements.Lexical.compile_declarations
#print axioms Ash.OneShot.SourceContextualRequirements.Lexical.recheck_declarations

namespace Ash.OneShot.SourceContextualRequirements.Lexical.Recursive
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations (Dependencies)
open SourceDependencyCapture (Scope select lookupDependencies modeDependencies)
open SourceDependencyChecks.Lexical (ReturnHints)
open SourceDependencyChecks.Lexical.ReturnHints.Recursive (Local Pending)
open SourceContextualClauses (RequestCapability)
open OwnerPhaseTransitions (Phases spend)

def providerHints (provided : List Nat) (hints : ReturnHints scope) : ReturnHints (providerScope provided scope) :=
  match provided with
  | [] => hints
  | identity :: rest => .cell (identity := identity) (providerHints rest hints)

theorem provider_checked (provided : List Nat)
    (checked : Local outward actions phases world dependencies hints) :
    Local outward actions phases world dependencies (providerHints provided hints) := by
  induction provided with
  | nil => exact checked
  | cons identity rest ih => exact SourceDependencyProviders.Lexical.Recursive.local_transport ih (.here (identity := identity))

theorem request_checked {hints : ReturnHints scope} (capability : RequestCapability effect operation scope) :
    Local outward actions phases world (.request effect operation) hints := by
  cases capability with
  | builtin found =>
      apply Local.request (.builtin found)
      · intro capturedScope tailScope captured tail contract modes same looked disposes
        cases Option.some.inj (found.symm.trans looked)
      · intro captured tail contract modes looked disposes
        cases Option.some.inj (found.symm.trans looked)
  | handler found resumes rows bodies =>
      obtain ⟨row, rowFound⟩ := rows _
      obtain ⟨family, bodyFound⟩ := bodies _
      apply Local.request (.handler found (by simp [modeCheck, resumes]) rowFound bodyFound)
      · intro capturedScope tailScope captured tail contract modes same looked disposes
        cases Option.some.inj (found.symm.trans looked)
        simp [resumes] at disposes
      · intro captured tail contract modes looked disposes
        cases Option.some.inj (found.symm.trans looked)
        simp [resumes] at disposes

theorem handled_request_checked {hints : ReturnHints scope} :
    Local outward actions phases world
      (SourceDeclarationPlans.HandledRequest.dependencies effect operation) hints := by
  open SourceDeclarationPlans.HandledRequest in
    have selected : select effect operation (.handler effect (table operation) (families operation) scope) =
        some (.handler (.handler effect (table operation) (families operation) .nil)
          scope ⟨true, some [], none⟩ (some family, none)) := by
      simp [select, table, families, lookup, lookupDependencies]
    have cut : SourceDependencyNeutral.Lexical.Recursive.Cut effect operation
        ⟨true, some [], none⟩ (some family, none)
        (.handler (effect := effect) (table := table operation) (families := families operation) hints)
        (.handler (effect := effect) (table := table operation) (families := families operation) .nil) hints :=
      .hit (by simp [table, lookup]) (by simp [families, lookupDependencies])
    apply Local.handler
    apply Local.sequence .pure
    apply Local.request (.handler selected rfl rfl rfl)
    · intro capturedScope tailScope captured tail contract modes same looked disposes
      cases Option.some.inj (selected.symm.trans looked)
      obtain ⟨rfl, rfl⟩ := cut.unique same
      exact .handler .nil
    · intro captured tail contract modes looked disposes
      cases Option.some.inj (selected.symm.trans looked)
      exact .handler .nil

/-- Compile the existing finite recipe grammar from independently checked
primitive continuation actions and operation requirements. No whole-body or
successor check is an input. Resource scopes and pure cleanups are retained. -/
theorem compile_recipe_providers {captured : ReturnHints capturedScope} {tail : ReturnHints tailScope}
    (recipe : Recipe outward rights required family provided)
    (supplied : ∀ request ∈ required, RequestCapability request.1 request.2 tailScope)
    (resume : rights.resume = true → Local outward actions phases world (.invoke ⟨owner, .resume⟩) (.live (owner := owner) captured tail))
    (dispose : rights.dispose = true → Local outward actions phases world (.invoke ⟨owner, .dispose⟩) (.live (owner := owner) captured tail)) :
    Local outward actions phases world (family owner) (providerHints provided (.live (owner := owner) captured tail)) := by
  induction recipe generalizing world with
  | resume permission => exact provider_checked _ (resume permission)
  | dispose permission => exact provider_checked _ (dispose permission)
  | silent recipe empty ih => exact .sequence (.silent empty) (ih supplied resume dispose)
  | request recipe ih =>
      exact .sequence (.sequence .pure (request_checked (capability_plain
        (provider_capability _ (capability_live (supplied _ List.mem_cons_self))))))
        (ih (fun request member => supplied request (List.mem_cons_of_mem _ member)) resume dispose)
  | localRequest member recipe ih =>
      exact .sequence (.sequence .pure (request_checked (capability_plain (provider_member member)))) (ih supplied resume dispose)
  | handledRequest recipe ih => exact .sequence handled_request_checked (ih supplied resume dispose)
  | resource body ih =>
      apply Local.resource
      intro identity fresh
      exact ih identity supplied
        (fun permission => SourceDependencySchemes.Lexical.Recursive.local_transport (resume permission)
          (fun _ ready => ready) (fun _ _ known => known) (List.subset_append_left _ _))
        (fun permission => SourceDependencySchemes.Lexical.Recursive.local_transport (dispose permission)
          (fun _ ready => ready) (fun _ _ known => known) (List.subset_append_left _ _))
  | cleanup recipe ih => exact SourceDependencyNeutral.Lexical.Recursive.pure_cleanup (ih supplied resume dispose)
  | choice left right ihLeft ihRight =>
      exact .choice (ihLeft (fun request member => supplied request (List.mem_append_left _ member)) resume dispose)
        (ihRight (fun request member => supplied request (List.mem_append_right _ member)) resume dispose)

theorem compile_recipe {captured : ReturnHints capturedScope} {tail : ReturnHints tailScope}
    (recipe : Recipe outward rights required family)
    (checked : checkRequirements tailScope required = true)
    (resume : rights.resume = true → Local outward actions phases world (.invoke ⟨owner, .resume⟩) (.live (owner := owner) captured tail))
    (dispose : rights.dispose = true → Local outward actions phases world (.invoke ⟨owner, .dispose⟩) (.live (owner := owner) captured tail)) :
    Local outward actions phases world (family owner) (.live (owner := owner) captured tail) :=
  compile_recipe_providers recipe (check_requirements_iff.mp checked) resume dispose

theorem mode_recipe_selected (recipe : ModeRecipe outward rights required alternative)
    (found : alternative = some family) : Recipe outward rights required family := by
  subst alternative
  cases recipe with | available body => exact body

/-- The operation and mode select a structural recipe for that exact clause;
its requirement list is a subset of the installed declaration's requirements. -/
theorem declaration_recipe_selected (recipes : DeclarationRecipes outward clauses families required)
    (selected : ClauseAt operation clauses parameter binder code)
    (found : (lookupDependencies operation families).bind (modeDependencies held) = some family) :
    ∃ needed, Recipe outward code.requiredActions needed family ∧ needed ⊆ required := by
  induction selected generalizing families required with
  | hit => cases recipes with
    | cons ordinary protectedMode rest =>
      simp only [lookupDependencies, if_true, Option.bind_some] at found
      cases held with
      | false => exact ⟨_, mode_recipe_selected ordinary found,
          fun _ member => List.mem_append_left _ (List.mem_append_left _ member)⟩
      | true => exact ⟨_, mode_recipe_selected protectedMode found,
          fun _ member => List.mem_append_left _ (List.mem_append_right _ member)⟩
  | pass different next ih => cases recipes with
    | cons ordinary protectedMode rest =>
      obtain ⟨needed, recipe, included⟩ := ih rest
        (by simpa only [lookupDependencies, if_neg different] using found)
      exact ⟨needed, recipe, fun _ member => List.mem_append_right _ (included member)⟩

theorem selected_clause_local {captured : ReturnHints capturedScope} {tail : ReturnHints tailScope}
    (recipes : DeclarationRecipes outward clauses families required)
    (selected : ClauseAt operation clauses parameter binder code)
    (found : (lookupDependencies operation families).bind (modeDependencies held) = some family)
    (checked : checkRequirements tailScope required = true)
    (resume : code.requiredActions.resume = true → Local outward actions phases world (.invoke ⟨owner, .resume⟩) (.live (owner := owner) captured tail))
    (dispose : code.requiredActions.dispose = true → Local outward actions phases world (.invoke ⟨owner, .dispose⟩) (.live (owner := owner) captured tail)) :
    Local outward actions phases world (family owner) (.live (owner := owner) captured tail) := by
  obtain ⟨needed, recipe, included⟩ := declaration_recipe_selected recipes selected found
  exact compile_recipe recipe (check_requirements_subset included checked) resume dispose
end Ash.OneShot.SourceContextualRequirements.Lexical.Recursive
#print axioms Ash.OneShot.SourceContextualRequirements.Lexical.Recursive.compile_recipe_providers
#print axioms Ash.OneShot.SourceContextualRequirements.Lexical.Recursive.selected_clause_local

namespace Ash.OneShot.SourceContextualRequirements
open ScopedExpressions
/-- Reuse the existing preservation of clause action rights under value
substitution. The finite recipe and its required operations stay unchanged. -/
theorem DeclarationRecipes.substitution (recipes : DeclarationRecipes outward clauses families required)
    (value : replacement.IsValue) (name : Nat) :
    DeclarationRecipes outward (clauses.subst name replacement) families required := by
  induction recipes with
  | nil => exact .nil
  | cons ordinary protectedMode rest ih =>
      simp only [Clauses.subst]
      split
      · exact .cons ordinary protectedMode ih
      · exact .cons
          (by simpa only [Code.substitution_required_actions _ name value] using ordinary)
          (by simpa only [Code.substitution_required_actions _ name value] using protectedMode) ih

/-- Existing instantiation preserves the clause's action rights. Recipes keep
the same dependency families, whose source authentication remains separate. -/
theorem DeclarationRecipes.instantiation (recipes : DeclarationRecipes outward clauses families required)
    (environment : Instantiation.Environment) :
    DeclarationRecipes outward (clauses.instantiate environment) families required := by
  induction recipes with
  | nil => exact .nil
  | cons ordinary protectedMode rest ih =>
      exact .cons
        (by simpa only [Code.instantiation_required_actions] using ordinary)
        (by simpa only [Code.instantiation_required_actions] using protectedMode) ih
end Ash.OneShot.SourceContextualRequirements
#print axioms Ash.OneShot.SourceContextualRequirements.DeclarationRecipes.substitution
#print axioms Ash.OneShot.SourceContextualRequirements.DeclarationRecipes.instantiation
