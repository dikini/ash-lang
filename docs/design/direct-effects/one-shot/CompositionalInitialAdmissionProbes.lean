import CoreCallableCompositionalAdmissionFacets
import CoreCallableCompositionalResourceRoot
import CoreCallableFiniteCellPortABI
namespace Ash.OneShot.CompositionalInitialAdmissionProbes
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableCompositionalAdmissionFacets
open SourceDeclarationPlans (Plan)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
local instance : SourcePlannedChecks.DeclarationPolicy :=
  SourceScheduledCleanupInterfaces.Lexical.Recursive.declarationPolicy
namespace Root
abbrev original := CoreCallableCompositionalResourceRoot.original
abbrev graph := CoreCallableCompositionalResourceRoot.graph
abbrev expression := CoreCallableCompositionalResourceRoot.rootCode
abbrev annotation := CoreCallableCompositionalResourceRoot.initializerAnnotation
abbrev body := CoreCallableCompositionalResourceRoot.body
abbrev globals := CoreCallableCompositionalResourceRoot.globals
abbrev policy := CoreCallableCompositionalResourceRoot.policy
end Root
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- SAME 23-node graph and full higher-order bodies; no new fixture. -/
theorem exact_graph : CoreSyntax.checkShape Root.graph = .ok () ∧
    CoreTranslation.translate Root.graph = .ok Root.expression :=
  ⟨CoreCallableCompositionalResourceRoot.original_graph_shape,
    CoreCallableCompositionalResourceRoot.original_graph_translation⟩

def rootCheck := check Root.annotation Root.body CoreCallableFiniteCellRegistry.original Root.policy 17 3 []

/-- Rich Source requirements and computed accounting root stay separate. Every
full private Plan/Rows component and old lexical slot is the original one. -/
theorem original_full_indices : ∃ program : CoreCallableInitialAdmission.Program Root.globals (fun _ => none) [] Root.expression,
    rootCheck = .ok program ∧
    HEq program.plan CoreCallableCompositionalResourceRoot.rootPlan ∧
    HEq program.rows CoreCallableCompositionalResourceRoot.rootRows ∧
    HEq program.requirements CoreCallableCompositionalResourceRoot.rootRequirements ∧
    HEq program.root (Account.requirements (.choice .done .done)) ∧
    program.row = [] := by
  obtain ⟨outer,outerAccepted⟩ := CoreCallableGeneralResourceInitialRoot.original_initializer_checked
  obtain ⟨resource,resourceAccepted⟩ := CoreCallableCompositionalResourceRoot.compositional_checked
  have initialValid : quietCheck (annotationRecipe Root.annotation) = true := by decide +kernel
  have bodyValid : cellCheck 3 (CoreCallableCompositionalResourceRoot.checkingOf Root.body) = true := rfl
  have usage : usageCheck Root.expression = true := rfl
  have support : CoreCallableGraphAnnotationChecks.subsetB
      (ScopedPorts.Support.evaluate ScopedPorts.Support.empty Root.expression.dependencies) [] = true := rfl
  have accountEq : rootAccount Root.annotation Root.body = Account.choice .done .done := by decide +kernel
  have evaluated : RecursiveRequirements.evaluate [] [] (OwnerPhaseTransitions.available [])
      (SourceScheduledCleanupInterfaces.Lexical.Recursive.annotateDisposals (rootAccount Root.annotation Root.body).requirements) = some ([] : Footprint) := by
    rw [accountEq]
    simp [Account.requirements, SourceScheduledCleanupInterfaces.Lexical.Recursive.annotateDisposals,
      RecursiveRequirements.evaluate, RecursiveRequirements.evaluateFuel, ProtectionResiduals.merge, OwnerSource.exportAt, ProtectionResiduals.residualize, OwnerPhaseTransitions.project]
  unfold rootCheck check
  simp only [CoreCallableFiniteCellInitialRoot.initial] at outerAccepted
  simp only [CoreCallableCompositionalResourceRoot.policy, Root.policy] at outerAccepted ⊢
  rw [outerAccepted,resourceAccepted]
  dsimp only
  split
  next h =>
    split
    next h =>
      split
      next h =>
        split
        next h =>
          split
          next absent =>
            simp [evaluated] at absent
          next row found =>
            have rowEq : row = [] := Option.some.inj (found.symm.trans evaluated)
            subst row
            split
            next bounded =>
              refine ⟨_,rfl,HEq.rfl,HEq.rfl,HEq.rfl,?_,rfl⟩
              exact heq_of_eq (congrArg Account.requirements accountEq)
            next refused => exact False.elim (refused rfl)
        next h => exact False.elim (h support)
      next h => exact False.elim (h usage)
    next h => exact False.elim (h bodyValid)
  next h => exact False.elim (h initialValid)

theorem original_root_checked : ∃ program : CoreCallableInitialAdmission.Program Root.globals (fun _ => none) [] Root.expression,
    rootCheck = .ok program := by
  obtain ⟨program,accepted,_⟩ := original_full_indices
  exact ⟨program,accepted⟩

theorem same_root_initial_step :
    ∃ program : CoreCallableInitialAdmission.Program Root.globals (fun _ => none) [] Root.expression,
      rootCheck = .ok program ∧ ∃ registry after,
        NamedAccessStep [] ⟨⟨⟨Root.expression,.none,.nil⟩,[],[]⟩,[]⟩ after ∧
        ScopedPortJoint.Valid (CoreCallableContractExecution.lowerOperations Root.globals).ports
          Root.policy registry [] after program.result.port [] := by
  obtain ⟨program,accepted⟩ := original_root_checked
  have builtins := CoreCallableFiniteCellPortABI.compatibility_port_abi
    (policy := Root.policy) (owners := Root.globals.owners)
    CoreCallableGeneralResourceInitialRoot.original_compatibility
  rcases program.initial_progress builtins with value | ⟨registry,after,step,joint⟩
  · cases value
  · exact ⟨program,accepted,registry,after,step,joint⟩

/-- Produced family on SAME Checking/Plan/full Rows at every fresh identity. -/
theorem all_fresh_root_body : ∀ identity, Facets [] (fun _ => none) [] (OwnerPhaseTransitions.available []) [identity] [] []
    ((CoreCallableCompositionalResourceRoot.checkingOf Root.body).rows identity)
    (Contextual.Context.cell (identity := identity) Contextual.Context.nil)
    (checkingAccount (CoreCallableCompositionalResourceRoot.checkingOf Root.body) .done) :=
  fun identity => fresh_facets (world := []) _ (binder := 3) rfl identity

/-- Declaration RecipeTag.request is structurally certified, but the exact
closed request cannot denote every fresh cell in this one-cell context. -/
def unavailable := CoreCallableCompositionalResourceBody.Checking.closed
  (Plan.request (effect := .cell 99) (operation := 0)) Rows.request CoreCallableStaticProducer.RecipeTag.request

theorem unavailable_request_rejected : check_opened unavailable 3 [] [] [] [] (fun _ => none) []
    (OwnerPhaseTransitions.available []) = .error .bodyContext := rfl

def unsupportedInvoke := CoreCallableCompositionalResourceBody.Checking.closed
  (Plan.invoke (key := ⟨7,.resume⟩)) Rows.invoke CoreCallableStaticProducer.RecipeTag.invoke

theorem invocation_without_cut_rejected : check_opened unsupportedInvoke 3 [] [] [] [] (fun _ => none) []
    (OwnerPhaseTransitions.available []) = .error .bodyContext := rfl

/-- Full opaque choice rows are interpreted structurally, never replaced by
pure or by an erased port. Their computed choice root remains visible. -/
def opaqueChoice := CoreCallableCompositionalResourceBody.Checking.closed
  (Plan.choice Plan.pure Plan.pure) (CoreCallableContractSource.choiceRows Rows.pure Rows.pure)
  (CoreCallableStaticProducer.RecipeTag.choice .pure .pure)

theorem opaque_choice_checked : ∃ receipt, check_opened opaqueChoice 3 [] [] [] [] (fun _ => none) []
    (OwnerPhaseTransitions.available []) = .ok receipt := ⟨_,rfl⟩

theorem opaque_choice_accounting : checkingAccount opaqueChoice .done = .choice .done .done := rfl

theorem wrong_resource_name_rejected : check_opened
    (.request (.cell (.bound 4)) 0) 3 [] [] [] [] (fun _ => none) [] (OwnerPhaseTransitions.available []) = .error .bodyContext := rfl

theorem invalid_api_rejected : check Root.annotation Root.body
    {CoreCallableFiniteCellRegistry.original with binder := 1} Root.policy 17 3 [] =
      .error (.outer .incompatibleRegistry) := rfl

#print axioms exact_graph
#print axioms original_root_checked
#print axioms original_full_indices
#print axioms same_root_initial_step
#print axioms all_fresh_root_body
#print axioms unavailable_request_rejected
#print axioms invocation_without_cut_rejected
#print axioms opaque_choice_checked
#print axioms opaque_choice_accounting
#print axioms wrong_resource_name_rejected
#print axioms invalid_api_rejected
end Ash.OneShot.CompositionalInitialAdmissionProbes
