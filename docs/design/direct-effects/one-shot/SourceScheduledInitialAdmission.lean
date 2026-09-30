import SourceScheduledBuiltinSignatures

/-! Finite proof-carrying initial admission for the one-shot experiment.
All input judgments concern one closed source, its authenticated structural rows,
and their finite requirement interpretation. No machine state or successor is an
admission premise. This interface does not claim an inference algorithm. -/

namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Operations Contracts Value)
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open RecursiveRequirements (Requirements)
open SourceDependencyAnnotations (RowAnnotation)
open InstallationSupport

def contracts : Contracts := fun _ => none
def actions : Syntax.UsageTickets := fun _ => none
def annotations : Nat → Option SourceDependencyCapture.Scope := fun _ => none

def owners : ContractRows contracts := by intro owner contract known; cases known

def emptyRows : EnvironmentRows (fun _ => none) := by intro name value known; cases known

/-- A single authenticated source decoration supplies every static facet.
`Code` recursively checks lexical requests, continuation operations and cleanup;
`Run` interprets the same rows without assuming an execution or successor. Fresh
allocation premises are symbolic binders in these existing inductive judgments. -/
structure Program (operations : Operations) (policy : Syntax.TicketPolicy)
    (ports : OperationRows operations) (ambient : List Nat) (budget : Footprint)
    (expression : ScopedExpressions.Code) where
  result : Value
  resultRows : ValueRows result
  dependencies : SourceDependencyAnnotations.Dependencies
  plan : Plan dependencies
  rows : Rows (signature plan)
  demand : List Nat
  requirements : Requirements demand
  source : SourcePlannedSources.Expression operations policy contracts [] [] .none (fun _ => none)
    expression result demand requirements (signature plan)
  authenticated : Auth operations policy ports owners emptyRows source resultRows rows
  certified : SourcePlannedChecks.Certified (evidence := declarationPolicy) [] [] plan
  certificate : SourceAdmission.Code [] actions budget (OwnerPhaseTransitions.available []) [] [] rows Context.nil
  resourceChecked : CodeChecked ambient [] certificate
  rootDemand : List Nat
  root : Requirements rootDemand
  interpreted : Accounting.Run [] [] rows Context.nil root
  annotated : Requirements rootDemand
  annotation : RowAnnotation root annotated
  rootRow : Footprint
  checked : RecursiveRequirements.Checked [] [] (OwnerPhaseTransitions.available []) (annotateDisposals annotated) rootRow
  bounded : rootRow ⊆ budget
  resources : Syntax.resourceDependencies expression.dependencies ⊆ ambient
  builtinSignatures : SourceScheduledBuiltinSignatures.Compatible operations

/-- All execution bookkeeping starts empty; source resource references are
checked separately against the fixed ambient allowance. -/
def initialRun (expression : ScopedExpressions.Code) : LexicalUnwind.UseRunState :=
  ⟨⟨.eval ⟨expression, .none, .nil⟩, [], []⟩, actions⟩

def Program.site (program : Program operations policy ports ambient budget expression)
    (tables : CallableProtectionFrames.Tables) (families : SourceDependencyFrames.Families)
    (required : SourceContextualRechecking.Required) :
    ExecutionSite ambient operations policy contracts tables families required [] actions
      (OwnerPhaseTransitions.available []) [] [] [] budget ports owners emptyRows
      (.value program.result) (.value program.resultRows) :=
  { expression := expression, runtimeScope := .none, stack := .nil,
    result := program.result, resultRows := program.resultRows, allowed := [],
    dependencies := program.dependencies, plan := program.plan, rows := program.rows,
    sourceDemand := program.demand, sourceRequirements := program.requirements,
    receiving := .nil, hints := .nil, context := .nil,
    current := SourceAdmission.Admitted.of_source program.source program.authenticated program.certificate .nil,
    certified := program.certified, scopeTyped := ⟨.none, .none⟩,
    pendingDemand := [], pendingRequirements := .request [] [], pending := .nil,
    coherent := .nil, retained := .nil, currentResource := program.resourceChecked,
    retainedResource := .nil }

/-- Finite source admission constructs the complete current invariant, including
its installed-handler support. No transition-preservation theorem is used. -/
theorem Program.initial_state (program : Program operations policy ports ambient budget expression)
    (tables : CallableProtectionFrames.Tables) (families : SourceDependencyFrames.Families)
    (required : SourceContextualRechecking.Required) :
    InstallationState operations policy contracts tables families required [] annotations [] ambient [] [] [] [] budget
      ports owners emptyRows (.value program.result) (.value program.resultRows) (initialRun expression) := by
  let site := program.site tables families required
  refine ⟨⟨.eval site rfl (.contextual program.interpreted) .nil program.annotation program.checked program.bounded,
    ?_, ?_, .nil, ?_, ?_, .eval ⟨.nil _, program.resources⟩, ?_, ?_, ?_, ?_⟩, .nil _⟩
  · intro key body member; cases member
  · intro key body member; cases member
  · exact ⟨.refl [], List.nodup_nil⟩
  · exact empty_usage_registry_history
  · exact List.nil_subset _
  · exact List.nil_subset _
  · intro owner; exact Nat.le_refl 0
  · exact CaptureMetadataHistory.empty

/-- Closed programs supply neither external resources nor residual operations.
This is the public M2 endpoint; the generalized constructor above exposes any
nonempty ambient allowance or budget explicitly. -/
theorem Program.closed_initial_state (program : Program operations policy ports [] [] expression)
    (tables : CallableProtectionFrames.Tables) (families : SourceDependencyFrames.Families)
    (required : SourceContextualRechecking.Required) :
    InstallationState operations policy contracts tables families required [] annotations [] [] [] [] [] [] []
      ports owners emptyRows (.value program.result) (.value program.resultRows) (initialRun expression) :=
  program.initial_state tables families required

namespace Examples

def empty : Requirements [] := .request [] []
def application : ScopedExpressions.Code := .app (.lambda 2 .unit) .unit
def applicationPlan := Plan.sequence Plan.pure (Plan.sequence Plan.pure Plan.pure)
def applicationRequirements : Requirements [] := .emitAfter (.sequence empty empty) [] []
def callback : ScopedExpressions.Code := .lambda 1 .unit
def cleanup : ScopedExpressions.Code := .cleanup callback application
def cleanupPlan := Plan.sequence Plan.pure (Plan.cleanup (needs := []) Plan.pure applicationPlan)
def cleanupRequirements : Requirements [] := .emitAfter (.sequence empty applicationRequirements) [] []
def resource : ScopedExpressions.Code := .resource 0 (.integer 5) cleanup
def resourcePlan := Plan.sequence Plan.pure (Plan.resource (fun _ => cleanupPlan))
def resourceRequirements : Requirements [] := .sequence empty cleanupRequirements

theorem lambdaSource (parameter : Nat) :
    SourcePlannedSources.Expression operations policy contracts world allowed scope environment
      (.lambda parameter .unit) (.function .unit .unit [] [] .pure) [] empty .pure :=
  .lambda .unit (.request (layers := [])) (by intro identity member; cases member) (by simp)

theorem lambdaAuth (parameter : Nat) :
    Auth operations policy ports owners emptyRows (lambdaSource (operations := operations)
      (policy := policy) (world := world) (allowed := allowed)
      (scope := .none) (environment := fun _ => none) parameter) (.function .unit .unit .pure) .pure :=
  .lambda .unit (by exact List.nil_subset _) (outward := .request (layers := []))
    (formed := by intro identity member; cases member) (latentBound := by simp)

theorem applicationSource :
    SourcePlannedSources.Expression operations policy contracts world allowed scope environment
      application .unit [] applicationRequirements (signature applicationPlan) :=
  .app (lambdaSource 2) .unit (List.nil_subset _)

theorem applicationAuth : Auth operations policy ports owners emptyRows
    (applicationSource (operations := operations) (policy := policy)
      (world := world) (allowed := allowed) (scope := .none) (environment := fun _ => none))
    .unit (.sequence .pure (.sequence .pure .pure)) :=
  .app (lambdaAuth 2) .unit (admitted := List.nil_subset _)

theorem cleanupSource :
    SourcePlannedSources.Expression operations policy contracts world allowed scope environment
      cleanup .unit [] cleanupRequirements (signature cleanupPlan) :=
  .cleanup (lambdaSource 1) applicationSource (List.nil_subset _)

theorem cleanupAuth : Auth operations policy ports owners emptyRows
    (cleanupSource (operations := operations) (policy := policy)
      (world := world) (allowed := allowed) (scope := .none) (environment := fun _ => none))
    .unit (.sequence .pure (.cleanup [] .pure (.sequence .pure (.sequence .pure .pure)))) :=
  .cleanup (lambdaAuth 1) applicationAuth (admitted := List.nil_subset _)

theorem cleanupHidden (identity : Nat) : ResourceRequirements.Hides identity cleanupRequirements cleanupRequirements :=
  .emitAfter (.sequence .request (.emitAfter (.sequence .request .request)))

theorem resourceSource :
    SourcePlannedSources.Expression operations policy contracts [] [] .none (fun _ => none)
      resource .unit [] resourceRequirements (signature resourcePlan) :=
  .resource .integer (fun _ _ => cleanupSource) (by intro identity member; cases member)
    (List.nil_subset _) (List.nil_subset _) (fun identity _ => cleanupHidden identity)

theorem resourceAuth : Auth operations policy ports owners emptyRows
    (resourceSource (operations := operations) (policy := policy)) .unit
    (.sequence .pure (.resource (fun _ => .sequence .pure (.cleanup [] .pure (.sequence .pure (.sequence .pure .pure)))))) :=
  .resource (residual := []) .integer (fun _ _ => cleanupAuth)
    (formed := by intro identity member; cases member) (effectsBound := List.nil_subset _)
    (admitted := List.nil_subset _) (hidden := fun identity _ => cleanupHidden identity)

def resourceProgram (ports : OperationRows operations)
    (builtinSignatures : SourceScheduledBuiltinSignatures.Compatible operations) :
    Program operations policy ports [] [] resource :=
  { result := .unit, resultRows := .unit, dependencies := _, plan := resourcePlan,
    rows := .sequence .pure (.resource (fun _ => .sequence .pure (.cleanup [] .pure (.sequence .pure (.sequence .pure .pure))))),
    demand := [], requirements := resourceRequirements, source := resourceSource,
    authenticated := resourceAuth,
    certified := by
      letI : SourcePlannedChecks.DeclarationPolicy := declarationPolicy
      exact .sequence .pure (.resource (fun _ _ => .sequence .pure (.cleanup .pure (.sequence .pure (.sequence .pure .pure))))),
    certificate := .sequence .pure (.resource (fun _ _ => .sequence .pure (.cleanup (.sequence .pure (.sequence .pure .pure)) .pure))),
    resourceChecked := .sequence .pure (.resource (fun _ _ => .sequence .pure (.cleanup (.sequence .pure (.sequence .pure .pure)) .pure))),
    rootDemand := [], root := empty,
    interpreted := by
      apply Accounting.Run.sequence
      apply Accounting.Run.pure
      apply Accounting.Wait.plain
      apply Accounting.Run.installResource
      intro identity fresh
      apply Accounting.Run.sequence
      apply Accounting.Run.pure
      apply Accounting.Wait.plain
      apply Accounting.Run.installCleanup
      apply Accounting.Run.sequence
      apply Accounting.Run.pure
      apply Accounting.Wait.plain
      apply Accounting.Run.sequence
      apply Accounting.Run.pure
      apply Accounting.Wait.plain
      exact .pure (.cleanup (.pure (.normal (.cell .nil)))),
    annotated := empty, annotation := .original, rootRow := [], checked := .request rfl,
    bounded := List.nil_subset _, resources := List.nil_subset _, builtinSignatures := builtinSignatures }

theorem resource_cleanup_application_initial (ports : OperationRows operations)
    (builtinSignatures : SourceScheduledBuiltinSignatures.Compatible operations) :
    InstallationState operations policy contracts tables families required [] annotations [] [] [] [] [] [] []
      ports owners emptyRows (.value .unit) (.value .unit) (initialRun resource) :=
  (resourceProgram (policy := policy) ports builtinSignatures).closed_initial_state tables families required

/-- A closed initial program cannot contain an unsupported literal reference,
even if another source annotation were to overlook it. -/
theorem unsupported_literal_rejected (identity : Nat) :
    ¬ Nonempty (Program operations policy ports [] budget (.resourceRef (.activation identity))) := by
  rintro ⟨program⟩
  have impossible := program.resources (show identity ∈ Syntax.resourceDependencies
    (Code.resourceRef (.activation identity)).dependencies from List.mem_cons_self)
  cases impossible

private theorem no_initial_request
    (source : SourcePlannedSources.Expression operations policy contracts world [] scope environment
      code result demand requirements checking)
    (expressionEq : code = .perform effect operation operand) : False := by
  cases source <;> cases expressionEq
  all_goals simp_all

/-- The empty initial interpretation cannot admit a top-level request. -/
theorem unhandled_request_rejected (effect : Instance) (operation : Nat) (operand : ScopedExpressions.Code) :
    ¬ Nonempty (Program operations policy ports [] [] (.perform (Instantiation.freezeEffect effect) operation operand)) := by
  rintro ⟨program⟩
  exact no_initial_request program.source rfl

private theorem no_initial_resume
    (source : SourcePlannedSources.Expression operations policy contracts world allowed scope environment
      code result demand requirements checking)
    (expressionEq : code = .resume binder operand) : False := by
  cases source <;> cases expressionEq
  all_goals simp_all [contracts]

/-- Initial contracts are empty: continuation use must originate in an admitted
handler clause, after capture introduces its symbolic binder. -/
theorem missing_continuation_rejected (binder : Nat) (operand : ScopedExpressions.Code) :
    ¬ Nonempty (Program operations policy ports [] [] (.resume binder operand)) := by
  rintro ⟨program⟩
  exact no_initial_resume program.source rfl

end Examples

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.Program.initial_state
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.Program.closed_initial_state
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.Examples.resource_cleanup_application_initial

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.owners
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.emptyRows
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.Program.site
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.Examples.lambdaSource
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.Examples.lambdaAuth
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.Examples.applicationSource
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.Examples.applicationAuth
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.Examples.cleanupSource
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.Examples.cleanupAuth
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.Examples.cleanupHidden
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.Examples.resourceSource
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.Examples.resourceAuth
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.Examples.resourceProgram
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.Examples.unsupported_literal_rejected
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.Examples.unhandled_request_rejected
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.Examples.missing_continuation_rejected
