import SourceScheduledInitialAdmission

/-!
D4 component evidence for TASK-0032 / DN-0033. The target annotation permits
cell instances to represent callable capture support. Its actual latent
Footprint remains empty. This is annotation refinement, not equality with the
Core function's exact effect row, and not a general static translator. Ordinary
Core function type information alone does not identify these retained resources.
The resource reference remains in the source body; no request is inserted.
-/
namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreCallableSupport
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Operations Contracts Value Environment)
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open RecursiveRequirements (Requirements)
open InstallationSupport
variable {operations : Operations} {policy : Syntax.TicketPolicy}
  {ports : OperationRows operations} {world : List Nat} {allowed : List Instance}
  {scope : Execution.Scope} {environment : Environment}
  {environmentRows : EnvironmentRows environment}

/-- A finite capture-support bound can be represented by allowed cell instances
    in the existing lambda guard. This does not assert any actual operation. -/
theorem capture_guard_from_cell_support
    (support : ScopedPorts.Support.evaluate
      (LambdaPortCaptureSupport.portSupport environment)
      (Code.lambda parameter body).dependencies ⊆ resources) :
    LambdaPortCaptureSupport.captures environment parameter body input output
      (resources.map Instance.cell) := by
  intro identity member
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨.cell identity,
    List.mem_map.mpr ⟨identity, support member, rfl⟩, by simp [Instance.resources]⟩

def empty : Requirements [] := .request [] []
def body (identity : Nat) : Code := .bind 3 (.resourceRef (.activation identity)) .unit
def closure (identity : Nat) : Code := .lambda 2 (body identity)
def application (identity : Nat) : Code := .app (closure identity) .unit
def bodyPlan := Plan.sequence Plan.pure Plan.pure
def applicationPlan := Plan.sequence Plan.pure (Plan.sequence Plan.pure bodyPlan)
def bodyRequirements : Requirements [] := .sequence empty empty
def applicationRequirements : Requirements [] := .emitAfter (.sequence empty empty) [] []

theorem bodySource (issued : identity ∈ world) :
    SourcePlannedSources.Expression operations policy contracts world allowed scope environment
      (body identity) .unit [] bodyRequirements (signature bodyPlan) :=
  .bind (.reference issued) .unit

theorem bodyOutward : RecursiveOutward.Outward bodyRequirements (some []) :=
  .sequence (.request (layers := [])) (.request (layers := []))

theorem closureFormed (issued : identity ∈ world) :
    ScopedPorts.InWorld world
      (Value.function .unit .unit [.cell identity] [] (signature bodyPlan)).erase.erase.port := by
  intro resource member
  simp [Value.erase, SourceDependencyAnnotations.Value.erase,
    CoherentSourceTypes.Value.port, ScopedPorts.Port.resources, Instance.resources] at member
  subst resource
  exact issued

theorem closureSource (issued : identity ∈ world) :
    SourcePlannedSources.Expression operations policy contracts world allowed scope environment
      (closure identity) (.function .unit .unit [.cell identity] [] (signature bodyPlan))
      [] empty .pure :=
  .lambda (bodySource issued) bodyOutward (closureFormed issued)
    (by intro request member; cases member)

theorem bodyAuth (issued : identity ∈ world) :
    Auth operations policy ports owners environmentRows
      (bodySource (operations := operations) (policy := policy) (allowed := allowed)
        (scope := scope) (environment := environment) issued) .unit (.sequence .pure .pure) :=
  .bind (.reference (issued := issued)) .unit

theorem closureAuth (issued : identity ∈ world) :
    Auth operations policy ports owners environmentRows
      (closureSource (operations := operations) (policy := policy) (allowed := allowed)
        (scope := scope) (environment := environment) issued)
      (.function .unit .unit (.sequence .pure .pure)) .pure := by
  refine Auth.lambda (bodyAuth issued) ?_ (outward := bodyOutward)
    (formed := closureFormed issued) (latentBound := by intro request member; cases member)
  apply capture_guard_from_cell_support (resources := [identity])
  simp [body, Code.dependencies, Syntax.without, ScopedPorts.Support.evaluate]

/-- Keeping the exact empty Core row as the target request allowance would
    fail this existing guard even though the source makes no request. -/
theorem empty_allowance_does_not_supply_capture_guard (identity : Nat) :
    ¬ LambdaPortCaptureSupport.captures environment 2 (body identity) .unit .unit [] := by
  simp [LambdaPortCaptureSupport.captures, body, Code.dependencies, Syntax.without,
    ScopedPorts.Support.evaluate, Value.erase, SourceDependencyAnnotations.Value.erase,
    CoherentSourceTypes.Value.port, ScopedPorts.Port.resources]

theorem applicationSource (issued : identity ∈ world) (admitted : Instance.cell identity ∈ allowed) :
    SourcePlannedSources.Expression operations policy contracts world allowed scope environment
      (application identity) .unit [] applicationRequirements (signature applicationPlan) :=
  .app (closureSource issued) .unit (by simpa using admitted)

theorem applicationAuth (issued : identity ∈ world) (admitted : Instance.cell identity ∈ allowed) :
    Auth operations policy ports owners environmentRows
      (applicationSource (operations := operations) (policy := policy)
        (scope := scope) (environment := environment) issued admitted)
      .unit (.sequence .pure (.sequence .pure (.sequence .pure .pure))) :=
  .app (closureAuth issued) .unit (admitted := by simpa using admitted)

def template : Code :=
  .app (.lambda 2 (.bind 3 (.resourceRef (.bound 0)) .unit)) .unit

def resource : Code := .resource 0 (.integer 0) template

def resourcePlan := Plan.sequence Plan.pure (Plan.resource (fun _ => applicationPlan))
def resourceRequirements : Requirements [] := .sequence empty applicationRequirements

theorem instantiate_template (identity : Nat) :
    template.instantiate (Instantiation.Environment.empty.bind 0 identity) = application identity := rfl

theorem applicationHidden (identity : Nat) :
    ResourceRequirements.Hides identity applicationRequirements applicationRequirements :=
  .emitAfter (.sequence .request .request)

theorem resourceBodySource (identity : Nat) :
    SourcePlannedSources.Expression operations policy contracts ([] ++ [identity])
      [.cell identity] .none (fun _ => none)
      (template.instantiate (Instantiation.Environment.empty.bind 0 identity))
      .unit [] applicationRequirements (signature applicationPlan) := by
  simpa only [instantiate_template, List.nil_append] using
    applicationSource (world := [identity]) (allowed := [.cell identity])
      (scope := .none) (environment := fun _ => none) (List.mem_cons_self) (List.mem_cons_self)

theorem resourceSource :
    SourcePlannedSources.Expression operations policy contracts [] [] .none (fun _ => none)
      resource .unit [] resourceRequirements (signature resourcePlan) :=
  .resource .integer (fun identity _ => resourceBodySource identity)
    (by intro identity member; cases member) (List.nil_subset _) (List.nil_subset _)
    (fun identity _ => applicationHidden identity)

theorem resourceAuth : Auth operations policy ports owners emptyRows
    (resourceSource (operations := operations) (policy := policy)) .unit
    (.sequence .pure (.resource (fun _ =>
      .sequence .pure (.sequence .pure (.sequence .pure .pure))))) := by
  refine Auth.resource (residual := [])
    (body := fun identity _ => resourceBodySource identity) .integer (fun identity _ => ?_)
    (formed := by intro identity member; cases member)
    (effectsBound := List.nil_subset _) (admitted := List.nil_subset _)
    (hidden := fun identity _ => applicationHidden identity)
  simpa only [instantiate_template, List.nil_append] using
    applicationAuth (operations := operations) (policy := policy) (ports := ports)
      (world := [identity]) (allowed := [.cell identity]) (scope := .none)
      (environment := fun _ => none) (environmentRows := emptyRows)
      (List.mem_cons_self) (List.mem_cons_self)

/-- The concrete construction retains resourceRef under bind in the lambda.
    The annotation changes neither this code nor its source expression shape. -/
theorem retained_reference_source : resource =
    .resource 0 (.integer 0)
      (.app (.lambda 2 (.bind 3 (.resourceRef (.bound 0)) .unit)) .unit) := rfl

/-- An allowed cell instance is capture-support metadata here: all actual
    body requests residualize to the empty footprint. -/
theorem refined_annotation_empty_actual_footprint :
    RecursiveOutward.Outward bodyRequirements (some []) := bodyOutward

def resourceProgram (ports : OperationRows operations)
    (builtinSignatures : SourceScheduledBuiltinSignatures.Compatible operations) :
    Program operations policy ports [] [] resource :=
  { result := .unit, resultRows := .unit, dependencies := _, plan := resourcePlan,
    rows := .sequence .pure (.resource (fun _ =>
      .sequence .pure (.sequence .pure (.sequence .pure .pure)))),
    demand := [], requirements := resourceRequirements, source := resourceSource,
    authenticated := resourceAuth,
    certified := by
      letI : SourcePlannedChecks.DeclarationPolicy := declarationPolicy
      exact .sequence .pure (.resource (fun _ _ =>
        .sequence .pure (.sequence .pure (.sequence .pure .pure)))),
    certificate := .sequence .pure (.resource (fun _ _ =>
      .sequence .pure (.sequence .pure (.sequence .pure .pure)))),
    resourceChecked := .sequence .pure (.resource (fun _ _ =>
      .sequence .pure (.sequence .pure (.sequence .pure .pure)))),
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
      apply Accounting.Run.sequence
      apply Accounting.Run.pure
      apply Accounting.Wait.plain
      apply Accounting.Run.sequence
      apply Accounting.Run.pure
      apply Accounting.Wait.plain
      exact .pure (.cell .nil),
    annotated := empty, annotation := .original, rootRow := [], checked := .request rfl,
    bounded := List.nil_subset _, resources := List.nil_subset _, builtinSignatures := builtinSignatures }

theorem pure_retaining_closure_initial (ports : OperationRows operations)
    (builtinSignatures : SourceScheduledBuiltinSignatures.Compatible operations) :
    InstallationState operations policy contracts tables families required [] annotations [] [] [] [] [] [] []
      ports owners emptyRows (.value .unit) (.value .unit) (initialRun resource) :=
  (resourceProgram (policy := policy) ports builtinSignatures).closed_initial_state tables families required

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreCallableSupport

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreCallableSupport.capture_guard_from_cell_support
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreCallableSupport.closureAuth
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreCallableSupport.resourceProgram
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreCallableSupport.pure_retaining_closure_initial

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreCallableSupport.empty_allowance_does_not_supply_capture_guard
