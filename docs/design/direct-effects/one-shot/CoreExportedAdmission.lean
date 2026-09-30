import CoreExportedFixture
import CoreKernelProgram

/-! Direct static admission of exported administrative syntax. The actual
getter closure and application below are translated from the validated fixture;
resource instantiation and lexical bindings remain explicit. -/
namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreExportedAdmission
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Value Environment Contracts)
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open RecursiveRequirements (Requirements)
open InstallationSupport
open CoreInitialExample CoreKernelProgram

def getterBody (identity : Nat) : Code :=
  .perform (Instantiation.freezeEffect (.cell identity)) 0 (.variable 1)
def getter (identity : Nat) : Code := .lambda 1 (getterBody identity)
def getterApplication : Code := .app (.variable 11) (.variable 4)

theorem exportedGetter (identity : Nat) :
    (CoreTranslation.translateFuel CoreExportedFixture.graph 56 [] 4).map
      (fun code => code.instantiate (Instantiation.Environment.empty.bind 0 identity)) = .ok (getter identity) := rfl

theorem exportedGetterApplication :
    CoreTranslation.translateFuel CoreExportedFixture.graph 56 [] 44 = .ok getterApplication := rfl

/-- Pure callable and argument evaluation retains the actual body rows. This
uses a current structural source certificate, not future execution evidence. -/
def administrativeApplication {actions : Syntax.UsageTickets} {phases : OwnerPhaseTransitions.Phases}
    {world installations : List Nat}
    (body : SourceProof actions phases world installations rows context) :
    SourceProof actions phases world installations (.sequence .pure (.sequence .pure rows)) context :=
  SourceProof.sequence pureProof (SourceProof.sequence pureProof body)

variable {world : List Nat} {environment : Environment} {environmentRows : EnvironmentRows environment}

def getterFootprint (identity : Nat) : Footprint := [⟨.cell identity, 0, false⟩]
def getterValue (identity : Nat) : Value :=
  .function (.reference identity) .integer [.cell identity] (getterFootprint identity) (signature (readPlan identity))

def savedEnvironment (identity : Nat) (base : Environment) : Environment :=
  base.extend 4 (.reference identity)
def applicationEnvironment (identity : Nat) (base : Environment) : Environment :=
  (savedEnvironment identity base).extend 11 (getterValue identity)

def getterValueRows (identity : Nat) : ValueRows (getterValue identity) :=
  .function .reference .integer (operationRows identity 0)
def applicationEnvironmentRows (identity : Nat) (base : EnvironmentRows environment) :
    EnvironmentRows (applicationEnvironment identity environment) :=
  (base.extend 4 .reference).extend 11 (getterValueRows identity)

theorem referenceFormed (issued : identity ∈ world) :
    ScopedPorts.InWorld world (Value.reference identity).erase.erase.port := by
  intro resource member
  simp [Value.erase, SourceDependencyAnnotations.Value.erase, CoherentSourceTypes.Value.port,
    ScopedPorts.Port.resources] at member
  subst resource
  exact issued

theorem getterFormed (issued : identity ∈ world) :
    ScopedPorts.InWorld world (getterValue identity).erase.erase.port := by
  intro resource member
  simp [getterValue, Value.erase, SourceDependencyAnnotations.Value.erase, CoherentSourceTypes.Value.port,
    ScopedPorts.Port.resources, Instance.resources] at member
  subst resource
  exact issued

theorem getterBodySource (issued : identity ∈ world) :
    SourcePlannedSources.Expression operations policy InitialAdmission.contracts world [.cell identity] .none
      ((savedEnvironment identity environment).extend 1 (.reference identity))
      (getterBody identity) .integer [] (readRequirements identity) (signature (readPlan identity)) :=
  .perform rfl List.mem_cons_self
    (.variable (by simp [Environment.extend]) (referenceFormed issued)) (List.nil_subset _)

theorem getterBodyAuth (issued : identity ∈ world) :
    Auth operations policy ports InitialAdmission.owners
      ((environmentRows.extend 4 .reference).extend 1 .reference)
      (getterBodySource (environment := environment) issued) .integer (operationRows identity 0) := by
  exact .perform (input := .reference identity) (output := .integer)
    (known := (rfl : operations (.cell identity) 0 = some (.reference identity, .integer))) (admitted := List.mem_cons_self) (formed := List.nil_subset _)
    (.variable (known := by simp [Environment.extend]) (formed := referenceFormed issued))

theorem getterOutward : RecursiveOutward.Outward (readRequirements identity) (some (getterFootprint identity)) :=
  .emitAfter (layers := []) (raw := getterFootprint identity) (.request (layers := []) (raw := []))

theorem getterSource (issued : identity ∈ world) :
    SourcePlannedSources.Expression operations policy InitialAdmission.contracts world allowed .none
      (savedEnvironment identity environment) (getter identity) (getterValue identity) [] empty .pure :=
  .lambda (getterBodySource issued) getterOutward (getterFormed issued)
    (by intro requested member; simp only [getterFootprint, List.mem_singleton] at member; subst requested; exact List.mem_cons_self)

theorem getterAuth (issued : identity ∈ world) :
    Auth operations policy ports InitialAdmission.owners (environmentRows.extend 4 .reference)
      (getterSource (allowed := allowed) (environment := environment) issued) (getterValueRows identity) .pure := by
  refine Auth.lambda (getterBodyAuth issued) ?_ (outward := getterOutward) (formed := getterFormed issued)
    (latentBound := by intro requested member; simp only [getterFootprint, List.mem_singleton] at member; subst requested; exact List.mem_cons_self)
  apply CoreCallableSupport.capture_guard_from_cell_support (resources := [identity])
  simp [getterBody, Code.dependencies, Instantiation.freezeEffect,
    effectAtoms, Instantiation.Effect.resources, Syntax.without, ScopedPorts.Support.evaluate]

def applicationPlan (identity : Nat) := Plan.sequence Plan.pure (Plan.sequence Plan.pure (readPlan identity))
def applicationRequirements (identity : Nat) : Requirements [] :=
  .emitAfter (.sequence empty empty) [] (getterFootprint identity)
def applicationRows (identity : Nat) : Rows (signature (applicationPlan identity)) :=
  .sequence .pure (.sequence .pure (operationRows identity 0))

theorem applicationSource (issued : identity ∈ world) :
    SourcePlannedSources.Expression operations policy InitialAdmission.contracts world [.cell identity] .none
      (applicationEnvironment identity environment) getterApplication .integer []
      (applicationRequirements identity) (signature (applicationPlan identity)) :=
  .app
    (.variable (by simp [applicationEnvironment, Environment.extend, getterValue]) (getterFormed issued))
    (.variable (by simp [applicationEnvironment, savedEnvironment, Environment.extend]) (referenceFormed issued))
    (List.Subset.refl _)

theorem applicationAuth (issued : identity ∈ world) :
    Auth operations policy ports InitialAdmission.owners (applicationEnvironmentRows identity environmentRows)
      (applicationSource (environment := environment) issued) .integer (applicationRows identity) := by
  have functionChecked : Auth operations policy ports owners
      (applicationEnvironmentRows identity environmentRows)
      (SourcePlannedSources.Expression.variable (allowed := [.cell identity]) (scope := .none)
        (by simp [applicationEnvironment, Environment.extend, getterValue] :
          applicationEnvironment identity environment 11 = some (getterValue identity))
        (getterFormed issued)) (getterValueRows identity) .pure := by
    simpa [applicationEnvironmentRows, EnvironmentRows.extend] using
      (Auth.variable (operations := operations) (policy := policy) (ports := ports)
        (owners := owners) (environmentRows := applicationEnvironmentRows identity environmentRows)
        (known := (by simp [applicationEnvironment, Environment.extend] :
          applicationEnvironment identity environment 11 = some (getterValue identity)))
        (formed := getterFormed issued))
  have argumentChecked : Auth operations policy ports owners
      (applicationEnvironmentRows identity environmentRows)
      (SourcePlannedSources.Expression.variable (allowed := [.cell identity]) (scope := .none)
        (by simp [applicationEnvironment, savedEnvironment, Environment.extend] :
          applicationEnvironment identity environment 4 = some (.reference identity))
        (referenceFormed issued)) .reference .pure := by
    simpa [applicationEnvironmentRows, EnvironmentRows.extend] using
      (Auth.variable (operations := operations) (policy := policy) (ports := ports)
        (owners := owners) (environmentRows := applicationEnvironmentRows identity environmentRows)
        (known := (by simp [applicationEnvironment, savedEnvironment, Environment.extend] :
          applicationEnvironment identity environment 4 = some (.reference identity)))
        (formed := referenceFormed issued))
  exact Auth.app (admitted := List.Subset.refl _) functionChecked argumentChecked

/-- The exported variable application obtains its current source certificate
from the actual cell receiver; the administrative row prefixes stay present. -/
def applicationCertificate :
    SourceProof InitialAdmission.actions (OwnerPhaseTransitions.available []) [identity] []
      (applicationRows identity) (Context.cell (identity := identity) .nil) :=
  administrativeApplication (operationProof (identity := identity) (operation := 0) (by simp [select]))

theorem applicationAccounting :
    Accounting.Run [identity] [] (applicationRows identity) (Context.cell (identity := identity) .nil) empty :=
  .sequence (.pure (.plain (.sequence (.pure (.plain
    (operationAccounting (identity := identity) (operation := 0) (by simp [select]) (.cell .nil)))))))

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreExportedAdmission

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreExportedAdmission.exportedGetter
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreExportedAdmission.exportedGetterApplication

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreExportedAdmission.getterAuth
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreExportedAdmission.applicationAuth
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreExportedAdmission.applicationCertificate

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreExportedAdmission.applicationAccounting
