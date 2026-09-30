import CoreCallableSupport
import SourceScheduledInitialHandlerExample

/-!
TASK-0032 C2 construction for the normalization target of
fixtures/core-cleanup-restored-clause-suffix.ash. This is a scoped source
construction attempt; Rust graph translation and normalization remain separate
proofs. Primitive source/Auth components compile, but no full Program is built.
The final negative theorem exposes an overbroad clause-row interface rather than
asserting that the Rust fixture is unsafe or that coherent runtime states fail.
-/
namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreInitialExample
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Operations Value Environment Contract)
open SourceDeclarationPlans
open SourcePlanSignatures (signature)
open RecursiveRequirements (Requirements)
open InstallationSupport

 def effect : Instance := .user 0 []
 def policy : Syntax.TicketPolicy := fun _ => ⟨true, true⟩
 def operations : Operations
  | .cell identity, 0 => some (.reference identity, .integer)
  | .cell identity, 1 => some (.pair (.reference identity) .integer, .unit)
  | .user 0 [], 0 => some (.boolean, .unit)
  | _, _ => none

 def ports : OperationRows operations := by
  intro requested operation input output known
  cases requested with
  | cell identity =>
      cases operation with
      | zero => cases known; exact ⟨.reference, .integer⟩
      | succ operation => cases operation with
          | zero => cases known; exact ⟨.pair .reference .integer, .unit⟩
          | succ operation => cases known
  | user name arguments =>
      cases name with
      | zero => cases arguments with
          | nil => cases operation with
              | zero => cases known; exact ⟨.boolean, .unit⟩
              | succ operation => cases known
          | cons arg rest => cases known
      | succ name => cases known

 theorem builtinSignatures : SourceScheduledBuiltinSignatures.Compatible operations := by
  intro identity operation input output known
  cases operation with
  | zero =>
      simp [operations, SourcePlannedTyping.Operations.erase,
        SourceDependencyAnnotations.Operations.erase, CoherentSourceTypes.Operations.ports] at known
      exact .inl ⟨rfl, known.1.symm, known.2.symm⟩
  | succ operation => cases operation with
      | zero =>
          simp [operations, SourcePlannedTyping.Operations.erase,
            SourceDependencyAnnotations.Operations.erase, CoherentSourceTypes.Operations.ports] at known
          exact .inr ⟨rfl, known.1.symm, known.2.symm⟩
      | succ operation => simp [operations, SourcePlannedTyping.Operations.erase,
          SourceDependencyAnnotations.Operations.erase, CoherentSourceTypes.Operations.ports] at known

 def empty : Requirements [] := .request [] []
 def write (identity : Nat) (value : Int) : Code :=
  .perform (Instantiation.freezeEffect (.cell identity)) 1
    (.pair (.resourceRef (.activation identity)) (.integer value))
 def read (identity : Nat) : Code :=
  .perform (Instantiation.freezeEffect (.cell identity)) 0 (.resourceRef (.activation identity))
 def request (flag : Bool) : Code := .perform (Instantiation.freezeEffect effect) 0 (.boolean flag)
 def writePlan (identity : Nat) := Plan.sequence Plan.pure (Plan.request (effect := .cell identity) (operation := 1))
 def readPlan (identity : Nat) := Plan.sequence Plan.pure (Plan.request (effect := .cell identity) (operation := 0))
 def requestPlan := Plan.sequence Plan.pure (Plan.request (effect := effect) (operation := 0))
 def writeRequirements (identity : Nat) : Requirements [] := .emitAfter empty [] [⟨.cell identity, 1, false⟩]
 def readRequirements (identity : Nat) : Requirements [] := .emitAfter empty [] [⟨.cell identity, 0, false⟩]
 def requestRequirements : Requirements [] := .emitAfter empty [] [⟨effect, 0, false⟩]

 variable {world : List Nat} {allowed : List Instance} {scope : Execution.Scope}
  {environment : Environment} {environmentRows : EnvironmentRows environment}

 theorem writeSource (issued : identity ∈ world) (admitted : Instance.cell identity ∈ allowed) (value : Int) :
    SourcePlannedSources.Expression operations policy contracts world allowed scope environment
      (write identity value) .unit [] (writeRequirements identity) (signature (writePlan identity)) :=
  .perform rfl admitted (.purePair (.reference issued) .integer) (List.nil_subset _)

 theorem writeAuth (issued : identity ∈ world) (admitted : Instance.cell identity ∈ allowed) (value : Int) :
    Auth operations policy ports owners environmentRows
      (writeSource (scope := scope) (environment := environment) issued admitted value)
      .unit (.sequence .pure .request) :=
  .perform (operand := .purePair (.reference issued) .integer)
    (known := (rfl : operations (.cell identity) 1 = some (.pair (.reference identity) .integer, .unit)))
    (admitted := admitted) (formed := List.nil_subset _)
    (.purePair (.reference (issued := issued)) .integer)

 theorem readSource (issued : identity ∈ world) (admitted : Instance.cell identity ∈ allowed) :
    SourcePlannedSources.Expression operations policy contracts world allowed scope environment
      (read identity) .integer [] (readRequirements identity) (signature (readPlan identity)) :=
  .perform rfl admitted (.reference issued) (List.nil_subset _)

 theorem readAuth (issued : identity ∈ world) (admitted : Instance.cell identity ∈ allowed) :
    Auth operations policy ports owners environmentRows
      (readSource (scope := scope) (environment := environment) issued admitted)
      .integer (.sequence .pure .request) :=
  .perform (operand := .reference issued)
    (known := (rfl : operations (.cell identity) 0 = some (.reference identity, .integer))) (admitted := admitted)
    (formed := List.nil_subset _) (.reference (issued := issued))

 theorem requestSource (admitted : effect ∈ allowed) (flag : Bool) :
    SourcePlannedSources.Expression operations policy contracts world allowed scope environment
      (request flag) .unit [] requestRequirements (signature requestPlan) :=
  .perform rfl admitted .boolean (List.nil_subset _)

 theorem requestAuth (admitted : effect ∈ allowed) (flag : Bool) :
    Auth operations policy ports owners environmentRows
      (requestSource (world := world) (scope := scope) (environment := environment) admitted flag)
      .unit (.sequence .pure .request) :=
  .perform (operand := .boolean (value := flag))
    (known := (rfl : operations effect 0 = some (.boolean, .unit))) (admitted := admitted)
    (formed := List.nil_subset _) .boolean

 def callback (identity : Nat) : Code := .lambda 10 (write identity 7)
 def callbackFootprint (identity : Nat) : Footprint := [⟨.cell identity, 1, false⟩]

 theorem callbackSource (issued : identity ∈ world) :
    SourcePlannedSources.Expression operations policy contracts world allowed scope environment
      (callback identity) (.function .unit .unit [.cell identity] (callbackFootprint identity)
        (signature (writePlan identity))) [] empty .pure :=
  .lambda (writeSource issued List.mem_cons_self 7)
    (.emitAfter (layers := []) (raw := callbackFootprint identity)
      (.request (layers := []) (raw := [])))
    (CoreCallableSupport.closureFormed issued)
    (by intro requested member; simp only [callbackFootprint, List.mem_singleton] at member; subst requested; exact List.mem_cons_self)

 theorem callbackAuth (issued : identity ∈ world) :
    Auth operations policy ports owners environmentRows
      (callbackSource (allowed := allowed) (scope := scope) (environment := environment) issued)
      (.function .unit .unit (.sequence .pure .request)) .pure := by
  refine Auth.lambda (writeAuth issued List.mem_cons_self 7) ?_
    (outward := .emitAfter (layers := []) (raw := callbackFootprint identity)
      (.request (layers := []) (raw := [])))
    (formed := CoreCallableSupport.closureFormed issued)
    (latentBound := by intro requested member; simp only [callbackFootprint, List.nil_append, List.mem_singleton] at member; subst requested; exact List.mem_cons_self)
  apply CoreCallableSupport.capture_guard_from_cell_support (resources := [identity])
  simp [write, Code.dependencies, Instance.resources,
    Syntax.without, ScopedPorts.Support.evaluate]

 def protectedBody (identity : Nat) : Code :=
  .bind 4 (request true) (.bind 5 (request false) (write identity 99))
 def protectedPlan (identity : Nat) := Plan.sequence requestPlan (Plan.sequence requestPlan (writePlan identity))
 def protectedRequirements (identity : Nat) : Requirements [] :=
  .sequence requestRequirements (.sequence requestRequirements (writeRequirements identity))

 theorem protectedSource (issued : identity ∈ world) (cell : Instance.cell identity ∈ allowed)
    (user : effect ∈ allowed) :
    SourcePlannedSources.Expression operations policy contracts world allowed scope environment
      (protectedBody identity) .unit [] (protectedRequirements identity) (signature (protectedPlan identity)) :=
  .bind (requestSource user true) (.bind (requestSource user false) (writeSource issued cell 99))

 theorem protectedAuth (issued : identity ∈ world) (cell : Instance.cell identity ∈ allowed)
    (user : effect ∈ allowed) :
    Auth operations policy ports owners environmentRows
      (protectedSource (scope := scope) (environment := environment) issued cell user)
      .unit (.sequence (.sequence .pure .request)
        (.sequence (.sequence .pure .request) (.sequence .pure .request))) :=
  .bind (requestAuth user true) (.bind (requestAuth user false) (writeAuth issued cell 99))

/-- Full requested normalization target. The admission attempt does not erase
    the branch, resumed suffix write, cleanup or either user operation. -/
def writeAt (name : Instantiation.ResourceName) (value : Int) : Code :=
  .perform (.cell name) 1 (.pair (.resourceRef name) (.integer value))
def readAt (name : Instantiation.ResourceName) : Code := .perform (.cell name) 0 (.resourceRef name)
def normalized : Code :=
  .resource 0 (.integer 0)
    (.bind 20
      (.handle (Instantiation.freezeEffect effect)
        (.cleanup (.lambda 10 (writeAt (.bound 0) 7))
          (.bind 4 (request true) (.bind 5 (request false) (writeAt (.bound 0) 99))))
        (.cons 0 6 7
          (.branch (.variable 6)
            (.bind 8 (.resume 7 .unit) (writeAt (.bound 0) 11))
            (.discard 7)) .nil))
      (readAt (.bound 0)))

/-- The general interface alone does not preserve a suffix advertisement:
    another consumed live owner can remove a protected barrier in the tail. -/
theorem resumed_demand_changes_suffix_interpretation :
    OwnerSource.exportAt [.live 9 true] (OwnerPhaseTransitions.available [8, 9])
      [⟨.cell 0, 1, false⟩] = some [⟨.cell 0, 1, true⟩] ∧
    OwnerSource.exportAt (.live 8 false :: [.live 9 true])
      (OwnerPhaseTransitions.spendAll (OwnerPhaseTransitions.available [8, 9]) [8, 9])
      [⟨.cell 0, 1, false⟩] = some [⟨.cell 0, 1, false⟩] := by
  constructor <;> rfl

theorem changed_suffix_not_covered_by_before_advertisement :
    ¬ EffectBounds.Covers ([⟨Instance.cell 0, 1, true⟩] ++ [])
      [⟨Instance.cell 0, 1, false⟩] := by
  intro covered
  have impossible := covered (List.mem_cons_self)
  simp at impossible

namespace InterfaceObstruction
open CoherentSourceTypes
open ClauseRowAdmission
open RecursiveRequirements (Store Checked)

def nestedContract : CoherentSourceTypes.Owners.Contract :=
  ⟨.unit, .unit, false, [], [], [], some [], [], []⟩
def selectedContract : CoherentSourceTypes.Owners.Contract :=
  ⟨.unit, .unit, false, [9], [], [9], some [], [.cell 0], [.cell 0]⟩
def sourceContracts : CoherentSourceTypes.Owners.Contracts := fun owner =>
  if owner = 8 then some selectedContract else if owner = 9 then some nestedContract else none

def plain : ScopedExecution.PlainData :=
  ⟨.bind 1 (.discard 7), .ticket 7 9, .unit, .unit, [9], rfl⟩
def capture : ScopedExecution.Stack :=
  .push (.plain plain) (.live 9 .unit .unit .nil .none .nil)
def root : ScopedExecution.Stack := .live 8 .unit .unit capture .none .nil
def tables : CallableProtectionFrames.Tables := fun _ => []
def resumeTemplate : Requirements [9] :=
  .sequence (.invoke ⟨9, .dispose⟩ [] [.live 9 false]) (.sequence (.spent 9) empty)
def closeTemplate : Requirements [9] :=
  .sequence (.request [.ordinary (.barrier true)] []) (.sequence (.retire 9) empty)
def store : Store :=
  [(⟨8, .resume⟩, ⟨[9], resumeTemplate⟩),
    (⟨8, .dispose⟩, ⟨[9], closeTemplate⟩),
    (⟨9, .dispose⟩, ⟨[], empty⟩)]

theorem nested_known : sourceContracts 9 = some nestedContract := rfl
theorem selected_known : sourceContracts 8 = some selectedContract := rfl

theorem discard_source : SourceTemplates.Expression operations.erase.erase policy sourceContracts [] []
    (.ticket 7 9) (CoherentSourceTypes.Environment.empty.extend 1 .unit)
    (.discard 7) .unit [9] (.invoke ⟨9, .dispose⟩ [] []) :=
  .discard nested_known rfl rfl rfl (List.nil_subset _)

theorem plain_source : SourceTemplates.Frame operations.erase.erase policy sourceContracts []
    (.plain plain) .unit .unit [9] (.invoke ⟨9, .dispose⟩ [] []) :=
  .plain (.bind discard_source)
    (.bound (CoherentSourceTypes.Owners.ports_lookup nested_known)) rfl rfl

theorem capture_source : StoreModeSource operations.erase.erase policy sourceContracts tables []
    capture (some .unit) (some .unit) [9] resumeTemplate :=
  .push (.ordinary (.ordinary plain_source))
    (.live nested_known rfl rfl ⟨_, .none⟩ rfl .nil (.inl rfl) .nil)

theorem root_source : StoreModeSource operations.erase.erase policy sourceContracts tables []
    root (some .unit) (some .unit) [] (.sequence (.spent 8) empty) :=
  .live selected_known rfl rfl ⟨_, .none⟩ rfl capture_source (.inl rfl) .nil

theorem closing_source : StoreClosingRecords operations.erase.erase policy sourceContracts tables [] root
    [(⟨8, .dispose⟩, ⟨[9], closeTemplate⟩), (⟨9, .dispose⟩, ⟨[], empty⟩)] :=
  .close rfl (.plain (.live .nil .nil))
    (.push (.close rfl .nil .nil .nil)) .nil

theorem source_store : SourceStore operations.erase.erase 8 selectedContract store := by
  refine ⟨policy, sourceContracts, tables, [], root, some .unit, some .unit, [],
    .sequence (.spent 8) empty, [(⟨8, .resume⟩, ⟨[9], resumeTemplate⟩)],
    [(⟨8, .dispose⟩, ⟨[9], closeTemplate⟩), (⟨9, .dispose⟩, ⟨[], empty⟩)],
    root_source, ?_, closing_source, selected_known, ?_⟩
  · intro key body member
    cases List.mem_singleton.mp member
    exact .resume .here selected_known capture_source (.inl rfl)
  · exact SourceDependencyAnnotations.StoreAnnotation.refl _

def before : OwnerPhaseTransitions.Phases := OwnerPhaseTransitions.available [8, 9]
def tail : OwnerPhases.Context := [.live 9 true]
def advertised : Footprint := [⟨.cell 0, 1, false⟩]
def requestRow : Footprint := [⟨.cell 0, 1, true⟩]

theorem interface : Interface 8 selectedContract true store tail before requestRow := by
  constructor
  · apply Checked.invoke (body := resumeTemplate) (known := rfl) (ownersReady := rfl) (selection := .hit)
    dsimp only [resumeTemplate, closeTemplate, empty]
    refine Checked.sequence (firstRow := []) (secondRow := []) ?_ ?_
    · exact .invoke (body := empty) (known := rfl) (ownersReady := rfl)
        (selection := .hit) (.request rfl)
    · refine Checked.sequence (firstRow := []) (secondRow := []) (.spent rfl) ?_
      exact .request rfl
  · intro _ row known
    simp only [selectedContract, Option.some.injEq] at known
    subst row
    apply Checked.invoke (body := closeTemplate) (known := rfl) (ownersReady := rfl) (selection := .hit)
    dsimp only [resumeTemplate, closeTemplate, empty]
    refine Checked.sequence (firstRow := []) (secondRow := []) (.request rfl) ?_
    refine Checked.sequence (firstRow := []) (secondRow := []) (.retire rfl) ?_
    exact .request rfl
  · intro _; exact ⟨[], rfl⟩
  · intro _ row known
    simp only [selectedContract, Option.some.injEq] at known
    subst row
    exact List.nil_subset _
  · decide

theorem advertisement : OwnerSource.exportAt tail before advertised = some requestRow := rfl

/-- Minimal post-resume suffix requirement: the actual cell write remains after
    the invocation rather than being folded into its supplied resume row. -/
def suffixRequirements : Requirements [8, 9] :=
  .sequence (.sequence empty (.invoke ⟨8, .resume⟩ [9] []))
    (writeRequirements 0)

theorem suffix_checked : Checked store (.live 8 false :: tail) before suffixRequirements
    [⟨.cell 0, 1, false⟩] := by
  refine Checked.sequence (firstRow := []) (secondRow := [⟨.cell 0, 1, false⟩])
    (Checked.sequence (firstRow := []) (secondRow := []) (.request rfl) interface.resume) ?_
  exact Checked.emitAfter (bodyRow := []) (requestRow := [⟨.cell 0, 1, false⟩]) (.request rfl) rfl

/-- Source-store authentication and the advertised interface do not suffice for
    this post-resume suffix. The source witness gives owner 9 an unprotected
    capture, while the independent receiving tail marks owner 9 protected.
    No premise relates those two metadata interpretations. This is an interface
    counterexample, not a claim that a coherent Rust state has this alias. -/
theorem suffix_rows_impossible :
    ¬ ClauseRowAdmission.Rows ⟨8, selectedContract, true, advertised⟩ suffixRequirements
      (ClauseRowAdmission.SourceStore operations.erase.erase 8 selectedContract) := by
  intro rows
  obtain ⟨actualRow, checked, covered⟩ := rows.instantiate interface advertisement source_store
  have expected := RecursiveRequirements.checked_complete suffix_checked
  have actual := RecursiveRequirements.checked_complete checked
  have same : actualRow = [⟨Instance.cell 0, 1, false⟩] := Option.some.inj (actual.symm.trans expected)
  subst actualRow
  exact changed_suffix_not_covered_by_before_advertisement covered

end InterfaceObstruction

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreInitialExample

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreInitialExample.ports
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreInitialExample.callbackAuth
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreInitialExample.protectedAuth
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreInitialExample.InterfaceObstruction.source_store
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreInitialExample.InterfaceObstruction.interface
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreInitialExample.InterfaceObstruction.suffix_rows_impossible
