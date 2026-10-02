import CoreCallableCompositionalResourceOpening
import CoreCallableInitialAdmission
namespace Ash.OneShot.CoreCallableCompositionalAdmissionFacets
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract Environment sequenceRows choiceRows)
open CoreCallableStaticProducer (RecipeTag Annotation)
open CoreCallableCompositionalResourceBody (Checking)
open SourceDeclarationPlans (Plan)
open SourceDependencyAnnotations (Dependencies)
open SourcePlanSignatures (signature)
open RecursiveRequirements (Requirements)
open SourceScheduledCleanupInterfaces.Lexical.Recursive
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
local instance : SourcePlannedChecks.DeclarationPolicy := declarationPolicy
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- Computed continuation accounting. Branches remain actual choice roots. -/
inductive Account where
  | done
  | choice : Account → Account → Account
  deriving DecidableEq

def Account.requirements : Account → Requirements []
  | .done => .request [] []
  | .choice first second => .choice first.requirements second.requirements (List.Perm.refl [])

def quietCheck : RecipeTag plan → Bool
  | .pure => true
  | .sequence first second | .choice first second => quietCheck first && quietCheck second
  | .request | .invoke | .cleanup _ _ | .unsupported _ => false

def quietAccount : RecipeTag plan → Account → Account
  | .sequence first second,tail => quietAccount first (quietAccount second tail)
  | .choice first second,tail => .choice (quietAccount first tail) (quietAccount second tail)
  | _,tail => tail

/-- Joint outputs on the same exact rows and contextual certificate. -/
structure Facets (outward : List Instance) (actions : Syntax.UsageTickets) (budget : Footprint)
    (phases : OwnerPhaseTransitions.Phases) (world installations ambient : List Nat)
    (rows : Rows checking) (context : Context hints) (account : Account) : Prop where
  certificate : SourceAdmission.Code outward actions budget phases world installations rows context
  checked : InstallationSupport.CodeChecked ambient outward certificate
  accounting : Accounting.Run world installations rows context account.requirements

private theorem quiet_facets {scope : SourceDependencyCapture.Scope} {hints : SourceDependencyChecks.Lexical.ReturnHints scope}
    {context : Context hints} (tag : RecipeTag plan) (rows : Rows (signature plan))
    (valid : quietCheck tag = true)
    (waiting : Accounting.Wait world installations context .ordinary tail.requirements) :
    Facets outward actions budget phases world installations ambient rows context (quietAccount tag tail) := by
  induction tag generalizing scope hints context tail with
  | pure => cases rows; exact ⟨.pure,.pure,.pure waiting⟩
  | sequence first second ihF ihS =>
    cases rows with
    | sequence firstRows secondRows =>
      obtain ⟨a,b⟩ : quietCheck first = true ∧ quietCheck second = true := by simpa [quietCheck] using valid
      let right := ihS secondRows b waiting
      let left := ihF firstRows a (Accounting.Wait.plain right.accounting)
      exact ⟨.sequence left.certificate right.certificate,.sequence left.checked right.checked,.sequence left.accounting⟩
  | choice first second ihF ihS =>
    cases rows with
    | choice firstRows secondRows =>
      obtain ⟨a,b⟩ : quietCheck first = true ∧ quietCheck second = true := by simpa [quietCheck] using valid
      let left := ihF firstRows a waiting
      let right := ihS secondRows b waiting
      exact ⟨.choice left.certificate right.certificate,.choice left.checked right.checked,
        .choice left.accounting right.accounting (List.Perm.refl [])⟩
  | request | invoke | cleanup | unsupported => cases valid

/-- Existing initializer annotation supplies finite recipe instructions; no
contextual proof is stored in this interpretation. -/
def annotationRecipe (annotation : Annotation entries owners bindings code contract demand req plan rows) : RecipeTag plan := by
  cases annotation with
  | unit | boolean | integer | reference | «variable» | lambda => exact .pure
  | pair first second | bind first second => exact .sequence (annotationRecipe first) (annotationRecipe second)
  | app function argument recipe => exact .sequence (annotationRecipe function) (.sequence (annotationRecipe argument) recipe)
  | perform reference operand => exact .sequence (annotationRecipe operand) .request
  | resume reference operand => exact .sequence (annotationRecipe operand) .invoke
  | discard reference => exact .invoke
  | cleanup callback body recipe => exact .sequence (annotationRecipe callback) (.cleanup recipe (annotationRecipe body))
  | branch condition yes no same => exact .sequence (annotationRecipe condition) (.choice (annotationRecipe yes) (annotationRecipe no))
  | unsupported => exact .unsupported _
termination_by sizeOf code

private def CellHere (identity : Nat) (context : Context hints) : Prop :=
  ∀ operation, select (.cell identity) operation context = some (.builtin identity)
private theorem cell_plain (here : CellHere identity context) : CellHere identity (.plain rows context) := by
  intro operation
  simp [select,here operation,Selection.prepend]

private def boundCheck (binder : Nat) : Instantiation.ResourceName → Bool
  | .bound name => decide (name = binder)
  | .activation _ => false
private theorem bound_value (valid : boundCheck binder name = true) :
    CoreCallableFiniteResourceTemplate.nameValue identity name = identity := by
  cases name with
  | bound name => rfl
  | activation value => cases valid

private def oldCheck (binder : Nat) : CoreCallableFiniteResourceTemplate.Body context code pattern → Bool
  | .unit | .boolean _ | .integer _ | .reference _ | .variable _ => true
  | .pair first second | .bind first second => oldCheck binder first && oldCheck binder second
  | .read (name := name) operand | .write (name := name) operand => oldCheck binder operand && boundCheck binder name

private theorem old_facets {scope : SourceDependencyCapture.Scope} {hints : SourceDependencyChecks.Lexical.ReturnHints scope}
    {context : Context hints} (body : CoreCallableFiniteResourceTemplate.Body lexical code pattern)
    (valid : oldCheck binder body = true) (here : CellHere identity context)
    (waiting : Accounting.Wait world installations context .ordinary tail.requirements) :
    Facets outward actions budget phases world installations ambient (body.rows identity) context tail := by
  induction body generalizing scope hints context with
  | unit | boolean | integer | reference | «variable» => exact ⟨.pure,.pure,.pure waiting⟩
  | pair first second ihF ihS | bind first second ihF ihS =>
    obtain ⟨a,b⟩ : oldCheck binder first = true ∧ oldCheck binder second = true := by simpa [oldCheck] using valid
    let right := ihS b here waiting
    let left := ihF a (cell_plain here) (Accounting.Wait.plain right.accounting)
    exact ⟨.sequence left.certificate right.certificate,.sequence left.checked right.checked,.sequence left.accounting⟩
  | @read lexical code name operand ih =>
    obtain ⟨a,b⟩ : oldCheck binder operand = true ∧ boundCheck binder name = true := by simpa [oldCheck] using valid
    have found : select (.cell (CoreCallableFiniteResourceTemplate.nameValue identity name)) 0 context = some (.builtin identity) := by
      rw [bound_value b]; exact here 0
    let left := ih a (cell_plain here) (Accounting.Wait.plain (Accounting.Run.builtin found waiting))
    exact ⟨.sequence left.certificate (.builtin found),.sequence left.checked (.builtin (found := found)),.sequence left.accounting⟩
  | @write lexical code name operand ih =>
    obtain ⟨a,b⟩ : oldCheck binder operand = true ∧ boundCheck binder name = true := by simpa [oldCheck] using valid
    have found : select (.cell (CoreCallableFiniteResourceTemplate.nameValue identity name)) 1 context = some (.builtin identity) := by
      rw [bound_value b]; exact here 1
    let left := ih a (cell_plain here) (Accounting.Wait.plain (Accounting.Run.builtin found waiting))
    exact ⟨.sequence left.certificate (.builtin found),.sequence left.checked (.builtin (found := found)),.sequence left.accounting⟩

/-- Universal fresh-cell validity is checked symbolically. Closed opaque rows
retain their original full Plan and Rows; unavailable literal requests fail. -/
def cellCheck (binder : Nat) : Checking → Bool
  | .pure => true
  | .embedded body => oldCheck binder body
  | .request (.cell name) _ => boundCheck binder name
  | .request (.closed _) _ => false
  | .sequence first second | .choice first second => cellCheck binder first && cellCheck binder second
  | .closed _ _ recipe => quietCheck recipe

def checkingAccount : Checking → Account → Account
  | .sequence first second,tail => checkingAccount first (checkingAccount second tail)
  | .choice first second,tail => .choice (checkingAccount first tail) (checkingAccount second tail)
  | .closed _ _ recipe,tail => quietAccount recipe tail
  | _,tail => tail

private theorem checking_facets {scope : SourceDependencyCapture.Scope} {hints : SourceDependencyChecks.Lexical.ReturnHints scope}
    {context : Context hints} (checking : Checking) (valid : cellCheck binder checking = true)
    (here : CellHere identity context)
    (waiting : Accounting.Wait world installations context .ordinary tail.requirements) :
    Facets outward actions budget phases world installations ambient (checking.rows identity) context (checkingAccount checking tail) := by
  induction checking generalizing scope hints context tail with
  | pure => exact ⟨.pure,.pure,.pure waiting⟩
  | embedded body => exact old_facets body valid here waiting
  | request effect operation =>
    cases effect with
    | cell name =>
      have found : select (.cell (CoreCallableFiniteResourceTemplate.nameValue identity name)) operation context = some (.builtin identity) := by
        rw [bound_value valid]; exact here _
      exact ⟨.builtin found,.builtin (found := found),.builtin found waiting⟩
    | closed effect => cases valid
  | sequence first second ihF ihS =>
    obtain ⟨a,b⟩ : cellCheck binder first = true ∧ cellCheck binder second = true := by simpa [cellCheck] using valid
    let right := ihS b here waiting
    let left := ihF a (cell_plain here) (Accounting.Wait.plain right.accounting)
    exact ⟨.sequence left.certificate right.certificate,.sequence left.checked right.checked,.sequence left.accounting⟩
  | choice first second ihF ihS =>
    obtain ⟨a,b⟩ : cellCheck binder first = true ∧ cellCheck binder second = true := by simpa [cellCheck] using valid
    let left := ihF a here waiting
    let right := ihS b here waiting
    exact ⟨.choice left.certificate right.certificate,.choice left.checked right.checked,
      .choice left.accounting right.accounting (List.Perm.refl [])⟩
  | closed plan rows recipe => exact quiet_facets recipe rows valid waiting

/-- Same actual syntax usage, including lambda bodies. Unsupported capability
or handler forms report failure rather than assuming a Usage judgment. -/
def usageCheck : Code → Bool
  | .unit | .boolean _ | .integer _ | .variable _ | .resourceRef _ => true
  | .pair first second | .app first second | .bind _ first second | .resource _ first second | .cleanup first second =>
      usageCheck first && usageCheck second
  | .lambda _ body | .perform _ _ body => usageCheck body
  | .branch condition yes no => usageCheck condition && usageCheck yes && usageCheck no
  | .handle _ _ _ | .resume _ _ | .discard _ => false

theorem usage_sound (code : Code) (valid : usageCheck code = true) : Uses policy scope state code state := by
  cases code with
  | unit => exact .unit
  | boolean value => exact .boolean
  | integer value => exact .integer
  | «variable» name => exact .variable
  | resourceRef name => exact .resourceRef
  | pair first second | app first second | bind name first second | resource name first second | cleanup first second =>
    obtain ⟨a,b⟩ : usageCheck first = true ∧ usageCheck second = true := by simpa [usageCheck] using valid
    first
    | exact .pair (usage_sound first a) (usage_sound second b)
    | exact .app (usage_sound first a) (usage_sound second b)
    | exact .bind (usage_sound first a) (usage_sound second b)
    | exact .resource (usage_sound first a) (usage_sound second b)
    | exact .cleanup (usage_sound first a) (usage_sound second b)
  | lambda parameter body => exact .lambda (usage_sound body valid)
  | perform effect operation body => exact .perform (usage_sound body valid)
  | branch condition yes no =>
    obtain ⟨⟨a,b⟩,c⟩ : (usageCheck condition = true ∧ usageCheck yes = true) ∧ usageCheck no = true := by
      simpa [usageCheck] using valid
    exact .branch (usage_sound condition a) (usage_sound yes b) (usage_sound no c)
  | handle | resume | discard => cases valid
termination_by sizeOf code

/-- The same finite validator constructs the full family, at every identity.
Resource Source/Auth freshness remains the separate existing rich gate. -/
theorem fresh_facets (checking : Checking) (valid : cellCheck binder checking = true) (identity : Nat) :
    Facets outward actions budget phases (world ++ [identity]) installations ambient
      (checking.rows identity) (Context.cell (identity := identity) Context.nil) (checkingAccount checking .done) :=
  checking_facets checking valid (by intro operation; simp [select]) (.cell .nil)

open CoreCallableCompositionalResourceBody (Body)

def rootExpression (name : Nat) (value : Int) (binder : Nat) (initial body : Code) : Code :=
  .bind name (.integer value) (.resource binder initial body)

def rootPlan (body : Body original context code pattern checking needs) (initialPlan : Plan initialDependencies) :=
  Plan.sequence Plan.pure (CoreCallableCompositionalResourceOpening.combinedPlan body initialPlan)
def rootRows (body : Body original context code pattern checking needs) (initialRows : Rows (signature initialPlan)) :
    Rows (signature (rootPlan body initialPlan)) :=
  sequenceRows Rows.pure (CoreCallableCompositionalResourceOpening.combinedRows body initialRows)
def rootAccount (annotation : Annotation entries owners original initial .integer initialDemand initialReq initialPlan initialRows)
    (_body : Body original context code pattern checking needs) : Account :=
  quietAccount (annotationRecipe annotation) (checkingAccount checking .done)

theorem root_facets
    (annotation : Annotation entries owners original initial .integer initialDemand initialReq initialPlan initialRows)
    (body : Body original context code pattern checking needs)
    (initialValid : quietCheck (annotationRecipe annotation) = true) (bodyValid : cellCheck binder checking = true) :
    Facets [] (fun _ => none) budget (OwnerPhaseTransitions.available []) [] [] []
      (rootRows body initialRows) Context.nil (rootAccount annotation body) := by
  let inside := fun identity => fresh_facets (outward := []) (actions := fun _ => none) (budget := budget)
    (phases := OwnerPhaseTransitions.available []) (world := []) (installations := []) (ambient := []) checking bodyValid identity
  let resource : Facets [] (fun _ => none) budget (OwnerPhaseTransitions.available []) [] [] []
      (Rows.resource (fun identity => checking.rows identity)) Context.nil (checkingAccount checking .done) :=
    ⟨.resource (fun identity _ => (inside identity).certificate),
      .resource (fun identity _ => (inside identity).checked),
      .installResource (fun identity _ => (inside identity).accounting)⟩
  let initialized := quiet_facets (outward := []) (actions := fun _ => none) (budget := budget)
    (phases := OwnerPhaseTransitions.available []) (ambient := []) (annotationRecipe annotation) initialRows initialValid
    (Accounting.Wait.plain resource.accounting)
  exact ⟨.sequence .pure (.sequence initialized.certificate resource.certificate),
    .sequence .pure (.sequence initialized.checked resource.checked),
    .sequence (.pure (.plain (.sequence initialized.accounting)))⟩

inductive Error where
  | outer : CoreCallableFiniteRegistryBridge.Error → Error
  | resource : CoreCallableCompositionalResourceOpening.Error → Error
  | initializerContext
  | bodyContext
  | usage
  | support
  | accounting
  | budget
  deriving Repr

/-- Public finite contextual checker. Universal proofs are output from one
structural check, never identity-indexed accepted-check metadata. -/
def check_opened (checking : Checking) (binder : Nat) (world installations ambient : List Nat)
    (outward : List Instance) (actions : Syntax.UsageTickets) (budget : Footprint)
    (phases : OwnerPhaseTransitions.Phases) :
    Except Error (PLift (∀ identity, Facets outward actions budget phases (world ++ [identity]) installations ambient
      (checking.rows identity) (Context.cell (identity := identity) Context.nil) (checkingAccount checking .done))) :=
  if valid : cellCheck binder checking = true then .ok ⟨fun identity => fresh_facets checking valid identity⟩
  else .error .bodyContext

/-- All proof inputs below are private outputs of the finite public checker.
Program stores the SAME rich requirements and independent computed accounting. -/
private def buildProgram
    (annotation : Annotation entries owners [(name,.integer)] initial .integer initialDemand initialReq initialPlan initialRows)
    (body : Body [(name,.integer)] context code pattern checking needs)
    (outer : CoreCallableFiniteRegistryBridge.Rechecked api entries policy [] owners [] [] .none
      [] (.integer value) .integer [] (.request [] []) .pure Rows.pure ([] : CoreCallableReceiverRefinement.LexicalBounds) [])
    (resource : CoreCallableCompositionalResourceOpening.Result api entries policy [] owners [] [] [] .none
      [(name,.integer)] binder annotation body [(name,[])] [])
    (facets : Facets [] (fun _ => none) budget (OwnerPhaseTransitions.available []) [] [] []
      (rootRows body initialRows) Context.nil (rootAccount annotation body))
    (usage : usageCheck (rootExpression name value binder initial code) = true)
    (support : CoreCallableGraphAnnotationChecks.subsetB
      (ScopedPorts.Support.evaluate ScopedPorts.Support.empty (rootExpression name value binder initial code).dependencies) [] = true)
    (evaluated : RecursiveRequirements.evaluate [] [] (OwnerPhaseTransitions.available [])
      (annotateDisposals (rootAccount annotation body).requirements) = some row)
    (bounded : CoreCallableGraphAnnotationChecks.subsetB row budget = true) :
    CoreCallableInitialAdmission.Program
      ⟨CoreCallableFiniteCellRegistry.operations (some api) entries,policy,owners⟩
      (fun _ => none) budget (rootExpression name value binder initial code) := by
  let initialSource := Classical.choose outer
  have initialAuth := (Classical.choose_spec outer).2.1
  have rootSupport : SourceSupport.Bounds ScopedPorts.Support.empty
      (rootExpression name value binder initial code).dependencies [] :=
    SourceSupport.bounds_iff.mpr (CoreCallableGraphAnnotationChecks.subsetB_sound support)
  exact {
    result := pattern.value [(name,.integer)] 0
    dependencies := _
    plan := rootPlan body initialPlan
    rows := rootRows body initialRows
    demand := [] ++ (initialDemand ++ [])
    requirements := .sequence (.request [] []) (.sequence initialReq needs.outsideRequirements)
    source := .bind initialSource resource.source
    authenticated := .checked rootSupport (.bind initialAuth resource.authenticated)
    support := rootSupport
    usage := usage_sound _ usage
    certificate := facets.certificate
    certificateChecked := facets.checked
    rootDemand := []
    root := (rootAccount annotation body).requirements
    accounting := facets.accounting
    annotated := (rootAccount annotation body).requirements
    annotation := .original
    row := row
    checked := RecursiveRequirements.evaluate_sound evaluated
    bounded := CoreCallableGraphAnnotationChecks.subsetB_sound bounded }

/-- Executes original initializer/resource rich checks and contextual facets.
No desired Source/Auth, certificate, accounting, Usage or future-success family
is an input. The one outer integer bind is the connected closed-root slice. -/
def check
    (annotation : Annotation entries owners [(name,.integer)] initial .integer initialDemand initialReq initialPlan initialRows)
    (body : Body [(name,.integer)] context code pattern checking needs)
    (api : CoreCallableFiniteCellRegistry.CellApi) (policy : Syntax.TicketPolicy)
    (value : Int) (binder : Nat) (budget : Footprint) :
    Except Error (CoreCallableInitialAdmission.Program
      ⟨CoreCallableFiniteCellRegistry.operations (some api) entries,policy,owners⟩
      (fun _ => none) budget (rootExpression name value binder initial code)) := do
  match CoreCallableFiniteRegistryBridge.recheck
      (Annotation.integer value : Annotation entries owners [] (.integer value) .integer [] (.request [] []) .pure Rows.pure)
      api policy [] [] [] .none ([] : CoreCallableReceiverRefinement.LexicalBounds) [] with
  | .error error => .error (.outer error)
  | .ok outer =>
    match CoreCallableCompositionalResourceOpening.check_compositional annotation body api policy [] [] [] [] .none binder [(name,[])] [] with
    | .error error => .error (.resource error)
    | .ok resource =>
      if initialValid : quietCheck (annotationRecipe annotation) = true then
        if bodyValid : cellCheck binder checking = true then
          if usage : usageCheck (rootExpression name value binder initial code) = true then
            if support : CoreCallableGraphAnnotationChecks.subsetB
                (ScopedPorts.Support.evaluate ScopedPorts.Support.empty (rootExpression name value binder initial code).dependencies) [] = true then
              match evaluated : RecursiveRequirements.evaluate [] [] (OwnerPhaseTransitions.available [])
                  (annotateDisposals (rootAccount annotation body).requirements) with
              | none => .error .accounting
              | some row =>
                if bounded : CoreCallableGraphAnnotationChecks.subsetB row budget = true then
                  .ok (buildProgram annotation body outer.down resource.down (root_facets annotation body initialValid bodyValid)
                    usage support evaluated bounded)
                else .error .budget
            else .error .support
          else .error .usage
        else .error .bodyContext
      else .error .initializerContext

#print axioms annotationRecipe
#print axioms fresh_facets
#print axioms root_facets
#print axioms usage_sound
#print axioms check_opened
#print axioms check
end Ash.OneShot.CoreCallableCompositionalAdmissionFacets
