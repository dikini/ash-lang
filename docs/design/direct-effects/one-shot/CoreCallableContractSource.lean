import CoreCallableRootRefinement

/-! Separate contract-source experiment for DN-0033. A public callable checking
contract retains declared ports and rows; the lambda keeps its recursively
constructed private body and a contextual refinement. This is not a constructor
of the legacy Source/Auth or M4 execution judgments. -/
namespace Ash.OneShot.CoreCallableContractSource
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlanSignatures (Signature signature)
open SourceDeclarationPlans (Plan)
open SourceDependencyAnnotations (Dependencies RowAnnotation)
open SourcePlannedTyping (Value)
open RecursiveRequirements (Requirements Checked)
open SourceScheduledCleanupInterfaces.Lexical.Recursive (annotateDisposals)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open CoreCallableRootRefinement (Refines RootTransport)

/-- Public checking data, distinct from a lambda's private body derivation. -/
inductive Contract where
  | unit | boolean | integer
  | reference : Nat → Contract
  | pair : Contract → Contract → Contract
  | function : Contract → Contract → List Instance → Footprint →
      {dependencies : Dependencies} → (plan : Plan dependencies) → Rows (signature plan) → Contract

namespace Contract
def value : Contract → Value
  | .unit => .unit
  | .boolean => .boolean
  | .integer => .integer
  | .reference identity => .reference identity
  | .pair left right => .pair left.value right.value
  | .function input output requests latent plan _ =>
      .function input.value output.value requests latent (signature plan)
def rows : (contract : Contract) → ValueRows contract.value
  | .unit => .unit
  | .boolean => .boolean
  | .integer => .integer
  | .reference _ => .reference
  | .pair left right => .pair left.rows right.rows
  | .function input output _ _ _ rows => .function input.rows output.rows rows
def port (contract : Contract) : ScopedPorts.Port := contract.value.erase.erase.port
end Contract

abbrev Environment := Nat → Option Contract
namespace Environment
def empty : Environment := fun _ => none
def extend (environment : Environment) (name : Nat) (contract : Contract) : Environment :=
  fun other => if other = name then some contract else environment other
def ports (environment : Environment) : ScopedPorts.TypeEnv :=
  fun name => (environment name).map Contract.port
@[simp] theorem ports_extend (environment : Environment) (name : Nat) (contract : Contract) :
    (environment.extend name contract).ports = environment.ports.extend name contract.port := by
  funext other
  by_cases same : other = name <;> simp [ports, extend, ScopedPorts.TypeEnv.extend, same]
theorem extend_shadow (environment : Environment) (name : Nat) (first last : Contract) :
    (environment.extend name first).extend name last = environment.extend name last := by
  funext other
  by_cases same : other = name <;> simp [extend, same]
theorem extend_commute (environment : Environment) (name binder : Nat) (input bound : Contract)
    (different : name ≠ binder) :
    (environment.extend name input).extend binder bound = (environment.extend binder bound).extend name input := by
  funext other
  by_cases first : other = name <;> by_cases second : other = binder <;> simp_all [extend]
end Environment

def sequenceRows {first : Plan firstDependencies} {second : Plan secondDependencies}
    (left : Rows (signature first)) (right : Rows (signature second)) : Rows (signature (.sequence first second)) := by
  simpa only [signature] using Rows.sequence left right

def choiceRows {first : Plan firstDependencies} {second : Plan secondDependencies}
    (left : Rows (signature first)) (right : Rows (signature second)) : Rows (signature (.choice first second)) := by
  simpa only [signature] using Rows.choice left right

/-- One structural derivation of actual syntax. Application uses public rows;
lambda keeps its actual-body rows and refinement without identifying them. -/
inductive Source (world : List Nat) : List Instance → Environment → Code → Contract →
    {dependencies : Dependencies} → (plan : Plan dependencies) → Rows (signature plan) → Prop where
  | unit : Source world allowed environment .unit .unit .pure Rows.pure
  | boolean : Source world allowed environment (.boolean value) .boolean .pure Rows.pure
  | integer : Source world allowed environment (.integer value) .integer .pure Rows.pure
  | reference (issued : identity ∈ world) :
      Source world allowed environment (.resourceRef (.activation identity)) (.reference identity) .pure Rows.pure
  | variable (known : environment name = some contract) (formed : ScopedPorts.InWorld world contract.port) :
      Source world allowed environment (.variable name) contract .pure Rows.pure
  | lambda {contractDependencies : Dependencies} {contractPlan : Plan contractDependencies}
      {contractRows : Rows (signature contractPlan)} (body : Source world requests (environment.extend parameter input) code output actualPlan actualRows)
      (refinement : Refines contractRows actualRows)
      (formed : ScopedPorts.InWorld world (Contract.function input output requests latent contractPlan contractRows).port) :
      Source world allowed environment (.lambda parameter code)
        (Contract.function input output requests latent contractPlan contractRows) .pure Rows.pure
  | purePair (left : Source world allowed environment a first .pure Rows.pure)
      (right : Source world allowed environment b second .pure Rows.pure) :
      Source world allowed environment (.pair a b) (.pair first second) .pure Rows.pure
  | pair (left : Source world allowed environment a first leftPlan leftRows)
      (right : Source world allowed environment b second rightPlan rightRows) :
      Source world allowed environment (.pair a b) (.pair first second) (.sequence leftPlan rightPlan) (sequenceRows leftRows rightRows)
  | app (function : Source world allowed environment f
        (Contract.function input output requests latent contractPlan contractRows) functionPlan functionRows)
      (argument : Source world allowed environment a input argumentPlan argumentRows) (admitted : requests ⊆ allowed) :
      Source world allowed environment (.app f a) output
        (.sequence functionPlan (.sequence argumentPlan contractPlan)) (sequenceRows functionRows (sequenceRows argumentRows contractRows))
  | bind (initializer : Source world allowed environment a input initialPlan initialRows)
      (body : Source world allowed (environment.extend parameter input) b output bodyPlan bodyRows) :
      Source world allowed environment (.bind parameter a b) output (.sequence initialPlan bodyPlan) (sequenceRows initialRows bodyRows)
  | branch (condition : Source world allowed environment test .boolean conditionPlan conditionRows)
      (yes : Source world allowed environment a output yesPlan yesRows)
      (no : Source world allowed environment b output noPlan noRows) :
      Source world allowed environment (.branch test a b) output (.sequence conditionPlan (.choice yesPlan noPlan))
        (sequenceRows conditionRows (choiceRows yesRows noRows))

/-- Declared erasure changes no request instance or ordinary port. Retained
support is checked independently; erasure alone is not whole admission. -/
theorem Source.erase (source : Source world allowed environment code contract plan rows)
    (operations : ScopedPorts.Signature) :
    ScopedPorts.Typed operations world environment.ports .none allowed code contract.port := by
  induction source with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference issued => exact .reference issued
  | «variable» known formed => exact .variable (by simp [Environment.ports, known]) formed
  | lambda body refinement formed ih => exact .lambda (by simpa only [Environment.ports_extend, Contract.port] using ih) formed
  | purePair left right ihL ihR | pair left right ihL ihR => exact .pair ihL ihR
  | app function argument admitted ihF ihA => exact .app ihF ihA admitted
  | bind initial body ihI ihB => exact .bind ihI (by simpa using ihB)
  | branch condition yes no ihC ihY ihN => exact .branch ihC ihY ihN

/-- Only actual free ordinary names constrain lexical transport. The private
body derivations are transported recursively, not replaced with a summary. -/
theorem Source.environment_congr (source : Source world allowed environment code contract plan rows)
    (agree : ∀ name, Syntax.Dependency.variable name ∈ code.dependencies → environment name = destination name) :
    Source world allowed destination code contract plan rows := by
  induction source generalizing destination with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference issued => exact .reference issued
  | «variable» known formed => exact .variable ((agree _ (by simp [Code.dependencies])).symm.trans known) formed
  | lambda body refinement formed ih =>
      rename_i parameter contractDependencies contractPlan contractRows
      apply Source.lambda (ih ?_) refinement formed
      intro name member
      by_cases same : name = parameter
      · subst name; simp [Environment.extend]
      · simp only [Environment.extend, same, ↓reduceIte]
        exact agree name (Syntax.mem_without.mpr ⟨member, by simpa using same⟩)
  | purePair left right ihL ihR =>
      exact .purePair (ihL (fun name member => agree name (List.mem_append_left _ member)))
        (ihR (fun name member => agree name (List.mem_append_right _ member)))
  | pair left right ihL ihR =>
      exact .pair (ihL (fun name member => agree name (List.mem_append_left _ member)))
        (ihR (fun name member => agree name (List.mem_append_right _ member)))
  | app function argument admitted ihF ihA =>
      exact .app (ihF (fun name member => agree name (List.mem_append_left _ member)))
        (ihA (fun name member => agree name (List.mem_append_right _ member))) admitted
  | bind initial body ihI ihB =>
      rename_i parameter b output bodyDependencies bodySignature bodyRows
      apply Source.bind (ihI (fun name member => agree name (List.mem_append_left _ member))) (ihB ?_)
      intro name member
      by_cases same : name = parameter
      · subst name; simp [Environment.extend]
      · simp only [Environment.extend, same, ↓reduceIte]
        exact agree name (List.mem_append_right _ (Syntax.mem_without.mpr ⟨member, by simpa using same⟩))
  | branch condition yes no ihC ihY ihN =>
      exact .branch
        (ihC (fun name member => agree name (List.mem_append_left _ (List.mem_append_left _ member))))
        (ihY (fun name member => agree name (List.mem_append_left _ (List.mem_append_right _ member))))
        (ihN (fun name member => agree name (List.mem_append_right _ member)))

theorem Source.closed_environment (source : Source world allowed environment value contract .pure Rows.pure)
    (closed : ClosedValue value) (destination : Environment) : Source world allowed destination value contract .pure Rows.pure :=
  source.environment_congr (fun _ member => False.elim (ScopedTyping.closedValue_no_variable closed member))

/-- Closed values retain their public contract when the caller's allowed row
changes. The private lambda body continues under its own declared requests. -/
theorem Source.value_allowed (source : Source world allowed environment value contract plan rows)
    (valueIsValue : value.IsValue) (next : List Instance) : Source world next environment value contract plan rows := by
  induction source with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference issued => exact .reference issued
  | lambda body refinement formed ih => exact .lambda body refinement formed
  | purePair left right ihL ihR => exact .purePair (ihL valueIsValue.1) (ihR valueIsValue.2)
  | pair left right ihL ihR => exact .pair (ihL valueIsValue.1) (ihR valueIsValue.2)
  | «variable» | app | bind | branch => cases valueIsValue

/-- Normalize only immediate checking rows of a value. The public contract
and each lambda's private recursive body/refinement remain unchanged. -/
theorem Source.value_summary (source : Source world allowed environment value contract plan rows)
    (valueIsValue : value.IsValue) : Source world allowed environment value contract .pure Rows.pure := by
  induction source with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference issued => exact .reference issued
  | lambda body refinement formed ih => exact .lambda body refinement formed
  | purePair left right ihL ihR | pair left right ihL ihR =>
      exact .purePair (ihL valueIsValue.1) (ihR valueIsValue.2)
  | «variable» | app | bind | branch => cases valueIsValue

/-- Compositional substitution for this contract judgment. It preserves the
same exposed contract and rows, including private lambda-body refinements. -/
theorem Source.substitution_at (source : Source world allowed sourceEnvironment code result plan rows) :
    ∀ environment name input value, sourceEnvironment = environment.extend name input →
      Source world allowed environment value input .pure Rows.pure → ClosedValue value →
      Source world allowed environment (code.subst name value) result plan rows := by
  induction source with
  | unit | boolean | integer | reference =>
      intro environment name input value same replacement closed
      cases same
      first | exact .unit | exact .boolean | exact .integer | apply Source.reference; assumption
  | «variable» known formed =>
      intro environment name input value same replacement closed
      cases same
      simp only [Code.subst]
      split
      · rename_i equal
        subst name
        simp only [Environment.extend, ↓reduceIte] at known
        cases Option.some.inj known
        exact replacement
      · rename_i different
        exact .variable (by simpa [Environment.extend, Ne.symm different] using known) formed
  | lambda body refinement formed ih =>
      intro environment name input value same replacement closed
      cases same
      simp only [Code.subst]
      apply Source.lambda _ refinement formed
      split
      · rename_i equal
        subst name
        simpa only [Environment.extend_shadow] using body
      · rename_i different
        exact ih _ name input value (Environment.extend_commute environment name _ input _ different)
          ((replacement.value_allowed closed.1 _).closed_environment closed _) closed
  | purePair left right ihL ihR =>
      intro environment name input value same replacement closed
      cases same
      exact .purePair (ihL environment name input value rfl replacement closed) (ihR environment name input value rfl replacement closed)
  | pair left right ihL ihR =>
      intro environment name input value same replacement closed
      cases same
      exact .pair (ihL environment name input value rfl replacement closed) (ihR environment name input value rfl replacement closed)
  | app function argument admitted ihF ihA =>
      intro environment name input value same replacement closed
      cases same
      exact .app (ihF environment name input value rfl replacement closed) (ihA environment name input value rfl replacement closed) admitted
  | bind initial body ihI ihB =>
      intro environment name input value same replacement closed
      cases same
      simp only [Code.subst]
      apply Source.bind (ihI environment name input value rfl replacement closed)
      split
      · rename_i equal
        subst name
        simpa only [Environment.extend_shadow] using body
      · rename_i different
        exact ihB _ name input value (Environment.extend_commute environment name _ input _ different)
          (replacement.closed_environment closed _) closed
  | branch condition yes no ihC ihY ihN =>
      intro environment name input value same replacement closed
      cases same
      exact .branch (ihC environment name input value rfl replacement closed)
        (ihY environment name input value rfl replacement closed) (ihN environment name input value rfl replacement closed)

theorem Source.substitution
    (source : Source world allowed (environment.extend name input) code result plan rows)
    (replacement : Source world allowed environment value input .pure Rows.pure) (closed : ClosedValue value) :
    Source world allowed environment (code.subst name value) result plan rows :=
  source.substitution_at environment name input value rfl replacement closed

/-- Closed products as well as primitive and callable values may substitute;
only their immediate value-checking rows are normalized. -/
theorem Source.closed_substitution
    (source : Source world allowed (environment.extend name input) code result plan rows)
    (replacement : Source world allowed environment value input replacementPlan replacementRows) (closed : ClosedValue value) :
    Source world allowed environment (code.subst name value) result plan rows :=
  source.substitution (replacement.value_summary closed.1) closed

/-- Independent lexical support uses actual dependencies and supplied finite
value-support entries. Neither a result port nor an unknown-to-empty default
provides a captured resource bound. -/
structure Supported (world : List Nat) (allowed : List Instance) (environment : Environment)
    (supportEnvironment : ScopedPorts.Support.Env) (code : Code) (contract : Contract)
    {dependencies : Dependencies} (plan : Plan dependencies) (rows : Rows (signature plan))
    (bound : List Nat) : Prop where
  source : Source world allowed environment code contract plan rows
  support : SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.Bounds supportEnvironment code.dependencies bound
  issued : bound ⊆ world

namespace Supported
open SourceScheduledCleanupInterfaces.Lexical.Recursive
open ScopedPorts.Support (evaluate extend)

theorem canonical (source : Source world allowed environment code contract plan rows)
    (supportEnvironment : ScopedPorts.Support.Env)
    (issued : evaluate supportEnvironment code.dependencies ⊆ world) :
    Supported world allowed environment supportEnvironment code contract plan rows
      (evaluate supportEnvironment code.dependencies) :=
  ⟨source, SourceSupport.Bounds.canonical _ _, issued⟩

theorem substitution
    (body : Supported world allowed (environment.extend name input)
      (extend supportEnvironment name valueBound) code output plan rows bodyBound)
    (replacement : Supported world allowed environment replacementEnvironment value input replacementPlan replacementRows valueBound)
    (closed : ClosedValue value) :
    Supported world allowed environment supportEnvironment (code.subst name value) output plan rows bodyBound := by
  refine ⟨body.source.closed_substitution replacement.source closed, ?_, body.issued⟩
  apply SourceSupport.bounds_iff.mpr
  exact (ScopedPorts.Support.substitution_support_bound code name closed replacement.support.resources).trans
    (SourceSupport.bounds_iff.mp body.support)
end Supported

/-- Inversion recovers the selected private actual body from the very lambda
source used by a caller; no successor source is supplied. -/
theorem Source.lambda_body
    (source : Source world allowed environment (.lambda parameter body)
      (Contract.function input output requests latent contractPlan contractRows) .pure Rows.pure) :
    ∃ (actualDependencies : Dependencies) (actualPlan : Plan actualDependencies)
      (actualRows : Rows (signature actualPlan)),
      Source world requests (environment.extend parameter input) body output actualPlan actualRows ∧
      Refines contractRows actualRows := by
  cases source with
  | lambda body refinement formed => exact ⟨_, _, _, body, refinement⟩

/-- Beta obtains the actual body by inversion, substitutes the same public
argument contract, and retains the contract-to-actual row refinement. -/
theorem Source.beta
    (function : Source world allowed environment (.lambda parameter body)
      (Contract.function input output requests latent contractPlan contractRows) .pure Rows.pure)
    (argument : Source world requests environment value input argumentPlan argumentRows)
    (closed : ClosedValue value) (closureReady : ClosedValue (.lambda parameter body))
    (runtimeScope : Execution.Scope) (stack : Stack) :
    ∃ (actualDependencies : Dependencies) (actualPlan : Plan actualDependencies)
      (actualRows : Rows (signature actualPlan)),
      Source world requests environment (body.subst parameter value) output actualPlan actualRows ∧
      Refines contractRows actualRows ∧
      RawStep ⟨.app (.lambda parameter body) value, runtimeScope, stack⟩
        ⟨body.subst parameter value, .none, stack⟩ [] [] := by
  obtain ⟨dependencies, plan, rows, actualBody, refinement⟩ := function.lambda_body
  exact ⟨dependencies, plan, rows, actualBody.closed_substitution argument closed, refinement,
    .beta parameter body value runtimeScope stack closed closureReady⟩

/-- Current static fields for the selected actual body. Actual normal and
annotated roots keep the contract's demand index and current checking budget.
These fields do not manufacture legacy Auth or an M4 ExecutionSite. -/
theorem Source.beta_current
    (function : Source world allowed environment (.lambda parameter body)
      (Contract.function input output requests latent contractPlan contractRows) .pure Rows.pure)
    (argument : Source world requests environment value input argumentPlan argumentRows)
    (closed : ClosedValue value) (closureReady : ClosedValue (.lambda parameter body))
    (runtimeScope : Execution.Scope) (stack : Stack)
    (installations ambient : List Nat) (outward : List Instance) (actions : Syntax.UsageTickets)
    (phases : OwnerPhaseTransitions.Phases) (budget : Footprint)
    {scope : SourceDependencyCapture.Scope} {hints : SourceDependencyChecks.Lexical.ReturnHints scope}
    (context : Context hints)
    (certificate : SourceAdmission.Code outward actions budget phases world installations contractRows context)
    (certificateChecked : InstallationSupport.CodeChecked ambient outward certificate)
    (root annotated : Requirements demand)
    (run : Accounting.Run world installations contractRows context root)
    (entries : RecursiveRequirements.Store) (receiving : OwnerPhases.Context) (row : Footprint)
    (annotation : RowAnnotation root annotated)
    (check : Checked entries receiving phases (annotateDisposals annotated) row) (bounded : row ⊆ budget) :
    ∃ (actualDependencies : Dependencies) (actualPlan : Plan actualDependencies)
      (actualRows : Rows (signature actualPlan)),
      Source world requests environment (body.subst parameter value) output actualPlan actualRows ∧
      RawStep ⟨.app (.lambda parameter body) value, runtimeScope, stack⟩
        ⟨body.subst parameter value, .none, stack⟩ [] [] ∧
      ∃ actualCertificate : SourceAdmission.Code outward actions budget phases world installations actualRows context,
        InstallationSupport.CodeChecked ambient outward actualCertificate ∧
        ∃ actualRoot actualAnnotated : Requirements demand, ∃ actualRow : Footprint,
          Accounting.Run world installations actualRows context actualRoot ∧
          RootTransport root actualRoot ∧ RowAnnotation actualRoot actualAnnotated ∧
          Checked entries receiving phases (annotateDisposals actualAnnotated) actualRow ∧ actualRow ⊆ budget := by
  obtain ⟨dependencies, plan, rows, bodySource, refinement, raw⟩ :=
    function.beta argument closed closureReady runtimeScope stack
  let actualCertificate := refinement.code outward actions budget phases world installations context certificate
  obtain ⟨actualRoot, actualAnnotated, actualRow, actualRun, transport, actualAnnotation, actualCheck, actualBound⟩ :=
    CoreCallableRootRefinement.checked_accounting refinement world installations context root annotated run
      entries receiving phases budget row annotation check bounded
  exact ⟨dependencies, plan, rows, bodySource, raw, actualCertificate,
    refinement.checked ambient outward actions budget phases world installations context certificate certificateChecked,
    actualRoot, actualAnnotated, actualRow, actualRun, transport, actualAnnotation, actualCheck, actualBound⟩

/-- Bind reduction uses the initializer and body in this same derivation. -/
theorem Source.bind_step
    (source : Source world allowed environment (.bind parameter value body) output
      (.sequence .pure bodyPlan) (sequenceRows Rows.pure bodyRows))
    (closed : ClosedValue value) (ready : ClosedExcept parameter body)
    (runtimeScope : Execution.Scope) (stack : Stack) :
    Source world allowed environment (body.subst parameter value) output bodyPlan bodyRows ∧
      RawStep ⟨.bind parameter value body, runtimeScope, stack⟩
        ⟨body.subst parameter value, runtimeScope, stack⟩ [] [] := by
  cases source with
  | bind initializer bodySource =>
    exact ⟨bodySource.substitution initializer closed, .bind parameter value body runtimeScope stack closed ready⟩

theorem Source.true_step
    (source : Source world allowed environment (.branch (.boolean true) yes no) output
      (.sequence .pure (.choice yesPlan noPlan)) (sequenceRows Rows.pure (choiceRows yesRows noRows)))
    (runtimeScope : Execution.Scope) (stack : Stack) :
    Source world allowed environment yes output yesPlan yesRows ∧
      RawStep ⟨.branch (.boolean true) yes no, runtimeScope, stack⟩ ⟨yes, runtimeScope, stack⟩ [] [] := by
  cases source with
  | branch condition yesSource noSource => exact ⟨yesSource, .ifTrue yes no runtimeScope stack⟩

theorem Source.false_step
    (source : Source world allowed environment (.branch (.boolean false) yes no) output
      (.sequence .pure (.choice yesPlan noPlan)) (sequenceRows Rows.pure (choiceRows yesRows noRows)))
    (runtimeScope : Execution.Scope) (stack : Stack) :
    Source world allowed environment no output noPlan noRows ∧
      RawStep ⟨.branch (.boolean false) yes no, runtimeScope, stack⟩ ⟨no, runtimeScope, stack⟩ [] [] := by
  cases source with
  | branch condition yesSource noSource => exact ⟨noSource, .ifFalse yes no runtimeScope stack⟩

/- Rows/root refinement alone does not transport SourcePlannedChecks.Certified.
The actual Plan is retained here so ordinary examples can construct its
certification structurally. Effectful/handler-bearing private plans still need
actual declaration certification or a proved transport. Legacy ExecutionSite
current/pending/coherent and whole InitialAdmission are not supplied here. -/

#print axioms Source.bind_step
#print axioms Source.true_step
#print axioms Source.false_step
#print axioms Source.lambda_body
#print axioms Source.beta
#print axioms Source.beta_current
#print axioms Source.erase
#print axioms Source.environment_congr
#print axioms Source.value_summary
#print axioms Source.closed_substitution
#print axioms Supported.substitution

end Ash.OneShot.CoreCallableContractSource
