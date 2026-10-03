import CoreCallableContractAdmission
import CoreCallableOwnerMonotone

/-! Upper companion for a bounded current/plain-frame/builtin-reply migration.
It uses existing M4 certificates and accounting, but carries the new recursive
contract source instead of asserting legacy exact-body Auth. No back import
into the shared M4 module is required. -/
namespace Ash.OneShot.CoreCallableContractExecution
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceDependencyAnnotations (Dependencies RowAnnotation)
open SourceDependencyChecks.Lexical (ReturnHints)
open RecursiveRequirements (Requirements Checked)
open CoreCallableContractSource (Contract Environment sequenceRows)
open CoreCallableContractAdmission (Globals Source Supported IndexedSource)
open SourceScheduledCleanupInterfaces.Lexical.Recursive
open SourceScheduledCleanupInterfaces.Lexical.Recursive (annotateDisposals)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourcePlannedChecks (DeclarationPolicy Certified)

/-- These erasures retain the declared ports and latent scalar footprints,
without identifying a public signature with a lambda's private body signature. -/
def lowerOperations (globals : Globals) : CoherentSourceTypes.Operations :=
  fun effect operation => (globals.operations effect operation).map (fun pair =>
    (pair.1.value.erase.erase, pair.2.value.erase.erase))
def lowerEnvironment (environment : Environment) : CoherentSourceTypes.Environment :=
  fun name => (environment name).map (fun contract => contract.value.erase.erase)
@[simp] theorem lowerEnvironment_extend :
    lowerEnvironment (environment.extend name contract) =
      (lowerEnvironment environment).extend name contract.value.erase.erase := by
  funext other
  by_cases same : other = name <;> simp [lowerEnvironment, Environment.extend, CoherentSourceTypes.Environment.extend, same]

section
variable [evidence : DeclarationPolicy]
open CoreCallableReceiverRefinement (LexicalBounds)
open CoreCallableContractAdmission (Authenticated Hereditary SubstitutionPolicyStable)

def actualReceiver (world : List Nat) (receiving : SourceDependencyCapture.Scope) (ambient : List Nat) : List Nat :=
  (receiving.visibleResources ++ ambient).filter (fun identity => identity ∈ world)

omit evidence in
theorem actualReceiver.issued : actualReceiver world receiving ambient ⊆ world :=
  fun _ member => of_decide_eq_true (List.mem_filter.mp member).2
omit evidence in
theorem actualReceiver.received : actualReceiver world receiving ambient ⊆ receiving.visibleResources ++ ambient :=
  fun _ member => (List.mem_filter.mp member).1
omit evidence in
@[simp] theorem lowerOperations_ports :
    (lowerOperations globals).ports = globals.registry.ports := by
  funext effect operation
  simp only [lowerOperations, CoherentSourceTypes.Operations.ports, CoreCallableContractAdmission.Globals.registry,
    CoreCallableContractRegistries.Registry.ports, Option.map_map, Function.comp_def, CoreCallableContractSource.Contract.port]
omit evidence in
@[simp] theorem lowerEnvironment_ports :
    (lowerEnvironment environment).ports = environment.ports := by
  funext name
  simp only [lowerEnvironment, CoherentSourceTypes.Environment.ports, CoreCallableContractSource.Environment.ports,
    Option.map_map, Function.comp_def]
  cases environment name <;> rfl
theorem Source.lower (source : Source globals outward world allowed scope environment code contract demand requirements plan rows) :
    SourceTemplates.Expression (lowerOperations globals) globals.policy globals.owners.legacy.erase.erase world allowed scope
      (lowerEnvironment environment) code contract.value.erase.erase demand requirements := by
  rcases globals with ⟨operations, policy, owners⟩
  dsimp only [Source, CoreCallableContractAdmission.Globals.registry] at source ⊢
  induction source using IndexedSource.rec
    (motive_2 := fun _ _ _ _ _ _ _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ _ _ _ _ _ _ => True) with
  | unit => exact .stable .unit
  | boolean => exact .stable .boolean
  | integer => exact .stable .integer
  | reference issued => exact .stable (.reference issued)
  | «variable» known formed => exact .stable (.variable (by simp [lowerEnvironment, known]) formed)
  | lambda body refinement bodyOutward latentBound publicCertified formed ih =>
      exact .lambda (by simpa using ih) bodyOutward formed
  | receiverLambda body bodyOutward latentBound publicCertified formed ih =>
      exact .lambda (by simpa only [CoreCallableReceiverRefinement.CallBounds.current, lowerEnvironment_extend] using ih [] (CoreCallableReceiverRefinement.CallBounds.current _)) bodyOutward formed
  | purePair left right ihL ihR => exact .purePair ihL ihR
  | pair left right ihL ihR => exact .pair ihL ihR
  | app function argument admitted publicCertified ihF ihA => exact .app ihF ihA admitted
  | bind initial body ihI ihB => exact .bind ihI (by simpa using ihB)
  | cleanup callback body admitted publicCertified ihC ihB => exact .cleanup ihC ihB admitted
  | resource initializer body formed effectsBound admitted hidden ihI ihB =>
      exact .scopedResource ihI ihB formed effectsBound admitted hidden
  | branch condition yes no same ihC ihY ihN => exact .branch ihC ihY ihN same
  | perform known admitted operand formed ih =>
      dsimp only at known
      exact .perform (by simp [lowerOperations, known]) admitted ih formed

  | handler body clauses capabilities coverage unique admitted table modes declarations recipes ihBody _ihDecl =>
      apply SourceTemplates.Expression.handler ihBody ?_ capabilities ?_ unique admitted table modes
      · change ScopedPorts.ClausesTyped _ _ _ _ _ _ _
        rw [lowerOperations_ports, lowerEnvironment_ports]
        exact clauses
      · change ScopedPorts.Covers _ _ _
        rw [lowerOperations_ports]
        exact coverage

  | resume known resolved permission operand admitted formed ih =>
      exact .resume (CoreCallableContractRegistries.Owners.known_lower known) resolved permission ih admitted formed
  | discard known resolved permission unprotected admitted =>
      exact .discard (CoreCallableContractRegistries.Owners.known_lower known) resolved permission unprotected admitted

  | typed | unavailable | available | nil | cons => trivial

/-- The actual saved bind suffix, including private recursive bodies and a
finite lexical support entry for the eventual value. That entry is independent
of the input's declared port; plugging must supply its authenticated bound. -/
structure FrameSource (globals : Globals) (outward : List Instance) (world : List Nat) (allowed : List Instance)
    (data : PlainData) (input output : Contract) (parameter : Nat) (body : Code)
    (demand : List Nat) (requirements : Requirements demand)
    {dependencies : Dependencies} (plan : Plan dependencies) (rows : Rows (signature plan))
    (inputBound bodyBound receiver : List Nat) : Prop where
  position : data.context = ScopedExecution.Context.bind parameter body
  inputAnnotation : ScopedPorts.eraseType data.input = input.port
  outputAnnotation : ScopedPorts.eraseType data.output = output.port
  inputIssued : inputBound ⊆ world
  bodySource : CoreCallableContractAdmission.Supported globals outward world
    allowed data.scope (Environment.empty.extend parameter input)
    (ScopedPorts.Support.extend ScopedPorts.Support.empty parameter receiver) body output demand requirements plan rows bodyBound receiver


/-- A saved suffix is plugged using its own recursive evidence and the actual
returned value, with the same public input contract and finite support bound. -/
theorem FrameSource.plug
    (stable : SubstitutionPolicyStable (evidence := evidence) outward)
    (frame : FrameSource globals outward world allowed data input output parameter body demand requirements plan rows inputBound bodyBound receiver)
    (valueSource : CoreCallableContractAdmission.Supported globals outward world allowed data.scope Environment.empty
      ScopedPorts.Support.empty value input valueDemand valueRequirements valuePlan valueRows inputBound receiver)
    (closed : ClosedValue value) :
    ∃ nextPlan : Plan _, ∃ nextRows : Rows (signature nextPlan),
      CoreCallableContractAdmission.Supported globals outward world allowed data.scope Environment.empty ScopedPorts.Support.empty
        (body.subst parameter value) output demand requirements nextPlan nextRows bodyBound receiver ∧
      nextPlan = CoreCallablePlanSubstitution.plan body plan parameter value ∧
      signature nextPlan = signature plan ∧ HEq nextRows rows ∧ Certified outward world nextPlan := by
  let replacement : CoreCallableContractAdmission.Supported globals outward world allowed data.scope Environment.empty
      ScopedPorts.Support.empty value input valueDemand valueRequirements valuePlan valueRows receiver receiver :=
    ⟨valueSource.source, SourceSupport.bounds_iff.mpr valueSource.actual_received, frame.bodySource.receiverIssued,
      valueSource.authentication, frame.bodySource.receiverIssued⟩
  obtain ⟨nextPlan, nextRows, supported, exactPlan, sameSignature, sameRows⟩ :=
    frame.bodySource.substitution_reannotated stable replacement closed
  exact ⟨nextPlan, nextRows, supported, exactPlan, sameSignature, sameRows, IndexedSource.certified supported.source⟩

structure HandlerSource (globals : Globals) (outward : List Instance) (world : List Nat)
    (residual : List Instance) (data : HandlerData) (answer : Contract) (table : List (Nat × ClauseContract))
    {families : SourceDependencyAnnotations.ClauseDependencies}
    (plans : SourceDeclarationPlans.ClausePlans data.clauses families)
    (rows : ClauseRows (SourcePlanSignatures.clauseSignatures plans)) (receiver : List Nat) : Prop where
  annotation : ScopedPorts.eraseType data.answer = answer.port
  modes : SourceTemplates.ClauseModes data.clauses table
  source : CoreCallableContractAdmission.SourceDeclarations globals.registry outward globals.owners world Environment.empty
    residual data.effectInst answer data.clauses table plans rows
  authentication : ∃ lexical : LexicalBounds, lexical.environment = ScopedPorts.Support.empty ∧
    (CoreCallableContractAdmission.DeclarationAuthentication globals.registry outward source lexical receiver ∨
      CoreCallableContractAdmission.DomainDeclarationAuthentication globals.registry outward source lexical receiver)

/-- Preserve the original whole-receiver frame path explicitly. -/
theorem HandlerSource.of_whole
    {families : SourceDependencyAnnotations.ClauseDependencies}
    {plans : SourceDeclarationPlans.ClausePlans data.clauses families}
    {rows : ClauseRows (SourcePlanSignatures.clauseSignatures plans)}
    (annotation : ScopedPorts.eraseType data.answer = answer.port)
    (modes : SourceTemplates.ClauseModes data.clauses table)
    (source : CoreCallableContractAdmission.SourceDeclarations globals.registry outward globals.owners world Environment.empty
      residual data.effectInst answer data.clauses table plans rows)
    (authentication : ∃ lexical : LexicalBounds, lexical.environment = ScopedPorts.Support.empty ∧
      CoreCallableContractAdmission.DeclarationAuthentication globals.registry outward source lexical receiver) :
    HandlerSource globals outward world residual data answer table plans rows receiver := by
  obtain ⟨lexical, empty, checked⟩ := authentication
  exact ⟨annotation,modes,source,lexical,empty,Or.inl checked⟩

/-- Domain evidence installs the SAME complete source without whole relabeling. -/
theorem HandlerSource.of_domain
    {families : SourceDependencyAnnotations.ClauseDependencies}
    {plans : SourceDeclarationPlans.ClausePlans data.clauses families}
    {rows : ClauseRows (SourcePlanSignatures.clauseSignatures plans)}
    (annotation : ScopedPorts.eraseType data.answer = answer.port)
    (modes : SourceTemplates.ClauseModes data.clauses table)
    (source : CoreCallableContractAdmission.SourceDeclarations globals.registry outward globals.owners world Environment.empty
      residual data.effectInst answer data.clauses table plans rows)
    (authentication : ∃ lexical : LexicalBounds, lexical.environment = ScopedPorts.Support.empty ∧
      CoreCallableContractAdmission.DomainDeclarationAuthentication globals.registry outward source lexical receiver) :
    HandlerSource globals outward world residual data answer table plans rows receiver := by
  obtain ⟨lexical, empty, checked⟩ := authentication
  exact ⟨annotation,modes,source,lexical,empty,Or.inr checked⟩

/- Saved frame contracts, installed handler families and current live owners
share the same physical and contextual boundary. -/
set_option linter.unusedVariables false in
mutual
inductive Pending (globals : Globals) (outward : List Instance) (world : List Nat) :
    List Instance → List Nat → Stack → Contract → Contract → {scope : SourceDependencyCapture.Scope} → {hints : ReturnHints scope} → Context hints → Prop where
  | nil : Pending globals outward world allowed ambient .nil input input .nil
  | plain
      (frame : FrameSource globals outward world allowed
        data input middle parameter body demand requirements plan rows inputBound bodyBound (actualReceiver world scope ambient))
      (received : bodyBound ⊆ scope.visibleResources ++ ambient)
      (accepts : ∀ identity, identity ∈ world → identity ∈ scope.visibleResources ++ ambient → identity ∈ inputBound)
      (tail : Pending globals outward world allowed ambient stack middle output (context : Context (hints : ReturnHints scope))) :
      Pending globals outward world allowed ambient (.push (.plain data) stack) input output (.plain rows context)
  | handler
      (frame : HandlerSource globals outward world residual data answer table plans rows (actualReceiver world scope ambient))
      (admitted : residual ⊆ outsideAllowed)
      (tail : Pending globals outward world outsideAllowed ambient stack answer output (context : Context (hints : ReturnHints scope))) :
      Pending globals outward world (data.effectInst :: residual) ambient (.push (.handler data) stack) answer output
        (.handler (effect := data.effectInst) (table := table) data.activation rows context)
  | handlerView
      (frame : HandlerSource globals outward world residual data answer table plans rows (actualReceiver world scope ambient))
      (admitted : residual ⊆ outsideAllowed)
      (entered : (data.effectInst :: residual) ⊆ beforeAllowed)
      (bounded : beforeAllowed ⊆ (data.effectInst :: outsideAllowed))
      (tail : Pending globals outward world outsideAllowed ambient stack answer output (context : Context (hints : ReturnHints scope))) :
      Pending globals outward world beforeAllowed ambient (.push (.handler data) stack) answer output
        (.handler (effect := data.effectInst) (table := table) data.activation rows context)
  | live
      (known : globals.owners owner = some contract)
      (inputSame : contract.input = input) (answerSame : contract.answer = answer)
      (heldSame : contract.held = captureScope.held) (resumeSame : contract.resumeDemand = savedDemand)
      (balanced : contract.closeDemand.Perm contract.resumeDemand)
      (inputAnnotation : ScopedPorts.eraseType operationResult = input.port)
      (answerAnnotation : ScopedPorts.eraseType answerType = answer.port)
      (saved : Pending globals outward world savedAllowed (tailScope.visibleResources ++ ambient)
        cap input answer (captured : Context (captureHints : ReturnHints captureScope)))
      (tail : Pending globals outward world tailAllowed ambient stack answer output
        (outside : Context (tailHints : ReturnHints tailScope))) :
      Pending globals outward world allowed ambient (.live owner operationResult answerType cap caller stack)
        answer output (.live (owner := owner) (resumeDemand := savedDemand) captured outside)
  | capture
      (known : globals.owners owner = some contract)
      (inputSame : contract.input = input) (answerSame : contract.answer = answer)
      (heldSame : contract.held = captureScope.held) (resumeSame : contract.resumeDemand = savedDemand)
      (balanced : contract.closeDemand.Perm contract.resumeDemand)
      (inputAnnotation : ScopedPorts.eraseType operationResult = input.port)
      (answerAnnotation : ScopedPorts.eraseType handler.answer = answer.port)
      (frame : HandlerSource globals outward world residual handler answer table plans rows (actualReceiver world tailScope ambient))
      (installed : SelectedPending globals outward world
        (beforeAllowed := beforeAllowed) (whole := whole) (input := input) (output := output)
        (wholeContext := wholeContext) (tailAllowed := tailAllowed) (tail := tail) (outside := outside) frame)
      (physical : HandlerCut handler.effectInst whole cap tail handler)
      (contextual : SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Cut handler.effectInst operation
        wholeContext (captured : Context (captureHints : ReturnHints captureScope)) outside offered modes)
      (terminal : TerminalHandler handler.effectInst handler.activation rows captured) :
      Pending globals outward world residual ambient (.live owner operationResult handler.answer cap handler.scope tail)
        answer output (.live (owner := owner) (resumeDemand := savedDemand) captured outside)
  | spent
      (known : globals.owners owner = some contract)
      (answerSame : contract.answer = input)
      (annotation : ScopedPorts.eraseType answer = input.port)
      (tail : Pending globals outward world tailAllowed ambient stack input output context) :
      Pending globals outward world allowed ambient (.spent owner answer caller stack) input output (.spent (owner := owner) context)
  | cell (issued : identity ∈ world)
      (annotation : ScopedPorts.eraseType answer = input.port)
      (tail : Pending globals outward world allowed ambient stack input output context) :
      Pending globals outward world allowed ambient (.push (.cell identity payload caller answer) stack) input output (.cell (identity := identity) context)

inductive SelectedPending (globals : Globals) (outward : List Instance) (world : List Nat) :
    {beforeAllowed : List Instance} → {ambient : List Nat} → {whole : Stack} → {input output : Contract} →
    {wholeScope : SourceDependencyCapture.Scope} → {wholeHints : ReturnHints wholeScope} → {wholeContext : Context wholeHints} →
    {residual : List Instance} → {handler : HandlerData} → {answer : Contract} → {table : List (Nat × ClauseContract)} →
    {families : SourceDependencyAnnotations.ClauseDependencies} → {plans : SourceDeclarationPlans.ClausePlans handler.clauses families} →
    {rows : ClauseRows (SourcePlanSignatures.clauseSignatures plans)} →
    {tailAllowed : List Instance} → {tail : Stack} → {tailScope : SourceDependencyCapture.Scope} →
    {tailHints : ReturnHints tailScope} → {outside : Context tailHints} →
    HandlerSource globals outward world residual handler answer table plans rows (actualReceiver world tailScope ambient) →
    Prop where
  | here
      (frame : HandlerSource globals outward world residual handler answer table plans rows (actualReceiver world tailScope ambient))
      (admitted : residual ⊆ tailAllowed)
      (tail : Pending globals outward world tailAllowed ambient stack answer output (outside : Context (tailHints : ReturnHints tailScope))) :
      SelectedPending globals outward world (beforeAllowed := handler.effectInst :: residual)
        (whole := .push (.handler handler) stack) (input := answer) (output := output)
        (wholeContext := .handler (effect := handler.effectInst) (table := table) handler.activation rows outside)
        (tailAllowed := tailAllowed) (tail := stack) (outside := outside) frame
  | hereView
      (frame : HandlerSource globals outward world residual handler answer table plans rows (actualReceiver world tailScope ambient))
      (admitted : residual ⊆ tailAllowed)
      (entered : (handler.effectInst :: residual) ⊆ beforeAllowed)
      (bounded : beforeAllowed ⊆ (handler.effectInst :: tailAllowed))
      (tail : Pending globals outward world tailAllowed ambient stack answer output (outside : Context (tailHints : ReturnHints tailScope))) :
      SelectedPending globals outward world (beforeAllowed := beforeAllowed)
        (whole := .push (.handler handler) stack) (input := answer) (output := output)
        (wholeContext := .handler (effect := handler.effectInst) (table := table) handler.activation rows outside)
        (tailAllowed := tailAllowed) (tail := stack) (outside := outside) frame
  | plainPath
      (saved : FrameSource globals outward world allowed data input middle parameter body demand requirements plan waiting inputBound bodyBound (actualReceiver world scope ambient))
      (received : bodyBound ⊆ scope.visibleResources ++ ambient)
      (accepts : ∀ identity, identity ∈ world → identity ∈ scope.visibleResources ++ ambient → identity ∈ inputBound)
      (selected : SelectedPending globals outward world (ambient := ambient) (tailAllowed := selectedAllowed) (tail := selectedTail) (outside := (selectedOutside : Context (selectedHints : ReturnHints selectedScope))) (beforeAllowed := allowed) (whole := stack) (input := middle)
        (output := output) (wholeContext := (context : Context (hints : ReturnHints scope))) frame) :
      SelectedPending globals outward world (ambient := ambient) (tailAllowed := selectedAllowed) (tail := selectedTail) (outside := (selectedOutside : Context (selectedHints : ReturnHints selectedScope))) (beforeAllowed := allowed) (whole := .push (.plain data) stack)
        (input := input) (output := output) (wholeContext := .plain waiting context) frame
  | handlerMiss
      (saved : HandlerSource globals outward world outerResidual data middle outerTable outerPlans outerRows (actualReceiver world scope ambient))
      (admitted : outerResidual ⊆ allowed)
      (miss : data.effectInst ≠ handler.effectInst)
      (selected : SelectedPending globals outward world (ambient := ambient) (tailAllowed := selectedAllowed) (tail := selectedTail) (outside := (selectedOutside : Context (selectedHints : ReturnHints selectedScope))) (beforeAllowed := allowed) (whole := stack) (input := middle)
        (output := output) (wholeContext := (context : Context (hints : ReturnHints scope))) (handler := handler) frame) :
      SelectedPending globals outward world (ambient := ambient) (tailAllowed := selectedAllowed) (tail := selectedTail) (outside := (selectedOutside : Context (selectedHints : ReturnHints selectedScope))) (beforeAllowed := data.effectInst :: outerResidual) (whole := .push (.handler data) stack)
        (input := middle) (output := output)
        (wholeContext := .handler (effect := data.effectInst) (table := outerTable) data.activation outerRows context) frame
  | handlerMissView
      (saved : HandlerSource globals outward world outerResidual data middle outerTable outerPlans outerRows (actualReceiver world scope ambient))
      (admitted : outerResidual ⊆ allowed)
      (entered : (data.effectInst :: outerResidual) ⊆ beforeAllowed)
      (bounded : beforeAllowed ⊆ (data.effectInst :: allowed))
      (miss : data.effectInst ≠ handler.effectInst)
      (selected : SelectedPending globals outward world (ambient := ambient) (tailAllowed := selectedAllowed) (tail := selectedTail) (outside := (selectedOutside : Context (selectedHints : ReturnHints selectedScope))) (beforeAllowed := allowed) (whole := stack) (input := middle)
        (output := output) (wholeContext := (context : Context (hints : ReturnHints scope))) (handler := handler) frame) :
      SelectedPending globals outward world (ambient := ambient) (tailAllowed := selectedAllowed) (tail := selectedTail) (outside := (selectedOutside : Context (selectedHints : ReturnHints selectedScope))) (beforeAllowed := beforeAllowed) (whole := .push (.handler data) stack)
        (input := middle) (output := output)
        (wholeContext := .handler (effect := data.effectInst) (table := outerTable) data.activation outerRows context) frame
  | cellPath
      (issued : identity ∈ world) (annotation : ScopedPorts.eraseType answerType = input.port)
      (selected : SelectedPending globals outward world (ambient := ambient) (tailAllowed := selectedAllowed) (tail := selectedTail) (outside := (selectedOutside : Context (selectedHints : ReturnHints selectedScope))) (beforeAllowed := allowed) (whole := stack) (input := input)
        (output := output) (wholeContext := context) frame) :
      SelectedPending globals outward world (ambient := ambient) (tailAllowed := selectedAllowed) (tail := selectedTail) (outside := (selectedOutside : Context (selectedHints : ReturnHints selectedScope))) (beforeAllowed := allowed)
        (whole := .push (.cell identity payload caller answerType) stack) (input := input) (output := output)
        (wholeContext := .cell (identity := identity) context) frame
  | spentPath
      (known : globals.owners owner = some contract)
      (answerSame : contract.answer = input)
      (annotation : ScopedPorts.eraseType answer = input.port)
      (selected : SelectedPending globals outward world (ambient := ambient) (tailAllowed := selectedAllowed)
        (tail := selectedTail) (outside := (selectedOutside : Context (selectedHints : ReturnHints selectedScope)))
        (beforeAllowed := tailAllowed) (whole := stack) (input := input) (output := output)
        (wholeContext := context) frame) :
      SelectedPending globals outward world (ambient := ambient) (tailAllowed := selectedAllowed)
        (tail := selectedTail) (outside := (selectedOutside : Context (selectedHints : ReturnHints selectedScope)))
        (beforeAllowed := allowed) (whole := .spent owner answer caller stack) (input := input) (output := output)
        (wholeContext := .spent (owner := owner) context) frame
  | liveTail
      (known : globals.owners owner = some contract)
      (inputSame : contract.input = input) (answerSame : contract.answer = answer)
      (heldSame : contract.held = captureScope.held) (resumeSame : contract.resumeDemand = savedDemand)
      (balanced : contract.closeDemand.Perm contract.resumeDemand)
      (inputAnnotation : ScopedPorts.eraseType operationResult = input.port)
      (answerAnnotation : ScopedPorts.eraseType answerType = answer.port)
      (saved : Pending globals outward world savedAllowed (tailScope.visibleResources ++ ambient)
        cap input answer (captured : Context (captureHints : ReturnHints captureScope)))
      (selected : SelectedPending globals outward world (ambient := ambient) (tailAllowed := selectedAllowed) (tail := selectedTail) (outside := (selectedOutside : Context (selectedHints : ReturnHints selectedScope))) (beforeAllowed := tailAllowed) (whole := stack) (input := answer)
        (output := output) (wholeContext := (outside : Context (tailHints : ReturnHints tailScope))) frame) :
      SelectedPending globals outward world (ambient := ambient) (tailAllowed := selectedAllowed) (tail := selectedTail) (outside := (selectedOutside : Context (selectedHints : ReturnHints selectedScope))) (beforeAllowed := allowed)
        (whole := .live owner operationResult answerType cap caller stack) (input := answer) (output := output)
        (wholeContext := .live (owner := owner) (resumeDemand := savedDemand) captured outside) frame
  | captureTail
      (known : globals.owners owner = some contract)
      (inputSame : contract.input = input) (answerSame : contract.answer = answer)
      (heldSame : contract.held = captureScope.held) (resumeSame : contract.resumeDemand = savedDemand)
      (balanced : contract.closeDemand.Perm contract.resumeDemand)
      (inputAnnotation : ScopedPorts.eraseType operationResult = input.port)
      (answerAnnotation : ScopedPorts.eraseType earlierHandler.answer = answer.port)
      (installedFrame : HandlerSource globals outward world earlierResidual earlierHandler answer earlierTable earlierPlans earlierRows
        (actualReceiver world outsideScope ambient))
      (installation : SelectedPending globals outward world (ambient := ambient) (beforeAllowed := beforeAllowed) (whole := whole)
        (input := input) (output := output) (wholeContext := wholeContext) (tailAllowed := outsideAllowed)
        (tail := stack) (outside := outside) installedFrame)
      (physical : HandlerCut earlierHandler.effectInst whole cap stack earlierHandler)
      (contextual : SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Cut earlierHandler.effectInst operation
        wholeContext (captured : Context (captureHints : ReturnHints captureScope)) outside offered modes)
      (terminal : TerminalHandler earlierHandler.effectInst earlierHandler.activation earlierRows captured)
      (selected : SelectedPending globals outward world (ambient := ambient) (tailAllowed := selectedAllowed) (tail := selectedTail) (outside := (selectedOutside : Context (selectedHints : ReturnHints selectedScope))) (beforeAllowed := outsideAllowed) (whole := stack)
        (input := answer) (output := output) (wholeContext := outside) frame) :
      SelectedPending globals outward world (ambient := ambient) (tailAllowed := selectedAllowed) (tail := selectedTail) (outside := (selectedOutside : Context (selectedHints : ReturnHints selectedScope))) (beforeAllowed := earlierResidual)
        (whole := .live owner operationResult earlierHandler.answer cap earlierHandler.scope stack) (input := answer) (output := output)
        (wholeContext := .live (owner := owner) (resumeDemand := savedDemand) captured outside) frame

end

theorem SelectedPending.connection
    (selected : SelectedPending globals outward world (beforeAllowed := beforeAllowed) (ambient := ambient)
      (whole := whole) (input := input) (output := output) (wholeContext := wholeContext)
      (tailAllowed := tailAllowed) (tail := tail) (outside := outside) (answer := answer) frame) :
    Pending globals outward world beforeAllowed ambient whole input output wholeContext ∧
      Pending globals outward world tailAllowed ambient tail answer output outside := by
  induction selected using SelectedPending.rec
    (motive_1 := fun _ _ _ _ _ _ _ _ _ => True) with
  | nil | plain | handler | handlerView | live | capture | spent | cell => trivial
  | here frame admitted tail ih => exact ⟨.handler frame admitted tail, tail⟩
  | hereView frame admitted entered bounded tail ih => exact ⟨.handlerView frame admitted entered bounded tail, tail⟩
  | plainPath saved received accepts selected ih => exact ⟨.plain saved received accepts ih.1, ih.2⟩
  | handlerMiss saved admitted miss selected ih => exact ⟨.handler saved admitted ih.1, ih.2⟩
  | handlerMissView saved admitted entered bounded miss selected ih => exact ⟨.handlerView saved admitted entered bounded ih.1, ih.2⟩
  | cellPath issued annotation selected ih => exact ⟨.cell issued annotation ih.1, ih.2⟩
  | spentPath known answerSame annotation selected ih => exact ⟨.spent known answerSame annotation ih.1, ih.2⟩
  | liveTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved selected ihSaved ih =>
      exact ⟨.live known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved ih.1, ih.2⟩
  | captureTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation installedFrame installation physical contextual terminal selected ihInstallation ih =>
      exact ⟨.capture known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation installedFrame installation physical contextual terminal, ih.2⟩

theorem SelectedPending.before
    (selected : SelectedPending globals outward world (beforeAllowed := beforeAllowed) (ambient := ambient)
      (whole := whole) (input := input) (output := output) (wholeContext := wholeContext)
      (tailAllowed := tailAllowed) (tail := tail) (outside := outside) (answer := answer) frame) :
    Pending globals outward world beforeAllowed ambient whole input output wholeContext := selected.connection.1

theorem SelectedPending.outside
    (selected : SelectedPending globals outward world (beforeAllowed := beforeAllowed) (ambient := ambient)
      (whole := whole) (input := input) (output := output) (wholeContext := wholeContext)
      (tailAllowed := tailAllowed) (tail := tail) (outside := outsideContext) (answer := answer) frame) :
    Pending globals outward world tailAllowed ambient tail answer output outsideContext := selected.connection.2

#print axioms SelectedPending.connection
#print axioms SelectedPending.before
#print axioms SelectedPending.outside
theorem FrameSource.owners_known_mono
    (frame : FrameSource globals outward world allowed data input output parameter body demand requirements plan rows inputBound bodyBound receiver)
    (agree : CoreCallableContractAdmission.OwnerKnownMonotone globals.owners destination) :
    FrameSource (globals.withOwners destination) outward world allowed data input output parameter body demand requirements plan rows inputBound bodyBound receiver :=
  ⟨frame.position, frame.inputAnnotation, frame.outputAnnotation, frame.inputIssued, frame.bodySource.owners_known_mono agree⟩
theorem HandlerSource.owners_congr
    (frame : HandlerSource globals outward world residual data answer table plans rows receiver) (destination : CoreCallableContractRegistries.Owners) :
    HandlerSource (globals.withOwners destination) outward world residual data answer table plans rows receiver := by
  obtain ⟨lexical, sameEnvironment, authenticated⟩ := frame.authentication
  cases authenticated with
  | inl whole =>
    obtain ⟨nextSource, nextAuthentication⟩ := whole.owners_congr destination
    exact ⟨frame.annotation, frame.modes, nextSource, ⟨lexical, sameEnvironment, Or.inl nextAuthentication⟩⟩
  | inr domain =>
    obtain ⟨nextSource, nextAuthentication⟩ := domain.owners_congr destination
    exact ⟨frame.annotation, frame.modes, nextSource, ⟨lexical, sameEnvironment, Or.inr nextAuthentication⟩⟩
theorem Pending.owners_known_mono
    (pending : Pending globals outward world allowed ambient stack input output context)
    (agree : CoreCallableContractAdmission.OwnerKnownMonotone globals.owners destination) :
    Pending (globals.withOwners destination) outward world allowed ambient stack input output context := by
  induction pending using Pending.rec
    (motive_2 := fun {beforeAllowed} {ambient} {whole} {input} {output} {_} {_} {wholeContext} {_} {_} {_} {_} {_} {_} {_} {tailAllowed} {tail} {_} {_} {outside} frame _ =>
      SelectedPending (globals.withOwners destination) outward world (beforeAllowed := beforeAllowed) (ambient := ambient)
        (whole := whole) (input := input) (output := output) (wholeContext := wholeContext)
        (tailAllowed := tailAllowed) (tail := tail) (outside := outside) (frame.owners_congr destination)) with
  | nil => exact .nil
  | plain frame received accepts tail ih => exact .plain (frame.owners_known_mono agree) received accepts ih
  | handler frame admitted tail ih => exact .handler (frame.owners_congr destination) admitted ih
  | handlerView frame admitted entered bounded tail ih => exact .handlerView (frame.owners_congr destination) admitted entered bounded ih
  | live known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved tail ihSaved ihTail =>
    exact .live (agree _ _ known) inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation ihSaved ihTail
  | capture known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation frame installed physical contextual terminal ihInstalled =>
      exact .capture (agree _ _ known) inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation
        (frame.owners_congr destination) ihInstalled physical contextual terminal
  | cell issued annotation tail ih => exact .cell issued annotation ih
  | spent known answerSame annotation tail ih => exact .spent (agree _ _ known) answerSame annotation ih
  | here frame admitted tail ih => exact .here (frame.owners_congr destination) admitted ih
  | hereView frame admitted entered bounded tail ih => exact .hereView (frame.owners_congr destination) admitted entered bounded ih
  | plainPath saved received accepts selected ih => exact .plainPath (saved.owners_known_mono agree) received accepts ih
  | handlerMiss saved admitted miss selected ih => exact .handlerMiss (saved.owners_congr destination) admitted miss ih
  | handlerMissView saved admitted entered bounded miss selected ih => exact .handlerMissView (saved.owners_congr destination) admitted entered bounded miss ih
  | cellPath issued annotation selected ih => exact .cellPath issued annotation ih
  | spentPath known answerSame annotation selected ih => exact .spentPath (agree _ _ known) answerSame annotation ih
  | liveTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved selected ihSaved ih =>
      exact .liveTail (agree _ _ known) inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation ihSaved ih
  | captureTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation frame installed physical contextual terminal selected ihInstalled ih =>
      exact .captureTail (agree _ _ known) inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation
        (frame.owners_congr destination) ihInstalled physical contextual terminal ih

theorem SelectedPending.owners_known_mono
    (selected : SelectedPending globals outward world (beforeAllowed := beforeAllowed) (ambient := ambient)
      (whole := whole) (input := input) (output := output) (wholeContext := wholeContext)
      (tailAllowed := tailAllowed) (tail := tail) (outside := outsideContext) frame)
    (agree : CoreCallableContractAdmission.OwnerKnownMonotone globals.owners destination) :
    SelectedPending (globals.withOwners destination) outward world (beforeAllowed := beforeAllowed) (ambient := ambient)
      (whole := whole) (input := input) (output := output) (wholeContext := wholeContext)
      (tailAllowed := tailAllowed) (tail := tail) (outside := outsideContext) (frame.owners_congr destination) := by
  induction selected using SelectedPending.rec
    (motive_1 := fun allowed ambient stack input output _ _ context _ =>
      Pending (globals.withOwners destination) outward world allowed ambient stack input output context) with
  | nil => exact .nil
  | plain frame received accepts tail ih => exact .plain (frame.owners_known_mono agree) received accepts ih
  | handler frame admitted tail ih => exact .handler (frame.owners_congr destination) admitted ih
  | handlerView frame admitted entered bounded tail ih => exact .handlerView (frame.owners_congr destination) admitted entered bounded ih
  | live known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved tail ihSaved ihTail =>
    exact .live (agree _ _ known) inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation ihSaved ihTail
  | capture known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation frame installed physical contextual terminal ihInstalled =>
      exact .capture (agree _ _ known) inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation
        (frame.owners_congr destination) ihInstalled physical contextual terminal
  | cell issued annotation tail ih => exact .cell issued annotation ih
  | spent known answerSame annotation tail ih => exact .spent (agree _ _ known) answerSame annotation ih
  | here frame admitted tail ih => exact .here (frame.owners_congr destination) admitted ih
  | hereView frame admitted entered bounded tail ih => exact .hereView (frame.owners_congr destination) admitted entered bounded ih
  | plainPath saved received accepts selected ih => exact .plainPath (saved.owners_known_mono agree) received accepts ih
  | handlerMiss saved admitted miss selected ih => exact .handlerMiss (saved.owners_congr destination) admitted miss ih
  | handlerMissView saved admitted entered bounded miss selected ih => exact .handlerMissView (saved.owners_congr destination) admitted entered bounded miss ih
  | cellPath issued annotation selected ih => exact .cellPath issued annotation ih
  | spentPath known answerSame annotation selected ih => exact .spentPath (agree _ _ known) answerSame annotation ih
  | liveTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved selected ihSaved ih =>
      exact .liveTail (agree _ _ known) inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation ihSaved ih
  | captureTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation frame installed physical contextual terminal selected ihInstalled ih =>
      exact .captureTail (agree _ _ known) inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation
        (frame.owners_congr destination) ihInstalled physical contextual terminal ih

omit evidence in
theorem physical_rebase (cut : HandlerCut requested whole cap tail handler) (after : Stack) :
    HandlerCut requested (cap.append after) cap after handler := by
  induction cut with
  | hit handler tail same => exact .hit handler after same
  | push frame rest cap tail handler miss next ih => exact .push frame _ _ _ _ miss ih
  | live ticket q a saved scope rest cap tail handler next ih => exact .live ticket q a saved scope _ _ _ _ ih
  | spent ticket a scope rest cap tail handler next ih => exact .spent ticket a scope _ _ _ _ ih

theorem Pending.cell_update (pending : Pending globals outward world allowed ambient before input output context)
    (updated : CellUpdate identity old new before after) : Pending globals outward world allowed ambient after input output context := by
  induction pending using Pending.rec
    (motive_2 := fun {beforeAllowed} {ambient} {whole} {input} {output} {_} {_} {wholeContext}
      {_} {handler} {answer} {_} {_} {_} {_} {tailAllowed} {tail} {_} {_} {outside} frame _ =>
      (∀ after, CellUpdate identity old new tail after → Pending globals outward world tailAllowed ambient after answer output outside) ∧
      (∀ after, Pending globals outward world tailAllowed ambient after answer output outside →
      ∀ cap, HandlerCut handler.effectInst whole cap tail handler →
      SelectedPending globals outward world (beforeAllowed := beforeAllowed) (ambient := ambient)
        (whole := cap.append after) (input := input) (output := output) (wholeContext := wholeContext)
        (tailAllowed := tailAllowed) (tail := after) (outside := outside) frame))
    generalizing after with
  | nil => cases updated
  | plain frame received accepts tail ih => cases updated with
    | push miss next => exact .plain frame received accepts (ih next)
  | handler frame admitted tail ih => cases updated with
    | push miss next => exact .handler frame admitted (ih next)
  | handlerView frame admitted entered bounded tail ih => cases updated with
    | push miss next => exact .handlerView frame admitted entered bounded (ih next)
  | live known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved tail _ihSaved ihTail =>
    cases updated with
    | live next => exact .live known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved (ihTail next)
  | capture known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation frame installed physical contextual terminal ih =>
    cases updated with
    | live next =>
      have nextOutside := ih.1 _ next
      exact .capture known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation frame
        (ih.2 _ nextOutside _ physical) (physical_rebase physical _) contextual terminal
  | spent known answerSame annotation tail ih => cases updated with
    | spent next => exact .spent known answerSame annotation (ih next)
  | cell issued annotation tail ih => cases updated with
    | hit => exact .cell issued annotation tail
    | push miss next => exact .cell issued annotation (ih next)
  | here frame admitted tail ih =>
      refine ⟨fun _ update => ih update, ?_⟩
      intro after nextTail cap cut
      cases cut with
      | hit => exact .here frame admitted nextTail
      | push frame rest cap tail handler miss next =>
          exact False.elim (miss rfl)
  | hereView frame admitted entered bounded tail ih =>
      refine ⟨fun _ update => ih update, ?_⟩
      intro after nextTail cap cut
      cases cut with
      | hit => exact .hereView frame admitted entered bounded nextTail
      | push frame rest cap tail handler miss next =>
          exact False.elim (miss rfl)
  | plainPath saved received accepts selected ih =>
      refine ⟨ih.1, ?_⟩
      intro after nextTail cap cut
      cases cut with
      | push frame rest cap tail handler miss next =>
          exact .plainPath saved received accepts (ih.2 after nextTail cap next)
  | handlerMiss saved admitted miss selected ih =>
      refine ⟨ih.1, ?_⟩
      intro after nextTail cap cut
      cases cut with
      | hit handler tail same => exact False.elim (miss same)
      | push frame rest cap tail handler physicalMiss next =>
          exact .handlerMiss saved admitted miss (ih.2 after nextTail cap next)
  | handlerMissView saved admitted entered bounded miss selected ih =>
      refine ⟨ih.1, ?_⟩
      intro after nextTail cap cut
      cases cut with
      | hit handler tail same => exact False.elim (miss same)
      | push frame rest cap tail handler physicalMiss next =>
          exact .handlerMissView saved admitted entered bounded miss (ih.2 after nextTail cap next)
  | cellPath issued annotation selected ih =>
      refine ⟨ih.1, ?_⟩
      intro after nextTail cap cut
      cases cut with
      | push frame rest cap tail handler miss next =>
          exact .cellPath issued annotation (ih.2 after nextTail cap next)
  | spentPath known answerSame annotation selected ih =>
      refine ⟨ih.1, ?_⟩
      intro after nextTail cap cut
      cases cut with
      | spent ticket a scope rest cap tail handler next =>
          exact .spentPath known answerSame annotation (ih.2 after nextTail cap next)
  | liveTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved selected ihSaved ih =>
      refine ⟨ih.1, ?_⟩
      intro after nextTail cap cut
      cases cut with
      | live ticket q a savedStack scope rest cap tail handler next =>
          exact .liveTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved
            (ih.2 after nextTail cap next)
  | captureTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation frame installed physical contextual terminal selected ihInstalled ih =>
      refine ⟨ih.1, ?_⟩
      intro after nextTail cap cut
      cases cut with
      | live ticket q a savedStack scope rest cap tail handler next =>
          have selectedNext := ih.2 after nextTail cap next
          exact .captureTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation frame
            (ihInstalled.2 _ selectedNext.before _ physical) (physical_rebase physical _) contextual terminal selectedNext

/-- The same physical cell update and saved-frame relation identify the
actual contextual builtin receiver. No chosen response source is assumed. -/
theorem Pending.cell_update_builtin
    (pending : Pending globals outward world allowed ambient before input output context)
    (updated : CellUpdate identity old new before after) : select (.cell identity) 0 context = some (.builtin identity) := by
  induction pending using Pending.rec
    (motive_2 := fun {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {tail} {_} {_} {outside} _ _ =>
      ∀ {after}, CellUpdate identity old new tail after → select (.cell identity) 0 outside = some (.builtin identity))
    generalizing after with
  | nil => cases updated
  | plain frame received accepts tail ih =>
      cases updated with
      | push miss next => simp only [select, ih next, Option.map_some, Selection.prepend]
  | handler frame admitted tail ih =>
      cases updated with
      | push miss next =>
        simp only [select]
        split
        · rename_i same
          exact False.elim (miss (by simpa only [ExecFrame.erase, HandlerData.erase, Frame.target] using congrArg some same.symm))
        · simp only [ih next, Option.map_some, Selection.prepend]
  | handlerView frame admitted entered bounded tail ih =>
      cases updated with
      | push miss next =>
        simp only [select]
        split
        · rename_i same
          exact False.elim (miss (by simpa only [ExecFrame.erase, HandlerData.erase, Frame.target] using congrArg some same.symm))
        · simp only [ih next, Option.map_some, Selection.prepend]
  | live known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved tail _ihSaved ihTail =>
    cases updated with
    | live next => simp only [select, ihTail next, Option.map_some, Selection.prepend]
  | capture known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation frame installed physical contextual terminal ih =>
    cases updated with
    | live next => simp only [select, ih next, Option.map_some, Selection.prepend]
  | spent known answerSame annotation tail ih =>
      cases updated with
      | spent next => simp only [select, ih next, Option.map_some, Selection.prepend]
  | cell issued annotation tail ih =>
      cases updated with
      | hit => simp [select]
      | push miss next =>
          simp only [select]
          split
          · rename_i same
            exact False.elim (miss (by simpa only [ExecFrame.erase, Frame.target] using congrArg some same.symm))
          · simp only [ih next, Option.map_some, Selection.prepend]

  | here frame admitted tail ih => apply ih; assumption
  | hereView frame admitted entered bounded tail ih => apply ih; assumption
  | plainPath saved received accepts selected ih => apply ih; assumption
  | handlerMiss saved admitted miss selected ih => apply ih; assumption
  | handlerMissView saved admitted entered bounded miss selected ih => apply ih; assumption
  | cellPath issued annotation selected ih => apply ih; assumption
  | spentPath known answerSame annotation selected ih => apply ih; assumption
  | liveTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation saved selected ihSaved ih => apply ih; assumption
  | captureTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation frame installed physical contextual terminal selected ihInstalled ih => apply ih; assumption

/-- Actual current source and saved recursive frames share one context. The
certificate, retained checks and executable root are existing M4 structures;
this replaces the legacy exact-body facet in the bounded companion only. -/
structure Site (globals : Globals) (outward : List Instance) (world : List Nat) (allowed : List Instance)
    (actions : Syntax.UsageTickets) (phases : OwnerPhaseTransitions.Phases) (budget : Footprint)
    (ambient installations : List Nat) (expression : Code) (runtimeScope : Execution.Scope) (stack : Stack)
    (result final : Contract) {receiving : SourceDependencyCapture.Scope} {hints : ReturnHints receiving}
    (context : Context hints) (root : Requirements rootDemand) where
  sourceDemand : List Nat
  requirements : Requirements sourceDemand
  dependencies : Dependencies
  plan : Plan dependencies
  rows : Rows (signature plan)
  bound : List Nat
  current : CoreCallableContractAdmission.Supported globals outward
    world allowed runtimeScope
    Environment.empty ScopedPorts.Support.empty expression result sourceDemand requirements plan rows bound (actualReceiver world receiving ambient)
  received : bound ⊆ receiving.visibleResources ++ ambient
  certificate : SourceAdmission.Code outward actions budget phases
    world installations rows context
  certificateChecked : InstallationSupport.CodeChecked ambient outward certificate
  pending : Pending globals outward world allowed ambient stack result final context
  retained : SourceAdmission.Pending outward actions budget phases
    world installations context .nil .ordinary .ordinary
  retainedChecked : InstallationSupport.PendingChecked ambient outward retained
  accounting : Accounting.Run
    world installations rows context root
  annotated : Requirements rootDemand
  row : Footprint
  annotation : RowAnnotation root annotated
  checked : Checked [] [] phases (annotateDisposals annotated) row
  bounded : row ⊆ budget

theorem Site.certified (site : Site globals outward world allowed actions phases budget ambient installations expression runtimeScope stack result final context root) :
    Certified outward world site.plan := (IndexedSource.certified site.current.source)

/-- Runtime port annotations erase to the same common declared contract.
Retained support is deliberately checked in separate lexical fields. -/
def runtimeType : Contract → Ty
  | .unit => .unit
  | .boolean => .boolean
  | .integer => .integer
  | .reference identity => .reference identity
  | .pair left right => .product (runtimeType left) (runtimeType right)
  | .function input output requests _ _ _ => .function (runtimeType input) (runtimeType output) requests []
omit [DeclarationPolicy] in
theorem runtimeType_port (contract : Contract) : ScopedPorts.eraseType (runtimeType contract) = contract.port := by
  induction contract with
  | unit | boolean | integer | reference => rfl
  | pair first second ihL ihR => simp [runtimeType, ScopedPorts.eraseType, Contract.port, Contract.value, SourcePlannedTyping.Value.erase,
      SourceDependencyAnnotations.Value.erase, CoherentSourceTypes.Value.port, ihL, ihR]
  | function input output requests latent plan rows ihI ihO => simp [runtimeType, ScopedPorts.eraseType, Contract.port, Contract.value,
      SourcePlannedTyping.Value.erase, SourceDependencyAnnotations.Value.erase, CoherentSourceTypes.Value.port, ihI, ihO]

omit [DeclarationPolicy] in
private theorem empty_extend (parameter : Nat) : ScopedPorts.Support.extend ScopedPorts.Support.empty parameter [] = ScopedPorts.Support.empty := by
  funext other
  simp [ScopedPorts.Support.extend, ScopedPorts.Support.empty]

omit [DeclarationPolicy] in
private theorem finite_bounds {environment : ScopedPorts.Support.Env} {dependencies : List Syntax.Dependency} {bound : List Nat}
    (resources : Syntax.resourceDependencies dependencies ⊆ bound)
    (variables : ∀ name, environment name ⊆ bound) : SourceSupport.Bounds environment dependencies bound := by
  induction dependencies with
  | nil => exact .nil
  | cons dependency rest ih =>
      have tail : Syntax.resourceDependencies rest ⊆ bound := by
        intro identity member
        exact resources (Syntax.mem_resourceDependencies.mpr (List.mem_cons_of_mem _ (Syntax.mem_resourceDependencies.mp member)))
      cases dependency with
      | resource identity => exact .resource (resources (by simp [Syntax.resourceDependencies])) (ih tail)
      | «variable» name => exact .variable (variables name) (ih tail)
      | ticket owner => exact .ticket (ih tail)

theorem Site.focus_bind {receiving : SourceDependencyCapture.Scope} {hints : ReturnHints receiving} {context : Context hints}
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.bind parameter initializer body) runtimeScope stack output final context root)
    (notValue : ¬ initializer.IsValue)
    (translated : runtimeScope.translate (ScopedExecution.Context.bind parameter body).dependencies = some []) :
    ∃ (input : Contract) (data : PlainData) (restDependencies : Dependencies) (restPlan : Plan restDependencies)
      (restRows : Rows (signature restPlan)),
      data.context = .bind parameter body ∧ data.scope = runtimeScope ∧
      ∃ _next : Site globals outward world allowed actions phases budget ambient installations initializer runtimeScope
        (.push (.plain data) stack) input final (.plain restRows context) root,
        RawStep ⟨.bind parameter initializer body, runtimeScope, stack⟩ ⟨initializer, runtimeScope, .push (.plain data) stack⟩ [] [] := by
  rcases site with ⟨sourceDemand, requirements, dependencies, plan, rows, bound, current, received, certificate, certificateChecked,
    pending, retained, retainedChecked, accounting, annotated, row, annotation, checked, bounded⟩
  rcases current with ⟨source, support, issued, authentication, receiverIssued⟩
  obtain ⟨lexical, sameEnvironment, authenticated⟩ := authentication
  cases authenticated with
  | checked actualSupport hereditary =>
    cases hereditary with
    | bind initialAuthentication bodyAuthentication =>
        rename_i input initialDemand initialReq initialDependencies initialPlan initialRows bodyDemand bodyReq bodyDependencies bodyPlan bodyRows initialSource bodySource
        let data : PlainData := ⟨.bind parameter body, runtimeScope, runtimeType input, runtimeType output, [], translated⟩
        let receiverBound := (receiving.visibleResources ++ ambient).filter (fun identity => identity ∈ world)
        have accepts : ∀ identity, identity ∈ world → identity ∈ receiving.visibleResources ++ ambient → identity ∈ receiverBound := by
          intro identity historical visible
          exact List.mem_filter.mpr ⟨visible, by simpa using historical⟩
        have receiverIssued : receiverBound ⊆ world := by
          intro identity member
          exact of_decide_eq_true (List.mem_filter.mp member).2
        have receiverReceived : receiverBound ⊆ receiving.visibleResources ++ ambient := fun _ member => (List.mem_filter.mp member).1
        have currentBound : bound ⊆ receiverBound := fun identity member => accepts identity (issued member) (received member)
        have childSupport : SourceSupport.Bounds ScopedPorts.Support.empty initializer.dependencies receiverBound := by
          apply finite_bounds
          · intro identity member
            apply currentBound
            apply support.resources
            exact Syntax.mem_resourceDependencies.mpr (List.mem_append_left _ (Syntax.mem_resourceDependencies.mp member))
          · intro name; simp [ScopedPorts.Support.empty]
        have bodySupport : SourceSupport.Bounds (ScopedPorts.Support.extend ScopedPorts.Support.empty parameter receiverBound) body.dependencies receiverBound := by
          apply finite_bounds
          · intro identity member
            apply currentBound
            apply support.resources
            exact Syntax.mem_resourceDependencies.mpr (List.mem_append_right _
              (Syntax.mem_without.mpr ⟨Syntax.mem_resourceDependencies.mp member, by simp⟩))
          · intro name
            by_cases same : name = parameter
            · simp [ScopedPorts.Support.extend, same]
            · simp [ScopedPorts.Support.extend, ScopedPorts.Support.empty, same]
        let frame : FrameSource globals outward world allowed data input output parameter body bodyDemand bodyReq bodyPlan bodyRows receiverBound receiverBound receiverBound :=
          ⟨rfl, runtimeType_port _, runtimeType_port _, receiverIssued, ⟨bodySource, bodySupport, receiverIssued, ⟨lexical.extend parameter receiverBound, by simp [receiverBound, sameEnvironment, LexicalBounds.environment_extend], bodyAuthentication⟩, receiverIssued⟩⟩
        have split : FocusRows (sequenceRows initialRows bodyRows) initialRows bodyRows := .sequence
        obtain ⟨childCertificate, restCertificate⟩ := split.source_certificate certificate
        obtain ⟨childChecked, restChecked⟩ := InstallationSupport.focus_rows split certificateChecked
        let nextRetained : SourceAdmission.Pending outward actions budget phases world installations (.plain bodyRows context) .nil .ordinary .ordinary :=
          .plain (restCertificate.reindex_context context.append_nil_pack.symm) retained
        let next : Site globals outward world allowed actions phases budget ambient installations initializer runtimeScope
          (.push (.plain data) stack) input final (.plain bodyRows context) root :=
          { sourceDemand := initialDemand, requirements := initialReq, dependencies := initialDependencies, plan := initialPlan, rows := initialRows,
            bound := receiverBound, current := ⟨initialSource, childSupport, receiverIssued, ⟨lexical, sameEnvironment, initialAuthentication⟩, receiverIssued⟩, received := receiverReceived,
            certificate := childCertificate, certificateChecked := childChecked,
            pending := .plain frame receiverReceived accepts pending, retained := nextRetained,
            retainedChecked := .plain (restChecked.reindex_context context.append_nil_pack.symm) retainedChecked,
            accounting := accounting.focus_rows split, annotated := annotated, row := row, annotation := annotation, checked := checked, bounded := bounded }
        exact ⟨input, data, bodyDependencies, bodyPlan, bodyRows, rfl, rfl, next, .focus data (.bind notValue) stack⟩

/-- Immediate rows of an actual value are silent, including product values;
private callable bodies remain in the recursive source witness. -/
theorem Source.value_silent {dependencies : Dependencies} {plan : Plan dependencies} {rows : Rows (signature plan)}
    (source : Source globals outward world allowed scope environment value contract demand requirements plan rows)
    (isValue : value.IsValue) : dependencies.Silent := by
  rcases globals with ⟨operations, policy, owners⟩
  dsimp only [Source, CoreCallableContractAdmission.Globals.registry] at source ⊢
  induction source using IndexedSource.rec
    (motive_2 := fun _ _ _ _ _ _ _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ _ _ _ _ _ _ => True) with
  | unit | boolean | integer | reference | lambda | receiverLambda | purePair => exact .pure
  | pair left right ihL ihR => exact .sequence (ihL isValue.1) (ihR isValue.2)
  | «variable» | app | bind | branch | perform | resume | discard | handler | cleanup | resource => cases isValue
  | typed | unavailable | available | nil | cons => trivial

omit evidence in
private theorem transport_current_rows
    {first second : SourcePlanSignatures.Signature dependencies}
    {firstRows : Rows first} {secondRows : Rows second}
    (same : first = second) (sameRows : HEq firstRows secondRows)
    (certificate : SourceAdmission.Code outward actions budget phases world installations secondRows context)
    (checked : InstallationSupport.CodeChecked ambient outward certificate)
    (run : Accounting.Run world installations secondRows context root) :
    ∃ nextCertificate : SourceAdmission.Code outward actions budget phases world installations firstRows context,
      InstallationSupport.CodeChecked ambient outward nextCertificate ∧
      Accounting.Run world installations firstRows context root := by
  subst second
  cases eq_of_heq sameRows
  exact ⟨certificate, checked, run⟩

theorem Site.bind_value {receiving : SourceDependencyCapture.Scope} {hints : ReturnHints receiving} {context : Context hints}
    (stable : SubstitutionPolicyStable (evidence := evidence) outward)
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.bind parameter value body) runtimeScope stack output final context root)
    (closed : ClosedValue value) (captureClosed : ClosedExcept parameter body) :
    ∃ _next : Site globals outward world allowed actions phases budget ambient installations
      (body.subst parameter value) runtimeScope stack output final context root,
      RawStep ⟨.bind parameter value body, runtimeScope, stack⟩ ⟨body.subst parameter value, runtimeScope, stack⟩ [] [] := by
  rcases site with ⟨sourceDemand, requirements, dependencies, plan, rows, bound, current, received, certificate, certificateChecked,
    pending, retained, retainedChecked, accounting, annotated, row, annotation, checked, bounded⟩
  obtain ⟨lexical, sameEnvironment, authenticated⟩ := current.authentication
  cases authenticated with
  | checked actualSupport hereditary =>
    cases hereditary with
    | bind initialAuthentication bodyAuthentication =>
      rename_i input initialDemand initialReq initialDependencies initialPlan initialRows bodyDemand bodyReq bodyDependencies bodyPlan bodyRows initialSource bodySource
      let receiver := actualReceiver world receiving ambient
      have operandSupport : SourceSupport.Bounds ScopedPorts.Support.empty value.dependencies receiver := by
        simpa only [sameEnvironment] using initialAuthentication.current_support
      have bodySupport : SourceSupport.Bounds (ScopedPorts.Support.extend ScopedPorts.Support.empty parameter receiver) body.dependencies receiver := by
        simpa only [LexicalBounds.environment_extend, sameEnvironment] using bodyAuthentication.current_support
      let valueSupported : CoreCallableContractAdmission.Supported globals outward world allowed runtimeScope Environment.empty
          ScopedPorts.Support.empty value input initialDemand initialReq initialPlan initialRows receiver receiver :=
        ⟨initialSource, operandSupport, actualReceiver.issued, ⟨lexical, sameEnvironment, initialAuthentication⟩, actualReceiver.issued⟩
      let bodySupported : CoreCallableContractAdmission.Supported globals outward world allowed runtimeScope
          (Environment.empty.extend parameter input) (ScopedPorts.Support.extend ScopedPorts.Support.empty parameter receiver)
          body output bodyDemand bodyReq bodyPlan bodyRows receiver receiver :=
        ⟨bodySource, bodySupport, actualReceiver.issued,
          ⟨lexical.extend parameter receiver, by simp only [LexicalBounds.environment_extend, sameEnvironment], bodyAuthentication⟩,
          actualReceiver.issued⟩
      obtain ⟨nextPlan, nextRows, nextCurrent, exactPlan, sameSignature, sameRows⟩ :=
        bodySupported.substitution_reannotated stable valueSupported closed
      cases certificate with
      | sequence initialCertificate bodyCertificate =>
        cases certificateChecked with
        | sequence initialChecked bodyChecked =>
          have bodyRun := (Accounting.silent_prefix_iff (Source.value_silent initialSource closed.1) initialRows bodyRows).mp accounting
          obtain ⟨nextCertificate, nextChecked, nextRun⟩ := transport_current_rows sameSignature sameRows bodyCertificate bodyChecked bodyRun
          let next : Site globals outward world allowed actions phases budget ambient installations
              (body.subst parameter value) runtimeScope stack output final context root :=
            { sourceDemand := bodyDemand, requirements := bodyReq, dependencies := bodyDependencies, plan := nextPlan, rows := nextRows,
              bound := receiver, current := nextCurrent, received := actualReceiver.received,
              certificate := nextCertificate, certificateChecked := nextChecked,
              pending := pending, retained := retained, retainedChecked := retainedChecked,
              accounting := nextRun,
              annotated := annotated, row := row, annotation := annotation, checked := checked, bounded := bounded }
          exact ⟨next, .bind parameter value body runtimeScope stack closed captureClosed⟩

theorem Site.plug_bind {receiving : SourceDependencyCapture.Scope} {hints : ReturnHints receiving} {context : Context hints}
    (site : Site globals outward world allowed actions phases budget ambient installations
      value runtimeScope (.push (.plain data) stack) input final (.plain restRows context) root)
    (closed : ClosedValue value) :
    ∃ (parameter : Nat) (body : Code), data.context = .bind parameter body ∧
      ∃ output : Contract, ∃ _next : Site globals outward world allowed actions phases budget ambient installations
        (.bind parameter value body) data.scope stack output final context root,
        RawStep ⟨value, runtimeScope, .push (.plain data) stack⟩ ⟨.bind parameter value body, data.scope, stack⟩ [] [] := by
  rcases site with ⟨sourceDemand, requirements, dependencies, plan, rows, bound, current, received, certificate, certificateChecked,
    pending, retained, retainedChecked, accounting, annotated, row, annotation, checked, bounded⟩
  cases pending with
  | plain frame bodyReceived accepts tail =>
      rename_i middle parameter body bodyDemand bodyReq inputBound bodyBound bodyPlan bodyRows
      have valueSupport : SourceSupport.Bounds ScopedPorts.Support.empty value.dependencies inputBound := by
        apply finite_bounds
        · intro identity member
          have supported := current.support.resources member
          exact accepts identity (current.issued supported) (received supported)
        · intro name; simp [ScopedPorts.Support.empty]
      obtain ⟨currentLexical, currentEnvironment, currentAuth⟩ := current.authentication
      obtain ⟨bodyLexical, bodyEnvironment, bodyAuth⟩ := frame.bodySource.authentication
      let lexical := bodyLexical.extend parameter []
      have lexicalEnvironment : lexical.environment = ScopedPorts.Support.empty := by
        funext n
        by_cases same : n = parameter
        · subst n; simp [lexical, LexicalBounds.environment, ScopedPorts.Support.empty]
        · have old := congrFun bodyEnvironment n
          simpa [lexical, LexicalBounds.environment, CoreCallableContractAdmission.lexical_lookup_extend,
            ScopedPorts.Support.extend, ScopedPorts.Support.empty, same] using old
      have bodyName : bodyLexical.environment parameter = actualReceiver world receiving ambient := by
        simpa [ScopedPorts.Support.extend] using congrFun bodyEnvironment parameter
      have bodyAuthCompleted := bodyAuth.complete_binding parameter
      have bodyAuthCurrent : Authenticated globals.registry outward frame.bodySource.source
          (lexical.extend parameter (actualReceiver world receiving ambient)) (actualReceiver world receiving ambient) := by
        have completed : Authenticated globals.registry outward frame.bodySource.source
            (bodyLexical.extend parameter (actualReceiver world receiving ambient)) (actualReceiver world receiving ambient) := by
          simpa only [bodyName] using bodyAuthCompleted
        apply completed.lexical_congr
        intro n _
        by_cases same : n = parameter <;> simp [lexical, CoreCallableContractAdmission.lexical_lookup_extend, same]
      have valueSource : Source globals outward world allowed data.scope Environment.empty value input [] (.request [] []) .pure Rows.pure :=  ((IndexedSource.value_summary current.source) closed.1).value_allowed closed.1 allowed data.scope
      have valueSupported : CoreCallableContractAdmission.Supported globals outward world allowed data.scope Environment.empty
          ScopedPorts.Support.empty value input [] (.request [] []) .pure Rows.pure inputBound (actualReceiver world receiving ambient) :=
        ⟨valueSource, valueSupport, frame.inputIssued,
          ⟨currentLexical, currentEnvironment, (currentAuth.value_summary closed.1).value_allowed closed.1 allowed data.scope⟩,
          actualReceiver.issued⟩
      have valueAuth : Authenticated globals.registry outward valueSource lexical (actualReceiver world receiving ambient) := by
        apply ((currentAuth.value_summary closed.1).value_allowed closed.1 allowed data.scope).value_reauthenticate closed
        simpa only [lexicalEnvironment, actualReceiver, SourceDependencyCapture.Scope.visibleResources] using current.actual_received
      have pluggedSource := Source.bind valueSource frame.bodySource.source
      have pluggedSupport : SourceSupport.Bounds ScopedPorts.Support.empty (Code.bind parameter value body).dependencies (bound ++ bodyBound) := by
        apply finite_bounds
        · intro identity member
          obtain left | right := List.mem_append.mp (Syntax.mem_resourceDependencies.mp member)
          · exact List.mem_append_left _ (current.support.resources (Syntax.mem_resourceDependencies.mpr left))
          · exact List.mem_append_right _ (frame.bodySource.support.resources (Syntax.mem_resourceDependencies.mpr (Syntax.mem_without.mp right).1))
        · intro name; simp [ScopedPorts.Support.empty]
      have bindActual : SourceSupport.Bounds lexical.environment (Code.bind parameter value body).dependencies
          (actualReceiver world receiving ambient) := by
        rw [lexicalEnvironment]
        apply finite_bounds
        · intro identity member
          obtain left | right := List.mem_append.mp (Syntax.mem_resourceDependencies.mp member)
          · exact valueAuth.current_support.resources (Syntax.mem_resourceDependencies.mpr left)
          · exact bodyAuthCurrent.current_support.resources (Syntax.mem_resourceDependencies.mpr (Syntax.mem_without.mp right).1)
        · intro name; simp [ScopedPorts.Support.empty]
      have bindAuth : Authenticated globals.registry outward pluggedSource lexical (actualReceiver world receiving ambient) :=
        .checked bindActual (.bind valueAuth bodyAuthCurrent)
      have nextReceived : bound ++ bodyBound ⊆ _ := List.append_subset.mpr ⟨received, bodyReceived⟩
      have nextIssued : bound ++ bodyBound ⊆ world := List.append_subset.mpr ⟨current.issued, frame.bodySource.issued⟩
      have waiting := (Accounting.silent_iff (Source.value_silent current.source closed.1) rows).mp accounting
      cases retained with
      | plain suffixCertificate tailCertificate =>
          cases retainedChecked with
          | plain suffixChecked tailChecked =>
              cases waiting with
              | plain suffixRun =>
                  have bodyCertificate := suffixCertificate.reindex_context context.append_nil_pack
                  have bodyChecked := suffixChecked.reindex_context context.append_nil_pack
                  have shape : PlugRows bodyRows (sequenceRows (first := .pure) Rows.pure bodyRows) := .single
                  let next : Site globals outward world allowed actions phases budget ambient installations
                      (.bind parameter value body) data.scope stack middle final context root :=
                    { sourceDemand := bodyDemand, requirements := .sequence (.request [] []) bodyReq,
                      dependencies := .sequence .pure _, plan := .sequence .pure bodyPlan, rows := sequenceRows (first := .pure) Rows.pure bodyRows,
                      bound := bound ++ bodyBound, current := ⟨pluggedSource, pluggedSupport, nextIssued, ⟨lexical, lexicalEnvironment, bindAuth⟩, actualReceiver.issued⟩, received := nextReceived,
                      certificate := shape.source_certificate bodyCertificate, certificateChecked := InstallationSupport.plug_rows shape bodyChecked,
                      pending := tail, retained := tailCertificate, retainedChecked := tailChecked,
                      accounting := shape.accounting_iff.mpr suffixRun,
                      annotated := annotated, row := row, annotation := annotation, checked := checked, bounded := bounded }
                  refine ⟨parameter, body, frame.position, middle, next, ?_⟩
                  have raw := RawStep.plug data value closed runtimeScope stack
                  simpa only [frame.position, ScopedExecution.Context.plug] using raw

theorem Site.read_cell_reply
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.perform (Instantiation.freezeEffect (.cell identity)) 0 (.resourceRef (.activation identity))) runtimeScope stack result final context root)
    (compatible : globals.operations (.cell identity) 0 = some (.reference identity, .integer))
    (updated : CellUpdate identity payload payload stack after) :
    ∃ _next : Site globals outward world allowed actions phases budget ambient installations
      (.integer payload) runtimeScope after .integer final context root,
      RawStep ⟨.perform (Instantiation.freezeEffect (.cell identity)) 0 (.resourceRef (.activation identity)), runtimeScope, stack⟩
        ⟨.integer payload, runtimeScope, after⟩ [] [] := by
  rcases site with ⟨sourceDemand, requirements, dependencies, plan, rows, bound, current, received, certificate, certificateChecked,
    pending, retained, retainedChecked, accounting, annotated, row, annotation, checked, bounded⟩
  rcases current with ⟨source, support, issued, authentication, receiverIssued⟩
  generalize equation : Code.perform (Instantiation.freezeEffect (.cell identity)) 0 (.resourceRef (.activation identity)) = code at source
  cases source <;> try { cases equation }
  case perform =>
    rename_i actual operationActual input valueActual deps operandPlan operandRows admitted known formed operandReq operand
    simp only [Code.perform.injEq] at equation
    obtain ⟨sameEffect, sameOperation, sameValue⟩ := equation
    have same : Instance.cell identity = actual := Instantiation.effect_realization_unique
      (Instantiation.frozen_effect_realizes Instantiation.Environment.empty (.cell identity))
      (by rw [sameEffect]; exact Instantiation.frozen_effect_realizes Instantiation.Environment.empty actual)
    subst actual
    subst operationActual
    subst valueActual
    have signatures := Option.some.inj (known.symm.trans compatible)
    obtain ⟨inputSame, resultSame⟩ := Prod.mk.inj signatures
    subst input
    subst result
    cases operand with
    | reference operandIssued =>
        have requestRun : Accounting.Run world installations Rows.request context root :=
          (Accounting.silent_prefix_iff .pure Rows.pure Rows.request).mp accounting
        have waiting := requestRun.builtin_wait (pending.cell_update_builtin updated)
        let next : Site globals outward world allowed actions phases budget ambient installations
            (.integer payload) runtimeScope after .integer final context root :=
          { sourceDemand := [], requirements := .request [] [], dependencies := .pure, plan := .pure, rows := Rows.pure,
            bound := [], current := ⟨.integer, .nil, by simp, ⟨[], rfl, .checked .nil .integer⟩, actualReceiver.issued⟩, received := by simp,
            certificate := .pure, certificateChecked := .pure,
            pending := pending.cell_update updated, retained := retained, retainedChecked := retainedChecked,
            accounting := .pure waiting, annotated := annotated, row := row, annotation := annotation, checked := checked, bounded := bounded }
        exact ⟨next, .readCell identity payload runtimeScope stack after updated⟩

/-- Finite structural row data for the concrete builtin acceptance gate. -/
inductive ReadRows : {dependencies : Dependencies} → {plan : Plan dependencies} → Rows (signature plan) → Prop where
  | pure : ReadRows (plan := .pure) Rows.pure
  | read : ReadRows (plan := .request (effect := .cell 0) (operation := 0)) Rows.request
  | sequence (left : ReadRows first) (right : ReadRows second) : ReadRows (sequenceRows first second)

/-- Actual lexical receivers with cell0, allowing retained plain suffixes. -/
inductive ReadReceiver : {scope : SourceDependencyCapture.Scope} → {hints : ReturnHints scope} → Context hints → Prop where
  | cell : ReadReceiver (Context.cell (identity := 0) Context.nil)
  | plain (tail : ReadReceiver context) : ReadReceiver (Context.plain rows context)

omit [DeclarationPolicy] in
theorem ReadReceiver.select (receiver : ReadReceiver context) : select (.cell 0) 0 context = some (.builtin 0) := by
  induction receiver with
  | cell => rfl
  | plain tail ih => simp [SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.select, ih, Selection.prepend]

omit [DeclarationPolicy] in
/-- Construct current checking, rather than leave it a generic premise. -/
theorem ReadRows.admission {scope : SourceDependencyCapture.Scope} {hints : ReturnHints scope} {context : Context hints} (structural : ReadRows rows) (receiver : ReadReceiver context) :
    ∃ certificate : SourceAdmission.Code outward actions budget phases world installations rows context,
      InstallationSupport.CodeChecked ambient outward certificate := by
  induction structural generalizing scope with
  | pure => exact ⟨.pure, .pure⟩
  | read => exact ⟨.builtin receiver.select, .builtin (found := receiver.select)⟩
  | sequence left right ihL ihR =>
      obtain ⟨first, firstChecked⟩ := ihL (.plain receiver)
      obtain ⟨second, secondChecked⟩ := ihR receiver
      exact ⟨.sequence first second, .sequence firstChecked secondChecked⟩

omit [DeclarationPolicy] in
/-- Every read is interpreted by the actual cell receiver. The exact root
comes from the continuation, with no assumption about a future execution. -/
theorem ReadRows.accounting {scope : SourceDependencyCapture.Scope} {hints : ReturnHints scope} {context : Context hints} (structural : ReadRows rows) (receiver : ReadReceiver context)
    (waiting : Accounting.Wait world installations context .ordinary root) :
    Accounting.Run world installations rows context root := by
  induction structural generalizing scope with
  | pure => exact .pure waiting
  | read => exact .builtin receiver.select waiting
  | sequence left right ihL ihR => exact .sequence (ihL (.plain receiver) (.plain (ihR receiver waiting)))

#print axioms Site.read_cell_reply
#print axioms ReadReceiver.select
#print axioms ReadRows.admission
#print axioms ReadRows.accounting
#print axioms Source.value_silent
#print axioms FrameSource.plug
#print axioms Pending.cell_update
#print axioms Pending.cell_update_builtin
#print axioms Source.lower
#print axioms SelectedPending.owners_known_mono
#print axioms Pending.owners_known_mono
#print axioms HandlerSource.owners_congr
#print axioms HandlerSource.of_whole
#print axioms HandlerSource.of_domain
#print axioms FrameSource.owners_known_mono
#print axioms Site.plug_bind
#print axioms Site.bind_value
#print axioms Site.focus_bind
#print axioms Site.certified
end
end Ash.OneShot.CoreCallableContractExecution
