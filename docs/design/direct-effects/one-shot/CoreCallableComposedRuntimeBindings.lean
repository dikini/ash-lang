import CoreCallableComposedResourceEntry
import CoreCallableComposedCapturedHandle
import CoreReadyBindings
import CoreTypeSupport
import CoreOperationSignatures
namespace Ash.OneShot.CoreCallableComposedRuntimeBindings
open ScopedExpressions ScopedExecution CoreSyntax CoreTranslation CoreMachine CoreValueRelation
open CoreStrictStack CoreStrictFrames CoreInitialPrefix CoreCallableComposedResourceEntry
open CoreOrdinaryCompletion CoreCallableChecks

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

variable {graph : Graph} {s : Selection graph}

def closeCode (s : Selection graph) (code : Code) : Code :=
  ((code.subst s.outer.id (.integer s.outerValue)).instantiate
    (Instantiation.Environment.empty.bind s.resource s.s8.nextActivation)).subst s.handle.id
      (.resourceRef (.activation s.s8.nextActivation))

/-- The next original node and its exact raw children are finite data. Current
suffix/plain readiness stays explicit; no environment or runtime value enters. -/
structure ReaderSelection (s : Selection graph) where
  binder : Binder
  parameter : Binder
  binderType : binder.type = .function .unit .integer [.cell (.bound s.resource)]
  functionSite : Nat
  functionBody : Nat
  tailSite : Nat
  node : CoreSyntax.Node
  functionNode : CoreSyntax.Node
  rawFunction : Code
  rawTail : Code
  fuel : Nat
  fnFuel : Nat
  known : graph.node s.bodySite = some node
  kind : node.kind = .bind binder functionSite tailSite
  functionKnown : graph.node functionSite = some functionNode
  functionKind : functionNode.kind = .function parameter functionBody
  functionTranslated : translateFuel graph fuel [] functionSite = .ok (.lambda parameter.id rawFunction)
  tailTranslated : translateFuel graph fuel [] tailSite = .ok rawTail
  rawSame : s.rawBody = .bind binder.id (.lambda parameter.id rawFunction) rawTail
  outerDifferent : binder.id ≠ s.outer.id
  handleDifferent : binder.id ≠ s.handle.id
  ready : ClosedExcept binder.id (closeCode s rawTail)
  noTicket : Execution.Scope.none.translate (Context.bind binder.id (closeCode s rawTail)).dependencies = some []

def ReaderSelection.closedBody (r : ReaderSelection s) : Code :=
  if s.handle.id = r.parameter.id then
    (if s.outer.id = r.parameter.id then r.rawFunction else r.rawFunction.subst s.outer.id (.integer s.outerValue)).instantiate
      (Instantiation.Environment.empty.bind s.resource s.s8.nextActivation)
  else
    ((if s.outer.id = r.parameter.id then r.rawFunction else r.rawFunction.subst s.outer.id (.integer s.outerValue)).instantiate
      (Instantiation.Environment.empty.bind s.resource s.s8.nextActivation)).subst s.handle.id
        (.resourceRef (.activation s.s8.nextActivation))
def ReaderSelection.initializer (r : ReaderSelection s) : Code := .lambda r.parameter.id r.closedBody
def ReaderSelection.suffix (r : ReaderSelection s) : Code := closeCode s r.rawTail
def ReaderSelection.support (r : ReaderSelection s) : List Nat :=
  Syntax.resourceDependencies r.closedBody.dependencies

def ReaderSelection.inputType (r : ReaderSelection s) : Ty :=
  .function .unit .integer [.cell s.s8.nextActivation] r.support

def ReaderSelection.plain (r : ReaderSelection s) : PlainData :=
  ⟨.bind r.binder.id r.suffix,.none,r.inputType,.integer,[],r.noTicket⟩

theorem ReaderSelection.input_decorated (r : ReaderSelection s) :
    CoreTypeSupport.decorate r.binder.type
      (.function .unit .integer (r.support.map Instantiation.ResourceName.activation)) =
      .ok (.function .unit .integer [.cell (.bound s.resource)]
        (r.support.map Instantiation.ResourceName.activation)) := by
  rw [r.binderType]
  rfl

private theorem realize_support (resources : List Nat) (environment : Instantiation.Environment) :
    (resources.map Instantiation.ResourceName.activation).mapM
      (CoreOperationSignatures.realizeName environment) = .ok resources := by
  induction resources with
  | nil => rfl
  | cons name rest ih =>
    simp only [List.map_cons,List.mapM_cons,CoreOperationSignatures.realizeName,ih]
    rfl

theorem ReaderSelection.input_realized (r : ReaderSelection s) :
    CoreOperationSignatures.realizeType
      (Instantiation.Environment.empty.bind s.resource s.s8.nextActivation)
      (.function .unit .integer [.cell (.bound s.resource)]
        (r.support.map Instantiation.ResourceName.activation)) = .ok r.inputType := by
  simp only [CoreOperationSignatures.realizeType,realize_support]
  simp [CoreOperationSignatures.realizeEffect,CoreOperationSignatures.realizeName,
    Instantiation.Environment.bind,ReaderSelection.inputType,Bind.bind,Except.bind]
  rfl

theorem ReaderSelection.initializer_exact (r : ReaderSelection s) :
    closeCode s (.lambda r.parameter.id r.rawFunction) = r.initializer := by
  simp only [closeCode,ReaderSelection.initializer,ReaderSelection.closedBody,Code.subst,Code.instantiate]

theorem ReaderSelection.body_exact (r : ReaderSelection s) :
    s.openedBody = .bind r.binder.id r.initializer r.suffix := by
  rw [Selection.openedBody,Selection.closedBody,r.rawSame]
  simp only [Code.subst,Code.instantiate,Ne.symm r.outerDifferent,Ne.symm r.handleDifferent,↓reduceIte]
  rw [← r.initializer_exact]
  rfl

def closedLambdaCheck (code : Code) : Bool :=
  decide (code.freeNames = []) && code.dependencies.all (fun dependency =>
    match dependency with | .resource _ => true | _ => false)

theorem closedLambdaCheck_sound (checked : closedLambdaCheck (.lambda parameter body) = true) :
    ClosedValue (.lambda parameter body) := by
  obtain ⟨resources,names⟩ := Bool.and_eq_true_iff.mp checked
  have resourceClosed : (Code.lambda parameter body).freeNames = [] := of_decide_eq_true resources
  refine ⟨trivial,resourceClosed,?_⟩
  intro dependency member
  have actual := List.all_eq_true.mp names dependency member
  cases dependency <;> simp_all

/-- Output of current executable callable and closure checks. -/
structure CheckedReader (r : ReaderSelection s) where
  callable : CheckedCallable
  accepted : checkAmbient graph r.functionSite [] = .ok callable
  parameterSame : callable.parameter = r.parameter.id
  bodySame : callable.body = r.functionBody
  rawSame : callable.rawBody = r.rawFunction
  closedAccepted : closedLambdaCheck r.initializer = true
  closed : ClosedValue r.initializer

inductive Error where
  | callable : CoreCallableChecks.Error → Error
  | selection
  | closed

def produce_reader (r : ReaderSelection s) : Except Error (CheckedReader r) := do
  match accepted : checkAmbient graph r.functionSite [] with
  | .error error => .error (.callable error)
  | .ok callable =>
    if parameterSame : callable.parameter = r.parameter.id then
      if bodySame : callable.body = r.functionBody then
        if rawSame : codeEq callable.rawBody r.rawFunction = true then
          if closed : closedLambdaCheck r.initializer = true then
            .ok ⟨callable,accepted,parameterSame,bodySame,codeEq_sound _ _ rawSame,closed,closedLambdaCheck_sound closed⟩
          else .error .closed
        else .error .selection
      else .error .selection
    else .error .selection

def ReaderSelection.s10 (r : ReaderSelection s) : CoreMachine.State := {s.s9 with
  control := .evaluate r.functionSite s.acquiredEnvironment,
  frames := .bind r.binder.id r.tailSite s.acquiredEnvironment :: s.s9.frames,
  observations := s.s9.observations ++ [.entered s.bodySite]}
def ReaderSelection.s11 (r : ReaderSelection s) : CoreMachine.State := {r.s10 with
  control := .returned (.closure r.parameter.id r.functionBody s.acquiredEnvironment),
  observations := r.s10.observations ++ [.entered r.functionSite]}
def ReaderSelection.installedEnvironment (r : ReaderSelection s) : Environment :=
  .binding r.binder.id (.closure r.parameter.id r.functionBody s.acquiredEnvironment) s.acquiredEnvironment
def ReaderSelection.s12 (r : ReaderSelection s) : CoreMachine.State := {r.s11 with
  control := .evaluate r.tailSite r.installedEnvironment,frames := s.s9.frames}
def ReaderSelection.p10 (r : ReaderSelection s) : Point := ⟨r.s10,s.p9.target,[],
  ([], .bind r.binder.id r.tailSite s.acquiredEnvironment)::s.p9.annotations⟩
def ReaderSelection.p11 (r : ReaderSelection s) : Point := ⟨r.s11,s.p9.target,[],r.p10.annotations⟩
def ReaderSelection.p12 (r : ReaderSelection s) : Point := ⟨r.s12,
  ⟨r.suffix.subst r.binder.id r.initializer,.none,s.p9.target.stack⟩,[],s.p9.annotations⟩

/-- Current closing is derived from original acquisition, not passed to the
callable factory as a desired environment interpretation. -/
theorem reader_closing (s : Selection graph) (r : ReaderSelection s)
    (input : CoreCallableInitialChronology.InitialInput graph s.rootCode) :
    EnvCloses graph [] [] s.acquiredEnvironment (.lambda r.parameter.id r.rawFunction) r.initializer := by
  have closed := entry_opened s input
  rw [r.rawSame,r.body_exact] at closed
  exact (bind_components closed).1

theorem reader_value (s : Selection graph) (r : ReaderSelection s)
    (input : CoreCallableInitialChronology.InitialInput graph s.rootCode) (checked : CheckedReader r) :
    ValueRel graph [] [] (.closure r.parameter.id r.functionBody s.acquiredEnvironment) r.initializer := by
  have certificate := checkAmbient_certificate checked.accepted
  rw [checked.parameterSame,checked.bodySame,checked.rawSame] at certificate
  exact .closure certificate.2 certificate.1 (reader_closing s r input) checked.closed

theorem reader_chain (s : Selection graph) (r : ReaderSelection s)
    (input : CoreCallableInitialChronology.InitialInput graph s.rootCode) (checked : CheckedReader r) :
    Chain graph s.p9 [r.p10,r.p11,r.p12] r.p12 ∧
    EnvCloses graph [] [] r.installedEnvironment r.rawTail (r.suffix.subst r.binder.id r.initializer) := by
  have certificates := checkAmbient_certificate checked.accepted
  rw [checked.parameterSame,checked.bodySame,checked.rawSame] at certificates
  have certificate := certificates.1
  have closing := entry_opened s input
  rw [r.rawSame,r.body_exact] at closing
  have tail : PushedWithMaps graph [] s.p9.annotations s.p9.target.stack :=
    .boundary (.cell s.resourceKnown s.resourceKind) .nil
  have produced := CoreReadyBindings.lambda_binding_mapped (base := s.s9)
    (ordered := CoreTranslationFuel.checkShape_postorder graph input.shape)
    r.known r.kind r.functionKnown r.functionKind r.functionTranslated r.tailTranslated
    certificates.2 rfl certificate closing checked.closed r.ready
    r.plain rfl tail
  simpa [ReaderSelection.p10,ReaderSelection.p11,ReaderSelection.p12,ReaderSelection.s10,
    ReaderSelection.s11,ReaderSelection.s12,ReaderSelection.installedEnvironment,
    ReaderSelection.plain,Selection.p9,Selection.s9,framesOf,
    checked.parameterSame,checked.bodySame,checked.rawSame,r.body_exact,Selection.s8,Selection.s7,Selection.s6,Selection.s5,Selection.s4,Selection.s3,Selection.s2,Selection.s1,Selection.s0,CoreMachine.initial] using ⟨produced.1,produced.2.1⟩

private theorem append_chain (first : Chain graph before points middle)
    (last : Chain graph middle later after) : Chain graph before (points ++ later) after := by
  induction first with
  | last link => exact .next link last
  | next link rest ih => exact .next link (ih last)

private theorem link_step (link : Link graph before after) : CoreMachine.Step graph before.state after.state := by
  cases link with
  | positive _ core _ _ => exact core
  | traversal witness => exact witness.core
  | value witness => exact witness.core

private theorem chain_steps (chain : Chain graph before points after) :
    CoreAllocationHistory.Steps graph points.length before.state after.state := by
  induction chain with
  | last link => exact .snoc (.refl _) (link_step link)
  | next link rest ih =>
    simpa [Nat.add_comm] using (CoreAllocationHistory.Steps.snoc (.refl _) (link_step link)).trans ih

/-- The same initial endpoint, acquisition, and installed reader form one
produced path, including both ranked administrative edges of the lambda bind. -/
theorem installed_chain (s : Selection graph) (r : ReaderSelection s)
    (input : CoreCallableInitialChronology.InitialInput graph s.rootCode) (checked : CheckedReader r) :
    Chain graph s.p0 [s.p1,s.p2,s.p3,s.p4,s.p5,s.p6,s.p7,s.p8,s.p9,r.p10,r.p11,r.p12] r.p12 :=
  append_chain (entry_chain s input) (reader_chain s r input checked).1

theorem installed_steps (s : Selection graph) (r : ReaderSelection s)
    (input : CoreCallableInitialChronology.InitialInput graph s.rootCode) (checked : CheckedReader r) :
    CoreAllocationHistory.Steps graph 12 (CoreMachine.initial graph) r.s12 :=
  chain_steps (installed_chain s r input checked)

theorem installed_lookup (s : Selection graph) (r : ReaderSelection s) :
    r.installedEnvironment.lookup r.binder.id = some (.closure r.parameter.id r.functionBody s.acquiredEnvironment) := by
  simp [ReaderSelection.installedEnvironment,Environment.lookup]

noncomputable def installed_history (s : Selection graph) (r : ReaderSelection s) :
    CoreCallableGeneralHistory.GeneralHistory graph r.s12.heap r.s12.frames
      (.push (.cell s.s8.nextActivation s.payload .none .integer) .nil) := entry_history s

theorem installed_activation (s : Selection graph) (r : ReaderSelection s)
    (input : CoreCallableInitialChronology.InitialInput graph s.rootCode) (checked : CheckedReader r) :
    r.s12.nextActivation = 1 ∧ CoreAllocationHistory.History r.s12 :=
  ⟨rfl,CoreAllocationHistory.initial_steps_history graph (installed_steps s r input checked)⟩

open ProtectionContracts CoreCallableContractAdmission CoreCallableReceiverRefinement
open CoreCallableComposedResourceOrigins CoreCallableComposedCapturedHandle
open CoreCallableCompositionalResourceBody
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
local instance : SourcePlannedChecks.DeclarationPolicy :=
  SourceScheduledCleanupInterfaces.Lexical.Recursive.declarationPolicy
section StaticReader
variable {entries : CoreCallableStaticProducer.OperationEntries} {owners : CoreCallableContractRegistries.Owners}
variable {root originalInitializer code : Code} {binder : Nat} {original : CoreCallableStaticProducer.Bindings}
variable {originalPath : Prefix entries owners root (.resource binder originalInitializer code) original}
variable {prior : CheckedOriginalPrefix originalPath
  api policy declarations outward world allowed scope receiver}
variable {annotation : CoreCallableStaticProducer.Annotation entries owners original originalInitializer .integer initialDemand initialReq initialPlan initialRows}
variable {body : Body original rootContext code rootPattern rootChecking rootNeeds}
variable {opened : ResourceOpened prior annotation body initialRecipe bodyRecipe residual bound}
variable {current : Body original ((name,.old (.reference (.bound binder)))::context)
  (.lambda formal readerCode) (.function input output requests latent checking) .pure .empty}
variable {produced : CoreCallableCompositionalResourceStorage.Produced api binder world
  ((name,.storage [.fresh])::storage) (.lambda formal readerCode) stored}
variable {path : OpenedBind opened current produced recipe (name::names)}
variable {fresh : s.s8.nextActivation ∉ world}

/-- One retained full constructor family, its exact original receipt and
lower substitution, joined to the actual Core closure at the computed owner.
The root/code equalities are outputs of finite executable comparisons. -/
def PairedReader (r : ReaderSelection s)
    (receipt : Current path s.s8.nextActivation fresh)
    (_handle : CapturedHandle path s.s8.nextActivation fresh) : Prop :=
    s.rootCode = root ∧
    CoreCallableGraphAnnotationChecks.typeB
      (Instantiation.Environment.empty.bind binder s.s8.nextActivation) r.binder.type
      ((Pattern.function input output requests latent checking).value original s.s8.nextActivation) = true ∧
    ∃ nextCode, ∃ family : CoreCallableCapturedLambdaConstructor.Family
        (CoreCallableFiniteCellRegistry.registry (some api) entries policy) outward owners
        (world ++ [s.s8.nextActivation]) (CoreCallableStaticProducer.environment (bindings original s.s8.nextActivation context)) formal nextCode
        (input.value original s.s8.nextActivation) (output.value original s.s8.nextActivation)
        (requests.map (EffectName.value s.s8.nextActivation)) (latent.map (RequestName.value s.s8.nextActivation))
        (checking.plan s.s8.nextActivation) (checking.rows s.s8.nextActivation),
      ∃ replacement : IndexedSource (CoreCallableFiniteCellRegistry.registry (some api) entries policy) outward owners
        (world ++ [s.s8.nextActivation]) (.cell s.s8.nextActivation::residual) scope
        (CoreCallableStaticProducer.environment (bindings original s.s8.nextActivation context))
        (.resourceRef (.activation s.s8.nextActivation)) (.reference s.s8.nextActivation) [] (.request [] []) .pure Rows.pure,
      CoreCallableCapturedLambdaConstructor.Receipt receipt.source replacement structural_policy_stable _handle.closed nextCode family ∧
      Code.lambda formal nextCode =
        (Code.lambda formal (readerCode.instantiate (Instantiation.Environment.empty.bind binder s.s8.nextActivation))).subst name (.resourceRef (.activation s.s8.nextActivation)) ∧
      Authenticated (CoreCallableFiniteCellRegistry.registry (some api) entries policy) outward
        (family.whole (allowed := .cell s.s8.nextActivation::residual) (scope := scope))
        (lexicalAfter prior.lexical (s.s8.nextActivation::receiver) names) (s.s8.nextActivation::receiver) ∧
      CallableContracts.Derives declarations
        (CoreCallableReturnStorageProducer.environment (CoreCallableCompositionalResourceStorage.realize s.s8.nextActivation storage))
        (world ++ [s.s8.nextActivation]) .none (Code.lambda formal nextCode) (stored.value s.s8.nextActivation) ∧
      ValueRel graph [] [] (.closure r.parameter.id r.functionBody s.acquiredEnvironment) (.lambda formal nextCode)

/-- Consume already executed original static receipts. The executable root and
changed-reader comparisons preserve their indices; they do not supply a new
origin, constructor family, environment, or future operational result. -/
noncomputable def pair_reader (r : ReaderSelection s)
    (initial : CoreCallableInitialChronology.InitialInput graph s.rootCode) (checked : CheckedReader r)
    (receipt : Current path s.s8.nextActivation fresh)
    (handle : CapturedHandle path s.s8.nextActivation fresh) : Except Error (PLift (PairedReader r receipt handle)) :=
  if rootSame : codeEq s.rootCode root = true then
    if changedSame : codeEq r.initializer
        ((Code.lambda formal (readerCode.instantiate (Instantiation.Environment.empty.bind binder s.s8.nextActivation))).subst name (.resourceRef (.activation s.s8.nextActivation))) = true then
      if typeSame : CoreCallableGraphAnnotationChecks.typeB
          (Instantiation.Environment.empty.bind binder s.s8.nextActivation) r.binder.type
          ((Pattern.function input output requests latent checking).value original s.s8.nextActivation) = true then
        .ok ⟨by
          refine ⟨codeEq_sound _ _ rootSame,typeSame,?_⟩
          obtain ⟨nextCode,family,replacement,origin,same,auth,lower⟩ := close_reader_handle receipt handle
          refine ⟨nextCode,family,replacement,origin,same,auth,lower,?_⟩
          rw [same,← codeEq_sound _ _ changedSame]
          exact reader_value s r initial checked⟩
      else .error .selection
    else .error .selection
  else .error .selection

theorem pair_reader_success (r : ReaderSelection s)
    (initial : CoreCallableInitialChronology.InitialInput graph s.rootCode) (checked : CheckedReader r)
    (receipt : Current path s.s8.nextActivation fresh) (handle : CapturedHandle path s.s8.nextActivation fresh)
    (rootSame : codeEq s.rootCode root = true)
    (changedSame : codeEq r.initializer
      ((Code.lambda formal (readerCode.instantiate (Instantiation.Environment.empty.bind binder s.s8.nextActivation))).subst name (.resourceRef (.activation s.s8.nextActivation))) = true)
    (typeSame : CoreCallableGraphAnnotationChecks.typeB
      (Instantiation.Environment.empty.bind binder s.s8.nextActivation) r.binder.type
      ((Pattern.function input output requests latent checking).value original s.s8.nextActivation) = true) :
    ∃ produced, pair_reader r initial checked receipt handle = .ok produced := by
  unfold pair_reader
  rw [dif_pos rootSame,dif_pos changedSame,dif_pos typeSame]
  exact ⟨_,rfl⟩
end StaticReader

#print axioms ReaderSelection.initializer_exact
#print axioms ReaderSelection.body_exact
#print axioms closedLambdaCheck_sound
#print axioms produce_reader
#print axioms reader_closing
#print axioms reader_value
#print axioms reader_chain
#print axioms installed_chain
#print axioms installed_steps
#print axioms installed_lookup
#print axioms installed_history
#print axioms installed_activation
#print axioms ReaderSelection.input_decorated
#print axioms ReaderSelection.input_realized
#print axioms PairedReader
#print axioms pair_reader
#print axioms pair_reader_success
end Ash.OneShot.CoreCallableComposedRuntimeBindings
