import CoreCallableOriginalResourceCurrent
namespace Ash.OneShot.CoreCallableOriginalCallableCurrent
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract Environment)
open CoreCallableContractAdmission CoreCallableReceiverRefinement CoreCallableContractExecution
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceScheduledCleanupInterfaces.Lexical.Recursive
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
local instance : SourcePlannedChecks.DeclarationPolicy := declarationPolicy
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace Original
open CoreCallableCompositionalResourceRoot
abbrev globals := CoreCallableOriginalResourceCurrent.Original.globals
abbrev reader := ComposedResourceRuntimeOriginProbes.reader
abbrev readerContract := readerPattern.value original 0
abbrev tailBody := CoreCallableCompositionalResourceBody.Body.bind (parameter := 13) higherOrder
  (CoreCallableCompositionalResourceBody.Body.bind (parameter := 5) actualCall choice)
abbrev tailCode := codeOf tailBody
abbrev tailChecking := checkingOf tailBody
abbrev tailNeeds := needsOf tailBody
abbrev instantiatedTail := tailCode.instantiate (Instantiation.Environment.empty.bind 3 0)
abbrev handleValue : Code := .resourceRef (.activation 0)
abbrev handleClosed : ClosedValue handleValue := by
  simp [ClosedValue,Code.IsValue,Code.ResourceClosed,Code.freeNames,Code.dependencies,Instantiation.ResourceName.freeNames]
abbrev outerClosed : ClosedValue (.integer 17) := by
  simp [ClosedValue,Code.IsValue,Code.ResourceClosed,Code.freeNames,Code.dependencies]
abbrev tailLexical : LexicalBounds := [(12,[0]),(9,[0]),(7,[])]
abbrev handleRemovedLexical : LexicalBounds := [(12,[0]),(7,[])]
abbrev tailEnvironment := (Environment.empty.extend 7 .integer).extend 12 readerContract
abbrev closedTail := (instantiatedTail.subst 9 handleValue).subst 7 (.integer 17)

theorem tail_derived : CoreCallableCompositionalResourceBody.Derived CoreCallableFiniteCellRegistry.original
    entries policy [] globals.owners [] .none original 3 0 [.cell (.bound 3)] tailBody :=
  tailBody.derive (residual := []) (by rfl) (by rfl)

theorem tail_authenticated : Authenticated globals.registry [] tail_derived.source tailLexical [0] := by
  apply tail_derived.tree.authenticate_world
  · exact List.Subset.refl _
  · exact CoreCallableGraphAnnotationChecks.knownB_sound (by rfl)
  · exact SourceSupport.bounds_iff.mpr (CoreCallableGraphAnnotationChecks.subsetB_sound (by rfl))

def handleCheck := CoreCallableFiniteRegistryBridge.recheck
  (CoreCallableStaticProducer.Annotation.reference (entries := entries) (owners := globals.owners)
    (bindings := original) 0) CoreCallableFiniteCellRegistry.original policy [] [0] [.cell 0] .none [(7,[])] [0]
theorem handle_checked : ∃ receipt, handleCheck = .ok receipt := ⟨_,rfl⟩

/-- Both removed bindings are the actual literal outer7 and acquired handle0.
The reader slot stays the full original Contract throughout substitution. -/
theorem tail_closed_source : ∃ nextPlan : Plan _, ∃ nextRows : Rows (signature nextPlan),
    ∃ source : Source globals [] [0] [.cell 0] .none (Environment.empty.extend 12 readerContract)
      closedTail .integer [] (tailNeeds.requirements 0) nextPlan nextRows,
    Authenticated globals.registry [] source [(12,[0])] [0] ∧
    signature nextPlan = signature (tailChecking.plan 0) ∧ HEq nextRows (tailChecking.rows 0) := by
  obtain ⟨handle,accepted⟩ := handle_checked
  obtain ⟨handleSource,_tree,handleAuth,_⟩ := CoreCallableFiniteRegistryBridge.recheck_success accepted
  let replacement := handleSource.closed_environment handleClosed tailEnvironment
  have replacementAuth : Authenticated globals.registry [] replacement handleRemovedLexical [0] := by
    apply (handleAuth.closed_environment handleClosed _).lexical_congr
    intro name member
    exact False.elim (ScopedTyping.closedValue_no_variable handleClosed member)
  have environmentEq : CoreCallableStaticProducer.environment
      (CoreCallableCompositionalResourceBody.bindings original 0 withReader) = tailEnvironment.extend 9 (.reference 0) := by
    change ((Environment.empty.extend 7 .integer).extend 9 (.reference 0)).extend 12 readerContract =
      tailEnvironment.extend 9 (.reference 0)
    exact Environment.extend_commute (Environment.empty.extend 7 .integer) 9 12 (.reference 0) readerContract (by decide)
  have lexicalEq : ∀ name, Syntax.Dependency.variable name ∈ instantiatedTail.dependencies →
      tailLexical.lookup name = (handleRemovedLexical.extend 9 [0]).lookup name := by
    intro name _
    by_cases n12 : name = 12 <;> by_cases n9 : name = 9 <;>
      simp_all [LexicalBounds.lookup,LexicalBounds.extend]
  obtain ⟨plan9,rows9,source9,auth9,_computed9,signature9,aligned9⟩ :=
    tail_authenticated.substitution_reannotated_at CoreCallableComposedCapturedHandle.structural_policy_stable
      tailEnvironment 9 (.reference 0) handleValue handleRemovedLexical [0] environmentEq lexicalEq
      replacement handleClosed (by simp [Code.dependencies,Syntax.resourceDependencies]) (fun _ => replacementAuth)
  have environment7 : tailEnvironment = (Environment.empty.extend 12 readerContract).extend 7 .integer :=
    Environment.extend_commute Environment.empty 7 12 .integer readerContract (by decide)
  have lexical7 : ∀ name, Syntax.Dependency.variable name ∈ (instantiatedTail.subst 9 handleValue).dependencies →
      handleRemovedLexical.lookup name = (LexicalBounds.extend [(12,[0])] 7 []).lookup name := by
    intro name _
    by_cases n12 : name = 12 <;> by_cases n7 : name = 7 <;>
      simp_all [LexicalBounds.lookup,LexicalBounds.extend]
  let integer := IndexedSource.closed_environment CoreCallableOriginalResourceCurrent.Original.integerSupported.source outerClosed
    (Environment.empty.extend 12 readerContract)
  have integerAuth : Authenticated globals.registry [] integer [(12,[0])] [0] := by
    obtain ⟨lexical,_same,auth⟩ := CoreCallableOriginalResourceCurrent.Original.integerSupported.authentication
    apply (auth.closed_environment outerClosed _).lexical_congr
    intro name member
    exact False.elim (ScopedTyping.closedValue_no_variable outerClosed member)
  obtain ⟨plan,rows,source,auth,_computed,signature,aligned⟩ :=
    auth9.substitution_reannotated_at CoreCallableComposedCapturedHandle.structural_policy_stable
      (Environment.empty.extend 12 readerContract) 7 .integer (.integer 17) [(12,[0])] []
      environment7 lexical7 integer outerClosed (by simp [Code.dependencies,Syntax.resourceDependencies]) (fun _ => integerAuth)
  exact ⟨plan,rows,source,auth,signature.trans signature9,aligned.trans aligned9⟩

abbrev readerInput := (CoreCallableCompositionalResourceBody.Pattern.old .unit).value original 0
abbrev readerOutput := (CoreCallableCompositionalResourceBody.Pattern.old .integer).value original 0
abbrev readerRequests := ([CoreCallableCompositionalResourceBody.EffectName.cell (.bound 3)] : List CoreCallableCompositionalResourceBody.EffectName).map (CoreCallableCompositionalResourceBody.EffectName.value 0)
abbrev readerLatent := ((CoreCallableCompositionalResourceBody.Need.embedded oldRead).summary).map (CoreCallableCompositionalResourceBody.RequestName.value 0)
abbrev readerPlan := (CoreCallableCompositionalResourceBody.Checking.embedded oldRead).plan 0
abbrev readerRows := (CoreCallableCompositionalResourceBody.Checking.embedded oldRead).rows 0
abbrev ClosedReaderFamily := CoreCallableCapturedLambdaConstructor.Family globals.registry [] globals.owners
  [0] Environment.empty 10 reader.closedBody readerInput readerOutput readerRequests readerLatent readerPlan readerRows

structure ClosedReaderOrigin {opened : CoreCallableComposedResourceOrigins.Probes.Opened}
    (selected : CoreCallableComposedResourceOrigins.Probes.ReaderPath opened)
    (current : CoreCallableComposedResourceOrigins.Current selected.path 0 (by simp))
    (handle : CoreCallableComposedCapturedHandle.CapturedHandle selected.path 0 (by simp)) where
  first : CoreCallableCapturedLambdaConstructor.Family globals.registry [] globals.owners [0]
    (Environment.empty.extend 7 .integer) 10 reader.closedBody readerInput readerOutput readerRequests readerLatent readerPlan readerRows
  replacement : Source globals [] [0] [.cell 0] .none (Environment.empty.extend 7 .integer)
    handleValue (.reference 0) [] (.request [] []) .pure Rows.pure
  handleReceipt : CoreCallableCapturedLambdaConstructor.Receipt current.source replacement
    CoreCallableComposedCapturedHandle.structural_policy_stable handle.closed reader.closedBody first
  lower : CallableContracts.Derives CoreCallableComposedResourceOrigins.Probes.Original.declarations
    (CoreCallableReturnStorageProducer.environment [(7,.storage [])]) [0] .none
    (Code.lambda 10 reader.closedBody) (selected.stored.value 0)
  lowerClosed : CallableContracts.Derives CoreCallableComposedResourceOrigins.Probes.Original.declarations
    (CoreCallableReturnStorageProducer.environment []) [0] .none
    (Code.lambda 10 reader.closedBody) (selected.stored.value 0)
  firstAuthentic : first.Authentic
  family : ClosedReaderFamily
  pointPlans : ∀ lexical call, HEq (family.plans lexical call)
    (CoreCallablePlanSubstitution.plan reader.closedBody
      (first.plans (CoreCallableCapturedLambdaConstructor.restored lexical 7 (.integer 17)) call) 7 (.integer 17))
  pointRows : ∀ lexical call, HEq (family.rows lexical call)
    (first.rows (CoreCallableCapturedLambdaConstructor.restored lexical 7 (.integer 17)) call)
  outerReceipt : CoreCallableCapturedLambdaConstructor.Receipt (first.whole (allowed := [.cell 0]) (scope := .none))
    CoreCallableOriginalResourceCurrent.Original.integerSupported.source
    CoreCallableComposedCapturedHandle.structural_policy_stable outerClosed reader.closedBody family
  authenticated : Authenticated globals.registry [] (family.whole (allowed := [.cell 0]) (scope := .none)) [] [0]

/-- Both complete constructor receipts are output from the original current
and captured-handle checks, then actual outer7 replacement. -/
theorem closed_reader_origin {opened : CoreCallableComposedResourceOrigins.Probes.Opened}
    (selected : CoreCallableComposedResourceOrigins.Probes.ReaderPath opened)
    (current : CoreCallableComposedResourceOrigins.Current selected.path 0 (by simp))
    (handle : CoreCallableComposedCapturedHandle.CapturedHandle selected.path 0 (by simp)) :
    Nonempty (ClosedReaderOrigin selected current handle) := by
  obtain ⟨replacement,_tree,replacementAuth,_⟩ := handle.rechecked
  obtain ⟨originalFamily,originalOrigin,originalAuthentic,_known⟩ :=
    CoreCallableCapturedLambdaConstructor.extract current.authenticated
  let first := originalFamily.changed CoreCallableComposedCapturedHandle.structural_policy_stable
    (show 9 ≠ 10 by decide) replacement handle.closed
  have firstAuthentic := originalFamily.changed_authentic originalAuthentic
    CoreCallableComposedCapturedHandle.structural_policy_stable (show 9 ≠ 10 by decide)
    replacement handle.closed replacementAuth
  have firstReceipt : CoreCallableCapturedLambdaConstructor.Receipt current.source replacement
      CoreCallableComposedCapturedHandle.structural_policy_stable handle.closed reader.closedBody first :=
    .changed originalFamily originalOrigin (by decide)
  have lower : CallableContracts.Derives CoreCallableComposedResourceOrigins.Probes.Original.declarations
      (CoreCallableReturnStorageProducer.environment [(7,.storage [])]) [0] .none
      (Code.lambda 10 reader.closedBody) (selected.stored.value 0) :=
    CallableContracts.substitution current.storage handle.lower handle.closed
  have integerChecked : CoreCallableReturnStorageProducer.check [] (.integer 17)
      (.node (some (.storage [])) []) = some (.storage []) := by
    simp [CoreCallableReturnStorageProducer.check,CoreCallableReturnStorageProducer.captureCheck,Code.dependencies]
  have integerLower : CallableContracts.Derives CoreCallableComposedResourceOrigins.Probes.Original.declarations
      (CoreCallableReturnStorageProducer.environment []) [0] .none (.integer 17) (.storage []) :=
    CoreCallableReturnStorageProducer.check_sound integerChecked
  have lowerClosed : CallableContracts.Derives CoreCallableComposedResourceOrigins.Probes.Original.declarations
      (CoreCallableReturnStorageProducer.environment []) [0] .none
      (Code.lambda 10 reader.closedBody) (selected.stored.value 0) :=
    CallableContracts.substitution lower integerLower outerClosed
  obtain ⟨_lexical,_same,integerAuth⟩ := CoreCallableOriginalResourceCurrent.Original.integerSupported.authentication
  have scalarAuth : Authenticated globals.registry []
      CoreCallableOriginalResourceCurrent.Original.integerSupported.source [] [0] := by
    apply integerAuth.lexical_congr
    intro name member
    exact False.elim (ScopedTyping.closedValue_no_variable outerClosed member)
  let family := first.changed CoreCallableComposedCapturedHandle.structural_policy_stable
    (show 7 ≠ 10 by decide) CoreCallableOriginalResourceCurrent.Original.integerSupported.source outerClosed
  have authentic := first.changed_authentic firstAuthentic
    CoreCallableComposedCapturedHandle.structural_policy_stable (show 7 ≠ 10 by decide)
    CoreCallableOriginalResourceCurrent.Original.integerSupported.source outerClosed scalarAuth
  have ordinaryClosed : LexicalBounds.Known [] (Code.lambda 10 reader.closedBody).dependencies := by
    intro name member
    change Syntax.Dependency.variable name ∈ [.resource 0,.resource 0] at member
    simp at member
  have bounds : ScopedPorts.Support.evaluate (LexicalBounds.environment [])
      (Code.lambda 10 reader.closedBody).dependencies ⊆ [0] := by
    intro identity member
    change identity ∈ [0,0] at member
    simpa using member
  have auth : Authenticated globals.registry [] (family.whole (allowed := [.cell 0]) (scope := .none)) [] [0] :=
    .checked (SourceSupport.bounds_iff.mpr bounds)
      (.receiverLambda family.bodyOutward family.latentBound family.publicCertified family.formed
        ordinaryClosed authentic.1 authentic.2)
  exact ⟨⟨first,replacement,firstReceipt,lower,lowerClosed,firstAuthentic,family,
    (fun lexical call => first.changed_plan _ _ _ _ lexical call),
    (fun lexical call => first.changed_rows _ _ _ _ lexical call),
    .changed first (.receiver first) (by decide),auth⟩⟩

private theorem tail_facets : ∃ certificate : SourceAdmission.Code [] (fun _ => none) []
    (OwnerPhaseTransitions.available []) [0] [] (tailChecking.rows 0)
    CoreCallableOriginalResourceCurrent.Original.cellContext,
    InstallationSupport.CodeChecked [] [] certificate ∧
    Accounting.Run [0] [] (tailChecking.rows 0) CoreCallableOriginalResourceCurrent.Original.cellContext
      CoreCallableOriginalResourceCurrent.Original.root := by
  let facets := CoreCallableCompositionalAdmissionFacets.fresh_facets
    (outward := []) (actions := fun _ => none) (budget := [])
    (phases := OwnerPhaseTransitions.available []) (world := []) (installations := []) (ambient := [])
    (checkingOf body) (binder := 3) (by rfl) 0
  have account : Accounting.Run [0] [] ((checkingOf body).rows 0)
      CoreCallableOriginalResourceCurrent.Original.cellContext CoreCallableOriginalResourceCurrent.Original.root := by
    simpa only [CoreCallableOriginalResourceCurrent.Original.root,
      CoreCallableOriginalResourceCurrent.Original.initializer_account,List.nil_append] using facets.accounting
  have afterHandle := (Accounting.silent_prefix_iff (firstDependencies := .pure) .pure
    Rows.pure (CoreCallableContractSource.sequenceRows (first := .pure) Rows.pure (tailChecking.rows 0))).mp account
  have afterReader := (Accounting.silent_prefix_iff (firstDependencies := .pure) .pure Rows.pure
    (tailChecking.rows 0)).mp afterHandle
  rcases facets with ⟨certificate,checked,_accounting⟩
  cases certificate with
  | sequence handleCertificate restCertificate =>
    cases checked with
    | sequence _handleChecked restChecked =>
      cases restCertificate with
      | sequence readerCertificate tailCertificate =>
        cases restChecked with
        | sequence _readerChecked tailChecked => exact ⟨tailCertificate,tailChecked,afterReader⟩

private theorem transport_tail_rows
    {first second : SourcePlanSignatures.Signature dependencies}
    {firstRows : Rows first} {secondRows : Rows second}
    (same : first = second) (sameRows : HEq firstRows secondRows)
    (certificate : SourceAdmission.Code [] (fun _ => none) [] (OwnerPhaseTransitions.available [])
      [0] [] secondRows CoreCallableOriginalResourceCurrent.Original.cellContext)
    (checked : InstallationSupport.CodeChecked [] [] certificate)
    (run : Accounting.Run [0] [] secondRows CoreCallableOriginalResourceCurrent.Original.cellContext
      CoreCallableOriginalResourceCurrent.Original.root) :
    ∃ nextCertificate : SourceAdmission.Code [] (fun _ => none) [] (OwnerPhaseTransitions.available [])
      [0] [] firstRows CoreCallableOriginalResourceCurrent.Original.cellContext,
      InstallationSupport.CodeChecked [] [] nextCertificate ∧ Accounting.Run [0] [] firstRows
        CoreCallableOriginalResourceCurrent.Original.cellContext CoreCallableOriginalResourceCurrent.Original.root := by
  subst second
  cases eq_of_heq sameRows
  exact ⟨certificate,checked,run⟩

theorem p12_code : closedTail.subst 12 reader.initializer = reader.p12.target.expression := rfl

/-- The reconstructed FULL reader family is the replacement consumed by
ordinary rich substitution, not an independent static conjunct. -/
theorem installed_site {opened : CoreCallableComposedResourceOrigins.Probes.Opened}
    {selected : CoreCallableComposedResourceOrigins.Probes.ReaderPath opened}
    {current : CoreCallableComposedResourceOrigins.Current selected.path 0 (by simp)}
    {handle : CoreCallableComposedCapturedHandle.CapturedHandle selected.path 0 (by simp)}
    (origin : ClosedReaderOrigin selected current handle) :
    ∃ site : Site globals [] [0] [.cell 0] (fun _ => none) (OwnerPhaseTransitions.available [])
      [] [] [] reader.p12.target.expression .none CoreCallableOriginalResourceCurrent.Original.cellStack
      .integer .integer CoreCallableOriginalResourceCurrent.Original.cellContext
      CoreCallableOriginalResourceCurrent.Original.root,
      HEq site.rows (tailChecking.rows 0) := by
  obtain ⟨tailPlan,tailRows,tailSource,tailAuth,tailSignature,tailAligned⟩ := tail_closed_source
  have tailEnvironment : LexicalBounds.environment [(12,[0])] =
      ScopedPorts.Support.extend ScopedPorts.Support.empty 12 [0] := by
    funext name
    by_cases same : name = 12 <;> simp [LexicalBounds.environment,LexicalBounds.lookup,ScopedPorts.Support.extend,ScopedPorts.Support.empty,same]
  let current : CoreCallableContractAdmission.Supported globals [] [0] [.cell 0] .none
      (Environment.empty.extend 12 readerContract) (ScopedPorts.Support.extend ScopedPorts.Support.empty 12 [0])
      closedTail .integer [] (tailNeeds.requirements 0) tailPlan tailRows [0] [0] :=
    ⟨tailSource,by rw [← tailEnvironment]; exact tailAuth.current_support,List.Subset.refl _,
      ⟨[(12,[0])],tailEnvironment,tailAuth⟩,List.Subset.refl _⟩
  let replacement : CoreCallableContractAdmission.Supported globals [] [0] [.cell 0] .none
      Environment.empty ScopedPorts.Support.empty reader.initializer readerContract [] (.request [] []) .pure Rows.pure [0] [0] :=
    ⟨origin.family.whole,by
      change SourceSupport.Bounds ScopedPorts.Support.empty (Code.lambda 10 reader.closedBody).dependencies [0]
      have empty : LexicalBounds.environment ([] : LexicalBounds) = ScopedPorts.Support.empty := rfl
      rw [← empty]
      exact origin.authenticated.current_support,
      List.Subset.refl _,
      ⟨[],rfl,origin.authenticated⟩,List.Subset.refl _⟩
  obtain ⟨plan,rows,supported,_computed,signature,aligned⟩ :=
    current.substitution replacement ComposedResourceRuntimeOriginProbes.checkedReader.closed
  obtain ⟨certificate,checked,accounting⟩ := tail_facets
  obtain ⟨nextCertificate,nextChecked,nextAccounting⟩ := transport_tail_rows
    (signature.trans tailSignature) (aligned.trans tailAligned) certificate checked accounting
  have evaluated : RecursiveRequirements.evaluate [] [] (OwnerPhaseTransitions.available [])
      (annotateDisposals CoreCallableOriginalResourceCurrent.Original.root) = some ([] : Footprint) := by
    have accountEq : CoreCallableCompositionalAdmissionFacets.rootAccount initializerAnnotation body =
        .choice .done .done := by decide +kernel
    simp [CoreCallableOriginalResourceCurrent.Original.root,accountEq,CoreCallableCompositionalAdmissionFacets.Account.requirements,
      annotateDisposals,RecursiveRequirements.evaluate,RecursiveRequirements.evaluateFuel,ProtectionResiduals.merge,
      OwnerSource.exportAt,ProtectionResiduals.residualize,OwnerPhaseTransitions.project]
  rw [p12_code] at supported
  let site : Site globals [] [0] [.cell 0] (fun _ => none) (OwnerPhaseTransitions.available []) [] [] []
      reader.p12.target.expression .none CoreCallableOriginalResourceCurrent.Original.cellStack
      .integer .integer CoreCallableOriginalResourceCurrent.Original.cellContext CoreCallableOriginalResourceCurrent.Original.root :=
    { sourceDemand := [],requirements := tailNeeds.requirements 0,dependencies := _,plan := plan,rows := rows,
      bound := [0],current := by simpa [actualReceiver,SourceDependencyCapture.Scope.visibleResources] using supported,
      received := by simp [SourceDependencyCapture.Scope.visibleResources],certificate := nextCertificate,
      certificateChecked := nextChecked,pending := .cell (by simp) rfl .nil,
      retained := .cell .nil,retainedChecked := .cell .nil,accounting := nextAccounting,
      annotated := _,annotation := .original,row := [],checked := RecursiveRequirements.evaluate_sound evaluated,
      bounded := List.Subset.refl _ }
  exact ⟨site,aligned.trans tailAligned⟩

structure Installed where
  program : CoreCallableInitialAdmission.Program globals (fun _ => none) [] rootCode
  programAccepted : CompositionalInitialAdmissionProbes.rootCheck = .ok program
  sameRoot : HEq program.root CoreCallableOriginalResourceCurrent.Original.root
  opened : CoreCallableComposedResourceOrigins.Probes.Opened
  openedAccepted : CoreCallableComposedResourceOrigins.produce_opened
    CoreCallableComposedResourceOrigins.Probes.originalPrefix
    CoreCallableComposedResourceOrigins.Probes.Original.annotation
    CoreCallableComposedResourceOrigins.Probes.Original.body
    CoreCallableComposedResourceOrigins.Probes.Original.initialRecipe
    CoreCallableComposedResourceOrigins.Probes.Original.bodyRecipe [] [] = .ok opened
  selected : CoreCallableComposedResourceOrigins.Probes.ReaderPath opened
  current : CoreCallableComposedResourceOrigins.Current selected.path 0 (by simp)
  currentAccepted : CoreCallableComposedResourceOrigins.produce_current selected.path 0 (by simp) = some (PLift.up current)
  handle : CoreCallableComposedCapturedHandle.CapturedHandle selected.path 0 (by simp)
  handleAccepted : CoreCallableComposedCapturedHandle.capture_handle selected.path 0 (by simp) = .ok (PLift.up handle)
  origin : ClosedReaderOrigin selected current handle
  site : Site globals [] [0] [.cell 0] (fun _ => none) (OwnerPhaseTransitions.available [])
    [] [] [] reader.p12.target.expression .none CoreCallableOriginalResourceCurrent.Original.cellStack
    .integer .integer CoreCallableOriginalResourceCurrent.Original.cellContext CoreCallableOriginalResourceCurrent.Original.root
  exactRows : HEq site.rows (tailChecking.rows 0)
  actual : CoreAllocationHistory.Steps graph 12 (CoreMachine.initial graph) reader.s12
  chain : CoreInitialPrefix.Chain graph CoreCallableOriginalResourceCurrent.Original.selection.p0
    [CoreCallableOriginalResourceCurrent.Original.selection.p1,CoreCallableOriginalResourceCurrent.Original.selection.p2,
     CoreCallableOriginalResourceCurrent.Original.selection.p3,CoreCallableOriginalResourceCurrent.Original.selection.p4,
     CoreCallableOriginalResourceCurrent.Original.selection.p5,CoreCallableOriginalResourceCurrent.Original.selection.p6,
     CoreCallableOriginalResourceCurrent.Original.selection.p7,CoreCallableOriginalResourceCurrent.Original.selection.p8,
     CoreCallableOriginalResourceCurrent.Original.selection.p9,reader.p10,reader.p11,reader.p12] reader.p12
  related : CoreCallableRichBetaCore.Current (CoreCallableComposedRuntimeCurrent.current reader) site

/-- Execute the original Program and retained original Body/Recipe selectors,
then close the full reader family and derive the actual CURRENT Site. -/
theorem installed_current : Nonempty Installed := by
  obtain ⟨program,accepted,_plan,_rows,_req,sameRoot,_budget⟩ := CoreCallableOriginalResourceCurrent.Original.original_program
  obtain ⟨opened,openedAccepted⟩ := CoreCallableComposedResourceOrigins.Probes.resource_executed
  obtain ⟨selected,_⟩ := CoreCallableComposedResourceOrigins.Probes.connected_reader opened
  obtain ⟨current,currentAccepted⟩ := CoreCallableComposedResourceOrigins.Probes.reader_current_all_fresh selected 0
  obtain ⟨handle,handleAccepted⟩ := ComposedResourceRuntimeOriginProbes.handle_at_computed_owner selected
  obtain ⟨origin⟩ := closed_reader_origin selected current.down handle.down
  obtain ⟨site,exactRows⟩ := installed_site origin
  exact ⟨⟨program,accepted,sameRoot,opened,openedAccepted,selected,current.down,currentAccepted,
    handle.down,handleAccepted,origin,site,exactRows,
    ComposedResourceRuntimeOriginProbes.initial_to_reader,
    CoreCallableComposedRuntimeBindings.installed_chain CoreCallableOriginalResourceCurrent.Original.selection reader
      ComposedResourceRuntimeOriginProbes.initialInput ComposedResourceRuntimeOriginProbes.checkedReader,
    ⟨rfl⟩⟩⟩

#print axioms tail_derived
#print axioms tail_authenticated
#print axioms handle_checked
#print axioms tail_closed_source
#print axioms closed_reader_origin
#print axioms installed_site
#print axioms installed_current
end Original
end Ash.OneShot.CoreCallableOriginalCallableCurrent
