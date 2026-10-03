import CoreCallableOriginalCallableCurrent
import CoreCallableComposedRuntimeCalls
namespace Ash.OneShot.CoreCallableOriginalHigherCurrent
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract Environment)
open CoreCallableContractAdmission CoreCallableReceiverRefinement CoreCallableContractExecution
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceScheduledCleanupInterfaces.Lexical.Recursive
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open CoreCallableCapturedLambdaConstructor (Family Origin)
local instance : SourcePlannedChecks.DeclarationPolicy := declarationPolicy
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
namespace Original
open CoreCallableOriginalCallableCurrent.Original
abbrev runtime := CoreCallableComposedRuntimeCalls.Original.selectedHigher
abbrev higherContract := CoreCallableCompositionalResourceRoot.higherPattern.value [(7,.integer)] 0
abbrev higherInput := readerContract
abbrev higherOutput := Contract.integer
abbrev higherRequests : List Instance := [.cell 0]
abbrev higherLatent := (CoreCallableCompositionalResourceRoot.needsOf CoreCallableCompositionalResourceRoot.applyFormal).summary.map
  (CoreCallableCompositionalResourceBody.RequestName.value 0)
abbrev higherChecking := CoreCallableCompositionalResourceRoot.checkingOf CoreCallableCompositionalResourceRoot.applyFormal
abbrev higherPlan := higherChecking.plan 0
abbrev higherRows := higherChecking.rows 0
abbrev higherCode := CoreCallableCompositionalResourceRoot.codeOf CoreCallableCompositionalResourceRoot.higherOrder
abbrev baseEnvironment := (Environment.empty.extend 7 .integer).extend 9 (.reference 0)
abbrev HigherFamily := Family globals.registry [] globals.owners [0] Environment.empty 11 runtime.closedBody
  higherInput higherOutput higherRequests higherLatent higherPlan higherRows

structure ClosedHigherOrigin (installed : Installed)
    (path : CoreCallableComposedResourceOrigins.Probes.HigherPath installed.opened)
    (receipt : CoreCallableComposedResourceOrigins.Current path.path 0 (by simp)) where
  original : Family globals.registry [] globals.owners [0] (baseEnvironment.extend 12 readerContract)
    11 runtime.closedBody higherInput higherOutput higherRequests higherLatent higherPlan higherRows
  originalOrigin : Origin receipt.source original
  originalAuthentic : original.Authentic
  readerRemoved : Family globals.registry [] globals.owners [0] baseEnvironment
    11 runtime.closedBody higherInput higherOutput higherRequests higherLatent higherPlan higherRows
  readerReceipt : CoreCallableCapturedLambdaConstructor.Receipt receipt.source
    (IndexedSource.closed_environment (installed.origin.family.whole (allowed := [.cell 0]) (scope := .none))
      ComposedResourceRuntimeOriginProbes.checkedReader.closed baseEnvironment)
    CoreCallableComposedCapturedHandle.structural_policy_stable
    ComposedResourceRuntimeOriginProbes.checkedReader.closed runtime.closedBody readerRemoved
  readerPointPlans : ∀ lexical call, HEq (readerRemoved.plans lexical call)
    (CoreCallablePlanSubstitution.plan runtime.closedBody
      (original.plans (CoreCallableCapturedLambdaConstructor.restored lexical 12 reader.initializer) call) 12 reader.initializer)
  readerPointRows : ∀ lexical call, HEq (readerRemoved.rows lexical call)
    (original.rows (CoreCallableCapturedLambdaConstructor.restored lexical 12 reader.initializer) call)
  handleReplacement : Source globals [] [0] [.cell 0] .none (Environment.empty.extend 7 .integer)
    handleValue (.reference 0) [] (.request [] []) .pure Rows.pure
  handleRemoved : Family globals.registry [] globals.owners [0] (Environment.empty.extend 7 .integer)
    11 runtime.closedBody higherInput higherOutput higherRequests higherLatent higherPlan higherRows
  handleReceipt : CoreCallableCapturedLambdaConstructor.Receipt
    (readerRemoved.whole (allowed := [.cell 0]) (scope := .none)) handleReplacement
    CoreCallableComposedCapturedHandle.structural_policy_stable installed.handle.closed runtime.closedBody handleRemoved
  handlePointPlans : ∀ lexical call, HEq (handleRemoved.plans lexical call)
    (CoreCallablePlanSubstitution.plan runtime.closedBody
      (readerRemoved.plans (CoreCallableCapturedLambdaConstructor.restored lexical 9 handleValue) call) 9 handleValue)
  handlePointRows : ∀ lexical call, HEq (handleRemoved.rows lexical call)
    (readerRemoved.rows (CoreCallableCapturedLambdaConstructor.restored lexical 9 handleValue) call)
  family : HigherFamily
  outerReceipt : CoreCallableCapturedLambdaConstructor.Receipt
    (handleRemoved.whole (allowed := [.cell 0]) (scope := .none)) CoreCallableOriginalResourceCurrent.Original.integerSupported.source
    CoreCallableComposedCapturedHandle.structural_policy_stable outerClosed runtime.closedBody family
  outerPointPlans : ∀ lexical call, HEq (family.plans lexical call)
    (CoreCallablePlanSubstitution.plan runtime.closedBody
      (handleRemoved.plans (CoreCallableCapturedLambdaConstructor.restored lexical 7 (.integer 17)) call) 7 (.integer 17))
  outerPointRows : ∀ lexical call, HEq (family.rows lexical call)
    (handleRemoved.rows (CoreCallableCapturedLambdaConstructor.restored lexical 7 (.integer 17)) call)
  authentic : family.Authentic
  authenticated : Authenticated globals.registry [] (family.whole (allowed := [.cell 0]) (scope := .none)) [] [0]

/-- This join checks the exact existing current constructor indices in the kernel. -/
theorem close_higher (installed : Installed)
    (path : CoreCallableComposedResourceOrigins.Probes.HigherPath installed.opened)
    (receipt : CoreCallableComposedResourceOrigins.Current path.path 0 (by simp)) :
    Nonempty (ClosedHigherOrigin installed path receipt) := by
  obtain ⟨original,originalOrigin,originalAuthentic,_known⟩ := CoreCallableCapturedLambdaConstructor.extract receipt.authenticated
  let readerReplacement := IndexedSource.closed_environment (installed.origin.family.whole (allowed := [.cell 0]) (scope := .none))
    ComposedResourceRuntimeOriginProbes.checkedReader.closed baseEnvironment
  have readerAuth : Authenticated globals.registry [] readerReplacement [(9,[0]),(7,[])] [0] := by
    apply (installed.origin.authenticated.closed_environment ComposedResourceRuntimeOriginProbes.checkedReader.closed baseEnvironment).lexical_congr
    intro name member
    exact False.elim (ScopedTyping.closedValue_no_variable ComposedResourceRuntimeOriginProbes.checkedReader.closed member)
  let readerRemoved := original.changed CoreCallableComposedCapturedHandle.structural_policy_stable
    (show 12 ≠ 11 by decide) readerReplacement ComposedResourceRuntimeOriginProbes.checkedReader.closed
  have readerAuthentic := original.changed_authentic originalAuthentic
    CoreCallableComposedCapturedHandle.structural_policy_stable (show 12 ≠ 11 by decide)
    readerReplacement ComposedResourceRuntimeOriginProbes.checkedReader.closed readerAuth
  obtain ⟨handleSource,_tree,handleAuth,_⟩ := installed.handle.rechecked
  let handleRemoved := readerRemoved.changed CoreCallableComposedCapturedHandle.structural_policy_stable
    (show 9 ≠ 11 by decide) handleSource installed.handle.closed
  have handleAuthentic := readerRemoved.changed_authentic readerAuthentic
    CoreCallableComposedCapturedHandle.structural_policy_stable (show 9 ≠ 11 by decide)
    handleSource installed.handle.closed handleAuth
  obtain ⟨_lexical,_same,integerAuth⟩ := CoreCallableOriginalResourceCurrent.Original.integerSupported.authentication
  have scalarAuth : Authenticated globals.registry [] CoreCallableOriginalResourceCurrent.Original.integerSupported.source [] [0] := by
    apply integerAuth.lexical_congr
    intro name member
    exact False.elim (ScopedTyping.closedValue_no_variable outerClosed member)
  let family := handleRemoved.changed CoreCallableComposedCapturedHandle.structural_policy_stable
    (show 7 ≠ 11 by decide) CoreCallableOriginalResourceCurrent.Original.integerSupported.source outerClosed
  have authentic := handleRemoved.changed_authentic handleAuthentic
    CoreCallableComposedCapturedHandle.structural_policy_stable (show 7 ≠ 11 by decide)
    CoreCallableOriginalResourceCurrent.Original.integerSupported.source outerClosed scalarAuth
  have known : LexicalBounds.Known [] (Code.lambda 11 runtime.closedBody).dependencies := by
    intro name member
    change Syntax.Dependency.variable name ∈ [] at member
    simp at member
  have bounds : SourceSupport.Bounds (LexicalBounds.environment []) (Code.lambda 11 runtime.closedBody).dependencies [0] := by
    apply SourceSupport.bounds_iff.mpr
    change ([] : List Nat) ⊆ [0]
    simp
  have auth : Authenticated globals.registry [] (family.whole (allowed := [.cell 0]) (scope := .none)) [] [0] :=
    .checked bounds (.receiverLambda family.bodyOutward family.latentBound family.publicCertified family.formed known authentic.1 authentic.2)
  exact ⟨⟨original,originalOrigin,originalAuthentic,readerRemoved,
    .changed original originalOrigin (by decide),
    (fun lexical call => original.changed_plan _ _ _ _ lexical call),
    (fun lexical call => original.changed_rows _ _ _ _ lexical call),handleSource,handleRemoved,
    .changed readerRemoved (.receiver readerRemoved) (by decide),
    (fun lexical call => readerRemoved.changed_plan _ _ _ _ lexical call),
    (fun lexical call => readerRemoved.changed_rows _ _ _ _ lexical call),family,
    .changed handleRemoved (.receiver handleRemoved) (by decide),
    (fun lexical call => handleRemoved.changed_plan _ _ _ _ lexical call),
    (fun lexical call => handleRemoved.changed_rows _ _ _ _ lexical call),authentic,auth⟩⟩

abbrev applicationPlan := Plan.sequence Plan.pure (Plan.sequence Plan.pure higherPlan)
abbrev applicationRows : Rows (signature applicationPlan) := CoreCallableContractSource.sequenceRows Rows.pure
  (CoreCallableContractSource.sequenceRows Rows.pure higherRows)
abbrev branchPlan := Plan.sequence Plan.pure (Plan.choice Plan.pure Plan.pure)
abbrev branchRows : Rows (signature branchPlan) := CoreCallableContractSource.sequenceRows Rows.pure
  (CoreCallableContractSource.choiceRows Rows.pure Rows.pure)
abbrev applicationRequirements : RecursiveRequirements.Requirements ([] ++ []) :=
  .emitAfter (.sequence (.request [] []) (.request [] [])) [] higherLatent
abbrev branchRequirements : RecursiveRequirements.Requirements ([] ++ []) :=
  .sequence (.request [] []) (.choice (.request [] []) (.request [] []) (by rfl))
abbrev suffixPlan := Plan.sequence applicationPlan branchPlan
abbrev suffixRows : Rows (signature suffixPlan) := CoreCallableContractSource.sequenceRows applicationRows branchRows
abbrev suffixRequirements := RecursiveRequirements.Requirements.sequence applicationRequirements branchRequirements

abbrev applicationSource (installed : Installed) (family : HigherFamily) :
    Source globals [] [0] [.cell 0] .none Environment.empty
      (.app runtime.initializer reader.initializer) .integer ([] ++ []) applicationRequirements applicationPlan applicationRows :=
  .app family.whole installed.origin.family.whole (List.Subset.refl _) family.publicCertified

abbrev branchSource : Source globals [] [0] [.cell 0] .none (Environment.empty.extend 5 .integer)
    CoreCallableComposedRuntimeCalls.Original.branchCode .integer ([] ++ []) branchRequirements branchPlan branchRows :=
  .branch .boolean .integer .integer (by rfl)

abbrev suffixSource (installed : Installed) (family : HigherFamily) :
    Source globals [] [0] [.cell 0] .none Environment.empty
      (.bind 5 (.app runtime.initializer reader.initializer) CoreCallableComposedRuntimeCalls.Original.branchCode)
      .integer (([] ++ []) ++ ([] ++ [])) suffixRequirements suffixPlan suffixRows :=
  .bind (applicationSource installed family) branchSource

theorem application_authenticated (installed : Installed)
    {path : CoreCallableComposedResourceOrigins.Probes.HigherPath installed.opened}
    {receipt : CoreCallableComposedResourceOrigins.Current path.path 0 (by simp)}
    (origin : ClosedHigherOrigin installed path receipt) :
    Authenticated globals.registry [] (applicationSource installed origin.family) [] [0] := by
  unfold applicationSource
  refine .checked ?_ (Hereditary.app (admitted := List.Subset.refl _) (publicCertified := origin.family.publicCertified) origin.authenticated installed.origin.authenticated)
  apply SourceSupport.bounds_iff.mpr
  change [0,0] ⊆ [0]
  simp

theorem suffix_authenticated (installed : Installed)
    {path : CoreCallableComposedResourceOrigins.Probes.HigherPath installed.opened}
    {receipt : CoreCallableComposedResourceOrigins.Current path.path 0 (by simp)}
    (origin : ClosedHigherOrigin installed path receipt) :
    Authenticated globals.registry [] (suffixSource installed origin.family) [] [0] := by
  unfold suffixSource
  refine .checked ?_ (Hereditary.bind (bodySource := branchSource) (application_authenticated installed origin) ?_)
  · apply SourceSupport.bounds_iff.mpr
    change [0,0] ⊆ [0]
    simp
  · exact .checked .nil (.branch (.checked .nil .boolean) (.checked .nil .integer) (.checked .nil .integer))

/-- The checked original resource body supplies these exact suffix rows. Three
value initializers have silent immediate rows; private callable rows stay full. -/
theorem suffix_facets : ∃ certificate : SourceAdmission.Code [] (fun _ => none) []
    (OwnerPhaseTransitions.available []) [0] [] suffixRows
    CoreCallableOriginalResourceCurrent.Original.cellContext,
    InstallationSupport.CodeChecked [] [] certificate ∧ Accounting.Run [0] [] suffixRows
      CoreCallableOriginalResourceCurrent.Original.cellContext CoreCallableOriginalResourceCurrent.Original.root := by
  let facets := CoreCallableCompositionalAdmissionFacets.fresh_facets
    (outward := []) (actions := fun _ => none) (budget := [])
    (phases := OwnerPhaseTransitions.available []) (world := []) (installations := []) (ambient := [])
    (CoreCallableCompositionalResourceRoot.checkingOf CoreCallableCompositionalResourceRoot.body) (binder := 3) (by rfl) 0
  have account : Accounting.Run [0] []
      ((CoreCallableCompositionalResourceRoot.checkingOf CoreCallableCompositionalResourceRoot.body).rows 0)
      CoreCallableOriginalResourceCurrent.Original.cellContext CoreCallableOriginalResourceCurrent.Original.root := by
    simpa only [CoreCallableOriginalResourceCurrent.Original.root,
      CoreCallableOriginalResourceCurrent.Original.initializer_account,List.nil_append] using facets.accounting
  have afterHandle := (Accounting.silent_prefix_iff (firstDependencies := .pure) .pure Rows.pure
    (CoreCallableContractSource.sequenceRows (first := Plan.pure) Rows.pure (CoreCallableContractSource.sequenceRows (first := Plan.pure) Rows.pure suffixRows))).mp account
  have afterReader := (Accounting.silent_prefix_iff (firstDependencies := .pure) .pure Rows.pure
    (CoreCallableContractSource.sequenceRows (first := Plan.pure) Rows.pure suffixRows)).mp afterHandle
  have afterHigher := (Accounting.silent_prefix_iff (firstDependencies := .pure) .pure Rows.pure suffixRows).mp afterReader
  rcases facets with ⟨certificate,checked,_accounting⟩
  cases certificate with
  | sequence _ rest =>
    cases checked with
    | sequence _ restChecked =>
      cases rest with
      | sequence _ rest =>
        cases restChecked with
        | sequence _ restChecked =>
          cases rest with
          | sequence _ suffix =>
            cases restChecked with
            | sequence _ suffixChecked => exact ⟨suffix,suffixChecked,afterHigher⟩

structure HigherInstalled where
  installed : Installed
  path : CoreCallableComposedResourceOrigins.Probes.HigherPath installed.opened
  receipt : CoreCallableComposedResourceOrigins.Current path.path 0 (by simp)
  currentAccepted : CoreCallableComposedResourceOrigins.produce_current path.path 0 (by simp) = some (PLift.up receipt)
  checked : CoreCallableComposedRuntimeCalls.CheckedHigher runtime
  higherAccepted : CoreCallableComposedRuntimeCalls.produce_higher runtime = .ok checked
  origin : ClosedHigherOrigin installed path receipt
  site : Site globals [] [0] [.cell 0] (fun _ => none) (OwnerPhaseTransitions.available [])
    [] [] [] runtime.p15.target.expression .none CoreCallableOriginalResourceCurrent.Original.cellStack
    .integer .integer CoreCallableOriginalResourceCurrent.Original.cellContext CoreCallableOriginalResourceCurrent.Original.root
  sameSource : HEq site.current.source (suffixSource installed origin.family)
  certificate : SourceAdmission.Code [] (fun _ => none) [] (OwnerPhaseTransitions.available []) [0] [] suffixRows
    CoreCallableOriginalResourceCurrent.Original.cellContext
  certificateChecked : InstallationSupport.CodeChecked [] [] certificate
  accounting : Accounting.Run [0] [] suffixRows CoreCallableOriginalResourceCurrent.Original.cellContext CoreCallableOriginalResourceCurrent.Original.root
  actual : CoreAllocationHistory.Steps CoreCallableCompositionalResourceRoot.graph 15
    (CoreMachine.initial CoreCallableCompositionalResourceRoot.graph) runtime.s15
  related : CoreCallableRichBetaCore.Current CoreCallableComposedRuntimeCalls.Original.e15 site

private theorem link_step {graph : CoreSyntax.Graph} (link : CoreInitialPrefix.Link graph before after) :
    CoreMachine.Step graph before.state after.state := by
  cases link with
  | positive _ core _ _ => exact core
  | traversal witness => exact witness.core
  | value witness => exact witness.core

private theorem chain_steps {graph : CoreSyntax.Graph} (chain : CoreInitialPrefix.Chain graph before points after) :
    CoreAllocationHistory.Steps graph points.length before.state after.state := by
  induction chain with
  | last link => exact .snoc (.refl _) (link_step link)
  | next link rest ih =>
    simpa [Nat.add_comm] using (CoreAllocationHistory.Steps.snoc (.refl _) (link_step link)).trans ih

theorem higher_installed_current : Nonempty HigherInstalled := by
  obtain ⟨installed⟩ := installed_current
  obtain ⟨path,_⟩ := CoreCallableComposedResourceOrigins.Probes.connected_higher installed.opened
  obtain ⟨receipt,accepted⟩ := CoreCallableComposedResourceOrigins.Probes.higher_current_all_fresh path 0
  obtain ⟨checked,higherAccepted⟩ := CoreCallableComposedRuntimeCalls.Original.higher_executed
  obtain ⟨origin⟩ := close_higher installed path receipt.down
  obtain ⟨certificate,certificateChecked,accounting⟩ := suffix_facets
  have auth := suffix_authenticated installed origin
  have evaluated : RecursiveRequirements.evaluate [] [] (OwnerPhaseTransitions.available [])
      (annotateDisposals CoreCallableOriginalResourceCurrent.Original.root) = some ([] : Footprint) := by
    have accountEq : CoreCallableCompositionalAdmissionFacets.rootAccount
        CoreCallableCompositionalResourceRoot.initializerAnnotation CoreCallableCompositionalResourceRoot.body =
        .choice .done .done := by decide +kernel
    simp [CoreCallableOriginalResourceCurrent.Original.root,accountEq,
      CoreCallableCompositionalAdmissionFacets.Account.requirements,annotateDisposals,
      RecursiveRequirements.evaluate,RecursiveRequirements.evaluateFuel,ProtectionResiduals.merge,
      OwnerSource.exportAt,ProtectionResiduals.residualize,OwnerPhaseTransitions.project]
  let site : Site globals [] [0] [.cell 0] (fun _ => none) (OwnerPhaseTransitions.available [])
      [] [] [] runtime.p15.target.expression .none CoreCallableOriginalResourceCurrent.Original.cellStack
      .integer .integer CoreCallableOriginalResourceCurrent.Original.cellContext CoreCallableOriginalResourceCurrent.Original.root :=
    { sourceDemand := _, requirements := suffixRequirements, dependencies := _, plan := suffixPlan, rows := suffixRows,
      bound := [0], current := ⟨suffixSource installed origin.family, by exact auth.current_support,
        by simp, ⟨[],rfl,auth⟩,by simp [actualReceiver,SourceDependencyCapture.Scope.visibleResources]⟩,
      received := by simp [SourceDependencyCapture.Scope.visibleResources], certificate := certificate,
      certificateChecked := certificateChecked, pending := .cell (by simp) rfl .nil,
      retained := .cell .nil, retainedChecked := .cell .nil, accounting := accounting,
      annotated := _, row := [], annotation := .original,checked := RecursiveRequirements.evaluate_sound evaluated,bounded := List.Subset.refl _ }
  exact ⟨⟨installed,path,receipt.down,accepted,checked,higherAccepted,origin,site,HEq.rfl,certificate,certificateChecked,accounting,
    installed.actual.trans (chain_steps
      (CoreCallableComposedRuntimeCalls.higher_chain runtime ComposedResourceRuntimeOriginProbes.initialInput
        ComposedResourceRuntimeOriginProbes.checkedReader checked).1),⟨rfl⟩⟩⟩

#print axioms higher_installed_current
#print axioms close_higher
#print axioms application_authenticated
#print axioms suffix_authenticated
#print axioms suffix_facets
end Original
end Ash.OneShot.CoreCallableOriginalHigherCurrent
