import CoreCallableOriginalHigherCurrent
import CoreCallableRichBetaCore
namespace Ash.OneShot.CoreCallableOriginalBetaCurrent
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract Environment)
open CoreCallableContractAdmission CoreCallableReceiverRefinement CoreCallableContractExecution
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceScheduledCleanupInterfaces.Lexical.Recursive
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open CoreCallableCapturedLambdaConstructor (Family Origin)
open CoreCallableRichBetaPreservation (Selected actualCall)
local instance : SourcePlannedChecks.DeclarationPolicy := declarationPolicy
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
namespace Original
open CoreCallableOriginalCallableCurrent.Original
open CoreCallableOriginalHigherCurrent.Original
open CoreCallableComposedRuntimeCalls.Original

theorem saved_stack : e16.lexical = .push (.plain bindReady.plain) CoreCallableOriginalResourceCurrent.Original.cellStack := rfl
theorem admin_machine : e20.point.machine = e16.point.machine := rfl
abbrev callerContext := Context.plain branchRows CoreCallableOriginalResourceCurrent.Original.cellContext
abbrev appCode := Code.app runtime.initializer reader.initializer
abbrev AppSite := Site globals [] [0] [.cell 0] (fun _ => none) (OwnerPhaseTransitions.available [])
  [] [] [] appCode .none e16.lexical .integer .integer callerContext CoreCallableOriginalResourceCurrent.Original.root

structure Focused (higher : HigherInstalled) where
  site : AppSite
  sameSource : HEq site.current.source (applicationSource higher.installed higher.origin.family)
  certificate : SourceAdmission.Code [] (fun _ => none) [] (OwnerPhaseTransitions.available []) [0] [] applicationRows callerContext
  certificateChecked : InstallationSupport.CodeChecked [] [] certificate
  accounting : Accounting.Run [0] [] applicationRows callerContext CoreCallableOriginalResourceCurrent.Original.root
  related : CoreCallableRichBetaCore.Current e16 site
  adminRelated : CoreCallableRichBetaCore.Current e20 site
  raw : RawStep ⟨runtime.p15.target.expression,.none,CoreCallableOriginalResourceCurrent.Original.cellStack⟩
    ⟨appCode,.none,e16.lexical⟩ [] []

/-- Focus the executed original bind5 using the exact CURRENT components.
The frame saves the original branch rows and current caller cell boundary. -/
theorem focus_current (higher : HigherInstalled) : Nonempty (Focused higher) := by
  have split : FocusRows suffixRows applicationRows branchRows := .sequence
  obtain ⟨certificate,restCertificate⟩ := split.source_certificate higher.certificate
  obtain ⟨checked,restChecked⟩ := InstallationSupport.focus_rows split higher.certificateChecked
  have bodyAuth : Authenticated globals.registry [] branchSource (LexicalBounds.extend [] 5 [0]) [0] :=
    .checked .nil (.branch (.checked .nil .boolean) (.checked .nil .integer) (.checked .nil .integer))
  let frame : FrameSource globals [] [0] [.cell 0] bindReady.plain .integer .integer 5 branchCode
      ([] ++ []) branchRequirements branchPlan branchRows [0] [0] [0] :=
    ⟨rfl,rfl,rfl,by simp,⟨branchSource,.nil,by simp,⟨(LexicalBounds.extend [] 5 [0]),by simp only [LexicalBounds.environment_extend]; rfl,bodyAuth⟩,by simp⟩⟩
  have auth := application_authenticated higher.installed higher.origin
  let site : AppSite :=
    { sourceDemand := _, requirements := applicationRequirements, dependencies := _,plan := applicationPlan,rows := applicationRows,
      bound := [0],current := ⟨applicationSource higher.installed higher.origin.family,auth.current_support,by simp,
        ⟨[],rfl,auth⟩,by simp [actualReceiver,SourceDependencyCapture.Scope.visibleResources]⟩,
      received := by simp [SourceDependencyCapture.Scope.visibleResources],certificate := certificate,certificateChecked := checked,
      pending := by
        rw [saved_stack]
        exact .plain frame (by simp [SourceDependencyCapture.Scope.visibleResources])
          (by intro identity historical _; simpa using historical) higher.site.pending,
      retained := .plain (restCertificate.reindex_context CoreCallableOriginalResourceCurrent.Original.cellContext.append_nil_pack.symm) higher.site.retained,
      retainedChecked := .plain (restChecked.reindex_context CoreCallableOriginalResourceCurrent.Original.cellContext.append_nil_pack.symm) higher.site.retainedChecked,
      accounting := higher.accounting.focus_rows split,annotated := higher.site.annotated,row := higher.site.row,
      annotation := higher.site.annotation,checked := higher.site.checked,bounded := higher.site.bounded }
  have raw : RawStep ⟨runtime.p15.target.expression,.none,CoreCallableOriginalResourceCurrent.Original.cellStack⟩
      ⟨appCode,.none,e16.lexical⟩ [] [] := by
    rw [saved_stack]
    exact .focus bindReady.plain (.bind bindReady.notValue) _
  exact ⟨⟨site,HEq.rfl,certificate,checked,higher.accounting.focus_rows split,⟨by simp only [CoreCallableGeneratedChronology.Endpoint.point,e16_focus,CoreCleanupRunFrames.attach,Stack.append]⟩,⟨by rw [admin_machine]; simp only [CoreCallableGeneratedChronology.Endpoint.point,e16_focus,CoreCleanupRunFrames.attach,Stack.append]⟩,raw⟩⟩

abbrev readerSupported (higher : HigherInstalled) : CoreCallableContractAdmission.Supported globals [] [0] [.cell 0] .none
    Environment.empty ScopedPorts.Support.empty reader.initializer readerContract [] (.request [] []) .pure Rows.pure [0] [0] :=
  ⟨higher.installed.origin.family.whole,higher.installed.origin.authenticated.current_support,
    by simp,⟨[],rfl,higher.installed.origin.authenticated⟩,by simp⟩
abbrev originalCall (higher : HigherInstalled) :=
  actualCall [0] [0] reader.initializer (by simp) (readerSupported higher).actual_received

/-- Choose the already-produced original Family at the actual argument support.
No successful successor, desired family, or private point is supplied as input. -/
theorem select_original (higher : HigherInstalled) :
    ∃ selected : Selected (higher.origin.family.whole (allowed := [.cell 0]) (scope := .none))
      [] (originalCall higher) reader.initializer,
      selected.family = higher.origin.family := by
  let family := higher.origin.family
  let call := originalCall higher
  have known : LexicalBounds.Known [] (Code.lambda 11 runtime.closedBody).dependencies := by
    intro name member
    change Syntax.Dependency.variable name ∈ [] at member
    simp at member
  have functionReceived : ScopedPorts.Support.evaluate (LexicalBounds.environment [])
      (Code.lambda 11 runtime.closedBody).dependencies ⊆ call.receiver := by
    change ([] : List Nat) ⊆ [0]
    simp
  have bodyAuth := higher.origin.authentic.1 [] call known functionReceived
  have refinement := higher.origin.authentic.2 [] call known functionReceived
  let replacementSource := IndexedSource.value_allowed
    (IndexedSource.value_summary (readerSupported higher).source ComposedResourceRuntimeOriginProbes.checkedReader.closed.1)
    ComposedResourceRuntimeOriginProbes.checkedReader.closed.1 higherRequests .none
  have replacementAuth : Authenticated globals.registry [] replacementSource [] [0] := by
    exact ((higher.installed.origin.authenticated.value_summary ComposedResourceRuntimeOriginProbes.checkedReader.closed.1).value_allowed
      ComposedResourceRuntimeOriginProbes.checkedReader.closed.1 higherRequests .none)
  let replacement : CoreCallableContractAdmission.Supported globals [] [0] higherRequests .none Environment.empty ScopedPorts.Support.empty
      reader.initializer readerContract [] (.request [] []) .pure Rows.pure call.argument [0] :=
    ⟨replacementSource,SourceSupport.Bounds.canonical _ _,
      call.argumentReceived.trans call.receivingIssued,⟨[],rfl,replacementAuth⟩,call.receivingIssued⟩
  let bodySupported : CoreCallableContractAdmission.Supported globals [] [0] higherRequests .none (Environment.empty.extend 11 readerContract)
      (ScopedPorts.Support.extend ScopedPorts.Support.empty 11 call.argument) runtime.closedBody .integer
      family.demand family.requirements (family.plans [] call) (family.rows [] call) [0] [0] :=
    ⟨family.body [] call,by simpa only [LexicalBounds.environment_extend, show LexicalBounds.environment [] = ScopedPorts.Support.empty from rfl,call,originalCall,actualCall] using bodyAuth.current_support,
      by simp,⟨LexicalBounds.extend [] 11 call.argument,by simp only [LexicalBounds.environment_extend]; rfl,bodyAuth⟩,by simp⟩
  obtain ⟨nextPlan,nextRows,current,exactPlan,sameSignature,sameRows⟩ :=
    bodySupported.substitution_reannotated CoreCallableComposedCapturedHandle.structural_policy_stable
      replacement ComposedResourceRuntimeOriginProbes.checkedReader.closed
  exact ⟨⟨family,.receiver family,higher.origin.authentic,known,refinement,
    nextPlan,nextRows,current,exactPlan,sameSignature,sameRows⟩,rfl⟩

private theorem transport_beta_rows
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
  exact ⟨certificate,checked,run⟩

structure FirstBeta (higher : HigherInstalled) (focused : Focused higher) where
  selected : Selected (higher.origin.family.whole (allowed := [.cell 0]) (scope := .none))
    [] (originalCall higher) reader.initializer
  chosen : selected.family = higher.origin.family
  nextRoot : RecursiveRequirements.Requirements []
  rootTransport : CoreCallableRootRefinement.RootTransport CoreCallableOriginalResourceCurrent.Original.root nextRoot
  next : Site globals [] [0] [.cell 0] (fun _ => none) (OwnerPhaseTransitions.available []) [] [] []
    (runtime.closedBody.subst 11 reader.initializer) .none e21.lexical .integer .integer callerContext nextRoot
  exactDemand : next.sourceDemand = selected.family.demand
  exactRequirements : HEq next.requirements selected.family.requirements
  exactPlan : HEq next.plan selected.nextPlan
  exactRows : HEq next.rows selected.nextRows
  related : CoreCallableRichBetaCore.Current e21 next
  actual : CoreMachine.next G e20.state = .stepped e21.state
  matching : CoreCallableGeneratedChronology.Matching G e20 e21 [] []
  raw : RawStep ⟨appCode,.none,e20.lexical⟩
    ⟨runtime.closedBody.subst 11 reader.initializer,.none,e21.lexical⟩ [] []
  callee : e21.state.control = .evaluate 9 higherBodyEnvironment
  history : e21.history = e20.history

/-- CURRENT component authority constructs the exact chosen private successor,
refinement, checked rows and root accounting before actual Core beta is joined. -/
theorem beta_current (higher : HigherInstalled) (focused : Focused higher) :
    Nonempty (FirstBeta higher focused) := by
  obtain ⟨selected,chosen⟩ := select_original higher
  have known := selected.known
  have functionReceived : ScopedPorts.Support.evaluate (LexicalBounds.environment [])
      (Code.lambda 11 runtime.closedBody).dependencies ⊆ (originalCall higher).receiver := by
    change ([] : List Nat) ⊆ [0]
    simp
  have bodyReceived := SourceSupport.bounds_iff.mp
    (selected.authentic.1 [] (originalCall higher) known functionReceived).current_support
  rcases focused with ⟨site,_source,certificate,certificateChecked,accounting,_related,_admin,_raw⟩
  cases certificate with
  | sequence _ rest =>
    cases rest with
    | sequence _ publicCertificate =>
      cases certificateChecked with
      | sequence _ restChecked =>
        cases restChecked with
        | sequence _ publicChecked =>
          have publicRun := (Accounting.silent_prefix_iff (firstDependencies := .pure) .pure Rows.pure higherRows).mp
            ((Accounting.silent_prefix_iff (firstDependencies := .pure) .pure Rows.pure
              (CoreCallableContractSource.sequenceRows (first := Plan.pure) Rows.pure higherRows)).mp accounting)
          let retained := site.retained
          let retainedChecked := site.retainedChecked
          let privateCertificate := selected.refinement.code [] (fun _ => none) [] (OwnerPhaseTransitions.available []) [0] []
            callerContext retained publicCertificate
          have privateChecked := selected.refinement.checked [] [] (fun _ => none) [] (OwnerPhaseTransitions.available []) [0] []
            callerContext retained publicCertificate bodyReceived (by simp [originalCall,actualCall]) (by simp [originalCall,actualCall,SourceDependencyCapture.Scope.visibleResources])
            retainedChecked publicChecked
          obtain ⟨nextRoot,privateRun,rootTransport⟩ := selected.refinement.accounting [0] [] callerContext
            CoreCallableOriginalResourceCurrent.Original.root publicRun
          obtain ⟨nextCertificate,nextChecked,nextRun⟩ := transport_beta_rows selected.sameSignature selected.sameRows
            privateCertificate privateChecked privateRun
          obtain ⟨nextAnnotated,nextRow,nextAnnotation,nextRootChecked,nextBounded⟩ :=
            rootTransport.checked [] [] (OwnerPhaseTransitions.available []) [] site.annotation site.checked site.bounded
          let next : Site globals [] [0] [.cell 0] (fun _ => none) (OwnerPhaseTransitions.available []) [] [] []
              (runtime.closedBody.subst 11 reader.initializer) .none e21.lexical .integer .integer callerContext nextRoot :=
            { sourceDemand := selected.family.demand,requirements := selected.family.requirements,
              dependencies := _,plan := selected.nextPlan,rows := selected.nextRows,bound := [0],
              current := selected.current.allowed_weaken (List.Subset.refl _),received := by simp [SourceDependencyCapture.Scope.visibleResources],
              certificate := nextCertificate,certificateChecked := nextChecked,pending := site.pending,
              retained := site.retained,retainedChecked := site.retainedChecked,accounting := nextRun,
              annotated := nextAnnotated,row := nextRow,annotation := nextAnnotation,checked := nextRootChecked,bounded := nextBounded }
          exact ⟨⟨selected,chosen,nextRoot,rootTransport,next,rfl,HEq.rfl,HEq.rfl,HEq.rfl,⟨rfl⟩,
            (CoreCallableGeneratedChronology.Operation.actual (.beta outerBeta)).1,
            (CoreCallableGeneratedChronology.Operation.actual (.beta outerBeta)).2,
            .beta 11 runtime.closedBody reader.initializer .none e20.lexical
              ComposedResourceRuntimeOriginProbes.checkedReader.closed CoreCallableComposedRuntimeCalls.Original.checkedHigher.closed,
            first_beta_environment,rfl⟩⟩

noncomputable def first_segment : CoreCallableInitialChronology.OperationSegment e15 e21 6 [] [] :=
  .next (.next (.next (.next (.next (.next .initial (.bind bindInput)) (.entry outerEntry))
    (.literal outerFunction)) (.swap outerSwap)) (.literal outerArgument)) (.beta outerBeta)

structure InstalledFirstBeta where
  higher : HigherInstalled
  focused : Focused higher
  beta : FirstBeta higher focused
  actual : CoreAllocationHistory.Steps G 21 (CoreMachine.initial G) e21.state

/-- One no-input producer executes the original checks and retains the whole
initial prefix through the first rich beta. -/
theorem installed_first_beta : Nonempty InstalledFirstBeta := by
  obtain ⟨higher⟩ := higher_installed_current
  obtain ⟨focused⟩ := focus_current higher
  obtain ⟨beta⟩ := beta_current higher focused
  exact ⟨⟨higher,focused,beta,higher.actual.trans first_segment.actual_steps⟩⟩

theorem argument_support (higher : HigherInstalled) : (originalCall higher).argument = [0,0] := rfl
theorem captured_callee : higherBodyEnvironment =
    .binding 11 (.closure 10 5 ComposedResourceRuntimeOriginProbes.selection.acquiredEnvironment)
      ComposedResourceRuntimeOriginProbes.reader.installedEnvironment := rfl

#print axioms installed_first_beta
#print axioms argument_support
#print axioms captured_callee
#print axioms beta_current
#print axioms select_original
#print axioms focus_current
#print axioms saved_stack
#print axioms admin_machine
end Original
end Ash.OneShot.CoreCallableOriginalBetaCurrent
