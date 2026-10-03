import CoreCallableOriginalBetaCurrent
import CoreCallableComposedRuntimeCompletion
namespace Ash.OneShot.CoreCallableOriginalSecondBetaCurrent
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
set_option maxHeartbeats 3000000
namespace Original
open CoreCallableOriginalCallableCurrent.Original
open CoreCallableOriginalHigherCurrent.Original
open CoreCallableOriginalBetaCurrent.Original
open CoreCallableComposedRuntimeCalls.Original
abbrev readerApplicationPlanDeps := SourceDependencyAnnotations.Dependencies.sequence .pure (.sequence .pure ((CoreCallableCompositionalResourceBody.Checking.embedded CoreCallableCompositionalResourceRoot.oldRead).dependencies 0))
abbrev readerApplicationPlan := Plan.sequence Plan.pure (Plan.sequence Plan.pure readerPlan)
abbrev readerApplicationRows : Rows (signature readerApplicationPlan) :=
  CoreCallableContractSource.sequenceRows Rows.pure (CoreCallableContractSource.sequenceRows Rows.pure readerRows)
abbrev readerApplicationRequirements : RecursiveRequirements.Requirements ([] ++ []) :=
  .emitAfter (.sequence (.request [] []) (.request [] [])) [] readerLatent

/-- Invert the actual variable11/Unit application. The environment lookup
retains the full original reader Contract, including its public Plan and Rows. -/
theorem private_application_shape {plan : Plan dependencies} {rows : Rows (signature plan)}
    (source : Source globals [] [0] [.cell 0] .none (Environment.empty.extend 11 readerContract)
      (.app (.variable 11) .unit) .integer demand requirements plan rows) :
    dependencies = readerApplicationPlanDeps ∧ demand = [] ∧ HEq requirements readerApplicationRequirements ∧
    HEq plan readerApplicationPlan ∧ HEq rows readerApplicationRows := by
  cases source with
  | app function argument admitted certified =>
    cases function with
    | «variable» known formed =>
      change some readerContract = some _ at known
      injection known with same
      cases same
      cases argument
      exact ⟨rfl,rfl,HEq.rfl,HEq.rfl,HEq.rfl⟩

/-- The selected higher Family's current body supplies the exact private join.
Family identity is read from the first receipt rather than inferred from code. -/
theorem selected_private_application_shape (produced : InstalledFirstBeta) :
    produced.beta.selected.family.dependencies [] (originalCall produced.higher) =
      readerApplicationPlanDeps ∧
    produced.beta.selected.family.demand = [] ∧
    HEq produced.beta.selected.family.requirements readerApplicationRequirements ∧
    HEq (produced.beta.selected.family.plans [] (originalCall produced.higher)) readerApplicationPlan ∧
    HEq (produced.beta.selected.family.rows [] (originalCall produced.higher)) readerApplicationRows := by
  exact private_application_shape (produced.beta.selected.family.body [] (originalCall produced.higher))

theorem substituted_application_shape {plan : Plan dependencies}
    (dependenciesSame : dependencies = readerApplicationPlanDeps) (same : HEq plan readerApplicationPlan) :
    HEq (CoreCallablePlanSubstitution.plan (.app (.variable 11) .unit) plan 11 reader.initializer)
      readerApplicationPlan := by
  subst dependencies
  cases eq_of_heq same
  rfl

/-- The deterministic substitution joins the selected successor's private
Plan and Rows without supplying future-success metadata. -/
theorem selected_successor_shape (produced : InstalledFirstBeta) :
    HEq produced.beta.selected.nextPlan readerApplicationPlan ∧
    HEq produced.beta.selected.nextRows readerApplicationRows := by
  have shape := selected_private_application_shape produced
  have computed := substituted_application_shape shape.1 shape.2.2.2.1
  have selected : HEq produced.beta.selected.nextPlan readerApplicationPlan := by
    rw [produced.beta.selected.exactPlan]
    exact computed
  exact ⟨selected,produced.beta.selected.sameRows.trans shape.2.2.2.2⟩

/-- The frozen CURRENT successor retains heterogeneous Plan/Rows joins.
Their dependency-index transport remains the named stop diagnostic. -/
theorem successor_heterogeneous_shape (produced : InstalledFirstBeta) :
    HEq produced.beta.next.plan readerApplicationPlan ∧
    HEq produced.beta.next.rows readerApplicationRows := by
  have shape := selected_successor_shape produced
  exact ⟨produced.beta.exactPlan.trans shape.1,produced.beta.exactRows.trans shape.2⟩

/-- A current dependency-index join suffices to transport the exact checked
rows and accounting. This diagnostic does not produce that missing join. -/
theorem application_facets_at_shared_dependencies {plan : Plan dependencies} {rows : Rows (signature plan)}
    (dependenciesSame : dependencies = readerApplicationPlanDeps)
    (planShape : HEq plan readerApplicationPlan) (rowShape : HEq rows readerApplicationRows)
    (certificate : SourceAdmission.Code [] (fun _ => none) [] (OwnerPhaseTransitions.available []) [0] [] rows callerContext)
    (checked : InstallationSupport.CodeChecked [] [] certificate)
    (accounting : Accounting.Run [0] [] rows callerContext root) :
    ∃ certificate : SourceAdmission.Code [] (fun _ => none) [] (OwnerPhaseTransitions.available []) [0] [] readerApplicationRows callerContext,
      InstallationSupport.CodeChecked [] [] certificate ∧
      Accounting.Run [0] [] readerApplicationRows callerContext root := by
  subst dependencies
  cases eq_of_heq planShape
  cases eq_of_heq rowShape
  exact ⟨certificate,checked,accounting⟩

abbrev readerApplicationSource (produced : InstalledFirstBeta) :
    Source globals [] [0] [.cell 0] .none Environment.empty
      (.app reader.initializer .unit) .integer [] readerApplicationRequirements readerApplicationPlan readerApplicationRows :=
  .app produced.higher.installed.origin.family.whole .unit (List.Subset.refl _)
    produced.higher.installed.origin.family.publicCertified

theorem reader_application_authenticated (produced : InstalledFirstBeta) :
    Authenticated globals.registry [] (readerApplicationSource produced) [] [0] := by
  refine .checked ?_ (Hereditary.app (admitted := List.Subset.refl _)
    (publicCertified := produced.higher.installed.origin.family.publicCertified)
    produced.higher.installed.origin.authenticated (.checked .nil .unit))
  apply SourceSupport.bounds_iff.mpr
  change [0,0] ⊆ [0]
  simp

abbrev ReaderAppSite (produced : InstalledFirstBeta) :=
  Site globals [] [0] [.cell 0] (fun _ => none) (OwnerPhaseTransitions.available []) [] [] []
    (.app reader.initializer .unit) .none e21.lexical .integer .integer callerContext produced.beta.nextRoot

structure ReaderApplication (produced : InstalledFirstBeta) where
  site : ReaderAppSite produced
  sameSource : HEq site.current.source (readerApplicationSource produced)
  certificate : SourceAdmission.Code [] (fun _ => none) [] (OwnerPhaseTransitions.available []) [0] [] readerApplicationRows callerContext
  checked : InstallationSupport.CodeChecked [] [] certificate
  accounting : Accounting.Run [0] [] readerApplicationRows callerContext produced.beta.nextRoot
  related : CoreCallableRichBetaCore.Current e21 site
  adminRelated : CoreCallableRichBetaCore.Current e25 site

/-- Reconstruct from the same first CURRENT output. The added index equality
is computed by the existing first-beta constructor, not future metadata. -/
theorem reader_application_current (produced : InstalledFirstBeta) : Nonempty (ReaderApplication produced) := by
  have shape := successor_heterogeneous_shape produced
  have deps := produced.beta.exactDependencies.trans (selected_private_application_shape produced).1
  obtain ⟨certificate,checked,accounting⟩ := application_facets_at_shared_dependencies deps shape.1 shape.2
    produced.beta.next.certificate produced.beta.next.certificateChecked produced.beta.next.accounting
  have auth := reader_application_authenticated produced
  let site : ReaderAppSite produced :=
    { sourceDemand := [],requirements := readerApplicationRequirements,dependencies := _,plan := readerApplicationPlan,
      rows := readerApplicationRows,bound := [0],
      current := ⟨readerApplicationSource produced,auth.current_support,by simp,⟨[],rfl,auth⟩,
        by simp [actualReceiver,SourceDependencyCapture.Scope.visibleResources]⟩,
      received := by simp [SourceDependencyCapture.Scope.visibleResources],certificate := certificate,certificateChecked := checked,
      pending := produced.beta.next.pending,retained := produced.beta.next.retained,
      retainedChecked := produced.beta.next.retainedChecked,accounting := accounting,
      annotated := produced.beta.next.annotated,row := produced.beta.next.row,annotation := produced.beta.next.annotation,
      checked := produced.beta.next.checked,bounded := produced.beta.next.bounded }
  exact ⟨⟨site,HEq.rfl,certificate,checked,accounting,⟨rfl⟩,⟨rfl⟩⟩⟩

abbrev unitClosed : ClosedValue Code.unit := by
  simp [ClosedValue,Code.IsValue,Code.ResourceClosed,Code.freeNames,Code.dependencies]
abbrev unitSupported : CoreCallableContractAdmission.Supported globals [] [0] [.cell 0] .none Environment.empty ScopedPorts.Support.empty
    .unit .unit [] (.request [] []) .pure Rows.pure [] [0] :=
  ⟨.unit,.nil,by simp,⟨[],rfl,.checked .nil .unit⟩,by simp⟩
abbrev readerCall := CoreCallableRichBetaPreservation.actualCall [0] [0] .unit (by simp) unitSupported.actual_received

theorem reader_authentic (produced : InstalledFirstBeta) : produced.higher.installed.origin.family.Authentic :=
  produced.higher.installed.origin.authentic

/-- Select Installed's original closed reader at actual Unit support. -/
theorem select_reader (produced : InstalledFirstBeta) :
    ∃ selected : CoreCallableRichBetaPreservation.Selected
      (produced.higher.installed.origin.family.whole (allowed := [.cell 0]) (scope := .none)) [] readerCall .unit,
      selected.family = produced.higher.installed.origin.family := by
  let family := produced.higher.installed.origin.family
  have authentic := reader_authentic produced
  have known : LexicalBounds.Known [] (Code.lambda 10 reader.closedBody).dependencies := by
    intro name member
    change Syntax.Dependency.variable name ∈ [.resource 0,.resource 0] at member
    simp at member
  have received : ScopedPorts.Support.evaluate (LexicalBounds.environment [])
      (Code.lambda 10 reader.closedBody).dependencies ⊆ readerCall.receiver := by
    change [0,0] ⊆ [0]
    simp
  have bodyAuth := authentic.1 [] readerCall known received
  have refinement := authentic.2 [] readerCall known received
  let replacement : CoreCallableContractAdmission.Supported globals [] [0] readerRequests .none Environment.empty ScopedPorts.Support.empty
      .unit .unit [] (.request [] []) .pure Rows.pure readerCall.argument [0] :=
    ⟨.unit,.nil,by change ([] : List Nat) ⊆ [0]; simp,
      ⟨[],rfl,.checked .nil .unit⟩,by simp⟩
  let bodySupported : CoreCallableContractAdmission.Supported globals [] [0] readerRequests .none (Environment.empty.extend 10 .unit)
      (ScopedPorts.Support.extend ScopedPorts.Support.empty 10 readerCall.argument) reader.closedBody .integer
      family.demand family.requirements (family.plans [] readerCall) (family.rows [] readerCall) [0] [0] :=
    ⟨family.body [] readerCall,by simpa only [LexicalBounds.environment_extend,
      show LexicalBounds.environment [] = ScopedPorts.Support.empty from rfl,
      readerCall,CoreCallableRichBetaPreservation.actualCall] using bodyAuth.current_support,
      by simp,⟨LexicalBounds.extend [] 10 readerCall.argument,by simp only [LexicalBounds.environment_extend]; rfl,bodyAuth⟩,by simp⟩
  obtain ⟨nextPlan,nextRows,current,exactPlan,sameSignature,sameRows⟩ :=
    bodySupported.substitution_reannotated CoreCallableComposedCapturedHandle.structural_policy_stable replacement unitClosed
  exact ⟨⟨family,.receiver family,authentic,known,refinement,nextPlan,nextRows,current,exactPlan,sameSignature,sameRows⟩,rfl⟩

private theorem transport_reader_rows
    {first second : SourcePlanSignatures.Signature dependencies}
    {firstRows : Rows first} {secondRows : Rows second}
    (same : first = second) (sameRows : HEq firstRows secondRows)
    (certificate : SourceAdmission.Code [] (fun _ => none) [] (OwnerPhaseTransitions.available []) [0] [] secondRows callerContext)
    (checked : InstallationSupport.CodeChecked [] [] certificate)
    (run : Accounting.Run [0] [] secondRows callerContext root) :
    ∃ nextCertificate : SourceAdmission.Code [] (fun _ => none) [] (OwnerPhaseTransitions.available []) [0] [] firstRows callerContext,
      InstallationSupport.CodeChecked [] [] nextCertificate ∧ Accounting.Run [0] [] firstRows callerContext root := by
  subst second
  cases eq_of_heq sameRows
  exact ⟨certificate,checked,run⟩

structure SecondBeta (produced : InstalledFirstBeta) (application : ReaderApplication produced) where
  selected : CoreCallableRichBetaPreservation.Selected
    (produced.higher.installed.origin.family.whole (allowed := [.cell 0]) (scope := .none)) [] readerCall .unit
  chosen : selected.family = produced.higher.installed.origin.family
  nextRoot : RecursiveRequirements.Requirements []
  rootTransport : CoreCallableRootRefinement.RootTransport produced.beta.nextRoot nextRoot
  next : Site globals [] [0] [.cell 0] (fun _ => none) (OwnerPhaseTransitions.available []) [] [] []
    (reader.closedBody.subst 10 .unit) .none e26.lexical .integer .integer callerContext nextRoot
  exactDependencies : next.dependencies = selected.family.dependencies [] readerCall
  exactDemand : next.sourceDemand = selected.family.demand
  exactRequirements : HEq next.requirements selected.family.requirements
  exactPlan : HEq next.plan selected.nextPlan
  exactRows : HEq next.rows selected.nextRows
  related : CoreCallableRichBetaCore.Current e26 next
  actual : CoreMachine.next G e25.state = .stepped e26.state
  matching : CoreCallableGeneratedChronology.Matching G e25 e26 [] []
  raw : RawStep ⟨.app reader.initializer .unit,.none,e25.lexical⟩
    ⟨reader.closedBody.subst 10 .unit,.none,e26.lexical⟩ [] []
  callee : e26.state.control = .evaluate 5 readerBodyEnvironment
  history : e26.history = e25.history

/-- CURRENT reconstruction chooses the original closed reader and computes its
private substitution, root refinement and same actual positive Core beta. -/
theorem second_beta_current (produced : InstalledFirstBeta) (application : ReaderApplication produced) :
    Nonempty (SecondBeta produced application) := by
  obtain ⟨selected,chosen⟩ := select_reader produced
  have known := selected.known
  have received : ScopedPorts.Support.evaluate (LexicalBounds.environment [])
      (Code.lambda 10 reader.closedBody).dependencies ⊆ readerCall.receiver := by
    change [0,0] ⊆ [0]
    simp
  have bodyReceived := SourceSupport.bounds_iff.mp (selected.authentic.1 [] readerCall known received).current_support
  rcases application with ⟨site,_source,certificate,certificateChecked,accounting,_related,_admin⟩
  cases certificate with
  | sequence _ rest =>
    cases rest with
    | sequence _ publicCertificate =>
      cases certificateChecked with
      | sequence _ restChecked =>
        cases restChecked with
        | sequence _ publicChecked =>
          have publicRun := (Accounting.silent_prefix_iff .pure Rows.pure readerRows).mp
            ((Accounting.silent_prefix_iff .pure Rows.pure
              (CoreCallableContractSource.sequenceRows (first := Plan.pure) Rows.pure readerRows)).mp accounting)
          let privateCertificate := selected.refinement.code [] (fun _ => none) [] (OwnerPhaseTransitions.available []) [0] []
            callerContext site.retained publicCertificate
          have privateChecked := selected.refinement.checked [] [] (fun _ => none) [] (OwnerPhaseTransitions.available []) [0] []
            callerContext site.retained publicCertificate bodyReceived
            (by simp [readerCall,CoreCallableRichBetaPreservation.actualCall])
            (by simp [readerCall,CoreCallableRichBetaPreservation.actualCall,SourceDependencyCapture.Scope.visibleResources])
            site.retainedChecked publicChecked
          obtain ⟨nextRoot,privateRun,rootTransport⟩ := selected.refinement.accounting [0] [] callerContext produced.beta.nextRoot publicRun
          obtain ⟨nextCertificate,nextChecked,nextRun⟩ := transport_reader_rows selected.sameSignature selected.sameRows
            privateCertificate privateChecked privateRun
          obtain ⟨nextAnnotated,nextRow,nextAnnotation,nextRootChecked,nextBounded⟩ :=
            rootTransport.checked [] [] (OwnerPhaseTransitions.available []) [] site.annotation site.checked site.bounded
          let next : Site globals [] [0] [.cell 0] (fun _ => none) (OwnerPhaseTransitions.available []) [] [] []
              (reader.closedBody.subst 10 .unit) .none e26.lexical .integer .integer callerContext nextRoot :=
            { sourceDemand := selected.family.demand,requirements := selected.family.requirements,dependencies := _,
              plan := selected.nextPlan,rows := selected.nextRows,bound := [0],
              current := selected.current.allowed_weaken (List.Subset.refl _),received := by simp [SourceDependencyCapture.Scope.visibleResources],
              certificate := nextCertificate,certificateChecked := nextChecked,pending := site.pending,
              retained := site.retained,retainedChecked := site.retainedChecked,accounting := nextRun,
              annotated := nextAnnotated,row := nextRow,annotation := nextAnnotation,checked := nextRootChecked,bounded := nextBounded }
          exact ⟨⟨selected,chosen,nextRoot,rootTransport,next,rfl,rfl,HEq.rfl,HEq.rfl,HEq.rfl,⟨rfl⟩,
            (CoreCallableGeneratedChronology.Operation.actual (.beta innerBeta)).1,
            (CoreCallableGeneratedChronology.Operation.actual (.beta innerBeta)).2,
            .beta 10 reader.closedBody .unit .none e25.lexical unitClosed ComposedResourceRuntimeOriginProbes.checkedReader.closed,
            second_beta_environment,rfl⟩⟩

noncomputable def second_segment : CoreCallableInitialChronology.OperationSegment e21 e26 5 [] [] :=
  .next (.next (.next (.next (.next .initial (.entry innerEntry)) (.literal innerFunction))
    (.swap innerSwap)) (.literal innerArgument)) (.beta innerBeta)

structure InstalledSecondBeta where
  first : InstalledFirstBeta
  application : ReaderApplication first
  beta : SecondBeta first application
  actual : CoreAllocationHistory.Steps G 26 (CoreMachine.initial G) e26.state

/-- The same original no-input factory continues through actual second beta. -/
theorem installed_second_beta : Nonempty InstalledSecondBeta := by
  obtain ⟨first⟩ := installed_first_beta
  obtain ⟨application⟩ := reader_application_current first
  obtain ⟨beta⟩ := second_beta_current first application
  exact ⟨⟨first,application,beta,first.actual.trans second_segment.actual_steps⟩⟩

#print axioms installed_second_beta
#print axioms second_beta_current
#print axioms reader_application_current
#print axioms reader_authentic
#print axioms select_reader
#print axioms private_application_shape
#print axioms selected_private_application_shape
#print axioms substituted_application_shape
#print axioms selected_successor_shape
#print axioms successor_heterogeneous_shape
#print axioms application_facets_at_shared_dependencies
end Original
end Ash.OneShot.CoreCallableOriginalSecondBetaCurrent
