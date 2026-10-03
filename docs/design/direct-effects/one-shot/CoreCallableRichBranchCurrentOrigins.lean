import CoreCallableRichAdmittedEventConsumers
import CoreCallableContractCaptureConnection
import CoreCallableOriginalReadCompletionCurrent
import CoreResumeFrames

namespace Ash.OneShot.CoreCallableRichBranchCurrentOrigins
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract Environment)
open CoreCallableContractAdmission CoreCallableReceiverRefinement CoreCallableContractExecution
open CoreCallableGeneratedChronology CoreValueRelation CoreStrictFrames CoreStrictStack
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceDependencyAnnotations (Dependencies RowAnnotation)
open RecursiveRequirements (Requirements Checked)
open SourceScheduledCleanupInterfaces.Lexical.Recursive
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourcePlannedChecks (DeclarationPolicy)

section
variable [DeclarationPolicy]

/-- Selection retains the SAME full original recursive arm derivation. -/
inductive OriginalArm :
    {code : Code} → {demand : List Nat} → {requirements : Requirements demand} →
    {dependencies : Dependencies} → {plan : Plan dependencies} → {rows : Rows (signature plan)} →
    Source globals outward world allowed scope environment code output demand requirements plan rows →
    {chosen : Code} → {selectedDemand : List Nat} → {selectedRequirements : Requirements selectedDemand} →
    {selectedDependencies : Dependencies} → {selectedPlan : Plan selectedDependencies} →
    {selectedRows : Rows (signature selectedPlan)} →
    Source globals outward world allowed scope environment chosen output selectedDemand selectedRequirements selectedPlan selectedRows → Prop where
  | yes (condition : Source globals outward world allowed scope environment (.boolean true) .boolean conditionDemand conditionReq conditionPlan conditionRows)
      (left : Source globals outward world allowed scope environment yes output yesDemand yesReq yesPlan yesRows)
      (right : Source globals outward world allowed scope environment no output noDemand noReq noPlan noRows)
      (same : yesDemand.Perm noDemand) : OriginalArm (IndexedSource.branch condition left right same) left
  | no (condition : Source globals outward world allowed scope environment (.boolean false) .boolean conditionDemand conditionReq conditionPlan conditionRows)
      (left : Source globals outward world allowed scope environment yes output yesDemand yesReq yesPlan yesRows)
      (right : Source globals outward world allowed scope environment no output noDemand noReq noPlan noRows)
      (same : yesDemand.Perm noDemand) : OriginalArm (IndexedSource.branch condition left right same) right

/-- The selected actual accounting root keeps its own demand index. Permutation
is retained explicitly; it is never converted into Type index equality. -/
structure RootSelection {demand selectedDemand : List Nat}
    (original : Requirements demand) (selected : Requirements selectedDemand) : Prop where
  permutation : demand.Perm selectedDemand
  checked : ∀ (entries : RecursiveRequirements.Store) (receiving : OwnerPhases.Context)
      (phases : OwnerPhaseTransitions.Phases) (budget : Footprint)
      {annotated : Requirements demand} {row : Footprint},
      RowAnnotation original annotated → Checked entries receiving phases (annotateDisposals annotated) row →
      row ⊆ budget → ∃ selectedAnnotated : Requirements selectedDemand, ∃ selectedRow : Footprint,
        RowAnnotation selected selectedAnnotated ∧
        Checked entries receiving phases (annotateDisposals selectedAnnotated) selectedRow ∧ selectedRow ⊆ budget

omit [DeclarationPolicy] in
theorem select_left (left : Requirements demand) (right : Requirements rightDemand)
    (same : demand.Perm rightDemand) : RootSelection (.choice left right same) left := by
  refine ⟨List.Perm.refl _,?_⟩
  intro entries receiving phases budget annotated row annotation checked bounded
  obtain ⟨la,ra,lr,rr,lann,rann,lc,rc,lb,rb⟩ :=
    CoreCallableOriginalReadCompletionCurrent.choice_checks_at annotation left right same rfl checked
  exact ⟨la,lr,lann,lc,lb.trans bounded⟩

omit [DeclarationPolicy] in
theorem select_right (left : Requirements demand) (right : Requirements rightDemand)
    (same : demand.Perm rightDemand) : RootSelection (.choice left right same) right := by
  refine ⟨same,?_⟩
  intro entries receiving phases budget annotated row annotation checked bounded
  obtain ⟨la,ra,lr,rr,lann,rann,lc,rc,lb,rb⟩ :=
    CoreCallableOriginalReadCompletionCurrent.choice_checks_at annotation left right same rfl checked
  exact ⟨ra,rr,rann,rc,rb.trans bounded⟩

structure BranchPreserved
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.branch (.boolean choice) yes no) runtimeScope stack output final context root) where
  selectedDemand : List Nat
  selectedRoot : Requirements selectedDemand
  rootSelection : RootSelection root selectedRoot
  next : Site globals outward world allowed actions phases budget ambient installations
    (if choice then yes else no) runtimeScope stack output final context selectedRoot
  original : OriginalArm site.current.source next.current.source
  pending : next.pending = site.pending
  retained : next.retained = site.retained

/-- Project the actual chosen original arm, private checking and accounting.
Neither arm's body or full Contract is restricted to values or pure plans. -/
theorem branch_preserves
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.branch (.boolean choice) yes no) runtimeScope stack output final context root) :
    Nonempty (BranchPreserved site) := by
  rcases site with ⟨sourceDemand,requirements,dependencies,plan,rows,bound,current,received,
    certificate,certificateChecked,pending,retained,retainedChecked,accounting,annotated,row,annotation,checked,bounded⟩
  obtain ⟨lexical,sameEnvironment,authentication⟩ := current.authentication
  cases authentication with
  | checked currentSupport hereditary =>
    cases hereditary with
    | branch conditionAuth yesAuth noAuth =>
      rename_i sameDemand conditionSource yesSource noSource
      cases conditionSource
      have branchRun := (Accounting.silent_prefix_iff .pure Rows.pure _).mp accounting
      cases branchRun with
      | choice leftRun rightRun permutation =>
        rename_i secondDemand secondRoot firstRoot
        cases certificate with
        | sequence conditionCertificate branchesCertificate =>
          cases branchesCertificate with
          | choice leftCertificate rightCertificate =>
            cases certificateChecked with
            | sequence conditionChecked branchesChecked =>
              cases branchesChecked with
              | choice leftChecked rightChecked =>
                cases choice
                · have selection := select_right firstRoot secondRoot permutation
                  obtain ⟨nextAnnotated,nextRow,nextAnnotation,nextCheck,nextBound⟩ :=
                    selection.checked [] [] phases budget annotation checked bounded
                  let next : Site globals outward world allowed actions phases budget ambient installations
                      no runtimeScope stack output final context _ := {
                    sourceDemand := _,requirements := _,dependencies := _,plan := _,rows := _,
                    bound := actualReceiver world _ ambient,
                    current := ⟨noSource,by simpa only [sameEnvironment] using noAuth.current_support,
                      actualReceiver.issued,⟨lexical,sameEnvironment,noAuth⟩,current.receiverIssued⟩,
                    received := actualReceiver.received,certificate := rightCertificate,certificateChecked := rightChecked,
                    pending := pending,retained := retained,retainedChecked := retainedChecked,accounting := rightRun,
                    annotated := nextAnnotated,row := nextRow,annotation := nextAnnotation,checked := nextCheck,bounded := nextBound }
                  exact ⟨⟨_,_,selection,next,.no .boolean yesSource noSource sameDemand,rfl,rfl⟩⟩
                · have selection := select_left firstRoot secondRoot permutation
                  obtain ⟨nextAnnotated,nextRow,nextAnnotation,nextCheck,nextBound⟩ :=
                    selection.checked [] [] phases budget annotation checked bounded
                  let next : Site globals outward world allowed actions phases budget ambient installations
                      yes runtimeScope stack output final context _ := {
                    sourceDemand := _,requirements := _,dependencies := _,plan := _,rows := _,
                    bound := actualReceiver world _ ambient,
                    current := ⟨yesSource,by simpa only [sameEnvironment] using yesAuth.current_support,
                      actualReceiver.issued,⟨lexical,sameEnvironment,yesAuth⟩,current.receiverIssued⟩,
                    received := actualReceiver.received,certificate := leftCertificate,certificateChecked := leftChecked,
                    pending := pending,retained := retained,retainedChecked := retainedChecked,accounting := leftRun,
                    annotated := nextAnnotated,row := nextRow,annotation := nextAnnotation,checked := nextCheck,bounded := nextBound }
                  exact ⟨⟨_,_,selection,next,.yes .boolean yesSource noSource sameDemand,rfl,rfl⟩⟩

/-- Only the CURRENT mapped frame and literal control are inputs. Arm nodes,
translations and environments are projected from its existing FrameRel. -/
structure DecisionInput (current : Endpoint graph) where
  choice : Bool
  frame : CoreMachine.Frame
  plain : PlainData
  yesCode : Code
  noCode : Code
  context : plain.context = .branch yesCode noCode
  related : PlainFrameRel graph current.owners current.state.heap frame plain
  control : current.state.control = .returned (.boolean choice)
  maps : current.maps = [(current.owners,frame)]
  focus : current.focus = ⟨.branch (.boolean choice) yesCode noCode,plain.scope,.nil⟩

omit [DeclarationPolicy] in
theorem decision_produced {graph : CoreSyntax.Graph} {current : Endpoint graph}
    (input : DecisionInput current) : ∃ result : Result current [] [],
      result.after.focus = ⟨if input.choice then input.yesCode else input.noCode,input.plain.scope,.nil⟩ ∧
      result.after.lexical = current.lexical ∧ HEq result.after.history current.history ∧
      result.after.owners = current.owners ∧ result.after.state.heap = current.state.heap ∧
      result.after.physical = current.physical ∧ result.after.maps = [] := by
  rcases input with ⟨choice,frame,plain,yesCode,noCode,position,related,control,maps,focus⟩
  change FrameRel graph current.owners current.state.heap frame plain.context at related
  rw [position] at related
  cases related with
  | booleanMatch yesTranslated noTranslated yesSaved noSaved =>
    rename_i yesFuel yes rawYes noFuel no rawNo environment reversed
    let after : Endpoint graph := {
      state := { current.state with
        control := .evaluate (if choice then yes else no) environment
        frames := current.physical }
      focus := ⟨if choice then yesCode else noCode,plain.scope,.nil⟩
      owners := current.owners,maps := [],physical := current.physical,lexical := current.lexical
      history := current.history,frames := rfl }
    have shape : current.state.frames =
        .matchCases (CoreStrictSteps.booleanArms yes no reversed) environment :: current.physical := by
      simpa only [maps,framesOf,List.map_cons,List.map_nil,List.cons_append,List.nil_append] using current.frames
    have core : CoreMachine.next graph current.state = .stepped after.state := by
      simp only [CoreMachine.next,control,shape,CoreStrictSteps.select_boolean]
      rfl
    refine ⟨⟨after,core,.positive ?_⟩,rfl,rfl,HEq.rfl,rfl,rfl,rfl,rfl⟩
    simp only [Endpoint.point,focus,CoreCleanupRunFrames.attach,Stack.append]
    cases choice
    · exact .one (.evaluate (.ifFalse _ _ _ _) (by trivial))
    · exact .one (.evaluate (.ifTrue _ _ _ _) (by trivial))

noncomputable def decision_result (input : DecisionInput current) : Result current [] [] :=
  Classical.choose (decision_produced input)

omit [DeclarationPolicy] in
theorem decision_focus (input : DecisionInput current) :
    (decision_result input).after.focus =
      ⟨if input.choice then input.yesCode else input.noCode,input.plain.scope,.nil⟩ ∧
    (decision_result input).after.lexical = current.lexical ∧
    HEq (decision_result input).after.history current.history ∧
    (decision_result input).after.owners = current.owners ∧
    (decision_result input).after.state.heap = current.state.heap ∧
    (decision_result input).after.physical = current.physical ∧
    (decision_result input).after.maps = [] :=
  Classical.choose_spec (decision_produced input)

end
#print axioms select_left
#print axioms select_right
#print axioms branch_preserves
#print axioms decision_produced
#print axioms decision_result
#print axioms decision_focus
end Ash.OneShot.CoreCallableRichBranchCurrentOrigins
