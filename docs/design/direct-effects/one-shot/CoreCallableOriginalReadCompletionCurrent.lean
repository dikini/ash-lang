import CoreCallableOriginalSecondBetaCurrent
namespace Ash.OneShot.CoreCallableOriginalReadCompletionCurrent
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract Environment)
open CoreCallableContractAdmission CoreCallableReceiverRefinement CoreCallableContractExecution
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceDependencyAnnotations (RowAnnotation)
open RecursiveRequirements (Requirements Checked)
open SourceScheduledCleanupInterfaces.Lexical.Recursive
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
local instance : SourcePlannedChecks.DeclarationPolicy := declarationPolicy
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

/-- Project the actual choice check while retaining its budget bound. -/
theorem choice_checks_at {normal : Requirements demand}
    (annotation : RowAnnotation normal annotated) :
    ∀ (left : Requirements demand) {rightDemand : List Nat} (right : Requirements rightDemand)
      (same : demand.Perm rightDemand), normal = .choice left right same →
      Checked entries receiving phases (annotateDisposals annotated) row →
    ∃ leftAnnotated rightAnnotated leftRow rightRow,
      RowAnnotation left leftAnnotated ∧ RowAnnotation right rightAnnotated ∧
      Checked entries receiving phases (annotateDisposals leftAnnotated) leftRow ∧
      Checked entries receiving phases (annotateDisposals rightAnnotated) rightRow ∧
      leftRow ⊆ row ∧ rightRow ⊆ row := by
  induction annotation generalizing row with
  | original =>
    intro left rightDemand right same equation check
    cases equation
    cases check with
    | choice leftCheck rightCheck =>
      exact ⟨_,_,_,_,.original,.original,leftCheck,rightCheck,
        List.subset_append_left _ _,List.subset_append_right _ _⟩
  | choice leftAnnotation rightAnnotation ihL ihR =>
    intro left rightDemand right same equation check
    cases equation
    cases check with
    | choice leftCheck rightCheck =>
      exact ⟨_,_,_,_,leftAnnotation,rightAnnotation,leftCheck,rightCheck,
        List.subset_append_left _ _,List.subset_append_right _ _⟩
  | alternatives normal permutation ih =>
    intro left rightDemand right same equation check
    cases check with
    | choice first second =>
      obtain ⟨a,b,ar,br,aa,ba,ac,bc,ab,bb⟩ := ih left right same equation first
      exact ⟨a,b,ar,br,aa,ba,ac,bc,
        ab.trans (List.subset_append_left _ _),bb.trans (List.subset_append_left _ _)⟩
  | sequence first second ihF ihS => intro left rightDemand right same equation; cases equation
  | emitAfter body ih => intro left rightDemand right same equation; cases equation

/-- This bounded helper consumes the current literal true branch. It projects
its chosen original arm, current accounting and annotation rather than a fixture. -/
theorem true_integer_branch
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.branch (.boolean true) (.integer value) (.integer value)) runtimeScope stack .integer final context root) :
    ∃ demand, ∃ selectedRoot : Requirements demand,
      ∃ next : Site globals outward world allowed actions phases budget ambient installations
        (.integer value) runtimeScope stack .integer final context selectedRoot,
        next.bound = [] ∧
        RawStep ⟨.branch (.boolean true) (.integer value) (.integer value),runtimeScope,stack⟩
          ⟨.integer value,runtimeScope,stack⟩ [] [] := by
  rcases site with ⟨sourceDemand,requirements,dependencies,plan,rows,bound,current,received,
    certificate,certificateChecked,pending,retained,retainedChecked,accounting,annotated,row,annotation,checked,bounded⟩
  rcases current with ⟨source,support,issued,authentication,receiverIssued⟩
  cases source with
  | branch condition yes no same =>
    cases condition
    cases yes
    cases no
    have branchRun := (Accounting.silent_prefix_iff .pure Rows.pure
      (CoreCallableContractSource.choiceRows (first := Plan.pure) (second := Plan.pure) Rows.pure Rows.pure)).mp accounting
    cases branchRun with
    | choice left right permutation =>
      obtain ⟨leftAnnotated,rightAnnotated,leftRow,rightRow,leftAnnotation,rightAnnotation,
        leftCheck,rightCheck,leftBound,rightBound⟩ := choice_checks_at annotation _ _ permutation rfl checked
      let next : Site globals outward world allowed actions phases budget ambient installations
          (.integer value) runtimeScope stack .integer final context _ :=
        { sourceDemand := [],requirements := .request [] [],dependencies := .pure,plan := .pure,rows := Rows.pure,
          bound := [],current := ⟨.integer,.nil,by simp,⟨[],rfl,.checked .nil .integer⟩,receiverIssued⟩,
          received := by simp,certificate := .pure,certificateChecked := .pure,pending := pending,
          retained := retained,retainedChecked := retainedChecked,accounting := left,
          annotated := leftAnnotated,row := leftRow,annotation := leftAnnotation,checked := leftCheck,
          bounded := leftBound.trans bounded }
      exact ⟨_,_,next,rfl,.ifTrue _ _ _ _⟩

/-- Return the current empty-support integer through its actual cell boundary.
Historical world membership remains; only the active cell boundary is dropped. -/
theorem integer_cell_return {receiving : SourceDependencyCapture.Scope}
    {hints : SourceDependencyChecks.Lexical.ReturnHints receiving} {context : Context hints}
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.integer value) runtimeScope (.push (.cell identity payload caller answer) stack)
      .integer final (.cell (identity := identity) context) root) :
    ∃ next : Site globals outward world allowed actions phases budget ambient installations
      (.integer value) caller stack .integer final context root,
      next.bound = [] ∧
      RawStep ⟨.integer value,runtimeScope,.push (.cell identity payload caller answer) stack⟩
        ⟨.integer value,caller,stack⟩ [] [.resource identity] := by
  rcases site with ⟨sourceDemand,requirements,dependencies,plan,rows,bound,current,received,
    certificate,certificateChecked,pending,retained,retainedChecked,accounting,annotated,row,annotation,checked,bounded⟩
  rcases current with ⟨source,support,issued,authentication,receiverIssued⟩
  cases source
  cases accounting with
  | pure waiting =>
    cases waiting with
    | cell tailWaiting =>
      cases pending with
      | cell issued resultAnnotation tailPending =>
        cases retained with
        | cell tailRetained =>
          cases retainedChecked with
          | cell tailChecked =>
            let next : Site globals outward world allowed actions phases budget ambient installations
                (.integer value) caller stack .integer final context root :=
              { sourceDemand := [],requirements := .request [] [],dependencies := .pure,plan := .pure,rows := Rows.pure,
                bound := [],current := ⟨.integer,.nil,by simp,⟨[],rfl,.checked .nil .integer⟩,actualReceiver.issued⟩,
                received := by simp,certificate := .pure,certificateChecked := .pure,pending := tailPending,
                retained := tailRetained,retainedChecked := tailChecked,accounting := .pure tailWaiting,
                annotated := annotated,row := row,annotation := annotation,checked := checked,bounded := bounded }
            exact ⟨next,rfl,.leaveCell identity payload answer caller runtimeScope (.integer value) (by simp [ClosedValue,Code.IsValue,Code.ResourceClosed,Code.freeNames,Code.dependencies]) stack⟩

theorem terminal_cell_contract
    (pending : Pending globals outward world allowed ambient
      (.push (.cell identity payload caller answer) .nil) input output
      (Context.cell (identity := identity) Context.nil)) : input = output := by
  cases pending with
  | cell issued annotation tail => cases tail; rfl

namespace Original
open CoreCallableOriginalCallableCurrent.Original
open CoreCallableOriginalHigherCurrent.Original
open CoreCallableOriginalBetaCurrent.Original
open CoreCallableOriginalSecondBetaCurrent.Original
open CoreCallableComposedRuntimeCalls.Original
open CoreCallableComposedRuntimeCompletion

abbrev ReadSite (produced : InstalledSecondBeta) :=
  Site globals [] [0] [.cell 0] (fun _ => none) (OwnerPhaseTransitions.available []) [] [] []
    (.integer 0) .none e29.lexical .integer .integer callerContext produced.beta.nextRoot
abbrev BranchSite (produced : InstalledSecondBeta) :=
  Site globals [] [0] [.cell 0] (fun _ => none) (OwnerPhaseTransitions.available []) [] [] []
    branchCode .none e30.lexical .integer .integer CoreCallableOriginalResourceCurrent.Original.cellContext produced.beta.nextRoot

structure ReadBind (produced : InstalledSecondBeta) where
  read : ReadSite produced
  readRelated : CoreCallableRichBetaCore.Current e29 read
  readRaw : RawStep ⟨.perform (.cell (.activation 0)) 0 (.resourceRef (.activation 0)),.none,e28.lexical⟩
    ⟨.integer 0,.none,e29.lexical⟩ [] []
  branch : BranchSite produced
  branchRelated : CoreCallableRichBetaCore.Current e30 branch
  bindRaw : RawStep ⟨.integer 0,.none,e29.lexical⟩
    ⟨.bind 5 (.integer 0) branchCode,.none,e30.lexical⟩ [] []
  boundRaw : RawStep ⟨.bind 5 (.integer 0) branchCode,.none,e30.lexical⟩
    ⟨branchCode,.none,e30.lexical⟩ [] []

/-- The actual original stack gives the builtin update and saved bind5 caller.
The same second-beta root survives read waiting and both Raw bind steps. -/
theorem read_bind_current (produced : InstalledSecondBeta) : Nonempty (ReadBind produced) := by
  have compatible : globals.operations (.cell 0) 0 = some (.reference 0,.integer) := rfl
  have updated : CellUpdate 0 0 0 e28.lexical e29.lexical := by
    change CellUpdate 0 0 0 (.push (.plain bindReady.plain) CoreCallableOriginalResourceCurrent.Original.cellStack)
      (.push (.plain bindReady.plain) CoreCallableOriginalResourceCurrent.Original.cellStack)
    exact .push (by change (none : Option Instance) ≠ some (.cell 0); simp) .hit
  obtain ⟨read,readRaw⟩ := produced.beta.next.read_cell_reply compatible updated
  have readTyped : ReadSite produced := read
  have readStack : e29.lexical = .push (.plain bindReady.plain) CoreCallableOriginalResourceCurrent.Original.cellStack := rfl
  dsimp only [ReadSite] at readTyped
  rw [readStack] at readTyped
  obtain ⟨parameter,body,position,middle,plugged,bindRaw⟩ := readTyped.plug_bind (by
    simp [ClosedValue,Code.IsValue,Code.ResourceClosed,Code.freeNames,Code.dependencies])
  change ScopedExecution.Context.bind 5 branchCode = ScopedExecution.Context.bind parameter body at position
  have params := ScopedExecution.Context.bind.inj position
  cases params.1
  cases params.2
  have middleSame : middle = Contract.integer := terminal_cell_contract plugged.pending
  subst middle
  obtain ⟨branch,boundRaw⟩ := plugged.bind_value CoreCallableComposedCapturedHandle.structural_policy_stable
    (by simp [ClosedValue,Code.IsValue,Code.ResourceClosed,Code.freeNames,Code.dependencies]) bindReady.closed
  have branchTyped : BranchSite produced := branch
  exact ⟨⟨read,⟨rfl⟩,readRaw,branchTyped,⟨rfl⟩,bindRaw,boundRaw⟩⟩

structure Completion (produced : InstalledSecondBeta) where
  readBind : ReadBind produced
  finalDemand : List Nat
  finalRoot : Requirements finalDemand
  chosen : Site globals [] [0] [.cell 0] (fun _ => none) (OwnerPhaseTransitions.available []) [] [] []
    (.integer 17) .none e33.lexical .integer .integer CoreCallableOriginalResourceCurrent.Original.cellContext finalRoot
  chosenRelated : CoreCallableRichBetaCore.Current e33 chosen
  finalSite : Site globals [] [0] [.cell 0] (fun _ => none) (OwnerPhaseTransitions.available []) [] [] []
    (.integer 17) .none e35.lexical .integer .integer Context.nil finalRoot
  finalRelated : CoreCallableRichBetaCore.Current e35 finalSite
  finalBound : finalSite.bound = []
  choiceRaw : RawStep ⟨branchCode,.none,e32.lexical⟩ ⟨.integer 17,.none,e33.lexical⟩ [] []
  releaseRaw : RawStep ⟨.integer 17,.none,e34.lexical⟩ ⟨.integer 17,.none,e35.lexical⟩ [] [.resource 0]
  actual : CoreAllocationHistory.Steps G 35 (CoreMachine.initial G) e35.state

noncomputable def request_segment : CoreCallableInitialChronology.OperationSegment e26 e28 2 [] [] :=
  .next (.next .initial (.entry requestEntry)) (.literal requestOperand)

/-- Continue the SAME produced initial26 through read0/0, saved caller, original
true arm and release0. No unrelated initial35 theorem is a premise. -/
theorem completion_current (produced : InstalledSecondBeta) : Nonempty (Completion produced) := by
  obtain ⟨readBind⟩ := read_bind_current produced
  obtain ⟨demand,root,chosen,_bound,choiceRaw⟩ := true_integer_branch readBind.branch
  obtain ⟨finalSite,finalBound,releaseRaw⟩ := integer_cell_return chosen
  have beforeRead : CoreAllocationHistory.Steps G 28 (CoreMachine.initial G) e28.state :=
    produced.actual.trans request_segment.actual_steps
  have throughRead : CoreAllocationHistory.Steps G 29 (CoreMachine.initial G) e29.state :=
    .snoc beforeRead read_actual.1
  exact ⟨⟨readBind,demand,root,chosen,⟨rfl⟩,finalSite,⟨rfl⟩,finalBound,choiceRaw,releaseRaw,
    throughRead.trans remaining_steps⟩⟩

structure InstalledCompletion where
  second : InstalledSecondBeta
  completion : Completion second

/-- No-input original rich initial35 producer. -/
theorem installed_completion : Nonempty InstalledCompletion := by
  obtain ⟨second⟩ := installed_second_beta
  obtain ⟨completion⟩ := completion_current second
  exact ⟨⟨second,completion⟩⟩

#print axioms installed_completion
#print axioms completion_current
#print axioms read_bind_current
end Original

#print axioms choice_checks_at
#print axioms true_integer_branch
#print axioms integer_cell_return
end Ash.OneShot.CoreCallableOriginalReadCompletionCurrent
