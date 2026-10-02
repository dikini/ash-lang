import CoreCallableGeneralStrictFocus
namespace Ash.OneShot.CoreCallableStrictFocusConsumers
open CoreSyntax CoreMachine CoreTranslation CoreTranslationFuel CoreValueRelation CoreStrictFrames CoreStrictStack
open ScopedExpressions ScopedExecution CoreCallableGeneralHistory CoreCallableGeneratedChronology
open CoreCallableReachableResume CoreCallableSiteLineage CoreCallableInitialChronology CoreCallableGeneralStrictFocus

/-- Actual returned-head relation. The original saved map and right site are
indices, not new inputs; full after PlainData remains validated metadata. -/
structure ReturnedReady {kind : PairApplication} {original : Endpoint graph}
    (ready : EntryReady kind original) (receipt : EntryReceipt ready) (current : Endpoint graph) where
  value : CoreMachine.Value
  code : Code
  runtimeScope : Execution.Scope
  operand : ValueRel graph current.owners current.state.heap value code
  extension : HeapExtends original.state.heap current.state.heap
  afterPlain : PlainData
  context : afterPlain.context = kind.rightContext code
  sameScope : afterPlain.scope = ready.plain.scope
  notValue : ¬ ready.rightCode.IsValue
  control : current.state.control = .returned value
  empty : EmptyFocus current code runtimeScope
  physical : current.physical = kind.leftFrame ready.right ready.environment :: original.physical
  lexical : current.lexical = .push (.plain ready.plain) original.lexical
  history : HEq current.history
    (GeneralHistory.push (.ordinary (receipt.saved.related.heap_weaken extension))
      (by cases kind <;> trivial) (original.history.heap_weaken extension))

private theorem right_frame {kind : PairApplication} {original current : Endpoint graph}
    {ready : EntryReady kind original} {receipt : EntryReceipt ready} (input : ReturnedReady ready receipt current) :
    PlainFrameRel graph original.owners current.state.heap (kind.rightFrame input.value) input.afterPlain := by
  change FrameRel graph original.owners current.state.heap _ input.afterPlain.context
  rw [input.context]
  cases kind with
  | pair => exact .tupleRight (input.operand.owner_transport original.owners)
  | application => exact .applyArgument (input.operand.owner_transport original.owners)

noncomputable def right_after {kind : PairApplication} {original current : Endpoint graph}
    {ready : EntryReady kind original} {receipt : EntryReceipt ready} (input : ReturnedReady ready receipt current) : Endpoint graph := {
  state := {current.state with
    control := .evaluate ready.right ready.environment
    frames := kind.rightFrame input.value :: original.physical}
  focus := ⟨ready.rightCode,input.afterPlain.scope,.nil⟩
  owners := original.owners
  maps := []
  physical := kind.rightFrame input.value :: original.physical
  lexical := .push (.plain input.afterPlain) original.lexical
  history := .push (.ordinary (right_frame input)) (by cases kind <;> trivial) (original.history.heap_weaken input.extension)
  frames := rfl }

theorem right_actual {kind : PairApplication} {original current : Endpoint graph}
    {ready : EntryReady kind original} {receipt : EntryReceipt ready} (input : ReturnedReady ready receipt current) :
    CoreMachine.next graph current.state = .stepped (right_after input).state := by
  have frames : current.state.frames = kind.leftFrame ready.right ready.environment :: original.physical := by
    simpa [input.empty.maps,framesOf,input.physical] using current.frames
  have beforeSame : {current.state with control := .returned input.value,frames := kind.leftFrame ready.right ready.environment :: original.physical} = current.state := by
    rw [← input.control,← frames]
  have next : CoreMachine.next graph {current.state with control := .returned input.value,frames := kind.leftFrame ready.right ready.environment :: original.physical} =
      .stepped {current.state with control := .evaluate ready.right ready.environment,frames := kind.rightFrame input.value :: original.physical} := by
    cases kind <;> rfl
  simpa only [beforeSame,right_after] using next

theorem right_raw {kind : PairApplication} {original current : Endpoint graph}
    {ready : EntryReady kind original} {receipt : EntryReceipt ready} (input : ReturnedReady ready receipt current) :
    RawStep ⟨input.code,input.runtimeScope,.push (.plain ready.plain) original.lexical⟩
      ⟨kind.code input.code ready.rightCode,ready.plain.scope,original.lexical⟩ [] [] ∧
    RawStep ⟨kind.code input.code ready.rightCode,ready.plain.scope,original.lexical⟩
      ⟨ready.rightCode,input.afterPlain.scope,.push (.plain input.afterPlain) original.lexical⟩ [] [] := by
  have plug := RawStep.plug ready.plain input.code input.operand.closed input.runtimeScope original.lexical
  cases kind with
  | pair =>
    have first : RawStep ⟨input.code,input.runtimeScope,.push (.plain ready.plain) original.lexical⟩
        ⟨.pair input.code ready.rightCode,ready.plain.scope,original.lexical⟩ [] [] := by
      simpa only [ready.context,PairApplication.leftContext,Context.plug] using plug
    refine ⟨first,?_⟩
    rw [← input.sameScope]
    exact .focus input.afterPlain (by rw [input.context]; exact .pairRight input.operand.closed.1 input.notValue) original.lexical
  | application =>
    have actual := application_return_function ready.rightTranslated (receipt.rightClosing.heap_weaken input.extension)
      (input.operand.owner_transport original.owners) input.notValue ready.plain input.afterPlain
      ready.context input.context input.sameScope input.runtimeScope original.physical original.lexical
    exact ⟨actual.2.1,actual.2.2.1⟩

theorem right_positive {kind : PairApplication} {original current : Endpoint graph}
    {ready : EntryReady kind original} {receipt : EntryReceipt ready} (input : ReturnedReady ready receipt current) :
    CoreUnwindRelation.Positive current.point.machine (right_after input).point.machine [] [] := by
  have before : current.point.machine = .eval ⟨input.code,input.runtimeScope,.push (.plain ready.plain) original.lexical⟩ := by
    simp only [Endpoint.point,input.empty.focus,CoreCleanupRunFrames.attach,Stack.append,input.lexical]
  rw [before]
  change CoreUnwindRelation.Positive _ (.eval ⟨ready.rightCode,input.afterPlain.scope,.push (.plain input.afterPlain) original.lexical⟩) [] []
  have allowed : LexicalUnwind.ordinary input.code := CoreUnwindRelation.raw_without_close_ordinary (right_raw input).1 (by simp)
  exact .next (.evaluate (right_raw input).1 allowed) (.one (.evaluate (right_raw input).2 (by cases kind <;> trivial)))

theorem right_sites {kind : PairApplication} {original current : Endpoint graph}
    {ready : EntryReady kind original} {receipt : EntryReceipt ready} (input : ReturnedReady ready receipt current) : SiteOrigins (right_after input) := by
  refine ⟨CoreCallableCleanupOrigins.CurrentScopeOrigin.canonical receipt.saved.origin,?_,?_,?_⟩
  · simp [MapsCanonical,right_after]
  · simpa only [EvaluatingSite,right_after,input.sameScope] using receipt.rightSite
  · simp [SavedRightSites,right_after]

theorem right_scopes {kind : PairApplication} {original current : Endpoint graph}
    {ready : EntryReady kind original} {receipt : EntryReceipt ready} (input : ReturnedReady ready receipt current) : EvaluatedScopeOrigins (right_after input) := by
  refine ⟨?_,?_⟩
  · have sameTail := receipt.saved.origin.prepend_plain (right_frame input)
    simpa only [EvaluatingScopeOrigin,right_after,input.sameScope] using sameTail
  · simp [SavedMapScopeOrigins,right_after]

noncomputable def pair_right {original current : Endpoint graph} {ready : EntryReady .pair original}
    {receipt : EntryReceipt ready} (input : ReturnedReady ready receipt current) : Endpoint graph := right_after input
noncomputable def application_argument {original current : Endpoint graph} {ready : EntryReady .application original}
    {receipt : EntryReceipt ready} (input : ReturnedReady ready receipt current) : Endpoint graph := right_after input

/-- Honest original chronological pastRun; no origin or CoreSteps seeds. -/
inductive Prefix (graph : Graph) : Endpoint graph → Type where
  | initial (run : InitialChronology input current count created discharged) : Prefix graph current
  | generated (ordered : Postorder graph)
      (run : Generated start current count created discharged) : Prefix graph current

theorem Prefix.ordered (pastRun : Prefix graph current) : Postorder graph := by
  cases pastRun with
  | @initial code input current count created discharged run => exact checkShape_postorder graph input.shape
  | generated ordered run => exact ordered

theorem Prefix.sites (pastRun : Prefix graph current) : SiteOrigins current := by
  cases pastRun with
  | initial run => exact run.site_origins
  | generated ordered run => exact run.current_site_origins ordered

theorem Prefix.scopes (pastRun : Prefix graph current) : EvaluatedScopeOrigins current := by
  cases pastRun with
  | initial run => exact run.scope_origins
  | generated ordered run => exact run.current_evaluating_scope

theorem Prefix.receipt (pastRun : Prefix graph original) (ready : EntryReady kind original) : EntryReceipt ready :=
  installed pastRun.ordered pastRun.sites pastRun.scopes ready

private noncomputable def initial_base {graph : Graph} {code : Code} {input : InitialInput graph code}
    {current : Endpoint graph} {count : Nat} {created discharged : List Owner}
    (_run : InitialChronology input current count created discharged) : Endpoint graph := initial_endpoint input
private noncomputable def generated_base {graph : Graph}
    {start : CoreCallableRunningOccurrence.RunningStartPast graph cleanupOwners action environment data savedValue savedCode physical target}
    {current : Endpoint graph} {count : Nat} {created discharged : List Owner}
    (_run : Generated start current count created discharged) : Endpoint graph := started start
private def initial_info (_run : InitialChronology input current count created discharged) : Nat × List Owner × List Owner :=
  ⟨count,created,discharged⟩
private def generated_info (_run : Generated start current count created discharged) : Nat × List Owner × List Owner :=
  ⟨count,created,discharged⟩

noncomputable def Prefix.base (pastRun : Prefix graph current) : Endpoint graph :=
  match pastRun with | .initial run => initial_base run | .generated _ run => generated_base run

def Prefix.info (pastRun : Prefix graph current) : Nat × List Owner × List Owner :=
  match pastRun with | .initial run => initial_info run | .generated _ run => generated_info run

theorem Prefix.core (pastRun : Prefix graph current) :
    CoreAllocationHistory.Steps graph pastRun.info.1 pastRun.base.state current.state := by
  cases pastRun with
  | initial run => exact run.actual_steps
  | generated ordered run => exact run.core_steps

theorem Prefix.trace (pastRun : Prefix graph current) :
    CoreUnwindRelation.Trace pastRun.base.point.machine current.point.machine pastRun.info.2.1 pastRun.info.2.2 := by
  cases pastRun with
  | initial run => exact run.target_trace
  | generated ordered run => exact run.target_trace

private theorem steps_append {before middle after : CoreMachine.State}
    (first : CoreAllocationHistory.Steps graph left before middle)
    (second : CoreAllocationHistory.Steps graph right middle after) :
    CoreAllocationHistory.Steps graph (left+right) before after := by
  induction second with
  | refl => simpa using first
  | snoc earlier step ih => simpa [Nat.add_assoc] using CoreAllocationHistory.Steps.snoc (ih first) step

/-- One saved-right episode. Exact computed entry, then only existing named
outputs; no arbitrary matching/result/source-successor constructor. -/
inductive Middle (pastRun : Prefix graph original) (ready : EntryReady kind original) :
    Endpoint graph → Nat → List Owner → List Owner → Type where
  | entered : Middle pastRun ready (entry_after ready (pastRun.receipt ready)) 1 [] []
  | covered (earlier : Middle pastRun ready before count created discharged)
      (operation : Operation before after added removed) :
      Middle pastRun ready after (count+1) (created++added) (removed++discharged)

theorem Middle.core {graph : Graph} {kind : PairApplication} {original current : Endpoint graph}
    {pastRun : Prefix graph original} {ready : EntryReady kind original}
    (run : Middle pastRun ready current count created discharged) :
    CoreAllocationHistory.Steps graph count original.state current.state := by
  induction run with
  | entered => exact .snoc (.refl _) (entry_actual ready (pastRun.receipt ready))
  | covered earlier operation ih => exact .snoc ih operation.actual.1

theorem Middle.trace {graph : Graph} {kind : PairApplication} {original current : Endpoint graph}
    {pastRun : Prefix graph original} {ready : EntryReady kind original}
    (run : Middle pastRun ready current count created discharged) :
    CoreUnwindRelation.Trace original.point.machine current.point.machine created discharged := by
  induction run with
  | entered => exact (entry_positive ready (pastRun.receipt ready)).trace
  | covered earlier operation ih => exact ih.append operation.actual.2.target_trace

theorem Middle.sites {graph : Graph} {kind : PairApplication} {original current : Endpoint graph}
    {pastRun : Prefix graph original} {ready : EntryReady kind original}
    (run : Middle pastRun ready current count created discharged) : SiteOrigins current := by
  induction run with
  | entered => exact entry_sites ready (pastRun.receipt ready)
  | covered earlier operation ih => exact operation.site_origins pastRun.ordered ih

theorem Middle.scopes {graph : Graph} {kind : PairApplication} {original current : Endpoint graph}
    {pastRun : Prefix graph original} {ready : EntryReady kind original}
    (run : Middle pastRun ready current count created discharged) : EvaluatedScopeOrigins current := by
  induction run with
  | entered => exact entry_scopes ready (pastRun.receipt ready)
  | covered earlier operation ih => exact operation.evaluating_scope ih

/-- The actual right transition consumes the episode's own produced receipt. -/
theorem complete_episode {graph : Graph} {kind : PairApplication} {original current : Endpoint graph}
    {pastRun : Prefix graph original} {ready : EntryReady kind original}
    (run : Middle pastRun ready current count created discharged)
    (input : ReturnedReady ready (pastRun.receipt ready) current) :
    CoreAllocationHistory.Steps graph (count+1) original.state (right_after input).state ∧
    CoreUnwindRelation.Trace original.point.machine (right_after input).point.machine created discharged :=
  ⟨.snoc run.core (right_actual input),by simpa using run.trace.append (right_positive input).trace⟩

theorem Middle.accounting {graph : Graph} {kind : PairApplication} {original current : Endpoint graph}
    {pastRun : Prefix graph original} {ready : EntryReady kind original}
    (run : Middle pastRun ready current count created discharged) :
    (original.point.machine.stack.erase.owners ++ created).Perm
      (current.point.machine.stack.erase.owners ++ discharged) := by
  induction run with
  | entered => exact CoreGeneralCaptureResume.positive_accounting (entry_positive ready (pastRun.receipt ready))
  | covered earlier operation ih =>
    have edge := operation.actual.2.accounting
    apply List.perm_iff_count.mpr
    intro owner
    have firstCount := ih.count_eq owner
    have edgeCount := edge.count_eq owner
    simp only [List.count_append] at firstCount edgeCount ⊢
    omega

theorem complete_accounting {graph : Graph} {kind : PairApplication} {original current : Endpoint graph}
    {pastRun : Prefix graph original} {ready : EntryReady kind original}
    (run : Middle pastRun ready current count created discharged)
    (input : ReturnedReady ready (pastRun.receipt ready) current) :
    (original.point.machine.stack.erase.owners ++ created).Perm
      ((right_after input).point.machine.stack.erase.owners ++ discharged) := by
  have edge := CoreGeneralCaptureResume.positive_accounting (right_positive input)
  apply List.perm_iff_count.mpr
  intro owner
  have firstCount := run.accounting.count_eq owner
  have edgeCount := edge.count_eq owner
  simp only [List.count_append,List.count_nil] at firstCount edgeCount ⊢
  omega

theorem complete_original_prefix {graph : Graph} {kind : PairApplication} {original current : Endpoint graph}
    {pastRun : Prefix graph original} {ready : EntryReady kind original}
    (run : Middle pastRun ready current count created discharged)
    (input : ReturnedReady ready (pastRun.receipt ready) current) :
    CoreAllocationHistory.Steps graph (pastRun.info.1+(count+1)) pastRun.base.state (right_after input).state ∧
    CoreUnwindRelation.Trace pastRun.base.point.machine (right_after input).point.machine
      (pastRun.info.2.1++created) (discharged++pastRun.info.2.2) :=
  ⟨steps_append pastRun.core (complete_episode run input).1,
    pastRun.trace.append (complete_episode run input).2⟩

#print axioms right_actual
#print axioms right_raw
#print axioms right_positive
#print axioms right_sites
#print axioms right_scopes
#print axioms Prefix.sites
#print axioms Prefix.scopes
#print axioms Middle.core
#print axioms Middle.trace
#print axioms Middle.sites
#print axioms Middle.scopes
#print axioms complete_episode
#print axioms Middle.accounting
#print axioms complete_accounting
#print axioms Prefix.core
#print axioms Prefix.trace
#print axioms complete_original_prefix
end Ash.OneShot.CoreCallableStrictFocusConsumers
