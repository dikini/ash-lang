import CoreCallableRestoredBindConsumers
import CoreCallableGeneratedCleanupCompletion
import CoreCallableGeneratedTicketBound
import ScopedPortRetained
namespace Ash.OneShot.CoreCallableRestoredBindContinuationOrigins
open CoreSyntax CoreMachine CoreTranslation CoreValueRelation CoreStrictFrames CoreStrictStack
open CoreCaptureEntry CoreGeneralStack CoreRequestFrames
open ScopedExpressions ScopedExecution CoreCallableGeneralHistory CoreCallableGeneratedChronology
open CoreCallableReachableResume CoreCallableSiteLineage CoreCallableCallerBarriers
open CoreCallableGeneralStrictFocus CoreCallableStrictFocusConsumers CoreCallableStrictCaptureOrigins
open CoreCallableStrictCallerHeadCompatibility CoreCallableStrictOutsideHeadOrigins CoreCallableCleanupReachableTransport

private theorem and_rec_apply {P Q : Prop} {α : Sort u} (f : P → Q → α) (h : P ∧ Q) :
    And.rec f h = f h.left h.right := by cases h; rfl

/-- Append only scans a suffix after a missing static owner, preserving the
nearest consumed occurrence as a barrier. -/
theorem findOwner_append (handler owner : Nat) (first second : List CoreMachine.Frame) :
    CoreMachine.findOwner handler owner (first ++ second) =
      match CoreMachine.findOwner handler owner first with
      | .ok cut => .ok {cut with outside := cut.outside ++ second}
      | .error (.missingOwner _ _) => (CoreMachine.findOwner handler owner second).map
          (fun cut => {cut with inside := first ++ cut.inside})
      | .error error => .error error := by
  induction first with
  | nil =>
    cases found : CoreMachine.findOwner handler owner second <;> simp [CoreMachine.findOwner,found,Except.map]
  | cons frame rest ih =>
    cases frame
    case clauseBoundary candidate selected occurrence dynamicTicket saved =>
      by_cases matching : handler == candidate && owner == selected
      · cases saved <;> simp [CoreMachine.findOwner,matching]
      · simp only [List.cons_append,CoreMachine.findOwner,matching,Bool.false_eq_true,↓reduceIte]
        rw [ih]
        cases found : CoreMachine.findOwner handler owner rest with
        | ok cut => simp only [Bind.bind,Except.bind,Pure.pure,Except.pure]
        | error error => cases error <;> simp only [Bind.bind,Except.bind,Pure.pure,Except.pure,Except.map] <;> cases CoreMachine.findOwner handler owner second <;> rfl
    all_goals
      simp only [List.cons_append,CoreMachine.findOwner]
      rw [ih]
      cases found : CoreMachine.findOwner handler owner rest with
      | ok cut => simp only [Bind.bind,Except.bind,Pure.pure,Except.pure]
      | error error => cases error <;> simp only [Bind.bind,Except.bind,Pure.pure,Except.pure,Except.map] <;> cases CoreMachine.findOwner handler owner second <;> rfl
private theorem retained_missing (history : RetainedHistory graph heap physical target)
    (handler owner : Nat) : CoreMachine.findOwner handler owner physical = .error (.missingOwner handler owner) := by
  induction history with
  | nil => rfl
  | plain frame tail ih | handler installation header tail ih | spent installation header tail ih | retiring installation header tail ih => exact ih
  | cell frame tail ih | armed installed tail ih => simp only [CoreMachine.findOwner,ih,Bind.bind,Except.bind]
  | live installation header saved tail ihSaved ihTail =>
    rw [findOwner_append,ihSaved]
    simp only [ihTail,Except.map]

private theorem pushed_missing (frame : PushCarrier graph owners heap core target)
    (handler owner : Nat) : CoreMachine.findOwner handler owner [core] = .error (.missingOwner handler owner) := by
  cases frame with
  | ordinary related =>
    rename_i plain
    change FrameRel graph owners heap core plain.context at related
    generalize same : plain.context = context at related
    cases related <;> rfl
  | initializer related => cases related; rfl
  | request related => cases related; rfl
  | resume related => cases related; rfl
  | cleanup related => cases related; rfl
  | boundary related => cases related <;> rfl

/-- A missing result certifies actual absence; blocked certifies refusal to
scan past the nearest matching spent frame. Found carries the full receipt. -/
def SearchValid (search : OwnerSearch graph heap handler owner physical target) : Prop :=
  match search with
  | .found _ => True
  | .missing _ => CoreMachine.findOwner handler owner physical = .error (.missingOwner handler owner)
  | .blocked => CoreMachine.findOwner handler owner physical = .error (.consumedOwner handler owner)

private theorem valid_prepend (search : OwnerSearch graph heap handler owner physical target)
    (valid : SearchValid search) (leading : GeneralHistory graph heap leadingPhysical leadingTarget)
    (pass : ∀ rest cut, CoreMachine.findOwner handler owner rest = .ok cut →
      CoreMachine.findOwner handler owner (leadingPhysical ++ rest) = .ok {cut with inside := leadingPhysical ++ cut.inside})
    (missing : CoreMachine.findOwner handler owner leadingPhysical = .error (.missingOwner handler owner)) :
    SearchValid (search.prepend leading pass) := by
  cases search with
  | found location => trivial
  | missing restPass =>
    change CoreMachine.findOwner handler owner (leadingPhysical ++ physical) = _
    rw [findOwner_append,missing]
    simpa only [SearchValid,Except.map] using congrArg (Except.map (fun cut => {cut with inside := leadingPhysical ++ cut.inside})) valid
  | blocked =>
    change CoreMachine.findOwner handler owner (leadingPhysical ++ physical) = _
    rw [findOwner_append,missing]
    simpa only [SearchValid,Except.map] using congrArg (Except.map (fun cut => {cut with inside := leadingPhysical ++ cut.inside})) valid

private theorem pass_missing (missing : CoreMachine.findOwner handler owner leadingPhysical = .error (.missingOwner handler owner)) :
    ∀ rest cut, CoreMachine.findOwner handler owner rest = .ok cut →
      CoreMachine.findOwner handler owner (leadingPhysical ++ rest) = .ok {cut with inside := leadingPhysical ++ cut.inside} := by
  intro rest cut found
  rw [findOwner_append,missing]
  simp only [found,Except.map]

private theorem search_rec_eq (search next : OwnerSearch graph heap handler owner physical target)
    (picked : search = next) (foundF : OwnerLocation graph heap handler owner physical target → α)
    (missingF : (∀ rest cut, CoreMachine.findOwner handler owner rest = .ok cut →
      CoreMachine.findOwner handler owner (physical ++ rest) = .ok {cut with inside := physical ++ cut.inside}) → α)
    (blockedF : α) :
    OwnerSearch.rec (motive := fun next => search = next → α)
      (fun location _ => foundF location) (fun pass _ => missingF pass) (fun _ => blockedF) search rfl =
    OwnerSearch.rec (motive := fun _ => α) foundF missingF blockedF next := by
  cases picked
  cases search <;> rfl

private theorem search_append_eq (first : GeneralHistory graph heap firstPhysical firstTarget)
    (second : GeneralHistory graph heap secondPhysical secondTarget) :
    owner_search (first.append second) handler owner =
      match owner_search first handler owner with
      | .found location => .found (location.suffix second)
      | .missing pass => (owner_search second handler owner).prepend first pass
      | .blocked => .blocked := by
  cases picked : owner_search first handler owner <;>
    rw [owner_search.eq_def] <;>
    dsimp only
  all_goals exact (search_rec_eq _ _ picked
    (fun location => .found (location.suffix second))
    (fun pass => (owner_search second handler owner).prepend first pass) .blocked)

/-- Completeness and refusal classification are proved over the SAME full
history; no physical-only equality selects another original receipt. -/
theorem owner_search_valid (history : GeneralHistory graph heap physical target) (handler owner : Nat) :
    SearchValid (owner_search history handler owner) := by
  induction history with
  | nil => rfl
  | retained history => exact retained_missing history handler owner
  | push frame ordinary tail ih =>
    rw [owner_search]
    simpa only [Stack.append] using valid_prepend _ ih (.push frame ordinary .nil)
      (pass_missing (pushed_missing frame handler owner)) (pushed_missing frame handler owner)
  | handler installation header tail ih =>
    rw [owner_search]
    simpa only [Stack.append] using valid_prepend _ ih (.handler installation header .nil)
      (pass_missing (pushed_missing (.boundary header) handler owner)) (pushed_missing (.boundary header) handler owner)
  | running receipt => rfl
  | unwinding installed => rfl
  | closing core target scope => rfl
  | @live owners otherHandler otherOwner occurrence dynamicTicket captured data capturedTarget physical target result installation header saved tail ihSaved ih =>
    rw [owner_search]
    by_cases same : handler = otherHandler ∧ owner = otherOwner
    · obtain ⟨rfl,rfl⟩ := same
      with_unfolding_all
        simp only [SearchValid, eq_self, and_self, ↓reduceDIte]
        rw [and_rec_apply]
        trivial
    · have missing : CoreMachine.findOwner handler owner [.clauseBoundary otherHandler otherOwner occurrence dynamicTicket (some captured)] = .error (.missingOwner handler owner) := by
        simp only [CoreMachine.findOwner,Bool.and_eq_true,beq_iff_eq,same,↓reduceIte]
        rfl
      simpa only [same,↓reduceDIte,Stack.append] using valid_prepend _ ih (.live installation header saved .nil) (pass_missing missing) missing
  | @spent owners otherHandler otherOwner occurrence dynamicTicket captured data physical target installation header tail ih =>
    rw [owner_search]
    by_cases same : handler = otherHandler ∧ owner = otherOwner
    · obtain ⟨rfl,rfl⟩ := same
      simp [SearchValid,CoreMachine.findOwner]
    · have missing : CoreMachine.findOwner handler owner [.clauseBoundary otherHandler otherOwner occurrence dynamicTicket none] = .error (.missingOwner handler owner) := by
        simp only [CoreMachine.findOwner,Bool.and_eq_true,beq_iff_eq,same,↓reduceIte]
        rfl
      simpa only [same,↓reduceDIte,Stack.append] using valid_prepend _ ih (.spent installation header .nil) (pass_missing missing) missing
  | @append firstPhysical firstTarget secondPhysical secondTarget first second ihFirst ihSecond =>
    rw [search_append_eq]
    cases search : owner_search first handler owner with
    | found location => trivial
    | blocked =>
      change CoreMachine.findOwner handler owner (_ ++ _) = _
      rw [findOwner_append]
      have blocked : CoreMachine.findOwner handler owner firstPhysical = .error (.consumedOwner handler owner) := by simpa only [search,SearchValid] using ihFirst
      rw [blocked]
    | missing pass =>
      have missing : CoreMachine.findOwner handler owner firstPhysical = .error (.missingOwner handler owner) := by simpa only [search,SearchValid] using ihFirst
      simpa only [search] using valid_prepend _ ihSecond first pass missing

/-- A produced original OwnerPath lookup forces the computed search to return
its complete history-derived location, not a caller-supplied selection. -/
theorem owner_search_complete (history : GeneralHistory graph heap physical target)
    (found : CoreMachine.findOwner handler owner physical = .ok cut) :
    ∃ location, owner_search history handler owner = .found location := by
  have valid := owner_search_valid history handler owner
  cases search : owner_search history handler owner with
  | found location => exact ⟨location,rfl⟩
  | missing pass => simp only [search,SearchValid] at valid; rw [valid] at found; cases found
  | blocked => simp only [search,SearchValid] at valid; rw [valid] at found; cases found

/-- Actual absence determines the missing search constructor. This lets a
computed nonmatching kept prefix retain original suffix selection metadata. -/
theorem owner_search_missing (history : GeneralHistory graph heap physical target)
    (missing : CoreMachine.findOwner handler owner physical = .error (.missingOwner handler owner)) :
    ∃ pass, owner_search history handler owner = .missing pass := by
  have valid := owner_search_valid history handler owner
  cases search : owner_search history handler owner with
  | missing pass => exact ⟨pass,rfl⟩
  | found location =>
    have found := (owner_search_lookup history search).1
    rw [missing] at found
    cases found
  | blocked =>
    simp only [search,SearchValid] at valid
    rw [missing] at valid
    cases valid

/-- Stable full captured receipt; current front/outside reassociation is
excluded, while original installation and saved Type history are retained. -/
structure CapturedReceipt (graph : Graph) (heap : CoreMachine.Heap) (handler owner : Nat) where
  owners : OwnerMap
  occurrence : Nat
  dynamicTicket : Nat
  captured : List CoreMachine.Frame
  data : HandlerData
  result : Ty
  capturedTarget : Stack
  installation : GeneralClausePast graph owners handler owner occurrence dynamicTicket captured data
  header : OwnerHeader graph owners heap handler owner occurrence data
  history : GeneralHistory graph heap captured capturedTarget

def capturedReceipt (location : OwnerLocation graph heap handler owner physical target) :
    CapturedReceipt graph heap handler owner :=
  ⟨location.owners,location.occurrence,location.dynamicTicket,location.captured,location.data,
    location.result,location.capturedTarget,location.installation,location.header,location.capturedHistory⟩

theorem capturedReceipt_prepend (location : OwnerLocation graph heap handler owner physical target)
    (leading : GeneralHistory graph heap leadingPhysical leadingTarget)
    (pass : PhysicalPass handler owner leadingPhysical) :
    capturedReceipt (location.prepend leading pass) = capturedReceipt location := rfl

theorem capturedReceipt_suffix (location : OwnerLocation graph heap handler owner physical target)
    (last : GeneralHistory graph heap lastPhysical lastTarget) :
    capturedReceipt (location.suffix last) = capturedReceipt location := rfl

/-- A computed missing leading history changes only the current front. The
original saved capture and installation are transported as an OUTPUT. -/
theorem owner_search_append_missing
    (leading : GeneralHistory graph heap leadingPhysical leadingTarget)
    (history : GeneralHistory graph heap physical target)
    (missing : CoreMachine.findOwner handler owner leadingPhysical = .error (.missingOwner handler owner))
    (picked : owner_search history handler owner = .found original) :
    ∃ location, owner_search (leading.append history) handler owner = .found location ∧
      capturedReceipt location = capturedReceipt original := by
  obtain ⟨pass,computed⟩ := owner_search_missing leading missing
  rw [search_append_eq,computed,picked]
  exact ⟨original.prepend leading pass,rfl,rfl⟩

def searchedCapture (search : OwnerSearch graph heap handler owner physical target) :
    Option (CapturedReceipt graph heap handler owner) :=
  match search with | .found location => some (capturedReceipt location) | _ => none

/-- Original capture metadata are independent of every computed missing
leading history, even where that history is an opaque chosen rich receipt. -/
theorem searchedCapture_append_missing
    (leading : GeneralHistory graph heap leadingPhysical leadingTarget)
    (history : GeneralHistory graph heap physical target)
    (missing : CoreMachine.findOwner handler owner leadingPhysical = .error (.missingOwner handler owner)) :
    searchedCapture (owner_search (leading.append history) handler owner) =
      searchedCapture (owner_search history handler owner) := by
  obtain ⟨pass,computed⟩ := owner_search_missing leading missing
  rw [search_append_eq,computed]
  cases owner_search history handler owner <;> rfl

/-- A live original occurrence stays live across a represented bind-tail
replacement. The selected clause's own metadata and caller-front proof are
retained; this does not turn a consumed current scope into a resumable one. -/
theorem live_path_restored
    (path : OwnerPath handler owner occurrence callerTicket (some saved) physical front outsideTail)
    (same : physical = kept ++ outside)
    (ready : CoreCallableRestoredBindOrigins.BindScopeReady graph
      (⟨handler,owner,ticket graph owner⟩::callerTail)
      (.ticket (ticket graph owner) callerTicket) kept selectedOwners data.scope)
    (past : GeneralClausePast graph selectedOwners selectedHandler selectedOwner selectedOccurrence selectedTicket captured data)
    {addedHistory : GeneralHistory graph heap addedPhysical addedTarget}
    (added : PassFront handler owner addedHistory) :
    ∃ nextFront nextTail, OwnerPath handler owner occurrence callerTicket (some saved)
      (kept ++ (addedPhysical ++ .clauseBoundary selectedHandler selectedOwner selectedOccurrence selectedTicket none :: outside))
      nextFront nextTail := by
  cases ready with
  | inside checked =>
    have bound : front.length < kept.length := by
      by_cases inside : front.length < kept.length
      · exact inside
      obtain ⟨_,_,_,miss⟩ := CoreCallableOutsideOrigin.OwnerPath.drop_prefix path same (Nat.le_of_not_gt inside)
      simp [insideCheck,miss] at checked
    obtain ⟨prefixTail,preserved⟩ := OwnerPath.take_prefix path same bound
    exact ⟨_,_,OwnerPath.append_suffix preserved _⟩
  | outside unique metadata position =>
    obtain ⟨remaining,_,restored⟩ := original_owner_path_restored path same position past unique metadata added
    exact ⟨_,_,by simpa only [List.append_assoc,List.singleton_append] using restored⟩

/-- Full computed owner location from a retained live occurrence. This internal
adapter supplies no picked location, installation, or future successor. -/
noncomputable def owner_from_live_path
    (history : GeneralHistory graph heap physical target)
    (path : OwnerPath handler owner occurrence dynamicTicket (some saved) physical front outside) :
    OwnerLocation graph heap handler owner physical target :=
  Classical.choose (owner_search_complete history path.lookup)

theorem owner_from_live_path_picked
    (history : GeneralHistory graph heap physical target)
    (path : OwnerPath handler owner occurrence dynamicTicket (some saved) physical front outside) :
    owner_search history handler owner = .found (owner_from_live_path history path) :=
  Classical.choose_spec (owner_search_complete history path.lookup)

theorem owner_from_live_path_ticket
    (history : GeneralHistory graph heap physical target)
    (path : OwnerPath handler owner occurrence dynamicTicket (some saved) physical front outside) :
    (owner_from_live_path history path).dynamicTicket = dynamicTicket := by
  have actual := (owner_search_lookup history (owner_from_live_path_picked history path)).1
  have same := Except.ok.inj (actual.symm.trans path.lookup)
  exact congrArg CoreMachine.OwnerCut.ticket same

/-- Selection is the full unique output of this history's search, including
its original installation and captured Type history, not only physical data. -/
theorem owner_from_live_path_eq
    (history : GeneralHistory graph heap physical target)
    (path : OwnerPath handler owner occurrence dynamicTicket (some saved) physical front outside)
    (selected : owner_search history handler owner = .found original) :
    owner_from_live_path history path = original := by
  have produced := owner_from_live_path_picked history path
  exact OwnerSearch.found.inj (produced.symm.trans selected)


/-- Missing and consumed barriers remain distinct while preserving all
Type-valued original capture data. -/
def searchOutcome (search : OwnerSearch graph heap handler owner physical target) :
    Except Bool (CapturedReceipt graph heap handler owner) :=
  match search with
  | .found location => .ok (capturedReceipt location)
  | .missing _ => .error false
  | .blocked => .error true

private theorem searchOutcome_prepend (search : OwnerSearch graph heap handler owner physical target)
    (leading : GeneralHistory graph heap leadingPhysical leadingTarget) (pass : PhysicalPass handler owner leadingPhysical) :
    searchOutcome (search.prepend leading pass) = searchOutcome search := by
  cases search <;> rfl

private theorem searchOutcome_append (first : GeneralHistory graph heap firstPhysical firstTarget)
    (last : GeneralHistory graph heap lastPhysical lastTarget) (handler owner : Nat) :
    searchOutcome (owner_search (first.append last) handler owner) =
      match searchOutcome (owner_search first handler owner) with
      | .error false => searchOutcome (owner_search last handler owner)
      | other => other := by
  rw [search_append_eq]
  cases owner_search first handler owner with
  | found location => rfl
  | blocked => rfl
  | missing pass => exact searchOutcome_prepend _ _ _

/-- Removing the actual structural bind head preserves the full computed
capture receipt and the missing/consumed classification. -/
theorem searchOutcome_bind_below
    (member : CoreCallableRestoredBindOrigins.BindHead owners (.bind binder body environment) plain history below)
    (handler owner : Nat) :
    searchOutcome (owner_search history handler owner) =
      searchOutcome (owner_search below handler owner) := by
  induction member with
  | here related ordinary tail =>
    rw [owner_search]
    simpa only [Stack.append] using searchOutcome_prepend (owner_search tail handler owner)
      (.push (.ordinary related) ordinary .nil) (pass_missing (pushed_missing (.ordinary related) handler owner))
  | append first last below member ih =>
    rw [searchOutcome_append,searchOutcome_append,ih]
  | emptyPrefix leading member ih =>
    rw [searchOutcome_append,searchOutcome_append]
    obtain ⟨pass,computed⟩ := owner_search_missing leading (handler := handler) (owner := owner) rfl
    rw [computed]
    exact ih


theorem searchOutcome_live_here
    (installation : GeneralClausePast graph owners handler owner occurrence dynamicTicket captured data)
    (header : OwnerHeader graph owners heap handler owner occurrence data)
    (saved : GeneralHistory graph heap captured capturedTarget)
    (tail : GeneralHistory graph heap physical target) :
    searchOutcome (owner_search (.live (result := result) installation header saved tail) handler owner) =
      .ok ⟨owners,occurrence,dynamicTicket,captured,data,result,capturedTarget,installation,header,saved⟩ := by
  rw [owner_search]
  with_unfolding_all
    simp only [eq_self,and_self,↓reduceDIte]
    rw [and_rec_apply]
    rfl

private theorem searchOutcome_push (frame : PushCarrier graph owners heap core target) (ordinary)
    (tail : GeneralHistory graph heap physical lexical) (handler owner : Nat) :
    searchOutcome (owner_search (.push frame ordinary tail) handler owner) =
      searchOutcome (owner_search tail handler owner) := by
  rw [owner_search]
  simpa only [Stack.append] using searchOutcome_prepend (owner_search tail handler owner)
    (.push frame ordinary .nil) (pass_missing (pushed_missing frame handler owner))

private theorem searchOutcome_handler (installation : GeneralHandlerPast graph owners site environment data)
    (header : CoreEffectFrames.BoundaryRel graph owners heap (.handlerBoundary site environment data.activation) (.handler data))
    (tail : GeneralHistory graph heap physical lexical) (handler owner : Nat) :
    searchOutcome (owner_search (.handler installation header tail) handler owner) =
      searchOutcome (owner_search tail handler owner) := by
  rw [owner_search]
  simpa only [Stack.append] using searchOutcome_prepend (owner_search tail handler owner)
    (.handler installation header .nil) (pass_missing (pushed_missing (.boundary header) handler owner))

private theorem searchOutcome_live_ne
    (installation : GeneralClausePast graph owners otherHandler otherOwner occurrence dynamicTicket captured data)
    (header : OwnerHeader graph owners heap otherHandler otherOwner occurrence data)
    (saved : GeneralHistory graph heap captured capturedTarget)
    (tail : GeneralHistory graph heap physical target) (handler owner : Nat)
    (different : ¬ (handler = otherHandler ∧ owner = otherOwner)) :
    searchOutcome (owner_search (.live (result := result) installation header saved tail) handler owner) =
      searchOutcome (owner_search tail handler owner) := by
  rw [owner_search]
  simp only [different,↓reduceDIte]
  have missing : CoreMachine.findOwner handler owner [.clauseBoundary otherHandler otherOwner occurrence dynamicTicket (some captured)] = .error (.missingOwner handler owner) := by
    simp only [CoreMachine.findOwner,Bool.and_eq_true,beq_iff_eq,different,↓reduceIte]
    rfl
  simpa only [Stack.append] using searchOutcome_prepend (owner_search tail handler owner)
    (.live installation header saved .nil) (pass_missing missing)

private theorem searchOutcome_spent_ne
    (installation : GeneralClausePast graph owners otherHandler otherOwner occurrence dynamicTicket captured data)
    (header : OwnerHeader graph owners heap otherHandler otherOwner occurrence data)
    (tail : GeneralHistory graph heap physical target) (handler owner : Nat)
    (different : ¬ (handler = otherHandler ∧ owner = otherOwner)) :
    searchOutcome (owner_search (.spent installation header tail) handler owner) =
      searchOutcome (owner_search tail handler owner) := by
  rw [owner_search]
  simp only [different,↓reduceDIte]
  have missing : CoreMachine.findOwner handler owner [.clauseBoundary otherHandler otherOwner occurrence dynamicTicket none] = .error (.missingOwner handler owner) := by
    simp only [CoreMachine.findOwner,Bool.and_eq_true,beq_iff_eq,different,↓reduceIte]
    rfl
  simpa only [Stack.append] using searchOutcome_prepend (owner_search tail handler owner)
    (.spent installation header .nil) (pass_missing missing)

noncomputable def CapturedReceipt.heap_weaken
    (receipt : CapturedReceipt graph heap handler owner) (extension : HeapExtends heap larger) :
    CapturedReceipt graph larger handler owner :=
  ⟨receipt.owners,receipt.occurrence,receipt.dynamicTicket,receipt.captured,receipt.data,receipt.result,
    receipt.capturedTarget,receipt.installation,receipt.header.heap_weaken extension,
    receipt.history.heap_weaken extension⟩

/-- Heap growth transports original full Type history; it never substitutes a
physically equal saved stack. -/
theorem searchOutcome_heap_weaken (history : GeneralHistory graph heap physical target)
    (extension : HeapExtends heap larger) (handler owner : Nat) :
    searchOutcome (owner_search (history.heap_weaken extension) handler owner) =
      (searchOutcome (owner_search history handler owner)).map (fun receipt => receipt.heap_weaken extension) := by
  induction history with
  | nil => rfl
  | retained history => rfl
  | push frame ordinary tail ih =>
    simpa only [GeneralHistory.heap_weaken,searchOutcome_push] using ih
  | handler installation header tail ih =>
    simpa only [GeneralHistory.heap_weaken,searchOutcome_handler] using ih
  | running receipt => rfl
  | unwinding installed => rfl
  | closing core target scope => rfl
  | @live owners otherHandler otherOwner occurrence dynamicTicket captured data capturedTarget physical target result installation header saved tail ihSaved ih =>
    by_cases same : handler = otherHandler ∧ owner = otherOwner
    · obtain ⟨rfl,rfl⟩ := same
      simp only [GeneralHistory.heap_weaken]
      rw [owner_search,owner_search]
      with_unfolding_all
        simp only [eq_self,and_self,↓reduceDIte]
        rw [and_rec_apply,and_rec_apply]
        rfl
    · simpa only [GeneralHistory.heap_weaken,searchOutcome_live_ne _ _ _ _ _ _ same] using ih
  | @spent owners otherHandler otherOwner occurrence dynamicTicket captured data physical target installation header tail ih =>
    by_cases same : handler = otherHandler ∧ owner = otherOwner
    · obtain ⟨rfl,rfl⟩ := same
      simp only [GeneralHistory.heap_weaken]
      rw [owner_search,owner_search]
      with_unfolding_all simp only [eq_self,and_self,↓reduceDIte,searchOutcome,Except.map]
    · simpa only [GeneralHistory.heap_weaken,searchOutcome_spent_ne _ _ _ _ _ same] using ih
  | append first last ihFirst ihLast =>
    change searchOutcome (owner_search ((first.heap_weaken extension).append (last.heap_weaken extension)) handler owner) = _
    with_unfolding_all rw [searchOutcome_append,searchOutcome_append,ihFirst,ihLast]
    cases searchOutcome (owner_search first handler owner) with
    | ok receipt => rfl
    | error blocked => cases blocked <;> rfl


private theorem missing_append_parts
    (leading : GeneralHistory graph heap first firstTarget)
    (missing : CoreMachine.findOwner handler owner (first ++ last) = .error (.missingOwner handler owner)) :
    CoreMachine.findOwner handler owner first = .error (.missingOwner handler owner) ∧
      CoreMachine.findOwner handler owner last = .error (.missingOwner handler owner) := by
  have valid := owner_search_valid leading handler owner
  cases search : owner_search leading handler owner with
  | found location =>
    have found := (owner_search_lookup leading search).1
    rw [findOwner_append,found] at missing
    cases missing
  | blocked =>
    simp only [search,SearchValid] at valid
    change CoreMachine.findOwner handler owner first = .error (.consumedOwner handler owner) at valid
    rw [findOwner_append,valid] at missing
    cases missing
  | missing pass =>
    simp only [search,SearchValid] at valid
    change CoreMachine.findOwner handler owner first = .error (.missingOwner handler owner) at valid
    rw [findOwner_append,valid] at missing
    cases other : CoreMachine.findOwner handler owner last with
    | ok cut => simp only [other,Except.map] at missing; cases missing
    | error error =>
      simp only [other,Except.map] at missing
      cases missing
      exact ⟨valid,rfl⟩

private theorem searchOutcome_append_missing
    (leading : GeneralHistory graph heap leadingPhysical leadingTarget)
    (history : GeneralHistory graph heap physical target)
    (missing : CoreMachine.findOwner handler owner leadingPhysical = .error (.missingOwner handler owner)) :
    searchOutcome (owner_search (leading.append history) handler owner) =
      searchOutcome (owner_search history handler owner) := by
  obtain ⟨pass,computed⟩ := owner_search_missing leading missing
  rw [searchOutcome_append,computed]
  rfl

/-- A selected real physical handler's outside retains the same full H
capture output whenever its actual preceding physical prefix is H-missing.
Selection comes from this history's inventory, not a substituted receipt. -/
theorem searchOutcome_handler_after
    (history : GeneralHistory graph heap physical target)
    (selected : HandlerLocation graph heap physical target)
    (present : selected ∈ handler_locations history)
    (missing : CoreMachine.findOwner handler owner selected.inside = .error (.missingOwner handler owner)) :
    searchOutcome (owner_search history handler owner) =
      searchOutcome (owner_search selected.after handler owner) := by
  induction history with
  | nil | retained | running | unwinding | closing => simp only [handler_locations,List.not_mem_nil] at present
  | push frame ordinary tail ih =>
    simp only [handler_locations] at present
    obtain ⟨lower,member,same⟩ := List.mem_map.mp present
    cases same
    have pieces := missing_append_parts (.push frame ordinary .nil) missing
    rw [searchOutcome_push]
    exact ih lower member pieces.2
  | handler installation header tail ih =>
    simp only [handler_locations,List.mem_cons] at present
    rcases present with same | rest
    · cases same
      exact searchOutcome_handler installation header tail _ _
    · obtain ⟨lower,member,same⟩ := List.mem_map.mp rest
      cases same
      have pieces := missing_append_parts (.handler installation header .nil) missing
      rw [searchOutcome_handler]
      exact ih lower member pieces.2
  | @live owners otherHandler otherOwner occurrence dynamicTicket captured data capturedTarget physical target result installation header saved tail ihSaved ih =>
    simp only [handler_locations] at present
    obtain ⟨lower,member,same⟩ := List.mem_map.mp present
    cases same
    have pieces := missing_append_parts (.live (result := result) installation header saved .nil) missing
    have different : ¬ (handler = otherHandler ∧ owner = otherOwner) := by
      intro same
      obtain ⟨rfl,rfl⟩ := same
      have impossible := pieces.1
      simp [CoreMachine.findOwner] at impossible
    rw [searchOutcome_live_ne installation header saved tail handler owner different]
    exact ih lower member pieces.2
  | @spent owners otherHandler otherOwner occurrence dynamicTicket captured data physical target installation header tail ih =>
    simp only [handler_locations] at present
    obtain ⟨lower,member,same⟩ := List.mem_map.mp present
    cases same
    have pieces := missing_append_parts (.spent installation header .nil) missing
    have different : ¬ (handler = otherHandler ∧ owner = otherOwner) := by
      intro same
      obtain ⟨rfl,rfl⟩ := same
      have impossible := pieces.1
      simp [CoreMachine.findOwner] at impossible
    rw [searchOutcome_spent_ne installation header tail handler owner different]
    exact ih lower member pieces.2
  | append first last ihFirst ihLast =>
    simp only [handler_locations,List.mem_append] at present
    rcases present with left | right
    · obtain ⟨lower,member,same⟩ := List.mem_map.mp left
      cases same
      change searchOutcome (owner_search (first.append last) handler owner) =
        searchOutcome (owner_search (lower.after.append last) handler owner)
      rw [searchOutcome_append,searchOutcome_append,ihFirst lower member missing]
    · obtain ⟨lower,member,same⟩ := List.mem_map.mp right
      cases same
      have pieces := missing_append_parts first missing
      rw [searchOutcome_append_missing first last pieces.1]
      exact ihLast lower member pieces.2


/-- Named resume output preserves another owner's original capture when both
actual transported prefixes are missing that static pair. -/
theorem searchOutcome_resume_other {current : Endpoint graph} (input : ResumeInput current)
    (handler owner : Nat)
    (savedMissing : CoreMachine.findOwner handler owner input.captured = .error (.missingOwner handler owner))
    (frontMissing : CoreMachine.findOwner handler owner input.front = .error (.missingOwner handler owner))
    (different : ¬ (handler = input.handler ∧ owner = input.owner)) :
    searchOutcome (owner_search (resume_result input).after.history handler owner) =
      searchOutcome (owner_search input.outsideHistory handler owner) := by
  change searchOutcome (owner_search (input.capturedHistory.append
    (input.frontHistory.append (.spent input.installation input.header input.outsideHistory))) handler owner) = _
  rw [searchOutcome_append_missing _ _ savedMissing,searchOutcome_append_missing _ _ frontMissing,
    searchOutcome_spent_ne _ _ _ _ _ different]

/-- Ordinary head elimination retains the same computed original capture,
including classification at spent barriers. -/
theorem searchOutcome_head_below
    (member : CoreCallableStrictCaptureOrigins.HeadMember owners frame plain history below)
    (handler owner : Nat) :
    searchOutcome (owner_search history handler owner) =
      searchOutcome (owner_search below handler owner) := by
  induction member with
  | here related ordinary tail => exact searchOutcome_push _ _ _ _ _
  | append first last below member ih =>
    rw [searchOutcome_append,searchOutcome_append,ih]


/-- The returned saved handler carries its own original installation and rich
tail. This receipt is constructed at capture and transported as an output. -/
structure SavedHandler (receipt : CapturedReceipt graph heap handler owner) where
  site : Nat
  environment : Environment
  installation : GeneralHandlerPast graph receipt.owners site environment receipt.data
  header : CoreEffectFrames.BoundaryRel graph receipt.owners heap
    (.handlerBoundary site environment receipt.data.activation) (.handler receipt.data)
  tailPhysical : List CoreMachine.Frame
  tailTarget : Stack
  tail : GeneralHistory graph heap tailPhysical tailTarget
  head : HandlerHead installation header receipt.history tail

noncomputable def HandlerHead.heap_weaken
    {installation : GeneralHandlerPast graph owners site environment data}
    {header : CoreEffectFrames.BoundaryRel graph owners heap (.handlerBoundary site environment data.activation) (.handler data)}
    {history : GeneralHistory graph heap physical target}
    {tail : GeneralHistory graph heap tailPhysical tailTarget}
    (head : HandlerHead installation header history tail) (extension : HeapExtends heap larger) :
    HandlerHead installation (header.heap_weaken extension)
      (history.heap_weaken extension) (tail.heap_weaken extension) := by
  induction head with
  | here tail => exact .here _
  | append current tail last head ih => exact .append _ _ _ ih
  | emptyPrefix current tail head ih => exact .emptyPrefix _ _ ih

noncomputable def SavedHandler.heap_weaken {receipt : CapturedReceipt graph heap handler owner} (saved : SavedHandler receipt) (extension : HeapExtends heap larger) :
    SavedHandler (receipt.heap_weaken extension) := {
  site := saved.site,environment := saved.environment,installation := saved.installation
  header := saved.header.heap_weaken extension
  tailPhysical := saved.tailPhysical,tailTarget := saved.tailTarget
  tail := saved.tail.heap_weaken extension,head := HandlerHead.heap_weaken saved.head extension }

noncomputable def SavedHandler.transport {receipt original : CapturedReceipt graph heap handler owner} (same : receipt = original) (saved : SavedHandler original) : SavedHandler receipt := by
  cases same
  exact saved


private theorem retained_no_boundary (history : RetainedHistory graph heap physical target)
    (site : Nat) (environment : Environment) (activation : Nat) :
    .handlerBoundary site environment activation ∉ physical := by
  induction history with
  | nil => simp
  | plain frame tail ih | handler installation header tail ih | spent installation header tail ih | retiring installation header tail ih => exact ih
  | cell frame tail ih | armed installed tail ih => simp only [List.mem_cons]; intro h; rcases h with h | h; cases h; exact ih h
  | live installation header saved tail ihSaved ihTail => simpa only [List.mem_append,not_or] using And.intro ihSaved ihTail

/-- A real leading handler is selected from the SAME structural inventory.
Retained lexical projections cannot supply a physical handler boundary. -/
theorem handler_at_physical_head
    (history : GeneralHistory graph heap physical target)
    (same : physical = .handlerBoundary site environment activation :: rest) :
    ∃ selected ∈ handler_locations history, selected.inside = [] ∧
      selected.site = site ∧ selected.environment = environment ∧ selected.data.activation = activation := by
  induction history generalizing rest with
  | nil => cases same
  | retained receipt =>
    have impossible := retained_no_boundary receipt site environment activation
    rw [same] at impossible
    exact False.elim (impossible (by simp))
  | push frame ordinary tail ih =>
    have matching := (List.cons.inj same).1
    cases matching
    exact False.elim ordinary
  | handler installation header tail ih =>
    have matching := (List.cons.inj same).1
    cases matching
    exact ⟨_,List.mem_cons_self,rfl,rfl,rfl,rfl⟩
  | running receipt => cases same
  | unwinding installed => cases same
  | closing core target scope => cases same
  | live installation header saved tail ihSaved ihTail => cases same
  | spent installation header tail ih => cases same
  | @append firstPhysical firstTarget lastPhysical lastTarget first last ihFirst ihLast =>
    by_cases physicalFirst : firstPhysical = []
    ·
      have lastSame : lastPhysical = .handlerBoundary site environment activation :: rest := by simpa only [physicalFirst,List.nil_append] using same
      obtain ⟨lower,member,inside,atSite,atEnvironment,atActivation⟩ := ihLast lastSame
      refine ⟨lower.prepend first,?_,?_,atSite,atEnvironment,atActivation⟩
      · simp only [handler_locations,List.mem_append,List.mem_map]
        exact Or.inr ⟨lower,member,rfl⟩
      · change firstPhysical ++ lower.inside = []
        rw [physicalFirst,inside]
        rfl
    · obtain ⟨frame,tail,physicalFirst⟩ := List.exists_cons_of_ne_nil physicalFirst
      have firstSame : firstPhysical = .handlerBoundary site environment activation :: tail := by
        have matching := (List.cons.inj (by simpa only [physicalFirst,List.cons_append] using same)).1
        rw [physicalFirst,matching]
      obtain ⟨lower,member,inside,atSite,atEnvironment,atActivation⟩ := ihFirst firstSame
      refine ⟨lower.suffix last,?_,inside,atSite,atEnvironment,atActivation⟩
      simp only [handler_locations,List.mem_append,List.mem_map]
      exact Or.inl ⟨lower,member,rfl⟩


theorem SavedHandler.transport_tailTarget {receipt original : CapturedReceipt graph heap handler owner}
    (same : receipt = original) (saved : SavedHandler original) :
    (SavedHandler.transport same saved).tailTarget = saved.tailTarget := by cases same; rfl

theorem SavedHandler.transport_tailPhysical {receipt original : CapturedReceipt graph heap handler owner}
    (same : receipt = original) (saved : SavedHandler original) :
    (SavedHandler.transport same saved).tailPhysical = saved.tailPhysical := by cases same; rfl


/-- Full spent receipt extracted from an actual constructor. Logical zero
physical prefixes remain rich histories until the current lexical guard is
proved; their physical projection is never identified with nil history. -/
structure SpentPosition (graph : Graph) (heap : CoreMachine.Heap)
    (handler owner occurrence dynamicTicket : Nat) (physical : List CoreMachine.Frame) (target : Stack) where
  owners : OwnerMap
  captured : List CoreMachine.Frame
  data : HandlerData
  installation : GeneralClausePast graph owners handler owner occurrence dynamicTicket captured data
  header : OwnerHeader graph owners heap handler owner occurrence data
  prefixTarget : Stack
  leadingReceipt : GeneralHistory graph heap [] prefixTarget
  tailPhysical : List CoreMachine.Frame
  tailTarget : Stack
  tail : GeneralHistory graph heap tailPhysical tailTarget
  physicalSame : physical = .clauseBoundary handler owner occurrence dynamicTicket none :: tailPhysical
  targetSame : target = prefixTarget.append (.spent dynamicTicket data.answer data.scope tailTarget)

private theorem retained_no_clause (history : RetainedHistory graph heap physical target)
    (handler owner occurrence dynamicTicket : Nat) (saved : Option (List CoreMachine.Frame)) :
    .clauseBoundary handler owner occurrence dynamicTicket saved ∉ physical := by
  induction history with
  | nil => simp
  | plain frame tail ih | handler installation header tail ih | spent installation header tail ih | retiring installation header tail ih => exact ih
  | cell frame tail ih | armed installed tail ih => simp only [List.mem_cons]; intro h; rcases h with h | h; cases h; exact ih h
  | live installation header saved tail ihSaved ihTail => simpa only [List.mem_append,not_or] using And.intro ihSaved ihTail

private theorem push_no_clause (frame : PushCarrier graph owners heap core target) :
    core ≠ .clauseBoundary handler owner occurrence dynamicTicket saved := by
  cases frame with
  | ordinary related =>
    rename_i plain
    change FrameRel graph owners heap core plain.context at related
    generalize same : plain.context = context at related
    cases related <;> intro impossible <;> cases impossible
  | initializer related => cases related; intro impossible; cases impossible
  | request related => cases related; intro impossible; cases impossible
  | resume related => cases related; intro impossible; cases impossible
  | cleanup related => cases related; intro impossible; cases impossible
  | boundary related => cases related <;> intro impossible <;> cases impossible

/-- The producer inspects only actual history constructors and appends. It
retains the original full GeneralClausePast/Header and actual tail. -/
theorem spent_at_physical_head (history : GeneralHistory graph heap physical target)
    (same : physical = .clauseBoundary handler owner occurrence dynamicTicket none :: rest) :
    Nonempty (SpentPosition graph heap handler owner occurrence dynamicTicket physical target) := by
  induction history generalizing rest with
  | nil => cases same
  | retained receipt =>
    have impossible := retained_no_clause receipt handler owner occurrence dynamicTicket none
    rw [same] at impossible
    exact False.elim (impossible (by simp))
  | push frame ordinary tail ih => exact False.elim (push_no_clause frame (List.cons.inj same).1)
  | handler installation header tail ih => cases same
  | running receipt => cases same
  | unwinding installed => cases same
  | closing core target scope => cases same
  | live installation header saved tail ihSaved ihTail => cases same
  | spent installation header tail ih =>
    have matching := (List.cons.inj same).1
    cases matching
    exact ⟨⟨_,_,_,installation,header,.nil,.nil,_,_,tail,rfl,rfl⟩⟩
  | @append firstPhysical firstTarget lastPhysical lastTarget first last ihFirst ihLast =>
    by_cases empty : firstPhysical = []
    · have lastSame : lastPhysical = .clauseBoundary handler owner occurrence dynamicTicket none :: rest := by simpa only [empty,List.nil_append] using same
      obtain ⟨selected⟩ := ihLast lastSame
      have leadingReceipt : GeneralHistory graph heap [] (firstTarget.append selected.prefixTarget) := by
        rw [← empty]
        simpa only [List.append_nil] using first.append selected.leadingReceipt
      refine ⟨⟨selected.owners,selected.captured,selected.data,selected.installation,selected.header,
        firstTarget.append selected.prefixTarget,leadingReceipt,selected.tailPhysical,selected.tailTarget,selected.tail,?_,?_⟩⟩
      · simpa only [empty,List.nil_append] using selected.physicalSame
      · simpa only [stack_append_assoc] using congrArg (fun stack => firstTarget.append stack) selected.targetSame
    · obtain ⟨frame,tail,atFirst⟩ := List.exists_cons_of_ne_nil empty
      have firstSame : firstPhysical = .clauseBoundary handler owner occurrence dynamicTicket none :: tail := by
        have matching := (List.cons.inj (by simpa only [atFirst,List.cons_append] using same)).1
        rw [atFirst,matching]
      obtain ⟨selected⟩ := ihFirst firstSame
      refine ⟨⟨selected.owners,selected.captured,selected.data,selected.installation,selected.header,
        selected.prefixTarget,selected.leadingReceipt,selected.tailPhysical++lastPhysical,selected.tailTarget.append lastTarget,
        selected.tail.append last,?_,?_⟩⟩
      · simpa only [List.cons_append] using congrArg (fun frames => frames++lastPhysical) selected.physicalSame
      · simpa only [stack_append_assoc,Stack.append] using congrArg (fun stack => stack.append lastTarget) selected.targetSame

noncomputable def spent_position (history : GeneralHistory graph heap physical target)
    (same : physical = .clauseBoundary handler owner occurrence dynamicTicket none :: rest) :
    SpentPosition graph heap handler owner occurrence dynamicTicket physical target :=
  Classical.choice (spent_at_physical_head history same)


#print axioms searchOutcome_heap_weaken
#print axioms searchOutcome_handler_after
#print axioms searchOutcome_bind_below
#print axioms findOwner_append
#print axioms owner_search_valid
#print axioms owner_search_complete
#print axioms owner_search_missing
#print axioms capturedReceipt
#print axioms capturedReceipt_prepend
#print axioms capturedReceipt_suffix
#print axioms searchedCapture
#print axioms searchedCapture_append_missing
#print axioms owner_search_append_missing
#print axioms owner_from_live_path_eq
#print axioms live_path_restored
#print axioms owner_from_live_path
#print axioms owner_from_live_path_picked
#print axioms owner_from_live_path_ticket

end Ash.OneShot.CoreCallableRestoredBindContinuationOrigins

namespace Ash.OneShot.CoreCallableRestoredBindContinuationOrigins

/-- Local ports for the actual two Unit operands do not admit surrounding code. -/
theorem unit_pair_port : ScopedPorts.Typed signature world environment ticket allowed
    (.pair .unit .unit) (.product .unit .unit) := .pair .unit .unit

theorem pair_left_product_context
    (right : ScopedPorts.Typed signature world environment ticket allowed code .unit) :
    ScopedPorts.ContextTyped signature world environment ticket allowed
      (.pairLeft code) .unit (.product .unit .unit) := .pairLeft right

theorem pair_right_product_context :
    ScopedPorts.ContextTyped signature world environment ticket allowed
      (.pairRight .unit) .unit (.product .unit .unit) := .pairRight .unit

/-- The original H suffix ignores parameter20. Its input comes from the actual
Product initializer, not from an inferred use of that parameter. -/
theorem product_bind_resume_context
    (residual : residualEffects ⊆ allowed) :
    ScopedPorts.ContextTyped signature world ScopedPorts.TypeEnv.empty
      (.bound binder .unit .unit residualEffects closingEffects) allowed
      (.bind parameter (.resume binder .unit)) (.product .unit .unit) .unit := by
  exact .bind (.resume .unit residual (by simp [ScopedPorts.InWorld,ScopedPorts.Port.resources]))

theorem pair_output_not_unit
    (typed : ScopedPorts.Typed signature world environment ticket allowed (.pair left right) .unit) : False := by
  cases typed

theorem pair_left_context_output_not_unit
    (typed : ScopedPorts.ContextTyped signature world environment ticket allowed (.pairLeft right) input .unit) : False := by
  cases typed

theorem pair_right_context_output_not_unit
    (typed : ScopedPorts.ContextTyped signature world environment ticket allowed (.pairRight left) input .unit) : False := by
  cases typed

#print axioms unit_pair_port
#print axioms pair_left_product_context
#print axioms pair_right_product_context
#print axioms product_bind_resume_context
#print axioms pair_output_not_unit
#print axioms pair_left_context_output_not_unit
#print axioms pair_right_context_output_not_unit
end Ash.OneShot.CoreCallableRestoredBindContinuationOrigins
