import SourceRecursiveRoutes
import CoreGeneralStack
import CoreResourceUnwind
import CoreRunningSplice

/-! General saved segments connect actual user capture and one-shot restoration.
The old bounded relation embeds unchanged. Retained projected lookup requires
an explicit current lookup and source route; producing those route certificates
from an executing callback remains a separate admission obligation.
No future configuration relation or callback execution is a premise. -/
namespace Ash.OneShot.CoreGeneralCaptureResume
open CoreCleanupProjection
open ScopedExpressions ScopedExecution CoreValueRelation CoreStrictStack CoreStrictPotential
  CoreCaptureEntry CoreResumeEntry CoreRequestFrames CoreResumeFrames CoreEffectFrames
  CoreCleanupRunFrames CoreGeneralStack CoreUnwindRelation

set_option linter.unusedSimpArgs false

inductive GeneralRelated (graph : CoreSyntax.Graph) : CoreUnwindRelation.Point → Prop where
  | legacy (current : CoreUnwindRelation.Related graph point) : GeneralRelated graph point
  | evalSegment (segment : GeneralSegment graph state.heap physical lexical)
      (component : ComponentMapped graph owners maps (isolate state maps) focus)
      (frames : state.frames = framesOf maps ++ physical) :
      GeneralRelated graph ⟨state,.eval (attach focus lexical),owners,maps⟩
  | discardSegment (carrier : DiscardCarrier graph owners state.heap environment handler owner binder)
      (control : state.control = .discard handler owner)
      (frames : state.frames = physical)
      (segment : GeneralSegment graph state.heap physical lexical) :
      GeneralRelated graph ⟨state,.eval ⟨.discard binder,scope,lexical⟩,owners,[]⟩
  | unwindSegment (cursor : RetainedCursor graph state.heap physical lexical)
      (outside : GeneralSegment graph state.heap outsidePhysical outsideTarget)
      (control : state.control = .returned .unit)
      (frames : state.frames = physical ++ .closeCompletion coreClose :: outsidePhysical) :
      GeneralRelated graph ⟨state,.unwind scope (lexical.append (.push (.closing targetClose callerScope) outsideTarget)),owners,[]⟩

structure GeneralStepWitness (graph : CoreSyntax.Graph) (before after : CoreUnwindRelation.Point)
    (created discharged : List Owner) : Prop where
  current : GeneralRelated graph before
  core : CoreMachine.next graph before.state = .stepped after.state
  target : CoreUnwindRelation.Positive before.machine after.machine created discharged
  successor : GeneralRelated graph after

theorem GeneralStepWitness.of_legacy (step : CoreResourceUnwind.StepWitness graph before after created discharged) :
    GeneralStepWitness graph before after created discharged :=
  ⟨.legacy step.current,step.core,step.target,.legacy step.successor⟩

theorem positive_accounting (positive : CoreUnwindRelation.Positive before after created discharged) :
    (before.stack.erase.owners ++ created).Perm (after.stack.erase.owners ++ discharged) := by
  induction positive with
  | one transition => exact LexicalUnwind.transition_accounting transition
  | next transition rest ih =>
      have first := LexicalUnwind.transition_accounting transition
      apply List.perm_iff_count.mpr
      intro owner
      have firstCount := first.count_eq owner
      have restCount := ih.count_eq owner
      simp only [List.count_append] at firstCount restCount ⊢
      omega

theorem GeneralStepWitness.accounting (step : GeneralStepWitness graph before after created discharged) :
    (before.machine.stack.erase.owners ++ created).Perm (after.machine.stack.erase.owners ++ discharged) :=
  positive_accounting step.target

/-- Only physical live markers save resumable segments. Projected lexical
live records are not searched as dormant physical owner occurrences. -/
private def prependLookup (frame : CoreMachine.Frame)
    (lookup : Except CoreMachine.Error CoreMachine.InterpreterCut) : Except CoreMachine.Error CoreMachine.InterpreterCut := do
  match ← lookup with
  | .cell cut => pure (.cell {cut with inside := frame :: cut.inside})
  | .handler inside site environment occurrence outside => pure (.handler (frame :: inside) site environment occurrence outside)

private theorem lookup_tail
    (skip : CoreMachine.findInterpreter graph effect (frame :: rest) =
      prependLookup frame (CoreMachine.findInterpreter graph effect rest))
    (found : CoreMachine.findInterpreter graph effect (frame :: rest) = .ok (.handler inside site environment occurrence outside)) :
    ∃ suffixInside, inside = frame :: suffixInside ∧
      CoreMachine.findInterpreter graph effect rest = .ok (.handler suffixInside site environment occurrence outside) := by
  rw [skip] at found
  cases selected : CoreMachine.findInterpreter graph effect rest with
  | error error => simp [prependLookup,selected,Bind.bind,Except.bind] at found
  | ok cut =>
      cases cut with
      | cell cut => simp [prependLookup,selected,Bind.bind,Except.bind,Pure.pure,Except.pure] at found
      | handler suffix selectedSite selectedEnvironment selectedOccurrence selectedOutside =>
          simp [prependLookup,selected,Bind.bind,Except.bind,Pure.pure,Except.pure] at found
          obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := found
          exact ⟨suffix,rfl,rfl⟩

private theorem push_lookup_skip (frame : PushCarrier graph owners heap core targetFrame)
    (miss : targetFrame.erase.target ≠ some requested) :
    CoreMachine.findInterpreter graph (Instantiation.freezeEffect requested) (core :: rest) =
      prependLookup core (CoreMachine.findInterpreter graph (Instantiation.freezeEffect requested) rest) := by
  cases frame with
  | ordinary related =>
      rename_i plain
      change CoreStrictFrames.FrameRel graph owners heap core plain.context at related
      generalize contextEq : plain.context = context at related
      cases related <;> rfl
  | initializer related => cases related; rfl
  | request related => cases related; rfl
  | resume related => cases related; rfl
  | cleanup related => cases related; rfl
  | boundary related =>
      cases related with
      | @handler site node handlerId effect body clauses fuel rawBody rawClauses saved data known kind translated header =>
          have actual := handle_effect_at header _ _ _ _ _ _ rfl rfl
          have different : Instantiation.freezeEffect requested ≠ Instantiation.freezeEffect data.effectInst := by
            intro same
            apply miss
            have equal := Instantiation.effect_realization_unique
              (same ▸ Instantiation.frozen_effect_realizes Instantiation.Environment.empty requested)
              (Instantiation.frozen_effect_realizes Instantiation.Environment.empty data.effectInst)
            simpa [ExecFrame.erase,HandlerData.erase,Frame.target] using congrArg some equal.symm
          simp [CoreMachine.findInterpreter,known,kind,actual,different,prependLookup]
          rfl
      | @cell site node identity handle initializer body key payload scope answer known kind =>
          have different : Instantiation.freezeEffect requested ≠ Instantiation.Effect.cell (.activation key) := by
            intro same
            apply miss
            have equal := Instantiation.effect_realization_unique
              (same ▸ Instantiation.frozen_effect_realizes Instantiation.Environment.empty requested)
              (Instantiation.frozen_effect_realizes Instantiation.Environment.empty (.cell key))
            simpa [ExecFrame.erase,Frame.target] using congrArg some equal.symm
          simp [CoreMachine.findInterpreter,different,prependLookup]
          rfl

/-- Authentication of a physical handler split. Selection safety for erased
lexical handlers is a separate current route certificate on this prefix. -/
def GeneralHandlerSplit (graph : CoreSyntax.Graph) (heap : Heap) (requested : Instance)
    (_physical : List CoreMachine.Frame) (lexical : Stack) (inside : List CoreMachine.Frame)
    (site : Nat) (environment : CoreMachine.Environment) (occurrence : Nat) (outside : List CoreMachine.Frame) : Prop :=
  ∃ front tail owners data,
    data.activation = occurrence ∧ data.effectInst = requested ∧
    lexical = front.append (.push (.handler data) tail) ∧
    GeneralSegment graph heap inside front ∧
    BoundaryRel graph owners heap (.handlerBoundary site environment occurrence) (.handler data) ∧
    GeneralSegment graph heap outside tail

private theorem split_push
    (frame : PushCarrier graph owners heap core targetFrame)
    (split : GeneralHandlerSplit graph heap requested rest target inside site environment occurrence outside) :
    GeneralHandlerSplit graph heap requested (core :: rest) (.push targetFrame target)
      (core :: inside) site environment occurrence outside := by
  rcases split with ⟨front,tail,savedOwners,data,activation,same,shape,before,header,after⟩
  exact ⟨.push targetFrame front,tail,savedOwners,data,activation,same,
    congrArg (Stack.push targetFrame) shape,.push frame before,header,after⟩

private theorem split_append_prefix
    (prefixSegment : GeneralSegment graph heap physical lexical)
    (split : GeneralHandlerSplit graph heap requested rest target inside site environment occurrence outside) :
    GeneralHandlerSplit graph heap requested (physical ++ rest) (lexical.append target)
      (physical ++ inside) site environment occurrence outside := by
  rcases split with ⟨front,tail,savedOwners,data,activation,same,shape,before,header,after⟩
  exact ⟨lexical.append front,tail,savedOwners,data,activation,same,
    by simpa [stack_append_assoc] using congrArg (Stack.append lexical) shape,
    .append prefixSegment before,header,after⟩

private abbrev HandlerSplittable (graph : CoreSyntax.Graph) (heap : Heap) (requested : Instance)
    (physical : List CoreMachine.Frame) (lexical : Stack) : Prop :=
  ∀ suffixPhysical suffixTarget, GeneralSegment graph heap suffixPhysical suffixTarget →
    (∀ inside site environment occurrence outside,
      CoreMachine.findInterpreter graph (Instantiation.freezeEffect requested) suffixPhysical =
        .ok (.handler inside site environment occurrence outside) →
      GeneralHandlerSplit graph heap requested suffixPhysical suffixTarget inside site environment occurrence outside) →
    ∀ inside site environment occurrence outside,
      CoreMachine.findInterpreter graph (Instantiation.freezeEffect requested) (physical ++ suffixPhysical) =
        .ok (.handler inside site environment occurrence outside) →
      GeneralHandlerSplit graph heap requested (physical ++ suffixPhysical) (lexical.append suffixTarget)
        inside site environment occurrence outside

private theorem handler_cut_prepend
    (prefixStack : Stack) (miss : prefixStack.erase.resolve requested = none)
    (cut : HandlerCut requested target cap tail data) :
    HandlerCut requested (prefixStack.append target) (prefixStack.append cap) tail data := by
  induction prefixStack with
  | nil => exact cut
  | push frame rest ih =>
      have frameMiss : frame.erase.resolve requested = none := by
        cases h : frame.erase.resolve requested with
        | none => rfl
        | some selected => simp [Stack.erase,Control.resolve,h] at miss
      have targetMiss : frame.erase.target ≠ some requested := by
        cases kind : frame.erase.kind <;> simp_all [Frame.resolve,Frame.target]
        all_goals exact Ne.symm frameMiss
      have restMiss : rest.erase.resolve requested = none := by
        simpa [Stack.erase,Control.resolve,frameMiss] using miss
      exact .push _ _ _ _ _ targetMiss (ih restMiss)
  | live ticket q a saved scope rest ihSaved ih => exact .live _ _ _ _ _ _ _ _ _ (ih miss)
  | spent ticket a scope rest ih => exact .spent _ _ _ _ _ _ _ (ih miss)

inductive GeneralHandlerCut (graph : CoreSyntax.Graph) (heap : Heap) (requested : Instance) :
    List CoreMachine.Frame → Stack → List CoreMachine.Frame → CoreTranslation.OwnerMap → Nat →
      CoreMachine.Environment → HandlerData → List CoreMachine.Frame → Stack → Stack → Prop where
  | hit (header : BoundaryRel graph owners heap (.handlerBoundary site environment data.activation) (.handler data))
      (same : data.effectInst = requested) (outside : GeneralSegment graph heap physical lexical) :
      GeneralHandlerCut graph heap requested (.handlerBoundary site environment data.activation :: physical)
        (.push (.handler data) lexical) [] owners site environment data physical (.push (.handler data) .nil) lexical
  | push (frame : PushCarrier graph owners heap core targetFrame)
      (miss : targetFrame.erase.target ≠ some requested)
      (next : GeneralHandlerCut graph heap requested whole target inside savedOwners site environment data outside cap tail) :
      GeneralHandlerCut graph heap requested (core :: whole) (.push targetFrame target) (core :: inside)
        savedOwners site environment data outside (.push targetFrame cap) tail
  | completion (atom : CompletionRel graph heap core targetFrame)
      (next : GeneralHandlerCut graph heap requested whole target inside savedOwners site environment data outside cap tail) :
      GeneralHandlerCut graph heap requested (core :: whole) (.push targetFrame target) (core :: inside)
        savedOwners site environment data outside (.push targetFrame cap) tail
  | live (header : OwnerHeader graph owners heap handler owner occurrence oldData)
      (saved : GeneralSegment graph heap savedPhysical savedTarget)
      (next : GeneralHandlerCut graph heap requested whole target inside savedOwners site environment data outside cap tail) :
      GeneralHandlerCut graph heap requested
        (.clauseBoundary handler owner occurrence ticket (some savedPhysical) :: whole)
        (.live ticket result oldData.answer savedTarget oldData.scope target)
        (.clauseBoundary handler owner occurrence ticket (some savedPhysical) :: inside)
        savedOwners site environment data outside (.live ticket result oldData.answer savedTarget oldData.scope cap) tail
  | spent (header : OwnerHeader graph owners heap handler owner occurrence oldData)
      (next : GeneralHandlerCut graph heap requested whole target inside savedOwners site environment data outside cap tail) :
      GeneralHandlerCut graph heap requested (.clauseBoundary handler owner occurrence ticket none :: whole)
        (.spent ticket oldData.answer oldData.scope target) (.clauseBoundary handler owner occurrence ticket none :: inside)
        savedOwners site environment data outside (.spent ticket oldData.answer oldData.scope cap) tail
  | retained (cursor : RetainedCursor graph heap physical lexical)
      (scope : SourceRecursiveRoutes.Scope context lexical.erase)
      (route : SourceResourceRoutes.Route outward context requested none)
      (currentLookup : CoreMachine.findInterpreter graph (Instantiation.freezeEffect requested) (physical ++ whole) =
        .ok (.handler (physical ++ inside) site environment data.activation outside))
      (next : GeneralHandlerCut graph heap requested whole target inside savedOwners site environment data outside cap tail) :
      GeneralHandlerCut graph heap requested (physical ++ whole) (lexical.append target) (physical ++ inside)
        savedOwners site environment data outside (lexical.append cap) tail
  | split (wholeSegment : GeneralSegment graph heap whole target)
      (prefixSegment : GeneralSegment graph heap inside front)
      (header : BoundaryRel graph savedOwners heap (.handlerBoundary site environment data.activation) (.handler data))
      (same : data.effectInst = requested)
      (outsideSegment : GeneralSegment graph heap outside tail)
      (shape : target = front.append (.push (.handler data) tail))
      (scope : SourceRecursiveRoutes.Scope context front.erase)
      (route : SourceResourceRoutes.Route outward context requested none)
      (currentLookup : CoreMachine.findInterpreter graph (Instantiation.freezeEffect requested) whole =
        .ok (.handler inside site environment data.activation outside)) :
      GeneralHandlerCut graph heap requested whole target inside savedOwners site environment data outside
        (front.append (.push (.handler data) .nil)) tail

theorem GeneralHandlerCut.of_mapped
    (cut : MappedHandlerCut graph heap requested whole target inside savedOwners site environment data outside cap tail) :
    GeneralHandlerCut graph heap requested (framesOf whole) target (framesOf inside)
      savedOwners site environment data (framesOf outside) cap tail := by
  induction cut with
  | hit header same outside => exact .hit header same (.ordinary outside)
  | push frame miss next ih => exact .push frame miss ih
  | live header saved next ih => exact .live header (.ordinary saved) ih
  | spent header next ih => exact .spent header ih

private theorem handler_hit (header : BoundaryRel graph owners heap
    (.handlerBoundary site environment data.activation) (.handler data)) (same : data.effectInst = requested) :
    CoreMachine.findInterpreter graph (Instantiation.freezeEffect requested)
      (.handlerBoundary site environment data.activation :: outside) =
      .ok (.handler [] site environment data.activation outside) := by
  generalize coreEq : CoreMachine.Frame.handlerBoundary site environment data.activation = core at header
  generalize targetEq : ExecFrame.handler data = frame at header
  cases header with
  | handler known kind translated closing =>
      have dataEq := ExecFrame.handler.inj targetEq
      cases dataEq
      obtain ⟨rfl,rfl,_⟩ := CoreMachine.Frame.handlerBoundary.inj coreEq
      have actual := handle_effect_at closing _ _ _ _ _ _ rfl rfl
      simp [CoreMachine.findInterpreter,known,kind,actual,same,Bind.bind,Except.bind,Pure.pure,Except.pure]
  | cell known kind => cases coreEq

private theorem push_splittable
    (frame : PushCarrier graph owners heap core targetFrame)
    (tailSegment : GeneralSegment graph heap physical lexical)
    (ih : HandlerSplittable graph heap requested physical lexical) :
    HandlerSplittable graph heap requested (core :: physical) (.push targetFrame lexical) := by
  intro suffixPhysical suffixTarget suffixSegment suffixSplit inside site environment occurrence outside found
  by_cases miss : targetFrame.erase.target ≠ some requested
  · obtain ⟨suffixInside,rfl,lookup⟩ := lookup_tail (push_lookup_skip frame miss) found
    exact split_push frame (ih _ _ suffixSegment suffixSplit _ _ _ _ _ lookup)
  · have sameTarget : targetFrame.erase.target = some requested := Classical.not_not.mp miss
    cases frame with
    | ordinary related | initializer related | request related | resume related =>
        simp [ExecFrame.erase,PlainData.erase,Frame.target] at sameTarget
    | cleanup related => simp [ExecFrame.erase,ActionData.erase,Frame.target] at sameTarget
    | boundary related =>
        cases related with
        | @handler handlerSite node handlerId effect body clauses fuel rawBody rawClauses saved data known kind translated closing =>
            have same : data.effectInst = requested := by simpa [ExecFrame.erase,HandlerData.erase,Frame.target] using sameTarget
            have header : BoundaryRel graph owners heap (.handlerBoundary handlerSite saved data.activation) (.handler data) :=
              .handler known kind translated closing
            have head := handler_hit (outside := physical ++ suffixPhysical) header same
            simp only [List.cons_append] at found
            rw [head] at found
            simp only [Except.ok.injEq,CoreMachine.InterpreterCut.handler.injEq] at found
            obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := found
            exact ⟨.nil,lexical.append suffixTarget,owners,data,rfl,same,rfl,.ordinary .nil,header,.append tailSegment suffixSegment⟩
        | @cell cellSite node identity handle initializer body key payload scope answer known kind =>
            have same : Instance.cell key = requested := by simpa [ExecFrame.erase,Frame.target] using sameTarget
            subst requested
            simp [CoreMachine.findInterpreter,Instantiation.freezeEffect] at found

private theorem live_splittable
    (header : OwnerHeader graph owners heap handler owner occurrence data)
    (saved : GeneralSegment graph heap savedPhysical savedTarget)
    (_outsideSegment : GeneralSegment graph heap physical lexical)
    (ih : HandlerSplittable graph heap requested physical lexical) :
    HandlerSplittable graph heap requested
      (.clauseBoundary handler owner occurrence ticket (some savedPhysical) :: physical)
      (.live ticket result data.answer savedTarget data.scope lexical) := by
  intro suffixPhysical suffixTarget suffixSegment suffixSplit inside site environment selectedOccurrence outside found
  obtain ⟨suffixInside,rfl,lookup⟩ := lookup_tail (by rfl) found
  rcases ih _ _ suffixSegment suffixSplit _ _ _ _ _ lookup with
    ⟨front,tail,savedOwners,selectedData,activation,same,shape,before,selectedHeader,after⟩
  exact ⟨.live ticket result data.answer savedTarget data.scope front,tail,savedOwners,selectedData,activation,same,
    congrArg (Stack.live ticket result data.answer savedTarget data.scope) shape,
    .live header saved before,selectedHeader,after⟩

private theorem spent_splittable
    (header : OwnerHeader graph owners heap handler owner occurrence data)
    (_outsideSegment : GeneralSegment graph heap physical lexical)
    (ih : HandlerSplittable graph heap requested physical lexical) :
    HandlerSplittable graph heap requested (.clauseBoundary handler owner occurrence ticket none :: physical)
      (.spent ticket data.answer data.scope lexical) := by
  intro suffixPhysical suffixTarget suffixSegment suffixSplit inside site environment selectedOccurrence outside found
  obtain ⟨suffixInside,rfl,lookup⟩ := lookup_tail (by rfl) found
  rcases ih _ _ suffixSegment suffixSplit _ _ _ _ _ lookup with
    ⟨front,tail,savedOwners,selectedData,activation,same,shape,before,selectedHeader,after⟩
  exact ⟨.spent ticket data.answer data.scope front,tail,savedOwners,selectedData,activation,same,
    congrArg (Stack.spent ticket data.answer data.scope) shape,.spent header before,selectedHeader,after⟩

private theorem ordinary_splittable
    (stack : PushedWithMaps graph heap maps target) :
    HandlerSplittable graph heap requested (framesOf maps) target := by
  induction stack with
  | nil => intro _ _ _ suffixSplit; exact suffixSplit
  | cons frame tail ih => exact push_splittable (.ordinary frame) (.ordinary tail) ih
  | initializer frame tail ih => exact push_splittable (.initializer frame) (.ordinary tail) ih
  | boundary frame tail ih => exact push_splittable (.boundary frame) (.ordinary tail) ih
  | cleanup frame tail ih => exact push_splittable (.cleanup frame) (.ordinary tail) ih
  | request frame tail ih => exact push_splittable (.request frame) (.ordinary tail) ih
  | resume frame tail ih => exact push_splittable (.resume frame) (.ordinary tail) ih
  | live header saved outside ihSaved ihOutside => exact live_splittable header (.ordinary saved) (.ordinary outside) ihOutside
  | spent header outside ih => exact spent_splittable header (.ordinary outside) ih

private theorem GeneralSegment.handler_splittable
    (segment : GeneralSegment graph heap physical lexical) : HandlerSplittable graph heap requested physical lexical := by
  induction segment with
  | ordinary stack => exact ordinary_splittable stack
  | retained cursor =>
      intro suffixPhysical suffixTarget suffixSegment suffixSplit inside site environment occurrence outside found
      obtain ⟨suffixInside,rfl,lookup⟩ := CoreGeneralStack.RetainedCursor.handler_lookup_decompose cursor found
      exact split_append_prefix (.retained cursor) (suffixSplit _ _ _ _ _ lookup)
  | push frame tail ih => exact push_splittable frame tail ih
  | @completion core targetFrame atom =>
      intro suffixPhysical suffixTarget suffixSegment suffixSplit inside site environment occurrence outside found
      have skip : CoreMachine.findInterpreter graph (Instantiation.freezeEffect requested) (core :: suffixPhysical) =
        prependLookup core (CoreMachine.findInterpreter graph (Instantiation.freezeEffect requested) suffixPhysical) := by
        cases atom <;> rfl
      obtain ⟨suffixInside,rfl,lookup⟩ := lookup_tail skip found
      simpa [List.cons_append] using split_append_prefix (.completion atom) (suffixSplit _ _ _ _ _ lookup)
  | live header saved outside ihSaved ihOutside => exact live_splittable header saved outside ihOutside
  | spent header outside ih => exact spent_splittable header outside ih
  | append first second ihFirst ihSecond =>
      intro suffixPhysical suffixTarget suffixSegment suffixSplit inside site environment occurrence outside found
      have split := ihFirst _ _ (.append second suffixSegment)
        (ihSecond _ _ suffixSegment suffixSplit) _ _ _ _ _ (by simpa [List.append_assoc] using found)
      simpa [List.append_assoc,stack_append_assoc] using split

private theorem stack_append_nil (stack : Stack) : stack.append .nil = stack := by
  induction stack <;> simp_all [Stack.append]

/-- Derive the authenticated split from the same arbitrary carrier and the
current physical selector. No split or successor relation is an input. -/
theorem GeneralSegment.handler_split
    (segment : GeneralSegment graph heap physical lexical)
    (found : CoreMachine.findInterpreter graph (Instantiation.freezeEffect requested) physical =
      .ok (.handler inside site environment occurrence outside)) :
    GeneralHandlerSplit graph heap requested physical lexical inside site environment occurrence outside := by
  have result := GeneralSegment.handler_splittable segment [] .nil (.ordinary .nil)
    (by intro inside site environment occurrence outside impossible; simp [CoreMachine.findInterpreter] at impossible)
    inside site environment occurrence outside (by simpa using found)
  simpa [stack_append_nil] using result

theorem GeneralHandlerCut.realizes
    (cut : GeneralHandlerCut graph heap requested whole target inside owners site environment data outside cap tail) :
    CoreMachine.findInterpreter graph (Instantiation.freezeEffect requested) whole =
      .ok (.handler inside site environment data.activation outside) ∧
    HandlerCut requested target cap tail data ∧ GeneralSegment graph heap whole target ∧
    GeneralSegment graph heap (inside ++ [.handlerBoundary site environment data.activation]) cap ∧
    GeneralSegment graph heap outside tail := by
  induction cut with
  | hit header same outside =>
      exact ⟨handler_hit header same,.hit _ _ same,.push (.boundary header) outside,
        .push (.boundary header) (.ordinary .nil),outside⟩
  | push frame miss next ih =>
      obtain ⟨found,target,whole,cap,outside⟩ := ih
      exact ⟨PushCarrier.selector_miss frame miss found,.push _ _ _ _ _ miss target,
        .push frame whole,.push frame cap,outside⟩
  | completion atom next ih =>
      obtain ⟨found,target,whole,cap,outside⟩ := ih
      exact ⟨atom.handler_pass found,.push _ _ _ _ _ atom.selector_miss target,
        by simpa [Stack.append] using GeneralSegment.append (.completion atom) whole,
        by simpa [Stack.append] using GeneralSegment.append (.completion atom) cap,outside⟩
  | live header saved next ih =>
      obtain ⟨found,target,whole,cap,outside⟩ := ih
      exact ⟨by simp [CoreMachine.findInterpreter,found,Bind.bind,Except.bind,Pure.pure,Except.pure],
        .live _ _ _ _ _ _ _ _ _ target,.live header saved whole,.live header saved cap,outside⟩
  | spent header next ih =>
      obtain ⟨found,target,whole,cap,outside⟩ := ih
      exact ⟨by simp [CoreMachine.findInterpreter,found,Bind.bind,Except.bind,Pure.pure,Except.pure],
        .spent _ _ _ _ _ _ _ target,.spent header whole,.spent header cap,outside⟩
  | retained cursor scope route currentLookup next ih =>
      obtain ⟨found,target,whole,cap,outside⟩ := ih
      exact ⟨currentLookup,handler_cut_prepend _ (scope.route route).1 target,
        .append (.retained cursor) whole,
        by simpa [List.append_assoc] using GeneralSegment.append (.retained cursor) cap,outside⟩
  | split whole prefixSegment header same outside shape scope route currentLookup =>
      refine ⟨currentLookup,?_,whole,?_,outside⟩
      · rw [shape]
        exact handler_cut_prepend _ (scope.route route).1 (.hit _ _ same)
      · exact .append prefixSegment (.push (.boundary header) (.ordinary .nil))

theorem GeneralHandlerCut.header
    (cut : GeneralHandlerCut graph heap requested whole target inside owners site environment data outside cap tail) :
    BoundaryRel graph owners heap (.handlerBoundary site environment data.activation) (.handler data) := by
  induction cut with
  | hit header same outside => exact header
  | split whole prefixSegment header same outside shape scope route currentLookup => exact header
  | push frame miss next ih | completion atom next ih | live header saved next ih | spent header next ih | retained cursor scope route currentLookup next ih => exact ih
/-- The retained-prefix case is extracted from the exact current physical
selector result. Its lexical miss is obtained from the same source Scope and
Route, while the outside cut still requires its own structural extraction. -/
theorem GeneralHandlerCut.retained_of_lookup
    (cursor : RetainedCursor graph heap physical lexical)
    (scope : SourceRecursiveRoutes.Scope context lexical.erase)
    (route : SourceResourceRoutes.Route outward context requested none)
    (next : GeneralHandlerCut graph heap requested whole target inside savedOwners site environment data outside cap tail)
    (currentLookup : CoreMachine.findInterpreter graph (Instantiation.freezeEffect requested) (physical ++ whole) =
      .ok (.handler actualInside site environment data.activation outside)) :
    actualInside = physical ++ inside ∧
    GeneralHandlerCut graph heap requested (physical ++ whole) (lexical.append target) actualInside
      savedOwners site environment data outside (lexical.append cap) tail := by
  obtain ⟨suffixInside,shape,found⟩ := CoreGeneralStack.RetainedCursor.handler_lookup_decompose cursor currentLookup
  have unique : suffixInside = inside := by
    have equality := found.symm.trans next.realizes.1
    simpa using equality
  subst suffixInside
  subst actualInside
  exact ⟨rfl,.retained cursor scope route currentLookup next⟩

/-- Current static safety for the exact authenticated prefix, expressed only
with the existing source Scope and outward Route certificates. Its producer
from an executing cleanup callback is the separate C2 admission bridge. -/
def CurrentHandlerPrefixRoutes (graph : CoreSyntax.Graph) (heap : Heap) (requested : Instance)
    (lexical : Stack) (inside : List CoreMachine.Frame) (site : Nat)
    (environment : CoreMachine.Environment) (occurrence : Nat) : Prop :=
  ∀ front tail owners data,
    lexical = front.append (.push (.handler data) tail) →
    GeneralSegment graph heap inside front →
    BoundaryRel graph owners heap (.handlerBoundary site environment occurrence) (.handler data) →
    ∃ context outward, SourceRecursiveRoutes.Scope context front.erase ∧
      SourceResourceRoutes.Route outward context requested none

/-- Completeness is conditional on current source route safety, rather than a
supplied target cut. The split and all physical miss decisions are derived
from this same carrier and actual lookup. -/
theorem GeneralSegment.handler_extract
    (segment : GeneralSegment graph heap physical lexical)
    (found : CoreMachine.findInterpreter graph (Instantiation.freezeEffect requested) physical =
      .ok (.handler inside site environment occurrence outside))
    (routes : CurrentHandlerPrefixRoutes graph heap requested lexical inside site environment occurrence) :
    ∃ owners data cap tail, data.activation = occurrence ∧
      GeneralHandlerCut graph heap requested physical lexical inside owners site environment data outside cap tail := by
  obtain ⟨front,tail,owners,data,activation,same,shape,before,header,after⟩ := GeneralSegment.handler_split segment found
  obtain ⟨context,outward,scope,route⟩ := routes front tail owners data shape before header
  subst occurrence
  exact ⟨owners,data,front.append (.push (.handler data) .nil),tail,rfl,
    .split segment before header same after shape scope route found⟩


def captureBefore (base : CoreMachine.State) (value : CoreMachine.Value)
    (effect : Instantiation.Effect) (operation : Nat) (requestEnvironment : CoreMachine.Environment)
    (whole : List CoreMachine.Frame) : CoreMachine.State :=
  {base with control := .returned value,frames := .request effect operation requestEnvironment :: whole}

def captureAfter (base : CoreMachine.State) (clause : CoreSyntax.Clause) (argument : Nat)
    (value : CoreMachine.Value) (handler occurrence site : Nat) (environment : CoreMachine.Environment)
    (inside outside : List CoreMachine.Frame) : CoreMachine.State :=
  { base with control := .evaluate clause.body (.binding argument value environment), frames := .clauseBoundary handler clause.owner occurrence base.nextOwner (some (inside ++ [.handlerBoundary site environment occurrence])) :: outside, nextOwner := base.nextOwner + 1, observations := base.observations ++ [.captured occurrence base.nextOwner] }

/-- Selected clause closing and owner authentication come from the same saved
handler header. The captured carrier is reused in the resulting physical owner. -/
theorem capture_general {base : CoreMachine.State}
    (cut : GeneralHandlerCut graph base.heap requested whole target inside savedOwners site environment data outside cap tail)
    (known : graph.node site = some node) (kind : node.kind = .handler handler handled handlerBody clauses)
    (selected : clauses.find? (fun clause => clause.operation == operation) = some clause)
    (operand : ValueRel graph operandOwners base.heap value operandCode)
    (requestCarrier : EnvCloses graph operandOwners base.heap requestEnvironment
      (.perform effect operation .unit) (.perform (Instantiation.freezeEffect requested) operation .unit))
    (plain : PlainData) (context : plain.context = .perform (Instantiation.freezeEffect requested) operation)
    (ready : ∀ parameter binder body, ClauseAt operation data.clauses parameter binder body → ClosedExcept parameter body)
    (operationResult : Ty) (runtimeScope : Scope) :
    ∃ fuel argument rawBody body,
      clause.argument = .binder argument ∧
      ClauseAt operation data.clauses argument.id (CoreTranslation.ticket graph clause.owner) body ∧
      CoreTranslation.translateFuel graph fuel
        (⟨handler,clause.owner,CoreTranslation.ticket graph clause.owner⟩ :: savedOwners) clause.body = .ok rawBody ∧
      EnvCloses graph (⟨handler,clause.owner,CoreTranslation.ticket graph clause.owner⟩ :: savedOwners)
        base.heap (.binding argument.id value environment) rawBody (body.subst argument.id operandCode) ∧
      OwnerHeader graph savedOwners base.heap handler clause.owner data.activation data ∧
      GeneralStepWitness graph
        ⟨captureBefore base value effect operation requestEnvironment whole,
          .eval ⟨.perform (Instantiation.freezeEffect requested) operation operandCode,plain.scope,target⟩,
          operandOwners,[(operandOwners,.request effect operation requestEnvironment)]⟩
        ⟨captureAfter base clause argument.id value handler data.activation site environment inside outside,
          .eval ⟨body.subst argument.id operandCode,.ticket (CoreTranslation.ticket graph clause.owner) base.nextOwner,
            .live base.nextOwner operationResult data.answer cap data.scope tail⟩,
          ⟨handler,clause.owner,CoreTranslation.ticket graph clause.owner⟩ :: savedOwners,[]⟩ [.ticket base.nextOwner] [] := by
  obtain ⟨selector,targetCut,currentStack,capturedStack,outsideStack⟩ := cut.realizes
  have header := cut.header
  generalize coreEq : CoreMachine.Frame.handlerBoundary site environment data.activation = core at header
  generalize targetEq : ExecFrame.handler data = frame at header
  cases header with
  | @handler savedSite savedNode handlerId rawEffect bodyIndex rawDeclarations handlerFuel rawHandlerBody rawClauses savedEnv savedData found shape translated closing =>
    have dataEq := ExecFrame.handler.inj targetEq
    cases dataEq
    obtain ⟨rfl,rfl,_⟩ := CoreMachine.Frame.handlerBoundary.inj coreEq
    have nodeEq := Option.some.inj (known.symm.trans found)
    cases nodeEq
    have kindEq := kind.symm.trans shape
    cases kindEq
    obtain ⟨fuel,argument,rawBody,pattern,bodyTranslation,rawSelection⟩ :=
      handler_selected_translation found shape translated selected
    obtain ⟨body,selection,masked⟩ := selected_clause_at closing _ _ _ _ _ _ _ _ rfl rfl rawSelection
    have clauseEnvironment := (masked.owner_transport
      (⟨handler,clause.owner,CoreTranslation.ticket graph clause.owner⟩ :: savedOwners)).beta_argument
      (operand.owner_transport _)
    have member := List.mem_of_find?_eq_some selected
    have operationEq : clause.operation = operation := by simpa using List.find?_some selected
    have ownerHeader : OwnerHeader graph savedOwners base.heap handler clause.owner data.activation data :=
      .selected found shape member rfl (.handler found shape translated closing) rfl (operationEq ▸ selection)
    have requestFrame : RequestRel graph operandOwners base.heap (.request effect operation requestEnvironment) plain :=
      .operand requestCarrier context
    have beforeStack := prepend_request requestFrame operand.closed (pushed_mapped (.nil (graph := graph) (heap := base.heap))) runtimeScope
    simp only [context,Context.plug] at beforeStack
    have instantiated := (perform_components requestCarrier).1
    have coreNext : CoreMachine.next graph (captureBefore base value effect operation requestEnvironment whole) =
        .stepped (captureAfter base clause argument.id value handler data.activation site environment inside outside) := by
      simp only [captureBefore,captureAfter,CoreMachine.next,CoreMachine.request,instantiated]
      cases node with
      | mk original type effects source nodeKind =>
        cases shape
        cases requested <;> simp only [Instantiation.freezeEffect] at selector ⊢
        all_goals simp only [selector,found,selected,pattern]
    have targetNext : RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operandCode,plain.scope,target⟩
        ⟨body.subst argument.id operandCode,.ticket (CoreTranslation.ticket graph clause.owner) base.nextOwner,
          .live base.nextOwner operationResult data.answer cap data.scope tail⟩ [.ticket base.nextOwner] [] :=
      .capture _ _ _ _ _ _ _ _ _ _ _ _ _ targetCut selection operand.closed (ready _ _ _ selection)
    have currentComponent : ComponentMapped graph operandOwners [(operandOwners,.request effect operation requestEnvironment)]
        (isolate (captureBefore base value effect operation requestEnvironment whole) [(operandOwners,.request effect operation requestEnvironment)])
        ⟨.perform (Instantiation.freezeEffect requested) operation operandCode,plain.scope,.nil⟩ :=
      ⟨rfl,operandCode,runtimeScope,.returned operand,beforeStack⟩
    have successorComponent : ComponentMapped graph
        (⟨handler,clause.owner,CoreTranslation.ticket graph clause.owner⟩ :: savedOwners) []
        (isolate (captureAfter base clause argument.id value handler data.activation site environment inside outside) [])
        ⟨body.subst argument.id operandCode,.ticket (CoreTranslation.ticket graph clause.owner) base.nextOwner,.nil⟩ :=
      ⟨rfl,_,_,.evaluate bodyTranslation clauseEnvironment,pushed_mapped .nil⟩
    refine ⟨fuel,argument,rawBody,body,pattern,selection,bodyTranslation,clauseEnvironment,ownerHeader,?_,coreNext,
      .one (.evaluate targetNext trivial),?_⟩
    · simpa [attach,Stack.append] using GeneralRelated.evalSegment (state := captureBefore base value effect operation requestEnvironment whole) currentStack currentComponent (by rfl)
    · simpa [attach,Stack.append,captureAfter] using
        GeneralRelated.evalSegment (state := captureAfter base clause argument.id value handler data.activation site environment inside outside) (.live (ticket := base.nextOwner) (result := operationResult) ownerHeader capturedStack outsideStack)
          successorComponent (by rfl)
  | cell found shape => cases coreEq

private theorem push_owner_pass (frame : PushCarrier graph owners heap core target)
    (found : CoreMachine.findOwner handler owner rest = .ok cut) :
    CoreMachine.findOwner handler owner (core :: rest) = .ok {cut with inside := core :: cut.inside} := by
  cases frame with
  | ordinary related =>
      rename_i plain
      change CoreStrictFrames.FrameRel graph owners heap core plain.context at related
      generalize contextEq : plain.context = context at related
      cases related <;> simp [CoreMachine.findOwner,found,Bind.bind,Except.bind,Pure.pure,Except.pure]
  | initializer related => cases related; simp [CoreMachine.findOwner,found,Bind.bind,Except.bind,Pure.pure,Except.pure]
  | request related => cases related; simp [CoreMachine.findOwner,found,Bind.bind,Except.bind,Pure.pure,Except.pure]
  | resume related => cases related; simp [CoreMachine.findOwner,found,Bind.bind,Except.bind,Pure.pure,Except.pure]
  | cleanup related => cases related; simp [CoreMachine.findOwner,found,Bind.bind,Except.bind,Pure.pure,Except.pure]
  | boundary related => cases related <;> simp [CoreMachine.findOwner,found,Bind.bind,Except.bind,Pure.pure,Except.pure]

private def prependOwnerLookup (frame : CoreMachine.Frame) (lookup : Except CoreMachine.Error CoreMachine.OwnerCut) :
    Except CoreMachine.Error CoreMachine.OwnerCut := do
  let cut ← lookup
  pure {cut with inside := frame :: cut.inside}

private theorem owner_lookup_tail
    (skip : CoreMachine.findOwner handler owner (frame :: rest) =
      prependOwnerLookup frame (CoreMachine.findOwner handler owner rest))
    (found : CoreMachine.findOwner handler owner (frame :: rest) = .ok ⟨inside,handler,owner,occurrence,ticket,captured,outside⟩) :
    ∃ suffixInside, inside = frame :: suffixInside ∧
      CoreMachine.findOwner handler owner rest = .ok ⟨suffixInside,handler,owner,occurrence,ticket,captured,outside⟩ := by
  rw [skip] at found
  cases selected : CoreMachine.findOwner handler owner rest with
  | error error => simp [prependOwnerLookup,selected,Bind.bind,Except.bind] at found
  | ok cut =>
      cases cut with
      | mk suffix selectedHandler selectedOwner selectedOccurrence selectedTicket selectedCapture selectedOutside =>
          simp [prependOwnerLookup,selected,Bind.bind,Except.bind,Pure.pure,Except.pure,CoreMachine.OwnerCut.mk.injEq] at found
          obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := found
          exact ⟨suffix,rfl,rfl⟩

private theorem push_owner_skip (frame : PushCarrier graph owners heap core targetFrame) :
    CoreMachine.findOwner handler owner (core :: rest) = prependOwnerLookup core (CoreMachine.findOwner handler owner rest) := by
  cases frame with
  | ordinary related =>
      rename_i plain
      change CoreStrictFrames.FrameRel graph owners heap core plain.context at related
      generalize contextEq : plain.context = context at related
      cases related <;> rfl
  | initializer related => cases related; rfl
  | request related => cases related; rfl
  | resume related => cases related; rfl
  | cleanup related => cases related; rfl
  | boundary related => cases related <;> rfl

/-- A physical owner split authenticates only an actual live clause boundary.
Retained cursor records may occur in the caller prefix but cannot be hits. -/
def GeneralOwnerSplit (graph : CoreSyntax.Graph) (heap : Heap) (handler owner : Nat)
    (_physical : List CoreMachine.Frame) (lexical : Stack) (inside : List CoreMachine.Frame)
    (occurrence ticket : Nat) (captured outside : List CoreMachine.Frame) : Prop :=
  ∃ front savedOwners data result capturedTarget outsideTarget,
    lexical = front.append (.live ticket result data.answer capturedTarget data.scope outsideTarget) ∧
    OwnerHeader graph savedOwners heap handler owner occurrence data ∧
    GeneralSegment graph heap inside front ∧ GeneralSegment graph heap captured capturedTarget ∧
    GeneralSegment graph heap outside outsideTarget

private theorem owner_split_push
    (frame : PushCarrier graph owners heap core targetFrame)
    (split : GeneralOwnerSplit graph heap handler owner rest target inside occurrence ticket captured outside) :
    GeneralOwnerSplit graph heap handler owner (core :: rest) (.push targetFrame target) (core :: inside) occurrence ticket captured outside := by
  rcases split with ⟨front,savedOwners,data,result,capturedTarget,outsideTarget,shape,header,before,saved,after⟩
  exact ⟨.push targetFrame front,savedOwners,data,result,capturedTarget,outsideTarget,
    congrArg (Stack.push targetFrame) shape,header,.push frame before,saved,after⟩

private theorem owner_split_prefix
    (prefixSegment : GeneralSegment graph heap physical lexical)
    (split : GeneralOwnerSplit graph heap handler owner rest target inside occurrence ticket captured outside) :
    GeneralOwnerSplit graph heap handler owner (physical ++ rest) (lexical.append target)
      (physical ++ inside) occurrence ticket captured outside := by
  rcases split with ⟨front,savedOwners,data,result,capturedTarget,outsideTarget,shape,header,before,saved,after⟩
  exact ⟨lexical.append front,savedOwners,data,result,capturedTarget,outsideTarget,
    by simpa [stack_append_assoc] using congrArg (Stack.append lexical) shape,header,.append prefixSegment before,saved,after⟩

private abbrev OwnerSplittable (graph : CoreSyntax.Graph) (heap : Heap) (handler owner : Nat)
    (physical : List CoreMachine.Frame) (lexical : Stack) : Prop :=
  ∀ suffixPhysical suffixTarget, GeneralSegment graph heap suffixPhysical suffixTarget →
    (∀ inside occurrence ticket captured outside,
      CoreMachine.findOwner handler owner suffixPhysical = .ok ⟨inside,handler,owner,occurrence,ticket,captured,outside⟩ →
      GeneralOwnerSplit graph heap handler owner suffixPhysical suffixTarget inside occurrence ticket captured outside) →
    ∀ inside occurrence ticket captured outside,
      CoreMachine.findOwner handler owner (physical ++ suffixPhysical) = .ok ⟨inside,handler,owner,occurrence,ticket,captured,outside⟩ →
      GeneralOwnerSplit graph heap handler owner (physical ++ suffixPhysical) (lexical.append suffixTarget) inside occurrence ticket captured outside

private theorem owner_push_splittable
    (frame : PushCarrier graph owners heap core targetFrame)
    (_tailSegment : GeneralSegment graph heap physical lexical)
    (ih : OwnerSplittable graph heap handler owner physical lexical) :
    OwnerSplittable graph heap handler owner (core :: physical) (.push targetFrame lexical) := by
  intro suffixPhysical suffixTarget suffixSegment suffixSplit inside occurrence ticket captured outside found
  obtain ⟨suffixInside,rfl,lookup⟩ := owner_lookup_tail (push_owner_skip frame) found
  exact owner_split_push frame (ih _ _ suffixSegment suffixSplit _ _ _ _ _ lookup)

private theorem owner_live_splittable
    (header : OwnerHeader graph owners heap otherHandler otherOwner oldOccurrence data)
    (saved : GeneralSegment graph heap savedPhysical savedTarget)
    (outsideSegment : GeneralSegment graph heap physical lexical)
    (ih : OwnerSplittable graph heap handler owner physical lexical) :
    OwnerSplittable graph heap handler owner
      (.clauseBoundary otherHandler otherOwner oldOccurrence oldTicket (some savedPhysical) :: physical)
      (.live oldTicket result data.answer savedTarget data.scope lexical) := by
  intro suffixPhysical suffixTarget suffixSegment suffixSplit inside occurrence ticket captured outside found
  by_cases same : handler = otherHandler ∧ owner = otherOwner
  · rcases same with ⟨rfl,rfl⟩
    simp [CoreMachine.findOwner,CoreMachine.OwnerCut.mk.injEq] at found
    obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := found
    exact ⟨.nil,owners,data,result,savedTarget,lexical.append suffixTarget,rfl,header,.ordinary .nil,saved,.append outsideSegment suffixSegment⟩
  · have different : handler ≠ otherHandler ∨ owner ≠ otherOwner := by
      by_cases equal : handler = otherHandler
      · exact .inr (fun own => same ⟨equal,own⟩)
      · exact .inl equal
    have skip : CoreMachine.findOwner handler owner
        (.clauseBoundary otherHandler otherOwner oldOccurrence oldTicket (some savedPhysical) :: (physical ++ suffixPhysical)) =
        prependOwnerLookup (.clauseBoundary otherHandler otherOwner oldOccurrence oldTicket (some savedPhysical)) (CoreMachine.findOwner handler owner (physical ++ suffixPhysical)) := by
      rcases different with different | different <;> simp [CoreMachine.findOwner,different,prependOwnerLookup]
      all_goals rfl
    obtain ⟨suffixInside,rfl,lookup⟩ := owner_lookup_tail skip found
    rcases ih _ _ suffixSegment suffixSplit _ _ _ _ _ lookup with
      ⟨front,savedOwners,selectedData,selectedResult,capturedTarget,outsideTarget,shape,selectedHeader,before,captured,after⟩
    exact ⟨.live oldTicket result data.answer savedTarget data.scope front,savedOwners,selectedData,selectedResult,capturedTarget,outsideTarget,
      congrArg (Stack.live oldTicket result data.answer savedTarget data.scope) shape,selectedHeader,.live header saved before,captured,after⟩

private theorem owner_spent_splittable
    (header : OwnerHeader graph owners heap otherHandler otherOwner oldOccurrence data)
    (_outsideSegment : GeneralSegment graph heap physical lexical)
    (ih : OwnerSplittable graph heap handler owner physical lexical) :
    OwnerSplittable graph heap handler owner (.clauseBoundary otherHandler otherOwner oldOccurrence oldTicket none :: physical)
      (.spent oldTicket data.answer data.scope lexical) := by
  intro suffixPhysical suffixTarget suffixSegment suffixSplit inside occurrence ticket captured outside found
  by_cases same : handler = otherHandler ∧ owner = otherOwner
  · rcases same with ⟨rfl,rfl⟩
    simp [CoreMachine.findOwner] at found
  · have different : handler ≠ otherHandler ∨ owner ≠ otherOwner := by
      by_cases equal : handler = otherHandler
      · exact .inr (fun own => same ⟨equal,own⟩)
      · exact .inl equal
    have skip : CoreMachine.findOwner handler owner
        (.clauseBoundary otherHandler otherOwner oldOccurrence oldTicket none :: (physical ++ suffixPhysical)) =
        prependOwnerLookup (.clauseBoundary otherHandler otherOwner oldOccurrence oldTicket none) (CoreMachine.findOwner handler owner (physical ++ suffixPhysical)) := by
      rcases different with different | different <;> simp [CoreMachine.findOwner,different,prependOwnerLookup]
      all_goals rfl
    obtain ⟨suffixInside,rfl,lookup⟩ := owner_lookup_tail skip found
    rcases ih _ _ suffixSegment suffixSplit _ _ _ _ _ lookup with
      ⟨front,savedOwners,selectedData,selectedResult,capturedTarget,outsideTarget,shape,selectedHeader,before,captured,after⟩
    exact ⟨.spent oldTicket data.answer data.scope front,savedOwners,selectedData,selectedResult,capturedTarget,outsideTarget,
      congrArg (Stack.spent oldTicket data.answer data.scope) shape,selectedHeader,.spent header before,captured,after⟩

private theorem ordinary_owner_splittable
    (stack : PushedWithMaps graph heap maps target) :
    OwnerSplittable graph heap handler owner (framesOf maps) target := by
  induction stack with
  | nil => intro _ _ _ suffixSplit; exact suffixSplit
  | cons frame tail ih => exact owner_push_splittable (.ordinary frame) (.ordinary tail) ih
  | initializer frame tail ih => exact owner_push_splittable (.initializer frame) (.ordinary tail) ih
  | boundary frame tail ih => exact owner_push_splittable (.boundary frame) (.ordinary tail) ih
  | cleanup frame tail ih => exact owner_push_splittable (.cleanup frame) (.ordinary tail) ih
  | request frame tail ih => exact owner_push_splittable (.request frame) (.ordinary tail) ih
  | resume frame tail ih => exact owner_push_splittable (.resume frame) (.ordinary tail) ih
  | live header saved outside ihSaved ihOutside => exact owner_live_splittable header (.ordinary saved) (.ordinary outside) ihOutside
  | spent header outside ih => exact owner_spent_splittable header (.ordinary outside) ih

private theorem GeneralSegment.owner_splittable
    (segment : GeneralSegment graph heap physical lexical) : OwnerSplittable graph heap handler owner physical lexical := by
  induction segment with
  | ordinary stack => exact ordinary_owner_splittable stack
  | retained cursor =>
      intro suffixPhysical suffixTarget suffixSegment suffixSplit inside occurrence ticket captured outside found
      obtain ⟨suffixInside,rfl,lookup⟩ := CoreGeneralStack.RetainedCursor.owner_lookup_decompose cursor found
      exact owner_split_prefix (.retained cursor) (suffixSplit _ _ _ _ _ lookup)
  | push frame tail ih => exact owner_push_splittable frame tail ih
  | @completion core targetFrame atom =>
      intro suffixPhysical suffixTarget suffixSegment suffixSplit inside occurrence ticket captured outside found
      have skip : CoreMachine.findOwner handler owner (core :: suffixPhysical) =
        prependOwnerLookup core (CoreMachine.findOwner handler owner suffixPhysical) := by cases atom <;> rfl
      obtain ⟨suffixInside,rfl,lookup⟩ := owner_lookup_tail skip found
      simpa [List.cons_append] using owner_split_prefix (.completion atom) (suffixSplit _ _ _ _ _ lookup)
  | live header saved outside ihSaved ihOutside => exact owner_live_splittable header saved outside ihOutside
  | spent header outside ih => exact owner_spent_splittable header outside ih
  | append first second ihFirst ihSecond =>
      intro suffixPhysical suffixTarget suffixSegment suffixSplit inside occurrence ticket captured outside found
      have split := ihFirst _ _ (.append second suffixSegment)
        (ihSecond _ _ suffixSegment suffixSplit) _ _ _ _ _ (by simpa [List.append_assoc] using found)
      simpa [List.append_assoc,stack_append_assoc] using split

/-- This split follows actual nearest static-owner lookup. A consumed nearest
physical owner rejects, and consumed projected records are never owner hits. -/
theorem GeneralSegment.owner_split
    (segment : GeneralSegment graph heap physical lexical)
    (found : CoreMachine.findOwner handler owner physical = .ok ⟨inside,handler,owner,occurrence,ticket,captured,outside⟩) :
    GeneralOwnerSplit graph heap handler owner physical lexical inside occurrence ticket captured outside := by
  have result := GeneralSegment.owner_splittable segment [] .nil (.ordinary .nil)
    (by intro inside occurrence ticket captured outside impossible; simp [CoreMachine.findOwner] at impossible)
    inside occurrence ticket captured outside (by simpa using found)
  simpa [stack_append_nil] using result

inductive GeneralOwnerCut (graph : CoreSyntax.Graph) (heap : Heap) (handler owner : Nat) :
    List CoreMachine.Frame → Stack → List CoreMachine.Frame → Stack → CoreTranslation.OwnerMap → Nat → Nat →
      HandlerData → Ty → List CoreMachine.Frame → Stack → List CoreMachine.Frame → Stack → Prop where
  | hit (header : OwnerHeader graph owners heap handler owner occurrence data)
      (captured : GeneralSegment graph heap capturedPhysical capturedTarget)
      (outside : GeneralSegment graph heap outsidePhysical outsideTarget) :
      GeneralOwnerCut graph heap handler owner
        (.clauseBoundary handler owner occurrence ticket (some capturedPhysical) :: outsidePhysical)
        (.live ticket result data.answer capturedTarget data.scope outsideTarget)
        [] .nil owners occurrence ticket data result capturedPhysical capturedTarget outsidePhysical outsideTarget
  | push (frame : PushCarrier graph owners heap core targetFrame)
      (next : GeneralOwnerCut graph heap handler owner whole target front frontTarget savedOwners occurrence ticket data result captured capturedTarget outside outsideTarget) :
      GeneralOwnerCut graph heap handler owner (core :: whole) (.push targetFrame target) (core :: front)
        (.push targetFrame frontTarget) savedOwners occurrence ticket data result captured capturedTarget outside outsideTarget
  | completion (atom : CompletionRel graph heap core targetFrame)
      (next : GeneralOwnerCut graph heap handler owner whole target front frontTarget savedOwners occurrence ticket data result captured capturedTarget outside outsideTarget) :
      GeneralOwnerCut graph heap handler owner (core :: whole) (.push targetFrame target) (core :: front)
        (.push targetFrame frontTarget) savedOwners occurrence ticket data result captured capturedTarget outside outsideTarget
  | live (header : OwnerHeader graph owners heap otherHandler otherOwner otherOccurrence oldData)
      (different : handler ≠ otherHandler ∨ owner ≠ otherOwner)
      (saved : GeneralSegment graph heap savedPhysical savedTarget)
      (next : GeneralOwnerCut graph heap handler owner whole target front frontTarget savedOwners occurrence ticket data result captured capturedTarget outside outsideTarget) :
      GeneralOwnerCut graph heap handler owner
        (.clauseBoundary otherHandler otherOwner otherOccurrence oldTicket (some savedPhysical) :: whole)
        (.live oldTicket oldResult oldData.answer savedTarget oldData.scope target)
        (.clauseBoundary otherHandler otherOwner otherOccurrence oldTicket (some savedPhysical) :: front)
        (.live oldTicket oldResult oldData.answer savedTarget oldData.scope frontTarget)
        savedOwners occurrence ticket data result captured capturedTarget outside outsideTarget
  | spent (header : OwnerHeader graph owners heap otherHandler otherOwner otherOccurrence oldData)
      (different : handler ≠ otherHandler ∨ owner ≠ otherOwner)
      (next : GeneralOwnerCut graph heap handler owner whole target front frontTarget savedOwners occurrence ticket data result captured capturedTarget outside outsideTarget) :
      GeneralOwnerCut graph heap handler owner (.clauseBoundary otherHandler otherOwner otherOccurrence oldTicket none :: whole)
        (.spent oldTicket oldData.answer oldData.scope target)
        (.clauseBoundary otherHandler otherOwner otherOccurrence oldTicket none :: front)
        (.spent oldTicket oldData.answer oldData.scope frontTarget)
        savedOwners occurrence ticket data result captured capturedTarget outside outsideTarget
  | retained (cursor : RetainedCursor graph heap physical lexical)
      (next : GeneralOwnerCut graph heap handler owner whole target front frontTarget savedOwners occurrence ticket data result captured capturedTarget outside outsideTarget) :
      GeneralOwnerCut graph heap handler owner (physical ++ whole) (lexical.append target)
        (physical ++ front) (lexical.append frontTarget) savedOwners occurrence ticket data result
        captured capturedTarget outside outsideTarget
  | split (wholeSegment : GeneralSegment graph heap whole target)
      (prefixSegment : GeneralSegment graph heap front frontTarget)
      (header : OwnerHeader graph savedOwners heap handler owner occurrence data)
      (saved : GeneralSegment graph heap captured capturedTarget)
      (outsideSegment : GeneralSegment graph heap outside outsideTarget)
      (shape : target = frontTarget.append (.live ticket result data.answer capturedTarget data.scope outsideTarget))
      (currentLookup : CoreMachine.findOwner handler owner whole = .ok ⟨front,handler,owner,occurrence,ticket,captured,outside⟩) :
      GeneralOwnerCut graph heap handler owner whole target front frontTarget savedOwners occurrence ticket data result captured capturedTarget outside outsideTarget

theorem GeneralOwnerCut.of_mapped
    (cut : MappedOwnerCut graph heap handler owner whole target front frontTarget savedOwners occurrence ticket data result captured capturedTarget outside outsideTarget) :
    GeneralOwnerCut graph heap handler owner (framesOf whole) target (framesOf front) frontTarget
      savedOwners occurrence ticket data result (framesOf captured) capturedTarget (framesOf outside) outsideTarget := by
  induction cut with
  | hit header captured outside => exact .hit header (.ordinary captured) (.ordinary outside)
  | push frame next ih => exact .push frame ih
  | live header different saved next ih => exact .live header different (.ordinary saved) ih
  | spent header different next ih => exact .spent header different ih

theorem GeneralOwnerCut.realizes
    (cut : GeneralOwnerCut graph heap handler owner whole target front frontTarget savedOwners occurrence ticket data result captured capturedTarget outside outsideTarget) :
    CoreMachine.findOwner handler owner whole = .ok ⟨front,handler,owner,occurrence,ticket,captured,outside⟩ ∧
    target = frontTarget.append (.live ticket result data.answer capturedTarget data.scope outsideTarget) ∧
    OwnerHeader graph savedOwners heap handler owner occurrence data ∧
    GeneralSegment graph heap whole target ∧ GeneralSegment graph heap front frontTarget ∧
    GeneralSegment graph heap captured capturedTarget ∧ GeneralSegment graph heap outside outsideTarget := by
  induction cut with
  | hit header captured outside =>
      exact ⟨by simp [CoreMachine.findOwner],rfl,header,.live header captured outside,.ordinary .nil,captured,outside⟩
  | push frame next ih =>
      obtain ⟨found,shape,header,whole,front,captured,outside⟩ := ih
      exact ⟨push_owner_pass frame found,congrArg (Stack.push _) shape,header,.push frame whole,.push frame front,captured,outside⟩
  | completion atom next ih =>
      obtain ⟨found,shape,header,whole,front,captured,outside⟩ := ih
      exact ⟨atom.owner_pass found,congrArg (Stack.push _) shape,header,
        by simpa [Stack.append] using GeneralSegment.append (.completion atom) whole,
        by simpa [Stack.append] using GeneralSegment.append (.completion atom) front,captured,outside⟩
  | live header different saved next ih =>
      obtain ⟨found,shape,selected,whole,front,captured,outside⟩ := ih
      refine ⟨?_,congrArg (Stack.live _ _ _ _ _) shape,selected,.live header saved whole,.live header saved front,captured,outside⟩
      rcases different with different | different <;>
        simp [CoreMachine.findOwner,different,found,Bind.bind,Except.bind,Pure.pure,Except.pure]
  | spent header different next ih =>
      obtain ⟨found,shape,selected,whole,front,captured,outside⟩ := ih
      refine ⟨?_,congrArg (Stack.spent _ _ _) shape,selected,.spent header whole,.spent header front,captured,outside⟩
      rcases different with different | different <;>
        simp [CoreMachine.findOwner,different,found,Bind.bind,Except.bind,Pure.pure,Except.pure]
  | retained cursor next ih =>
      obtain ⟨found,shape,header,whole,front,captured,outside⟩ := ih
      exact ⟨CoreGeneralStack.RetainedCursor.owner_lookup_pass cursor found,
        by simpa [stack_append_assoc] using congrArg (Stack.append _) shape,
        header,.append (.retained cursor) whole,.append (.retained cursor) front,captured,outside⟩
  | split whole prefixSegment header saved outside shape currentLookup =>
      exact ⟨currentLookup,shape,header,whole,prefixSegment,saved,outside⟩

/-- Extract an actual live owner and the same saved carrier. This supplies raw
correspondence; admitted-state ticket uniqueness is not inferred here. Resume
still requires current ResumeRel and scope resolution to this exact ticket. -/
theorem GeneralSegment.owner_extract
    (segment : GeneralSegment graph heap physical lexical)
    (found : CoreMachine.findOwner handler owner physical = .ok ⟨inside,handler,owner,occurrence,ticket,captured,outside⟩) :
    ∃ frontTarget savedOwners data result capturedTarget outsideTarget,
      GeneralOwnerCut graph heap handler owner physical lexical inside frontTarget savedOwners occurrence ticket data result captured capturedTarget outside outsideTarget := by
  obtain ⟨front,savedOwners,data,result,capturedTarget,outsideTarget,shape,header,before,saved,after⟩ := GeneralSegment.owner_split segment found
  exact ⟨front,savedOwners,data,result,capturedTarget,outsideTarget,.split segment before header saved after shape found⟩

def resumeBefore (base : CoreMachine.State) (handler owner : Nat) (value : CoreMachine.Value)
    (whole : List CoreMachine.Frame) : CoreMachine.State :=
  {base with control := .returned value,frames := .resume handler owner :: whole}

def resumeAfter (base : CoreMachine.State) (handler owner occurrence ticket : Nat) (value : CoreMachine.Value)
    (captured front outside : List CoreMachine.Frame) : CoreMachine.State :=
  {base with control := .returned value,frames := captured ++ front ++ .clauseBoundary handler owner occurrence ticket none :: outside,observations := base.observations ++ [.resumed ticket]}

/-- The same saved physical/lexical carrier is restored before caller work,
the consumed marker and outside. Completion values and local close pairs survive. -/
theorem resume_general {base : CoreMachine.State}
    (cut : GeneralOwnerCut graph base.heap handler owner whole target front frontTarget savedOwners occurrence ticket data result captured capturedTarget outside outsideTarget)
    (frame : ResumeRel graph frameOwners base.heap (.resume handler owner) plain)
    (context : plain.context = .resume binder)
    (value : ValueRel graph owners base.heap coreValue code)
    (resolve : plain.scope.resolve binder = some ticket) (runtimeScope : Scope) :
    GeneralStepWitness graph
      ⟨resumeBefore base handler owner coreValue whole,.eval ⟨.resume binder code,plain.scope,target⟩,
        owners,[(frameOwners,.resume handler owner)]⟩
      ⟨resumeAfter base handler owner occurrence ticket coreValue captured front outside,
        .eval ⟨code,plain.scope,capturedTarget.append (frontTarget.append (.spent ticket data.answer data.scope outsideTarget))⟩,
        owners,[]⟩ [] [.ticket ticket] := by
  obtain ⟨found,shape,header,current,frontSegment,capturedSegment,outsideSegment⟩ := cut.realizes
  have beforeStack := prepend_resume frame value.closed (pushed_mapped (.nil (graph := graph) (heap := base.heap))) runtimeScope
  simp only [context,Context.plug] at beforeStack
  have currentComponent : ComponentMapped graph owners [(frameOwners,.resume handler owner)]
      (isolate (resumeBefore base handler owner coreValue whole) [(frameOwners,.resume handler owner)])
      ⟨.resume binder code,plain.scope,.nil⟩ := ⟨rfl,code,runtimeScope,.returned value,beforeStack⟩
  have afterStack := capturedSegment.append (frontSegment.append (.spent (ticket := ticket) header outsideSegment))
  have successorComponent : ComponentMapped graph owners []
      (isolate (resumeAfter base handler owner occurrence ticket coreValue captured front outside) [])
      ⟨code,plain.scope,.nil⟩ := ⟨rfl,code,plain.scope,.returned value,pushed_mapped .nil⟩
  refine ⟨?_,?_,?_,?_⟩
  · simpa [attach,Stack.append] using GeneralRelated.evalSegment
      (state := resumeBefore base handler owner coreValue whole) current currentComponent (by rfl)
  · simp only [resumeBefore,resumeAfter,CoreMachine.next,CoreMachine.returnResume,found]
  · apply ordinary_step (allowed := by trivial)
    rw [shape]
    exact .resume binder ticket plain.scope data.scope result data.answer _ _ _ code value.closed resolve
  · simpa [attach,Stack.append,List.append_assoc] using GeneralRelated.evalSegment
      (state := resumeAfter base handler owner occurrence ticket coreValue captured front outside) afterStack successorComponent (by simp [resumeAfter,framesOf,List.append_assoc])

/-- Connect extraction to an actual resume redex with current scope evidence.
The result carries the same extracted cut and its derived two endpoints. -/
theorem resume_from_lookup {base : CoreMachine.State}
    (segment : GeneralSegment graph base.heap whole target)
    (found : CoreMachine.findOwner handler owner whole = .ok ⟨front,handler,owner,occurrence,ticket,captured,outside⟩)
    (frame : ResumeRel graph frameOwners base.heap (.resume handler owner) plain)
    (context : plain.context = .resume binder)
    (value : ValueRel graph owners base.heap coreValue code)
    (resolve : plain.scope.resolve binder = some ticket) (runtimeScope : Scope) :
    ∃ frontTarget savedOwners data result capturedTarget outsideTarget,
      GeneralOwnerCut graph base.heap handler owner whole target front frontTarget savedOwners occurrence ticket data result captured capturedTarget outside outsideTarget ∧
      GeneralStepWitness graph
        ⟨resumeBefore base handler owner coreValue whole,.eval ⟨.resume binder code,plain.scope,target⟩,
          owners,[(frameOwners,.resume handler owner)]⟩
        ⟨resumeAfter base handler owner occurrence ticket coreValue captured front outside,
          .eval ⟨code,plain.scope,capturedTarget.append (frontTarget.append (.spent ticket data.answer data.scope outsideTarget))⟩,
          owners,[]⟩ [] [.ticket ticket] := by
  obtain ⟨frontTarget,savedOwners,data,result,capturedTarget,outsideTarget,cut⟩ := GeneralSegment.owner_extract segment found
  exact ⟨frontTarget,savedOwners,data,result,capturedTarget,outsideTarget,cut,
    resume_general cut frame context value resolve runtimeScope⟩

/-- Administrative matching uses the existing isolated witnesses and strict
potential decrease. It cannot match an arbitrary Core step with zero target work. -/
inductive GeneralLink (graph : CoreSyntax.Graph) : CoreUnwindRelation.Point → CoreUnwindRelation.Point →
    List Owner → List Owner → Prop where
  | positive (step : GeneralStepWitness graph before after created discharged) : GeneralLink graph before after created discharged
  | administrative (segment : GeneralSegment graph before.heap physical lexical)
      (witness : CoreCleanupRunFrames.Administrative graph beforeOwners afterOwners beforeMaps afterMaps before after target)
      (beforeFrames : before.frames = framesOf beforeMaps ++ physical)
      (afterFrames : after.frames = framesOf afterMaps ++ physical)
      (core : CoreMachine.next graph before = .stepped after) :
      GeneralLink graph ⟨before,.eval (attach target lexical),beforeOwners,beforeMaps⟩
        ⟨after,.eval (attach target lexical),afterOwners,afterMaps⟩ [] []

theorem GeneralLink.endpoints (link : GeneralLink graph before after created discharged) :
    GeneralRelated graph before ∧ GeneralRelated graph after := by
  cases link with
  | positive step => exact ⟨step.current,step.successor⟩
  | administrative segment witness beforeFrames afterFrames core =>
      obtain ⟨current,successor,extension,decrease⟩ := witness.components
      exact ⟨.evalSegment segment current beforeFrames,.evalSegment (segment.heap_weaken extension) successor afterFrames⟩

theorem GeneralLink.core_next (link : GeneralLink graph before after created discharged) :
    CoreMachine.next graph before.state = .stepped after.state := by
  cases link with
  | positive step => exact step.core
  | administrative segment witness beforeFrames afterFrames core => exact core

theorem GeneralLink.target_trace (link : GeneralLink graph before after created discharged) :
    CoreUnwindRelation.Trace before.machine after.machine created discharged := by
  cases link with
  | positive step => exact step.target.trace
  | administrative => exact .refl _

inductive GeneralChain (graph : CoreSyntax.Graph) : CoreUnwindRelation.Point → List CoreUnwindRelation.Point →
    CoreUnwindRelation.Point → List Owner → List Owner → Prop where
  | last (link : GeneralLink graph before after created discharged) : GeneralChain graph before [after] after created discharged
  | next (link : GeneralLink graph before middle created discharged)
      (rest : GeneralChain graph middle points after laterCreated laterDischarged) :
      GeneralChain graph before (middle :: points) after (created ++ laterCreated) (laterDischarged ++ discharged)

theorem GeneralChain.endpoints (chain : GeneralChain graph before points after created discharged) :
    GeneralRelated graph before ∧ GeneralRelated graph after := by
  induction chain with
  | last link => exact link.endpoints
  | next link rest ih => exact ⟨link.endpoints.1,ih.2⟩

theorem GeneralChain.core_steps (chain : GeneralChain graph before points after created discharged) :
    CoreAllocationHistory.Steps graph points.length before.state after.state := by
  have extend : ∀ {count start}, CoreAllocationHistory.Steps graph count start before.state →
      CoreAllocationHistory.Steps graph (count + points.length) start after.state := by
    induction chain with
    | last link =>
        intro count start earlier
        exact CoreAllocationHistory.Steps.snoc earlier link.core_next
    | next link rest ih =>
        intro count start earlier
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (CoreAllocationHistory.Steps.snoc earlier link.core_next)
  simpa using extend (CoreAllocationHistory.Steps.refl before.state)

theorem GeneralChain.target_trace (chain : GeneralChain graph before points after created discharged) :
    CoreUnwindRelation.Trace before.machine after.machine created discharged := by
  induction chain with
  | last link => exact link.target_trace
  | next link rest ih => exact link.target_trace.append ih

theorem GeneralChain.accounting (chain : GeneralChain graph before points after created discharged) :
    (before.machine.stack.erase.owners ++ created).Perm (after.machine.stack.erase.owners ++ discharged) := by
  have linkAccounting : ∀ {a b c d}, GeneralLink graph a b c d →
      (a.machine.stack.erase.owners ++ c).Perm (b.machine.stack.erase.owners ++ d) := by
    intro a b c d link
    cases link with
    | positive witness => exact witness.accounting
    | administrative => exact .refl _
  induction chain with
  | last link => exact linkAccounting link
  | next link rest ih =>
      have first := linkAccounting link
      apply List.perm_iff_count.mpr
      intro owner
      have firstCount := first.count_eq owner
      have restCount := ih.count_eq owner
      simp only [List.count_append] at firstCount restCount ⊢
      omega

private theorem resume_unit_identity (related : EnvCloses graph owners heap environment source output) :
    ∀ binder, source = .resume binder .unit → output = .resume binder .unit := by
  induction related using EnvCloses.rec (motive_1 := fun _ _ _ _ _ => True) with
  | unit | boolean | integer | handle | location | closure => trivial
  | empty => intro binder same; exact same
  | binding replacement tail ihReplacement ihTail =>
      intro binder same
      exact ihTail binder (by simp [same,Code.subst])
  | resource tail ihTail =>
      intro binder same
      exact ihTail binder (by simp [same,Code.instantiate])
  | templateUnused absent tail ihTail => exact ihTail
  | templateExpand translated callable nonrecursive replacement closed tail ihReplacement ihTail =>
      intro binder same
      exact ihTail binder (by simp [same,Code.subst])

private theorem translation_unique
    (first : CoreTranslation.translateFuel graph fuel owners index = .ok rawCode)
    (second : CoreTranslation.translateFuel graph otherFuel owners index = .ok otherRaw) : rawCode = otherRaw := by
  have one := CoreTranslationFuel.success_mono graph fuel (max fuel otherFuel) owners index rawCode (Nat.le_max_left _ _) first
  have two := CoreTranslationFuel.success_mono graph otherFuel (max fuel otherFuel) owners index otherRaw (Nat.le_max_right _ _) second
  exact Except.ok.inj (one.symm.trans two)

/-- Three actual Core steps enter the immediate resume operand, return Unit,
and restore the same general capture. Only the last step moves the target;
the first two use the established decreasing administrative witnesses. -/
theorem immediate_resume_chain {base : CoreMachine.State}
    (ordered : Postorder graph)
    (known : graph.node resumeSite = some resumeNode)
    (kind : resumeNode.kind = .resume handler owner post unitSite)
    (translated : CoreTranslation.translateFuel graph fuel owners resumeSite = .ok (.resume binder .unit))
    (current : EnvCloses graph owners base.heap environment (.resume binder .unit) (.resume binder .unit))
    (unitKnown : graph.node unitSite = some unitNode) (unitKind : unitNode.kind = .unit)
    (header : OwnerHeader graph savedOwners base.heap handler owner occurrence data)
    (captured : GeneralSegment graph base.heap capturedPhysical capturedTarget)
    (outside : GeneralSegment graph base.heap outsidePhysical outsideTarget)
    (plain : PlainData) (context : plain.context = .resume binder)
    (scope : plain.scope = .ticket binder ticket) (result : Ty) :
    let physical := CoreMachine.Frame.clauseBoundary handler owner occurrence ticket (some capturedPhysical) :: outsidePhysical
    let ownerTarget := Stack.live ticket result data.answer capturedTarget data.scope outsideTarget
    let start : CoreMachine.State := {base with control := .evaluate resumeSite environment,frames := physical}
    let entered : CoreMachine.State := {start with control := .evaluate unitSite environment,frames := .resume handler owner :: physical,observations := start.observations ++ [.entered resumeSite]}
    let returned : CoreMachine.State := {entered with control := .returned .unit,observations := entered.observations ++ [.entered unitSite]}
    let restored := resumeAfter returned handler owner occurrence ticket .unit capturedPhysical [] outsidePhysical
    let focus : Configuration := ⟨.resume binder .unit,plain.scope,ownerTarget⟩
    let finalTarget : Configuration := ⟨.unit,plain.scope,capturedTarget.append (.spent ticket data.answer data.scope outsideTarget)⟩
    GeneralChain graph ⟨start,.eval focus,owners,[]⟩
      [⟨entered,.eval focus,owners,[(owners,.resume handler owner)]⟩,
        ⟨returned,.eval focus,owners,[(owners,.resume handler owner)]⟩,
        ⟨restored,.eval finalTarget,owners,[]⟩]
      ⟨restored,.eval finalTarget,owners,[]⟩ [] [.ticket ticket] := by
  dsimp only
  let physical := CoreMachine.Frame.clauseBoundary handler owner occurrence ticket (some capturedPhysical) :: outsidePhysical
  let ownerTarget := Stack.live ticket result data.answer capturedTarget data.scope outsideTarget
  let start : CoreMachine.State := {base with control := .evaluate resumeSite environment,frames := physical}
  let entered : CoreMachine.State := {start with control := .evaluate unitSite environment,frames := .resume handler owner :: physical,observations := start.observations ++ [.entered resumeSite]}
  let returned : CoreMachine.State := {entered with control := .returned .unit,observations := entered.observations ++ [.entered unitSite]}
  let focus : Configuration := ⟨.resume binder .unit,plain.scope,.nil⟩
  have segment : GeneralSegment graph base.heap physical ownerTarget := .live header captured outside
  have unit : ValueRel graph owners base.heap CoreMachine.Value.unit Code.unit := .unit
  obtain ⟨operandFuel,resolved,childTranslation⟩ := resume_translation_parts known kind translated
  have parts := resume_components current
  have frame : ResumeRel graph owners base.heap (.resume handler owner) plain :=
    .operand known kind translated resolved parts.2.2 context
  have entry : SilentMapped graph owners owners [] [(owners,.resume handler owner)]
      (isolate start []) (isolate entered [(owners,.resume handler owner)]) focus := by
    simpa [isolate,start,entered,focus,framesOf] using
      resume_entry_same_target_mapped (base := isolate start []) ordered known kind translated current unit.closed plain context .nil
  have entryActual : CoreMachine.next graph start = .stepped entered := by
    simpa [CoreSuffixSplice.appendFrames,isolate,start,entered,framesOf] using CoreSuffixSplice.next_append entry.core physical
  have enteredLink : GeneralLink graph ⟨start,.eval (attach focus ownerTarget),owners,[]⟩
      ⟨entered,.eval (attach focus ownerTarget),owners,[(owners,.resume handler owner)]⟩ [] [] :=
    .administrative segment (.traversal entry rfl) rfl rfl entryActual
  obtain ⟨unitEvaluation,unitTranslation⟩ := CoreAdministrativeSteps.unit_evaluate
    (base := isolate entered [(owners,.resume handler owner)]) unitKnown unitKind parts.2.1
    (framesOf [(owners,.resume handler owner)])
  have returnedStack := prepend_resume frame unit.closed (pushed_mapped (.nil (graph := graph) (heap := base.heap))) plain.scope
  simp only [context,Context.plug] at returnedStack
  have valueEntry : CoreAdministrativeTransport.TransportMapped graph owners owners
      [(owners,.resume handler owner)] [(owners,.resume handler owner)]
      (isolate entered [(owners,.resume handler owner)]) (isolate returned [(owners,.resume handler owner)]) focus := by
    simpa [returned,entered,isolate,focus,framesOf] using
      CoreAdministrativeTransport.value_entry_mapped unitEvaluation rfl rfl returnedStack
  have valueActual : CoreMachine.next graph entered = .stepped returned := by
    simpa [CoreSuffixSplice.appendFrames,isolate,entered,returned,framesOf] using CoreSuffixSplice.next_append valueEntry.core physical
  have returnedLink : GeneralLink graph ⟨entered,.eval (attach focus ownerTarget),owners,[(owners,.resume handler owner)]⟩
      ⟨returned,.eval (attach focus ownerTarget),owners,[(owners,.resume handler owner)]⟩ [] [] :=
    .administrative segment (.value valueEntry rfl) rfl rfl valueActual
  have cut : GeneralOwnerCut graph base.heap handler owner physical ownerTarget [] .nil savedOwners occurrence ticket data result
      capturedPhysical capturedTarget outsidePhysical outsideTarget := .hit header captured outside
  have resumed := resume_general (base := returned) cut frame context unit
    (by simp [scope,Execution.Scope.resolve]) plain.scope
  have restoredLink : GeneralLink graph
      ⟨returned,.eval (attach focus ownerTarget),owners,[(owners,.resume handler owner)]⟩
      ⟨resumeAfter returned handler owner occurrence ticket .unit capturedPhysical [] outsidePhysical,
        .eval ⟨.unit,plain.scope,capturedTarget.append (.spent ticket data.answer data.scope outsideTarget)⟩,owners,[]⟩
      [] [.ticket ticket] := by
    simpa [resumeBefore,returned,entered,focus,attach,Stack.append,physical] using GeneralLink.positive resumed
  simpa [attach,focus,Stack.append,start,entered,returned] using
    GeneralChain.next enteredLink (GeneralChain.next returnedLink (GeneralChain.last restoredLink))

/-- Capture, clause entry, operand return and resume form one connected chain
for arbitrary graphs, captured segments and saved completion values. The exact
immediate clause translation is current static evidence, not a future step. -/
theorem capture_immediate_resume {base : CoreMachine.State}
    (cut : GeneralHandlerCut graph base.heap requested whole target inside savedOwners site environment data outside cap tail)
    (known : graph.node site = some node) (kind : node.kind = .handler handler handled handlerBody clauses)
    (selected : clauses.find? (fun clause => clause.operation == operation) = some clause)
    (operand : ValueRel graph operandOwners base.heap value operandCode)
    (requestCarrier : EnvCloses graph operandOwners base.heap requestEnvironment
      (.perform effect operation .unit) (.perform (Instantiation.freezeEffect requested) operation .unit))
    (requestPlain : PlainData) (requestContext : requestPlain.context = .perform (Instantiation.freezeEffect requested) operation)
    (ready : ∀ parameter binder body, ClauseAt operation data.clauses parameter binder body → ClosedExcept parameter body)
    (operationResult : Ty) (runtimeScope : Scope)
    (ordered : Postorder graph)
    (resumeKnown : graph.node clause.body = some resumeNode)
    (resumeKind : resumeNode.kind = .resume handler clause.owner post unitSite)
    (resumeTranslation : CoreTranslation.translateFuel graph resumeFuel
      (⟨handler,clause.owner,CoreTranslation.ticket graph clause.owner⟩ :: savedOwners)
      clause.body = .ok (.resume (CoreTranslation.ticket graph clause.owner) .unit))
    (unitKnown : graph.node unitSite = some unitNode) (unitKind : unitNode.kind = .unit)
    (resumePlain : PlainData) (resumeContext : resumePlain.context = .resume (CoreTranslation.ticket graph clause.owner))
    (resumeScope : resumePlain.scope = .ticket (CoreTranslation.ticket graph clause.owner) base.nextOwner) :
    ∃ argument : CoreSyntax.Binder, clause.argument = .binder argument ∧
      let owners := ⟨handler,clause.owner,CoreTranslation.ticket graph clause.owner⟩ :: savedOwners
      let capturedPhysical := inside ++ [.handlerBoundary site environment data.activation]
      let start := captureBefore base value effect operation requestEnvironment whole
      let captured := captureAfter base clause argument.id value handler data.activation site environment inside outside
      let entered : CoreMachine.State := {captured with control := .evaluate unitSite (.binding argument.id value environment),frames := .resume handler clause.owner :: captured.frames,observations := captured.observations ++ [.entered clause.body]}
      let returned : CoreMachine.State := {entered with control := .returned .unit,observations := entered.observations ++ [.entered unitSite]}
      let restored := resumeAfter returned handler clause.owner data.activation base.nextOwner .unit capturedPhysical [] outside
      let requestTarget : Configuration := ⟨.perform (Instantiation.freezeEffect requested) operation operandCode,requestPlain.scope,target⟩
      let clauseTarget : Configuration := ⟨.resume (CoreTranslation.ticket graph clause.owner) .unit,resumePlain.scope,
        .live base.nextOwner operationResult data.answer cap data.scope tail⟩
      let finalTarget : Configuration := ⟨.unit,resumePlain.scope,cap.append (.spent base.nextOwner data.answer data.scope tail)⟩
      GeneralChain graph ⟨start,.eval requestTarget,operandOwners,[(operandOwners,.request effect operation requestEnvironment)]⟩
        [⟨captured,.eval clauseTarget,owners,[]⟩,
          ⟨entered,.eval clauseTarget,owners,[(owners,.resume handler clause.owner)]⟩,
          ⟨returned,.eval clauseTarget,owners,[(owners,.resume handler clause.owner)]⟩,
          ⟨restored,.eval finalTarget,owners,[]⟩]
        ⟨restored,.eval finalTarget,owners,[]⟩ [.ticket base.nextOwner] [.ticket base.nextOwner] := by
  obtain ⟨fuel,argument,rawBody,body,pattern,selection,bodyTranslation,clauseClosing,ownerHeader,capture⟩ :=
    capture_general cut known kind selected operand requestCarrier requestPlain requestContext ready operationResult runtimeScope
  have rawEq := translation_unique bodyTranslation resumeTranslation
  rw [rawEq] at clauseClosing
  have bodyEq := resume_unit_identity clauseClosing _ rfl
  rw [bodyEq] at clauseClosing capture
  have parts := cut.realizes
  have restored := immediate_resume_chain (base := captureAfter base clause argument.id value handler data.activation site environment inside outside)
    ordered resumeKnown resumeKind resumeTranslation clauseClosing unitKnown unitKind ownerHeader parts.2.2.2.1 parts.2.2.2.2
    resumePlain resumeContext resumeScope operationResult
  rw [resumeScope] at restored
  refine ⟨argument,pattern,?_⟩
  simpa [captureAfter,captureBefore,resumeAfter,resumeScope] using
    GeneralChain.next (GeneralLink.positive capture) restored

/-- The newly allocated physical owner retains the running marker. Core's
preflight rejects disposal before consumption, observations or counters change. -/
theorem captured_normal_discard_rejected (base : CoreMachine.State) (handler owner occurrence ticket identity : Nat)
    (saved : CoreMachine.Value) (remaining outside : List CoreMachine.Frame) :
    CoreMachine.next graph
      {base with control := .discard handler owner,frames := .clauseBoundary handler owner occurrence ticket (some (.cleanupCompletion identity saved :: remaining)) :: outside} = .rejected .runningCloseBlocked := by
  simp [CoreMachine.next,CoreMachine.discardOwner,CoreMachine.findOwner,CoreMachine.closeFuel,CoreMachine.framesMass]
  rfl

/-- Every protected obligation in the selected actual saved segment prevents
successful disposal, including obligations behind prefixes or nested owners. -/
theorem captured_protected_discard_no_step (base : CoreMachine.State)
    (cut : GeneralOwnerCut graph base.heap handler owner whole target front frontTarget savedOwners occurrence ticket data result captured capturedTarget outside outsideTarget)
    (obligation : ProtectedCapture captured) (after : CoreMachine.State) :
    CoreMachine.next graph {base with control := .discard handler owner,frames := whole} ≠ .stepped after := by
  have found := cut.realizes.1
  cases closed : CoreMachine.closeFuel (CoreMachine.framesMass captured + 1) captured with
  | error error => simp [CoreMachine.next,CoreMachine.discardOwner,found,closed]
  | ok pair => exact False.elim (obligation.close_no_success _ pair.1 pair.2 closed)

theorem resume_restores_exactly (base : CoreMachine.State) (handler owner occurrence ticket : Nat)
    (value : CoreMachine.Value) (captured front outside : List CoreMachine.Frame) :
    (resumeAfter base handler owner occurrence ticket value captured front outside).frames =
      captured ++ front ++ .clauseBoundary handler owner occurrence ticket none :: outside ∧
    (resumeAfter base handler owner occurrence ticket value captured front outside).observations =
      base.observations ++ [.resumed ticket] ∧
    (resumeAfter base handler owner occurrence ticket value captured front outside).nextOwner = base.nextOwner ∧
    (resumeAfter base handler owner occurrence ticket value captured front outside).heap = base.heap :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem immediate_capture_resume_observations (base : CoreMachine.State) (clause : CoreSyntax.Clause)
    (argument : Nat) (value : CoreMachine.Value) (handler occurrence site unitSite : Nat)
    (environment : CoreMachine.Environment) (inside outside : List CoreMachine.Frame) :
    let captured := captureAfter base clause argument value handler occurrence site environment inside outside
    let entered : CoreMachine.State := {captured with control := .evaluate unitSite environment,observations := captured.observations ++ [.entered clause.body]}
    let returned : CoreMachine.State := {entered with control := .returned .unit,observations := entered.observations ++ [.entered unitSite]}
    (resumeAfter returned handler clause.owner occurrence base.nextOwner .unit
      (inside ++ [.handlerBoundary site environment occurrence]) [] outside).observations =
      base.observations ++ [.captured occurrence base.nextOwner,.entered clause.body,.entered unitSite,.resumed base.nextOwner] := by
  simp [captureAfter,resumeAfter,List.append_assoc]

#print axioms GeneralStepWitness.of_legacy
#print axioms GeneralStepWitness.accounting
#print axioms GeneralSegment.handler_split
#print axioms GeneralSegment.handler_extract
#print axioms GeneralHandlerCut.of_mapped
#print axioms GeneralHandlerCut.realizes
#print axioms GeneralHandlerCut.header
#print axioms GeneralHandlerCut.retained_of_lookup
#print axioms capture_general
#print axioms GeneralSegment.owner_split
#print axioms GeneralSegment.owner_extract
#print axioms GeneralOwnerCut.of_mapped
#print axioms GeneralOwnerCut.realizes
#print axioms resume_general
#print axioms resume_from_lookup
#print axioms GeneralLink.endpoints
#print axioms GeneralLink.core_next
#print axioms GeneralLink.target_trace
#print axioms GeneralChain.endpoints
#print axioms GeneralChain.core_steps
#print axioms GeneralChain.target_trace
#print axioms GeneralChain.accounting
#print axioms immediate_resume_chain
#print axioms capture_immediate_resume
#print axioms captured_normal_discard_rejected
#print axioms captured_protected_discard_no_step
#print axioms positive_accounting
#print axioms resume_restores_exactly
#print axioms immediate_capture_resume_observations
end Ash.OneShot.CoreGeneralCaptureResume
