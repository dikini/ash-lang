import CoreRunningSplice
import CoreCellSteps
import SourceDependencyScopes

/-! Builtin selection in a running projected cleanup follows the same current
lexical scope and ownership ledger. Dormant cells cannot intercept the request;
no additional transparency checker or callback-success premise is used.
The current source selector is the dependency-scope selector; decorated source
selection reaches it through the existing contextual select_sound bridge.
This covers builtin requests in an authenticated retainedProjected tail, with
a mapped prefix. Nested running frames, source-handler capture into the tail,
issued-history freshness and whole-state static admission are separate. -/
namespace Ash.OneShot.CoreProjectedCellDispatch
open ScopedExpressions ScopedExecution CoreValueRelation CoreStrictStack CoreCellWriteFrames
  CoreRequestFrames CoreCleanupFrames CoreCleanupRunFrames CoreCleanupProjection CoreUnwindRelation

set_option linter.unusedSimpArgs false

/-- Selector-relevant scope realization suffices; callable typing is separate. -/
theorem selected_builtin_update
    (source : SourceDependencyCapture.Realizes tables families scope before)
    (found : SourceDependencyCapture.select (.cell identity) operation scope = some (.builtin identity)) :
    ∃ old, ∀ new, ∃ after, CellUpdate identity old new before after := by
  induction source with
  | nil => cases found
  | push frame tail ih =>
    cases frame with
    | cell =>
      simp only [SourceDependencyCapture.select] at found
      split at found
      · rename_i selected
        cases Instance.cell.inj selected
        exact ⟨_,fun _ => ⟨_,.hit⟩⟩
      · rename_i missed
        simp only [Option.map_eq_some_iff] at found
        obtain ⟨selected,selectedEq,mapped⟩ := found
        cases selected <;> cases mapped
        obtain ⟨old,update⟩ := ih selectedEq
        exact ⟨old,fun new => by
          obtain ⟨after,next⟩ := update new
          exact ⟨_,.push (by intro equal; apply missed; simpa [ExecFrame.erase,Frame.target] using equal.symm) next⟩⟩
    | handler =>
      simp only [SourceDependencyCapture.select] at found
      split at found
      · split at found <;> simp_all
      · rename_i missed
        simp only [Option.map_eq_some_iff] at found
        obtain ⟨selected,selectedEq,mapped⟩ := found
        cases selected <;> cases mapped
        obtain ⟨old,update⟩ := ih selectedEq
        exact ⟨old,fun new => by
          obtain ⟨after,next⟩ := update new
          exact ⟨_,.push (by intro equal; apply missed; simpa [ExecFrame.erase,HandlerData.erase,Frame.target] using equal.symm) next⟩⟩
    | plain | cleanup | running | unwinding | closing | retiring =>
      simp only [SourceDependencyCapture.select,Option.map_eq_some_iff] at found
      obtain ⟨selected,selectedEq,mapped⟩ := found
      cases selected <;> cases mapped
      obtain ⟨old,update⟩ := ih selectedEq
      exact ⟨old,fun new => by
        obtain ⟨after,next⟩ := update new
        exact ⟨_,.push (by simp [ExecFrame.erase,PlainData.erase,ActionData.erase,closeFrame,CloseItem.frame,Frame.target]) next⟩⟩
  | live saved tail ihSaved ih =>
      simp only [SourceDependencyCapture.select,Option.map_eq_some_iff] at found
      obtain ⟨selected,selectedEq,mapped⟩ := found
      cases selected <;> cases mapped
      obtain ⟨old,update⟩ := ih selectedEq
      exact ⟨old,fun new => by obtain ⟨after,next⟩ := update new; exact ⟨_,.live next⟩⟩
  | spent tail ih =>
      simp only [SourceDependencyCapture.select,Option.map_eq_some_iff] at found
      obtain ⟨selected,selectedEq,mapped⟩ := found
      cases selected <;> cases mapped
      obtain ⟨old,update⟩ := ih selectedEq
      exact ⟨old,fun new => by obtain ⟨after,next⟩ := update new; exact ⟨_,.spent next⟩⟩

/-- Recover the mapped cell cut from the current stack interpretation. -/
theorem pushed_update (before : PushedWithMaps graph heap maps target)
    (update : CellUpdate identity old new target changed) :
    ∃ changedMaps, WriteCut graph heap identity old new maps target changedMaps changed := by
  induction before generalizing changed with
  | nil => cases update
  | cons frame tail ih | initializer frame tail ih | request frame tail ih | resume frame tail ih =>
      cases update with
      | push miss next =>
        obtain ⟨after,cut⟩ := ih next
        first | exact ⟨_,.push (.ordinary frame) miss cut⟩
              | exact ⟨_,.push (.initializer frame) miss cut⟩
              | exact ⟨_,.push (.request frame) miss cut⟩
              | exact ⟨_,.push (.resume frame) miss cut⟩
  | cleanup frame tail ih => cases update with
    | push miss next => obtain ⟨after,cut⟩ := ih next; exact ⟨_,.push (.cleanup frame) miss cut⟩
  | boundary frame tail ih =>
      cases frame with
      | handler known kind translated header => cases update with
        | push miss next => obtain ⟨after,cut⟩ := ih next; exact ⟨_,.push (.boundary (.handler known kind translated header)) miss cut⟩
      | cell known kind => cases update with
        | hit => exact ⟨_,.hit known kind tail⟩
        | push miss next => obtain ⟨after,cut⟩ := ih next; exact ⟨_,.push (.boundary (.cell known kind)) miss cut⟩
  | live header saved tail ihSaved ih => cases update with
    | live next => obtain ⟨after,cut⟩ := ih next; exact ⟨_,.live header saved cut⟩
  | spent header tail ih => cases update with
    | spent next => obtain ⟨after,cut⟩ := ih next; exact ⟨_,.spent header cut⟩

/-- The selected cell is owned in the active outside, including beneath live clauses. -/
theorem update_owned (update : CellUpdate identity old new before after) :
    Owner.resource identity ∈ before.erase.owners := by
  induction update with
  | hit => simp [Stack.erase,ExecFrame.erase,Control.owners,Frame.owners]
  | push miss next ih => exact List.mem_append_right _ ih
  | live next ih => exact List.mem_cons_of_mem _ (List.mem_append_right _ ih)
  | spent next ih => exact ih

/-- Every physical resource in a retained projection has the same lexical owner.
A unique owner in the active outside consequently cannot be intercepted here. -/
theorem cursor_miss (cursor : RetainedCursor graph heap physical lexical)
    (absent : Owner.resource identity ∉ lexical.erase.owners)
    (selected : CoreMachine.findInterpreter graph (.cell (.activation identity)) rest = .ok (.cell cut)) :
    CoreMachine.findInterpreter graph (.cell (.activation identity)) (physical++rest) =
      .ok (.cell {cut with inside := physical++cut.inside}) := by
  induction cursor generalizing rest cut with
  | nil => exact selected
  | plain frame next ih | handler frame next ih =>
      exact ih (by simpa [Stack.erase,ExecFrame.erase,PlainData.erase,HandlerData.erase,Control.owners,Frame.owners] using absent) selected
  | @cell owners site key payload scope answer physical lexical frame next ih =>
      have different : identity ≠ key := by
        intro same; subst key; apply absent
        simp [Stack.erase,ExecFrame.erase,Control.owners,Frame.owners]
      have tail := ih (fun member => absent (List.mem_append_right _ member)) selected
      simp [CoreMachine.findInterpreter,different,tail,List.cons_append,Bind.bind,Except.bind,Pure.pure,Except.pure]
  | @armed owners action environment data physical lexical frame next ih =>
      have tail := ih (by simpa [Stack.erase,ExecFrame.erase,ActionData.erase,Control.owners,Frame.owners] using absent) selected
      simp [CoreMachine.findInterpreter,tail,List.cons_append,Bind.bind,Except.bind,Pure.pure,Except.pure]
  | live header saved outside ihSaved ihOutside =>
      have notSaved := fun member => absent (List.mem_cons_of_mem _ (List.mem_append_left _ member))
      have notOutside := fun member => absent (List.mem_cons_of_mem _ (List.mem_append_right _ member))
      have tail := ihOutside notOutside selected
      have whole := ihSaved notSaved tail
      simpa [List.append_assoc] using whole
  | spent header next ih => exact ih absent selected
  | retiring header next ih =>
      exact ih (fun member => absent (List.mem_append_right _ member)) selected

/-- One current target update constructs both retained and mapped residuals,
the exact nearest physical cut, and its actual replacement spine. -/
theorem cursor_update
    (cursor : RetainedCursor graph heap physical lexical)
    (outside : PushedWithMaps graph heap maps target)
    (unique : Unique (lexical.append (.push (.closing targetClose closeScope) target)).erase)
    (update : CellUpdate identity old new
      (lexical.append (.push (.closing targetClose closeScope) target)) changed) :
    ∃ changedPhysical changedLexical changedMaps changedTarget inside site rest,
      RetainedCursor graph heap changedPhysical changedLexical ∧
      PushedWithMaps graph heap changedMaps changedTarget ∧
      changed = changedLexical.append (.push (.closing targetClose closeScope) changedTarget) ∧
      physical++ .closeCompletion coreClose :: framesOf maps = inside++ .resourceBoundary site identity old :: rest ∧
      changedPhysical++ .closeCompletion coreClose :: framesOf changedMaps = inside++ .resourceBoundary site identity new :: rest ∧
      CoreMachine.findInterpreter graph (.cell (.activation identity))
        (physical++ .closeCompletion coreClose :: framesOf maps) = .ok (.cell ⟨inside,site,identity,old,rest⟩) := by
  induction cursor generalizing changed with
  | nil =>
      cases update with
      | push miss next =>
          obtain ⟨changedMaps,cut⟩ := pushed_update outside next
          obtain ⟨inside,site,rest,beforeEq,afterEq,selected⟩ := cut.realizes
          exact ⟨[],.nil,changedMaps,_,.closeCompletion coreClose::inside,site,rest,.nil,cut.components.2.1,rfl,
            by simp [beforeEq],by simp [afterEq],by simp [CoreMachine.findInterpreter,selected,Bind.bind,Except.bind,Pure.pure,Except.pure]⟩
  | plain frame next ih | handler frame next ih =>
      cases update with
      | push miss update =>
          obtain ⟨cp,cl,cm,ct,inside,site,rest,cur,out,same,be,ae,sel⟩ := ih (by
            simpa [Unique,Stack.append,Stack.erase,ExecFrame.erase,PlainData.erase,HandlerData.erase,Control.owners,Frame.owners] using unique) update
          first
          | exact ⟨cp,_,cm,ct,inside,site,rest,.plain frame cur,out,by simp [Stack.append,same],be,ae,sel⟩
          | exact ⟨cp,_,cm,ct,inside,site,rest,.handler frame cur,out,by simp [Stack.append,same],be,ae,sel⟩
  | @cell owners site key payload scope answer physical lexical frame next ih =>
      cases update with
      | hit =>
          cases frame with
          | cell known kind =>
              exact ⟨.resourceBoundary site identity new::physical,_,maps,target,[],site,
                physical++ .closeCompletion coreClose::framesOf maps,.cell (owners := owners) (.cell known kind) next,outside,rfl,
                by simp,by simp,by simp [CoreMachine.findInterpreter]⟩
      | push miss update =>
          have tailUnique : Unique _ := (List.nodup_append.mp unique).2.1
          obtain ⟨cp,cl,cm,ct,inside,selectedSite,rest,cur,out,same,be,ae,sel⟩ := ih tailUnique update
          have full := PushCarrier.cell_selector_miss (.boundary frame) miss sel
          exact ⟨.resourceBoundary site key payload::cp,_,cm,ct,.resourceBoundary site key payload::inside,
            selectedSite,rest,.cell frame cur,out,by simp [Stack.append,same],by simp [be],by simp [ae],by simpa [Instantiation.freezeEffect] using full⟩
  | @armed owners action environment data physical lexical frame next ih =>
      cases update with
      | push miss update =>
          have tailUnique : Unique _ := (List.nodup_append.mp unique).2.1
          obtain ⟨cp,cl,cm,ct,inside,site,rest,cur,out,same,be,ae,sel⟩ := ih tailUnique update
          have full := PushCarrier.cell_selector_miss (.cleanup frame) miss sel
          exact ⟨.cleanupBoundary action environment data.identity::cp,_,cm,ct,
            .cleanupBoundary action environment data.identity::inside,site,rest,.armed frame cur,out,
            by simp [Stack.append,same],by simp [be],by simp [ae],by simpa [Instantiation.freezeEffect] using full⟩
  | @live owners handler owner occurrence data savedPhysical savedTarget outsidePhysical outsideTarget ticket result header saved tail ihSaved ih =>
      cases update with
      | live update =>
          have separated : (savedTarget.erase.owners ++ (outsideTarget.append (.push (.closing targetClose closeScope) target)).erase.owners).Nodup := unique.tail
          have tailUnique : Unique _ := (List.nodup_append.mp separated).2.1
          have absent : Owner.resource identity ∉ savedTarget.erase.owners := by
            intro member
            exact (List.nodup_append.mp separated).2.2 _ member _ (update_owned update) rfl
          obtain ⟨cp,cl,cm,ct,inside,site,rest,cur,out,same,be,ae,sel⟩ := ih tailUnique update
          have selected := cursor_miss saved absent sel
          exact ⟨savedPhysical++cp,.live ticket result data.answer savedTarget data.scope cl,cm,ct,savedPhysical++inside,site,rest,.live header saved cur,out,
            by simp [Stack.append,same],by simp [List.append_assoc,be],by simp [List.append_assoc,ae],
            by simpa [List.append_assoc] using selected⟩
  | @spent owners handler owner occurrence data physical lexical ticket header next ih =>
      cases update with
      | spent update =>
          obtain ⟨cp,cl,cm,ct,inside,site,rest,cur,out,same,be,ae,sel⟩ := ih unique update
          exact ⟨cp,.spent ticket data.answer data.scope cl,cm,ct,inside,site,rest,.spent header cur,out,by simp [Stack.append,same],be,ae,sel⟩
  | @retiring owners handler owner occurrence data physical lexical ticket header next ih =>
      cases update with
      | push miss update =>
          obtain ⟨cp,cl,cm,ct,inside,site,rest,cur,out,same,be,ae,sel⟩ := ih unique.tail update
          exact ⟨cp,.push (.retiring ticket) cl,cm,ct,inside,site,rest,.retiring header cur,out,by simp [Stack.append,same],be,ae,sel⟩

/-- A current target cut either selects within the mapped prefix or crosses
that entire prefix. The latter branch derives physical selector extension. -/
theorem split_update (pending : PushedWithMaps graph heap maps target)
    (update : CellUpdate identity old new (target.append tail) changed) :
    (∃ changedMaps changedTarget, WriteCut graph heap identity old new maps target changedMaps changedTarget ∧
      changed = changedTarget.append tail) ∨
    (∃ inner, CellUpdate identity old new tail inner ∧ changed = target.append inner ∧
      ∀ rest cut, CoreMachine.findInterpreter graph (.cell (.activation identity)) rest = .ok (.cell cut) →
        CoreMachine.findInterpreter graph (.cell (.activation identity)) (framesOf maps++rest) =
          .ok (.cell {cut with inside := framesOf maps++cut.inside})) := by
  induction pending generalizing changed with
  | nil => exact .inr ⟨changed,update,rfl,fun _ _ selected => selected⟩
  | @cons owners core plain cores target frame next ih
  | @initializer owners core plain cores target frame next ih
  | @request owners core plain cores target frame next ih
  | @resume owners core plain cores target frame next ih =>
      cases update with
      | push miss update =>
        have carrier : CoreCaptureEntry.PushCarrier graph owners heap core (.plain plain) := by
          first | exact .ordinary frame | exact .initializer frame | exact .request frame | exact .resume frame | exact .cleanup frame
        rcases ih update with ⟨cm,ct,cut,same⟩ | ⟨inner,cut,same,selector⟩
        · exact .inl ⟨_,_,.push carrier miss cut,by simp [Stack.append,same]⟩
        · refine .inr ⟨inner,cut,by simp [Stack.append,same],?_⟩
          intro rest cut selected
          have full := CoreCellWriteFrames.PushCarrier.cell_selector_miss carrier miss (selector rest cut selected)
          simpa [framesOf_cons,Instantiation.freezeEffect] using full
  | @cleanup owners core data cores target frame next ih =>
      cases update with
      | push miss update =>
        rcases ih update with ⟨cm,ct,cut,same⟩ | ⟨inner,cut,same,selector⟩
        · exact .inl ⟨_,_,.push (.cleanup frame) miss cut,by simp [Stack.append,same]⟩
        · refine .inr ⟨inner,cut,by simp [Stack.append,same],?_⟩
          intro rest cut selected
          have full := CoreCellWriteFrames.PushCarrier.cell_selector_miss (.cleanup frame) miss (selector rest cut selected)
          simpa [framesOf_cons,Instantiation.freezeEffect] using full
  | @boundary owners core effectFrame cores target frame next ih =>
      cases frame with
      | handler known kind translated header => cases update with
        | push miss update =>
          rcases ih update with ⟨cm,ct,cut,same⟩ | ⟨inner,cut,same,selector⟩
          · exact .inl ⟨_,_,.push (.boundary (.handler known kind translated header)) miss cut,by simp [Stack.append,same]⟩
          · refine .inr ⟨inner,cut,by simp [Stack.append,same],?_⟩
            intro rest cut selected
            have full := CoreCellWriteFrames.PushCarrier.cell_selector_miss (.boundary (.handler known kind translated header)) miss (selector rest cut selected)
            simpa [framesOf_cons,Instantiation.freezeEffect] using full
      | cell known kind => cases update with
        | hit => exact .inl ⟨_,_,.hit known kind next,rfl⟩
        | push miss update =>
          rcases ih update with ⟨cm,ct,cut,same⟩ | ⟨inner,cut,same,selector⟩
          · exact .inl ⟨_,_,.push (.boundary (.cell known kind)) miss cut,by simp [Stack.append,same]⟩
          · refine .inr ⟨inner,cut,by simp [Stack.append,same],?_⟩
            intro rest cut selected
            have full := CoreCellWriteFrames.PushCarrier.cell_selector_miss (heap := heap) (owners := owners) (.boundary (.cell known kind)) miss (selector rest cut selected)
            simpa [framesOf_cons,Instantiation.freezeEffect] using full
  | @live owners handler owner occurrence data capturedMaps capturedTarget outsideMaps outsideTarget ticket result header saved next ihSaved ih =>
      cases update with
      | live update =>
        rcases ih update with ⟨cm,ct,cut,same⟩ | ⟨inner,cut,same,selector⟩
        · exact .inl ⟨_,_,.live header saved cut,by simp [Stack.append,same]⟩
        · refine .inr ⟨inner,cut,by simp [Stack.append,same],?_⟩
          intro rest cut selected
          simp [framesOf_cons,CoreMachine.findInterpreter,selector rest cut selected,Bind.bind,Except.bind,Pure.pure,Except.pure]
  | spent header next ih =>
      cases update with
      | spent update =>
        rcases ih update with ⟨cm,ct,cut,same⟩ | ⟨inner,cut,same,selector⟩
        · exact .inl ⟨_,_,.spent header cut,by simp [Stack.append,same]⟩
        · refine .inr ⟨inner,cut,by simp [Stack.append,same],?_⟩
          intro rest cut selected
          simp [framesOf_cons,CoreMachine.findInterpreter,selector rest cut selected,Bind.bind,Except.bind,Pure.pure,Except.pure]

def physicalTail (data : ActionData) (physical : List CoreMachine.Frame) (coreClose : Nat)
    (maps : List MappedFrame) : List CoreMachine.Frame :=
  .cleanupCompletion data.identity .unit :: physical ++ .closeCompletion coreClose :: framesOf maps

def lexicalTail (data : ActionData) (lexical : Stack) (targetClose : Nat) (closeScope : Scope) (target : Stack) : Stack :=
  .push (.unwinding data) (lexical.append (.push (.closing targetClose closeScope) target))

def beforePoint (base : CoreMachine.State) (effect : Instantiation.Effect) (operation : Nat)
    (environment : CoreMachine.Environment) (value : CoreMachine.Value) (operandCode : Code)
    (owners requestOwners : CoreTranslation.OwnerMap) (plain : PlainData)
    (pendingMaps : List MappedFrame) (pendingTarget : Stack) (data : ActionData)
    (physical : List CoreMachine.Frame) (lexical : Stack) (coreClose targetClose : Nat)
    (closeScope : Scope) (outsideMaps : List MappedFrame) (outsideTarget : Stack) : Point :=
  ⟨CoreSuffixSplice.appendFrames (CoreCellSteps.requestBefore base effect operation environment value pendingMaps)
      (physicalTail data physical coreClose outsideMaps),
    .eval (attach ⟨plain.context.plug operandCode,plain.scope,pendingTarget⟩
      (lexicalTail data lexical targetClose closeScope outsideTarget)),
    owners,(requestOwners,.request effect operation environment)::pendingMaps⟩

private theorem read_update {base : CoreMachine.State}
    (request : RequestRel graph requestOwners base.heap (.request effect 0 environment) plain)
    (context : plain.context = .perform (Instantiation.freezeEffect (.cell identity)) 0)
    (operand : ValueRel graph owners base.heap value (.resourceRef (.activation identity)))
    (pending : PushedWithMaps graph base.heap pendingMaps pendingTarget)
    (delayed : CleanupRel graph cleanupOwners base.heap (.cleanupBoundary action savedEnvironment data.identity) data)
    (cursor : RetainedCursor graph base.heap physical lexical)
    (outside : PushedWithMaps graph base.heap outsideMaps outsideTarget)
    (unique : Unique (pendingTarget.append (lexicalTail data lexical targetClose closeScope outsideTarget)).erase)
    (update : CellUpdate identity old old
      (pendingTarget.append (lexicalTail data lexical targetClose closeScope outsideTarget)) changed) :
    ∃ after, CoreResourceUnwind.StepWitness graph
      (beforePoint base effect 0 environment value (.resourceRef (.activation identity)) owners requestOwners plain
        pendingMaps pendingTarget data physical lexical coreClose targetClose closeScope outsideMaps outsideTarget)
      after [] [] ∧ after.state.control = .returned (.integer old) ∧
      after.state.observations = base.observations ++ [.read identity old] := by
  have carrier : RunningTail graph base.heap (physicalTail data physical coreClose outsideMaps)
      (lexicalTail data lexical targetClose closeScope outsideTarget) := .retainedProjected delayed cursor outside
  rcases split_update pending update with ⟨cm,ct,cut,_same⟩ | ⟨inner,cut,fullSame,extend⟩
  · obtain ⟨current,actual,target,successor⟩ := CoreCellSteps.read_complete request context operand cut .none
    have witness := CoreRunningSplice.running_positive (before := CoreCellSteps.requestBefore base effect 0 environment value pendingMaps) carrier current actual (.one target) successor
    refine ⟨⟨CoreSuffixSplice.appendFrames (CoreCellSteps.readAfter base identity old pendingMaps)
      (physicalTail data physical coreClose outsideMaps),
      .eval (attach ⟨.integer old,plain.scope,pendingTarget⟩ (lexicalTail data lexical targetClose closeScope outsideTarget)),
      owners,pendingMaps⟩,?_,rfl,rfl⟩
    simpa [beforePoint,attach,context,Context.plug] using witness
  · cases cut with
    | push _miss cut =>
      have tailUnique : Unique (lexical.append (.push (.closing targetClose closeScope) outsideTarget)).erase := by
        have suffix := (List.nodup_append.mp (show
          (pendingTarget.erase.owners ++ (lexicalTail data lexical targetClose closeScope outsideTarget).erase.owners).Nodup from
          by simpa [Unique,erase_append,owners_append] using unique)).2.1
        exact suffix.tail
      obtain ⟨cp,cl,cm,ct,inside,site,rest,cur,out,tailSame,be,ae,selected⟩ := cursor_update (coreClose := coreClose) cursor outside tailUnique cut
      have selectedFull := extend (physicalTail data physical coreClose outsideMaps)
        {inside := .cleanupCompletion data.identity .unit::inside,node := site,key := identity,payload := old,outside := rest}
        (by simp [physicalTail,CoreMachine.findInterpreter,selected,Bind.bind,Except.bind,Pure.pure,Except.pure])
      have actualEffect := CoreCellSteps.request_effect request context
      have decoded := CoreCellSteps.handle_operand operand
      let afterState : CoreMachine.State := { base with
          control := .returned (.integer old)
          frames := framesOf pendingMaps ++ physicalTail data cp coreClose cm
          observations := base.observations ++ [.read identity old] }
      let afterTarget : Configuration := attach ⟨.integer old,plain.scope,pendingTarget⟩ (lexicalTail data cl targetClose closeScope ct)
      let afterPoint : Point := ⟨afterState,.eval afterTarget,owners,pendingMaps⟩
      have currentComponent : ComponentMapped graph owners ((requestOwners,.request effect 0 environment)::pendingMaps)
          (isolate (beforePoint base effect 0 environment value (.resourceRef (.activation identity)) owners requestOwners plain
            pendingMaps pendingTarget data physical lexical coreClose targetClose closeScope outsideMaps outsideTarget).state
            ((requestOwners,.request effect 0 environment)::pendingMaps))
          ⟨.perform (Instantiation.freezeEffect (.cell identity)) 0 (.resourceRef (.activation identity)),plain.scope,pendingTarget⟩ := by
        refine ⟨rfl,_,.none,.returned operand,?_⟩
        have stack := prepend_request request operand.closed (pushed_mapped pending) .none
        simpa [context,Context.plug,beforePoint,isolate,CoreSuffixSplice.appendFrames,CoreCellSteps.requestBefore] using stack
      have successorComponent : ComponentMapped graph owners pendingMaps (isolate afterState pendingMaps)
          ⟨.integer old,plain.scope,pendingTarget⟩ :=
        ⟨rfl,_,plain.scope,.returned .integer,pushed_mapped pending⟩
      refine ⟨afterPoint,⟨?_,?_,?_,?_⟩,rfl,rfl⟩
      · simpa [beforePoint,context,Context.plug] using
          Related.runningCleanup (state := (beforePoint base effect 0 environment value (.resourceRef (.activation identity)) owners requestOwners plain pendingMaps pendingTarget data physical lexical coreClose targetClose closeScope outsideMaps outsideTarget).state) carrier currentComponent (by rfl)
      · have changedEq : framesOf pendingMaps ++ physicalTail data cp coreClose cm =
            framesOf pendingMaps ++ physicalTail data physical coreClose outsideMaps := by
          have equal := ae.trans be.symm
          simp only [physicalTail,List.cons_append]
          rw [equal]
        simp [beforePoint,CoreSuffixSplice.appendFrames,CoreCellSteps.requestBefore,CoreMachine.next,CoreMachine.request,
          actualEffect,selectedFull,CoreMachine.interpretCell,CoreMachine.cellOperand,decoded,afterPoint,afterState,changedEq]
      · have target : RawStep
          ⟨.perform (Instantiation.freezeEffect (.cell identity)) 0 (.resourceRef (.activation identity)),plain.scope,
            pendingTarget.append (lexicalTail data lexical targetClose closeScope outsideTarget)⟩
          ⟨.integer old,plain.scope,pendingTarget.append (lexicalTail data cl targetClose closeScope ct)⟩ [] [] :=
          .readCell identity old plain.scope _ _ (by simpa [fullSame,tailSame,lexicalTail,Stack.append] using update)
        simpa [beforePoint,afterPoint,afterTarget,attach,context,Context.plug] using
          Positive.one (LexicalUnwind.Transition.evaluate target (by trivial))
      · exact .runningCleanup (.retainedProjected delayed cur out) successorComponent rfl

private theorem write_update {base : CoreMachine.State}
    (request : RequestRel graph requestOwners base.heap (.request effect 1 environment) plain)
    (context : plain.context = .perform (Instantiation.freezeEffect (.cell identity)) 1)
    (operand : ValueRel graph owners base.heap value (.pair (.resourceRef (.activation identity)) (.integer written)))
    (pending : PushedWithMaps graph base.heap pendingMaps pendingTarget)
    (delayed : CleanupRel graph cleanupOwners base.heap (.cleanupBoundary action savedEnvironment data.identity) data)
    (cursor : RetainedCursor graph base.heap physical lexical)
    (outside : PushedWithMaps graph base.heap outsideMaps outsideTarget)
    (unique : Unique (pendingTarget.append (lexicalTail data lexical targetClose closeScope outsideTarget)).erase)
    (update : CellUpdate identity old written
      (pendingTarget.append (lexicalTail data lexical targetClose closeScope outsideTarget)) changed) :
    ∃ after, CoreResourceUnwind.StepWitness graph
      (beforePoint base effect 1 environment value (.pair (.resourceRef (.activation identity)) (.integer written)) owners requestOwners plain
        pendingMaps pendingTarget data physical lexical coreClose targetClose closeScope outsideMaps outsideTarget)
      after [] [] ∧ after.state.control = .returned (.unit) ∧
      after.state.observations = base.observations ++ [.written identity written] := by
  have carrier : RunningTail graph base.heap (physicalTail data physical coreClose outsideMaps)
      (lexicalTail data lexical targetClose closeScope outsideTarget) := .retainedProjected delayed cursor outside
  rcases split_update pending update with ⟨cm,ct,cut,_same⟩ | ⟨inner,cut,fullSame,extend⟩
  · obtain ⟨current,actual,target,successor⟩ := CoreCellSteps.write_complete request context operand cut .none
    have witness := CoreRunningSplice.running_positive (before := CoreCellSteps.requestBefore base effect 1 environment value pendingMaps) carrier current actual (.one target) successor
    refine ⟨⟨CoreSuffixSplice.appendFrames (CoreCellSteps.writeAfter base identity written cm)
      (physicalTail data physical coreClose outsideMaps),
      .eval (attach ⟨.unit,plain.scope,ct⟩ (lexicalTail data lexical targetClose closeScope outsideTarget)),
      owners,cm⟩,?_,rfl,rfl⟩
    simpa [beforePoint,attach,context,Context.plug] using witness
  · cases cut with
    | push _miss cut =>
      have tailUnique : Unique (lexical.append (.push (.closing targetClose closeScope) outsideTarget)).erase := by
        have suffix := (List.nodup_append.mp (show
          (pendingTarget.erase.owners ++ (lexicalTail data lexical targetClose closeScope outsideTarget).erase.owners).Nodup from
          by simpa [Unique,erase_append,owners_append] using unique)).2.1
        exact suffix.tail
      obtain ⟨cp,cl,cm,ct,inside,site,rest,cur,out,tailSame,be,ae,selected⟩ := cursor_update (coreClose := coreClose) cursor outside tailUnique cut
      have selectedFull := extend (physicalTail data physical coreClose outsideMaps)
        {inside := .cleanupCompletion data.identity .unit::inside,node := site,key := identity,payload := old,outside := rest}
        (by simp [physicalTail,CoreMachine.findInterpreter,selected,Bind.bind,Except.bind,Pure.pure,Except.pure])
      have actualEffect := CoreCellSteps.request_effect request context
      obtain ⟨index,valueEq,known⟩ := CoreCellSteps.write_operand operand
      let afterState : CoreMachine.State := { base with
          control := .returned (.unit)
          frames := framesOf pendingMaps ++ physicalTail data cp coreClose cm
          observations := base.observations ++ [.written identity written] }
      let afterTarget : Configuration := attach ⟨.unit,plain.scope,pendingTarget⟩ (lexicalTail data cl targetClose closeScope ct)
      let afterPoint : Point := ⟨afterState,.eval afterTarget,owners,pendingMaps⟩
      have currentComponent : ComponentMapped graph owners ((requestOwners,.request effect 1 environment)::pendingMaps)
          (isolate (beforePoint base effect 1 environment value (.pair (.resourceRef (.activation identity)) (.integer written)) owners requestOwners plain
            pendingMaps pendingTarget data physical lexical coreClose targetClose closeScope outsideMaps outsideTarget).state
            ((requestOwners,.request effect 1 environment)::pendingMaps))
          ⟨.perform (Instantiation.freezeEffect (.cell identity)) 1 (.pair (.resourceRef (.activation identity)) (.integer written)),plain.scope,pendingTarget⟩ := by
        refine ⟨rfl,_,.none,.returned operand,?_⟩
        have stack := prepend_request request operand.closed (pushed_mapped pending) .none
        simpa [context,Context.plug,beforePoint,isolate,CoreSuffixSplice.appendFrames,CoreCellSteps.requestBefore] using stack
      have successorComponent : ComponentMapped graph owners pendingMaps (isolate afterState pendingMaps)
          ⟨.unit,plain.scope,pendingTarget⟩ :=
        ⟨rfl,_,plain.scope,.returned .unit,pushed_mapped pending⟩
      refine ⟨afterPoint,⟨?_,?_,?_,?_⟩,rfl,rfl⟩
      · simpa [beforePoint,context,Context.plug] using
          Related.runningCleanup (state := (beforePoint base effect 1 environment value (.pair (.resourceRef (.activation identity)) (.integer written)) owners requestOwners plain pendingMaps pendingTarget data physical lexical coreClose targetClose closeScope outsideMaps outsideTarget).state) carrier currentComponent (by rfl)
      · have changedEq : framesOf pendingMaps ++ physicalTail data cp coreClose cm = framesOf pendingMaps ++ .cleanupCompletion data.identity .unit :: inside ++ .resourceBoundary site identity written :: rest := by simp [physicalTail,ae,List.append_assoc]

        simp [beforePoint,CoreSuffixSplice.appendFrames,CoreCellSteps.requestBefore,CoreMachine.next,CoreMachine.request,
          actualEffect,selectedFull,CoreMachine.interpretCell,CoreMachine.cellOperand,known,valueEq,afterPoint,afterState,changedEq]
      · have target : RawStep
          ⟨.perform (Instantiation.freezeEffect (.cell identity)) 1 (.pair (.resourceRef (.activation identity)) (.integer written)),plain.scope,
            pendingTarget.append (lexicalTail data lexical targetClose closeScope outsideTarget)⟩
          ⟨.unit,plain.scope,pendingTarget.append (lexicalTail data cl targetClose closeScope ct)⟩ [] [] :=
          .writeCell identity old written plain.scope _ _ (by simpa [fullSame,tailSame,lexicalTail,Stack.append] using update)
        simpa [beforePoint,afterPoint,afterTarget,attach,context,Context.plug] using
          Positive.one (LexicalUnwind.Transition.evaluate target (by trivial))
      · exact .runningCleanup (.retainedProjected delayed cur out) successorComponent rfl

/-- The current source-selected builtin and ledger construct the runtime cut.
Neither physical selection nor a future related endpoint is supplied. -/
theorem read_dispatch {base : CoreMachine.State}
    (request : RequestRel graph requestOwners base.heap (.request effect 0 environment) plain)
    (context : plain.context = .perform (Instantiation.freezeEffect (.cell identity)) 0)
    (operand : ValueRel graph owners base.heap value (.resourceRef (.activation identity)))
    (pending : PushedWithMaps graph base.heap pendingMaps pendingTarget)
    (delayed : CleanupRel graph cleanupOwners base.heap (.cleanupBoundary action savedEnvironment data.identity) data)
    (cursor : RetainedCursor graph base.heap physical lexical)
    (outside : PushedWithMaps graph base.heap outsideMaps outsideTarget)
    (source : SourceDependencyCapture.Realizes tables families scope
      (pendingTarget.append (lexicalTail data lexical targetClose closeScope outsideTarget)))
    (selected : SourceDependencyCapture.select (.cell identity) 0 scope = some (.builtin identity))
    (ledger : Ledger ⟨(pendingTarget.append (lexicalTail data lexical targetClose closeScope outsideTarget)).erase,
      issued,completed⟩) :
    ∃ old after, CoreResourceUnwind.StepWitness graph
      (beforePoint base effect 0 environment value (.resourceRef (.activation identity)) owners requestOwners plain
        pendingMaps pendingTarget data physical lexical coreClose targetClose closeScope outsideMaps outsideTarget)
      after [] [] ∧ after.state.control = .returned (.integer old) ∧
      after.state.observations = base.observations ++ [.read identity old] := by
  obtain ⟨old,updates⟩ := selected_builtin_update source selected
  obtain ⟨changed,update⟩ := updates old
  have unique := ledger_unique_live ledger
  obtain ⟨after,witness,control,observations⟩ := read_update request context operand pending delayed cursor outside unique update
  exact ⟨old,after,witness,control,observations⟩

/-- The current source-selected builtin and ledger construct the runtime cut.
Neither physical selection nor a future related endpoint is supplied. -/
theorem write_dispatch {base : CoreMachine.State}
    (request : RequestRel graph requestOwners base.heap (.request effect 1 environment) plain)
    (context : plain.context = .perform (Instantiation.freezeEffect (.cell identity)) 1)
    (operand : ValueRel graph owners base.heap value (.pair (.resourceRef (.activation identity)) (.integer written)))
    (pending : PushedWithMaps graph base.heap pendingMaps pendingTarget)
    (delayed : CleanupRel graph cleanupOwners base.heap (.cleanupBoundary action savedEnvironment data.identity) data)
    (cursor : RetainedCursor graph base.heap physical lexical)
    (outside : PushedWithMaps graph base.heap outsideMaps outsideTarget)
    (source : SourceDependencyCapture.Realizes tables families scope
      (pendingTarget.append (lexicalTail data lexical targetClose closeScope outsideTarget)))
    (selected : SourceDependencyCapture.select (.cell identity) 1 scope = some (.builtin identity))
    (ledger : Ledger ⟨(pendingTarget.append (lexicalTail data lexical targetClose closeScope outsideTarget)).erase,
      issued,completed⟩) :
    ∃ after, CoreResourceUnwind.StepWitness graph
      (beforePoint base effect 1 environment value (.pair (.resourceRef (.activation identity)) (.integer written)) owners requestOwners plain
        pendingMaps pendingTarget data physical lexical coreClose targetClose closeScope outsideMaps outsideTarget)
      after [] [] ∧ after.state.control = .returned (.unit) ∧
      after.state.observations = base.observations ++ [.written identity written] := by
  obtain ⟨old,updates⟩ := selected_builtin_update source selected
  obtain ⟨changed,update⟩ := updates written
  have unique := ledger_unique_live ledger
  exact write_update request context operand pending delayed cursor outside unique update

/-- Ownership multiplicities refer to the exact transition witness returned
by dispatch, with no created or discharged owner in a builtin cell operation. -/
theorem dispatch_accounting (witness : CoreResourceUnwind.StepWitness graph before after [] []) :
    before.machine.stack.erase.owners.Perm after.machine.stack.erase.owners := by
  simpa using CoreRunningSplice.running_accounting witness

#print axioms selected_builtin_update
#print axioms pushed_update
#print axioms update_owned
#print axioms cursor_miss
#print axioms cursor_update
#print axioms split_update
#print axioms read_dispatch
#print axioms write_dispatch
#print axioms dispatch_accounting
end Ash.OneShot.CoreProjectedCellDispatch
