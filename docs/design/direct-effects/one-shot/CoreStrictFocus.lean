import CoreOrdinaryCompletion
import CoreEffectEntry
import CoreCaptureEntry
import CoreResumeEntry
import CoreCleanupEntry
import CoreCellWriteFrames

/-! Strict focus and return transitions over the current translated expression
and arbitrary authenticated mapped tail. Value-ready administrative traversal
remains in CoreStrictPotential; completed operations retain their existing rules.
The other non-value operands use CoreCaptureEntry.request_focus_mapped and
CoreResumeEntry.resume_focus_mapped directly. Supported cleanup stores a value
callback, so its action-focus position has no transition. -/
namespace Ash.OneShot.CoreStrictFocus
open ScopedExpressions ScopedExecution CoreValueRelation CoreStrictFrames CoreStrictStack
open CoreStrictPotential CoreOrdinaryCompletion CoreEffectFrames CoreResumeFrames

/-- A non-value tuple left child moves both machines to that same child. -/
theorem pair_left_focus {base : CoreMachine.State}
    (known : graph.node site = some node) (kind : node.kind = .tuple [left, right])
    (lt : CoreTranslation.translateFuel graph fuel owners left = .ok rawLeft)
    (rt : CoreTranslation.translateFuel graph fuel owners right = .ok rawRight)
    (current : EnvCloses graph owners base.heap environment (.pair rawLeft rawRight) (.pair leftCode rightCode))
    (notValue : ¬ leftCode.IsValue) (plain : PlainData) (context : plain.context = .pairLeft rightCode)
    (older : PushedWithMaps graph base.heap annotations target) :
    ComponentMapped graph owners annotations
      {base with control := .evaluate site environment, frames := framesOf annotations}
      ⟨.pair leftCode rightCode,plain.scope,target⟩ ∧
    CoreMachine.next graph {base with control := .evaluate site environment, frames := framesOf annotations} =
      .stepped {base with control := .evaluate left environment, frames := .tupleLeft right environment :: framesOf annotations, observations := base.observations ++ [.entered site]} ∧
    RawStep ⟨.pair leftCode rightCode,plain.scope,target⟩ ⟨leftCode,plain.scope,.push (.plain plain) target⟩ [] [] ∧
    ComponentMapped graph owners ((owners,.tupleLeft right environment) :: annotations)
      {base with control := .evaluate left environment, frames := .tupleLeft right environment :: framesOf annotations, observations := base.observations ++ [.entered site]}
      ⟨leftCode,plain.scope,.push (.plain plain) target⟩ ∧
    CoreInitialPrefix.Link graph
      ⟨{base with control := .evaluate site environment, frames := framesOf annotations},⟨.pair leftCode rightCode,plain.scope,target⟩,owners,annotations⟩
      ⟨{base with control := .evaluate left environment, frames := .tupleLeft right environment :: framesOf annotations, observations := base.observations ++ [.entered site]},⟨leftCode,plain.scope,.push (.plain plain) target⟩,owners,((owners,.tupleLeft right environment) :: annotations)⟩ := by
  obtain ⟨leftSaved,rightSaved⟩ := CoreCellWriteFrames.pair_components current
  have translated : CoreTranslation.translateFuel graph (fuel + 1) owners site = .ok (.pair rawLeft rawRight) := by
    cases node with
    | mk original type effects source nodeKind =>
      cases kind
      simp only [CoreTranslation.translateFuel,CoreTranslation.requireNode,known]
      change (do pure (Code.pair (← CoreTranslation.translateFuel graph fuel owners left)
        (← CoreTranslation.translateFuel graph fuel owners right))) = _
      rw [lt,rt]; rfl
  have frame : PlainFrameRel graph owners base.heap (.tupleLeft right environment) plain := by
    change FrameRel graph owners base.heap _ plain.context
    rw [context]; exact .tupleLeft rt rightSaved
  have next : CoreMachine.next graph {base with control := .evaluate site environment, frames := framesOf annotations} = .stepped {base with control := .evaluate left environment, frames := .tupleLeft right environment :: framesOf annotations, observations := base.observations ++ [.entered site]} := by
    cases node with
    | mk original type effects source nodeKind => cases kind; simp only [CoreMachine.next,known]
  have beforeMapped : ComponentMapped graph owners annotations
      {base with control := .evaluate site environment, frames := framesOf annotations}
      ⟨.pair leftCode rightCode,plain.scope,target⟩ := ⟨rfl,_,plain.scope,.evaluate translated current,pushed_mapped older⟩
  have actualNext : CoreMachine.next graph {base with control := .evaluate site environment, frames := framesOf annotations} =
      .stepped {base with control := .evaluate left environment, frames := .tupleLeft right environment :: framesOf annotations, observations := base.observations ++ [.entered site]} := next
  have focused : RawStep ⟨.pair leftCode rightCode,plain.scope,target⟩ ⟨leftCode,plain.scope,.push (.plain plain) target⟩ [] [] := .focus plain (by rw [context]; exact .pairLeft notValue) target
  have afterMapped : ComponentMapped graph owners ((owners,.tupleLeft right environment) :: annotations)
      {base with control := .evaluate left environment, frames := .tupleLeft right environment :: framesOf annotations, observations := base.observations ++ [.entered site]}
      ⟨leftCode,plain.scope,.push (.plain plain) target⟩ := ⟨rfl,_,plain.scope,.evaluate lt leftSaved,pushed_mapped (.cons frame older)⟩
  exact ⟨beforeMapped,actualNext,focused,afterMapped,
    .positive beforeMapped actualNext (.one focused) afterMapped⟩

/-- Returning a left value reconstructs the pair before focusing its non-value
right child. The saved map, rather than the returned value's map, is restored. -/
theorem pair_right_focus {base : CoreMachine.State}
    (translated : CoreTranslation.translateFuel graph fuel savedOwners right = .ok rawRight)
    (saved : EnvCloses graph savedOwners base.heap environment rawRight rightCode)
    (left : ValueRel graph owners base.heap leftValue leftCode) (notValue : ¬ rightCode.IsValue)
    (before after : PlainData) (bc : before.context = .pairLeft rightCode) (ac : after.context = .pairRight leftCode)
    (sameScope : after.scope = before.scope) (runtimeScope : Scope)
    (older : PushedWithMaps graph base.heap annotations target) :
    ComponentMapped graph owners ((savedOwners,.tupleLeft right environment) :: annotations)
      {base with control := .returned leftValue, frames := .tupleLeft right environment :: framesOf annotations}
      ⟨leftCode,runtimeScope,.push (.plain before) target⟩ ∧
    CoreMachine.next graph {base with control := .returned leftValue, frames := .tupleLeft right environment :: framesOf annotations} =
      .stepped {base with control := .evaluate right environment, frames := .tupleRight leftValue :: framesOf annotations} ∧
    RawStep ⟨leftCode,runtimeScope,.push (.plain before) target⟩ ⟨.pair leftCode rightCode,before.scope,target⟩ [] [] ∧
    RawStep ⟨.pair leftCode rightCode,before.scope,target⟩ ⟨rightCode,after.scope,.push (.plain after) target⟩ [] [] ∧
    ComponentMapped graph savedOwners ((savedOwners,.tupleRight leftValue) :: annotations)
      {base with control := .evaluate right environment, frames := .tupleRight leftValue :: framesOf annotations}
      ⟨rightCode,after.scope,.push (.plain after) target⟩ ∧
    CoreInitialPrefix.Link graph
      ⟨{base with control := .returned leftValue, frames := .tupleLeft right environment :: framesOf annotations},⟨leftCode,runtimeScope,.push (.plain before) target⟩,owners,((savedOwners,.tupleLeft right environment) :: annotations)⟩
      ⟨{base with control := .evaluate right environment, frames := .tupleRight leftValue :: framesOf annotations},⟨rightCode,after.scope,.push (.plain after) target⟩,savedOwners,((savedOwners,.tupleRight leftValue) :: annotations)⟩ := by
  have first : PlainFrameRel graph savedOwners base.heap (.tupleLeft right environment) before := by
    change FrameRel graph savedOwners base.heap _ before.context
    rw [bc]; exact .tupleLeft translated saved
  have second : PlainFrameRel graph savedOwners base.heap (.tupleRight leftValue) after := by
    change FrameRel graph savedOwners base.heap _ after.context
    rw [ac]; exact .tupleRight (left.owner_transport savedOwners)
  have plug := RawStep.plug before leftCode left.closed runtimeScope target
  simp only [bc,Context.plug] at plug
  have focus : RawStep ⟨.pair leftCode rightCode,before.scope,target⟩ ⟨rightCode,after.scope,.push (.plain after) target⟩ [] [] := by
    rw [← sameScope]
    exact .focus after (by rw [ac]; exact .pairRight left.closed.1 notValue) target
  have beforeMapped : ComponentMapped graph owners ((savedOwners,.tupleLeft right environment) :: annotations)
      {base with control := .returned leftValue, frames := .tupleLeft right environment :: framesOf annotations}
      ⟨leftCode,runtimeScope,.push (.plain before) target⟩ := ⟨rfl,_,runtimeScope,.returned left,pushed_mapped (.cons first older)⟩
  have actualNext : CoreMachine.next graph {base with control := .returned leftValue, frames := .tupleLeft right environment :: framesOf annotations} =
      .stepped {base with control := .evaluate right environment, frames := .tupleRight leftValue :: framesOf annotations} := rfl
  have focused : RawStep ⟨.pair leftCode rightCode,before.scope,target⟩ ⟨rightCode,after.scope,.push (.plain after) target⟩ [] [] := focus
  have afterMapped : ComponentMapped graph savedOwners ((savedOwners,.tupleRight leftValue) :: annotations)
      {base with control := .evaluate right environment, frames := .tupleRight leftValue :: framesOf annotations}
      ⟨rightCode,after.scope,.push (.plain after) target⟩ := ⟨rfl,_,after.scope,.evaluate translated saved,pushed_mapped (.cons second older)⟩
  have plugged : RawStep ⟨leftCode,runtimeScope,.push (.plain before) target⟩ ⟨.pair leftCode rightCode,before.scope,target⟩ [] [] := plug
  have allowed : LexicalUnwind.ordinary leftCode := by
    have value := left.closed.1
    cases leftCode <;> simp_all [Code.IsValue,LexicalUnwind.ordinary]
  exact ⟨beforeMapped,actualNext,plugged,focused,afterMapped,
    .positive beforeMapped actualNext (.next plugged (.one focused) allowed) afterMapped⟩

/-- The existing raw application-focus proof supplies the same closing and
frame witnesses used to construct both mapped endpoints. -/
theorem application_function_focus {base : CoreMachine.State}
    (known : graph.node site = some node) (kind : node.kind = .apply function argument)
    (ft : CoreTranslation.translateFuel graph fuel owners function = .ok rawFunction)
    (argt : CoreTranslation.translateFuel graph fuel owners argument = .ok rawArgument)
    (current : EnvCloses graph owners base.heap environment (.app rawFunction rawArgument) (.app functionCode argumentCode))
    (notValue : ¬ functionCode.IsValue) (plain : PlainData) (context : plain.context = .appFunction argumentCode)
    (older : PushedWithMaps graph base.heap annotations target) :
    ComponentMapped graph owners annotations
      {base with control := .evaluate site environment, frames := framesOf annotations}
      ⟨.app functionCode argumentCode,plain.scope,target⟩ ∧
    CoreMachine.next graph {base with control := .evaluate site environment, frames := framesOf annotations} =
      .stepped {base with control := .evaluate function environment, frames := .applyFunction argument environment :: framesOf annotations, observations := base.observations ++ [.entered site]} ∧
    RawStep ⟨.app functionCode argumentCode,plain.scope,target⟩ ⟨functionCode,plain.scope,.push (.plain plain) target⟩ [] [] ∧
    ComponentMapped graph owners ((owners,.applyFunction argument environment) :: annotations)
      {base with control := .evaluate function environment, frames := .applyFunction argument environment :: framesOf annotations, observations := base.observations ++ [.entered site]}
      ⟨functionCode,plain.scope,.push (.plain plain) target⟩ ∧
    CoreInitialPrefix.Link graph
      ⟨{base with control := .evaluate site environment, frames := framesOf annotations},⟨.app functionCode argumentCode,plain.scope,target⟩,owners,annotations⟩
      ⟨{base with control := .evaluate function environment, frames := .applyFunction argument environment :: framesOf annotations, observations := base.observations ++ [.entered site]},⟨functionCode,plain.scope,.push (.plain plain) target⟩,owners,((owners,.applyFunction argument environment) :: annotations)⟩ := by
  obtain ⟨next,focus,_,saved,frame⟩ := application_focus known kind ft argt current notValue plain context (framesOf annotations) target
  have translated : CoreTranslation.translateFuel graph (fuel + 1) owners site = .ok (.app rawFunction rawArgument) := by
    cases node with
    | mk original type effects source nodeKind =>
      cases kind
      simp only [CoreTranslation.translateFuel,CoreTranslation.requireNode,known]
      change (do pure (Code.app (← CoreTranslation.translateFuel graph fuel owners function)
        (← CoreTranslation.translateFuel graph fuel owners argument))) = _
      rw [ft,argt]; rfl
  have beforeMapped : ComponentMapped graph owners annotations
      {base with control := .evaluate site environment, frames := framesOf annotations}
      ⟨.app functionCode argumentCode,plain.scope,target⟩ := ⟨rfl,_,plain.scope,.evaluate translated current,pushed_mapped older⟩
  have actualNext : CoreMachine.next graph {base with control := .evaluate site environment, frames := framesOf annotations} =
      .stepped {base with control := .evaluate function environment, frames := .applyFunction argument environment :: framesOf annotations, observations := base.observations ++ [.entered site]} := next
  have focused : RawStep ⟨.app functionCode argumentCode,plain.scope,target⟩ ⟨functionCode,plain.scope,.push (.plain plain) target⟩ [] [] := focus
  have afterMapped : ComponentMapped graph owners ((owners,.applyFunction argument environment) :: annotations)
      {base with control := .evaluate function environment, frames := .applyFunction argument environment :: framesOf annotations, observations := base.observations ++ [.entered site]}
      ⟨functionCode,plain.scope,.push (.plain plain) target⟩ := ⟨rfl,_,plain.scope,.evaluate ft saved,pushed_mapped (.cons frame older)⟩
  exact ⟨beforeMapped,actualNext,focused,afterMapped,
    .positive beforeMapped actualNext (.one focused) afterMapped⟩

/-- Function return performs plug then focus, restoring the argument's saved
owner map while retaining arbitrary older mapped frames. -/
theorem application_argument_focus {base : CoreMachine.State}
    (translated : CoreTranslation.translateFuel graph fuel savedOwners argument = .ok rawArgument)
    (saved : EnvCloses graph savedOwners base.heap environment rawArgument argumentCode)
    (function : ValueRel graph owners base.heap functionValue functionCode) (notValue : ¬ argumentCode.IsValue)
    (before after : PlainData) (bc : before.context = .appFunction argumentCode) (ac : after.context = .appArgument functionCode)
    (sameScope : after.scope = before.scope) (runtimeScope : Scope)
    (older : PushedWithMaps graph base.heap annotations target) :
    ComponentMapped graph owners ((savedOwners,.applyFunction argument environment) :: annotations)
      {base with control := .returned functionValue, frames := .applyFunction argument environment :: framesOf annotations}
      ⟨functionCode,runtimeScope,.push (.plain before) target⟩ ∧
    CoreMachine.next graph {base with control := .returned functionValue, frames := .applyFunction argument environment :: framesOf annotations} =
      .stepped {base with control := .evaluate argument environment, frames := .applyArgument functionValue :: framesOf annotations} ∧
    RawStep ⟨functionCode,runtimeScope,.push (.plain before) target⟩ ⟨.app functionCode argumentCode,before.scope,target⟩ [] [] ∧
    RawStep ⟨.app functionCode argumentCode,before.scope,target⟩ ⟨argumentCode,after.scope,.push (.plain after) target⟩ [] [] ∧
    ComponentMapped graph savedOwners ((savedOwners,.applyArgument functionValue) :: annotations)
      {base with control := .evaluate argument environment, frames := .applyArgument functionValue :: framesOf annotations}
      ⟨argumentCode,after.scope,.push (.plain after) target⟩ ∧
    CoreInitialPrefix.Link graph
      ⟨{base with control := .returned functionValue, frames := .applyFunction argument environment :: framesOf annotations},⟨functionCode,runtimeScope,.push (.plain before) target⟩,owners,((savedOwners,.applyFunction argument environment) :: annotations)⟩
      ⟨{base with control := .evaluate argument environment, frames := .applyArgument functionValue :: framesOf annotations},⟨argumentCode,after.scope,.push (.plain after) target⟩,savedOwners,((savedOwners,.applyArgument functionValue) :: annotations)⟩ := by
  obtain ⟨next,plug,focus,second,_,first⟩ := application_return_function translated saved
    (function.owner_transport savedOwners) notValue before after bc ac sameScope runtimeScope (framesOf annotations) target
  have beforeMapped : ComponentMapped graph owners ((savedOwners,.applyFunction argument environment) :: annotations)
      {base with control := .returned functionValue, frames := .applyFunction argument environment :: framesOf annotations}
      ⟨functionCode,runtimeScope,.push (.plain before) target⟩ := ⟨rfl,_,runtimeScope,.returned function,pushed_mapped (.cons first older)⟩
  have actualNext : CoreMachine.next graph {base with control := .returned functionValue, frames := .applyFunction argument environment :: framesOf annotations} =
      .stepped {base with control := .evaluate argument environment, frames := .applyArgument functionValue :: framesOf annotations} := next
  have focused : RawStep ⟨.app functionCode argumentCode,before.scope,target⟩ ⟨argumentCode,after.scope,.push (.plain after) target⟩ [] [] := focus
  have afterMapped : ComponentMapped graph savedOwners ((savedOwners,.applyArgument functionValue) :: annotations)
      {base with control := .evaluate argument environment, frames := .applyArgument functionValue :: framesOf annotations}
      ⟨argumentCode,after.scope,.push (.plain after) target⟩ := ⟨rfl,_,after.scope,.evaluate translated saved,pushed_mapped (.cons second older)⟩
  have plugged : RawStep ⟨functionCode,runtimeScope,.push (.plain before) target⟩ ⟨.app functionCode argumentCode,before.scope,target⟩ [] [] := plug
  have allowed : LexicalUnwind.ordinary functionCode := by
    have value := function.closed.1
    cases functionCode <;> simp_all [Code.IsValue,LexicalUnwind.ordinary]
  exact ⟨beforeMapped,actualNext,plugged,focused,afterMapped,
    .positive beforeMapped actualNext (.next plugged (.one focused) allowed) afterMapped⟩

/-- Non-value bind entry saves the same closed suffix used by the existing
mapped bind return/completion theorem. -/
theorem bind_focus {base : CoreMachine.State}
    (known : graph.node site = some node) (kind : node.kind = .bind binder initializer body)
    (it : CoreTranslation.translateFuel graph fuel owners initializer = .ok rawInitializer)
    (bt : CoreTranslation.translateFuel graph fuel owners body = .ok rawBody)
    (current : EnvCloses graph owners base.heap environment
      (.bind binder.id rawInitializer rawBody) (.bind binder.id initializerCode suffix))
    (notValue : ¬ initializerCode.IsValue) (ready : ClosedExcept binder.id suffix)
    (plain : PlainData) (context : plain.context = .bind binder.id suffix)
    (older : PushedWithMaps graph base.heap annotations target) :
    ComponentMapped graph owners annotations
      {base with control := .evaluate site environment, frames := framesOf annotations}
      ⟨.bind binder.id initializerCode suffix,plain.scope,target⟩ ∧
    CoreMachine.next graph {base with control := .evaluate site environment, frames := framesOf annotations} =
      .stepped {base with control := .evaluate initializer environment, frames := .bind binder.id body environment :: framesOf annotations, observations := base.observations ++ [.entered site]} ∧
    RawStep ⟨.bind binder.id initializerCode suffix,plain.scope,target⟩ ⟨initializerCode,plain.scope,.push (.plain plain) target⟩ [] [] ∧
    ComponentMapped graph owners ((owners,.bind binder.id body environment) :: annotations)
      {base with control := .evaluate initializer environment, frames := .bind binder.id body environment :: framesOf annotations, observations := base.observations ++ [.entered site]}
      ⟨initializerCode,plain.scope,.push (.plain plain) target⟩ ∧
    CoreInitialPrefix.Link graph
      ⟨{base with control := .evaluate site environment, frames := framesOf annotations},⟨.bind binder.id initializerCode suffix,plain.scope,target⟩,owners,annotations⟩
      ⟨{base with control := .evaluate initializer environment, frames := .bind binder.id body environment :: framesOf annotations, observations := base.observations ++ [.entered site]},⟨initializerCode,plain.scope,.push (.plain plain) target⟩,owners,((owners,.bind binder.id body environment) :: annotations)⟩ := by
  obtain ⟨initializerSaved,bodySaved⟩ := bind_components current
  have frame : PlainFrameRel graph owners base.heap (.bind binder.id body environment) plain := by
    change FrameRel graph owners base.heap _ plain.context
    rw [context]; exact .bind bt bodySaved ready
  have translated : CoreTranslation.translateFuel graph (fuel + 1) owners site = .ok (.bind binder.id rawInitializer rawBody) := by
    cases node with
    | mk original type effects source nodeKind =>
      cases kind
      simp only [CoreTranslation.translateFuel,CoreTranslation.requireNode,known]
      change (do pure (Code.bind binder.id (← CoreTranslation.translateFuel graph fuel owners initializer)
        (← CoreTranslation.translateFuel graph fuel owners body))) = _
      rw [it,bt]; rfl
  have next : CoreMachine.next graph {base with control := .evaluate site environment, frames := framesOf annotations} = .stepped {base with control := .evaluate initializer environment, frames := .bind binder.id body environment :: framesOf annotations, observations := base.observations ++ [.entered site]} := by
    cases node with
    | mk original type effects source nodeKind => cases kind; simp only [CoreMachine.next,known]
  have beforeMapped : ComponentMapped graph owners annotations
      {base with control := .evaluate site environment, frames := framesOf annotations}
      ⟨.bind binder.id initializerCode suffix,plain.scope,target⟩ := ⟨rfl,_,plain.scope,.evaluate translated current,pushed_mapped older⟩
  have actualNext : CoreMachine.next graph {base with control := .evaluate site environment, frames := framesOf annotations} =
      .stepped {base with control := .evaluate initializer environment, frames := .bind binder.id body environment :: framesOf annotations, observations := base.observations ++ [.entered site]} := next
  have focused : RawStep ⟨.bind binder.id initializerCode suffix,plain.scope,target⟩ ⟨initializerCode,plain.scope,.push (.plain plain) target⟩ [] [] := .focus plain (by rw [context]; exact .bind notValue) target
  have afterMapped : ComponentMapped graph owners ((owners,.bind binder.id body environment) :: annotations)
      {base with control := .evaluate initializer environment, frames := .bind binder.id body environment :: framesOf annotations, observations := base.observations ++ [.entered site]}
      ⟨initializerCode,plain.scope,.push (.plain plain) target⟩ := ⟨rfl,_,plain.scope,.evaluate it initializerSaved,pushed_mapped (.cons frame older)⟩
  exact ⟨beforeMapped,actualNext,focused,afterMapped,
    .positive beforeMapped actualNext (.one focused) afterMapped⟩

/-- Unit match is the other supported Core realization of a bind focus.
Both dummy absence certificates are retained; Core creates no dummy binding. -/
theorem unit_match_focus {base : CoreMachine.State}
    (known : graph.node site = some node) (kind : node.kind = .matchCases scrutinee [⟨.unit,body⟩])
    (st : CoreTranslation.translateFuel graph fuel owners scrutinee = .ok rawScrutinee)
    (bt : CoreTranslation.translateFuel graph fuel owners body = .ok rawBody)
    (current : EnvCloses graph owners base.heap environment
      (.bind (CoreTranslation.dummy graph site) rawScrutinee rawBody)
      (.bind (CoreTranslation.dummy graph site) scrutineeCode suffix))
    (rawAbsent : Syntax.Dependency.variable (CoreTranslation.dummy graph site) ∉ rawBody.dependencies)
    (absent : Syntax.Dependency.variable (CoreTranslation.dummy graph site) ∉ suffix.dependencies)
    (notValue : ¬ scrutineeCode.IsValue) (ready : ClosedExcept (CoreTranslation.dummy graph site) suffix)
    (plain : PlainData) (context : plain.context = .bind (CoreTranslation.dummy graph site) suffix)
    (older : PushedWithMaps graph base.heap annotations target) :
    ComponentMapped graph owners annotations
      {base with control := .evaluate site environment, frames := framesOf annotations}
      ⟨.bind (CoreTranslation.dummy graph site) scrutineeCode suffix,plain.scope,target⟩ ∧
    CoreMachine.next graph {base with control := .evaluate site environment, frames := framesOf annotations} =
      .stepped {base with control := .evaluate scrutinee environment, frames := .matchCases [⟨.unit,body⟩] environment :: framesOf annotations, observations := base.observations ++ [.entered site]} ∧
    RawStep ⟨.bind (CoreTranslation.dummy graph site) scrutineeCode suffix,plain.scope,target⟩
      ⟨scrutineeCode,plain.scope,.push (.plain plain) target⟩ [] [] ∧
    ComponentMapped graph owners ((owners,.matchCases [⟨.unit,body⟩] environment) :: annotations)
      {base with control := .evaluate scrutinee environment, frames := .matchCases [⟨.unit,body⟩] environment :: framesOf annotations, observations := base.observations ++ [.entered site]}
      ⟨scrutineeCode,plain.scope,.push (.plain plain) target⟩ ∧
    CoreInitialPrefix.Link graph
      ⟨{base with control := .evaluate site environment, frames := framesOf annotations},⟨.bind (CoreTranslation.dummy graph site) scrutineeCode suffix,plain.scope,target⟩,owners,annotations⟩
      ⟨{base with control := .evaluate scrutinee environment, frames := .matchCases [⟨.unit,body⟩] environment :: framesOf annotations, observations := base.observations ++ [.entered site]},⟨scrutineeCode,plain.scope,.push (.plain plain) target⟩,owners,((owners,.matchCases [⟨.unit,body⟩] environment) :: annotations)⟩ := by
  obtain ⟨scrutineeSaved,bodySaved⟩ := bind_components current
  have bodyClosed := bodySaved.lambda_argument_at _ _ _ .unit rfl rfl
    (ValueRel.unit (graph := graph) (owners := owners) (heap := base.heap)).closed
  rw [ScopedTyping.subst_absent rawBody _ .unit rawAbsent,ScopedTyping.subst_absent suffix _ .unit absent] at bodyClosed
  have frame : PlainFrameRel graph owners base.heap (.matchCases [⟨.unit,body⟩] environment) plain := by
    change FrameRel graph owners base.heap _ plain.context
    rw [context]; exact .unitMatch known kind bt bodyClosed absent ready
  have translated : CoreTranslation.translateFuel graph (fuel + 1) owners site = .ok (.bind (CoreTranslation.dummy graph site) rawScrutinee rawBody) := by
    cases node with
    | mk original type effects source nodeKind =>
      cases kind
      simp only [CoreTranslation.translateFuel,CoreTranslation.requireNode,known]
      change (do pure (Code.bind (CoreTranslation.dummy graph site)
        (← CoreTranslation.translateFuel graph fuel owners scrutinee) (← CoreTranslation.translateFuel graph fuel owners body))) = _
      rw [st,bt]; rfl
  have next : CoreMachine.next graph {base with control := .evaluate site environment, frames := framesOf annotations} = .stepped {base with control := .evaluate scrutinee environment, frames := .matchCases [⟨.unit,body⟩] environment :: framesOf annotations, observations := base.observations ++ [.entered site]} := by
    cases node with
    | mk original type effects source nodeKind => cases kind; simp only [CoreMachine.next,known]
  have beforeMapped : ComponentMapped graph owners annotations
      {base with control := .evaluate site environment, frames := framesOf annotations}
      ⟨.bind (CoreTranslation.dummy graph site) scrutineeCode suffix,plain.scope,target⟩ := ⟨rfl,_,plain.scope,.evaluate translated current,pushed_mapped older⟩
  have actualNext : CoreMachine.next graph {base with control := .evaluate site environment, frames := framesOf annotations} =
      .stepped {base with control := .evaluate scrutinee environment, frames := .matchCases [⟨.unit,body⟩] environment :: framesOf annotations, observations := base.observations ++ [.entered site]} := next
  have focused : RawStep ⟨.bind (CoreTranslation.dummy graph site) scrutineeCode suffix,plain.scope,target⟩
      ⟨scrutineeCode,plain.scope,.push (.plain plain) target⟩ [] [] := .focus plain (by rw [context]; exact .bind notValue) target
  have afterMapped : ComponentMapped graph owners ((owners,.matchCases [⟨.unit,body⟩] environment) :: annotations)
      {base with control := .evaluate scrutinee environment, frames := .matchCases [⟨.unit,body⟩] environment :: framesOf annotations, observations := base.observations ++ [.entered site]}
      ⟨scrutineeCode,plain.scope,.push (.plain plain) target⟩ := ⟨rfl,_,plain.scope,.evaluate st scrutineeSaved,pushed_mapped (.cons frame older)⟩
  exact ⟨beforeMapped,actualNext,focused,afterMapped,
    .positive beforeMapped actualNext (.one focused) afterMapped⟩

/-- Both actual Boolean arm orders focus the same closed condition and retain
both saved alternatives. Completion stays in boolean_match_complete. -/
theorem boolean_focus {base : CoreMachine.State}
    (known : graph.node site = some node)
    (kind : node.kind = .matchCases scrutinee (CoreStrictSteps.booleanArms yes no reversed))
    (st : CoreTranslation.translateFuel graph fuel owners scrutinee = .ok rawScrutinee)
    (yt : CoreTranslation.translateFuel graph fuel owners yes = .ok rawYes)
    (nt : CoreTranslation.translateFuel graph fuel owners no = .ok rawNo)
    (current : EnvCloses graph owners base.heap environment
      (.branch rawScrutinee rawYes rawNo) (.branch scrutineeCode yesCode noCode))
    (notValue : ¬ scrutineeCode.IsValue) (plain : PlainData) (context : plain.context = .branch yesCode noCode)
    (older : PushedWithMaps graph base.heap annotations target) :
    ComponentMapped graph owners annotations
      {base with control := .evaluate site environment, frames := framesOf annotations}
      ⟨.branch scrutineeCode yesCode noCode,plain.scope,target⟩ ∧
    CoreMachine.next graph {base with control := .evaluate site environment, frames := framesOf annotations} =
      .stepped {base with control := .evaluate scrutinee environment, frames := .matchCases (CoreStrictSteps.booleanArms yes no reversed) environment :: framesOf annotations, observations := base.observations ++ [.entered site]} ∧
    RawStep ⟨.branch scrutineeCode yesCode noCode,plain.scope,target⟩ ⟨scrutineeCode,plain.scope,.push (.plain plain) target⟩ [] [] ∧
    ComponentMapped graph owners ((owners,.matchCases (CoreStrictSteps.booleanArms yes no reversed) environment) :: annotations)
      {base with control := .evaluate scrutinee environment, frames := .matchCases (CoreStrictSteps.booleanArms yes no reversed) environment :: framesOf annotations, observations := base.observations ++ [.entered site]}
      ⟨scrutineeCode,plain.scope,.push (.plain plain) target⟩ ∧
    CoreInitialPrefix.Link graph
      ⟨{base with control := .evaluate site environment, frames := framesOf annotations},⟨.branch scrutineeCode yesCode noCode,plain.scope,target⟩,owners,annotations⟩
      ⟨{base with control := .evaluate scrutinee environment, frames := .matchCases (CoreStrictSteps.booleanArms yes no reversed) environment :: framesOf annotations, observations := base.observations ++ [.entered site]},⟨scrutineeCode,plain.scope,.push (.plain plain) target⟩,owners,((owners,.matchCases (CoreStrictSteps.booleanArms yes no reversed) environment) :: annotations)⟩ := by
  obtain ⟨scrutineeSaved,yesSaved,noSaved⟩ := branch_components current
  have frame : PlainFrameRel graph owners base.heap (.matchCases (CoreStrictSteps.booleanArms yes no reversed) environment) plain := by
    change FrameRel graph owners base.heap _ plain.context
    rw [context]; exact .booleanMatch yt nt yesSaved noSaved
  have translated : CoreTranslation.translateFuel graph (fuel + 1) owners site = .ok (.branch rawScrutinee rawYes rawNo) := by
    cases node with
    | mk original type effects source nodeKind =>
      cases kind
      cases reversed <;> simp only [CoreStrictSteps.booleanArms,Bool.false_eq_true,↓reduceIte,
        CoreTranslation.translateFuel,CoreTranslation.requireNode,known] <;>
        change (do pure (Code.branch (← CoreTranslation.translateFuel graph fuel owners scrutinee)
          (← CoreTranslation.translateFuel graph fuel owners yes) (← CoreTranslation.translateFuel graph fuel owners no))) = _ <;>
        rw [st,yt,nt] <;> rfl
  have next : CoreMachine.next graph {base with control := .evaluate site environment, frames := framesOf annotations} = .stepped {base with control := .evaluate scrutinee environment, frames := .matchCases (CoreStrictSteps.booleanArms yes no reversed) environment :: framesOf annotations, observations := base.observations ++ [.entered site]} := by
    cases node with
    | mk original type effects source nodeKind => cases kind; simp only [CoreMachine.next,known]
  have beforeMapped : ComponentMapped graph owners annotations
      {base with control := .evaluate site environment, frames := framesOf annotations}
      ⟨.branch scrutineeCode yesCode noCode,plain.scope,target⟩ := ⟨rfl,_,plain.scope,.evaluate translated current,pushed_mapped older⟩
  have actualNext : CoreMachine.next graph {base with control := .evaluate site environment, frames := framesOf annotations} =
      .stepped {base with control := .evaluate scrutinee environment, frames := .matchCases (CoreStrictSteps.booleanArms yes no reversed) environment :: framesOf annotations, observations := base.observations ++ [.entered site]} := next
  have focused : RawStep ⟨.branch scrutineeCode yesCode noCode,plain.scope,target⟩ ⟨scrutineeCode,plain.scope,.push (.plain plain) target⟩ [] [] := .focus plain (by rw [context]; exact .branch notValue) target
  have afterMapped : ComponentMapped graph owners ((owners,.matchCases (CoreStrictSteps.booleanArms yes no reversed) environment) :: annotations)
      {base with control := .evaluate scrutinee environment, frames := .matchCases (CoreStrictSteps.booleanArms yes no reversed) environment :: framesOf annotations, observations := base.observations ++ [.entered site]}
      ⟨scrutineeCode,plain.scope,.push (.plain plain) target⟩ := ⟨rfl,_,plain.scope,.evaluate st scrutineeSaved,pushed_mapped (.cons frame older)⟩
  exact ⟨beforeMapped,actualNext,focused,afterMapped,
    .positive beforeMapped actualNext (.one focused) afterMapped⟩

/-- Initializer focus precedes allocation. Its actual handle bind and masked
resource opening remain in the same saved initializer certificate. -/
theorem resource_initializer_focus {base : CoreMachine.State}
    (known : graph.node site = some node) (kind : node.kind = .resource identity handle initializer body)
    (it : CoreTranslation.translateFuel graph fuel owners initializer = .ok rawInitializer)
    (bt : CoreTranslation.translateFuel graph fuel owners body = .ok rawBody)
    (current : EnvCloses graph owners base.heap environment
      (.resource identity rawInitializer (.bind handle.id (.resourceRef (.bound identity)) rawBody))
      (.resource identity initializerCode suffix))
    (notValue : ¬ initializerCode.IsValue) (plain : PlainData) (context : plain.context = .resource identity suffix)
    (older : PushedWithMaps graph base.heap annotations target) :
    ComponentMapped graph owners annotations
      {base with control := .evaluate site environment, frames := framesOf annotations}
      ⟨.resource identity initializerCode suffix,plain.scope,target⟩ ∧
    CoreMachine.next graph {base with control := .evaluate site environment, frames := framesOf annotations} =
      .stepped {base with control := .evaluate initializer environment, frames := .resourceInitializer site identity handle body environment :: framesOf annotations, observations := base.observations ++ [.entered site]} ∧
    RawStep ⟨.resource identity initializerCode suffix,plain.scope,target⟩ ⟨initializerCode,plain.scope,.push (.plain plain) target⟩ [] [] ∧
    ComponentMapped graph owners ((owners,.resourceInitializer site identity handle body environment) :: annotations)
      {base with control := .evaluate initializer environment, frames := .resourceInitializer site identity handle body environment :: framesOf annotations, observations := base.observations ++ [.entered site]}
      ⟨initializerCode,plain.scope,.push (.plain plain) target⟩ ∧
    CoreInitialPrefix.Link graph
      ⟨{base with control := .evaluate site environment, frames := framesOf annotations},⟨.resource identity initializerCode suffix,plain.scope,target⟩,owners,annotations⟩
      ⟨{base with control := .evaluate initializer environment, frames := .resourceInitializer site identity handle body environment :: framesOf annotations, observations := base.observations ++ [.entered site]},⟨initializerCode,plain.scope,.push (.plain plain) target⟩,owners,((owners,.resourceInitializer site identity handle body environment) :: annotations)⟩ := by
  obtain ⟨initializerSaved,carrier⟩ := resource_components current
  have frame : InitializerRel graph owners base.heap (.resourceInitializer site identity handle body environment) plain :=
    .resource known kind bt carrier context
  have translated : CoreTranslation.translateFuel graph (fuel + 1) owners site =
      .ok (.resource identity rawInitializer (.bind handle.id (.resourceRef (.bound identity)) rawBody)) := by
    rw [CoreTranslation.resource_equation graph owners fuel site node identity handle initializer body known kind,it,bt]; rfl
  have next : CoreMachine.next graph {base with control := .evaluate site environment, frames := framesOf annotations} = .stepped {base with control := .evaluate initializer environment, frames := .resourceInitializer site identity handle body environment :: framesOf annotations, observations := base.observations ++ [.entered site]} := by
    cases node with
    | mk original type effects source nodeKind => cases kind; simp only [CoreMachine.next,known]
  have beforeMapped : ComponentMapped graph owners annotations
      {base with control := .evaluate site environment, frames := framesOf annotations}
      ⟨.resource identity initializerCode suffix,plain.scope,target⟩ := ⟨rfl,_,plain.scope,.evaluate translated current,pushed_mapped older⟩
  have actualNext : CoreMachine.next graph {base with control := .evaluate site environment, frames := framesOf annotations} =
      .stepped {base with control := .evaluate initializer environment, frames := .resourceInitializer site identity handle body environment :: framesOf annotations, observations := base.observations ++ [.entered site]} := next
  have focused : RawStep ⟨.resource identity initializerCode suffix,plain.scope,target⟩ ⟨initializerCode,plain.scope,.push (.plain plain) target⟩ [] [] := .focus plain (by rw [context]; exact .resource notValue) target
  have afterMapped : ComponentMapped graph owners ((owners,.resourceInitializer site identity handle body environment) :: annotations)
      {base with control := .evaluate initializer environment, frames := .resourceInitializer site identity handle body environment :: framesOf annotations, observations := base.observations ++ [.entered site]}
      ⟨initializerCode,plain.scope,.push (.plain plain) target⟩ := ⟨rfl,_,plain.scope,.evaluate it initializerSaved,pushed_mapped (.initializer frame older)⟩
  exact ⟨beforeMapped,actualNext,focused,afterMapped,
    .positive beforeMapped actualNext (.one focused) afterMapped⟩

/-- Supported Core cleanup stores its already related callback value. Therefore
that target focus position is unreachable; registration executes no callback. -/
theorem cleanup_focus_unreachable
    (callback : ValueRel graph owners heap (.closure parameter functionBody environment) action) :
    ¬ Focus (.cleanup action body) child context := by
  intro focus
  cases focus with
  | cleanup notValue => exact notValue callback.closed.1

#print axioms application_function_focus
#print axioms application_argument_focus
#print axioms bind_focus
#print axioms unit_match_focus
#print axioms boolean_focus
#print axioms resource_initializer_focus
#print axioms cleanup_focus_unreachable

#print axioms pair_left_focus
#print axioms pair_right_focus
end Ash.OneShot.CoreStrictFocus
