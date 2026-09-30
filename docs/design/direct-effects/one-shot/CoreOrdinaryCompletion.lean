import CoreAdministrativeTransport
import CoreCallableChecks

/-! Remaining bounded ordinary components. Each result gives actual Core.next
and current/successor interpretations over explicit saved-frame maps. Supplied
PlainData scopes and annotations are preserved, not authenticated. Effects,
reachable phase/map coverage and whole simulation remain outside this slice. -/
namespace Ash.OneShot.CoreOrdinaryCompletion
open ScopedExpressions ScopedExecution CoreValueRelation CoreStrictFrames CoreStrictStack
open CoreStrictPotential

/-- Unit pattern matching adds no Core binding. The target's generated dummy
binding disappears using its current absence certificate, restoring the saved
frame map and scope while retaining all older explicit annotations. -/
theorem unit_match_complete {base : CoreMachine.State}
    (known : graph.node site = some node)
    (kind : node.kind = .matchCases scrutinee [⟨.unit, body⟩])
    (translated : CoreTranslation.translateFuel graph fuel savedOwners body = .ok raw)
    (saved : EnvCloses graph savedOwners base.heap environment raw suffix)
    (absent : Syntax.Dependency.variable (CoreTranslation.dummy graph site) ∉ suffix.dependencies)
    (ready : ClosedExcept (CoreTranslation.dummy graph site) suffix)
    (plain : PlainData) (context : plain.context = .bind (CoreTranslation.dummy graph site) suffix)
    (older : PushedWithMaps graph base.heap annotations target) (runtimeScope : Scope)
    (codeOwners : CoreTranslation.OwnerMap) :
    ComponentMapped graph codeOwners ((savedOwners, .matchCases [⟨.unit, body⟩] environment) :: annotations)
      { base with control := .returned .unit, frames := .matchCases [⟨.unit, body⟩] environment :: framesOf annotations }
      ⟨.unit, runtimeScope, .push (.plain plain) target⟩ ∧
    CoreMachine.next graph { base with control := .returned .unit, frames := .matchCases [⟨.unit, body⟩] environment :: framesOf annotations } =
      .stepped { base with control := .evaluate body environment, frames := framesOf annotations } ∧
    RawStep ⟨.unit, runtimeScope, .push (.plain plain) target⟩
      ⟨.bind (CoreTranslation.dummy graph site) .unit suffix, plain.scope, target⟩ [] [] ∧
    RawStep ⟨.bind (CoreTranslation.dummy graph site) .unit suffix, plain.scope, target⟩
      ⟨suffix, plain.scope, target⟩ [] [] ∧
    ComponentMapped graph savedOwners annotations
      { base with control := .evaluate body environment, frames := framesOf annotations }
      ⟨suffix, plain.scope, target⟩ := by
  have frame : PlainFrameRel graph savedOwners base.heap (.matchCases [⟨.unit, body⟩] environment) plain := by
    change FrameRel graph savedOwners base.heap _ plain.context
    rw [context]; exact .unitMatch known kind translated saved absent ready
  have closed := (ValueRel.unit (graph := graph) (owners := codeOwners) (heap := base.heap)).closed
  have plug := RawStep.plug plain .unit closed runtimeScope target
  simp only [context, Context.plug] at plug
  have bind := RawStep.bind (CoreTranslation.dummy graph site) .unit suffix plain.scope target closed ready
  rw [ScopedTyping.subst_absent suffix (CoreTranslation.dummy graph site) .unit absent] at bind
  exact ⟨⟨rfl, .unit, runtimeScope, .returned .unit, pushed_mapped (.cons frame older)⟩,
    rfl, plug, bind, ⟨rfl, suffix, plain.scope, .evaluate translated saved, pushed_mapped older⟩⟩

/-- Split a single current bind closing derivation. In particular, the saved
body is interpreted under its binder barrier, preserving same-name shadowing,
resource instantiation and the exact finite template replacements. -/
theorem bind_components_at
    (related : EnvCloses graph owners heap environment source output) :
    ∀ binder rawInitializer rawBody initializer body,
      source = .bind binder rawInitializer rawBody → output = .bind binder initializer body →
      EnvCloses graph owners heap environment rawInitializer initializer ∧
      EnvCloses graph owners heap environment (.lambda binder rawBody) (.lambda binder body) := by
  induction related using EnvCloses.rec (motive_1 := fun _ _ _ _ _ => True) with
  | unit | boolean | integer | handle | location | closure => trivial
  | empty =>
      intro binder ri rb i b sourceEq targetEq
      have same : ri = i ∧ rb = b := by simpa [sourceEq] using targetEq
      rcases same with ⟨rfl, rfl⟩; exact ⟨.empty, .empty⟩
  | @binding owners heap value valueCode rest output name code replacement tail ihReplacement ihTail =>
      intro binder ri rb i b sourceEq targetEq
      obtain ⟨left, body⟩ := ihTail binder (ri.subst name valueCode)
        (if name = binder then rb else rb.subst name valueCode) i b
        (by simp only [sourceEq, Code.subst]) targetEq
      exact ⟨.binding replacement left, .binding replacement (by simpa only [Code.subst] using body)⟩
  | @resource owners heap rest output name key code tail ihTail =>
      intro binder ri rb i b sourceEq targetEq
      obtain ⟨left, body⟩ := ihTail binder
        (ri.instantiate (Instantiation.Environment.empty.bind name key))
        (rb.instantiate (Instantiation.Environment.empty.bind name key)) i b
        (by simp only [sourceEq, Code.instantiate]) targetEq
      exact ⟨.resource left, .resource (by simpa only [Code.instantiate] using body)⟩
  | @templateUnused name owners heap rest code output parameter fn absent tail ihTail =>
      intro binder ri rb i b sourceEq targetEq
      obtain ⟨left, body⟩ := ihTail binder ri rb i b sourceEq targetEq
      have leftAbsent : Syntax.Dependency.variable name ∉ ri.dependencies := by
        intro member; apply absent
        simpa only [sourceEq, Code.dependencies] using List.mem_append_left _ member
      have bodyAbsent : Syntax.Dependency.variable name ∉ (Code.lambda binder rb).dependencies := by
        intro member; apply absent
        simpa only [sourceEq, Code.dependencies] using List.mem_append_right ri.dependencies member
      exact ⟨.templateUnused leftAbsent left, .templateUnused bodyAbsent body⟩
  | @templateExpand fuel fn bodyCode parameter name heap rest valueCode owners output code translated callable nonrecursive replacement closed tail ihReplacement ihTail =>
      intro binder ri rb i b sourceEq targetEq
      obtain ⟨left, body⟩ := ihTail binder (ri.subst name valueCode)
        (if name = binder then rb else rb.subst name valueCode) i b
        (by simp only [sourceEq, Code.subst]) targetEq
      exact ⟨.templateExpand translated callable nonrecursive replacement closed left,
        .templateExpand translated callable nonrecursive replacement closed (by simpa only [Code.subst] using body)⟩

theorem bind_components
    (related : EnvCloses graph owners heap environment
      (.bind binder rawInitializer rawBody) (.bind binder initializer body)) :
    EnvCloses graph owners heap environment rawInitializer initializer ∧
    EnvCloses graph owners heap environment (.lambda binder rawBody) (.lambda binder body) :=
  bind_components_at related _ _ _ _ _ rfl rfl

#print axioms bind_components

/-- Singleton nonrecursive wrapper entry uses the actual finite Core check.
Its self-inclusive template successor is constructed from the current bind
interpretation, not supplied as a future relation premise. -/
theorem template_entry {base : CoreMachine.State}
    (known : graph.node site = some node)
    (kind : node.kind = .recursiveBind [member] body)
    (functionKnown : graph.node member.initializer = some functionNode)
    (functionKind : functionNode.kind = .function parameter functionBody)
    (mentions : CoreMachine.mentions graph (graph.nodes.length + 1) member.binder.id member.initializer = .ok false)
    (functionTranslated : CoreTranslation.translateFuel graph fuel owners member.initializer = .ok (.lambda parameter.id rawFunctionBody))
    (bodyTranslated : CoreTranslation.translateFuel graph fuel owners body = .ok rawBody)
    (callable : CallableCertificate graph parameter.id functionBody rawFunctionBody)
    (absent : Syntax.Dependency.variable member.binder.id ∉ (Code.lambda parameter.id rawFunctionBody).dependencies)
    (current : EnvCloses graph owners base.heap environment
      (.bind member.binder.id (.lambda parameter.id rawFunctionBody) rawBody)
      (.bind member.binder.id functionCode bodyCode))
    (closed : ClosedValue functionCode) (ready : ClosedExcept member.binder.id bodyCode)
    (older : PushedWithMaps graph base.heap annotations target) (scope : Scope) :
    ComponentMapped graph owners annotations
      { base with control := .evaluate site environment, frames := framesOf annotations }
      ⟨.bind member.binder.id functionCode bodyCode, scope, target⟩ ∧
    CoreMachine.next graph { base with control := .evaluate site environment, frames := framesOf annotations } =
      .stepped { base with control := .evaluate body (.functionTemplate member.binder.id parameter.id functionBody environment), frames := framesOf annotations, observations := base.observations ++ [.entered site] } ∧
    RawStep ⟨.bind member.binder.id functionCode bodyCode, scope, target⟩
      ⟨bodyCode.subst member.binder.id functionCode, scope, target⟩ [] [] ∧
    ComponentMapped graph owners annotations
      { base with control := .evaluate body (.functionTemplate member.binder.id parameter.id functionBody environment), frames := framesOf annotations, observations := base.observations ++ [.entered site] }
      ⟨bodyCode.subst member.binder.id functionCode, scope, target⟩ := by
  obtain ⟨initializer, savedBody⟩ := bind_components current
  have tail := savedBody.lambda_argument_at _ _ _ functionCode rfl rfl closed
  obtain ⟨emptyFuel, emptyTranslation⟩ := callable.emptyTranslation
  have successor := EnvCloses.templateExpand emptyTranslation callable absent
    (initializer.owner_transport []) closed tail
  have absentBool : (.lambda parameter.id rawFunctionBody : Code).dependencies.contains
      (.variable member.binder.id) = false := by
    apply Bool.eq_false_iff.mpr
    intro present
    exact absent (List.contains_iff_mem.mp present)
  have translation : CoreTranslation.translateFuel graph (fuel + 1) owners site =
      .ok (.bind member.binder.id (.lambda parameter.id rawFunctionBody) rawBody) := by
    cases node with
    | mk original type effects source nodeKind =>
      cases kind
      simp only [CoreTranslation.translateFuel, CoreTranslation.requireNode, known]
      change (do
        let initializer ← CoreTranslation.translateFuel graph fuel owners member.initializer
        if initializer.dependencies.contains (.variable member.binder.id) then
          throw (CoreSyntax.Error.recursiveInitializer site member.binder.id)
        pure (Code.bind member.binder.id initializer (← CoreTranslation.translateFuel graph fuel owners body))) = _
      simp only [functionTranslated, bodyTranslated]
      change (if (Code.lambda parameter.id rawFunctionBody).dependencies.contains (.variable member.binder.id) then
        Except.error (CoreSyntax.Error.recursiveInitializer site member.binder.id)
        else Except.ok (Code.bind member.binder.id (.lambda parameter.id rawFunctionBody) rawBody)) = _
      rw [absentBool]; rfl
  have next : CoreMachine.next graph { base with control := .evaluate site environment, frames := framesOf annotations } =
      .stepped { base with control := .evaluate body (.functionTemplate member.binder.id parameter.id functionBody environment), frames := framesOf annotations, observations := base.observations ++ [.entered site] } := by
    cases functionNode with
    | mk original type effects source nodeKind =>
      cases functionKind
      simp [CoreMachine.next, known, kind, functionKnown, mentions]
  exact ⟨⟨rfl, _, scope, .evaluate translation current, pushed_mapped older⟩, next,
    .bind _ _ _ scope target closed ready,
    ⟨rfl, _, scope, .evaluate bodyTranslated successor, pushed_mapped older⟩⟩

#print axioms template_entry

/-- Value-ready bind initializer entry keeps the whole target bind. Both
children are extracted from its one current closing derivation. -/
theorem bind_entry_same_target {base : CoreMachine.State}
    (ordered : Postorder graph) (known : graph.node site = some node)
    (kind : node.kind = .bind binder initializer body)
    (it : CoreTranslation.translateFuel graph fuel owners initializer = .ok rawInitializer)
    (bt : CoreTranslation.translateFuel graph fuel owners body = .ok rawBody)
    (current : EnvCloses graph owners base.heap environment
      (.bind binder.id rawInitializer rawBody) (.bind binder.id initializerCode suffix))
    (ready : ClosedValue initializerCode) (suffixReady : ClosedExcept binder.id suffix)
    (plain : PlainData) (context : plain.context = .bind binder.id suffix)
    (older : PushedWithMaps graph base.heap annotations target) :
    SilentMapped graph owners owners annotations ((owners, .bind binder.id body environment) :: annotations)
      { base with control := .evaluate site environment, frames := framesOf annotations }
      { base with control := .evaluate initializer environment, frames := .bind binder.id body environment :: framesOf annotations, observations := base.observations ++ [.entered site] }
      ⟨.bind binder.id initializerCode suffix, plain.scope, target⟩ := by
  obtain ⟨initializerSaved, bodySaved⟩ := bind_components current
  have frame : PlainFrameRel graph owners base.heap (.bind binder.id body environment) plain := by
    change FrameRel graph owners base.heap _ plain.context
    rw [context]; exact .bind bt bodySaved suffixReady
  have stack := prepend_mapped frame ready (pushed_mapped older) plain.scope
  simp only [context, Context.plug] at stack
  have translated : CoreTranslation.translateFuel graph (fuel + 1) owners site =
      .ok (.bind binder.id rawInitializer rawBody) := by
    cases node with
    | mk original type effects source nodeKind =>
      cases kind
      simp only [CoreTranslation.translateFuel, CoreTranslation.requireNode, known]
      change (do pure (Code.bind binder.id (← CoreTranslation.translateFuel graph fuel owners initializer)
        (← CoreTranslation.translateFuel graph fuel owners body))) = _
      rw [it, bt]; rfl
  have cost := cost_recurrence ordered known
  simp only [kind, CoreSyntax.Kind.children, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at cost
  refine ⟨?_, ?_, ?_, ⟨rfl, _, plain.scope, .evaluate translated current, pushed_mapped older⟩,
    ⟨rfl, initializerCode, plain.scope, .evaluate it initializerSaved, stack⟩⟩
  · simp [CoreMachine.next, known, kind]
  · simp only [potential, List.map_cons, List.sum_cons, frameWeight]; omega
  · simp [traversalReady, known, kind]

/-- Unit-match entry uses the same bind derivation and the generated dummy's
current raw/closed absence certificates. No dummy binding is added to Core. -/
theorem unit_entry_same_target {base : CoreMachine.State}
    (ordered : Postorder graph) (known : graph.node site = some node)
    (kind : node.kind = .matchCases scrutinee [⟨.unit, body⟩])
    (st : CoreTranslation.translateFuel graph fuel owners scrutinee = .ok rawScrutinee)
    (bt : CoreTranslation.translateFuel graph fuel owners body = .ok rawBody)
    (current : EnvCloses graph owners base.heap environment
      (.bind (CoreTranslation.dummy graph site) rawScrutinee rawBody)
      (.bind (CoreTranslation.dummy graph site) scrutineeCode suffix))
    (rawAbsent : Syntax.Dependency.variable (CoreTranslation.dummy graph site) ∉ rawBody.dependencies)
    (absent : Syntax.Dependency.variable (CoreTranslation.dummy graph site) ∉ suffix.dependencies)
    (ready : ClosedValue scrutineeCode) (suffixReady : ClosedExcept (CoreTranslation.dummy graph site) suffix)
    (plain : PlainData) (context : plain.context = .bind (CoreTranslation.dummy graph site) suffix)
    (older : PushedWithMaps graph base.heap annotations target) :
    SilentMapped graph owners owners annotations ((owners, .matchCases [⟨.unit, body⟩] environment) :: annotations)
      { base with control := .evaluate site environment, frames := framesOf annotations }
      { base with control := .evaluate scrutinee environment, frames := .matchCases [⟨.unit, body⟩] environment :: framesOf annotations, observations := base.observations ++ [.entered site] }
      ⟨.bind (CoreTranslation.dummy graph site) scrutineeCode suffix, plain.scope, target⟩ := by
  obtain ⟨scrutineeSaved, bodySaved⟩ := bind_components current
  have bodyClosed := bodySaved.lambda_argument_at _ _ _ .unit rfl rfl
    (ValueRel.unit (graph := graph) (owners := owners) (heap := base.heap)).closed
  rw [ScopedTyping.subst_absent rawBody _ .unit rawAbsent,
    ScopedTyping.subst_absent suffix _ .unit absent] at bodyClosed
  have frame : PlainFrameRel graph owners base.heap (.matchCases [⟨.unit, body⟩] environment) plain := by
    change FrameRel graph owners base.heap _ plain.context
    rw [context]; exact .unitMatch known kind bt bodyClosed absent suffixReady
  have stack := prepend_mapped frame ready (pushed_mapped older) plain.scope
  simp only [context, Context.plug] at stack
  have translated : CoreTranslation.translateFuel graph (fuel + 1) owners site =
      .ok (.bind (CoreTranslation.dummy graph site) rawScrutinee rawBody) := by
    cases node with
    | mk original type effects source nodeKind =>
      cases kind
      simp only [CoreTranslation.translateFuel, CoreTranslation.requireNode, known]
      change (do pure (Code.bind (CoreTranslation.dummy graph site)
        (← CoreTranslation.translateFuel graph fuel owners scrutinee)
        (← CoreTranslation.translateFuel graph fuel owners body))) = _
      rw [st, bt]; rfl
  have cost := cost_recurrence ordered known
  simp only [kind, CoreSyntax.Kind.children, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at cost
  refine ⟨?_, ?_, ?_, ⟨rfl, _, plain.scope, .evaluate translated current, pushed_mapped older⟩,
    ⟨rfl, scrutineeCode, plain.scope, .evaluate st scrutineeSaved, stack⟩⟩
  · simp [CoreMachine.next, known, kind]
  · simp only [potential, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, frameWeight]; omega
  · simp [traversalReady, known, kind]

#print axioms bind_entry_same_target
#print axioms unit_entry_same_target

/-- Value-ready Boolean entry has exact exhaustive arm shapes and explicit
current child interpretations. It shares the existing common potential. -/
theorem boolean_entry_same_target {base : CoreMachine.State}
    (ordered : Postorder graph) (known : graph.node site = some node)
    (kind : node.kind = .matchCases scrutinee (CoreStrictSteps.booleanArms yes no reversed))
    (st : CoreTranslation.translateFuel graph fuel owners scrutinee = .ok rawScrutinee)
    (yt : CoreTranslation.translateFuel graph fuel owners yes = .ok rawYes)
    (nt : CoreTranslation.translateFuel graph fuel owners no = .ok rawNo)
    (current : EnvCloses graph owners base.heap environment
      (.branch rawScrutinee rawYes rawNo) (.branch scrutineeCode yesCode noCode))
    (scrutineeSaved : EnvCloses graph owners base.heap environment rawScrutinee scrutineeCode)
    (yesSaved : EnvCloses graph owners base.heap environment rawYes yesCode)
    (noSaved : EnvCloses graph owners base.heap environment rawNo noCode)
    (ready : ClosedValue scrutineeCode)
    (plain : PlainData) (context : plain.context = .branch yesCode noCode)
    (older : PushedWithMaps graph base.heap annotations target) :
    SilentMapped graph owners owners annotations ((owners, .matchCases (CoreStrictSteps.booleanArms yes no reversed) environment) :: annotations)
      { base with control := .evaluate site environment, frames := framesOf annotations }
      { base with control := .evaluate scrutinee environment, frames := .matchCases (CoreStrictSteps.booleanArms yes no reversed) environment :: framesOf annotations, observations := base.observations ++ [.entered site] }
      ⟨.branch scrutineeCode yesCode noCode, plain.scope, target⟩ := by
  have frame : PlainFrameRel graph owners base.heap (.matchCases (CoreStrictSteps.booleanArms yes no reversed) environment) plain := by
    change FrameRel graph owners base.heap _ plain.context
    rw [context]; exact .booleanMatch yt nt yesSaved noSaved
  have stack := prepend_mapped frame ready (pushed_mapped older) plain.scope
  simp only [context, Context.plug] at stack
  have translated : CoreTranslation.translateFuel graph (fuel + 1) owners site =
      .ok (.branch rawScrutinee rawYes rawNo) := by
    cases node with
    | mk original type effects source nodeKind =>
      cases kind
      cases reversed <;>
        simp only [CoreStrictSteps.booleanArms, Bool.false_eq_true, ↓reduceIte,
          CoreTranslation.translateFuel, CoreTranslation.requireNode, known] <;>
        change (do pure (Code.branch (← CoreTranslation.translateFuel graph fuel owners scrutinee)
          (← CoreTranslation.translateFuel graph fuel owners yes)
          (← CoreTranslation.translateFuel graph fuel owners no))) = _ <;>
        rw [st, yt, nt] <;> rfl
  have cost := cost_recurrence ordered known
  refine ⟨?_, ?_, ?_, ⟨rfl, _, plain.scope, .evaluate translated current, pushed_mapped older⟩,
    ⟨rfl, scrutineeCode, plain.scope, .evaluate st scrutineeSaved, stack⟩⟩
  · simp [CoreMachine.next, known, kind]
  · cases reversed <;>
      simp [kind, CoreStrictSteps.booleanArms, CoreSyntax.Kind.children] at cost <;>
      simp [potential, frameWeight, CoreStrictSteps.booleanArms] <;> omega
  · cases reversed <;> simp [traversalReady, known, kind, CoreStrictSteps.booleanArms]

/-- Boolean selection pops the explicit saved frame and restores its map/scope;
both arm orders retain the actual selected Core environment unchanged. -/
theorem boolean_match_complete {base : CoreMachine.State}
    (yt : CoreTranslation.translateFuel graph fuel savedOwners yes = .ok rawYes)
    (nt : CoreTranslation.translateFuel graph fuel savedOwners no = .ok rawNo)
    (yesSaved : EnvCloses graph savedOwners base.heap environment rawYes yesCode)
    (noSaved : EnvCloses graph savedOwners base.heap environment rawNo noCode)
    (condition reversed : Bool) (plain : PlainData) (context : plain.context = .branch yesCode noCode)
    (older : PushedWithMaps graph base.heap annotations target) (runtimeScope : Scope)
    (codeOwners : CoreTranslation.OwnerMap) :
    ComponentMapped graph codeOwners ((savedOwners, .matchCases (CoreStrictSteps.booleanArms yes no reversed) environment) :: annotations)
      { base with control := .returned (.boolean condition), frames := .matchCases (CoreStrictSteps.booleanArms yes no reversed) environment :: framesOf annotations }
      ⟨.boolean condition, runtimeScope, .push (.plain plain) target⟩ ∧
    CoreMachine.next graph { base with control := .returned (.boolean condition), frames := .matchCases (CoreStrictSteps.booleanArms yes no reversed) environment :: framesOf annotations } =
      .stepped { base with control := .evaluate (if condition then yes else no) environment, frames := framesOf annotations } ∧
    RawStep ⟨.boolean condition, runtimeScope, .push (.plain plain) target⟩
      ⟨.branch (.boolean condition) yesCode noCode, plain.scope, target⟩ [] [] ∧
    RawStep ⟨.branch (.boolean condition) yesCode noCode, plain.scope, target⟩
      ⟨(if condition then yesCode else noCode), plain.scope, target⟩ [] [] ∧
    ComponentMapped graph savedOwners annotations
      { base with control := .evaluate (if condition then yes else no) environment, frames := framesOf annotations }
      ⟨(if condition then yesCode else noCode), plain.scope, target⟩ := by
  have frame : PlainFrameRel graph savedOwners base.heap (.matchCases (CoreStrictSteps.booleanArms yes no reversed) environment) plain := by
    change FrameRel graph savedOwners base.heap _ plain.context
    rw [context]; exact .booleanMatch yt nt yesSaved noSaved
  have closed := (ValueRel.boolean (graph := graph) (owners := codeOwners) (heap := base.heap) (value := condition)).closed
  have plug := RawStep.plug plain (.boolean condition) closed runtimeScope target
  simp only [context, Context.plug] at plug
  obtain ⟨next, step, saved, translated⟩ := CoreStrictSteps.branch_complete yt nt yesSaved noSaved
    condition reversed (framesOf annotations) plain.scope target
  exact ⟨⟨rfl, _, runtimeScope, .returned .boolean, pushed_mapped (.cons frame older)⟩,
    next, plug, step, ⟨rfl, _, plain.scope, .evaluate translated saved, pushed_mapped older⟩⟩

#print axioms boolean_entry_same_target
#print axioms boolean_match_complete

/-- Wrong scalar input is rejected; no unsupported-match error is a step. -/
theorem unit_match_rejects_integer (graph : CoreSyntax.Graph) (base : CoreMachine.State)
    (body : Nat) (environment : MEnv) (integer : Int) (tail : List CoreMachine.Frame) :
    CoreMachine.next graph { base with control := .returned (.integer integer), frames := .matchCases [⟨.unit, body⟩] environment :: tail } =
      .rejected .unsupportedMatch := rfl

namespace Exported
open CoreExportedFixture
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

private def effectCode : Code := (CoreTranslation.translateFuel graph 56 [] 48).toOption.getD .unit
private def mainCode : Code := .bind (CoreTranslation.dummy graph 49) (.variable 0) effectCode
private def functionCode : Code := .lambda 0 mainCode
private def template : MEnv := .functionTemplate 13 0 49 .empty
private def called : MEnv := .binding 0 .unit template
private def unitPlain : PlainData := ⟨.bind (CoreTranslation.dummy graph 49) effectCode, .none, .unit, .integer, [], rfl⟩
private def base : CoreMachine.State := { control := .returned .unit }
private def matchNode : CoreSyntax.Node :=
  ⟨49, .integer, [], some ⟨1, 1, 69, 548⟩, .matchCases 0 [⟨.unit, 48⟩]⟩
private def wrapperNode : CoreSyntax.Node :=
  ⟨54, .integer, [], some ⟨1, 1, 0, 549⟩,
    .recursiveBind [⟨⟨13, .function .unit .integer []⟩, 50⟩] 53⟩
private def functionNode : CoreSyntax.Node :=
  ⟨50, .function .unit .integer [], [], some ⟨1, 1, 88, 548⟩, .function ⟨0, .unit⟩ 49⟩

private theorem unitClosed : ClosedValue (Code.unit) :=
  (ValueRel.unit (graph := graph) (owners := []) (heap := [])).closed

private theorem callable : CallableCertificate graph 0 49 mainCode :=
  CoreCallableChecks.checkFunction_certificate (site := 50) (checked := ⟨0, 49, mainCode⟩) rfl

private theorem functionClosed : ClosedValue functionCode := by
  have dependencies : functionCode.dependencies = [] := by decide
  have resources : functionCode.freeNames = [] := by decide
  exact ⟨trivial, resources, by rw [dependencies]; simp⟩

private theorem templateAbsent : Syntax.Dependency.variable 13 ∉ functionCode.dependencies := by decide
private theorem effectZeroAbsent : Syntax.Dependency.variable 0 ∉ effectCode.dependencies := by decide
private theorem effectTemplateAbsent : Syntax.Dependency.variable 13 ∉ effectCode.dependencies := by decide
private theorem effectDummyAbsent : Syntax.Dependency.variable (CoreTranslation.dummy graph 49) ∉ effectCode.dependencies := by decide
private theorem effectReady : ClosedExcept (CoreTranslation.dummy graph 49) effectCode := by
  have dependencies : effectCode.dependencies = [] := by decide
  intro name member; rw [dependencies] at member; cases member

private theorem mainValue : ValueRel graph [] [] (.closure 0 49 template) functionCode :=
  .closure (fuel := 56) rfl callable (.templateUnused templateAbsent .empty) functionClosed

private theorem bodySaved : EnvCloses graph [] [] called effectCode effectCode := by
  apply EnvCloses.binding ValueRel.unit
  rw [ScopedTyping.subst_absent effectCode 0 .unit effectZeroAbsent]
  exact .templateUnused effectTemplateAbsent .empty

/-- Actual exported root wrapper entry. Its template successor is derived from
current empty-environment interpretation, not assumed or executed in calculus. -/
theorem wrapper_entry :
    CoreMachine.next graph { base with control := .evaluate 54 .empty } =
      .stepped { base with control := .evaluate 53 template, observations := [.entered 54] } ∧
    RawStep ⟨.bind 13 functionCode (.app (.variable 13) .unit), .none, .nil⟩
      ⟨.app functionCode .unit, .none, .nil⟩ [] [] ∧
    ComponentMapped graph [] []
      { base with control := .evaluate 53 template, observations := [.entered 54] }
      ⟨.app functionCode .unit, .none, .nil⟩ := by
  have ready : ClosedExcept 13 (.app (.variable 13) .unit) := by
    simp [ClosedExcept, Code.dependencies]
  have witness := template_entry (base := base) (graph := graph) (owners := []) (fuel := 56)
    (site := 54) (body := 53) (environment := .empty)
    (functionCode := functionCode) (bodyCode := .app (.variable 13) .unit) (annotations := []) (target := .nil)
    (node := wrapperNode) (member := ⟨⟨13, .function .unit .integer []⟩, 50⟩)
    (functionNode := functionNode) (parameter := ⟨0, .unit⟩) (functionBody := 49)
    (rawFunctionBody := mainCode) (rawBody := .app (.variable 13) .unit)
    rfl rfl rfl rfl rfl rfl rfl callable templateAbsent EnvCloses.empty
    functionClosed ready PushedWithMaps.nil Execution.Scope.none
  simpa only [Code.subst, ↓reduceIte, base, template, framesOf, List.map_nil, List.nil_append] using witness.2

/-- The actual exported main's beta/Unit-match prefix. Arbitrary older mapped
frames remain supplied components. The endpoint enters effect node48; no effect
transition or initial-state reachability theorem is claimed. -/
theorem main_unit_prefix (older : PushedWithMaps graph [] annotations target) :
    CoreMachine.next graph { base with control := .returned .unit, frames := .applyArgument (.closure 0 49 template) :: framesOf annotations } =
      .stepped { base with control := .evaluate 49 called, frames := framesOf annotations } ∧
    RawStep ⟨.app functionCode .unit, .none, target⟩
      ⟨.bind (CoreTranslation.dummy graph 49) .unit effectCode, .none, target⟩ [] [] ∧
    SilentMapped graph [] [] annotations (([], .matchCases [⟨.unit, 48⟩] called) :: annotations)
      { base with control := .evaluate 49 called, frames := framesOf annotations }
      { base with control := .evaluate 0 called, frames := .matchCases [⟨.unit, 48⟩] called :: framesOf annotations, observations := [.entered 49] }
      ⟨.bind (CoreTranslation.dummy graph 49) .unit effectCode, .none, target⟩ ∧
    CoreAdministrativeTransport.TransportMapped graph [] []
      (([], .matchCases [⟨.unit, 48⟩] called) :: annotations)
      (([], .matchCases [⟨.unit, 48⟩] called) :: annotations)
      { base with control := .evaluate 0 called, frames := .matchCases [⟨.unit, 48⟩] called :: framesOf annotations, observations := [.entered 49] }
      { base with control := .returned .unit, frames := .matchCases [⟨.unit, 48⟩] called :: framesOf annotations, observations := [.entered 49, .entered 0] }
      ⟨.bind (CoreTranslation.dummy graph 49) .unit effectCode, .none, target⟩ ∧
    CoreMachine.next graph { base with control := .returned .unit, frames := .matchCases [⟨.unit, 48⟩] called :: framesOf annotations, observations := [.entered 49, .entered 0] } =
      .stepped { base with control := .evaluate 48 called, frames := framesOf annotations, observations := [.entered 49, .entered 0] } ∧
    RawStep ⟨.bind (CoreTranslation.dummy graph 49) .unit effectCode, .none, target⟩
      ⟨effectCode, .none, target⟩ [] [] ∧
    ComponentMapped graph [] annotations
      { base with control := .evaluate 48 called, frames := framesOf annotations, observations := [.entered 49, .entered 0] }
      ⟨effectCode, .none, target⟩ := by
  obtain ⟨fuel, raw, translated, beta, step, closed, argument⟩ :=
    CoreStrictSteps.application_complete (base := base) (graph := graph) (owners := [])
      (parameter := 0) (body := 49) (saved := template) (result := mainCode) mainValue ValueRel.unit (framesOf annotations) Execution.Scope.none target
  have betaStep : RawStep ⟨.app functionCode .unit, .none, target⟩
      ⟨.bind (CoreTranslation.dummy graph 49) .unit effectCode, .none, target⟩ [] [] := by
    simpa [functionCode, mainCode, Code.subst, effectZeroAbsent,
      ScopedTyping.subst_absent effectCode 0 .unit effectZeroAbsent] using step
  have current : EnvCloses graph [] [] called
      (.bind (CoreTranslation.dummy graph 49) (.variable 0) effectCode)
      (.bind (CoreTranslation.dummy graph 49) .unit effectCode) := by
    apply EnvCloses.binding ValueRel.unit
    simp only [Code.subst, ↓reduceIte]
    rw [if_neg (by decide : ¬ (0 : Nat) = CoreTranslation.dummy graph 49),
      ScopedTyping.subst_absent effectCode 0 .unit effectZeroAbsent]
    exact .templateUnused (by decide) .empty
  have entered := unit_entry_same_target (base := base)
    (CoreTranslationFuel.checkShape_postorder (graph := graph) rfl)
    (site := 49) (scrutinee := 0) (body := 48) (environment := called) (owners := [])
    (node := matchNode) (fuel := 56) rfl rfl rfl rfl current effectDummyAbsent effectDummyAbsent
    unitClosed effectReady unitPlain rfl older
  have frame : PlainFrameRel graph [] [] (.matchCases [⟨.unit, 48⟩] called) unitPlain :=
    .unitMatch (site := 49) (scrutinee := 0) (body := 48) (environment := called) (owners := [])
    (node := matchNode) (fuel := 56) rfl rfl rfl bodySaved effectDummyAbsent effectReady
  have stack := prepend_mapped frame unitClosed (pushed_mapped older) Execution.Scope.none
  obtain ⟨returnedValue, lookup, entry, source⟩ := CoreAdministrativeSteps.variable_evaluate
    (base := { base with observations := [.entered 49] })
    (graph := graph) (owners := []) (index := 0)
    (node := ⟨48, .unit, [], some ⟨1, 1, 69, 548⟩, .variable 0⟩) rfl rfl
    (show EnvCloses graph [] [] called (.variable 0) .unit from
      .binding .unit (.templateUnused (by decide) .empty)) unitClosed
    (.matchCases [⟨.unit, 48⟩] called :: framesOf annotations)
  have valueEq : returnedValue = .unit := by
    simpa [called, CoreMachine.Environment.lookup] using lookup.symm
  cases valueEq
  have transport := CoreAdministrativeTransport.value_entry_mapped entry rfl rfl stack
  obtain ⟨before, next, plug, bind, after⟩ := unit_match_complete
    (base := { base with observations := [.entered 49, .entered 0] })
    (site := 49) (scrutinee := 0) (body := 48) (environment := called) (savedOwners := [])
    (node := matchNode) (fuel := 56) rfl rfl rfl bodySaved effectDummyAbsent effectReady
    unitPlain rfl older Execution.Scope.none []
  exact ⟨beta, betaStep, entered, transport, next, bind, after⟩

end Exported
#print axioms Exported.wrapper_entry
#print axioms Exported.main_unit_prefix

#print axioms unit_match_complete
#print axioms unit_match_rejects_integer
end Ash.OneShot.CoreOrdinaryCompletion
